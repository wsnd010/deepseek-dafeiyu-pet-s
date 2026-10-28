# -*- coding: utf-8 -*-
"""任务完成通知 —— 监听 Codex / DSH 的会话日志，任务结束就回一条事件。

设计要点（都是现场实测出来的，见 AGENTS.md「关键实测事实」）：

- **Codex**：标题在 `session_index.jsonl` 的 `thread_name`；
  完成信号在 `sessions/<年>/<月>/<日>/rollout-*.jsonl` 的 `event_msg.task_complete`。
- **DSH**：单个会话就是一个 `session.v4.jsonl.zstd`；
  标题是 `session/title` 事件（有两条，取最后一条），完成是 `turn/end` 的 `reason.kind`。
- **DSH 的 zstd 是多帧拼接的**：一个文件里若干个独立 zstd 帧，
  `decompress()` 只出第一帧，必须按魔数 `28 B5 2F FD` 切分逐帧解压。

两条硬规矩：
1. **按 offset 增量读** —— 会话日志会一直涨（一个会话几十 KB 很常见），绝不能每次全文重扫。
2. **`prime()` 先建基线** —— 第一次跑必须把现有文件都标成"已读到底"，
   否则一启动就把历史任务全报一遍。

这个模块**不依赖 Qt**，可以脱离界面单独测试（`python -m pet_ext.notify`）。
"""

import json
import os
import re
import time
from dataclasses import dataclass, field
from typing import Callable, Optional

try:
    import zstandard as _zstd
except ImportError:      # 没装就退化成"只认 DSH 的 session 头"，不报错
    _zstd = None

# 提示音放 assets/ 里跟点击音一起打包
ASSET_DIR = os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), "assets")


# ---------------------------------------------------------------- 数据结构

@dataclass
class TaskEvent:
    """一条"任务状态变了"的通知。"""
    agent: str                     # "codex" / "dsh"
    session_id: str
    title: str = ""
    state: str = "completed"       # started / completed / failed / cancelled
    text: str = ""                 # 结果正文（不显示，留着备用）
    turn_id: str = ""
    at: float = field(default_factory=time.time)

    def label(self) -> str:
        return self.title.strip() or "一个任务"


_UUID_RE = re.compile(
    r"[0-9a-f]{8}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{12}")
_ZSTD_MAGIC = b"\x28\xb5\x2f\xfd"


def _uuid_in(text: str) -> str:
    got = _UUID_RE.findall(text or "")
    return got[-1] if got else ""


def _read_jsonl_piece(path: str, offset: int):
    """从 offset 往后读，返回 (完整行列表, 新 offset)。

    末尾那半行不完整，要留给下次再读 —— 日志是边跑边写的。
    """
    try:
        size = os.path.getsize(path)
    except OSError:
        return [], offset
    if size < offset:          # 文件被截短 / 换了一份
        offset = 0
    if size == offset:
        return [], offset
    try:
        with open(path, "rb") as f:
            f.seek(offset)
            data = f.read()
    except OSError:
        return [], offset
    new_off = offset + len(data)
    if not data:
        return [], new_off
    # 只处理到最后一个换行符为止，剩下半行留到下次
    cut = data.rfind(b"\n")
    if cut < 0:
        return [], offset            # 连一行都不完整，这次先不动
    body = data[:cut]
    new_off = offset + cut + 1
    lines = []
    for raw in body.split(b"\n"):
        raw = raw.strip()
        if not raw:
            continue
        try:
            lines.append(json.loads(raw.decode("utf-8", "ignore")))
        except Exception:
            continue
    return lines, new_off


# ---------------------------------------------------------------- Codex

class CodexWatcher:
    """盯 `~/.codex-deepseek`：标题来自 session_index，完成来自 rollout 日志。"""

    def __init__(self, root: str = ""):
        base = os.path.expanduser("~")
        default = os.environ.get("CODEX_HOME") or os.path.join(base, ".codex")
        if not os.path.isdir(os.path.join(default, "sessions")):
            default = os.path.join(base, ".codex-deepseek")
        self.root = root or default
        self.index_path = os.path.join(self.root, "session_index.jsonl")
        self.sessions_dir = os.path.join(self.root, "sessions")
        self.titles = {}             # session_id -> thread_name
        self._index_off = 0
        self._files = {}             # path -> offset
        self._reported = set()       # (session_id, turn_id)
        self.available = os.path.isdir(self.root)

    # --- 标题
    def _read_index(self):
        if not os.path.isfile(self.index_path):
            return
        if not self._index_off:
            # 第一次：整个文件都读一遍，把已有的标题收进来（不产生事件）
            self._index_off = 0
        lines, off = _read_jsonl_piece(self.index_path, self._index_off)
        self._index_off = off
        for d in lines:
            sid = str(d.get("id") or "").strip()
            name = str(d.get("thread_name") or "").strip()
            if sid and name:
                self.titles[sid] = name

    # --- 会话日志
    def _recent_rollouts(self, limit: int = 12):
        """只挑最近改过的几个，别每次都遍历整棵目录树。"""
        got = []
        if not os.path.isdir(self.sessions_dir):
            return got
        try:
            for root, _dirs, files in os.walk(self.sessions_dir):
                for fn in files:
                    if not fn.endswith(".jsonl") or not fn.startswith("rollout-"):
                        continue
                    p = os.path.join(root, fn)
                    try:
                        got.append((os.path.getmtime(p), p))
                    except OSError:
                        continue
        except Exception:
            return []
        got.sort(reverse=True)
        return [p for _m, p in got[:limit]]

    def prime(self):
        """建基线：把现有文件全标成已读到底，历史任务不报。"""
        self._read_index()
        for p in self._recent_rollouts(limit=200):
            try:
                self._files[p] = os.path.getsize(p)
            except OSError:
                self._files[p] = 0
        # 历史里已经完成过的 turn 也记下来，免得下次读老行又报一遍
        for p in self._recent_rollouts(limit=200):
            sid = _uuid_in(os.path.basename(p))
            try:
                with open(p, "rb") as f:
                    for raw in f:
                        if b"task_complete" not in raw:
                            continue
                        d = json.loads(raw.decode("utf-8", "ignore"))
                        pay = d.get("payload") or {}
                        tid = str(pay.get("turn_id") or pay.get("root_turn_id") or "")
                        if tid:
                            self._reported.add((sid, tid))
            except Exception:
                continue

    def poll(self):
        out = []
        if not self.available:
            return out
        self._read_index()
        for p in self._recent_rollouts():
            sid = _uuid_in(os.path.basename(p))
            off = self._files.get(p)
            if off is None:
                # 新出现的文件：从现在开始读，不确定它有多久，先从头读但只报最新的完成
                off = 0
            lines, new_off = _read_jsonl_piece(p, off)
            self._files[p] = new_off
            if not lines:
                continue
            done = None
            for d in lines:
                if d.get("type") != "event_msg":
                    continue
                pay = d.get("payload") or {}
                if pay.get("type") == "task_complete":
                    done = pay
            if not done:
                continue
            tid = str(done.get("turn_id") or done.get("root_turn_id") or "")
            key = (sid, tid)
            if key in self._reported:
                continue
            self._reported.add(key)
            out.append(TaskEvent(
                agent="codex",
                session_id=sid,
                title=self.titles.get(sid, ""),
                state="completed",
                text=str(done.get("last_agent_message") or "")[:4000],
                turn_id=tid,
            ))
        return out


# ---------------------------------------------------------------- DSH

class DshWatcher:
    """盯 `~/.dsh/sessions`：每个会话一个多帧 zstd 文件。"""

    def __init__(self, root: str = ""):
        base = os.path.expanduser("~")
        self.root = root or os.path.join(base, ".dsh", "sessions")
        self._files = {}             # path -> {"frames": n, "title": str, "sid": str, "reported": set()}
        self.available = os.path.isdir(self.root) and _zstd is not None

    @staticmethod
    def _frames(path: str):
        """按 zstd 魔数切分，返回每个帧的原始字节。多帧拼接是 DSH 的写法定式。"""
        try:
            with open(path, "rb") as f:
                raw = f.read()
        except OSError:
            return None, []
        marks = []
        pos = 0
        while True:
            i = raw.find(_ZSTD_MAGIC, pos)
            if i < 0:
                break
            marks.append(i)
            pos = i + 4
        frames = []
        for k, start in enumerate(marks):
            end = marks[k + 1] if k + 1 < len(marks) else len(raw)
            frames.append(raw[start:end])
        return raw, frames

    @staticmethod
    def _decompress(frame: bytes) -> str:
        if _zstd is None or not frame:
            return ""
        try:
            dctx = _zstd.ZstdDecompressor()
            obj = dctx.decompressobj()
            return obj.decompress(frame).decode("utf-8", "ignore")
        except Exception:
            try:
                return _zstd.ZstdDecompressor().decompress(frame).decode("utf-8", "ignore")
            except Exception:
                return ""

    def _session_files(self, limit: int = 8):
        got = []
        if not os.path.isdir(self.root):
            return got
        try:
            for root, _dirs, files in os.walk(self.root):
                for fn in files:
                    if not fn.startswith("session.v") or ".jsonl" not in fn:
                        continue
                    p = os.path.join(root, fn)
                    try:
                        got.append((os.path.getmtime(p), p))
                    except OSError:
                        continue
        except Exception:
            return []
        got.sort(reverse=True)
        return [p for _m, p in got[:limit]]

    def prime(self):
        """建基线：现有帧全部记成"已读"，历史不报。"""
        for p in self._session_files(limit=50):
            _raw, frames = self._frames(p)
            st = self._files.setdefault(p, {"frames": 0, "title": "", "sid": "", "reported": set()})
            st["frames"] = len(frames)
            # 顺便把已有标题和已完成的 turn 记下来
            for fr in frames:
                for line in self._decompress(fr).split("\n"):
                    line = line.strip()
                    if not line:
                        continue
                    try:
                        d = json.loads(line)
                    except Exception:
                        continue
                    self._absorb(p, st, d, emit=False)

    def _absorb(self, path, st, d, emit: bool):
        """吃一条 DSH 事件。返回可能要上报的 TaskEvent。"""
        t = d.get("type")
        data = d.get("data") or {}
        if not st.get("sid"):
            if t == "session":
                st["sid"] = str(data.get("id") or d.get("id") or "")
            elif d.get("id"):
                st["sid"] = str(d.get("id"))
        if t == "session/title":
            title = str(data.get("title") or "").strip()
            if title:
                st["title"] = title          # 两条就取后一条（LLM 生成的那条）
            return None
        if t == "turn/end":
            turn = str(data.get("turn") or "")
            reason = str((data.get("reason") or {}).get("kind") or "completed")
            key = turn or str(d.get("seq") or "")
            if not emit or key in (st.get("reported") or set()):
                return None
            st.setdefault("reported", set()).add(key)
            state = {"completed": "completed"}.get(reason, reason or "completed")
            return TaskEvent(
                agent="dsh",
                session_id=st.get("sid") or os.path.basename(os.path.dirname(path)),
                title=st.get("title", ""),
                state=state,
                turn_id=turn,
            )
        return None

    def poll(self):
        out = []
        if not self.available:
            return out
        for p in self._session_files():
            _raw, frames = self._frames(p)
            st = self._files.setdefault(p, {"frames": 0, "title": "", "sid": "", "reported": set()})
            seen = st.get("frames", 0)
            if len(frames) < seen:          # 文件被重写 / 换了一份
                seen = 0
                st["reported"] = set()
            for fr in frames[seen:]:
                for line in self._decompress(fr).split("\n"):
                    line = line.strip()
                    if not line:
                        continue
                    try:
                        d = json.loads(line)
                    except Exception:
                        continue
                    ev = self._absorb(p, st, d, emit=True)
                    if ev:
                        out.append(ev)
            st["frames"] = len(frames)
        return out


# ---------------------------------------------------------------- 汇总

class Notifier:
    """把两个监听合起来，对外只有一个 poll()。

    用法：
        n = Notifier(on_event)      # on_event(ev) 在主线程被调用
        n.prime()                   # 启动时调一次，建基线
        # 之后在 tick 里每隔一两秒 n.poll()
    """

    def __init__(self, on_event: Callable[[TaskEvent], None],
                 codex_root: str = "", dsh_root: str = "",
                 only_done: bool = True):
        self.on_event = on_event
        self.only_done = only_done
        self.codex = CodexWatcher(codex_root)
        self.dsh = DshWatcher(dsh_root)
        self._primed = False

    def agents(self):
        got = []
        if self.codex.available:
            got.append("codex")
        if self.dsh.available:
            got.append("dsh")
        return got

    def prime(self):
        try:
            self.codex.prime()
        except Exception as exc:
            print("[notify] codex prime 失败:", exc)
        try:
            self.dsh.prime()
        except Exception as exc:
            print("[notify] dsh prime 失败:", exc)
        self._primed = True

    def poll(self):
        if not self._primed:
            self.prime()
            return []
        out = []
        for w in (self.codex, self.dsh):
            try:
                out.extend(w.poll())
            except Exception as exc:
                print("[notify] poll 失败:", exc)
        if self.only_done:
            out = [e for e in out if e.state in ("completed", "failed", "cancelled")]
        for ev in out:
            try:
                self.on_event(ev)
            except Exception as exc:
                print("[notify] 回调失败:", exc)
        return out


# ---------------------------------------------------------------- 挂到桌宠上

class NotifyExtension:
    """把 Notifier 挂到桌宠上：定时轮询，命中就弹一条提示。

    只用桌宠已有的几样东西：`pet.cfg`（开关）、`pet.say`（气泡）、`pet.tray`（兜底）、
    `pet.sound_on` / `pet.volume`（提示音跟着全局音效走）。
    不碰 `PetWindow` 的任何方法。
    """

    STATE_TEXT = {
        "completed": "干完了",
        "failed": "出问题了",
        "cancelled": "停下了",
    }

    def __init__(self, pet, interval_ms: int = 2000):
        self.pet = pet
        self.interval_ms = interval_ms
        self.notifier = Notifier(self._on_event)
        self.timer = None
        self._chime = None
        self._chime_path = ""

    # --- 提示音
    def _play_chime(self, force=False):
        """任务完成提示音：播主人选的那一段（内置是 assets/notify-chime.wav）。

        2026-10-24 起这段**不再写死文件名**：设置里能换成主人自己的音频
        （`pet.task_sound_path()`，选择 / 增删都在桌宠那边，这里只管播）。
        换过音频就重建一次 QSoundEffect —— 它按 source 缓存，不换会继续放旧的。

        `force=True` 是"试听"用：跳过开关判断（主人点了试听就该出声）。
        其余情况跟着全局 `sound_on` 和 `task_notify_sound`；
        QtMultimedia 起不来就安静跳过，绝不能因为没声音把气泡也带崩。
        """
        if not force:
            if not bool(getattr(self.pet, "sound_on", True)):
                return
            try:
                if not bool(self.pet.cfg.get("task_notify_sound", True)):
                    return
            except Exception:
                pass

        try:
            path = self.pet.task_sound_path()
        except Exception:
            path = ""
        if not path or not os.path.exists(path):
            path = os.path.join(ASSET_DIR, "notify-chime.wav")

        # ⚠️ 优先走桌宠那条**常开音频流**：能完整播完、音量也独立可调。
        # 旧版一律用 QSoundEffect，而它"刚 setSource 还没解码完"时 play() 只响开头一小截
        # —— 内置那声「叮」是立体声 wav，旧版 `load_clip` 又不认立体声，
        # 于是每次都走 QSoundEffect，每次都断在开头（主人 2026-10-27 报的
        # 「任务提示音播放时不完整」）。立体声下混已经加上了。
        try:
            if self.pet.play_task_chime(path):
                return
        except Exception:
            pass

        if self._chime is None or getattr(self, "_chime_path", "") != path:
            try:
                from PySide6.QtCore import QUrl
                from PySide6.QtMultimedia import QSoundEffect

                eff = QSoundEffect(self.pet)
                eff.setSource(QUrl.fromLocalFile(path))
                # 比点击音略小一档：是"提个醒"，不是"报喜"。自定义音频也一样缩，
                # 不然主人挑的那段可能比点击音响一截。
                try:
                    _vol = self.pet.task_sound_volume()
                except Exception:
                    _vol = 0.8 * float(getattr(self.pet, "volume", 0.9))
                eff.setVolume(_vol)
                self._chime = eff
                self._chime_path = path
            except Exception as exc:
                print("[notify] 提示音起不来（气泡照旧）:", exc)
                return
        if self._chime is not None:
            try:
                # 兜底也要等解码好：没 Ready 就排到 `_pending` 里（见 notify 的 tick）
                from PySide6.QtMultimedia import QSoundEffect
                if self._chime.status() == QSoundEffect.Status.Ready:
                    self._chime.play()
            except Exception:
                pass

    # --- 生命周期
    def start(self):
        from PySide6.QtCore import QTimer

        self.notifier.prime()          # 先建基线：历史任务一条都不报
        self.timer = QTimer(self.pet)
        self.timer.timeout.connect(self._tick)
        self.timer.start(self.interval_ms)
        src = "、".join(self.notifier.agents()) or "都没有"
        print(f"[notify] 任务完成通知已启动（盯：{src}）")
        return self

    def stop(self):
        if self.timer is not None:
            try:
                self.timer.stop()
            except Exception:
                pass
            self.timer = None

    # --- 每次轮询
    def _tick(self):
        if not bool(self.pet.cfg.get("task_notify_on", True)):
            return
        try:
            self.notifier.poll()
        except Exception as exc:
            print("[notify] 轮询出错:", exc)

    # --- 命中一条
    def _on_event(self, ev: TaskEvent):
        """在桌宠自己的气泡里说一句，不弹系统通知。

        系统通知只在"看不见桌宠"时兜底（被隐藏了 / 鼠标穿透找不到它），
        否则一律走桌宠的气泡 —— 冷冰冰的系统弹窗和这个盆友的调性不搭。
        """
        title = ev.label()
        body = self.STATE_TEXT.get(ev.state, "有动静了")
        who = "Codex" if ev.agent == "codex" else "DSH"
        text = f"{who}那个「{title}」{body}"
        print(f"[notify] {text}")

        visible = True
        try:
            visible = bool(self.pet.isVisible())
        except Exception:
            pass

        if visible:
            self._play_chime()          # 先响一声，再冒泡（声音起播有一点延迟，压在前面更自然）
            try:
                # queue=True：这是自动触发的提醒，排在其它话后面依次说，不抢
                self.pet.say(text, seconds=7.0, queue=True)
            except Exception as exc:
                print("[notify] 冒泡失败:", exc)
            # 顺手给个动作，别只是干说一句
            # （灵动版播一段真动作；三视图 / 挂件只有蹦跳 / 摇摆 / 拉伸三样，
            #   所以成功蹦一下、失败摇一下）
            try:
                _anim = getattr(self.pet, "ext", {}).get("anim")
                if _anim is not None and _anim._is_anim_skin():
                    _anim.play_once("wave" if ev.state == "completed" else "lion")
                else:
                    self.pet.play_action("jump" if ev.state == "completed" else "sway")
            except Exception:
                pass
            return

        # 看不见它才用系统通知兜底
        try:
            from PySide6.QtWidgets import QSystemTrayIcon
            tray = getattr(self.pet, "tray", None)
            if tray is not None:
                tray.showMessage(title, f"{who} {body}",
                                 QSystemTrayIcon.MessageIcon.Information, 6000)
        except Exception as exc:
            print("[notify] 兜底通知也失败了:", exc)


def setup(pet):
    """桌宠启动时被 `pet_ext.load_extensions` 调到。"""
    return NotifyExtension(pet).start()


# ---------------------------------------------------------------- 自测

if __name__ == "__main__":
    print("Codex 目录存在:", os.path.isdir(os.path.join(os.path.expanduser("~"), ".codex-deepseek")))
    print("DSH 目录存在:", os.path.isdir(os.path.join(os.path.expanduser("~"), ".dsh", "sessions")))
    print("zstandard:", "可用" if _zstd is not None else "未安装")

    got = []
    n = Notifier(lambda ev: got.append(ev), only_done=False)
    n.prime()
    print("已建基线，可用源:", n.agents())
    print("首次 poll（应为空）:", n.poll())
    print("Codex 已知标题数:", len(n.codex.titles))
    for sid, name in list(n.codex.titles.items())[:5]:
        print("   ", name)
