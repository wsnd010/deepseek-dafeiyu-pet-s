# -*- coding: utf-8 -*-
"""喂食、系统提醒与 Codex 状态联动，独立挂载到桌宠。"""
import json
import os
from pathlib import Path
import subprocess
import threading
import time

from PySide6.QtCore import QObject, QTimer, Qt, Signal, Slot
from PySide6.QtGui import QPixmap

from .notify import _read_jsonl_piece

FOODS = {
    "小鱼干": ("小鱼干！咔嚓咔嚓，谢谢投喂！", "snack"),
    "蛋糕": ("蛋糕！甜到冒泡泡，又圆了一圈。", "snack"),
    "棒棒糖": ("棒棒糖！这口甜甜的留着慢慢吃。", "icecream"),
    "团子": ("软乎乎的团子，糯叽叽！", "snack"),
    "钻石": ("钻石？！这个得收好，不能真咬。", "wave"),
}
STATE_LABELS = {"idle": "空闲", "start": "开始任务", "working": "思考中",
                "tool_read": "读文件", "tool_edit": "写代码", "tool_pwsh": "运行命令",
                "tool_web": "联网查询", "approval": "等待确认", "done": "任务完成",
                "error": "任务出错", "sing": "听歌"}


def event_state(event):
    """只读取事件类型和工具名，不显示或保存对话正文。"""
    payload = event.get("payload") or {}
    kind = payload.get("type")
    if event.get("type") == "event_msg":
        return {"task_started": "start", "task_complete": "done", "turn_aborted": "idle",
                "task_failed": "error", "error": "error", "agent_reasoning": "working",
                "approval_required": "approval"}.get(kind)
    if event.get("type") == "response_item":
        if kind in ("function_call", "custom_tool_call"):
            name = str(payload.get("name") or "").lower()
            if "request_user_input" in name:
                return "approval"
            if any(x in name for x in ("search", "browse", "web")):
                return "tool_web"
            if any(x in name for x in ("patch", "edit", "write_file")):
                return "tool_edit"
            if any(x in name for x in ("read", "list", "find")):
                return "tool_read"
            return "tool_pwsh"
        if kind in ("function_call_output", "custom_tool_call_output", "reasoning"):
            return "working"
    return None


class CodexStatus:
    def __init__(self, roots=None):
        home = Path.home()
        self.roots = roots if roots is not None else list(dict.fromkeys(
            [home / ".codex", home / ".codex-deepseek"] +
            ([Path(os.environ["CODEX_HOME"])] if os.environ.get("CODEX_HOME") else [])))
        self.files = {}
        self.states = {}
        self.paths = []
        self.next_scan = 0

    def poll(self):
        now = time.time()
        if now >= self.next_scan:
            candidates = []
            for root in self.roots:
                for path in (Path(root) / "sessions").glob("**/rollout-*.jsonl"):
                    try:
                        candidates.append((path.stat().st_mtime, str(path)))
                    except OSError:
                        pass
            self.paths = [p for _, p in sorted(candidates, reverse=True)[:16]]
            self.next_scan = now + 15
        for path in self.paths:
            try:
                stat = os.stat(path)
                old = self.files.get(path)
                if old is not None and old == (stat.st_size, stat.st_mtime):
                    continue
                # 初次和截断后只回放尾部，不把完整历史载入内存。
                offset = old[0] if old and stat.st_size >= old[0] else max(0, stat.st_size - 262144)
                events, offset = _read_jsonl_piece(path, offset)
                state = self.states.get(path, (0, "idle"))[1]
                for event in events:
                    state = event_state(event) or state
                self.states[path] = (stat.st_mtime, state)
                self.files[path] = (offset, stat.st_mtime)
            except OSError:
                pass
        self.states = {p: value for p, value in self.states.items() if p in self.paths}
        self.files = {p: value for p, value in self.files.items() if p in self.paths}
        recent = [(stamp, state) for stamp, state in self.states.values() if now - stamp < 120]
        active = [(stamp, state) for stamp, state in recent if state not in ("idle", "done", "error")]
        return max(active or recent, default=(0, "idle"))[1]


def sample_system():
    import psutil
    cpu = psutil.cpu_percent(interval=0.2)
    memory = psutil.virtual_memory().percent
    temperature = None
    try:
        result = subprocess.run(
            ["nvidia-smi", "--query-gpu=temperature.gpu", "--format=csv,noheader,nounits"],
            capture_output=True, text=True, timeout=3,
            creationflags=getattr(subprocess, "CREATE_NO_WINDOW", 0))
        values = [float(v.strip()) for v in result.stdout.splitlines() if v.strip().isdigit()]
        if result.returncode == 0 and values:
            temperature = max(values)
    except (OSError, subprocess.SubprocessError):
        pass
    return {"cpu": cpu, "memory": memory, "gpu": temperature}


class Companion(QObject):
    sampled = Signal(object, str, str)

    def __init__(self, pet):
        super().__init__(pet)
        self.pet = pet
        self.watcher = CodexStatus()
        self.state = "idle"
        self.metrics = {}
        self.error = ""
        self.busy = False
        self.last_monitor = 0
        self.last_feed = 0
        self.alerted = {}
        self.last_anim = 0
        self.state_since = time.monotonic()
        self.original_sprite = pet._sprite_key
        self.base_dir = Path(__file__).resolve().parents[1] / "sprites" / "dsh"
        self.pixmaps = {}
        self.sampled.connect(self._apply)
        pet._sprite_key = self.sprite_key
        self.timer = QTimer(self)
        self.timer.timeout.connect(self.poll)
        self.timer.start(2000)
        QTimer.singleShot(1500, self.poll)

    def option(self, name, default=False):
        return bool(self.pet.cfg.get(name, default))

    def set_option(self, name, value):
        self.pet.cfg[name] = bool(value)
        self.pet.save_config()
        if name == "companion_portraits":
            if value:
                self.pet.cfg["companion_previous_skin"] = self.pet.skin
                self.pet.set_skin("大肥鱼")
            else:
                self.pet.set_skin(self.pet.cfg.get("companion_previous_skin") or "大肥鱼")
        self.pet.update()
        self.poll()

    def feed(self, food):
        if food not in FOODS or time.monotonic() - self.last_feed < 1.5:
            return
        self.last_feed = time.monotonic()
        living = getattr(self.pet, "ext", {}).get("living")
        if living is not None:
            living.touch()
        line, clip = FOODS[food]
        self.pet.say(line, seconds=4, again=True)
        anim = getattr(self.pet, "ext", {}).get("anim")
        if anim is not None and anim._is_anim_skin():
            anim.play_once(clip)
        else:
            self.pet.play_action("jump")
        count = int(self.pet.cfg.get("feed_count", 0)) + 1
        self.pet.cfg["feed_count"] = count
        self.pet.save_config()

    def poll(self):
        if self.busy:
            return
        monitor = self.option("sys_monitor_on", True)
        link = self.option("codex_link_on", True)
        due = monitor and time.monotonic() - self.last_monitor >= 10
        if not due and not link:
            return
        self.busy = True
        if due:
            self.last_monitor = time.monotonic()

        def worker():
            metrics, state, error = {}, "idle", ""
            if due:
                try:
                    metrics = sample_system()
                except Exception:
                    error = "系统采样不可用，请确认已安装 psutil"
            if link:
                try:
                    state = self.watcher.poll()
                except Exception:
                    error = "Codex 日志暂时不可读"
            try:
                self.sampled.emit(metrics, state, error)
            except RuntimeError:
                pass

        threading.Thread(target=worker, daemon=True).start()

    @Slot(object, str, str)
    def _apply(self, metrics, state, error):
        self.busy = False
        self.error = error
        if metrics:
            self.metrics = metrics
        previous = self.state
        self.state = state if self.option("codex_link_on", True) else "idle"
        if self.state != previous:
            self.state_since = time.monotonic()
        if self.option("sys_monitor_on", True):
            for key, limit, label, unit in (("cpu", 90, "CPU 占用", "%"),
                                            ("memory", 95, "内存占用", "%"),
                                            ("gpu", 80, "NVIDIA 显卡温度", "℃")):
                value = metrics.get(key)
                if value is not None and value >= limit and time.monotonic() - self.alerted.get(key, -600) >= 300:
                    self.alerted[key] = time.monotonic()
                    self.pet.say(f"{label}已到 {value:.0f}{unit}，休息一下，检查正在运行的任务吧。",
                                 seconds=6, queue=True)
        if self.state != previous and self.option("codex_link_on", True):
            anim = getattr(self.pet, "ext", {}).get("anim")
            clip = {"start": "wave", "working": "thinking", "tool_edit": "coding",
                    "tool_pwsh": "coding", "tool_read": "thinking", "tool_web": "thinking",
                    "approval": "look_around", "done": "wave", "error": "startle"}.get(self.state)
            if (clip and anim is not None and anim._is_anim_skin()
                    and time.monotonic() - self.last_anim >= 8
                    and time.monotonic() - self.last_feed >= 8
                    and not getattr(self.pet, "dragging", False)):
                if not getattr(self.pet, "_anim_walking", False) and not getattr(self.pet, "_amb_phase", None):
                    if anim.player.clip not in anim.once_clips():
                        self.last_anim = time.monotonic()
                        anim.play_once(clip)
        self.pet.update()

    def sprite_key(self):
        original = self.original_sprite()
        if not self.option("companion_portraits") or self.pet.skin != "大肥鱼":
            return original
        state = self.state if self.option("codex_link_on", True) else "idle"
        if state == "idle" and self.pet._music_playing():
            state = "sing"
        if state == "idle":
            living = getattr(self.pet, "ext", {}).get("living")
            if living is not None and living.on():
                state = {"happy": "done", "focused": "working", "curious": "tool_read",
                         "missing": "start"}.get(living.mood, "idle")
        h = self.pet.cur_h
        frame = min(3, int((time.monotonic() - self.state_since) / 0.25) + 1) if state == "start" else 1
        cache_key = (state, frame, h)
        name = f"companion:{state}:{frame}"
        if cache_key not in self.pixmaps:
            pix = QPixmap(str(self.base_dir / state / f"{frame}_306.png"))
            base = self.pet.sprites.get(("正面", h))
            if pix.isNull() or base is None:
                return original
            pix = pix.scaled(base.size(), Qt.AspectRatioMode.KeepAspectRatio,
                             Qt.TransformationMode.SmoothTransformation)
            if len(self.pixmaps) > 32:
                self.pixmaps.clear()
            self.pixmaps[cache_key] = pix
        self.pet.sprites[(name, h)] = self.pixmaps[cache_key]
        return name, h, 1


def setup(pet):
    return Companion(pet)
