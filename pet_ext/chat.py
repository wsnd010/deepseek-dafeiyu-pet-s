# -*- coding: utf-8 -*-
"""聊天通道（P5）：右键「和她聊聊…」→ 侧边浮窗里跟 DeepSeek 说话。

和 P6（派活）是**两条分开的通道**（主人定的）：聊天走 API，任务走 Agent，不混在一起。

代码来源：老版本（`git show d6ae670^:桌宠.py` 的 `_call_ds` / `DS_SYSTEM` / `chat_history`）。
捡骨架、换皮，改了三处：
  1. **不再砍 30 字**：老版本头顶气泡只有 112px 高，只能硬砍（`reply[:28] + "…"`）。
     现在长回复进侧边浮窗，气泡只报个短的；
  2. 线程结果用 **Signal** 回主线程（老版本用 `_queue_say` 那个队列，也行，但这里要
     同时更新浮窗，用信号更直白）；
  3. 错误信息说人话（老版本是 `API错误: xxx[:12]`，砍得看不出问题）。

线程规矩（这条必须守）：**网络请求只在 worker 线程里做，所有 UI 操作只在主线程做**。
worker 里只 `emit`，槽函数跑在主线程。
"""

from __future__ import annotations

import threading
from .node import BASE_URL, MODEL, current_model

from PySide6.QtCore import QEvent, QObject, QPoint, QRect, Qt, QTimer, Signal
from PySide6.QtGui import QColor, QPainter, QPen
from PySide6.QtWidgets import QWidget

try:
    import requests
except Exception:                     # 没装 requests 也要能加载（到时候报一句能看懂的话）
    requests = None


DS_URL = BASE_URL + "/v1/chat/completions"
DS_MODEL = MODEL
DS_TIMEOUT = 60                       # 秒。长回复要慢一些，10 秒（老版本）经常不够
DS_MAX_TOKENS = 800                   # 浮窗装得下，不用再压到 100
HISTORY_MAX = 40                      # 默认最多记 40 条（20 轮）
MEMORY_CHOICES = (20, 40, 60, 80, 100)  # 设置里能选的上限（步长 20，最大 100）
BUBBLE_CHARS = 18                     # 桌宠头顶气泡里只显示前这么多字

# 人设：老版本那句 + 「可以多说几句」。
# 老版本限制 25 字是因为气泡装不下，现在长内容进浮窗了，不必再逼她说话像发电报。
SYSTEM_PROMPT = (
    "你是桌面宠物大肥鱼，贱兮兮但可爱，说话像熟人聊天。"
    "平时一两句就够；主人问正经事（代码、表格、计划）就好好答，可以长一点，"
    "但别写客套话和总结段。偶尔吐槽主人，但别真骂人。"
)


class ChatError(Exception):
    """请求失败（网络 / 鉴权 / 返回格式）。消息是**给人看的**，会直接显示在浮窗里。"""


def post_json(url, payload, key, timeout=DS_TIMEOUT):
    """发一次请求，返回解析好的 JSON。单独拆出来是为了测试时能替换掉（不花钱）。"""
    if requests is None:
        raise ChatError("没装 requests，跑不起来（pip install requests）")
    headers = {"Authorization": f"Bearer {key}", "Content-Type": "application/json"}
    try:
        resp = requests.post(url, json=payload, headers=headers, timeout=timeout)
    except Exception as exc:
        name = type(exc).__name__
        if "Timeout" in name:
            raise ChatError("等太久了（60 秒没回），请检查 Sub2API 节点") from exc
        if "Connection" in name or "SSL" in name:
            raise ChatError(f"连不上 Sub2API 节点 {BASE_URL}，请检查网络") from exc
        raise ChatError(f"请求失败：{name}: {exc}") from exc

    if resp.status_code != 200:
        detail = ""
        try:
            detail = (resp.json().get("error") or {}).get("message") or ""
        except Exception:
            detail = (resp.text or "")[:120]
        if resp.status_code == 401:
            raise ChatError("Sub2API 节点鉴权失败（401）。请在设置 → 余额和用量 → 设置 Key 核对节点 Key（不要带句号或 Bearer 前缀）")
        if resp.status_code == 402:
            raise ChatError("Sub2API 节点余额或额度不足（402）")
        if resp.status_code == 429:
            raise ChatError("请求太频繁（429），等几秒再说")
        raise ChatError(f"Sub2API 返回 {resp.status_code}：{detail or '没有说明'}")
    try:
        return resp.json()
    except Exception as exc:
        raise ChatError("返回的不是 JSON，可能被代理拦了") from exc


class ChatCircle(QWidget):
    """桌宠右上角那个圆形按钮：点一下 → 从圆长成聊天板子。

    为什么是桌宠的**子控件**（不是另开窗口）：
      另开一个 always-on-top 的小窗，得自己跟着桌宠走、自己处理显示/隐藏、
      还得保证不被桌宠窗口盖住。做成子控件，这些全免费 —— 窗口一动它就跟着动。

    ⚠️ 位置必须按 `pet.sprite_rect()` 算，不能用窗口矩形：灵动版窗口是按**最宽画布**
    固定的，鱼只占中间一条，按窗口算按钮会飘到离鱼很远的空地上（这个坑实测踩过）。
    """

    SIZE = 34          # 直径（跟着桌宠大小档位会略微变，见 `reposition`）

    def __init__(self, ext):
        super().__init__(ext.pet)
        self.ext = ext
        self._hover = False
        self._pix = None
        self._retries = 0
        self.setFixedSize(self.SIZE, self.SIZE)
        self.setCursor(Qt.CursorShape.PointingHandCursor)
        self.setToolTip("和她聊聊")
        self.setAttribute(Qt.WidgetAttribute.WA_TranslucentBackground, True)
        self.apply_theme()
        self.reposition()

    # ------------------------------------------------------------------ 外观
    def apply_theme(self):
        """配色跟设置窗口那套走（亮 / 暗主题都自动对上）。"""
        t = self.ext._tokens()
        self._bg = QColor(t["surface"])
        self._bg.setAlpha(228)
        self._border = QColor(t["border"])
        self._fg = t["accent"]
        if self._pix is None:
            try:
                import ui_console
                self._pix = ui_console.icon_pixmap("ui.chat", self._fg, 17)
            except Exception:
                self._pix = None
        self.update()

    def paintEvent(self, ev):
        p = QPainter(self)
        p.setRenderHint(QPainter.RenderHint.Antialiasing, True)
        r = self.rect().adjusted(1, 1, -1, -1)
        bg = QColor(self._bg)
        if self._hover:
            bg.setAlpha(248)
        p.setPen(QPen(self._border, 1))
        p.setBrush(bg)
        p.drawEllipse(r)
        if self._pix is not None:
            w = self._pix.width() / max(1.0, self._pix.devicePixelRatio())
            h = self._pix.height() / max(1.0, self._pix.devicePixelRatio())
            p.drawPixmap(QPoint(int((self.width() - w) / 2), int((self.height() - h) / 2)),
                         self._pix)
        p.end()

    # ------------------------------------------------------------------ 交互
    def enterEvent(self, ev):
        self._hover = True
        self.update()
        super().enterEvent(ev)

    def leaveEvent(self, ev):
        self._hover = False
        self.update()
        super().leaveEvent(ev)

    def mousePressEvent(self, ev):
        """按下就吃掉。

        ⚠️ 必须吃掉：不吃的话事件会冒到父窗口（桌宠），那边会当成"点了她一下" ——
        又蹦一下、又响一声，还开始拖动。点这个圆应该只有一件事发生：打开聊天。
        """
        if ev.button() == Qt.MouseButton.LeftButton:
            ev.accept()
            return
        super().mousePressEvent(ev)

    def mouseMoveEvent(self, ev):
        ev.accept()          # 同上：别让桌宠以为在拖它

    def mouseDoubleClickEvent(self, ev):
        ev.accept()          # 双击也别触发"换姿势"

    def mouseReleaseEvent(self, ev):
        if ev.button() == Qt.MouseButton.LeftButton and self.rect().contains(ev.position().toPoint()):
            self.ext.open_from(self)
            ev.accept()
            return
        super().mouseReleaseEvent(ev)

    # ------------------------------------------------------------------ 位置
    def reposition(self):
        """贴着鱼的右上角放（略压住一点头发，看着像别在头上的小徽章）。

        ⚠️ 启动那一两秒 `sprite_rect()` 还拿不到真实尺寸（灵动版的帧还没解出来），
        这时算出来的位置是"窗口右上角"——离鱼很远。所以**算不准就过 150ms 再来**，
        最多试 20 次（3 秒）。这条就是主人说的"第一次启动后位置不正确"。
        """
        pet = self.ext.pet
        try:
            spr = pet.sprite_rect()
            # ⚠️ 摆位用**鱼本体**（有像素的那块），不是画布：画布左右有透明留白，
            # 按画布摆，鱼一放大按钮就"飘在离鱼很远的地方"；鱼很小时又会压到头上
            # （主人 2026-10-27 两张截图：20% 压头、135% 离得远）。
            try:
                body = pet.sprite_body_rect()
            except Exception:
                body = spr
            win = pet.rect()
            ready = pet.sprite_ready()
        except Exception:
            return
        if not ready and self._retries < 20:
            self._retries += 1
            QTimer.singleShot(150, self.reposition)
            return
        if ready:
            self._retries = 0
        # 大小也跟鱼身宽成比例（12%），夹在 20~40：
        # 20% 档鱼身 53 宽 → 20px（再小就点不中了）；135% 档 357 宽 → 40px。
        size = max(20, min(40, int(round(body.width() * 0.12))))
        if size != self.width():
            self.setFixedSize(size, size)
        if body.width() >= 110:
            # 鱼够大：压在发梢上，像别在头上的小徽章（主人 2026-10-26 说"太诡异"就是嫌飘）
            cx = body.right() - int(size * 0.55)
            cy = body.top() + int(size * 0.60)
        else:
            # 鱼很小（20% 那种）：别压在头上，挪到右上外侧一点，谁也不挡谁
            cx = body.right() + int(size * 0.55)
            cy = body.top() + int(size * 0.10)
        x = cx - size // 2
        y = cy - size // 2
        x = max(2, min(x, win.width() - size - 2))
        y = max(2, min(y, win.height() - size - 2))
        self.move(x, y)
        self.raise_()

    def global_rect(self):
        return QRect(self.mapToGlobal(QPoint(0, 0)), self.size())


class ChatExtension(QObject):
    """挂到 `pet.ext["chat"]`。线程 → 主线程靠这两个信号。"""

    reply_ready = Signal(str)
    failed = Signal(str)

    def __init__(self, pet):
        super().__init__()
        self.pet = pet
        self.history = []             # [{"role": "user"/"assistant", "content": ...}]
        self._busy = False
        self._opened_once = False
        self._bubble = None           # 桌宠右上角那个圆形按钮（设置里可关）
        self._flyout_hooked = False   # 有没有连上浮窗的 closed 信号
        self._flyout_open = False     # 聊天板子现在是不是开着（开着就不许圆按钮冒出来）
        self._refreshing = False      # `refresh_bubble` 的防重入（见那个方法）
        # 默认是 AutoConnection：emit 发生在 worker 线程 → 槽函数排队回主线程执行
        self.reply_ready.connect(self._on_reply)
        self.failed.connect(self._on_failed)

    # ------------------------------------------------------------------ 生命周期
    def start(self):
        """把右上角那个圆形按钮挂上（设置里关掉就不建）。"""
        if bool(self.pet.cfg.get("chat_bubble", True)):
            self._ensure_bubble()
        # 桌宠换大小 / 换形象 / 被显示出来，按钮都要重新贴到鱼头上
        try:
            self.pet.installEventFilter(self)
        except Exception:
            pass
        # ⚠️ 这里**不能**连浮窗的 `closed` 信号：`load_extensions` 是先把所有扩展
        # setup 完再统一塞进 `pet.ext` 的，此刻 `self._flyout()` 还是 None（实测踩过，
        # 结果就是"关窗后圆按钮回不来"）。改成第一次用的时候再连，见 `_hook_flyout`。
        return self

    def _hook_flyout(self, fly):
        """第一次拿到浮窗时把 `closed` / `closing` 连上（只连一次）。

        `closing` 是收起动画**第一帧**就发的：圆按钮这时回来，让板子"缩进圆里"，
        而不是缩完才出现（主人 2026-10-26 要的"和打开一样缩回去"）。
        """
        if fly is None or self._flyout_hooked:
            return
        try:
            win = fly.window()
            win.closed.connect(self._on_flyout_closed)
            win.closing.connect(self._on_flyout_closed)
            self._flyout_hooked = True
        except Exception:
            pass

    def _on_flyout_closed(self):
        self._flyout_open = False      # 板子收起来了 → 圆按钮该回来了
        self.refresh_bubble()

    def _tokens(self):
        try:
            import ui_console
            return ui_console.tokens()
        except Exception:
            from .flyout import _fallback_tokens
            return _fallback_tokens()

    def _ensure_bubble(self):
        if self._bubble is None:
            self._bubble = ChatCircle(self)
        self._bubble.apply_theme()
        self._bubble.reposition()
        # ⚠️ 板子开着的时候**不许**把圆按钮放出来。
        # 主人 2026-10-27：「在打开聊天窗口的情况下调整了桌宠大小，圆按钮会自动再次出现」
        # —— 拖大小滑块时设置页会把「聊天入口」开关重新初始化一遍 → set_chat_bubble()
        # → 这里被调到 → 圆又冒出来压在聊天窗口上。
        # 用自己记的标记（不用 fly.visible）：收起动画第一帧 `closing` 就要把圆放回来，
        # 那会儿窗口还是可见的，按 visible 判会把"缩进圆里"的效果弄没。
        if self._flyout_open:
            self._bubble.hide()
            return self._bubble
        self._bubble.show()
        self._bubble.raise_()
        return self._bubble

    def refresh_bubble(self):
        """设置里改完开关调这个：开就建/显示，关就藏起来。

        ⚠️ 必须防重入：关掉时这里会 `fly.hide()`，而浮窗收起会发 `closing` 信号，
        那个信号又连回本函数 —— 不加锁就是无限递归，进程直接崩（实测 EXIT=127）。
        """
        if self._refreshing:
            return
        self._refreshing = True
        try:
            if bool(self.pet.cfg.get("chat_bubble", True)):
                self._ensure_bubble()
                return
            if self._bubble is not None:
                self._bubble.hide()
            # 关掉入口时顺手把已经开着的板子收回去 —— 不然圆没了、窗口还杵在那儿，
            # 看着像"没关干净"（也再没有入口能把它叫回来）。
            fly = self._flyout()
            try:
                if fly is not None and fly.visible:
                    fly.hide()
            except Exception:
                pass
        finally:
            self._refreshing = False

    @property
    def bubble(self):
        return self._bubble

    def eventFilter(self, obj, ev):
        """桌宠改大小 / 换形象 / 显示出来时，把按钮重新摆到鱼的右上角。"""
        try:
            if obj is self.pet and ev.type() in (QEvent.Type.Resize, QEvent.Type.Show,
                                                QEvent.Type.LayoutRequest):
                if self._bubble is not None and self._bubble.isVisible():
                    self._bubble.reposition()
        except RuntimeError:
            self._bubble = None
        return False

    @property
    def busy(self):
        return self._busy

    def _flyout(self):
        return (getattr(self.pet, "ext", {}) or {}).get("flyout")

    def _system(self):
        """人格：设置里改过就用改过的，没改过用内置的。

        内置那段（`SYSTEM_PROMPT`）是"默认人格"，用户可以在
        设置 → 聊天 → 人格 里整段替换掉；存 `cfg["chat_persona"]`。
        """
        custom = str(self.pet.cfg.get("chat_persona") or "").strip()
        return custom or SYSTEM_PROMPT

    def _key(self):
        try:
            return self.pet._api_key()
        except Exception:
            return (self.pet.cfg.get("ds_api_key") or "").strip()

    # ------------------------------------------------------------------ 打开
    def open(self, circle_rect=None, anchor_y=None):
        """打开聊天浮窗。

        `circle_rect` 给了就**从那个圆长成整块板子**（右上角按钮那条路），
        不给就走老路（右键菜单：从旁边滑出来）。
        """
        fly = self._flyout()
        if fly is None:
            self.pet.say("侧边浮窗没起来（pet_ext/flyout.py 加载失败？）", seconds=4.0, again=True)
            return None
        self._hook_flyout(fly)
        fly.set_send_handler(self.send)
        fly.set_clear_handler(self.clear_history)
        fly.set_title("和她聊聊")
        # 派活那排「Codex / DSH / 只打开」只在拖文件时才有 —— 正常打开聊天框必须清掉，
        # 否则聊着天还杵着一排派活按钮（主人 2026-10-26 提的）。
        fly.set_subtitle("")
        fly.set_quick_actions([])
        fly.set_status("")            # 切到聊天：把派活那行「● Codex 正在跑」收起来
        fly.set_mode("chat")
        fly.set_busy(self._busy)
        if self._bubble is not None:
            self._bubble.hide()
        # 板子刚被派活 `clear()` 过 → 把 history 重画上去。不重画的话模型记得、
        # 界面上却是空的（主人说的"她记得但我看不见"）。
        if fly.message_count() == 0:
            self._render_history(fly)
        if circle_rect is not None:
            win = fly.show_from_circle(circle_rect, title="和她聊聊", anchor_y=anchor_y)
        else:
            win = fly.show(title="和她聊聊", anchor_y=anchor_y)
        self._flyout_open = True      # 记下来：板子开着的时候圆按钮不许冒出来
        if fly.message_count() == 0 and not self._opened_once:
            self._opened_once = True
            if not self._key():
                fly.add("note", "还没配 Sub2API 节点 Key：设置 → 余额和用量 → 设置 Key。"
                                "配好再说话就能聊了。")
            else:
                fly.add("note", "在这儿跟她说话吧，回车发送。（右上角那个键清空对话）")
        return win

    def open_from(self, btn):
        """圆形按钮被点了：从按钮的位置长成整块板子。"""
        rect = btn.global_rect()
        # 尖角指按钮中心；窗口动画也从按钮中心出发
        return self.open(circle_rect=rect, anchor_y=rect.center().y())

    # ------------------------------------------------------------------ 发送
    def send(self, text):
        """浮窗按回车时调（**主线程**）。"""
        text = (text or "").strip()
        if not text or self._busy:
            return
        fly = self._flyout()
        key = self._key()
        if not key:
            if fly is not None:
                fly.add("note", "还没配 Sub2API 节点 Key：设置 → 余额和用量 → 设置 Key")
            return

        self._busy = True
        living = getattr(self.pet, "ext", {}).get("living")
        if living is not None:
            living.touch()
        self._remember("user", text)          # 先记下这句，历史才是一问一答配对
        if fly is not None:
            fly.set_busy(True)
        self._play_thinking()
        model = current_model(self.pet.cfg)
        threading.Thread(target=self._worker, args=(text, key, model), daemon=True).start()

    def _worker(self, text, key, model=DS_MODEL):
        """**worker 线程**：只发请求 + emit，别碰 UI。"""
        msgs = [{"role": "system", "content": self._system()}]
        # ⚠️ 这句在 `send()` 里已经 `_remember` 进 history 了，**这里不能再 append 一次**：
        # 原来两处都加，模型每次收到两条一模一样的用户消息（白烧 token，回答也容易重复）。
        # 只在"历史末尾不是它"时才补 —— 比如刚点过「清空记忆」，那句只存在于本地变量里。
        hist = list(self.history[-self.history_limit():])
        if not hist or hist[-1].get("role") != "user" or hist[-1].get("content") != text:
            hist.append({"role": "user", "content": text})
        msgs.extend(hist)
        payload = {"model": model, "messages": msgs,
                   "max_tokens": DS_MAX_TOKENS, "temperature": 0.9}
        try:
            data = post_json(DS_URL, payload, key)
            try:
                reply = (data["choices"][0]["message"]["content"] or "").strip()
            except (KeyError, IndexError, TypeError):
                raise ChatError("返回里没有 choices/message，格式不对")
            if not reply:
                raise ChatError("她这次什么都没说（返回空）")
            self.reply_ready.emit(reply)
        except ChatError as exc:
            self.failed.emit(str(exc))
        except Exception as exc:                  # 兜底：别让线程静默死掉
            self.failed.emit(f"出了个没预料到的错：{type(exc).__name__}: {exc}")

    def _on_reply(self, reply):
        """**主线程**：记历史 + 往浮窗塞 + 桌宠冒个短的。"""
        self._busy = False
        self._remember("assistant", reply)
        fly = self._flyout()
        if fly is not None:
            # 等回复的这几十秒里，你可能已经拖文件切到派活面板了（共用一块板子）。
            # 这时**别把回复插进派活面板** —— 下次打开聊天会从 history 重绘出来。
            if getattr(fly, "mode", "") == "chat":
                fly.add("her", reply)
            fly.set_busy(False)
        self._say_short(reply)

    def _on_failed(self, msg):
        self._busy = False
        fly = self._flyout()
        if fly is not None:
            fly.add("note", msg)
            fly.set_busy(False)
        self.pet.say("刚刚没连上，看旁边", seconds=3.5, again=True)

    def _remember(self, role, content):
        self.history.append({"role": role, "content": content})
        limit = self.history_limit()
        if len(self.history) > limit:
            self.history = self.history[-limit:]

    def history_limit(self):
        """记忆上限（条）。设置里能选 20~100，默认 40。

        ⚠️ 必须**夹住**：配置文件是能手改的，塞个 100000 进去上下文就爆了
        —— 主人 2026-10-26 担心的"一直记下去会被撑爆"就是这个。
        """
        try:
            n = int(self.pet.cfg.get("chat_memory_max") or HISTORY_MAX)
        except (TypeError, ValueError):
            n = HISTORY_MAX
        return max(2, min(max(MEMORY_CHOICES), n))

    def clear_history(self):
        self.history = []

    def _render_history(self, fly):
        """把 `self.history` 重新铺到浮窗里。

        什么时候会用到：派活面板会 `fly.clear()`（每次派活从空白开始），之后你再点圆按钮
        打开聊天 —— 不重画的话，模型记得你们聊过什么、屏幕上却一条都没有。

        ⚠️ `animate=False`：十几条一起淡入 = 十几个 `QGraphicsOpacityEffect` 同时跑，
        既卡又像"历史在一条条往外冒"。条数也限了 60，设成 100 条时全铺会顿一下。
        """
        rows = list(self.history or [])[-60:]
        hidden = max(0, len(self.history) - len(rows))
        if hidden:
            fly.add("note", f"（更早的 {hidden} 条不铺开显示，她还记着）", animate=False)
        for item in rows:
            if isinstance(item, dict):
                role, text = item.get("role"), item.get("content")
            elif isinstance(item, (tuple, list)) and len(item) == 2:
                role, text = item          # 老格式：(角色, 正文)
            else:
                continue
            text = str(text or "").strip()
            if not text:
                continue
            fly.add("me" if role == "user" else "her", text, animate=False)

    # ------------------------------------------------------------------ 小动作
    def _say_short(self, reply):
        """头顶气泡只报个短的（长内容在浮窗里，别把气泡撑爆）。"""
        one = " ".join((reply or "").split())
        if len(one) > BUBBLE_CHARS:
            one = one[:BUBBLE_CHARS] + "…"
        try:
            self.pet.say(one or "回你了，看旁边", seconds=4.5, again=True)
        except Exception:
            pass

    def _play_thinking(self):
        """她"正在想"的时候播一下「深度思考」（只有灵动版有这段素材）。"""
        try:
            # ⚠️ `SKIN_ANIM` 是 桌宠.py 的**模块常量**，不是 PetWindow 的属性 ——
            # 写 `getattr(self.pet, "SKIN_ANIM", None)` 永远拿到 None，这段就白写了。
            from .anim import ANIM_SKIN
            if self.pet.skin != ANIM_SKIN:
                return
            _anim = (getattr(self.pet, "ext", {}) or {}).get("anim")
            if _anim is not None and "thinking" in (_anim.player.clips() or []):
                self.pet._play_anim_clip("thinking")
        except Exception:
            pass


def setup(pet):
    return ChatExtension(pet).start()
