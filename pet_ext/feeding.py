# -*- coding: utf-8 -*-
"""悬浮食物篮与现有动作组合，不改主程序的方法体。"""
import ctypes
from PySide6.QtCore import QObject, QTimer, Qt, QPoint, QSize, QRect, QEvent
from PySide6.QtGui import QColor, QPainter, QPen, QCursor, QIcon
from PySide6.QtWidgets import QFrame, QVBoxLayout, QHBoxLayout, QPushButton, QLabel, QToolButton, QApplication
from .chat import ChatCircle
from .companion import FOODS

COMBOS = {
    "开心连跳": ("jump", "jump", "jump"),
    "伸懒腰再摇摇": ("stretch", "sway"),
    "摇摇蹦一下": ("sway", "jump"),
    "活力三连": ("stretch", "sway", "jump"),
}
ICONS = {"小鱼干": "act.dove", "蛋糕": "act.snack", "棒棒糖": "act.icecream",
         "团子": "act.bubbles", "钻石": "act.rubik"}


def food_panel_rect(body, screen, size):
    """先试左右，再试上下；夹屏后按遮挡面积挑位置，支持负坐标副屏。"""
    w, h = size.width(), size.height()
    gap = 10
    cx, cy = body.center().x(), body.center().y()
    positions = [(body.right() + gap + 1, cy - h // 2),
                 (body.left() - gap - w, cy - h // 2),
                 (cx - w // 2, body.bottom() + gap + 1),
                 (cx - w // 2, body.top() - gap - h)]
    candidates = []
    for x, y in positions:
        x = max(screen.left(), min(x, screen.right() - w + 1))
        y = max(screen.top(), min(y, screen.bottom() - h + 1))
        rect = QRect(x, y, w, h)
        overlap = rect.intersected(body.adjusted(-gap, -gap, gap, gap))
        candidates.append((max(0, overlap.width()) * max(0, overlap.height()), rect))
    return min(candidates, key=lambda item: item[0])[1]


class FoodPanel(QFrame):
    """透明圆角食物条；不用 Qt 子菜单，避免旧有鼠标捕获问题。"""
    def __init__(self, owner):
        super().__init__(owner.pet, Qt.WindowType.Tool | Qt.WindowType.FramelessWindowHint
                         | Qt.WindowType.WindowStaysOnTopHint)
        self.owner = owner
        self.setAttribute(Qt.WidgetAttribute.WA_TranslucentBackground)
        self.setWindowTitle("大肥鱼食物篮")
        self.setStyleSheet("QLabel {color:#f4f6ff;background:transparent;}"
                           "QToolButton {color:#f4f6ff;background:rgba(255,255,255,12);"
                           "border:1px solid rgba(255,255,255,28);border-radius:10px;padding:5px;}"
                           "QToolButton:hover,QToolButton:focus {background:rgba(130,177,255,65);border-color:#a4c8ff;}"
                           "QPushButton {color:#cbd6ec;background:transparent;border:0;padding:4px;}"
                           "QPushButton:hover {color:white;background:rgba(255,255,255,30);border-radius:6px;}")
        layout = QVBoxLayout(self)
        layout.setContentsMargins(8, 7, 8, 8)
        layout.setSpacing(5)
        header = QHBoxLayout()
        header.addWidget(QLabel("喂食"))
        header.addStretch()
        close = QPushButton("×")
        close.setFixedSize(24, 24)
        close.setAccessibleName("收起食物篮")
        close.setToolTip("收起（Esc）")
        close.clicked.connect(self.hide)
        header.addWidget(close)
        layout.addLayout(header)
        row = QVBoxLayout()
        row.setSpacing(5)
        import ui_console
        for food in FOODS:
            button = QToolButton()
            button.setText(food)
            button.setAccessibleName("投喂" + food)
            button.setToolButtonStyle(Qt.ToolButtonStyle.ToolButtonTextBesideIcon)
            button.setIcon(QIcon(ui_console.icon_pixmap(ICONS[food], "#ffd59d", 22)))
            button.setIconSize(QSize(22, 22))
            button.setFixedSize(96, 40)
            button.clicked.connect(lambda checked=False, name=food: owner.feed(name))
            row.addWidget(button)
        layout.addLayout(row)
        # 顶层 adjustSize 会给扩展布局补到 200px；按内容尺寸固定，避免空白挡屏。
        self.setFixedSize(layout.sizeHint())
        self._user32 = ctypes.WinDLL("user32", use_last_error=True)
        self._user32.GetAsyncKeyState.argtypes = [ctypes.c_int]
        self._user32.GetAsyncKeyState.restype = ctypes.c_short
        self._pressed = False
        self.dismiss_timer = QTimer(self)
        self.dismiss_timer.setInterval(30)
        self.dismiss_timer.timeout.connect(self.check_outside)
        QApplication.instance().installEventFilter(self)

    def paintEvent(self, event):
        painter = QPainter(self)
        painter.setRenderHint(QPainter.RenderHint.Antialiasing)
        painter.setPen(QPen(QColor(177, 200, 240, 100), 1))
        painter.setBrush(QColor(27, 35, 52, 220))
        painter.drawRoundedRect(self.rect().adjusted(1, 1, -1, -1), 14, 14)

    def showEvent(self, event):
        self._pressed = self.mouse_down()
        self.dismiss_timer.start()
        super().showEvent(event)

    def hideEvent(self, event):
        self.dismiss_timer.stop()
        super().hideEvent(event)

    def mouse_down(self):
        return any(self._user32.GetAsyncKeyState(key) & 0x8000 for key in (1, 2, 4))

    def outside(self, point):
        return (not self.frameGeometry().contains(point)
                and not self.owner.circle.global_rect().contains(point))

    def check_outside(self):
        pressed = self.mouse_down()
        if pressed and not self._pressed and self.outside(QCursor.pos()):
            self.hide()
        self._pressed = pressed
        if self._user32.GetAsyncKeyState(0x1B) & 0x8000:
            self.hide()

    def eventFilter(self, obj, event):
        if self.isVisible():
            if event.type() == QEvent.Type.MouseButtonPress and self.outside(event.globalPosition().toPoint()):
                self.hide()
            elif event.type() == QEvent.Type.KeyPress and event.key() == Qt.Key.Key_Escape:
                self.hide()
                return True
        return False


class FoodCircle(ChatCircle):
    def apply_theme(self):
        super().apply_theme()
        import ui_console
        self._pix = ui_console.icon_pixmap("act.snack", self._fg, 17)
        self.setToolTip("打开食物篮")
        self.setAccessibleName("打开食物篮")

    def reposition(self):
        super().reposition()
        self.move(self.x(), min(self.parent().height() - self.height() - 2,
                                self.y() + self.height() + 8))


class Feeding(QObject):
    def __init__(self, pet):
        super().__init__(pet)
        self.pet = pet
        self.circle = FoodCircle(self)
        self.panel = FoodPanel(self)
        self.steps = []
        self.skin = None
        self.step_timer = QTimer(self)
        self.step_timer.setInterval(950)
        self.step_timer.timeout.connect(self.advance)
        original = pet._add_tease_menu
        def menu(m):
            sub = original(m)
            if pet.skin != "灵动大肥鱼":
                sub.addSeparator()
                for name, steps in COMBOS.items():
                    action = sub.addAction(name + "（组合）", lambda n=name: self.play(n))
                    action.setEnabled(not any(k in pet.cfg.get("actions_off", []) for k in steps))
            return sub
        pet._add_tease_menu = menu
        self.timer = QTimer(self)
        self.timer.timeout.connect(self.refresh)
        self.timer.start(200)
        self.refresh()

    def _tokens(self):
        import ui_console
        return ui_console.tokens()

    def refresh(self):
        visible = self.pet.isVisible() and self.pet.cfg.get("feed_bubble", True)
        self.circle.setVisible(visible)
        if visible:
            self.circle.reposition()
        else:
            self.panel.hide()
        if self.panel.isVisible():
            self.place_panel()

    def place_panel(self):
        local_body = self.pet.sprite_body_rect()
        body = local_body.toAlignedRect() if hasattr(local_body, 'toAlignedRect') else QRect(local_body)
        body.moveTopLeft(self.pet.mapToGlobal(body.topLeft()))
        body = body.united(self.circle.global_rect())
        chat = self.pet.ext.get('chat')
        bubble = getattr(chat, 'bubble', None)
        if bubble is not None and bubble.isVisible():
            body = body.united(bubble.global_rect())
        geo = self.pet.screen().availableGeometry()
        rect = food_panel_rect(body, geo, self.panel.size())
        if self.panel.pos() != rect.topLeft():
            self.panel.move(rect.topLeft())

    def open_from(self, circle):
        if self.panel.isVisible():
            self.panel.hide()
            return
        self.panel.adjustSize()
        self.place_panel()
        self.panel.show()
        self.panel.raise_()

    def feed(self, name):
        companion = self.pet.ext.get("companion")
        if companion is not None:
            companion.feed(name)
        self.panel.hide()

    def play(self, name):
        self.steps = list(COMBOS[name])
        self.skin = self.pet.skin
        self.advance()
        if self.steps:
            self.step_timer.start()

    def advance(self):
        if self.pet.skin != self.skin or getattr(self.pet, "dragging", False):
            self.steps.clear()
        if not self.steps:
            self.step_timer.stop()
            return
        self.pet.play_action(self.steps.pop(0))


def setup(pet):
    return Feeding(pet)
