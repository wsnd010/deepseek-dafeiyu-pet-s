"""语音设置，复用桌宠设置页的控件与布局。"""
from PySide6.QtCore import QObject, Qt
from PySide6.QtWidgets import QFileDialog

from .voice import MODELS, VOICE_TYPES


class VoiceSettings(QObject):
    def __init__(self, page, pet):
        super().__init__(page)
        from ui_console import Switch
        self.voice = getattr(pet, 'ext', {}).get('voice')
        card = page.card('桌宠语音', '让她亲口说给你听', 'nav.sound')
        page.hint(card, '总开关开启后，只朗读下方勾选的消息类型；关闭声音不会隐藏文字。')
        if self.voice is None:
            page.hint(card, '语音模块未加载，请重启桌宠后重试。')
            return
        voice = self.voice
        self.toggle = Switch(voice.enabled(), lambda value: voice.configure('voice_enabled', value))
        page.row(card, '启用语音', '默认关闭；隐藏、全屏或免打扰时不自动朗读', self.toggle)
        self.model = page.combo(card, '语音模型', '训练版为本次训练的大肥鱼声音',
                                MODELS, voice.model(), lambda value: voice.configure('voice_model', value))
        self.model.setAccessibleName('语音模型')
        page.slider(card, '语音音量', '独立于点击音效和任务提示音', 0, 100,
                    round(voice.volume() * 100), '%', lambda value: voice.configure('voice_volume', value / 100))
        buttons = page.buttons(card, [('试听', voice.preview, 'primary', 'page.volume-high'),
                                      ('停止', voice.stop, None, 'ui.close')])
        self.preview_button, self.stop_button = buttons.buttons
        self.status = page.hint(card, voice.status)
        self.status.setTextFormat(Qt.TextFormat.PlainText)
        voice.changed.connect(self.refresh)
        categories = page.card('哪些消息要朗读', '各类独立控制，心声默认关闭', 'nav.sound')
        self.type_switches = {}
        for source, label, hint, _default in VOICE_TYPES:
            switch = Switch(voice.type_enabled(source),
                            lambda value, key=source: voice.configure('voice_type_' + key, value))
            self.type_switches[source] = switch
            page.row(categories, label, hint, switch)
        page.hint(categories, '觉得太频繁，可以关闭「AI 日常陪伴与闲聊」和「点击与拖拽回嘴」。修改开关会停止当前朗读并清空待播语音。试听不受这些开关限制。')
        directory = page.card('本地语音', '在本机生成声音', 'nav.sound')
        self.path = page.hint(directory, str(voice.root()))
        self.path.setTextFormat(Qt.TextFormat.PlainText)
        page.buttons(directory, [('选择语音目录…', self.choose_directory, None, 'ui.folder')])
        page.hint(directory, '自动使用 NVIDIA 显卡；没有独显时改用 CPU（会慢很多）。首次加载可继续聊天；停止或空闲一分钟会释放模型。关闭自动语音后仍可试听。')
        self.refresh(voice.status)

    def refresh(self, status):
        self.status.setText(status)
        busy = self.voice._active is not None
        self.preview_button.setEnabled(not busy)
        self.stop_button.setEnabled(busy or self.voice._file is not None or self.voice._process is not None)

    def choose_directory(self):
        folder = QFileDialog.getExistingDirectory(self.parent(), '选择已准备好的语音目录', str(self.voice.root()))
        if folder:
            self.voice.configure('voice_runtime', folder)
            self.path.setText(str(self.voice.root()))
