"""验证语音触发边界、取消、过期结果与配置，不调用 GPU。"""
from pathlib import Path
import tempfile
from types import SimpleNamespace
from unittest.mock import Mock, patch

from PySide6.QtCore import QObject, Signal
from PySide6.QtWidgets import QApplication
from PySide6.QtMultimedia import QMediaDevices
from pet_ext.voice import (Voice, setup, spoken_text, bubble_spoken_text,
                           runtime_problem, voice_python)


class Chat(QObject):
    reply_ready = Signal(str)

    def __init__(self, pet):
        super().__init__()
        self._flyout_open = True
        self.panel = SimpleNamespace(mode='chat')
        self.pet = pet
        self.reply_ready.connect(self._on_reply)

    def _say_short(self, text):
        self.pet.say(text[:12], again=True)

    def _on_reply(self, text):
        self._say_short(text)

    def _flyout(self):
        return self.panel


def run_checks():
    app = QApplication.instance() or QApplication([])
    pet = QObject()
    pet.cfg = {}
    pet.save_config = Mock()
    pet.quiet_left = lambda: 0
    pet.isVisible = lambda: True
    pet.bubble_text = ''
    pet.bubble_until = 0
    pet.pending = []
    def say(text, inner=False, seconds=2.8, again=False, idle=False, queue=False):
        if idle and text == pet.bubble_text and not again:
            return
        if queue:
            pet.pending.append((text, inner))
            return
        pet.bubble_text = f'（{text}）' if inner else text
        pet.bubble_until += 1
    pet.say = say
    chat = Chat(pet)
    pet.ext = {'chat': chat}
    voice = setup(pet)
    pet.ext['voice'] = voice
    app.processEvents()
    assert not voice.enabled()
    assert spoken_text('## 标题\n**你好** [主人](https://a.cn)\n```python\nabc\n```') == '标题 你好 主人'
    assert runtime_problem('C:/voice')
    with tempfile.TemporaryDirectory() as folder:
        root = Path(folder)
        portable = root / 'python'
        portable.mkdir()
        (portable / 'python.exe').write_bytes(b'')
        assert voice_python(root) == portable / 'python.exe'
    for line in ('（打了个哈欠）', '(看看主人)', '（想了想（还是算了））'):
        assert not bubble_spoken_text(line)
    assert not bubble_spoken_text('没有写括号但标记为心声', inner=True)
    assert bubble_spoken_text('记得喝水（温水就好）') == '记得喝水（温水就好）'
    assert bubble_spoken_text('（嗯）记得喝水（温水就好）')
    with patch.object(voice, 'speak', return_value=True) as speak:
        chat.reply_ready.emit('关闭时不读')
        speak.assert_not_called()
        voice.configure('voice_enabled', True)
        chat.reply_ready.emit('新回复')
        speak.assert_called_once_with('新回复')
        speak.reset_mock()
        pet.say('普通气泡')
        speak.assert_called_once_with('普通气泡', source='bubble')
        speak.reset_mock()
        pet.say('没有括号的心声', inner=True)
        pet.say('（心声）')
        pet.say('(心声)')
        speak.assert_not_called()
        pet.say('提醒喝水', queue=True)
        speak.assert_not_called()
        line, inner = pet.pending.pop()
        pet.say(line, inner=inner)
        speak.assert_called_once_with('提醒喝水', source='bubble')
        speak.reset_mock()
        pet.say('提醒喝水', idle=True)
        speak.assert_not_called()
        # 忙时排队，不能打断正在生成的声音；播完再开始下一条。
        voice._active = {'id': 1}
        pet.say('AI 情景对话的新话')
        pet.say('任务已经完成')
        speak.assert_not_called()
        assert list(voice._pending) == [('AI 情景对话的新话', 'bubble'), ('任务已经完成', 'bubble')]
        voice._active = None
        voice._next_bubble()
        speak.assert_called_once_with('AI 情景对话的新话', source='bubble')
        voice._pending.clear()
        speak.reset_mock()
        for attr in ('_auto_silent', '_fs_now'):
            setattr(pet, attr, True)
            chat.reply_ready.emit('不读')
            setattr(pet, attr, False)
        pet.isVisible = lambda: False
        chat.reply_ready.emit('隐藏不读')
        pet.isVisible = lambda: True
        chat._flyout_open = False
        chat.reply_ready.emit('历史或关闭窗口')
        speak.assert_called_once_with('历史或关闭窗口', source='bubble')
        speak.reset_mock()
        chat._flyout_open = True
        chat.panel.mode = 'dispatch'
        chat.reply_ready.emit('派活不读')
        speak.assert_called_once_with('派活不读', source='bubble')
        speak.reset_mock()
        chat.panel.mode = 'chat'
        pet.quiet_left = lambda: 30
        chat.reply_ready.emit('免打扰不读')
        speak.assert_not_called()
    pet.quiet_left = lambda: 0
    with tempfile.TemporaryDirectory(dir='I:/Codex/work') as folder:
        output = Path(folder) / 'voice.wav'
        output.touch()
        voice._active = {'id': 20, 'output': str(output), 'preview': False}
        with patch.object(voice.player, 'play') as play:
            voice._message({'event': 'result', 'id': 19, 'path': str(output)})
            assert voice._active is not None
            chat._flyout_open = False
            voice._message({'event': 'result', 'id': 20, 'path': str(output)})
            play.assert_not_called()
            assert not output.exists()
    with patch('pet_ext.voice.runtime_problem', return_value=''), patch.object(voice, '_start'):
        voice.configure('voice_enabled', False)
        assert voice.preview()
        assert voice._active['preview']
        voice.configure('voice_model', 'baseline')
        assert voice._active is None and not voice.deadline.isActive()
        assert voice.model() == 'baseline'
    voice.configure('voice_volume', .3)
    assert abs(voice.audio.volume() - .3) < .001
    default = QMediaDevices.defaultAudioOutput()
    other = next((d for d in QMediaDevices.audioOutputs() if d.id() != default.id()), None)
    if other is not None:
        voice.audio.setDevice(other)
        voice.devices.audioOutputsChanged.emit()
        assert voice.audio.device().id() == default.id()
        voice.audio.setDevice(other)
        voice.device_timer.timeout.emit()
        assert voice.audio.device().id() == default.id()
    voice.shutdown()
    assert not voice.device_timer.isActive()
    print('通过：语音默认关闭，普通/提醒/AI 情景气泡朗读，括号和心声静音，聊天不重读缩略气泡，气泡实际显示才读、忙时排队、隐藏/全屏/免打扰避让、过期结果丢弃、取消和音量。')
    print('通过：输出设备变更信号与轮询均跟随系统默认设备，退出停止轮询。')


if __name__ == '__main__':
    run_checks()
