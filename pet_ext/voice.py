"""本地语音：按消息类型控制朗读，心声默认保持安静。"""
from collections import deque
from functools import wraps
import json
import math
from pathlib import Path
import re
import sys
import uuid

from PySide6.QtCore import QObject, QProcess, QProcessEnvironment, QTimer, QUrl, Signal
from PySide6.QtMultimedia import QAudioOutput, QMediaDevices, QMediaPlayer
from PySide6.QtWidgets import QApplication

DEVELOPMENT_RUNTIME = Path('I:/dafeiyu-voice')
MODELS = [('trained', '大肥鱼 · 训练版'), ('baseline', '大肥鱼 · 底模对照')]
VOICE_TYPES = [
    ('chat', '聊天回复', '聊天窗口里的新回复', True),
    ('daily', 'AI 日常陪伴与闲聊', '情绪陪伴、本地日常台词和自动语录', True),
    ('inner', '心声', '标记为心声或整句括号包裹的气泡，默认不读', False),
    ('interaction', '点击与拖拽回嘴', '点击、双击互动台词及拖拽反应', True),
    ('feed', '喂食反馈', '投喂食物后的回应', True),
    ('notify', '任务通知', '任务完成等通知气泡，不影响提示音', True),
    ('bubble', '其他提示', '系统提醒、应用联动、天气和操作反馈等气泡', True),
]


def spoken_text(text):
    if not isinstance(text, str):
        return ''
    text = re.sub(r'```.*?```', '', text, flags=re.S)
    text = re.sub(r'!\[[^\]]*\]\([^)]*\)', '', text)
    text = re.sub(r'\[([^\]]+)\]\([^)]*\)', r'\1', text)
    text = re.sub(r'https?://\S+', '', text)
    text = re.sub(r'(?m)^\s{0,3}(?:#{1,6}\s+|[-*+]\s+|>\s*)', '', text)
    return re.sub(r'\s+', ' ', text.replace('`', '').replace('**', '')).strip()


def bubble_spoken_text(text, inner=False):
    if inner or not isinstance(text, str):
        return ''
    text = text.strip()
    # 括号覆盖整条气泡时属于心声；一句话中正常使用括号仍保留。
    if text.startswith(('（', '(')):
        stack = []
        for index, char in enumerate(text):
            if char in '（(':
                stack.append('）' if char == '（' else ')')
            elif char in '）)':
                if not stack or char != stack.pop():
                    break
                if not stack:
                    if index == len(text) - 1:
                        return ''
                    break
    return spoken_text(text)


def runtime_problem(root, model='trained'):
    from .voice_paths import weights
    root = Path(root)
    if model not in dict(MODELS):
        return '请选择列表中的语音模型'
    required = [voice_python(root), root / 'GPT-SoVITS/runtime/ffmpeg.exe',
                root / 'dataset/train/audio/dwg_0031.wav', *weights(root, model)]
    if not all(p.is_file() for p in required):
        return '语音环境或模型不完整，请选择已准备好的语音目录'
    return ''


def bundled_runtime():
    if getattr(sys, 'frozen', False):
        return Path(sys.executable).resolve().parent / 'voice_runtime'
    return DEVELOPMENT_RUNTIME


def voice_python(root):
    root = Path(root)
    portable = root / 'python/python.exe'
    return portable if portable.is_file() else root / 'env/Scripts/python.exe'


class Voice(QObject):
    changed = Signal(str)

    def __init__(self, pet):
        super().__init__(pet)
        self.pet = pet
        self.status = '已关闭'
        self._process = None
        self._buffer = b''
        self._ready = False
        self._active = None
        self._serial = 0
        self._file = None
        self._pending = deque(maxlen=6)
        self._chat_bubble_depth = 0
        self._source_context = None
        self._queued_sources = {}
        self.audio = QAudioOutput(self)
        self.player = QMediaPlayer(self)
        self.player.setAudioOutput(self.audio)
        self.audio.setVolume(self.volume())
        # QAudioOutput 会保留创建时的设备，后插耳机不会自行跟随系统默认输出。
        self.devices = QMediaDevices(self)
        self.devices.audioOutputsChanged.connect(self._sync_audio_device)
        self.device_timer = QTimer(self)
        self.device_timer.setInterval(1000)
        self.device_timer.timeout.connect(self._sync_audio_device)
        self.device_timer.start()
        self.player.mediaStatusChanged.connect(self._media_status)
        self.player.errorOccurred.connect(lambda *args: self._play_error())
        self.idle = QTimer(self)
        self.idle.setSingleShot(True)
        self.idle.timeout.connect(self._release)
        self.deadline = QTimer(self)
        self.deadline.setSingleShot(True)
        self.deadline.timeout.connect(self._timeout)
        if self.enabled():
            self.status = runtime_problem(self.root(), self.model()) or '就绪，等待新的话语'
        app = QApplication.instance()
        if app is not None:
            app.aboutToQuit.connect(self.shutdown)

    def enabled(self):
        return bool(self.pet.cfg.get('voice_enabled', False))

    def type_enabled(self, source):
        defaults = {key: default for key, _, _, default in VOICE_TYPES}
        return bool(self.pet.cfg.get('voice_type_' + source, defaults.get(source, True)))

    def root(self):
        return Path(self.pet.cfg.get('voice_runtime') or bundled_runtime())

    def model(self):
        return self.pet.cfg.get('voice_model', 'trained')

    def volume(self):
        try:
            value = float(self.pet.cfg.get('voice_volume', 0.8))
            return max(0., min(1., value)) if math.isfinite(value) else 0.8
        except (TypeError, ValueError):
            return 0.8

    def _status(self, text):
        self.status = text
        self.changed.emit(text)

    def _sync_audio_device(self):
        device = QMediaDevices.defaultAudioOutput()
        if not device.isNull() and self.audio.device().id() != device.id():
            self.audio.setDevice(device)

    def configure(self, key, value):
        if key not in ('voice_enabled', 'voice_model', 'voice_volume', 'voice_runtime') and key not in {
                'voice_type_' + source for source, _, _, _ in VOICE_TYPES}:
            raise ValueError('未知语音设置')
        if key == 'voice_model' and value not in dict(MODELS):
            raise ValueError('未知语音模型')
        if key == 'voice_runtime' and runtime_problem(value, self.model()):
            self._status(runtime_problem(value, self.model()))
            return
        if key != 'voice_volume':
            self.stop()
        self.pet.cfg[key] = value
        self.pet.save_config()
        self.audio.setVolume(self.volume())
        if key != 'voice_volume':
            self._status((runtime_problem(self.root(), self.model()) or '就绪，等待新的话语')
                         if self.enabled() else '已关闭')

    def _auto_allowed(self):
        if not self.enabled():
            return False
        return (self.pet.isVisible() and not getattr(self.pet, '_fs_now', False)
                and not getattr(self.pet, '_auto_silent', False) and self.pet.quiet_left() <= 0)

    def _chat_allowed(self):
        if not self._auto_allowed():
            return False
        chat = self.pet.ext.get('chat')
        fly = chat._flyout() if chat is not None else None
        if fly is None or getattr(fly, 'mode', '') != 'chat':
            return False
        if not getattr(chat, '_flyout_open', False):
            return False
        return True

    def on_chat_reply(self, text):
        if self._chat_allowed() and self.type_enabled('chat'):
            self._pending.clear()
            self.speak(text)

    def on_bubble(self, text, inner=False, source='bubble'):
        if self._chat_bubble_depth or not self._auto_allowed():
            return
        if inner or (isinstance(text, str) and text.strip() and not bubble_spoken_text(text)):
            source = 'inner'
        if not self.type_enabled(source):
            return
        text = spoken_text(text) if source == 'inner' else bubble_spoken_text(text, inner)
        if not text:
            return
        if self._active is not None or self._file is not None:
            self._pending.append((text, source))
        else:
            self.speak(text, source=source)

    def _next_bubble(self):
        if not self._auto_allowed():
            self._pending.clear()
            return
        while self._pending and self._active is None and self._file is None:
            text, source = self._pending.popleft()
            if self.type_enabled(source):
                self.speak(text, source=source)
                break

    def bubble_source(self, idle=False):
        if self._source_context:
            return self._source_context
        # 只检查调用来源，不按台词关键词猜测，改写台词后分类仍然有效。
        frame = sys._getframe(1)
        try:
            for _ in range(12):
                if frame is None:
                    break
                module = frame.f_globals.get('__name__', '')
                name = frame.f_code.co_name
                if module == 'pet_ext.living' and name == '_finish':
                    return 'daily'
                if module == 'pet_ext.notify':
                    return 'notify'
                if module == 'pet_ext.companion' and name == 'feed':
                    return 'feed'
                if name in ('_on_single_click', '_on_double_click', 'mouseReleaseEvent'):
                    return 'interaction'
                frame = frame.f_back
        finally:
            del frame
        return 'daily' if idle else 'bubble'

    def install_bubble_hook(self):
        original = self.pet.say

        @wraps(original)
        def say(text, inner=False, seconds=2.8, again=False, idle=False, queue=False):
            source = self.bubble_source(idle)
            before = (getattr(self.pet, 'bubble_text', None), getattr(self.pet, 'bubble_until', None))
            result = original(text, inner=inner, seconds=seconds, again=again, idle=idle, queue=queue)
            after = (getattr(self.pet, 'bubble_text', None), getattr(self.pet, 'bubble_until', None))
            if queue and after == before:
                self._queued_sources[(text, inner)] = source
                if len(self._queued_sources) > 32:
                    self._queued_sources.pop(next(iter(self._queued_sources)))
            # 原版去重或排队时尚未冒泡，等真正显示时再读。
            if after != before and after[0] == (f'（{text}）' if inner else text):
                source = self._queued_sources.pop((text, inner), source)
                self.on_bubble(text, inner, source)
            return result
        self.pet.say = say
        defer = getattr(self.pet, '_defer_single_line', None)
        if defer is not None:
            def defer_line(callback):
                def speak_later():
                    old = self._source_context
                    self._source_context = 'interaction'
                    try:
                        return callback()
                    finally:
                        self._source_context = old
                return defer(speak_later)
            self.pet._defer_single_line = defer_line

    def speak(self, text, preview=False, source='chat'):
        if not preview and (not self.enabled() or not self.type_enabled(source)):
            return False
        text = spoken_text(text)
        if not text:
            return False
        if len(text) > 2000:
            self._status('回复超过 2000 字，本次语音已跳过')
            return False
        problem = runtime_problem(self.root(), self.model())
        if problem:
            self._status(problem)
            return False
        # 新回复替代旧请求，防止关闭、换模型后还播出过期声音。
        if self._active is not None:
            self.stop()
        self.idle.stop()
        self.player.stop()
        self.player.setSource(QUrl())
        self._remove_file()
        self._serial += 1
        output = self.root() / 'cache/pet_voice' / f'{uuid.uuid4().hex}.wav'
        self._active = {'id': self._serial, 'model': self.model(), 'text': text,
                        'output': str(output), 'preview': preview, 'source': source}
        self._status('正在准备语音…首次加载可能需要几十秒')
        # CPU 机器首次载入和长句合成会明显慢于 CUDA，给足十分钟。
        self.deadline.start(600000)
        if self._process is None:
            self._start()
        elif self._ready:
            self._send()
        return True

    def preview(self):
        return self.speak('主人，语音已经准备好啦。今天也辛苦你了，记得喝点水。', preview=True)

    def _start(self):
        root = self.root().resolve()
        (root / 'logs').mkdir(parents=True, exist_ok=True)
        process = QProcess(self)
        self._process = process
        self._buffer = b''
        self._ready = False
        env = QProcessEnvironment.systemEnvironment()
        for key, value in {'TEMP': root / 'tmp', 'TMP': root / 'tmp',
                           'PYTHONPYCACHEPREFIX': root / 'cache/pycache',
                           'PYTHONIOENCODING': 'utf-8', 'PYTHONUTF8': '1'}.items():
            env.insert(key, str(value))
        process.setProcessEnvironment(env)
        process.setWorkingDirectory(str(root))
        process.setStandardErrorFile(str(root / 'logs/pet-voice.log'))
        process.readyReadStandardOutput.connect(lambda: self._read(process))
        process.finished.connect(lambda *args: self._finished(process))
        process.errorOccurred.connect(lambda *args: self._process_error(process))
        worker = Path(__file__).with_name('voice_worker.py')
        process.start(str(voice_python(root)), ['-u', str(worker), '--runtime', str(root)])

    def _send(self):
        if self._active is not None:
            request = {k: v for k, v in self._active.items() if k not in ('preview', 'source')}
            self._process.write((json.dumps(request, ensure_ascii=False) + '\n').encode('utf-8'))

    def _read(self, process):
        if process is not self._process:
            return
        self._buffer += bytes(process.readAllStandardOutput())
        while b'\n' in self._buffer:
            line, self._buffer = self._buffer.split(b'\n', 1)
            try:
                self._message(json.loads(line))
            except (ValueError, TypeError, KeyError):
                self._status('语音进程返回格式错误，请重试')

    def _message(self, message):
        event = message.get('event')
        if event == 'ready':
            self._ready = True
            self._send()
            return
        job = self._active
        if job is None or message.get('id') != job['id']:
            return
        if event in ('loading', 'generating'):
            self._status('正在加载语音模型…' if event == 'loading' else '正在生成语音…')
        elif event == 'error':
            self.deadline.stop()
            Path(job['output']).unlink(missing_ok=True)
            self._active = None
            self._status('语音生成失败：' + str(message.get('message', '请查看语音日志')))
            self.idle.start(60000)
            QTimer.singleShot(0, self._next_bubble)
        elif event == 'result':
            self.deadline.stop()
            path = Path(message['path'])
            if path != Path(job['output']) or not path.is_file():
                self.stop()
                self._status('语音文件缺失，请重试')
                return
            self._active = None
            source = job.get('source', 'chat')
            allowed = (self._chat_allowed() if source == 'chat' else self._auto_allowed()) and self.type_enabled(source)
            if not job['preview'] and not allowed:
                path.unlink(missing_ok=True)
                self._status('已跳过朗读：聊天已关闭或当前处于免打扰状态')
                self.idle.start(60000)
                QTimer.singleShot(0, self._next_bubble)
                return
            self._file = path
            self._sync_audio_device()
            self.player.setSource(QUrl.fromLocalFile(str(path)))
            self.player.play()
            self._status('正在播放语音')

    def _media_status(self, status):
        if status == QMediaPlayer.MediaStatus.EndOfMedia:
            self.player.setSource(QUrl())
            self._remove_file()
            self._status('就绪，等待新的话语' if self.enabled() else '试听结束，自动语音仍关闭')
            self.idle.start(60000)
            QTimer.singleShot(0, self._next_bubble)

    def _play_error(self):
        error = self.player.errorString()
        self.player.stop()
        self.player.setSource(QUrl())
        self._remove_file()
        self._status('声音播放失败：' + error)
        self.idle.start(60000)
        QTimer.singleShot(0, self._next_bubble)

    def _process_error(self, process):
        if process is self._process:
            error = process.errorString()
            self.stop()
            self._status('语音进程启动或运行失败：' + error)
            if process.state() == QProcess.ProcessState.NotRunning:
                process.deleteLater()

    def _timeout(self):
        self.stop()
        self._status('语音生成超过十分钟，已停止；可缩短文字或检查语音日志')

    def _finished(self, process):
        if process is self._process:
            self._process = None
            self._ready = False
            if self._active is not None:
                self.deadline.stop()
                Path(self._active['output']).unlink(missing_ok=True)
                self._active = None
                self._status('语音进程已退出，请重试；详情见语音日志')
        process.deleteLater()

    def _remove_file(self):
        if self._file is not None:
            try:
                self._file.unlink(missing_ok=True)
            except OSError:
                pass
            self._file = None

    def _release(self):
        process, self._process = self._process, None
        self._ready = False
        if process is not None:
            process.kill()

    def stop(self):
        self._serial += 1
        self._pending.clear()
        if self._active is not None:
            Path(self._active['output']).unlink(missing_ok=True)
        self._active = None
        self.deadline.stop()
        self.idle.stop()
        self.player.stop()
        self.player.setSource(QUrl())
        self._remove_file()
        self._release()
        self._status('已停止')

    def shutdown(self):
        self.device_timer.stop()
        process = self._process
        self.stop()
        if process is not None:
            process.waitForFinished(2000)


def setup(pet):
    ext = Voice(pet)
    ext.install_bubble_hook()
    # 加载器在全部 setup 后才赋 pet.ext，稍后连接聊天；缩略气泡和完整回复只读一次。
    def connect_chat():
        chat = getattr(pet, 'ext', {}).get('chat')
        if chat is not None:
            original = chat._say_short
            @wraps(original)
            def short_reply(*args, **kwargs):
                suppress = ext._chat_allowed() or not ext.type_enabled('chat')
                if suppress:
                    ext._chat_bubble_depth += 1
                try:
                    return original(*args, **kwargs)
                finally:
                    if suppress:
                        ext._chat_bubble_depth -= 1
            chat._say_short = short_reply
            chat.reply_ready.connect(ext.on_chat_reply)
    QTimer.singleShot(0, connect_chat)
    return ext
