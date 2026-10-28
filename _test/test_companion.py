# -*- coding: utf-8 -*-
"""互动扩展回归：日志增量、阈值与冷却、投喂、立绘回退。"""
import json
from pathlib import Path
import tempfile
from unittest.mock import Mock

from PySide6.QtGui import QPixmap
from PySide6.QtWidgets import QApplication, QWidget

from pet_ext.companion import CodexStatus, Companion, FOODS, event_state


class FakePet(QWidget):
    def __init__(self):
        super().__init__()
        self.cfg = {}
        self.skin = "大肥鱼"
        self.cur_h = 180
        self.ext = {}
        self.sprites = {("正面", 180): QPixmap(180, 180)}
        self.say = Mock()
        self.play_action = Mock()
        self.save_config = Mock()
        self._sprite_key = lambda: ("正面", 180, 1)
        self._music_playing = lambda: False

    def set_skin(self, skin):
        self.skin = skin


def run_checks():
    app = QApplication.instance() or QApplication([])
    def event(kind):
        return {"type": "event_msg", "payload": {"type": kind}}
    assert event_state(event("task_started")) == "start"
    assert event_state(event("task_complete")) == "done"
    assert event_state(event("turn_aborted")) == "idle"
    assert event_state({"type": "response_item", "payload": {"type": "function_call", "name": "apply_patch"}}) == "tool_edit"
    with tempfile.TemporaryDirectory() as root:
        folder = Path(root) / "sessions" / "2026"
        folder.mkdir(parents=True)
        log = folder / "rollout-test.jsonl"
        log.write_text(json.dumps(event("task_started")) + "\n", encoding="utf-8")
        watcher = CodexStatus([Path(root)])
        assert watcher.poll() == "start"
        assert watcher.poll() == "start"
        with log.open("a", encoding="utf-8") as output:
            output.write(json.dumps(event("task_complete")) + "\n")
        assert watcher.poll() == "done"
        log.write_text(json.dumps(event("turn_aborted")) + "\n", encoding="utf-8")
        assert watcher.poll() == "idle"
    pet = FakePet()
    ext = Companion(pet)
    ext.timer.stop()
    ext._apply({"cpu": 89, "memory": 94, "gpu": 79}, "idle", "")
    assert pet.say.call_count == 0
    ext._apply({"cpu": 90, "memory": 95, "gpu": 80}, "idle", "")
    assert pet.say.call_count == 3
    ext._apply({"cpu": 99, "memory": 99, "gpu": 99}, "idle", "")
    assert pet.say.call_count == 3
    for food in FOODS:
        ext.last_feed = 0
        ext.feed(food)
    assert pet.cfg["feed_count"] == 5
    ext.feed("小鱼干")
    assert pet.cfg["feed_count"] == 5
    pet.skin = "灵动大肥鱼"
    ext.set_option("companion_portraits", True)
    assert pet.skin == "大肥鱼"
    for state in ("idle", "working", "tool_read", "tool_edit", "tool_pwsh", "tool_web", "approval", "done", "error", "sing", "start"):
        ext.state = state
        key = ext.sprite_key()
        assert key[0].startswith("companion:") and not pet.sprites[key[:2]].isNull(), state
    ext.set_option("companion_portraits", False)
    assert pet.skin == "灵动大肥鱼"
    pet.close()
    print("通过：Codex 增量/完成/取消/截断，CPU/内存/GPU 边界与冷却，五种喂食与限流，11 套立绘与形象恢复。")
