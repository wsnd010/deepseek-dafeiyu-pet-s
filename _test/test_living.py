# -*- coding: utf-8 -*-
import time
from unittest.mock import patch
from PySide6.QtWidgets import QApplication
from test_companion import FakePet
from pet_ext.living import Living


def run_checks():
    app = QApplication.instance() or QApplication([])
    pet = FakePet()
    pet.quiet_left = lambda: 0
    pet.show()
    ext = Living(pet)
    pet.ext["living"] = ext
    ext.timer.stop()
    # 本组测手动陪伴，自动空闲门控由 test_idle_feeding 单独验证。
    ext.manual = True
    assert ext.choose_mood({"hour": 2}) == "sleepy"
    assert ext.choose_mood({"hour": 12, "activity": "开发工具"}) == "focused"
    ext.touch()
    assert ext.choose_mood({"hour": 12}) == "happy"
    ext._finish(0, {"hour": 12, "away": False, "activity": "开发工具"}, "")
    assert pet.say.called and ext.recent
    first = ext.recent[-1]
    ext._finish(0, {"hour": 12}, "")
    assert first != ext.recent[-1]
    before = pet.say.call_count
    ext._finish(0, {"away": True}, "")
    assert pet.say.call_count == before
    assert ext.choose_mood({"hour": 12}) == "missing"
    ext.configure("living_on", False)
    ext._finish(0, {"reply": "旧请求"}, "")
    assert pet.say.call_count == before
    ext.configure("living_on", True)
    pet._fs_now = True
    assert ext.blocked()
    pet._fs_now = False
    pet.cfg["living_ai"] = True
    pet._api_key = lambda: "test-key"
    with patch("pet_ext.living.observe", return_value={"activity": "开发工具", "away": False, "hour": 12}), \
         patch("pet_ext.chat.post_json", return_value={"choices": [{"message": {"content": "我陪你慢慢写。"}}]}) as post:
        ext.last_observe = 0
        ext.tick(force=True)
        until = time.monotonic() + 3
        while ext.busy and time.monotonic() < until:
            app.processEvents()
            time.sleep(.005)
        assert not ext.busy and post.called
        assert "开发工具" in post.call_args.args[1]["messages"][1]["content"]
        assert pet.say.call_args.args[0] == "我陪你慢慢写。"
    pet.hide()
    print("通过：情绪变化、去重、离开静音、关闭丢弃结果、全屏避让、后台 AI 摘要与发言。")
