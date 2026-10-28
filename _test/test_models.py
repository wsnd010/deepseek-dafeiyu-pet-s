# -*- coding: utf-8 -*-
"""模型获取、设置交互与实际聊天请求参数回归。"""
import threading
import time
from types import SimpleNamespace
from unittest.mock import Mock, patch

from PySide6.QtWidgets import QApplication

from pet_ext import chat, node
from pet_ext.model_settings import ModelSettings
from ui_console import Page


def run_checks():
    response = Mock(status_code=200)
    with patch.object(node.requests, "get", return_value=response) as get:
        response.json.return_value = {"data": [{"id": "a"}, {"id": "b"}, {"id": "a"}, {}]}
        assert node.query_models("test-key") == ["a", "b"]
        assert get.call_args.kwargs["headers"]["Authorization"] == "Bearer test-key"
        for data in [{}, {"data": []}, {"data": "bad"}, {"data": [{"id": 123}]}]:
            response.json.return_value = data
            try:
                node.query_models("test-key")
            except ValueError:
                pass
            else:
                raise AssertionError("空列表和错误格式必须报错")
        response.status_code = 401
        try:
            node.query_models("test-key")
        except ValueError as exc:
            assert "401" in str(exc)
        else:
            raise AssertionError("401 必须报错")

    app = QApplication.instance() or QApplication([])
    pet = SimpleNamespace(cfg={}, _api_key=lambda: "test-key", save_config=Mock())
    page = Page("聊天")
    controls = ModelSettings(page, pet)
    gate = threading.Event()

    def delayed(_key):
        gate.wait(2)
        return [node.MODEL, "another-model"]

    def drain():
        deadline = time.monotonic() + 3
        while controls.busy and time.monotonic() < deadline:
            app.processEvents()
            time.sleep(.005)
        assert not controls.busy

    with patch("pet_ext.model_settings.query_models", side_effect=delayed) as fetch:
        controls.button.click()
        assert controls.busy and not controls.button.isEnabled()
        controls.fetch()
        gate.set()
        drain()
        assert fetch.call_count == 1
    assert pet.cfg["chat_models"] == [node.MODEL, "another-model"]
    controls.combo.setCurrentIndex(controls.combo.findData("another-model"))
    assert pet.cfg["chat_model"] == "another-model" and pet.save_config.called
    reopened_page = Page("聊天")
    reopened = ModelSettings(reopened_page, pet)
    assert reopened.combo.currentData() == "another-model"
    with patch("pet_ext.model_settings.query_models", side_effect=ValueError("测试失败")):
        controls.button.click()
        drain()
    assert controls.combo.currentData() == "another-model" and controls.button.isEnabled()
    assert controls.status.text() == "测试失败"
    with patch("pet_ext.model_settings.query_models", return_value=["new-model"]):
        controls.button.click()
        drain()
    assert controls.combo.currentData() == "another-model"
    assert "不在返回列表" in controls.status.text()
    controls._request_key = "old-key"
    controls._finished(["stale-model"], "")
    assert pet.cfg["chat_models"] == ["new-model"]
    assert "Key 已更换" in controls.status.text()
    pet._api_key = lambda: ""
    controls.button.click()
    assert not controls.busy and "设置节点 Key" in controls.status.text()
    fake = SimpleNamespace(_system=lambda: "测试", history=[], history_limit=lambda: 40,
                           reply_ready=SimpleNamespace(emit=Mock()), failed=SimpleNamespace(emit=Mock()))
    with patch.object(chat, "post_json", return_value={"choices": [{"message": {"content": "ok"}}]}) as post:
        chat.ChatExtension._worker(fake, "你好", "test-key", node.current_model(pet.cfg))
        assert post.call_args.args[1]["model"] == "another-model"
    page.close()
    reopened_page.close()
    print("通过：模型解析、空列表/401、异步获取防重入、失败保留、选择保存/重开、聊天模型参数。")
