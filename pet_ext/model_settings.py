# -*- coding: utf-8 -*-
"""聊天模型设置：后台获取列表，主线程更新控件和配置。"""

import threading

from PySide6.QtCore import QObject, Qt, Signal, Slot
from PySide6.QtWidgets import QComboBox, QSizePolicy

from .node import BASE_URL, current_model, query_models


class ModelSettings(QObject):
    finished = Signal(object, str)

    def __init__(self, page, pet):
        super().__init__(page)
        self.pet = pet
        self.busy = False
        self._request_key = ""
        card = page.card("聊天模型", BASE_URL, "ui.chat")
        self.combo = QComboBox()
        self.combo.setMinimumWidth(180)
        self.combo.setMaximumWidth(360)
        self.combo.setSizePolicy(QSizePolicy.Policy.Expanding, QSizePolicy.Policy.Fixed)
        self.combo.setSizeAdjustPolicy(QComboBox.SizeAdjustPolicy.AdjustToMinimumContentsLengthWithIcon)
        self.combo.setMinimumContentsLength(18)
        self.combo.setAccessibleName("聊天模型")
        self.combo.setCursor(Qt.CursorShape.PointingHandCursor)
        cached = pet.cfg.get("chat_models")
        models = [m for m in cached if isinstance(m, str) and m.strip()] if isinstance(cached, list) else []
        self._fill(models)
        page.row(card, "模型", "", self.combo)
        self.combo.currentIndexChanged.connect(self._select)
        buttons = page.buttons(card, [("获取模型", self.fetch, "primary", "ui.refresh")])
        self.button = buttons.buttons[0]
        self.status = page.hint(card, "")
        self.status.setTextFormat(Qt.TextFormat.PlainText)
        self.finished.connect(self._finished)

    def _fill(self, models):
        selected = current_model(self.pet.cfg)
        choices = list(dict.fromkeys([selected] + models))
        self.combo.blockSignals(True)
        try:
            self.combo.clear()
            for model in choices:
                self.combo.addItem(model, model)
            self.combo.setCurrentIndex(0)
            self.combo.setToolTip(selected)
        finally:
            self.combo.blockSignals(False)

    def _select(self, _index):
        model = self.combo.currentData()
        if not model:
            return
        self.pet.cfg["chat_model"] = model
        self.pet.save_config()
        self.combo.setToolTip(model)
        self.status.setText(f"已选择：{model}")

    def fetch(self):
        if self.busy:
            return
        key = self.pet._api_key()
        if not key:
            self.status.setText("请先在「余额和用量」设置节点 Key")
            return
        self._request_key = key
        self.busy = True
        self.button.setEnabled(False)
        self.status.setText("正在获取模型…")

        def worker():
            models, error = [], ""
            try:
                models = query_models(key)
            except Exception as exc:
                error = str(exc) if isinstance(exc, ValueError) else "获取模型失败，请重试"
            try:
                self.finished.emit(models, error)
            except RuntimeError:
                pass  # 设置页已销毁，不再操作它的控件。

        threading.Thread(target=worker, daemon=True).start()

    @Slot(object, str)
    def _finished(self, models, error):
        self.busy = False
        self.button.setEnabled(True)
        if self._request_key != self.pet._api_key():
            self.status.setText("Key 已更换，请重新获取模型")
            return
        if error:
            self.status.setText(error)
            return
        self.pet.cfg["chat_models"] = models
        self.pet.save_config()
        self._fill(models)
        selected = current_model(self.pet.cfg)
        message = f"已获取 {len(models)} 个模型"
        if selected not in models:
            message += "；当前模型不在返回列表中"
        self.status.setText(message)
