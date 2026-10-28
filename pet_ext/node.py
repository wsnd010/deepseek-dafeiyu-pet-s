# -*- coding: utf-8 -*-
"""Sub2API 节点配置与余额；沿用原来的 Key 设置入口。"""

import math
import threading
import time

import requests

BASE_URL = "http://192.168.1.133:18881"
MODEL = "deepseek-v4.1-flash"


def current_model(cfg):
    value = cfg.get("chat_model")
    return value.strip() if isinstance(value, str) and value.strip() else MODEL


def query_models(key):
    """只获取模型名称，不产生聊天用量。失败时由界面保留旧列表。"""
    try:
        response = requests.get(BASE_URL + "/v1/models",
                                headers={"Authorization": "Bearer " + key}, timeout=15)
    except requests.RequestException as exc:
        raise ValueError("获取模型失败，请检查节点网络后重试") from exc
    if response.status_code == 401:
        raise ValueError("节点鉴权失败（401），请核对节点 Key")
    if response.status_code != 200:
        raise ValueError(f"获取模型失败：HTTP {response.status_code}")
    try:
        data = response.json()["data"]
        if not isinstance(data, list):
            raise ValueError()
        models = list(dict.fromkeys(item["id"].strip() for item in data
                                   if isinstance(item, dict) and isinstance(item.get("id"), str)
                                   and item["id"].strip()))
    except (KeyError, TypeError, ValueError) as exc:
        raise ValueError("节点返回的模型列表格式不正确") from exc
    if not models:
        raise ValueError("节点未返回可用模型，请检查 Key 的分组权限")
    return models


def query_balance(key):
    """返回主程序能处理的余额结构，不把网络异常带回界面线程。"""
    try:
        response = requests.get(
            BASE_URL + "/v1/usage",
            headers={"Authorization": "Bearer " + key}, timeout=15)
        if response.status_code != 200:
            return {"ok": False, "error": f"Sub2API 余额接口 HTTP {response.status_code}"}
        data = response.json()
        if data.get("mode") == "quota_limited":
            amount = (data.get("quota") or {}).get("remaining")
            name = "Sub2API 剩余额度"
        else:
            amount = data.get("balance", data.get("remaining"))
            name = "Sub2API"
        if amount is None:
            return {"ok": False, "error": "节点未返回余额或剩余额度（可能是订阅账户）"}
        total = float(amount)
        if not math.isfinite(total):
            raise ValueError("余额不是有限数字")
        return {"ok": True, "total": total, "currency": data.get("unit") or "USD",
                "name": name}
    except requests.RequestException:
        return {"ok": False, "error": "Sub2API 余额请求失败，请检查节点网络"}
    except (ValueError, TypeError, AttributeError):
        return {"ok": False, "error": "Sub2API 余额返回格式不正确"}


def setup(pet):
    original = pet.refresh_balance

    def set_key_dialog():
        from PySide6.QtCore import Qt
        from PySide6.QtWidgets import QInputDialog, QLineEdit
        with pet._ui_guard():
            key, ok = QInputDialog.getText(
                pet, "设置 Sub2API 节点 Key", "输入节点 API Key（不要带 Bearer 前缀或句号）：",
                QLineEdit.EchoMode.Password, pet.cfg.get("ds_api_key", ""),
                Qt.WindowType.WindowStaysOnTopHint)
        if ok and key.strip():
            pet.cfg["ds_api_key"] = key.strip()
            pet.save_config()
            pet.balance = None
            pet.refresh_balance(silent=False)

    def refresh_balance(silent=True):
        # 原来的 DeepSeek 槽位继续存节点 Key，其他服务仍走原来的实现。
        if (pet.cfg.get("balance_source") or "DeepSeek") != "DeepSeek":
            return original(silent=silent)
        key = pet._api_key()
        if not key:
            pet.bal_error = "未配置 Sub2API Key"
            if not silent:
                pet.say("先在设置 → 余额和用量 → 设置 Key 填入节点 Key")
            return
        if pet.bal_busy:
            return
        pet.bal_busy = True

        def worker():
            result = query_balance(key)
            result.setdefault("name", "Sub2API")
            result.update(silent=silent, ts=time.time())
            pet._bal_queue.append(result)

        threading.Thread(target=worker, daemon=True).start()

    pet.refresh_balance = refresh_balance
    pet._set_key_dialog = set_key_dialog
    return refresh_balance
