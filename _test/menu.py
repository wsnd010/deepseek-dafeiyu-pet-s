# -*- coding: utf-8 -*-
"""当前机器的手动验收入口；不打印、不保存 Key。"""
import getpass
import json
from pathlib import Path
import subprocess
import sys
import time
from types import SimpleNamespace
from unittest.mock import Mock, patch

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from pet_ext import node

ITEMS = {"1": "启动桌宠", "2": "实测节点余额", "3": "实测节点聊天", "4": "获取节点模型列表", "5": "系统采样与 Codex 当前状态", "6": "离线自检（不联网）", "7": "大肥鱼语音训练状态与试听（I 盘）"}
ITEMS['8'] = '项目内语音自检与验收指引'
ITEMS['9'] = '语录频率、空闲静音、悬浮喂食与动作组合验收'
ITEMS['10'] = '按消息类型选择语音验收'


def checks():
    from pet_ext import chat
    assert chat.DS_MODEL == "deepseek-v4.1-flash"
    response = Mock(status_code=200)
    with patch.object(node.requests, "get", return_value=response):
        for data, total in [({"balance": 12, "unit": "USD"}, 12),
                            ({"mode": "quota_limited", "quota": {"remaining": 3}}, 3)]:
            response.json.return_value = data
            result = node.query_balance("test-key")
            assert result["ok"] and result["total"] == total
        for data in [{}, {"balance": "nan"}, {"balance": "invalid"}, []]:
            response.json.return_value = data
            assert not node.query_balance("test-key")["ok"]
        response.status_code = 401
        assert "401" in node.query_balance("test-key")["error"]
    with patch.object(chat.requests, "post", return_value=response):
        response.json.return_value = {}
        try:
            chat.post_json(chat.DS_URL, {}, "test-key")
        except chat.ChatError as exc:
            assert "Sub2API" in str(exc) and "401" in str(exc)
        else:
            raise AssertionError("401 必须报错")
    fallback = Mock()
    pet = SimpleNamespace(cfg={"balance_source": "OpenRouter"}, refresh_balance=fallback,
                          _api_key=lambda: "test-key", bal_busy=False, _bal_queue=[])
    node.setup(pet)
    pet.refresh_balance(silent=True)
    fallback.assert_called_once_with(silent=True)
    pet.cfg["balance_source"] = "DeepSeek"
    with patch.object(node, "query_balance", return_value={"ok": True, "total": 5, "currency": "USD"}):
        pet.refresh_balance(silent=False)
        deadline = time.monotonic() + 2
        while not pet._bal_queue and time.monotonic() < deadline:
            time.sleep(.01)
    assert pet._bal_queue[0]["name"] == "Sub2API" and pet.bal_busy
    assert pet._bal_queue[0]["silent"] is False
    print("通过：模型配置、账户余额、Key 额度、缺失/非法数据、401 提示。")
    print("通过：后台余额回调、其他来源保留原路径。")


def main():
    for key, label in ITEMS.items():
        print(f"{key}. {label}")
    choice = sys.argv[1] if len(sys.argv) > 1 else input("请选择：").strip()
    if choice == "1":
        subprocess.Popen([sys.executable, str(ROOT / "桌宠.py")], cwd=ROOT)
    elif choice == "10":
        print('退出旧桌宠后选 1 启动。右键 → 打开设置 → 语音 → 哪些消息要朗读。')
        print('开启语音总开关，关闭 AI 日常陪伴与闲聊、点击与拖拽回嘴；点桌宠或陪我说一句，应只有文字。')
        print('保留聊天回复和喂食反馈：聊天发一句、投喂一种食物，应能听到；分别关闭后再试应只有文字。')
        print('心声默认关闭；开启后遇到括号心声应朗读，关闭后仍显示但不读。')
        print('生成或播放时改任一类型开关，应停止当前声音并清空待播；重启后开关保持。')
        print('试听独立于类型开关；本轮自动测试未调用 GPU 合成，实际听感请按上述步骤验收。')
    elif choice == "9":
        print('先退出旧桌宠，选 1 启动。设置 → 文案 → 语录频率，选 2分钟 / 5分钟。')
        print('喂食和状态页的语录频率共用这个值；主动陪伴开启后不会再叠加旧语录。')
        print('持续键盘输入或移动鼠标时不应弹自动闲聊；停止操作一分钟后才允许，离开三分钟后安静。')
        print('点击鱼旁的食物按钮，依次点小鱼干、蛋糕、棒棒糖、团子、钻石：应收起食物篮并出现投喂反馈。')
        print('食物篮应是半透明窄竖排，优先放鱼身旁，边缘自动换侧或移到上下；不想喂时点外部、Esc、入口或 ×，应收起且不投喂。')
        print('设置 → 喂食和状态 → 关闭悬浮喂食按钮，按钮与食物篮都应隐藏。')
        print('右击 → 逗她一下 → 依次点四个带（组合）的动作，检查顺序、拖动中断和观感。')
        print('组合使用原有三种动作；本机缺少灵动帧素材。阅读时不动键鼠超过一分钟仍可能被当作空闲。')
    elif choice == "7":
        voice_root = Path("I:/dafeiyu-voice")
        python = voice_root / "env/Scripts/pythonw.exe"
        preview = voice_root / "preview_voice.py"
        if not python.exists() or not preview.exists():
            raise RuntimeError("找不到 I 盘语音环境，请检查 I:/dafeiyu-voice。")
        subprocess.Popen([str(python), str(preview)], cwd=voice_root)
        print("已打开语音训练状态与试听窗口；训练完成后可输入新台词生成声音。")
    elif choice == '8':
        from test_voice import run_checks as voice_checks
        voice_checks()
        print('退出旧桌宠，菜单选 1 启动；右键 → 打开设置 → 语音。')
        print('先保持关闭并点试听；应能听到训练版声音。再开启语音，打开聊天发送一句话，新回复应朗读一次。')
        print('只朗读已开启的消息类型；心声默认关闭，可单独开启。聊天不重复读缩略气泡，生成或播放中点停止应安静下来。')
        print('启动后再连接耳机并试听，声音应跟随系统默认输出；断开耳机后再试，应回到当前默认设备。')
        print('首次加载较慢，状态会显示准备/加载/生成/播放；声音是否自然、漏字或重复需亲耳判断。')
    elif choice == "6":
        checks()
        from test_models import run_checks
        run_checks()
        from test_companion import run_checks as companion_checks
        companion_checks()
        from test_living import run_checks as living_checks
        living_checks()
        from test_voice import run_checks as voice_checks
        voice_checks()
    elif choice == "5":
        from pet_ext.companion import CodexStatus, STATE_LABELS, sample_system
        print(json.dumps(sample_system(), ensure_ascii=False, indent=2))
        print("Codex：", STATE_LABELS[CodexStatus().poll()])
    elif choice in ("2", "3", "4"):
        key = getpass.getpass("输入节点 Key（不显示、不保存）：").strip()
        if not key:
            raise ValueError("Key 不能为空")
        if choice == "2":
            print(json.dumps(node.query_balance(key), ensure_ascii=False, indent=2))
        elif choice == "4":
            print("\n".join(node.query_models(key)))
        else:
            from pet_ext import chat
            result = chat.post_json(chat.DS_URL, {
                "model": chat.DS_MODEL, "messages": [{"role": "user", "content": "只回复：连接成功"}],
                "max_tokens": 30, "temperature": 0.9}, key)
            print(result["choices"][0]["message"]["content"])
    else:
        raise ValueError("请选择菜单中列出的编号")


if __name__ == "__main__":
    try:
        main()
    except Exception as exc:
        print(f"测试失败：{exc}")
        sys.exit(1)
