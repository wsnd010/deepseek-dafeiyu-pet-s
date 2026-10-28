# -*- coding: utf-8 -*-
"""桌宠的可选扩展（新功能都放这里，不去改 桌宠.py 里已有的方法）。

为什么单独一个包：
    桌宠.py 里 `PetWindow` 一个类就 6000 多行、390 个方法，往里塞新东西很容易
    撞到看不见的耦合。所以约定成：**新功能一律独立成模块，只通过 `setup(pet)`
    挂上去**，对原有逻辑的侵入压到最小。

加载失败不要连带主程序：任何一个扩展抛异常都只打印一行，其它照常。
"""

from __future__ import annotations

import traceback


def load_extensions(pet):
    """按顺序加载扩展，返回 {名字: 实例}。"""
    from . import anim as anim_ext
    from . import chat as chat_ext
    from . import dispatch as dispatch_ext
    from . import flyout as flyout_ext
    from . import notify as notify_ext
    from . import rest as rest_ext
    from . import node as node_ext
    from . import companion as companion_ext
    from . import living as living_ext
    from . import voice as voice_ext
    from . import feeding as feeding_ext

    loaded = {}
    # 顺序有意义：chat 要用 flyout 那块板子，所以 flyout 先加载
    for mod in (node_ext, notify_ext, anim_ext, flyout_ext, chat_ext, dispatch_ext, rest_ext, companion_ext, living_ext, voice_ext, feeding_ext):
        name = mod.__name__.rsplit(".", 1)[-1]
        try:
            got = mod.setup(pet)
            if got is not None:
                loaded[name] = got
        except Exception:
            print(f"[pet_ext] 「{name}」加载失败，已跳过：")
            traceback.print_exc()
    return loaded
