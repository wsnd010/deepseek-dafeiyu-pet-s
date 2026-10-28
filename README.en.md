# Da Fei Yu Desktop Pet 🐋 · DeepSeek Desktop Pet & Balance Widget (Windows)

中文版说明见 [README.md](README.md)。

> **Keywords**: DeepSeek desktop pet · DeepSeek 桌宠 · Da Fei Yu / 大肥鱼 / whale-girl pet ·
> DeepSeek balance widget (standalone, no DSH required) · balance, today's spend, peak/off-peak hours,
> per-turn cost · Windows, double-click to run · drag-to-snap, flip on left snap,
> throw with inertia (bounces off screen edges), rolling numbers, click sounds ·
> sedentary / water reminders (off by default)

## ⬇️ Download (Windows)

[![latest release](https://img.shields.io/github/v/release/wsnd010/deepseek-dafeiyu-pet-s?label=latest&v=4&cacheSeconds=300)](https://github.com/wsnd010/deepseek-dafeiyu-pet-s/releases/latest)

### 👉 [**Download the latest Windows installer**](https://github.com/wsnd010/deepseek-dafeiyu-pet-s/releases/latest/download/dafeiyu-pet-setup.exe)

A ~257MB Chinese installer (most of it is the 239MB animated sprite set): double-click and click
Next a few times — you can pick the install folder, shortcuts are created for you, and the
installer itself can be deleted afterwards.

- Windows may warn about an unknown publisher (the exe is not code-signed): click "More info" → "Run anyway"
- Packaged build keeps its settings in `%APPDATA%\大肥鱼桌宠\`
- All versions and release notes: [Releases](https://github.com/wsnd010/deepseek-dafeiyu-pet-s/releases)

## 🆕 What's new in v1.1.7

- **Throw it**: release while moving and it flies on with inertia, **bounces off the screen edge**,
  and snaps to the edge once it settles; a slow release still snaps immediately. Three knobs under
  Settings → 动作和互动 → 甩出手感 (throw speed / inertia decay / edge bounce), each with a range limit
  and a "restore defaults" button
- **Work / rest reminder** (sedentary + water): **off by default** — turn it on and it reminds you to
  get up after 45 minutes of use and to drink water every 60 minutes. If keyboard and mouse are idle
  for 3+ minutes it assumes you already took a break and restarts the count
- **Snapping now really reaches the edge**: it used to stop 20–50 px short (it snapped the window,
  not the fish). The speech bubble shifts inward so it never gets clipped by the screen
- **Snapping only works in "stay in place" mode**: in follow / free-roam mode the switch turns itself
  off and greys out, and switches back on when you return
- **New right-click item「休息一下」**: becomes "end break (X min left)" while resting

> Full details in the first two sections of [CHANGELOG](CHANGELOG.md).

A transparent always-on-top desktop pet based on the DeepSeek fan-art character
「鲸鱼娘 · 大肥鱼」, built with Python + PySide6. It walks around your desktop,
tells you the weather, and doubles as a **DeepSeek balance widget**
(balance, today's spend, peak/off-peak hours, per-turn cost).

This repository is a slimmed-down fork of
[1190fasheqi/dafeiyu-pet](https://github.com/1190fasheqi/dafeiyu-pet) (MIT),
with the balance-widget features ported from
[MeteorNOX/DeepSeek-Balance-Whale-Widget](https://github.com/MeteorNOX/DeepSeek-Balance-Whale-Widget) (MIT).

## Features

**Pet**

- Three-view walking: side view for left/right (auto mirrored), back view when walking up, front view when walking down
- Three modes: free roam / follow the mouse / stay in place.
  In "stay in place" the pet keeps its front view by default (it no longer turns to glance at the
  cursor, so a custom front image stays on screen); dragging still flips it the same way as before
  — drag left and it faces left, release and it turns back to the front. If you want it to **follow
  the cursor** (cursor on the right → turns right, on the left → turns left, right next to it →
  faces you — it only turns, never moves, and never shows its back), turn on
  "原地待着时也跟着鼠标转" in the Mode submenu (off by default)
- Drag it around (it leans toward the drag direction and says something when you let go)
- **Throw it**: release while still moving and it flies on with inertia, slows down, **bounces off
  the screen edge**, and snaps to the edge once it settles. A slow release still snaps immediately.
  Three knobs under Settings → 动作和互动 → 甩出手感: throw speed 600–4000 px/s (default 2200),
  inertia decay 1–8 (default 3, higher stops sooner), edge bounce 0–80% (default 45%, 0 = no bounce)
- **Work / rest reminder** (sedentary + water): **off by default** — nothing runs until you flip the
  switch in Settings → 应用联动 → 工作与休息. Then it reminds you to get up after N minutes of use
  (default 45, followed by a quiet break of 5), and to drink water every 60 minutes. If the keyboard
  and mouse are idle for 3+ minutes it assumes you already took a break and restarts the count.
- Single click: hop + talk back + refresh the balance
- Tray icon, always-on-top, click-through mode, start with Windows, settings persisted in `config.json`

**Balance widget**

- Balance bubble above its head: `DeepSeek balance / ¥amount / today's spend / current peak or off-peak`
- Rolling number animation when the balance changes, auto refresh every 60s (click the pet to refresh now)
- Today's spend is tracked locally from balance drops (no platform token needed), resets daily, ledger in `usage.json`
- Drag to snap to screen edges (four quarters, corners allowed), flips horizontally when snapped left.
  **Only available in "stay in place" mode** — in follow / free-roam mode the switch turns itself
  off and greys out (can't be enabled), and switches back on automatically when you return to
  "stay in place", because snapping fights with following the cursor and with picking roaming spots.
  Snapping measures the **fish's body**, not the window, so the transparent padding no longer leaves
  a 20–50 px gap between the pet and the screen edge; the speech bubble shifts inward so it never
  gets clipped by the screen
- Squash-and-stretch when pressed; keeps its feet on the ground
- Click sounds: press + release clips merged into one complete sound, played through an always-open audio stream (no clipped first note, rapid clicks overlap)
- **Peak / off-peak indicator**: weekday 09:00–12:00 and 14:00–18:00 are peak, everything else (lunch break, evenings, weekends all day) is off-peak; three wording styles, and it tells you when the period switches
- **Per-turn cost**: reads the token usage from Codex session logs (`~/.codex-deepseek/sessions/*.jsonl`), converts it with the same peak/off-peak pricing table and reports it after each turn
- **Menus**: snapping and the peak wording switcher live in their own top-level menus (吸附 / 文案), no longer buried under 余额

**Weather**

- Manual default city, online city search, or IP-based auto locate; all announcements are in Chinese
- Weather text is mapped from WWO/WMO weather codes with an English-keyword fallback, `wttr.in` plus `open-meteo` as a backup source

**Appearance**

- Switch anytime between 大肥鱼 (three-view sprite) and 小鲸鱼挂件 (the widget's cut-out art)
- Bring your own art: **two separate libraries** — the three-view skin (front / side / back, uploaded as
  **one set of three pictures**: an incomplete set cannot be saved) and the widget skin (a single picture).
  Uploading now lives in **我的形象库… (My skin library)** — the 形象 submenu is just four entries:
  switch to 大肥鱼 / switch to the widget / open the library / restore both to the built-in art.
  Every upload gets **a name you choose**; that window also switches between the two libraries, previews
  the three-view skins with the **front** picture, and does rename / replace a picture / remove from
  library / apply. A small **这套恢复默认** button in that window puts just that one library back to the
  built-in art (the other library and everything in the libraries stay). An unfinished three-picture
  upload is remembered, so you can continue it later
- ⚠ Don't delete or move the source images you uploaded: the pet stores the **path** of your original file
  (it does not copy it). If a file goes missing, the menu and the library will flag it and you can use
  "重新定位…" (re-point) or upload it again

**Window**

- Layer: always-on-top / bottom-most (still above the wallpaper) / normal
- Opacity slider (100% → 20%)
- Single instance: launching the shortcut again won't spawn a second pet

**Other**

- Process reactions: it comments when you switch to Steam, your browser, a player, etc.
  Menu "进程联动 → 扫描电脑应用并添加…" opens a **visual list with real app icons** (searchable, like Windows Settings → Apps):
  built-in apps are marked `● built-in (can't be added twice)` but you can **edit their lines** (`修改默认台词`, replacing the
  built-in text, with one-click `恢复内置台词`), and any other app can get your own trigger text
- Multiple balance sources: add another API key (DeepSeek and OpenRouter can be queried; services like OpenAI have no balance API and it will tell you so)
- **Per-turn cost is agent-agnostic**: set the **agent name** (shows as "last turn Claude cost ¥…") and the **session log
  directory** from the menu; the log parser understands Codex (`payload.usage`), Claude Code (`message.usage`) and
  OpenAI-style (`prompt_tokens`/`completion_tokens`) records

**Right-click menu** (top level): 模式 / 大小 / 形象 / 吸附 / 文案 / 天气 / 余额 / 音效 / 层级 / 透明度 / 进程联动 /
显示隐藏 / 回到屏幕内 / 鼠标穿透 / 开机自启 / 退出

- 吸附: snap to edges / flip when snapped left　文案: peak-off-peak display and its three wording styles
- 层级: always-on-top / bottom-most / normal　透明度: 100% → 20%
- 形象 (four entries only): 大肥鱼（三视图）/ 小鲸鱼挂件（单张）switch the skin in one click,
  我的形象库… holds two named libraries of everything you uploaded (pick one to apply, upload a new
  three-view set / widget picture, replace a picture, rename, remove), 全部恢复默认形象 restores both

## Requirements

- Windows, Python 3.11+
- `pip install -r requirements.txt` (PySide6 + requests)

## Run

```bash
python 桌宠.py
```

or double-click `启动桌宠.bat`.

The DeepSeek API key is read from `config.json` (`ds_api_key`, set it via the
right-click menu → 余额 → 设置 Key) or from the `DEEPSEEK_API_KEY` environment variable.

## Build a standalone exe

```bash
pip install pyinstaller
pyinstaller --noconfirm 桌宠.spec
```

The result is `dist/大肥鱼桌宠.exe` — a single portable executable that needs no
Python install. Settings of the packaged build live in
`%APPDATA%\大肥鱼桌宠\` instead of next to the exe.

## Credits

- Original pet, sprites and lines: [1190fasheqi/dafeiyu-pet](https://github.com/1190fasheqi/dafeiyu-pet) (MIT)
- Balance widget design, sounds and the cut-out art: [MeteorNOX/DeepSeek-Balance-Whale-Widget](https://github.com/MeteorNOX/DeepSeek-Balance-Whale-Widget) (MIT)
- AI chat / weather / system monitor / PyInstaller config in the original project: [Cpanoe](https://github.com/Cpanoe) (PR#3)
- Facing fix: [B-A-A-GE](https://github.com/B-A-A-GE) (PR#1)

## License

MIT — see [LICENSE](LICENSE).
