param(
    [string]$VoiceSource = "I:\dafeiyu-voice",
    [string]$PythonVersion = "3.12.10",
    [switch]$SkipVoiceRuntime,
    [switch]$SkipPyInstaller
)

$ErrorActionPreference = "Stop"
$ProgressPreference = "SilentlyContinue"
$repo = Split-Path -Parent $MyInvocation.MyCommand.Path
$dist = Join-Path $repo "dist\大肥鱼桌宠"
$cache = Join-Path $repo "_build\voice-runtime-cpu"
$runtime = Join-Path $dist "voice_runtime"

function Require-File([string]$Path) {
    if (-not (Test-Path -LiteralPath $Path -PathType Leaf)) {
        throw "缺少文件：$Path"
    }
}

function Copy-One([string]$RelativePath) {
    $source = Join-Path $VoiceSource $RelativePath
    $target = Join-Path $runtime $RelativePath
    Require-File $source
    New-Item -ItemType Directory -Force -Path (Split-Path -Parent $target) | Out-Null
    Copy-Item -LiteralPath $source -Destination $target -Force
}

Set-Location $repo
if (-not $SkipPyInstaller) {
    $venvPython = Join-Path $repo ".venv\Scripts\python.exe"
    $pyinstaller = Join-Path $repo ".venv\Scripts\pyinstaller.exe"
    if (-not (Test-Path -LiteralPath $venvPython)) {
        if (Get-Command py -ErrorAction SilentlyContinue) {
            & py -3.12 -m venv (Join-Path $repo ".venv")
        } else {
            & python -m venv (Join-Path $repo ".venv")
        }
        if ($LASTEXITCODE) { throw "创建桌宠打包环境失败，请安装 Python 3.12" }
    }
    if (-not (Test-Path -LiteralPath $pyinstaller)) {
        & $venvPython -m pip install --upgrade pip
        & $venvPython -m pip install -r (Join-Path $repo "requirements.txt") "PySide6>=6.8" pyinstaller
        if ($LASTEXITCODE) { throw "安装桌宠打包依赖失败" }
    }
    & $pyinstaller --noconfirm --clean "桌宠.spec"
    if ($LASTEXITCODE) { throw "PyInstaller 打包失败：$LASTEXITCODE" }
}

if ($SkipVoiceRuntime) {
    Write-Host "已跳过语音运行时；桌宠 exe 位于 $dist"
    exit 0
}

Require-File (Join-Path $VoiceSource "GPT-SoVITS\GPT_SoVITS\TTS_infer_pack\TTS.py")
New-Item -ItemType Directory -Force -Path $cache | Out-Null
$pythonDir = Join-Path $cache "python"
$pythonExe = Join-Path $pythonDir "python.exe"

if (-not (Test-Path -LiteralPath $pythonExe)) {
    $zip = Join-Path $cache "python-embed.zip"
    $url = "https://www.python.org/ftp/python/$PythonVersion/python-$PythonVersion-embed-amd64.zip"
    Invoke-WebRequest $url -OutFile $zip
    New-Item -ItemType Directory -Force -Path $pythonDir | Out-Null
    Expand-Archive -LiteralPath $zip -DestinationPath $pythonDir -Force
    $pth = Get-ChildItem $pythonDir -Filter "python*._pth" | Select-Object -First 1
    if (-not $pth) { throw "便携 Python 缺少 ._pth 文件" }
    $lines = Get-Content -LiteralPath $pth.FullName
    $lines = $lines | ForEach-Object { if ($_ -eq "#import site") { "import site" } else { $_ } }
    $lines += "Lib\site-packages"
    Set-Content -LiteralPath $pth.FullName -Value ($lines | Select-Object -Unique) -Encoding ASCII
    Invoke-WebRequest "https://bootstrap.pypa.io/get-pip.py" -OutFile (Join-Path $cache "get-pip.py")
    & $pythonExe (Join-Path $cache "get-pip.py") --no-warn-script-location
    if ($LASTEXITCODE) { throw "便携 Python 安装 pip 失败" }
}

$site = Join-Path $pythonDir "Lib\site-packages"
if (-not (Test-Path -LiteralPath (Join-Path $site "torch"))) {
    & $pythonExe -m pip install --no-cache-dir --no-warn-script-location `
        --index-url "https://download.pytorch.org/whl/cpu" `
        "torch==2.7.1" "torchaudio==2.7.1"
    if ($LASTEXITCODE) { throw "CPU 版 PyTorch 安装失败" }
}
& $pythonExe -m pip install --no-cache-dir --no-warn-script-location `
    -r (Join-Path $repo "voice-runtime-requirements.txt")
if ($LASTEXITCODE) { throw "语音推理依赖安装失败" }

Remove-Item -LiteralPath $runtime -Recurse -Force -ErrorAction SilentlyContinue
New-Item -ItemType Directory -Force -Path $runtime | Out-Null
Copy-Item -LiteralPath $pythonDir -Destination (Join-Path $runtime "python") -Recurse -Force

$gptSource = Join-Path $VoiceSource "GPT-SoVITS"
$gptTarget = Join-Path $runtime "GPT-SoVITS"
New-Item -ItemType Directory -Force -Path $gptTarget | Out-Null
$null = robocopy $gptSource $gptTarget /E /NFL /NDL /NJH /NJS /NP `
    /XD ".git" "__pycache__" "pretrained_models" "logs" "output" "TEMP" `
    /XF "*.pyc" "*.pyo" "*.part"
if ($LASTEXITCODE -ge 8) { throw "GPT-SoVITS 推理代码复制失败：$LASTEXITCODE" }

# 只放运行时真正会用到的 2 个训练权重、2 个底模、BERT、HuBERT、语言识别模型和 1 条参考音频。
@(
    "weights\GPT\dafeiyu-e10.ckpt",
    "weights\SoVITS\dafeiyu_e8_s456.pth",
    "dataset\train\audio\dwg_0031.wav",
    "GPT-SoVITS\runtime\ffmpeg.exe",
    "GPT-SoVITS\runtime\ffprobe.exe",
    "GPT-SoVITS\GPT_SoVITS\pretrained_models\gsv-v2final-pretrained\s1bert25hz-5kh-longer-epoch=12-step=369668.ckpt",
    "GPT-SoVITS\GPT_SoVITS\pretrained_models\gsv-v2final-pretrained\s2G2333k.pth",
    "GPT-SoVITS\GPT_SoVITS\pretrained_models\chinese-hubert-base\config.json",
    "GPT-SoVITS\GPT_SoVITS\pretrained_models\chinese-hubert-base\preprocessor_config.json",
    "GPT-SoVITS\GPT_SoVITS\pretrained_models\chinese-hubert-base\pytorch_model.bin",
    "GPT-SoVITS\GPT_SoVITS\pretrained_models\chinese-roberta-wwm-ext-large\config.json",
    "GPT-SoVITS\GPT_SoVITS\pretrained_models\chinese-roberta-wwm-ext-large\pytorch_model.bin",
    "GPT-SoVITS\GPT_SoVITS\pretrained_models\chinese-roberta-wwm-ext-large\tokenizer_config.json",
    "GPT-SoVITS\GPT_SoVITS\pretrained_models\chinese-roberta-wwm-ext-large\tokenizer.json",
    "GPT-SoVITS\GPT_SoVITS\pretrained_models\chinese-roberta-wwm-ext-large\vocab.txt",
    "GPT-SoVITS\GPT_SoVITS\pretrained_models\fast_langdetect\lid.176.bin"
) | ForEach-Object { Copy-One $_ }

@("cache\pet_voice", "cache\nltk", "logs", "tmp") | ForEach-Object {
    New-Item -ItemType Directory -Force -Path (Join-Path $runtime $_) | Out-Null
}

# 英文夹杂文本需要这些 NLTK 数据；存在就复制，不存在时中文语音仍可用。
$nltkSource = Join-Path $VoiceSource "cache\nltk"
if (Test-Path -LiteralPath $nltkSource) {
    Get-ChildItem -LiteralPath $nltkSource -Force | Copy-Item `
        -Destination (Join-Path $runtime "cache\nltk") -Recurse -Force
}

& (Join-Path $runtime "python\python.exe") -c "import torch, torchaudio, transformers, librosa, soundfile; print('voice runtime ok', torch.__version__, 'cuda=', torch.cuda.is_available())"
if ($LASTEXITCODE) { throw "语音运行时自检失败" }

$bytes = (Get-ChildItem -LiteralPath $runtime -Recurse -File | Measure-Object Length -Sum).Sum
Write-Host ("打包完成：{0}" -f $dist)
Write-Host ("语音运行时：{0:N2} GB（CPU 版，不含 CUDA、训练集、旧权重、缓存）" -f ($bytes / 1GB))
