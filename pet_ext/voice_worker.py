"""独立语音进程：使用外部环境，标准输出只传 JSON，不占桌宠主线程。"""
import argparse
import contextlib
import gc
import json
import os
from pathlib import Path
import sys
import traceback


def configure(root):
    for key, folder in {
        'TEMP': 'tmp', 'TMP': 'tmp', 'HF_HOME': 'cache/huggingface',
        'HUGGINGFACE_HUB_CACHE': 'cache/huggingface/hub',
        'TORCH_HOME': 'cache/torch', 'XDG_CACHE_HOME': 'cache',
        'NUMBA_CACHE_DIR': 'cache/numba', 'MPLCONFIGDIR': 'cache/matplotlib',
        'NLTK_DATA': 'cache/nltk', 'GRADIO_TEMP_DIR': 'tmp/gradio',
        'CUDA_CACHE_PATH': 'cache/cuda', 'TORCHINDUCTOR_CACHE_DIR': 'cache/torchinductor',
        'TRITON_CACHE_DIR': 'cache/triton', 'PYTHONPYCACHEPREFIX': 'cache/pycache',
    }.items():
        path = root / folder
        path.mkdir(parents=True, exist_ok=True)
        os.environ[key] = str(path)
    sys.pycache_prefix = os.environ['PYTHONPYCACHEPREFIX']
    os.environ.update(HF_HUB_OFFLINE='1', GRADIO_ANALYTICS_ENABLED='False',
                      TOKENIZERS_PARALLELISM='false', OMP_NUM_THREADS='4', version='v2')
    repo = root / 'GPT-SoVITS'
    os.chdir(repo)
    sys.path[:0] = [str(repo), str(repo / 'GPT_SoVITS')]
    os.environ['PATH'] = str(repo / 'runtime') + os.pathsep + os.environ['PATH']


def main():
    from voice_paths import weights
    parser = argparse.ArgumentParser()
    parser.add_argument('--runtime', required=True)
    args = parser.parse_args()
    root = Path(args.runtime).resolve()
    configure(root)
    wire = sys.stdout
    def emit(**data):
        wire.write(json.dumps(data, ensure_ascii=False) + '\n')
        wire.flush()
    engine, selected = None, None
    emit(event='ready')
    with open(os.devnull, 'w', encoding='utf-8') as quiet, contextlib.redirect_stdout(quiet):
        for line in sys.stdin:
            request = {}
            try:
                request = json.loads(line)
                ident = request['id']
                model = request['model']
                text = request['text']
                if not isinstance(text, str) or not 0 < len(text) <= 2000:
                    raise ValueError('台词长度需为 1～2000 字')
                output = Path(request['output']).resolve()
                allowed = (root / 'cache/pet_voice').resolve()
                if output.parent != allowed or output.suffix != '.wav':
                    raise ValueError('无效的语音输出路径')
                if engine is None or selected != model:
                    emit(id=ident, event='loading')
                    import torch
                    use_cuda = torch.cuda.is_available()
                    device = 'cuda' if use_cuda else 'cpu'
                    if engine is not None:
                        del engine
                        engine = None
                        gc.collect()
                        if use_cuda:
                            torch.cuda.empty_cache()
                    if not use_cuda:
                        torch.set_num_threads(max(1, min(8, os.cpu_count() or 4)))
                    from TTS_infer_pack.TTS import TTS, TTS_Config
                    gpt, sovits = weights(root, model)
                    pre = root / 'GPT-SoVITS/GPT_SoVITS/pretrained_models'
                    engine = TTS(TTS_Config({'custom': {
                        'device': device, 'is_half': use_cuda, 'version': 'v2',
                        't2s_weights_path': str(gpt), 'vits_weights_path': str(sovits),
                        'bert_base_path': str(pre / 'chinese-roberta-wwm-ext-large'),
                        'cnhuhbert_base_path': str(pre / 'chinese-hubert-base'),
                    }}))
                    selected = model
                emit(id=ident, event='generating')
                import numpy as np
                import soundfile as sf
                chunks = []
                for sr, audio in engine.run({
                    'text': text, 'text_lang': 'all_zh',
                    'ref_audio_path': str(root / 'dataset/train/audio/dwg_0031.wav'),
                    'prompt_text': '今天的海水温度刚刚好，特别适合一边摸鱼，一边认真工作。',
                    'prompt_lang': 'all_zh', 'top_k': 15, 'top_p': 1,
                    'temperature': 1, 'text_split_method': 'cut5', 'batch_size': 1,
                    'speed_factor': 1.0, 'seed': 20261028,
                    'parallel_infer': torch.cuda.is_available(),
                    'split_bucket': True, 'return_fragment': False,
                }):
                    chunks.append(audio)
                if not chunks:
                    raise RuntimeError('模型没有生成声音')
                output.parent.mkdir(parents=True, exist_ok=True)
                sf.write(output, np.concatenate(chunks), sr, subtype='PCM_16')
                emit(id=ident, event='result', path=str(output))
            except Exception as exc:
                traceback.print_exc(file=sys.stderr)
                emit(id=request.get('id'), event='error', message=str(exc)[:240])


if __name__ == '__main__':
    main()
