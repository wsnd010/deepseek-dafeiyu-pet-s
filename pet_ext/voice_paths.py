"""桌宠和独立语音进程共用的模型位置；只依赖标准库。"""
def weights(root, model):
    pre = root / 'GPT-SoVITS/GPT_SoVITS/pretrained_models'
    if model == 'trained':
        return root / 'weights/GPT/dafeiyu-e10.ckpt', root / 'weights/SoVITS/dafeiyu_e8_s456.pth'
    if model == 'baseline':
        pre = pre / 'gsv-v2final-pretrained'
        return pre / 's1bert25hz-5kh-longer-epoch=12-step=369668.ckpt', pre / 's2G2333k.pth'
    raise ValueError('未知语音模型')
