"""有界比值、多尺度不规则的窗口（notes/117 §1）。

W_k = k·G_k，G_k 是分段常数的过程：段长在 [1, k] 中对数均匀，取值在 {1, 2, 3} 中随机。
下包络在一切尺度上都不规则。用 irregular_windows.py 的角点公式计算 Δ(M_{K→L})。
"""
import numpy as np
src = open("experiments/irregular_windows.py", encoding="utf-8").read().split("rng = np.random")[0]
ns = {}; exec(src, ns); corner = ns["corner"]

def multiscale(N, seed):
    rng = np.random.default_rng(seed)
    G = np.empty(N + 1); k = 0
    while k <= N:
        length = int(np.exp(rng.uniform(0, np.log(max(k, 2))))) + 1
        G[k:k + length] = rng.choice([1, 2, 3]); k += length
    return [max(1, int(k * G[k])) + 1 for k in range(N + 1)]

for seed in (1, 2, 3):
    W = multiscale(1300, seed)
    for K in (40, 150):
        print(f"seed={seed} K={K}", corner(W, K, (K + 10, 2 * K, 4 * K, 8 * K)), flush=True)
