"""比值无界的窗口：任意高的尖峰（notes/123 §2）。

W_k = k，但以概率 p 出现尖峰 W_k = ⌊k^α⌋（α = 1.5、2、2.5），间隔等于窗口。
段内的最大/最小比值无界（α > 1）。用 irregular_windows.py 的角点公式计算 Δ(M_{K→L})。
预测（123 定理 C）：尖峰后接小窗口时，两步核近似秩一（重置），所以仍刚性。
"""
import numpy as np
src = open("experiments/irregular_windows.py", encoding="utf-8").read().split("rng = np.random")[0]
ns = {}; exec(src, ns); corner = ns["corner"]

rng = np.random.default_rng(5)
N = 400
for alpha in (1.5, 2.0, 2.5):
    spikes = rng.random(N + 1) < 0.1
    W = [int(k ** alpha) + 1 if (spikes[k] and k > 5) else k + 1 for k in range(N + 1)]
    for K in (20, 60):
        if spikes[K]:
            K += 1
        print(f"alpha={alpha} K={K}", corner(W, K, (K + 10, 2 * K, 4 * K)), flush=True)
