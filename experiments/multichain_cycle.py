"""三链的三角形同步（含圈）：窗口是六边形（notes/123 §3）。

同 multichain_blocks.py，另加第三条边的约束 D¹ + D² = x₁ − x₃ ∈ [2, W3_k]。
W3 < W1 + W2 时，矩形被切去一个角，得到 120° 的角（白化后）。
"""
import numpy as np
src = open("experiments/multichain_blocks.py", encoding="utf-8").read().split("if __name__")[0]
ns = {}; exec(src, ns)
diameter = ns["diameter"]

def run(w1, w2, w3, K, Ls):
    Lmax = max(Ls); mar = int(8 * np.sqrt(Lmax)) + 5
    n = max(w1(Lmax), w2(Lmax)) + 2 * mar + 2; off = mar
    b1, b2, b3 = w1(K), w2(K), w3(K)
    starts = [(a, b) for a in range(1, b1 + 1) for b in range(1, b2 + 1)
              if (a + 2 * b) % 3 == 0 and a + b <= b3]
    V = np.zeros((len(starts), n, n))
    for s, (a, b) in enumerate(starts):
        V[s, a + off, b + off] = 1.0
    I, J = np.meshgrid(np.arange(n) - off, np.arange(n) - off, indexing='ij')
    for k in range(K + 1, Lmax + 1):
        for _ in range(k):
            N = np.zeros_like(V)
            N[:, 1:, :] += V[:, :-1, :]; N[:, :-1, 1:] += V[:, 1:, :-1]; N[:, :, :-1] += V[:, :, 1:]
            V = N / 3.0
        mask = (I >= 1) & (I <= w1(k)) & (J >= 1) & (J <= w2(k)) & (I + J <= w3(k))
        V[:, ~mask] = 0.0
        V /= V.sum(axis=(1, 2))[:, None, None]
        if k in Ls:
            with np.errstate(divide='ignore'):
                print(f"  L={k}: Δ={diameter(np.log(V[:, mask])):.3f}", flush=True)

K = 10
for name, w3 in (("W3 = 1.5k（六边形）", lambda k: int(1.5 * k)), ("W3 = 1.1k（强切角）", lambda k: int(1.1 * k))):
    print(name, "K =", K, flush=True)
    run(lambda k: k, lambda k: k, w3, K, [K + 5, 2 * K, 3 * K, 4 * K])
