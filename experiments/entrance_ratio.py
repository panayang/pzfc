"""进入比的数值检验（notes/116 §2）。

检查点链同 boundary_layer.py。块 [K, 2K]，K 取为接触点（窗口 ≈ 包络 k）。
计算 min_x P_x(存活, D_L ∈ S) / P_x(存活)，S = [W_L/4, W_L/2]。
引理 S″ 预测：只要（KU）在某个尺度 ℓ ≤ c W^{3/4} 上成立，这个最小值对 K 一致有界地远离 0。
"""
import numpy as np
from math import lgamma, log

def nbpmf(n, r):
    ys = np.arange(n, dtype=float)
    lg = np.array([lgamma(r + y) - lgamma(y + 1) for y in ys])
    return np.exp(lg - lgamma(r) - (r + ys) * log(2.0))

def back(W, K, L, s):
    for k in range(L - 1, K - 1, -1):
        Wn, Wk = W[k + 1], W[k]
        pmf = nbpmf(Wn + Wk, Wn)
        x = np.arange(1, Wk + 1); y = np.arange(1, Wn + 1)
        s = (pmf[(x[:, None] + Wn - y[None, :])] * s[None, :]).sum(axis=1)
    return s

def ratio(W, K, L):
    WL = W[L]
    ind = np.zeros(WL); ind[WL // 4 - 1: WL // 2] = 1.0
    a = back(W, K, L, np.ones(WL)); b = back(W, K, L, ind)
    return (b / a).min()

def contact_after(f, K0):
    ks = np.arange(K0, int(K0 * 1.3))
    return int(ks[np.argmin([f(k) / k for k in ks])])

rng = np.random.default_rng(3)
osc = lambda k: max(1, int(k * (1 + 0.5 * abs(np.sin(k ** 0.7)))))
print("K0  | 正则 k | k·U[1,3] | 振荡 k(1+½|sin k^0.7|)")
for K0 in (25, 50, 100, 200, 400):
    reg = [k for k in range(3 * K0 + 1)]
    U = rng.uniform(1, 3, size=3 * K0 + 1)
    ran = [max(1, int(k * U[k])) for k in range(3 * K0 + 1)]
    Kr = min(range(K0, int(1.3 * K0)), key=lambda k: U[k])
    Ko = contact_after(osc, K0)
    Wo = [osc(k) for k in range(2 * Ko + 1)]
    print(f"{K0:4d} | {ratio(reg, K0, 2*K0):.3f} | {ratio(ran, Kr, 2*Kr):.3f} (K={Kr}) | {ratio(Wo, Ko, 2*Ko):.3f} (K={Ko})", flush=True)
