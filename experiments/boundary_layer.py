"""不规则窗口的有效边界层（notes/113 §1）。

检查点链：D_{k+1} = D_k + W_{k+1} − NegBin(W_{k+1}, ½)，在 [1, W_{k+1}] 之外杀死。
向后计算存活函数 s_K(x) = P_x(存活到 L = 2K)，起点 K 取为接触点（窗口 = k）。
输出：顶部的相对存活 s_K(W_K)/max s_K，与"半高深度" δ½（s 达到最大值一半处离顶部的距离）。
正则窗口的预测：顶部 ≍ W^{-1/2}，δ½ ≍ W；稀疏接触的启发式预测：有效层 W^{2/3}。
"""
import numpy as np
from math import lgamma, log

def nbpmf(n, r):
    ys = np.arange(n, dtype=float)
    lg = np.array([lgamma(r + y) - lgamma(y + 1) for y in ys])
    return np.exp(lg - lgamma(r) - (r + ys) * log(2.0))

def profile(W, K, L):
    s = np.ones(W[L])
    for k in range(L - 1, K - 1, -1):
        Wn, Wk = W[k + 1], W[k]
        pmf = nbpmf(Wn + Wk, Wn)                 # N = 0 .. Wn+Wk-1
        # s_k(x) = sum_{y=1}^{Wn} pmf(x + Wn - y) s_{k+1}(y),  x = 1..Wk
        full = np.convolve(pmf, s[::-1])         # full[j] = sum_i pmf[i] s[::-1][j-i]
        # 取 y 下标 j' = y-1，s[::-1][Wn-y] ；需要 i = x + Wn - y ⇒ j = i + (Wn - y) = x + 2(Wn-y)?  直接循环更稳妥
        x = np.arange(1, Wk + 1)
        y = np.arange(1, Wn + 1)
        s = (pmf[(x[:, None] + Wn - y[None, :])] * s[None, :]).sum(axis=1)
        s /= s.max()
    return s

def stats(s):
    W = len(s)
    top = s[-1]
    half = np.nonzero(s >= 0.5)[0]
    d_half = W - 1 - half.max() if len(half) else W
    return top, d_half

rng = np.random.default_rng(7)
print("%6s | %-24s | %-24s | %-24s" % ("K", "k (正则)", "k·U[1,3] (稀疏接触)", "k·(1+2B) (稠密接触)"))
for K in (25, 50, 100, 200, 400):
    L = 2 * K
    reg = [k for k in range(L + 1)]
    tops, ds = [], []
    for seed in range(4):
        U = rng.uniform(1, 3, size=L + 1); U[K] = 1.0
        W = [max(1, int(k * U[k])) for k in range(L + 1)]
        t, d = stats(profile(W, K, L)); tops.append(t); ds.append(d)
    B = rng.integers(0, 2, size=L + 1); B[K] = 0
    Wb = [max(1, int(k * (1 + 2 * B[k]))) for k in range(L + 1)]
    t0, d0 = stats(profile(reg, K, L))
    tb, db = stats(profile(Wb, K, L))
    print("%6d | top=%.4f δ½=%5d      | top=%.4f δ½=%7.1f   | top=%.4f δ½=%5d" %
          (K, t0, d0, np.mean(tops), np.mean(ds), tb, db), flush=True)
