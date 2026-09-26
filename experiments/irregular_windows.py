"""Irregular windows (notes/110): corner diameter Delta(M_{K->L}) for windows that jump at random.

Heap model: W_k = f(k) + 1, gaps = windows.  Propagate the bottom and top rows of level K
(exact convolution with the negative binomial step) and print the corner log cross-ratio at level L.
Run: python experiments/irregular_windows.py
"""
import numpy as np
from math import lgamma, log

def lognb_vec(ys, r):
    ys = np.asarray(ys, dtype=float)
    return (np.array([lgamma(r + y) for y in ys]) - np.array([lgamma(y + 1) for y in ys])
            - lgamma(r) - (r + ys) * log(2.0))

def step(logv, Wk, Wn):
    m = logv.max(); v = np.exp(logv - m)
    pmf = np.exp(lognb_vec(np.arange(0, Wn + Wk), Wn))
    full = np.convolve(v[::-1], pmf)
    out = full[Wn - np.arange(Wn) + Wk - 1]
    with np.errstate(divide='ignore'):
        return np.log(out) + m

def corner(W, K, Ls):
    bot = np.full(W[K], -np.inf); bot[0] = 0.0
    top = np.full(W[K], -np.inf); top[-1] = 0.0
    out = []
    for k in range(K, max(Ls)):
        bot = step(bot, W[k], W[k + 1]); top = step(top, W[k], W[k + 1])
        bot -= bot.max(); top -= top.max()
        if k + 1 in Ls:
            out.append("L=%d:%.3f" % (k + 1, (top[-1] + bot[0]) - (top[0] + bot[-1])))
    return " ".join(out)

rng = np.random.default_rng(1)
N = 700
B = rng.integers(0, 2, size=N + 1)
cases = {
    "k(1+2B)": [int(k * (1 + 2 * B[k])) + 1 for k in range(N + 1)],
    "k":       [k + 1 for k in range(N + 1)],
    "k^1.5(1+2B)": [int(k ** 1.5 * (1 + 2 * B[k])) + 1 for k in range(N + 1)],
    "2^k(1+2B) [rho>0]": [int(2 ** min(k, 18) * (1 + 2 * B[k])) + 1 for k in range(N + 1)],
}
for name, W in cases.items():
    if name.startswith("2^k"):
        print("%-18s K=4 " % name, corner(W, 4, (8, 10, 12, 14, 16)))
    elif name.startswith("k^1.5"):
        print("%-18s K=8 " % name, corner(W, 8, (16, 32, 64, 128, 200)))
    else:
        for K in (20, 60):
            print("%-18s K=%d" % (name, K), corner(W, K, (K + 10, 2 * K, 4 * K, 8 * K)))
