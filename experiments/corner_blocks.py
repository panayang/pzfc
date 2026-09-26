"""Corner cross-ratio on the blocks of notes/98 (wide windows).

For f(k) = k^alpha, W = W_K, choose L with m_L = (W_L - W/2)/(P_L - P_{m1}) <= 1/(4W)
(m1: X-time Theta*W^2 after P_K, Theta = 1), propagate the rows d = 1 and d = W_K,
and print Delta(M_{K->L}) = log of the corner cross-ratio (notes/94 Thm 1).
Run: python experiments/corner_blocks.py
"""
import numpy as np
from math import lgamma, log

def lognb_vec(y, r):
    y = np.asarray(y, dtype=float)
    out = np.full(y.shape, -np.inf)
    ok = y >= 0
    yy = y[ok]
    out[ok] = (np.array([lgamma(r + v) for v in yy]) - np.array([lgamma(v + 1) for v in yy])
               - lgamma(r) - (r + yy) * log(2.0))
    return out

def step(logv, Wk, Wn):
    # out[d'] = sum_d v[d] * P(Y = Wn - d' + d), d in [1,Wk], d' in [1,Wn]
    m = logv.max(); v = np.exp(logv - m)
    ys = np.arange(0, Wn + Wk)
    pmf = np.exp(lognb_vec(ys, Wn))
    # for d' index j (d'=j+1), d index i (d=i+1): y = Wn - j + i
    full = np.convolve(v[::-1], pmf)           # full[k] = sum_i v[i] pmf[k - (Wk-1-i)]
    # need sum_i v[i] pmf[Wn - j + i] -> k - (Wk-1-i) = Wn - j + i  => k = Wn - j + Wk - 1
    ks = Wn - np.arange(Wn) + Wk - 1
    out = full[ks]
    with np.errstate(divide='ignore'):
        return np.log(out) + m

def run(alpha, K):
    f = lambda k: int(k ** alpha)
    W = lambda k: f(k) + 1
    P = {0: 0}
    for k in range(1, 100000):
        P[k] = P[k - 1] + W(k)
        if k > 5 * K and (W(k) - W(K) / 2) / (P[k] - P[K]) < 1 / (8 * W(K)):
            break
    Wk = W(K); m1 = K
    while P[m1] - P[K] < Wk * Wk: m1 += 1
    L = m1 + 1
    while (W(L) - Wk / 2) / (P[L] - P[m1]) > 1 / (4 * Wk): L += 1
    bot = np.full(Wk, -np.inf); bot[0] = 0.0
    top = np.full(Wk, -np.inf); top[-1] = 0.0
    dm1 = None
    for k in range(K, L):
        bot = step(bot, W(k), W(k + 1)); top = step(top, W(k), W(k + 1))
        bot -= bot.max(); top -= top.max()
        if k + 1 == m1:
            dm1 = (top[-1] + bot[0]) - (top[0] + bot[-1])
    cr = (top[-1] + bot[0]) - (top[0] + bot[-1])
    print("alpha=%.1f K=%d W_K=%d | single scale L=m1=%d: Delta=%.3f | block L=%d W_L=%d rho_L*W_K=%.3f: Delta=%.4f"
          % (alpha, K, Wk, m1, dm1, L, W(L), W(L) / P[L] * Wk, cr))

for alpha, Ks in ((1.5, (4, 6, 8, 10)), (2.0, (3, 4, 5, 6)), (3.0, (2, 3))):
    for K in Ks:
        run(alpha, K)
