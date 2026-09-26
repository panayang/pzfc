"""Ratio mixing of the killed D-walk (notes/94).

D_{k+1} = D_k + W_{k+1} - Y,  Y ~ NegBin(W_{k+1}, 1/2),  killed unless D_{k+1} in [1, W_{k+1}].
Start at level K from the bottom (d = 1) and from the top (d = W_K); propagate the survival-weighted
laws and print the Hilbert (ratio) distance between the two conditioned laws at later levels.
Distance -> 0 is the ratio-mixing lemma, which implies uniqueness (rigidity) by total positivity.

Run: python experiments/ratio_mixing.py
"""
import numpy as np
from math import lgamma

def lognb(y, r):   # log P(Y = y), Y ~ NegBin(r, 1/2): C(r-1+y, y) 2^{-(r+y)}
    return lgamma(r + y) - lgamma(y + 1) - lgamma(r) - (r + y) * np.log(2.0)

def step(logv, Wk, Wn):
    d = np.arange(1, Wk + 1)[:, None]; dn = np.arange(1, Wn + 1)[None, :]
    y = Wn - (dn - d)                                 # Y = W_{k+1} - (d' - d), always >= 1 here
    L = np.vectorize(lambda yy: lognb(yy, Wn))(y) if Wk * Wn < 1 else lgam_table(Wn)[y]
    A = logv[:, None] + L
    m = A.max(axis=0)
    return np.log(np.exp(A - m).sum(axis=0)) + m

_cache = {}
def lgam_table(r):
    if r not in _cache:
        yy = np.arange(0, 3 * r + 5)
        _cache[r] = np.array([lognb(int(y), r) for y in yy])
    return _cache[r]

def hilbert(a, b):
    diff = a - b
    return diff.max() - diff.min()

def run(name, f, K, steps, report):
    W = lambda k: f(k) + 1
    top = np.full(W(K), -np.inf); top[-1] = 0.0
    bot = np.full(W(K), -np.inf); bot[0] = 0.0
    out = []
    for j in range(1, steps + 1):
        k = K + j - 1
        top = step(top, W(k), W(k + 1)); bot = step(bot, W(k), W(k + 1))
        top -= top.max(); bot -= bot.max()
        if j in report:
            out.append("L=%d:%.3f" % (K + j, hilbert(top, bot)))
    print("%-6s K=%-3d" % (name, K), " ".join(out))

run("k", lambda k: k, 10, 160, (10, 20, 40, 80, 160))
run("k", lambda k: k, 40, 160, (10, 20, 40, 80, 160))
run("k^2", lambda k: k * k, 4, 36, (4, 8, 16, 24, 36))
run("k^2", lambda k: k * k, 8, 32, (4, 8, 16, 24, 32))
run("2^k", lambda k: 2 ** k, 3, 9, (2, 4, 6, 8, 9))
run("2^k", lambda k: 2 ** k, 5, 7, (2, 4, 6, 7))
