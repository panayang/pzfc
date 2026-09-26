"""Numerical check of the three-block sandwich (notes/97, Lemmas 6, 8-10) for f(k) = k.

For a block K -> m1 -> m2 -> L with X-times ~ Theta W^2, W^2, Theta W^2 (W = W_K), print
  eps_A = min_d A(d,S)/A(d,.),  eps_C = min_u C(V,u)/C(.,u),  beta ratio = max Q / min_{S x V} Q,
the resulting bound 2 log(beta_ratio / (eps_A eps_C)), and the true Delta(M_{K->L}).
Run: python experiments/sandwich_check.py
"""
import numpy as np
from math import lgamma, log

def lognb(y, r):
    return lgamma(r + y) - lgamma(y + 1) - lgamma(r) - (r + y) * log(2.0)

def kernel(Wk, Wn):  # log q(d, d'), d in [1,Wk], d' in [1,Wn]
    d = np.arange(1, Wk + 1)[:, None]; dn = np.arange(1, Wn + 1)[None, :]
    y = Wn - (dn - d)
    out = np.full(y.shape, -np.inf)
    ok = y >= 0
    out[ok] = np.vectorize(lambda yy: lognb(int(yy), Wn))(y[ok])
    return out

def logmm(A, B):
    m = A.max(axis=1, keepdims=True); M = B.max(axis=0, keepdims=True)
    m[~np.isfinite(m)] = 0; M[~np.isfinite(M)] = 0
    with np.errstate(divide='ignore'):
        return np.log(np.exp(A - m) @ np.exp(B - M)) + m + M

def product(W, a, b):
    P = None
    for k in range(a, b):
        K = kernel(W(k), W(k + 1))
        P = K if P is None else logmm(P, K)
    return P

def delta(L):
    d = 0.0
    for i in range(L.shape[0]):
        diff = L[i] - L
        d = max(d, np.nanmax(diff.max(axis=1) - diff.min(axis=1)))
    return d

def lse(v, axis):
    m = v.max(axis=axis, keepdims=True)
    return (np.log(np.exp(v - m).sum(axis=axis, keepdims=True)) + m).squeeze(axis)

def run(K, Theta):
    W = lambda k: k + 1
    Wk = W(K)
    P = lambda k: sum(W(l) for l in range(1, k + 1))
    def lvl(start, T):
        l = start
        while P(l) - P(start) < T: l += 1
        return l
    m1 = lvl(K, Theta * Wk * Wk); m2 = lvl(m1, Wk * Wk); L = lvl(m2, Theta * Wk * Wk)
    A = product(W, K, m1); Q = product(W, m1, m2); C = product(W, m2, L)
    S = np.arange(Wk // 4, Wk // 2 + 1) - 1  # indices of [W/4, W/2]
    epsA = np.exp(lse(A[:, S], 1) - lse(A, 1)).min()
    epsC = np.exp(lse(C[S, :], 0) - lse(C, 0)).min()
    br = np.exp(Q.max() - Q[np.ix_(S, S)].min())
    M = logmm(logmm(A, Q), C)
    print("K=%d W=%d levels %d->%d->%d->%d  epsA=%.3f epsC=%.3f beta=%.2f  bound=%.2f  Delta=%.4f"
          % (K, Wk, K, m1, m2, L, epsA, epsC, br, 2 * log(br / (epsA * epsC)), delta(M)))

for K in (12, 20, 30):
    run(K, 1)
