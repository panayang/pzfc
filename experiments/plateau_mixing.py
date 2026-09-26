"""Plateau mixing lengths (notes/93).

On a plateau where every block has size W, the checkpoint kernel is the fixed strictly positive
matrix K_W(t, t') = C(2W + 1 - t + t', W), t, t' in [0, W].  By Perron-Frobenius its powers contract
in Birkhoff's projective metric.  m(W) is the least m with Delta(K_W^m) <= 1.  Any heap whose
windows are W_j on plateaus of length >= m(W_j) is rigid (notes/93, Theorem 2).

Run: python experiments/plateau_mixing.py   (needs numpy)
"""
import numpy as np
from math import lgamma

def logC(n, k):
    return lgamma(n + 1) - lgamma(k + 1) - lgamma(n - k + 1)

def delta_log(L):
    d = 0.0
    for a in range(L.shape[0]):
        diff = L[a] - L
        d = max(d, (diff.max(axis=1) - diff.min(axis=1)).max())
    return d

def logmatmul(A, B):
    m = A.max(axis=1, keepdims=True); M = B.max(axis=0, keepdims=True)
    return np.log(np.exp(A - m) @ np.exp(B - M)) + m + M

for W in (4, 8, 16, 32, 64, 128):
    t = np.arange(W + 1)
    K = np.array([[logC(2 * W + 1 - a + b, W) for b in t] for a in t])
    P, m = K.copy(), 1
    while delta_log(P) > 1.0:
        P = logmatmul(P, K); P -= P.max(); m += 1
    print("W=%3d  one-step Delta=%7.2f  m(W)=%3d  m/W=%.2f" % (W, delta_log(K), m, m / W))
