"""Birkhoff diameters of checkpoint kernels (notes/78).

For the heap of prod_k (x^{f(k)} y^{f(k)} p q), compute in log-space the projective diameter
Delta(M_{K->L}) of the path-count kernel between checkpoint levels K and L.  The heap is rigid
(unique central linearization) iff Delta(M_{K->L}) -> 0 as L grows (notes/78, Theorem 2).

Run: python experiments/birkhoff_diameter.py poly   |   python experiments/birkhoff_diameter.py geom
"""
# Projective diameter of the path-count kernel between checkpoint levels K and L.
# State at level k = j when p_k is placed (j in [P_{k-1}, P_k - 1]); region column i allows
# j in [P_{k(i)-1}, P_{k(i)+1} - 1] where k(i) = max{k : P_k <= i}.
import numpy as np, bisect, sys
def P_of(f,K):
    P=[0]
    for k in range(1,K+1): P.append(P[-1]+f(k)+1)
    return P
def interval(P,i):
    k=bisect.bisect_right(P,i)-1          # P_k <= i < P_{k+1}
    lo=P[k-1] if k>=1 else 0
    hi=(P[k+1]-1) if k+1<len(P) else P[-1]
    return lo,hi
def row(P,K,L,j0):
    i=P[K]; lo,hi=interval(P,i)
    col=np.full(hi-lo+1,-np.inf); col[j0-lo:]=0.0; clo=lo
    for i in range(P[K]+1,P[L]):
        lo,hi=interval(P,i)
        prev=np.full(hi-lo+1,-np.inf)
        a=max(lo,clo); b=min(hi,clo+len(col)-1)
        if a<=b: prev[a-lo:b-lo+1]=col[a-clo:b-clo+1]
        col=np.logaddexp.accumulate(prev); m=col.max()
        col-=m
        clo=lo
    lo,hi=interval(P,P[L]-1)
    return np.array([col[j-clo] for j in range(P[L-1],P[L])])
def delta(f,K,L,Kmax):
    P=P_of(f,Kmax)
    R=np.array([row(P,K,L,j0) for j0 in range(P[K-1],P[K])])
    
    d=0.0
    for a in range(len(R)):
        diff=R[a]-R
        d=max(d,(diff.max(axis=1)-diff.min(axis=1)).max())
    return d
case=sys.argv[1]
if case=="poly":
    for K in (5,10,20):
        print("poly K=%d:"%K," ".join("L=%d D=%.3f"%(L,delta(lambda k:k,K,L,4*K+2)) for L in (K+2,2*K,3*K,4*K)))
else:
    for K in (2,3,4):
        print("geom K=%d:"%K," ".join("L=%d D=%.3f"%(L,delta(lambda k:2**k,K,L,K+10)) for L in (K+2,K+4,K+6,K+8)))
