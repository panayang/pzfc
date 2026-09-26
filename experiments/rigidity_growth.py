"""Rigidity versus growth of synchronization gaps (notes/83).

Birkhoff diameters Delta(M_{K->L}) for block sizes k^2, k^3, 1.5^k.  Delta -> 0 means rigid;
a positive limit means a hidden rate inside the component.  The predicted threshold is
rho_k = f(k)/P_k: rigid iff rho_k -> 0.

Run: python experiments/rigidity_growth.py "k^2"   (or "k^3", "1.5^k")
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

import math
tests={"k^2":(lambda k:k*k,[(4,(6,8,12,16)),(6,(8,12,18))]),
       "k^3":(lambda k:k**3,[(3,(5,6,9,12)),(4,(6,8,12))]),
       "1.5^k":(lambda k:int(1.5**k),[(4,(6,8,10,12,14)),(6,(8,10,12,14,16))])}
name=sys.argv[1]; f,plan=tests[name]
for K,Ls in plan:
    Kmax=max(Ls)+2
    P=P_of(f,Kmax)
    print(name,"K=%d"%K," ".join("L=%d D=%.3f"%(L,delta(f,K,L,Kmax)) for L in Ls),"| f(L)/P_L=%.3f"%(f(max(Ls))/P[max(Ls)]))
