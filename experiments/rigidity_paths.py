"""Rigidity experiment (notes/73).

Heap of the word prod_k (x^{f(k)} y^{f(k)} p q) over the dependence path x - p - q - y.
Its linearizations are monotone lattice paths (i, j) = (progress on the chain x..p, progress on
the chain y..q) that stay in a region fixed by the synchronizations p_k < q_k < p_{k+1}.
For far endpoints E in different directions, print the mean x-fraction at an early time T under
the uniform path measure to E.  If the limit does not depend on the direction of E, the heap has
a unique central linearization (rigid); if it does, the direction at infinity is a hidden rate.

Run: python experiments/rigidity_paths.py   (needs numpy)
"""
import numpy as np, sys
def setup(f, K):
    P=[0]; Q=[0]
    for k in range(1,K+1):
        P.append(P[-1]+f(k)+1); Q.append(Q[-1]+f(k)+1)
    return P,Q
def allowed_grid(P,Q):
    I=P[-1]; J=Q[-1]
    ii=np.arange(I+1)[:,None]; jj=np.arange(J+1)[None,:]
    ok=np.ones((I+1,J+1),bool)
    for k in range(1,len(P)):
        ok &= ~((ii>=P[k]) & (jj<Q[k-1]))
        ok &= ~((jj>=Q[k]) & (ii<P[k]))
    return ok
def forward(ok):
    I,J=ok.shape; N=np.zeros((I,J)); N[0,0]=1.0
    for d in range(1,I+J-1):
        i=np.arange(max(0,d-J+1),min(I-1,d)+1); j=d-i
        v=np.zeros(len(i))
        m=i>0; v[m]+=N[i[m]-1,j[m]]
        m=j>0; v[m]+=N[i[m],j[m]-1]
        v*=ok[i,j]; s=v.max()
        if s>0: v/=s
        N[i,j]=v
    return N
def backward(ok,E):
    iE,jE=E; M=np.zeros(ok.shape); M[iE,jE]=1.0
    for d in range(iE+jE-1,-1,-1):
        i=np.arange(max(0,d-jE),min(iE,d)+1); j=d-i
        v=np.zeros(len(i))
        m=i+1<=iE; v[m]+=M[i[m]+1,j[m]]
        m=j+1<=jE; v[m]+=M[i[m],j[m]+1]
        v*=ok[i,j]; s=v.max()
        if s>0: v/=s
        M[i,j]=v
    return M
def profile(ok,N,E,T):
    M=backward(ok,E)
    i=np.arange(max(0,T-ok.shape[1]+1),min(ok.shape[0]-1,T)+1); j=T-i
    w=N[i,j]*M[i,j]; w/=w.sum()
    return (w*i).sum()/T  # mean fraction of X-progress at time T
for name,f,K in [("poly f(k)=k",lambda k:k,80),("geom f(k)=2^k",lambda k:2**k,11)]:
    P,Q=setup(f,K); ok=allowed_grid(P,Q); N=forward(ok)
    I,J=P[-1],Q[-1]
    # endpoints on the last row/column region with different slopes: take E=(P[K],j) for allowed j
    js=[j for j in range(J+1) if ok[I,j]]
    cand=[js[0],js[len(js)//2],js[-1]]
    T=P[max(2,K//3)]
    print(name,"grid",I,J,"time T",T)
    for jE in cand:
        print("  endpoint (",I,",",jE,") slope y/x=%.3f"%(jE/I)," mean x-fraction at T: %.4f"%profile(ok,N,(I,jE),T))
