"""四条链的路状同步 1–2–3–4，尺度相当时的块直径（notes/123 §3.3）。

X-时间中每步以 1/4 推进一条链；差 (D1, D2, D3) 的增量为
e1: (1,0,0)、e2: (-1,1,0)、e3: (0,-1,1)、e4: (0,0,-1)。D1 + 2D2 + 3D3 (mod 4) 每步加 1。
第 k 个检查点：间隔 k 步，要求 D1, D2, D3 ∈ [1, W_k]。窗口盒有 8 个角，其中 6 个是混合角。
"""
import numpy as np

def diameter(logM):
    A = logM[:, np.isfinite(logM).all(axis=0)]
    best = 0.0
    for i in range(A.shape[0]):
        d = A[i] - A
        best = max(best, (d.max(axis=1) + (-d).max(axis=1)).max())
    return best

def run(w, K, Ls):
    Lmax = max(Ls); mar = int(3 * np.sqrt(Lmax)) + 3
    n = w(Lmax) + 2 * mar + 2; off = mar
    b = w(K)
    starts = [(a, c, d) for a in range(1, b + 1) for c in range(1, b + 1) for d in range(1, b + 1)
              if (a + 2 * c + 3 * d) % 4 == 0]
    V = np.zeros((len(starts), n, n, n))
    for s, (a, c, d) in enumerate(starts):
        V[s, a + off, c + off, d + off] = 1.0
    for k in range(K + 1, Lmax + 1):
        for _ in range(k):
            N = np.zeros_like(V)
            N[:, 1:, :, :] += V[:, :-1, :, :]                 # e1
            N[:, :-1, 1:, :] += V[:, 1:, :-1, :]              # e2
            N[:, :, :-1, 1:] += V[:, :, 1:, :-1]              # e3
            N[:, :, :, :-1] += V[:, :, :, 1:]                 # e4
            V = N / 4.0
        c = w(k)
        mask = np.zeros((n, n, n), bool)
        mask[1 + off:c + 1 + off, 1 + off:c + 1 + off, 1 + off:c + 1 + off] = True
        V[:, ~mask] = 0.0
        V /= V.sum(axis=(1, 2, 3))[:, None, None, None]
        if k in Ls:
            with np.errstate(divide='ignore'):
                print(f"  L={k}: Δ={diameter(np.log(V[:, mask])):.3f}", flush=True)

for K in (5, 7):
    print("W = k, K =", K, flush=True)
    run(lambda k: k, K, [K + 3, 2 * K, 3 * K, 4 * K])
