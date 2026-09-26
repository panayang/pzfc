"""三条链的路状同步（1-2-3），尺度相当时的块直径（notes/112 §1）。

X-时间中每步以 1/3 推进一条链，(D1, D2) 的增量为 (1,0)、(-1,1)、(0,-1)。
第 k 个检查点：间隔 g_k = k 步，要求 D1 ∈ [1, W1_k]、D2 ∈ [1, W2_k]。
输出块核 M_{K→L}（起点为第 K 个检查点的盒中的点）的 Hilbert 射影直径。
"""
import sys
import numpy as np

def diameter(logM):
    # Δ = max_{i,j} [max_k (A_ik - A_jk) + max_l (A_jl - A_il)]
    A = logM[:, np.isfinite(logM).all(axis=0)]
    best = 0.0
    for i in range(A.shape[0]):
        d = A[i] - A           # 行 i 减去一切行 j
        best = max(best, (d.max(axis=1) + (-d).max(axis=1)).max())
    return best

def run(w1, w2, K, Ls):
    Lmax = max(Ls)
    mar = int(8 * np.sqrt(Lmax)) + 5
    n = max(w1(Lmax), w2(Lmax)) + 2 * mar + 2
    off = mar                      # 格点坐标 = 值 + off
    b1, b2 = w1(K), w2(K)
    # 增量使 D1 + 2 D2 (mod 3) 每步加 1：游走活在一个陪集上，起点取同一陪集
    starts = [(a, b) for a in range(1, b1 + 1) for b in range(1, b2 + 1) if (a + 2 * b) % 3 == 0]
    V = np.zeros((len(starts), n, n))
    for s, (a, b) in enumerate(starts):
        V[s, a + off, b + off] = 1.0
    logscale = np.zeros(len(starts))
    out = {}
    for k in range(K + 1, Lmax + 1):
        for _ in range(k):         # 间隔 g_k = k 步
            N = np.zeros_like(V)
            N[:, 1:, :] += V[:, :-1, :]          # (1,0)
            N[:, :-1, 1:] += V[:, 1:, :-1]       # (-1,1)
            N[:, :, :-1] += V[:, :, 1:]          # (0,-1)
            V = N / 3.0
        c1, c2 = w1(k), w2(k)
        mask = np.zeros((n, n), bool)
        mask[1 + off:c1 + 1 + off, 1 + off:c2 + 1 + off] = True
        V[:, ~mask] = 0.0
        s = V.sum(axis=(1, 2))
        V /= s[:, None, None]
        logscale += np.log(s)
        if k in Ls:
            box = V[:, mask]
            with np.errstate(divide='ignore'):
                out[k] = diameter(np.log(box))
            print(f"  L={k}: Δ={out[k]:.3f}", flush=True)
    return out

if __name__ == "__main__":
    cases = {
        "W1=W2=k":       (lambda k: k, lambda k: k),
        "W1=k,W2=k/2":   (lambda k: k, lambda k: max(1, k // 2)),
    }
    K = int(sys.argv[1]) if len(sys.argv) > 1 else 10
    Ls = [K + 5, 2 * K, 3 * K, 4 * K]
    for name, (w1, w2) in cases.items():
        print(name, "K =", K, flush=True)
        run(w1, w2, K, Ls)
