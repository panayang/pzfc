"""锥中采样链的调和函数误差（notes/116 §1）。

(D1, D2) 的单步增量为 (1,0)、(-1,1)、(0,-1)，采样链每 c 步观察一次。
60° 角：锥由 e1、e2 张成（D1 >= 1, D2 >= 1）；120° 角：由 e1、-e2 张成（D1 >= 1, D2 <= -1）。
在锥 ∩ {|w| < R}（w 为白化坐标）上精确求解 u(x) = E_x[h(Y_T)] 与逃逸概率 P_x(|Y_T| >= R)，
检验：|u - h| / V ≍ √c/|x|（引理 G），P_x(逃逸)·R^p / V 有界（引理 W′）。
"""
import numpy as np
import scipy.sparse as sp
import scipy.sparse.linalg as spl

Sig = np.array([[2/3, -1/3], [-1/3, 2/3]])
ev, U = np.linalg.eigh(Sig)
L = U @ np.diag(ev ** -0.5) @ U.T          # 白化

def setup(kind):
    a = L @ np.array([1.0, 0.0])
    b = L @ (np.array([0.0, 1.0]) if kind == 60 else np.array([0.0, -1.0]))
    ta, tb = np.arctan2(a[1], a[0]), np.arctan2(b[1], b[0])
    alpha = (tb - ta) % (2 * np.pi)
    if alpha > np.pi:                        # 取正向的夹角
        alpha = 2 * np.pi - alpha; ta, tb = tb, ta
    return ta, alpha

def kernel(c):
    k = {(0, 0): 1.0}
    for _ in range(c):
        n = {}
        for (x, y), q in k.items():
            for dx, dy in ((1, 0), (-1, 1), (0, -1)):
                n[(x + dx, y + dy)] = n.get((x + dx, y + dy), 0) + q / 3
        k = n
    return list(k.items())

def run(kind, c, R):
    ta, alpha = setup(kind)
    p = np.pi / alpha
    sgn2 = 1 if kind == 60 else -1
    def geo(x, y):
        w = L @ np.array([x, y], float)
        r = np.hypot(*w)
        th = (np.arctan2(w[1], w[0]) - ta + np.pi - alpha / 2) % (2 * np.pi) - np.pi + alpha / 2
        d = min(r * np.sin(th) if 0 < th < np.pi / 2 else r,
                r * np.sin(alpha - th) if alpha - np.pi / 2 < th < alpha else r)
        return r, th, max(d, 0.0)
    def h(x, y):
        r, th, _ = geo(x, y)
        return r ** p * np.sin(p * th)
    def inside(x, y):
        return x >= 1 and sgn2 * y >= 1 and geo(x, y)[0] < R
    M = int(3 * R)
    states = [(x, sgn2 * y) for x in range(1, M) for y in range(1, M) if inside(x, sgn2 * y)]
    idx = {s: i for i, s in enumerate(states)}
    K = kernel(c)
    rows, cols, vals = [], [], []
    bh = np.zeros(len(states)); be = np.zeros(len(states))
    for i, (x, y) in enumerate(states):
        for (dx, dy), q in K:
            t = (x + dx, y + dy)
            j = idx.get(t)
            if j is not None:
                rows.append(i); cols.append(j); vals.append(q)
            else:
                bh[i] += q * h(*t)
                if geo(*t)[0] >= R and t[0] >= 1 and sgn2 * t[1] >= 1:
                    be[i] += q
    A = sp.identity(len(states), format='csr') - sp.csr_matrix((vals, (rows, cols)), shape=(len(states),) * 2)
    lu = spl.splu(A.tocsc())
    u = lu.solve(bh); esc = lu.solve(be)
    out = []
    for i, s in enumerate(states):
        r, th, d = geo(*s)
        V = (r + np.sqrt(c)) ** (p - 1) * (d + np.sqrt(c))
        out.append((r, d, abs(u[i] - h(*s)) / V, esc[i] * R ** p / V))
    return p, np.array(out)

for kind in (60, 120):
    for c in (1, 4):
        R = 45
        p, o = run(kind, c, R)
        print(f"角 {kind}°  p={p:.3f}  c={c}  R={R}", flush=True)
        for lo, hi in ((2, 4), (4, 8), (8, 16), (16, 30)):
            m = (o[:, 0] >= lo * np.sqrt(c) / np.sqrt(c) * 1.0) & (o[:, 0] < hi)
            if m.sum() == 0: continue
            err = o[m, 2]; esc = o[m, 3]
            print(f"  |x|∈[{lo},{hi}): 相对误差 max={err.max():.3f} 中位={np.median(err):.3f} ;"
                  f" max·|x|/√c={np.max(err * o[m,0]) / np.sqrt(c):.2f} ; 逃逸·R^p/V ∈ [{esc.min():.2f},{esc.max():.2f}]", flush=True)
