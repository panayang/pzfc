"""Hodge decomposition of pairwise comparisons:
how much of a leaderboard is actually there.

Given an antisymmetric flow Y on pairs of systems (Y[i][j] = "how much j beats
i"), solve the weighted least squares

    min_phi  sum_{i<j} w_ij (phi_j - phi_i - Y_ij)^2

The gradient part is the best single scalar explanation.  Whatever is left is
curl + harmonic: structure that *provably* cannot be represented by any scalar
ranking, and whose size is a number you can put in front of a reviewer.

A nonzero residual means there is a Condorcet cycle.  In the language of
notes/00 §4: nonzero curvature of the comparison connection.

Reference for the method: HodgeRank (Jiang, Lim, Yao, Ye).
"""

from __future__ import annotations

import itertools
from dataclasses import dataclass
from fractions import Fraction
from typing import Sequence

from .exact import F, Num, solve_linear


@dataclass
class HodgeResult:
    potential: dict[str, Fraction]          # the best scalar score (gauge: first item = 0)
    gradient_ratio: Fraction                # fraction of comparison energy a scalar explains
    residual: dict[tuple[str, str], Fraction]
    curls: list[tuple[tuple[str, str, str], Fraction, bool]]
    """Triangles with nonzero curl.  The flag marks the strict subset that are
    *ordinal* cycles (A beats B beats C beats A).  A nonzero curl that is not an
    ordinal cycle is a cardinal inconsistency -- the margins do not add up --
    and it obstructs a scalar just as surely."""

    def ranking(self) -> list[tuple[str, Fraction]]:
        return sorted(self.potential.items(), key=lambda kv: -kv[1])

    @property
    def condorcet_cycles(self) -> list[tuple[tuple[str, str, str], Fraction]]:
        return [(t, c) for t, c, ordinal in self.curls if ordinal]

    def summary(self) -> str:
        gr = self.gradient_ratio
        lines = [
            f"  scalar-explainable energy   : {gr}  ({float(gr):.4f})",
            f"  irreducible (curl+harmonic) : {1 - gr}  ({float(1 - gr):.4f})",
            "  best scalar ranking         : "
            + ", ".join(f"{k}={float(v):+.3f}" for k, v in self.ranking()),
        ]
        if self.curls:
            ords = self.condorcet_cycles
            lines.append(
                f"  inconsistent triangles      : {len(self.curls)}"
                f"  (of which ordinal Condorcet cycles: {len(ords)})"
            )
            for tri, c, ordinal in self.curls[:5]:
                tag = "CONDORCET" if ordinal else "margins do not add up"
                lines.append(
                    f"    {tri[0]}->{tri[1]}->{tri[2]}->{tri[0]}  curl={float(c):+.4f}  [{tag}]"
                )
        else:
            lines.append("  inconsistent triangles      : none (a scalar is fully adequate)")
        return "\n".join(lines)


def hodge(
    items: Sequence[str],
    comparisons: dict[tuple[str, str], Num],
    weights: dict[tuple[str, str], Num] | None = None,
) -> HodgeResult:
    """``comparisons[(i, j)] = y`` means "j beats i by y"; the antisymmetric
    partner is implied and must not be given twice."""
    idx = {name: k for k, name in enumerate(items)}
    n = len(items)

    Y: dict[tuple[int, int], Fraction] = {}
    W: dict[tuple[int, int], Fraction] = {}
    for (a, b), y in comparisons.items():
        i, j = idx[a], idx[b]
        key = (min(i, j), max(i, j))
        if key in Y:
            raise ValueError(f"duplicate comparison for {a},{b}")
        val = F(y) if i < j else -F(y)
        Y[key] = val
        W[key] = F(weights[(a, b)]) if weights and (a, b) in weights else Fraction(1)

    # normal equations  L phi = rhs,  with the gauge phi_0 = 0
    L = [[Fraction(0)] * n for _ in range(n)]
    rhs = [Fraction(0)] * n
    for (i, j), y in Y.items():
        w = W[(i, j)]
        L[i][i] += w
        L[j][j] += w
        L[i][j] -= w
        L[j][i] -= w
        # from  sum_j w_kj (phi_k - phi_j) = - sum_j w_kj Y_kj , with Y_ji = -Y_ij
        rhs[i] -= w * y
        rhs[j] += w * y
    L[0] = [Fraction(1) if k == 0 else Fraction(0) for k in range(n)]
    rhs[0] = Fraction(0)

    phi = solve_linear(L, rhs)
    if phi is None:  # cannot happen once the gauge row is pinned
        raise RuntimeError("Hodge normal equations inconsistent")

    energy = sum(W[e] * Y[e] ** 2 for e in Y)
    grad_energy = sum(W[(i, j)] * (phi[j] - phi[i]) ** 2 for (i, j) in Y)
    ratio = Fraction(1) if energy == 0 else grad_energy / energy

    residual = {
        (items[i], items[j]): Y[(i, j)] - (phi[j] - phi[i]) for (i, j) in Y
    }

    # curl over triangles; gradients telescope away, so this is pure obstruction
    def flow(i: int, j: int) -> Fraction | None:
        if (i, j) in Y:
            return Y[(i, j)]
        if (j, i) in Y:
            return -Y[(j, i)]
        return None

    curls: list[tuple[tuple[str, str, str], Fraction, bool]] = []
    for i, j, k in itertools.combinations(range(n), 3):
        a, b, c = flow(i, j), flow(j, k), flow(k, i)
        if a is None or b is None or c is None:
            continue
        curl = a + b + c
        if curl != 0:
            # an ordinal cycle traverses the triangle in one consistent direction
            ordinal = (a > 0 and b > 0 and c > 0) or (a < 0 and b < 0 and c < 0)
            curls.append(((items[i], items[j], items[k]), curl, ordinal))
    curls.sort(key=lambda t: (not t[2], -abs(t[1])))

    return HodgeResult(
        potential={items[k]: phi[k] for k in range(n)},
        gradient_ratio=ratio,
        residual=residual,
        curls=curls,
    )
