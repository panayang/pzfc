"""Exact rational linear algebra and linear programming.

No dependencies. Everything runs over ``fractions.Fraction`` so the obstruction
invariants come out as exact rationals rather than floats -- which matters when
the whole point is to distinguish "this is exactly zero" from "this is small".

Two-phase simplex with Bland's rule: exact arithmetic plus Bland guarantees
termination (no cycling, no numerical drift).
"""

from __future__ import annotations

from fractions import Fraction
from typing import Iterable, Sequence

Num = Fraction | int | str


def F(x: Num) -> Fraction:
    return x if isinstance(x, Fraction) else Fraction(x)


def vec(xs: Iterable[Num]) -> list[Fraction]:
    return [F(x) for x in xs]


def mat(rows: Iterable[Iterable[Num]]) -> list[list[Fraction]]:
    return [vec(r) for r in rows]


# --------------------------------------------------------------------------
# simplex
# --------------------------------------------------------------------------

INFEASIBLE = "infeasible"
UNBOUNDED = "unbounded"
OPTIMAL = "optimal"


def _pivot(T: list[list[Fraction]], basis: list[int], row: int, col: int) -> None:
    p = T[row][col]
    T[row] = [v / p for v in T[row]]
    pr = T[row]
    for r in range(len(T)):
        if r != row and T[r][col] != 0:
            f = T[r][col]
            T[r] = [a - f * b for a, b in zip(T[r], pr)]
    basis[row] = col


def _solve_tableau(T: list[list[Fraction]], basis: list[int], ncols: int) -> str:
    """Run simplex on a tableau whose last row holds reduced costs (minimise)."""
    m = len(T) - 1
    while True:
        # Bland: lowest-index column with negative reduced cost.
        col = -1
        for j in range(ncols):
            if T[m][j] < 0:
                col = j
                break
        if col < 0:
            return OPTIMAL
        # ratio test, Bland tie-break on smallest basis index
        row, best, best_basis = -1, None, None
        for r in range(m):
            if T[r][col] > 0:
                ratio = T[r][ncols] / T[r][col]
                if best is None or ratio < best or (ratio == best and basis[r] < best_basis):
                    row, best, best_basis = r, ratio, basis[r]
        if row < 0:
            return UNBOUNDED
        _pivot(T, basis, row, col)


def lp_min_standard(
    A: Sequence[Sequence[Fraction]],
    b: Sequence[Fraction],
    c: Sequence[Fraction],
) -> tuple[str, list[Fraction] | None, Fraction | None]:
    """min c.x subject to A x = b, x >= 0.  Rows with b_i < 0 are negated."""
    A = [list(r) for r in A]
    b = list(b)
    m, n = len(A), len(c)
    for i in range(m):
        if b[i] < 0:
            A[i] = [-v for v in A[i]]
            b[i] = -b[i]

    # ---- phase 1: minimise the sum of artificials -------------------------
    N = n + m
    T = [A[i] + [Fraction(1) if j == i else Fraction(0) for j in range(m)] + [b[i]] for i in range(m)]
    obj = [Fraction(0)] * n + [Fraction(1)] * m + [Fraction(0)]
    T.append(obj)
    basis = list(range(n, n + m))
    for r in range(m):  # price out the artificial basis
        T[m] = [a - b_ for a, b_ in zip(T[m], T[r])]

    if _solve_tableau(T, basis, N) != OPTIMAL:
        return INFEASIBLE, None, None
    if -T[m][N] != 0:
        return INFEASIBLE, None, None

    # drive any artificial still in the basis out (or drop a redundant row)
    for r in range(m - 1, -1, -1):
        if basis[r] >= n:
            piv = next((j for j in range(n) if T[r][j] != 0), None)
            if piv is None:
                del T[r]           # redundant constraint
                del basis[r]
            else:
                _pivot(T, basis, r, piv)

    # ---- phase 2 ----------------------------------------------------------
    m2 = len(T) - 1
    T2 = [[T[r][j] for j in range(n)] + [T[r][N]] for r in range(m2)]
    T2.append(list(c) + [Fraction(0)])
    for r in range(m2):
        cb = c[basis[r]]
        if cb != 0:
            T2[m2] = [a - cb * b_ for a, b_ in zip(T2[m2], T2[r])]

    status = _solve_tableau(T2, basis, n)
    if status != OPTIMAL:
        return status, None, None

    x = [Fraction(0)] * n
    for r in range(m2):
        if basis[r] < n:
            x[basis[r]] = T2[r][n]
    return OPTIMAL, x, -T2[m2][n]


def lp_max(
    c: Sequence[Num],
    A_ub: Sequence[Sequence[Num]] | None = None,
    b_ub: Sequence[Num] | None = None,
    A_eq: Sequence[Sequence[Num]] | None = None,
    b_eq: Sequence[Num] | None = None,
) -> tuple[str, list[Fraction] | None, Fraction | None]:
    """max c.x  s.t.  A_ub x <= b_ub,  A_eq x = b_eq,  x >= 0.

    Returns (status, x restricted to the original variables, objective value).
    """
    c = vec(c)
    n = len(c)
    A_ub = mat(A_ub) if A_ub else []
    b_ub = vec(b_ub) if b_ub else []
    A_eq = mat(A_eq) if A_eq else []
    b_eq = vec(b_eq) if b_eq else []

    n_slack = len(A_ub)
    rows: list[list[Fraction]] = []
    rhs: list[Fraction] = []
    for i, row in enumerate(A_ub):
        rows.append(list(row) + [Fraction(1) if j == i else Fraction(0) for j in range(n_slack)])
        rhs.append(b_ub[i])
    for i, row in enumerate(A_eq):
        rows.append(list(row) + [Fraction(0)] * n_slack)
        rhs.append(b_eq[i])

    obj = [-v for v in c] + [Fraction(0)] * n_slack  # min(-c) == max(c)
    status, x, val = lp_min_standard(rows, rhs, obj)
    if status != OPTIMAL:
        return status, None, None
    return OPTIMAL, x[:n], -val


def feasible(
    A_eq: Sequence[Sequence[Num]],
    b_eq: Sequence[Num],
    n: int,
) -> tuple[bool, list[Fraction] | None]:
    """Is {x >= 0 : A_eq x = b_eq} non-empty?  Returns a witness when it is."""
    status, x, _ = lp_max([Fraction(0)] * n, A_eq=A_eq, b_eq=b_eq)
    return (status == OPTIMAL), x


# --------------------------------------------------------------------------
# exact linear solve (for the Hodge normal equations)
# --------------------------------------------------------------------------

def solve_linear(A: Sequence[Sequence[Num]], b: Sequence[Num]) -> list[Fraction] | None:
    """Solve A x = b exactly.  Free variables are pinned to 0.

    Returns None only if the system is inconsistent.
    """
    A = mat(A)
    b = vec(b)
    m, n = len(A), len(A[0]) if A else 0
    M = [A[i] + [b[i]] for i in range(m)]

    pivots: list[int] = []
    r = 0
    for col in range(n):
        p = next((i for i in range(r, m) if M[i][col] != 0), None)
        if p is None:
            continue
        M[r], M[p] = M[p], M[r]
        M[r] = [v / M[r][col] for v in M[r]]
        for i in range(m):
            if i != r and M[i][col] != 0:
                f = M[i][col]
                M[i] = [a - f * c_ for a, c_ in zip(M[i], M[r])]
        pivots.append(col)
        r += 1
        if r == m:
            break

    for i in range(r, m):  # consistency of the zero rows
        if all(v == 0 for v in M[i][:n]) and M[i][n] != 0:
            return None

    x = [Fraction(0)] * n
    for i, col in enumerate(pivots):
        x[col] = M[i][n]
    return x
