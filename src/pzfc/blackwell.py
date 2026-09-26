"""Blackwell's order: saying "stronger" without inventing a scalar.

Experiment A (a row-stochastic matrix, states x outcomes) is *at least as
informative* as B iff there is a garbling -- a stochastic post-processing G --
with  A @ G == B.  (Blackwell 1953.)

This is a partial order, it is decidable by an LP, and its verdicts come with a
certificate: the matrix G itself.  Incomparability is a result, not a failure:
if neither direction holds, then any scalar that ranks the two has smuggled in
an external preference, and that preference is the reward you thought you had
dropped.

    notes/02-放弃标量之后如何度量.md  §4
"""

from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
from typing import Sequence

from .exact import F, Num, feasible


@dataclass
class Comparison:
    a_garbles_to_b: list[list[Fraction]] | None   # witness for A >= B
    b_garbles_to_a: list[list[Fraction]] | None   # witness for B >= A
    names: tuple[str, str] = ("A", "B")

    @property
    def verdict(self) -> str:
        first, second = self.names
        ab = self.a_garbles_to_b is not None
        ba = self.b_garbles_to_a is not None
        if ab and ba:
            return f"{first} and {second} are equivalent"
        if ab:
            return f"{first} strictly more informative than {second}"
        if ba:
            return f"{second} strictly more informative than {first}"
        return "incomparable"


def garbling(
    A: Sequence[Sequence[Num]], B: Sequence[Sequence[Num]]
) -> list[list[Fraction]] | None:
    """Find stochastic G with A @ G == B, or None.  Rows index states."""
    A = [[F(v) for v in r] for r in A]
    B = [[F(v) for v in r] for r in B]
    n_state, n_a = len(A), len(A[0])
    n_b = len(B[0])
    if len(B) != n_state:
        raise ValueError("A and B must have the same number of states")

    nvar = n_a * n_b
    idx = lambda a, b: a * n_b + b  # noqa: E731

    A_eq: list[list[Fraction]] = []
    b_eq: list[Fraction] = []

    for a in range(n_a):                       # G is row-stochastic
        row = [Fraction(0)] * nvar
        for b in range(n_b):
            row[idx(a, b)] = Fraction(1)
        A_eq.append(row)
        b_eq.append(Fraction(1))

    for s in range(n_state):                   # A @ G == B
        for b in range(n_b):
            row = [Fraction(0)] * nvar
            for a in range(n_a):
                row[idx(a, b)] = A[s][a]
            A_eq.append(row)
            b_eq.append(B[s][b])

    ok, x = feasible(A_eq, b_eq, nvar)
    if not ok or x is None:
        return None
    return [[x[idx(a, b)] for b in range(n_b)] for a in range(n_a)]


def compare(
    A: Sequence[Sequence[Num]],
    B: Sequence[Sequence[Num]],
    names: tuple[str, str] = ("A", "B"),
) -> Comparison:
    return Comparison(garbling(A, B), garbling(B, A), names)
