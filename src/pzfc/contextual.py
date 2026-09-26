"""The contextual fraction: how much of an object's behaviour refuses to come
from a single global state.

    max  sum_s w_s
    s.t. sum_{s|C = o} w_s  <=  e_C(o)     for every context C and event o
         w >= 0

    CF = 1 - (that maximum)

CF == 0  <=>  the model has a global section
         <=>  a classical hidden-variable / single-global-memory explanation exists
         <=>  (Fine's theorem) no Bell-type inequality is violated

The point of this number, in the ML setting, is that its reference value is a
*theorem*, not a competitor model.  You do not need a baseline to report it.

    notes/02-放弃标量之后如何度量.md  §2
"""

from __future__ import annotations

from fractions import Fraction

from .exact import OPTIMAL, lp_max
from .scenario import EmpiricalModel


def noncontextual_fraction(model: EmpiricalModel) -> tuple[Fraction, dict]:
    """Returns (NCF, the maximal sub-distribution over global assignments)."""
    sc = model.scenario
    globals_ = sc.global_assignments()
    n = len(globals_)

    A_ub: list[list[int]] = []
    b_ub: list[Fraction] = []
    for ctx, dist in model.table.items():
        for ev in sc.local_events(ctx):
            row = [
                1 if tuple(g[q] for q in ctx) == ev else 0
                for g in globals_
            ]
            A_ub.append(row)
            b_ub.append(dist.get(ev, Fraction(0)))

    status, w, val = lp_max([1] * n, A_ub=A_ub, b_ub=b_ub)
    if status != OPTIMAL:
        raise RuntimeError(f"contextual-fraction LP returned {status}")

    witness = {
        tuple(sorted(g.items())): wi
        for g, wi in zip(globals_, w)
        if wi != 0
    }
    return val, witness


def contextual_fraction(model: EmpiricalModel) -> Fraction:
    """CF in [0, 1].  Exact rational.

    Note this is only meaningful for no-signalling models; check
    ``model.disturbance()`` first.  For a signalling model the LP still returns
    a number, but "global section" is no longer the right null hypothesis --
    disturbance is already a stronger statement.
    """
    ncf, _ = noncontextual_fraction(model)
    return 1 - ncf


def report(model: EmpiricalModel, name: str = "model") -> str:
    d, arg = model.disturbance()
    lines = [f"{name}:"]
    lines.append(f"  probe complex is a simplex : {model.scenario.is_simplex}")
    lines.append(f"  disturbance (max TV)       : {d}  ({float(d):.4f})")
    if arg:
        c1, c2, shared = arg
        lines.append(f"    worst pair               : {c1} vs {c2} on {shared}")
    cf = contextual_fraction(model)
    lines.append(f"  contextual fraction  CF    : {cf}  ({float(cf):.4f})")
    if d == 0:
        verdict = (
            "explainable by a single global state"
            if cf == 0
            else "provably NOT explainable by any single global state"
        )
    else:
        verdict = "signalling: reading disturbs; classical evaluation already inapplicable"
    lines.append(f"  verdict                    : {verdict}")
    return "\n".join(lines)
