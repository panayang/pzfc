"""Run the three obstruction invariants on toy systems.

    python experiments/demo.py

Everything is exact rational arithmetic, so "0" below means exactly zero.
"""

from __future__ import annotations

import sys
from fractions import Fraction
from math import sqrt
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))

from pzfc import EmpiricalModel, Scenario, compare, hodge, report  # noqa: E402
from pzfc.contextual import contextual_fraction  # noqa: E402


def rule(title: str) -> None:
    print(f"\n{'=' * 72}\n{title}\n{'=' * 72}")


# ===========================================================================
# 1. Bell / CHSH scenario: does the object have a global state?
# ===========================================================================

CHSH = Scenario(
    probes=("a1", "a2", "b1", "b2"),
    outcomes={p: (0, 1) for p in ("a1", "a2", "b1", "b2")},
    contexts=(("a1", "b1"), ("a1", "b2"), ("a2", "b1"), ("a2", "b2")),
)

half = Fraction(1, 2)


def correlated(ctx_flip: set[tuple[str, str]]) -> EmpiricalModel:
    table = {}
    for ctx in CHSH.contexts:
        if ctx in ctx_flip:
            table[ctx] = {(0, 1): half, (1, 0): half}
        else:
            table[ctx] = {(0, 0): half, (1, 1): half}
    return EmpiricalModel.build(CHSH, table)


def from_correlators(E: dict[tuple[str, str], Fraction]) -> EmpiricalModel:
    """Unbiased marginals, given +-1 correlators."""
    table = {}
    for ctx in CHSH.contexts:
        e = E[ctx]
        same, diff = (1 + e) / 4, (1 - e) / 4
        table[ctx] = {(0, 0): same, (1, 1): same, (0, 1): diff, (1, 0): diff}
    return EmpiricalModel.build(CHSH, table)


rule("1. Bell/CHSH: is there a single global state behind the answers?")

classical = correlated(set())
print(report(classical, "classical (shared random bit)"))

pr = correlated({("a2", "b2")})
print()
print(report(pr, "PR box (maximally non-local)"))

inv = Fraction(round(sqrt(0.5) * 10**9), 10**9)
quantum = from_correlators(
    {("a1", "b1"): inv, ("a1", "b2"): inv, ("a2", "b1"): inv, ("a2", "b2"): -inv}
)
print()
print(report(quantum, "quantum, Tsirelson-optimal (rational approx of 1/sqrt2)"))

print("\n  noisy PR box, CF as a function of the noise level:")
for num in (0, 1, 2, 3, 4):
    eps = Fraction(num, 4)
    mixed = {}
    for ctx in CHSH.contexts:
        d = {}
        for ev in CHSH.local_events(ctx):
            p_pr = pr.table[ctx].get(ev, Fraction(0))
            d[ev] = (1 - eps) * p_pr + eps * Fraction(1, 4)
        mixed[ctx] = d
    m = EmpiricalModel.build(CHSH, mixed)
    print(f"    noise={eps}   CF = {contextual_fraction(m)}")


# ===========================================================================
# 2. A memory architecture: three queries, pairwise sessions
# ===========================================================================

rule("2. A memory system probed two queries at a time")

MEM = Scenario(
    probes=("q1", "q2", "q3"),
    outcomes={"q1": (0, 1), "q2": (0, 1), "q3": (0, 1)},
    contexts=(("q1", "q2"), ("q2", "q3"), ("q1", "q3")),
)

# (a) a static lookup table: one global memory state, read does not disturb
static = EmpiricalModel.build(
    MEM,
    {
        ("q1", "q2"): {(0, 0): half, (1, 1): half},
        ("q2", "q3"): {(0, 0): half, (1, 1): half},
        ("q1", "q3"): {(0, 0): half, (1, 1): half},
    },
)
print(report(static, "(a) static lookup table"))

# (b) reading q1 alongside q3 changes q1's own marginal -> signalling
disturbing = EmpiricalModel.build(
    MEM,
    {
        ("q1", "q2"): {(1, 1): Fraction(4, 5), (0, 0): Fraction(1, 5)},
        ("q2", "q3"): {(0, 0): half, (1, 1): half},
        ("q1", "q3"): {(1, 1): Fraction(3, 10), (0, 0): Fraction(7, 10)},
    },
)
print()
print(report(disturbing, "(b) read-disturbing memory"))

# (c) Specker's triangle: every pair always disagrees.
#     Marginals are uniform, so nothing is disturbed -- yet three bits cannot
#     pairwise disagree, so no global memory state exists.
specker = EmpiricalModel.build(
    MEM,
    {ctx: {(0, 1): half, (1, 0): half} for ctx in MEM.contexts},
)
print()
print(report(specker, "(c) pairwise-inconsistent memory (Specker triangle)"))
print("      pairwise consistent, globally impossible: no state to read.")


# ===========================================================================
# 3. Hodge: how much of a leaderboard is real
# ===========================================================================

rule("3. Evaluation data: how much of it does a single scalar explain?")

items = ["A", "B", "C", "D"]
# A>B, B>C, C>A  (a Condorcet cycle), and everyone beats D by 2.
comparisons = {
    ("A", "B"): -1, ("B", "C"): -1, ("C", "A"): -1,
    ("D", "A"): 2, ("D", "B"): 2, ("D", "C"): 2,
}
res = hodge(items, comparisons)
print("  cyclic evaluation data:")
print(res.summary())

# the same systems judged coherently: every margin is a difference of one score
# (A=0, B=-1, C=-2, D=-2)
acyclic = {
    ("A", "B"): -1, ("B", "C"): -1, ("A", "C"): -2,
    ("D", "A"): 2, ("D", "B"): 1, ("D", "C"): 0,
}
print("\n  the same systems, coherent judges:")
print(hodge(items, acyclic).summary())


# ===========================================================================
# 4. Blackwell: "stronger" without a scalar
# ===========================================================================

rule("4. Comparing systems as a partial order, with certificates")

A = [[1, 0], [0, 1]]                                   # perfect discrimination
B = [[Fraction(7, 8), Fraction(1, 8)],                 # slightly noisy binary
     [Fraction(1, 8), Fraction(7, 8)]]
C = [[half, 0, half], [0, half, half]]                 # perfect half the time, else "dunno"

for nx, ny, X, Y in (("A", "B", A, B), ("B", "C", B, C), ("A", "C", A, C)):
    c = compare(X, Y, (nx, ny))
    print(f"  {nx} vs {ny:4s}: {c.verdict}")
    if c.a_garbles_to_b is not None:
        rows = "; ".join(
            "[" + ", ".join(str(v) for v in row) + "]" for row in c.a_garbles_to_b
        )
        print(f"            garbling witness (left -> right): {rows}")

print(
    "\n  B and C are incomparable: no garbling either way.\n"
    "  Any scalar that ranks them has imported an outside preference --\n"
    "  which is exactly the reward you thought you had dropped."
)
