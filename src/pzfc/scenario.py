"""Probe complexes and empirical models -- the PZFC notion of "object".

An object is not a set of points.  It is the family of answers it gives,
indexed by which questions you are allowed to ask together.

    notes/01-三个旋钮与-PZFC-公理.md  §2.1
"""

from __future__ import annotations

import itertools
from dataclasses import dataclass
from fractions import Fraction
from typing import Hashable, Sequence

from .exact import F, Num

Outcome = Hashable
Context = tuple[str, ...]
LocalEvent = tuple[Outcome, ...]


@dataclass(frozen=True)
class Scenario:
    """A probe complex: which questions exist, what they can answer, and which
    of them may be asked in one and the same act.

    ``contexts`` lists the *maximal* compatible sets.  The compatibility
    relation is recovered as "co-occurs in some context"; note that it is
    deliberately **not** required to be transitive -- that non-transitivity is
    the whole source of contextuality.
    """

    probes: tuple[str, ...]
    outcomes: dict[str, tuple[Outcome, ...]]
    contexts: tuple[Context, ...]

    def __post_init__(self) -> None:
        for c in self.contexts:
            for q in c:
                if q not in self.probes:
                    raise ValueError(f"context {c} mentions unknown probe {q!r}")

    @property
    def is_simplex(self) -> bool:
        """True iff some single context contains every probe.

        This is the degenerate case of `notes/00 §3`: linear time with a perfect
        record.  On a simplex every no-signalling model glues, so CF == 0 always
        and no obstruction can ever be exhibited.
        """
        return any(set(c) == set(self.probes) for c in self.contexts)

    def local_events(self, context: Sequence[str]) -> list[LocalEvent]:
        return [tuple(e) for e in itertools.product(*(self.outcomes[q] for q in context))]

    def global_assignments(self) -> list[dict[str, Outcome]]:
        """All sections over the whole probe set -- the candidate "hidden states"."""
        return [
            dict(zip(self.probes, combo))
            for combo in itertools.product(*(self.outcomes[q] for q in self.probes))
        ]


@dataclass
class EmpiricalModel:
    """For each context, a distribution over that context's joint outcomes."""

    scenario: Scenario
    table: dict[Context, dict[LocalEvent, Fraction]]

    @classmethod
    def build(
        cls, scenario: Scenario, table: dict[Context, dict[LocalEvent, Num]]
    ) -> "EmpiricalModel":
        norm = {
            ctx: {ev: F(p) for ev, p in dist.items() if F(p) != 0}
            for ctx, dist in table.items()
        }
        for ctx, dist in norm.items():
            total = sum(dist.values(), Fraction(0))
            if total != 1:
                raise ValueError(f"context {ctx} sums to {total}, not 1")
        return cls(scenario, norm)

    # -- marginals ---------------------------------------------------------

    def marginal(self, context: Context, sub: Sequence[str]) -> dict[LocalEvent, Fraction]:
        idx = [context.index(q) for q in sub]
        out: dict[LocalEvent, Fraction] = {}
        for ev, p in self.table[context].items():
            key = tuple(ev[i] for i in idx)
            out[key] = out.get(key, Fraction(0)) + p
        return out

    # -- disturbance / signalling -----------------------------------------

    def disturbance(self) -> tuple[Fraction, tuple[Context, Context, tuple[str, ...]] | None]:
        """How much does the answer to a probe depend on what *else* was asked?

        Returns the largest total-variation distance between the two marginals
        that two contexts induce on their shared probes, together with the pair
        achieving it.

        Zero  => the model is no-signalling, and CF is meaningful.
        > 0   => probing disturbs.  For a memory architecture this is the direct,
                 reportable evidence that "reading changes the system", and it
                 already rules out any evaluation that assumes a fixed global
                 state.  (This is a plain disturbance measure, not the LP-based
                 signalling fraction of the literature.)
        """
        worst, arg = Fraction(0), None
        for c1, c2 in itertools.combinations(self.table.keys(), 2):
            shared = tuple(q for q in c1 if q in c2)
            if not shared:
                continue
            m1, m2 = self.marginal(c1, shared), self.marginal(c2, shared)
            keys = set(m1) | set(m2)
            tv = sum(
                abs(m1.get(k, Fraction(0)) - m2.get(k, Fraction(0))) for k in keys
            ) / 2
            if tv > worst:
                worst, arg = tv, (c1, c2, shared)
        return worst, arg

    @property
    def is_no_signalling(self) -> bool:
        return self.disturbance()[0] == 0
