"""pzfc -- obstruction invariants for measurement-first structures.

Three computable answers to "how do we measure after giving up a scalar":

    contextual.contextual_fraction   how much behaviour refuses a global state
    hodge.hodge                      how much of a leaderboard a scalar explains
    blackwell.compare                "stronger" as a partial order with certificates

None of them needs a baseline model or a reward.  Their reference values are
theorems.
"""

from .blackwell import compare, garbling
from .contextual import contextual_fraction, noncontextual_fraction, report
from .hodge import hodge
from .scenario import EmpiricalModel, Scenario

__all__ = [
    "Scenario",
    "EmpiricalModel",
    "contextual_fraction",
    "noncontextual_fraction",
    "report",
    "hodge",
    "compare",
    "garbling",
]
