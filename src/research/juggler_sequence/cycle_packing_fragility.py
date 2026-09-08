"""Fragility audit of the run-type packing (Paper A Theorems 4.7--4.8).

Not a halt theorem, not a floor raise, and not a refutation of
Theorem 4.8. It prices the one hypothesis Theorem 4.7 needs but does
not state -- that the itinerary contains no `EE` -- in the units of the
result that depends on it, and it maps which of Paper A's claims rest
on the six-term packing rather than on the three-term charge below it.

Two facts drive the audit.

*The three-term charge is what Theorem 4.6 runs on.* Corollary 4.5's
"length-only parity charge" is not a two-class parity split; read
`cycle_finance.parity_rhs`, it is

    theta <= (6/5) [ e/(n log n) + (o-e)/(t log t) + e/(2 n^2 log n) ],

the three-class bound with internal odds at `t`. It is Lean as
`threeTerm_bound` (`FinanceTransfer.lean`) and needs no hypothesis
about `EE`. So the cutoff 25781, the 141-length set, and every floor
downstream of them are hypothesis-free.

*The six-term packing buys exactly one constant.* At any leftover
length the ratio of the two majorants is `e/(o-e)` up to the tiny
`t`- and `n^2`-scale terms, uniformly 1.4048 at the published floor.
That is the whole budget of the refinement, and the 42 lengths
Theorem 4.8 excludes die with margins strictly inside it.

`EE` inflates the packed majorant because the packing counts *blocks*:
with `m` cyclic `EE` adjacencies the even letters form `e - m` maximal
runs, so

    #valleys   = e - m           (one per maximal even run)
    #internals = o - e + m
    #cheap    <= min(o - e + m, e - m)
    #expensive  = (e - m) - #cheap

and `#cheap <= o - e` -- the form Theorem 4.7 displays -- holds only at
`m = 0`. `ee_model_holds` checks this counting on explicit words.

The second cap matters and is easy to miss: `#cheap` is bounded by the
lemma's `o - #blocks` *and* by the valley count it is a part of. The
two cross at `m = e - o/2`, where both equal `o/2`. So `EE` cannot
inflate the `n`-scale charge past `(o/2)/(o-e)` however much of it a
word carries -- beyond that crossing the valleys themselves run out.
That ceiling is what decides whether a given exclusion is inside the
gap or survives it, and it does not resolve the same way for all 42.
"""

from __future__ import annotations

import json
import math
from typing import Any

from research.juggler_sequence.cycle_budget_opt import (
    first_odd_image,
    oe_start_min,
)
from research.juggler_sequence.cycle_finance import (
    DATA_DIR,
    EPS_CONST,
    MIN_STATE,
    PUBLISHED_FLOOR,
    sha256_int_list,
)
from research.juggler_sequence.paper_a_audit import o_min, theta

# The 42 lengths Theorem 4.8 excludes, as the statement names them.
PACKING_DEATHS: tuple[int, ...] = tuple(56347 + 1054 * k for k in range(42))


def inv_log(x: int) -> float:
    if x < 3:
        return math.inf
    return 1.0 / (float(x) * math.log(x))


def three_term_rhs(
    n: int, length: int, odd_count: int, *, const: float = EPS_CONST
) -> float:
    """Corollary 4.5's charge, i.e. Lean `threeTerm_bound` times the 6/5 unroll."""
    even = length - odd_count
    ln = math.log(n)
    t = n**1.5
    return const * (
        even / (n * ln)
        + (odd_count - even) / (t * math.log(t))
        + even / (2.0 * n * n * ln)
    )


def packed_rhs_with_ee(
    n: int, length: int, odd_count: int, ee: int, *, const: float = EPS_CONST
) -> float | None:
    """Theorem 4.7's six-term charge for a word carrying `ee` cyclic `EE` adjacencies.

    `ee = 0` reproduces the displayed bound. The worst case puts as many
    valleys as the two caps allow at the cheap `n`-scale. Returns `None`
    when `ee` leaves no valley to charge.
    """
    even = length - odd_count
    valleys = even - ee
    cheap = min(odd_count - even + ee, valleys)
    expensive = valleys - cheap
    internal = odd_count - valleys
    if valleys < 1 or cheap < 1 or expensive < 0 or internal < 1:
        return None
    v = oe_start_min(n)
    t, t_plus = first_odd_image(n), first_odd_image(n + 2)
    return const * (
        inv_log(n)
        + (cheap - 1) * inv_log(n + 2)
        + expensive * inv_log(v)
        + inv_log(t)
        + (internal - 1) * inv_log(t_plus)
        + even * inv_log(n * n)
    )


def ee_to_resurrect(length: int, *, floor: int = PUBLISHED_FLOOR) -> int | None:
    """Least `EE` count at which the packed comparison stops excluding `length`.

    `None` if no admissible `EE` count does, which makes the exclusion
    robust to the missing hypothesis. The scan runs the whole admissible
    range rather than stopping at the first inadmissible `ee`: the
    majorant rises to the cap crossing and falls after it, so an early
    `None` is not evidence of robustness.
    """
    n = max(floor + 1, MIN_STATE)
    odd = o_min(length)
    even = length - odd
    th = theta(length, odd)
    for ee in range(even):
        rhs = packed_rhs_with_ee(n, length, odd, ee)
        if rhs is not None and th <= rhs:
            return ee
    return None


def ee_model_holds(word: str) -> bool:
    """The block counting of the docstring, checked cyclically on an explicit word."""
    length = len(word)
    if length == 0:
        return True
    odd = word.count("O")
    even = length - odd
    runs = sum(1 for i in range(length) if word[i] == "E" and word[i - 1] == "O")
    ee = sum(1 for i in range(length) if word[i] == "E" and word[i - 1] == "E")
    valleys = sum(1 for i in range(length) if word[i] == "O" and word[i - 1] == "E")
    internals = sum(1 for i in range(length) if word[i] == "O" and word[i - 1] == "O")
    return ee == even - runs and valleys == runs and internals == odd - valleys


def fragility_row(length: int, *, floor: int = PUBLISHED_FLOOR) -> dict[str, Any]:
    n = max(floor + 1, MIN_STATE)
    odd = o_min(length)
    even = length - odd
    th = theta(length, odd)
    r3 = three_term_rhs(n, length, odd)
    r6 = packed_rhs_with_ee(n, length, odd, 0)
    return {
        "L": length,
        "o": odd,
        "e": even,
        "theta_over_three_term": th / r3,
        "theta_over_packed": th / r6,
        # The refinement's entire budget: how much the packed majorant
        # may inflate before it is no better than the hypothesis-free one.
        "refinement_budget": r3 / r6,
        "survives_three_term": th <= r3,
        "dies_under_packing": th > r6,
        "ee_to_resurrect": ee_to_resurrect(length, floor=floor),
        # Diagnostic, not the verdict: the cap crossing on the n-scale part
        # alone, (o/2)/(o-e). The full majorant carries t- and n^2-scale
        # terms too, so the true ceiling is a little lower; `ee_to_resurrect`
        # scans the exact right-hand side and is what decides a row.
        "ee_inflation_ceiling": (odd / 2.0) / (odd - even),
        # Expected cyclic EE adjacencies with the evens placed uniformly.
        "ee_expected_if_random": even * (even - 1) / (length - 1),
    }


def fragility_scan(*, floor: int = PUBLISHED_FLOOR) -> dict[str, Any]:
    rows = [fragility_row(L, floor=floor) for L in PACKING_DEATHS]
    budgets = [row["refinement_budget"] for row in rows]
    fragile = [row for row in rows if row["ee_to_resurrect"] is not None]
    robust = [row for row in rows if row["ee_to_resurrect"] is None]
    inside = [
        row
        for row in fragile
        if row["ee_to_resurrect"] <= row["ee_expected_if_random"]
    ]
    return {
        "bound": "packing_fragility",
        "floor": floor,
        "n": max(floor + 1, MIN_STATE),
        "deaths_examined": len(rows),
        "sha256_deaths": sha256_int_list(list(PACKING_DEATHS)),
        # Every death survives the hypothesis-free charge and dies only under the packing.
        "all_survive_three_term": all(row["survives_three_term"] for row in rows),
        "all_die_under_packing": all(row["dies_under_packing"] for row in rows),
        "refinement_budget_min": min(budgets),
        "refinement_budget_max": max(budgets),
        # Deaths some admissible EE count voids, against those the cap
        # crossing protects however much EE the word carries.
        "deaths_fragile_to_ee": len(fragile),
        "deaths_robust_to_ee": len(robust),
        "robust_lengths": [row["L"] for row in robust],
        "ee_to_resurrect_min": min((r["ee_to_resurrect"] for r in fragile), default=None),
        "ee_to_resurrect_max": max((r["ee_to_resurrect"] for r in fragile), default=None),
        # Of the fragile ones, those needing less EE than a random placement expects.
        "deaths_inside_random_ee": len(inside),
        "rows": rows,
        "halt_theorem": False,
        "no_cycle_all_lengths": False,
        "refutes_theorem_4_8": False,
    }


# --- Feasibility: can an admissible word carry the EE that voids an exclusion? ---
#
# The constraints below are the ones Paper A proves for a cycle-minimum
# itinerary, and nothing else:
#   (1) above-anchor, every prefix j has 3^{a_j} >= 2^j;
#   (2) Theorem 3.29's run cap, an odd run beginning after i evens have been
#       consumed has length at most floor((e-i) * log2/log(3/2));
#   (3) o = o_min(L);
#   (4) the word shape OO...E (`cycleMin_word_shape`).
#
# The witness deliberately keeps runs of length at most two -- the packing's
# own extremal shape -- so that no run-structure claim is violated. What it
# breaks is the block/even-letter correspondence: k of the evens sit in a tail
# rather than one per block. That is the whole of the `EE` gap.

RUN_CAP_CONST = math.log(2) / math.log(1.5)


def blocks_word(odd: int, blocks: int) -> str:
    """Beatty interleaving of `odd - blocks` OOE blocks with `2*blocks - odd` OE blocks."""
    ooe = odd - blocks
    oe = 2 * blocks - odd
    if ooe < 0 or oe < 0:
        return ""
    parts = []
    for i in range(1, blocks + 1):
        is_ooe = (i * ooe + blocks - 1) // blocks - ((i - 1) * ooe + blocks - 1) // blocks
        parts.append("OOE" if is_ooe else "OE")
    return "".join(parts)


def ee_witness_word(odd: int, even: int, tail: int) -> str:
    """Blocks over `even - tail` evens, then a tail of `tail` evens."""
    return blocks_word(odd, even - tail) + "E" * tail


def above_anchor_min(word: str) -> float:
    """Least prefix surplus `a_j*log3 - j*log2`; nonnegative iff above-anchor."""
    a = 0
    worst = math.inf
    l2, l3 = math.log(2), math.log(3)
    for j, ch in enumerate(word, start=1):
        if ch == "O":
            a += 1
        worst = min(worst, a * l3 - j * l2)
    return worst


def max_odd_run(word: str) -> int:
    best = run = 0
    for ch in word:
        run = run + 1 if ch == "O" else 0
        best = max(best, run)
    return best


def run_caps_hold(word: str, even: int) -> bool:
    """Theorem 3.29's cap on every odd run, at the position where it starts."""
    used = 0
    i = 0
    while i < len(word):
        if word[i] == "E":
            used += 1
            i += 1
            continue
        run = 0
        while i < len(word) and word[i] == "O":
            run += 1
            i += 1
        if run > int((even - used) * RUN_CAP_CONST):
            return False
    return True


def cyclic_ee(word: str) -> int:
    return sum(1 for i in range(len(word)) if word[i] == "E" and word[i - 1] == "E")


def ee_witness(length: int, *, floor: int = PUBLISHED_FLOOR) -> dict[str, Any] | None:
    """An admissible word carrying enough `EE` to void `length`, or `None`.

    `None` means either the length is robust (no `EE` count voids it) or no
    witness of this shape exists.
    """
    need = ee_to_resurrect(length, floor=floor)
    if need is None:
        return None
    odd = o_min(length)
    even = length - odd
    word = ee_witness_word(odd, even, need + 1)
    if len(word) != length or word.count("O") != odd:
        return None
    anchor = above_anchor_min(word)
    return {
        "L": length,
        "ee_needed": need,
        "ee_carried": cyclic_ee(word),
        "max_odd_run": max_odd_run(word),
        "above_anchor": anchor >= 0,
        "run_caps_hold": run_caps_hold(word, even),
        "shape_OO_dots_E": word[:2] == "OO" and word[-1] == "E",
        "o_is_o_min": True,
        "voids_exclusion": (
            anchor >= 0
            and run_caps_hold(word, even)
            and cyclic_ee(word) >= need
            and word[:2] == "OO"
            and word[-1] == "E"
        ),
    }


def witness_scan(*, floor: int = PUBLISHED_FLOOR) -> dict[str, Any]:
    """Every fragile length, against an admissible runs-at-most-two witness."""
    rows = [w for L in PACKING_DEATHS if (w := ee_witness(L, floor=floor)) is not None]
    return {
        "bound": "packing_ee_feasibility",
        "floor": floor,
        "fragile_examined": len(rows),
        "voided_by_admissible_word": sum(1 for r in rows if r["voids_exclusion"]),
        "max_run_over_witnesses": max((r["max_odd_run"] for r in rows), default=0),
        # The reopen condition of the dossier: does closure cap EE below threshold?
        "closure_caps_ee_below_threshold": all(
            not r["voids_exclusion"] for r in rows
        ),
        "rows": rows,
        "halt_theorem": False,
        "refutes_theorem_4_8": False,
    }

def write_packing_fragility_artifacts(
    payload: dict[str, Any] | None = None, *, floor: int = PUBLISHED_FLOOR
) -> dict[str, Any]:
    data = payload if payload is not None else fragility_scan(floor=floor)
    DATA_DIR.mkdir(parents=True, exist_ok=True)
    (DATA_DIR / "packing_fragility.json").write_text(
        json.dumps(data, indent=2) + "\n", encoding="utf-8"
    )
    return data


def main() -> None:
    data = write_packing_fragility_artifacts()
    print(f"floor {data['floor']}  n = {data['n']}  deaths {data['deaths_examined']}")
    print(
        "refinement budget (RHS3/RHS6): "
        f"{data['refinement_budget_min']:.4f} .. {data['refinement_budget_max']:.4f}"
    )
    print(
        f"fragile to EE: {data['deaths_fragile_to_ee']}   "
        f"robust to EE: {data['deaths_robust_to_ee']}"
    )
    print(
        "EE needed to resurrect a fragile one: "
        f"{data['ee_to_resurrect_min']} .. {data['ee_to_resurrect_max']}"
    )
    print(
        "fragile deaths inside the random-placement EE count: "
        f"{data['deaths_inside_random_ee']}/{data['deaths_fragile_to_ee']}"
    )


if __name__ == "__main__":
    main()
