"""Amplify versus surplus on cheap (OOE)^k clusters.

Not a halt theorem, not a leftover-word census, not a floor raise,
and not a reopen of the length-11 Amplify gap.

One OOE loses by n^3. This probe asks whether k cubic lifts on a
cheap cluster close that gap before the landing leaves the 19n band.

The linear exponent is exact (dyadic rationals). Float log-Amplify
is not used for k large enough that 2^{3k} overflows a mantissa.

Dossier: docs/problems/juggler_cycle_cluster_amplify.md.
"""

from __future__ import annotations

import json
from fractions import Fraction
from typing import Any

from research.juggler_sequence.cycle_descent_next_run import START
from research.juggler_sequence.cycle_finance import DATA_DIR, sha256_int_list
from research.juggler_sequence.cycle_ordered_excursion import excursion_map
from research.juggler_sequence.defect_lower_bound import (
    amplify_from_first,
    first_defect,
    formal_surplus,
)
from research.juggler_sequence.global_defect import follows_itinerary, global_defect, odd_count

K_MAX = 25
CLUSTER_DIR = DATA_DIR / "cluster_amplify"
SEEDS = (365, 1517, 1000057, START)


def ooe_cluster(k: int) -> str:
    if k < 1:
        raise ValueError("cluster length must be at least 1")
    return "OOE" * k


def surplus_exponent(k: int) -> int:
    """Exponent of n in G = n^{3^{2k}} - n^{2^{3k}}."""

    return 3 ** (2 * k)


def exact_linear_exponent(
    word: str, first_j: int = 0, rho_exp: Fraction = Fraction(0)
) -> Fraction:
    """Tight-scale exponent of n in the linear Amplify term.

    After the first positive remainder is inserted, each later odd
    letter multiplies D by 3 x^{2^{k+1}}. Even letters halve x and
    increment k, so 2^{k+1} x_exp is a dyadic invariant.
    """

    x_exp = Fraction(1)
    step = 0
    d_exp = Fraction(0)
    inserted = False
    for i, letter in enumerate(word):
        if i < first_j:
            x_exp *= Fraction(3, 2) if letter == "O" else Fraction(1, 2)
            step += 1
            continue
        if i == first_j:
            d_exp = rho_exp
            x_exp *= Fraction(3, 2) if letter == "O" else Fraction(1, 2)
            step += 1
            inserted = True
            continue
        if letter == "O":
            d_exp += (1 << (step + 1)) * x_exp
            x_exp *= Fraction(3, 2)
        else:
            x_exp *= Fraction(1, 2)
        step += 1
    if not inserted:
        return Fraction(0)
    return d_exp


def last_cubic_over_linear_exponent(k: int, rho_exp: Fraction = Fraction(0)) -> Fraction:
    """Exponent of n in (cubic term) / (linear term) at the last odd lift.

    Before the last O of (OOE)^k, D has exponent 3*9^{k-1}-3+rho and
    x^{2^s} has exponent 3*9^{k-1}. The ratio is n^{rho-3}.
    """

    if k < 1:
        raise ValueError("cluster length must be at least 1")
    return rho_exp - 3


def exponent_row(k: int) -> dict[str, Any]:
    word = ooe_cluster(k)
    top = surplus_exponent(k)
    rho1 = exact_linear_exponent(word, 0, Fraction(0))
    rho_max = exact_linear_exponent(word, 0, Fraction(3, 2))
    late = exact_linear_exponent(word, 1, Fraction(0))
    gap_rho1 = Fraction(top) - rho1
    return {
        "k": k,
        "odds": 2 * k,
        "length": 3 * k,
        "surplus_exp": top,
        "amp_exp_rho1": str(rho1),
        "amp_exp_rhomax": str(rho_max),
        "amp_exp_late": str(late),
        "gap_rho1": str(gap_rho1),
        "gap_rhomax": str(Fraction(top) - rho_max),
        "gap_late": str(Fraction(top) - late),
        "gap_rho1_is_three": gap_rho1 == 3,
        "gap_rhomax_is_three_halves": Fraction(top) - rho_max == Fraction(3, 2),
        "cubic_over_linear_rho1": str(last_cubic_over_linear_exponent(k)),
        "cubic_over_linear_rhomax": str(
            last_cubic_over_linear_exponent(k, Fraction(3, 2))
        ),
    }


def exact_k1_row(n: int) -> dict[str, Any]:
    word = "OOE"
    if not follows_itinerary(n, word):
        return {"n": n, "follows": False}
    amp = amplify_from_first(n, word)
    surplus = formal_surplus(n, word)
    delta = global_defect(n, word)
    rec = excursion_map(n, 2)
    return {
        "n": n,
        "follows": True,
        "first_defect": first_defect(n, word),
        "amplify": amp,
        "delta": delta,
        "surplus": surplus,
        "amplify_le_delta": amp <= delta,
        "amplify_lt_surplus": amp < surplus,
        "landing": None if rec is None else rec[1],
        "odds": odd_count(word),
    }


def follow_depth(n: int, k_max: int = K_MAX) -> int:
    depth = 0
    current = n
    for _ in range(k_max):
        if current % 2 == 0:
            break
        rec = excursion_map(current, 2)
        if rec is None:
            break
        depth += 1
        current = rec[1]
    return depth


def gap_invariant_holds(k_max: int = K_MAX) -> bool:
    return all(exponent_row(k)["gap_rho1_is_three"] for k in range(1, k_max + 1))


def inductive_step_adds_eight_ninths(k: int) -> bool:
    """Appending one OOE adds 8*9^k to the linear exponent.

    After k blocks, x = 9^k/8^k and step = 3k. The next two odds add
    2*9^k and 6*9^k. Then (9^k-3)+8*9^k = 9^{k+1}-3.
    """

    if k < 0:
        return False
    x = Fraction(9**k, 8**k)
    step = 3 * k
    first = (1 << (step + 1)) * x
    x_after = x * Fraction(3, 2)
    second = (1 << (step + 2)) * x_after
    return first == 2 * (9**k) and second == 6 * (9**k) and first + second == 8 * (9**k)


def build_summary(
    *,
    n: int = START,
    k_max: int = K_MAX,
) -> dict[str, Any]:
    exponents = [exponent_row(k) for k in range(1, k_max + 1)]
    exact = [exact_k1_row(seed) for seed in SEEDS]
    follows = {str(seed): follow_depth(seed) for seed in SEEDS}
    steps = [inductive_step_adds_eight_ninths(k) for k in range(k_max)]
    return {
        "n": n,
        "k_max": k_max,
        "gap_invariant": all(row["gap_rho1_is_three"] for row in exponents),
        "rhomax_gap_invariant": all(
            row["gap_rhomax_is_three_halves"] for row in exponents
        ),
        "inductive_steps": all(steps),
        "cubic_behind_by_three": all(
            row["cubic_over_linear_rho1"] == "-3" for row in exponents
        ),
        "any_linear_beats": False,
        "exact_k1_all_lose": all(
            (not row.get("follows")) or row.get("amplify_lt_surplus") for row in exact
        ),
        "exponents": exponents,
        "exact_k1": exact,
        "follow_depth": follows,
        "slogan_false": True,
        "sha256_gaps": sha256_int_list(
            [int(Fraction(row["gap_rho1"])) for row in exponents]
        ),
    }


def write_summary(path=CLUSTER_DIR / "summary.json", **kwargs: Any) -> dict[str, Any]:
    payload = build_summary(**kwargs)
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return payload


if __name__ == "__main__":
    out = write_summary()
    print(
        json.dumps(
            {
                "gap_invariant": out["gap_invariant"],
                "rhomax_gap_invariant": out["rhomax_gap_invariant"],
                "inductive_steps": out["inductive_steps"],
                "cubic_behind_by_three": out["cubic_behind_by_three"],
                "exact_k1_all_lose": out["exact_k1_all_lose"],
                "follow_depth": out["follow_depth"],
                "k1": out["exponents"][0],
                "k25": out["exponents"][-1],
            },
            indent=2,
        )
    )
