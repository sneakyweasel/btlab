"""2-adic landing remainder. Not a termination theorem.

On an odd-to-odd step, y^3 = T(y)^2 + ρ with both odd, so
ρ ≡ y-1 (mod 8). That congruence is the valuation law. PE
history does not change it, and y ≡ 1 (mod 16) does not force
v2 ≥ 4.
"""

from __future__ import annotations

from collections import Counter, defaultdict
from typing import Any

from research.juggler_sequence.expansion_slack import walk_pe_run
from research.juggler_sequence.global_defect import local_defect
from research.juggler_sequence.lean_paths import has_named, juggler_text
from research.juggler_sequence.power_itineraries import floor_power
from research.juggler_sequence.progress_coverage import is_odd_odd
from research.juggler_sequence.two_block_residual import (
    odd_odd_starts,
    sequel_of,
)

N_MAX = 2000

LEAN_THEOREMS = (
    "landingRemainder",
    "oddOddLanding",
    "landingValuation",
    "odd_cube_mod_eight",
    "odd_cube_minus_odd_square_mod_eight",
    "odd_odd_remainder_mod_eight",
    "odd_odd_remainder_even",
    "landing_remainder_mod_eight_cases",
    "landing_valuation_classification",
    "landing_valuation_three_or_seven",
    "landing_valuation_five",
    "landing_valuation_one",
    "landing_valuation_33",
    "pe_endpoint_763_valuation",
)

PE_CHAIN = {
    "x": 365,
    "ys": (763, 1749, 4447),
    "v2": (1, 2, 1),
}

LIFT_COUNTEREXAMPLE = {
    "y": 33,
    "T": 189,
    "rho": 216,
    "v2": 3,
    "y_mod16": 1,
}


def v2(n: int) -> int:
    if n == 0:
        return -1
    return (n & -n).bit_length() - 1


def landing_remainder(y: int) -> int:
    return local_defect(y)


def landing_valuation(y: int) -> int:
    return v2(landing_remainder(y))


def expected_from_mod8(y: int) -> str:
    r = y % 8
    if r == 1:
        return "ge3_or_zero"
    if r == 5:
        return "eq2"
    if r in (3, 7):
        return "eq1"
    return "other"


def classification_holds(y: int, rho: int, val: int) -> bool:
    kind = expected_from_mod8(y)
    if kind == "eq1":
        return val == 1 and rho % 8 in (2, 6)
    if kind == "eq2":
        return val == 2 and rho % 8 == 4
    if kind == "ge3_or_zero":
        if rho == 0:
            return True
        return val >= 3 and rho % 8 == 0
    return False


def landing_row(y: int) -> dict[str, Any] | None:
    if y % 2 == 0 or y <= 0:
        return None
    z = floor_power(y)
    rho = y**3 - z * z
    return {
        "y": y,
        "T": z,
        "rho": rho,
        "v2": v2(rho),
        "y_mod8": y % 8,
        "y_mod16": y % 16,
        "T_mod2": z % 2,
        "rho_mod8": rho % 8,
        "odd_odd": z % 2 == 1,
        "rho_eq_y_minus_1_mod8": rho % 8 == (y - 1) % 8,
        "class_ok": (
            classification_holds(y, rho, v2(rho)) if z % 2 == 1 else None
        ),
    }


def valuation_census(*, n_max: int = N_MAX) -> dict[str, Any]:
    v2_hist: Counter[int] = Counter()
    v2_by_mod8: dict[int, Counter[int]] = defaultdict(Counter)
    next_parity_by_v2: dict[int, Counter[int]] = defaultdict(Counter)
    keys: set[tuple[int, int]] = set()
    class_fail = 0
    rho_mod_fail = 0
    odd_odd = 0
    exact_squares = 0
    lift16_v2_three = 0
    for y in range(1, n_max + 1, 2):
        if not is_odd_odd(y):
            continue
        row = landing_row(y)
        if row is None:
            continue
        odd_odd += 1
        v2_hist[row["v2"]] += 1
        v2_by_mod8[row["y_mod8"]][row["v2"]] += 1
        keys.add((row["v2"], row["y_mod8"]))
        if not row["rho_eq_y_minus_1_mod8"]:
            rho_mod_fail += 1
        if not row["class_ok"]:
            class_fail += 1
        if row["rho"] == 0:
            exact_squares += 1
        if row["y_mod16"] == 1 and row["v2"] == 3:
            lift16_v2_three += 1
        nxt = floor_power(row["T"])
        next_parity_by_v2[row["v2"]][nxt % 2] += 1
    return {
        "n_max": n_max,
        "odd_odd": odd_odd,
        "class_fail": class_fail,
        "rho_mod_fail": rho_mod_fail,
        "exact_squares": exact_squares,
        "v2_hist": dict(sorted(v2_hist.items())),
        "v2_by_mod8": {
            k: dict(sorted(v.items())) for k, v in sorted(v2_by_mod8.items())
        },
        "keys": sorted(keys),
        "next_parity_by_v2": {
            k: dict(v) for k, v in sorted(next_parity_by_v2.items())
        },
        "mixed_next_parity": sum(
            1 for counts in next_parity_by_v2.values() if len(counts) > 1
        ),
        "lift16_v2_three": lift16_v2_three,
    }


def pe_valuation_census(*, n_max: int = N_MAX) -> dict[str, Any]:
    starts = odd_odd_starts(n_max)
    seen: set[int] = set()
    v2_hist: Counter[int] = Counter()
    v2_by_mod8: dict[int, Counter[int]] = defaultdict(Counter)
    next_by_v2: dict[int, Counter[tuple[str, bool]]] = defaultdict(Counter)
    keys: set[tuple[int, int]] = set()
    classes: set[int] = set()
    sequences: list[list[int]] = []
    class_fail = 0
    endpoints = 0
    v2_one = 0
    for n in starts:
        if n in seen:
            continue
        run = walk_pe_run(n, cap=8)
        if not run:
            continue
        seq_v: list[int] = []
        for block in run:
            seen.add(block["x"])
            y = block["y"]
            if y.bit_length() > 80:
                continue
            row = landing_row(y)
            if row is None or not row["odd_odd"]:
                continue
            endpoints += 1
            v2_hist[row["v2"]] += 1
            v2_by_mod8[row["y_mod8"]][row["v2"]] += 1
            keys.add((row["v2"], row["y_mod8"]))
            classes.add(row["y_mod8"])
            if row["v2"] == 1:
                v2_one += 1
            if not row["class_ok"]:
                class_fail += 1
            seq = sequel_of(y)
            if seq is not None:
                key = (seq["word"], bool(seq["persistent"]))
                next_by_v2[row["v2"]][key] += 1
            seq_v.append(row["v2"])
        if len(seq_v) >= 2:
            sequences.append(seq_v)
    all_ones = sum(1 for seq in sequences if all(v == 1 for v in seq))
    nondec = sum(
        1
        for seq in sequences
        if all(seq[i] <= seq[i + 1] for i in range(len(seq) - 1))
    )
    return {
        "n_max": n_max,
        "endpoints": endpoints,
        "class_fail": class_fail,
        "v2_hist": dict(sorted(v2_hist.items())),
        "v2_by_mod8": {
            k: dict(sorted(v.items())) for k, v in sorted(v2_by_mod8.items())
        },
        "keys": sorted(keys),
        "mod8_classes": sorted(classes),
        "v2_one": v2_one,
        "runs_ge2": len(sequences),
        "all_v2_one_runs": all_ones,
        "nondecreasing_runs": nondec,
        "next_word_splits_v2": sum(
            1 for counts in next_by_v2.values() if len(counts) > 1
        ),
    }


def compare_populations(*, n_max: int = N_MAX) -> dict[str, Any]:
    generic = valuation_census(n_max=n_max)
    pe = pe_valuation_census(n_max=n_max)
    gkeys = set(map(tuple, generic["keys"]))
    pkeys = set(map(tuple, pe["keys"]))
    return {
        "generic": generic,
        "pe": pe,
        "pe_only_keys": sorted(pkeys - gkeys),
        "generic_only_keys": sorted(gkeys - pkeys),
    }


def lean_api_present() -> dict[str, bool]:
    text = juggler_text()
    return {
        "sorry_free": "sorry" not in text and "admit" not in text,
        **{name: has_named(text, name) for name in LEAN_THEOREMS},
    }
