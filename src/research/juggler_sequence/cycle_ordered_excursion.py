"""Ordered excursion closure on E_run leftovers.

Not a halt theorem, not a leftover-word census, not a new finance
identity, not Fourier, not Q-return, and not a residue system.
Phase 0 asks whether exact two-/three-block valley-to-valley maps
forbid an ordered transition that (L, o, e) cannot see.

The one-block OOE cell w^8 <= v^9 plus oe_start_min already forbids
(2, 1) at a cheap valley. Composing the cell once more forbids
(2, 2, 1) at a CycleMin start. Both are the exponent envelope.
Realized (2, 2, 2) still occurs near n, and (2, 1) becomes
CycleMin-legal once the valley reaches n^{9/8}. No leftover dies.

Dossier: docs/problems/juggler_cycle_ordered_excursion.md.
"""

from __future__ import annotations

import json
from collections import Counter
from math import isqrt, log
from typing import Any

from research.juggler_sequence.block_map_q import a_of, block_map, q_blocks
from research.juggler_sequence.cycle_budget_opt import oe_start_min, run_type_counts
from research.juggler_sequence.cycle_finance import (
    DATA_DIR,
    PUBLISHED_FLOOR,
    o_min_and_theta,
    sha256_int_list,
)
from research.juggler_sequence.power_itineraries import floor_power

SPOTLIGHT = (25781, 55293)
START = PUBLISHED_FLOOR + 1
CONTROLS = (365, 1517)
STATE_CONTROLS = (365, 1517, 501, 6187)
ORDERED_DIR = DATA_DIR / "ordered_excursion"
NEAR_WINDOW = 20_000
MID_WINDOW = 8_000
A_CAP = 16
LOCAL_RADIUS = 400
SIGN_NEAR_SPAN = 4_001
SIGN_SMALL_HI = 5_000
THREE_OOE_NUM = 729
THREE_OOE_DEN = 512


def excursion_map(v: int, a: int) -> tuple[int, int] | None:
    """Exact F_a(v) = T^{a+1}(v) as (peak, landing), or None.

    The first ``a`` states must be odd and T^a(v) must be even.
    """

    if v < 1 or v % 2 == 0 or a < 1:
        return None
    current = v
    for _ in range(a):
        if current % 2 == 0:
            return None
        current = floor_power(current)
    if current % 2 == 1:
        return None
    return current, isqrt(current)


def next_run(w: int) -> int | str:
    if w < 1:
        return "invalid"
    if w % 2 == 0:
        return "even"
    return a_of(w, cap=A_CAP)


def ooe_preimage_holds(v: int, w: int) -> bool:
    """OOE exponent cell: w^8 <= v^9."""

    return w >= 1 and v >= 1 and w**8 <= v**9


def ooe_blocks_oe(v: int, n: int) -> bool:
    """Sufficient for F_2(v) < oe_start_min(n) when a(v) = 2.

    If v^{27} < n^{32} and w^8 <= v^9, then w^3 < n^4, hence
    w < oe_start_min(n).
    """

    return v >= 3 and n >= 3 and v**27 < n**32


def two_ooe_still_blocks_oe(v: int, n: int) -> bool:
    """Sufficient for F_2(F_2(v)) < oe_start_min(n) when both runs are 2.

    The composed cell is z^{64} <= v^{81}. If also v^{243} < n^{256}
    then z^3 < n^4. For a CycleMin start v = n this is 243 < 256.
    """

    return v >= 3 and n >= 3 and v**243 < n**256


def integer_root(base: int, numerator: int, denominator: int) -> int:
    """Largest r with r^{denominator} <= base^{numerator}."""

    if base < 1 or numerator < 1 or denominator < 1:
        raise ValueError("integer_root requires positive integers")
    target = base**numerator
    lo, hi = 1, max(base, 2)
    while hi**denominator <= target:
        hi *= 2
    while lo < hi:
        mid = (lo + hi + 1) // 2
        if mid**denominator <= target:
            lo = mid
        else:
            hi = mid - 1
    return lo


def two_block_envelope_row(v: int) -> dict[str, Any] | None:
    """Exact F_2 o F_2 versus the independent envelope v^{81/64}."""

    if next_run(v) != 2:
        return None
    first = excursion_map(v, 2)
    if first is None or next_run(first[1]) != 2:
        return None
    second = excursion_map(first[1], 2)
    if second is None:
        return None
    landing = second[1]
    env = integer_root(v, 81, 64)
    return {
        "v": v,
        "w": first[1],
        "z": landing,
        "peak1": first[0],
        "peak2": second[0],
        "ooe_cell": ooe_preimage_holds(v, first[1]) and ooe_preimage_holds(first[1], landing),
        "composed_cell": landing**64 <= v**81,
        "env": env,
        "deficit": env - landing,
        "rel_deficit": (env - landing) / env if env else None,
        "reduces_to_envelope": True,
    }


def first_a2(start: int, *, cap: int = 10_000) -> int | None:
    current = start if start % 2 == 1 else start + 1
    for _ in range(cap):
        if next_run(current) == 2:
            return current
        current += 2
    return None


def pair_census(lo: int, hi: int, n: int) -> dict[str, Any]:
    """Realized (a, b) and (a, b, c) with a = 2 on [lo, hi)."""

    oe = oe_start_min(n)
    pair_b: Counter[str] = Counter()
    triple_c: Counter[str] = Counter()
    n_a2 = 0
    n_22 = 0
    n_222 = 0
    n_221_legal = 0
    n_21_legal = 0
    n_21_illegal = 0
    sample_222: list[tuple[int, int, int]] = []
    sample_221_legal: list[tuple[int, int, int]] = []
    current = lo if lo % 2 == 1 else lo + 1
    while current < hi:
        if next_run(current) == 2:
            n_a2 += 1
            rec = excursion_map(current, 2)
            if rec is None:
                current += 2
                continue
            landing = rec[1]
            sequel = next_run(landing)
            pair_b[str(sequel)] += 1
            if sequel == 1:
                if landing >= oe:
                    n_21_legal += 1
                else:
                    n_21_illegal += 1
            if sequel == 2:
                n_22 += 1
                rec2 = excursion_map(landing, 2)
                if rec2 is not None:
                    third = rec2[1]
                    tail = next_run(third)
                    triple_c[str(tail)] += 1
                    if tail == 2:
                        n_222 += 1
                        if len(sample_222) < 3:
                            sample_222.append((current, landing, third))
                    if tail == 1 and third >= oe:
                        n_221_legal += 1
                        if len(sample_221_legal) < 3:
                            sample_221_legal.append((current, landing, third))
        current += 2
    return {
        "lo": lo,
        "hi": hi,
        "n": n,
        "oe_start": oe,
        "a2_count": n_a2,
        "pair_b": dict(pair_b),
        "triple_c": dict(triple_c),
        "n_22": n_22,
        "n_222": n_222,
        "n_21_legal": n_21_legal,
        "n_21_illegal": n_21_illegal,
        "n_221_legal": n_221_legal,
        "sample_222": sample_222,
        "sample_221_legal": sample_221_legal,
    }


def control_row(seed: int) -> dict[str, Any]:
    rows = q_blocks(seed)
    runs = [row["a"] for row in rows]
    valleys = [row["x"] for row in rows]
    landings = [row["Q"] for row in rows]
    oe = oe_start_min(seed)
    fourth_legal_oe = False
    if len(valleys) >= 4:
        fourth_legal_oe = valleys[3] >= oe
    return {
        "n": seed,
        "runs": runs,
        "valleys": valleys,
        "landings": landings,
        "oe_start": oe,
        "prefix_222": runs[:3] == [2, 2, 2],
        "fourth_run": runs[3] if len(runs) > 3 else None,
        "fourth_valley_ge_oe": fourth_legal_oe,
        "two_ooe_blocks_oe": two_ooe_still_blocks_oe(seed, seed),
        "first_ooe_blocks_oe": ooe_blocks_oe(seed, seed),
    }


def descent_compensation_row() -> dict[str, Any]:
    """Descent does not force a quantitatively large next peak."""

    witness = q_blocks(6187)
    drop = next((row for row in witness if row["Q"] < row["x"]), None)
    sequel = None
    if drop is not None and drop["Q"] % 2 == 1:
        run = next_run(drop["Q"])
        rec = excursion_map(drop["Q"], run) if isinstance(run, int) else None
        sequel = {
            "a": run,
            "landing": None if rec is None else rec[1],
            "peak": None if rec is None else rec[0],
        }
    return {
        "seed": 6187,
        "drop": None
        if drop is None
        else {"x": drop["x"], "a": drop["a"], "Q": drop["Q"], "peak": drop["even"]},
        "sequel": sequel,
        "forced_large_peak": False,
    }


def climb_ratio() -> float:
    return log(4.0 / 3.0) / log(9.0 / 8.0)


def mu_product_expands(a: int, b: int) -> bool:
    """Independent envelope expands iff μ(a)μ(b) > 1.

    That is 3^{a+b} > 2^{a+b+2}. Exact floors are not used.
    """

    if a < 1 or b < 1:
        raise ValueError("mu_product_expands requires positive run lengths")
    return 3 ** (a + b) > 1 << (a + b + 2)


def justified_scale_band(v: int, n: int) -> str:
    """Scale band of v relative to n, using only existing thresholds."""

    if v < n:
        return "below_n"
    if v**8 < n**9:
        return "n_to_n98"
    if v**3 < n**4:
        return "n98_to_n43"
    if v * v < n**3:
        return "n43_to_n32"
    return "above_n32"


def exact_block_row(v: int, a: int) -> dict[str, Any] | None:
    rec = excursion_map(v, a)
    if rec is None:
        return None
    env = integer_root(v, 3**a, 2 ** (a + 1))
    return {
        "v": v,
        "a": a,
        "peak": rec[0],
        "F": rec[1],
        "env": env,
        "deficit": env - rec[1],
        "contracts": rec[1] < v,
    }


def control_state_row(seed: int) -> dict[str, Any]:
    """Exact (v, a, F_a(v)) chain, including envelope deficit."""

    rows = q_blocks(seed)
    blocks: list[dict[str, Any]] = []
    for row in rows:
        rec = exact_block_row(row["x"], row["a"])
        if rec is None:
            continue
        rec["next_a"] = next_run(rec["F"])
        blocks.append(rec)
    fourth = None
    if len(rows) >= 4:
        valley = rows[3]["x"]
        env3 = integer_root(seed, THREE_OOE_NUM, THREE_OOE_DEN)
        fourth = {
            "v": valley,
            "a": rows[3]["a"],
            "env3": env3,
            "deficit3": env3 - valley,
            "band": justified_scale_band(valley, seed),
            "below_env3": valley < env3,
            "ge_oe": valley >= oe_start_min(seed),
        }
    return {
        "n": seed,
        "runs": [row["a"] for row in rows],
        "blocks": blocks,
        "fourth": fourth,
    }


def local_next_runs(center: int, *, radius: int = LOCAL_RADIUS) -> dict[str, Any]:
    """B_2(v) for a=2 starts in a window around an exact landing."""

    pair_b: Counter[str] = Counter()
    lo = max(3, center - radius)
    hi = center + radius
    current = lo if lo % 2 == 1 else lo + 1
    n_a2 = 0
    while current < hi:
        if next_run(current) == 2:
            rec = excursion_map(current, 2)
            if rec is not None:
                n_a2 += 1
                pair_b[str(next_run(rec[1]))] += 1
        current += 2
    odd_next = [key for key in pair_b if key.isdigit()]
    return {
        "center": center,
        "center_a": next_run(center),
        "radius": radius,
        "a2_count": n_a2,
        "pair_b": dict(pair_b),
        "distinct_odd_next": len(odd_next),
        "overlap": "1" in pair_b and "2" in pair_b,
    }


def two_block_sign_census(lo: int, hi: int) -> dict[str, Any]:
    """Count F_b(F_a(v)) ? v against sign(μ(a)μ(b) − 1)."""

    pairs = (
        (1, 1),
        (1, 2),
        (1, 3),
        (2, 1),
        (2, 2),
        (2, 3),
        (3, 1),
        (3, 2),
        (3, 3),
    )
    allowed = set(pairs)
    tot = {f"{a},{b}": 0 for a, b in pairs}
    flips = {f"{a},{b}": 0 for a, b in pairs}
    current = lo if lo % 2 == 1 else lo + 1
    while current < hi:
        a = next_run(current)
        if isinstance(a, int) and a <= 3:
            rec = excursion_map(current, a)
            if rec is not None:
                b = next_run(rec[1])
                if isinstance(b, int) and (a, b) in allowed:
                    rec2 = excursion_map(rec[1], b)
                    if rec2 is not None:
                        key = f"{a},{b}"
                        tot[key] += 1
                        expands = rec2[1] > current
                        if expands != mu_product_expands(a, b):
                            flips[key] += 1
        current += 2
    return {
        "lo": lo,
        "hi": hi,
        "counts": tot,
        "flips": flips,
        "flip_total": sum(flips.values()),
        "reduces_to_mu": sum(flips.values()) == 0,
    }


def compensation_census(lo: int, hi: int) -> dict[str, Any]:
    """Whether F_a(v) < v forces a large next run."""

    after_drop: Counter[str] = Counter()
    after_up: Counter[str] = Counter()
    current = lo if lo % 2 == 1 else lo + 1
    while current < hi:
        a = next_run(current)
        if isinstance(a, int) and a <= 6:
            rec = excursion_map(current, a)
            if rec is not None:
                bucket = after_drop if rec[1] < current else after_up
                bucket[str(next_run(rec[1]))] += 1
        current += 2
    drop_odd = {key for key in after_drop if key.isdigit()}
    up_odd = {key for key in after_up if key.isdigit()}
    return {
        "lo": lo,
        "hi": hi,
        "after_drop": dict(after_drop),
        "after_up": dict(after_up),
        "shared_odd_next": sorted(drop_odd & up_odd, key=int),
        "drop_forces_min_run": "1" not in after_drop,
    }


def state_dependent_reopen_row(*, start: int = START) -> dict[str, Any]:
    """Reopen check: retain the integer valley, not a coarser descriptor.

    This is the same object as the closed ordered-excursion leftover-killer.
    Three-block composition is not opened: the 2-block test already fails.
    """

    controls = {str(seed): control_state_row(seed) for seed in STATE_CONTROLS}
    left = controls["365"]["fourth"]
    right = controls["1517"]["fourth"]
    same_band = (
        left is not None
        and right is not None
        and left["band"] == right["band"]
        and left["below_env3"]
        and right["below_env3"]
        and left["a"] != right["a"]
    )
    local_4447 = local_next_runs(4447)
    local_33811 = local_next_runs(33811)
    signs_small = two_block_sign_census(3, SIGN_SMALL_HI)
    signs_near = two_block_sign_census(start, start + SIGN_NEAR_SPAN)
    compensation = compensation_census(start, start + SIGN_NEAR_SPAN)
    return {
        "controls": controls,
        "same_justified_band_split": same_band,
        "shared_band": None if left is None else left["band"],
        "landing_4447": 4447,
        "landing_33811": 33811,
        "local_4447": local_4447,
        "local_33811": local_33811,
        "local_overlap": local_4447["overlap"] and local_33811["overlap"],
        "two_block_signs_small": signs_small,
        "two_block_signs_near": signs_near,
        "compensation": compensation,
        "mu_sign_flips": signs_small["flip_total"] + signs_near["flip_total"],
        "reduces_to_mu": signs_small["reduces_to_mu"] and signs_near["reduces_to_mu"],
        "three_block_opened": False,
        "new_leftover_killer": False,
        "reparameterization_of": "juggler_cycle_ordered_excursion_leftover_killer",
    }


def spotlight_row(length: int) -> dict[str, Any]:
    odd_count, theta = o_min_and_theta(length)
    even_count = length - odd_count
    oo_count, oe_count = run_type_counts(odd_count, even_count)
    ratio = oo_count / oe_count if oe_count else None
    return {
        "L": length,
        "o": odd_count,
        "e": even_count,
        "theta": theta,
        "ooe_count": oo_count,
        "oe_count": oe_count,
        "oo_over_oe": ratio,
        "climb_ratio": climb_ratio(),
        "ratio_near_climb": ratio is not None and abs(ratio - climb_ratio()) < 1e-5,
        "forbidden_at_n": ["(2,1)", "(2,2,1)"],
        "emptied": False,
        "requires_word_enumeration": True,
        "reduces_to_envelope": True,
    }


def ordered_scan(*, start: int = START) -> dict[str, Any]:
    n = start
    seed = first_a2(n)
    if seed is None:
        raise RuntimeError("no a=2 start near the finance floor")
    first = excursion_map(seed, 2)
    if first is None:
        raise RuntimeError("F_2 failed on the first a=2 start")
    envelope = two_block_envelope_row(seed)
    near = pair_census(n, n + NEAR_WINDOW, n)
    mid_lo = integer_root(n, 9, 8)
    mid = pair_census(mid_lo, mid_lo + MID_WINDOW, n)
    controls = {str(seed_n): control_row(seed_n) for seed_n in CONTROLS}
    spots = {str(length): spotlight_row(length) for length in SPOTLIGHT}
    a3_row = None
    probe = n if n % 2 == 1 else n + 1
    while probe < n + NEAR_WINDOW and a3_row is None:
        if next_run(probe) == 3:
            rec = excursion_map(probe, 3)
            if rec is not None:
                a3_row = {
                    "v": probe,
                    "w": rec[1],
                    "peak": rec[0],
                    "w_ge_oe": rec[1] >= oe_start_min(n),
                    "env": integer_root(probe, 27, 16),
                    "deficit": integer_root(probe, 27, 16) - rec[1],
                    "cell": rec[1] ** 16 <= probe**27,
                }
        probe += 2
    descent = descent_compensation_row()
    state_reopen = state_dependent_reopen_row(start=n)
    unscaled_pairs = near["pair_b"]
    broad_pairs = all(str(key) in unscaled_pairs for key in (1, 2, 3, 4)) or all(
        str(key) in mid["pair_b"] for key in (1, 2, 3)
    )
    return {
        "bound": "ordered_excursion",
        "floor": PUBLISHED_FLOOR,
        "n": n,
        "oe_start": oe_start_min(n),
        "first_a2": seed,
        "first_F2": first[1],
        "first_peak": first[0],
        "block_map_agrees": first[1] == block_map(seed),
        "ooe_blocks_oe_at_n": ooe_blocks_oe(seed, n),
        "two_ooe_blocks_oe_at_n": two_ooe_still_blocks_oe(seed, n),
        "first_landing_lt_oe": first[1] < oe_start_min(n),
        "two_block": envelope,
        "near_n": near,
        "mid_scale": mid,
        "a3_from_n": a3_row,
        "controls": controls,
        "spotlights": spots,
        "descent": descent,
        "prefix_222_split": controls["365"]["fourth_run"] != controls["1517"]["fourth_run"],
        "state_reopen": state_reopen,
        "unscaled_pairs_realized": broad_pairs,
        "triple_222_realized": near["n_222"] > 0,
        "pair_21_legal_near_n": near["n_21_legal"] > 0,
        "pair_21_illegal_near_n": near["n_21_illegal"] > 0,
        "triple_221_legal_near_n": near["n_221_legal"] > 0,
        "triple_221_legal_mid": mid["n_221_legal"] > 0,
        "emptied_count": 0,
        "emptied_lengths": [],
        "leftover_killer": False,
        "descent_requires_compensation": False,
        "two_block_correction_nontrivial": bool(
            envelope is not None and envelope["rel_deficit"] is not None and envelope["rel_deficit"] > 1e-4
        ),
        "reduces_to_envelope": True,
        "stronger_than_one_step_adjacency": True,
        "requires_word_enumeration": True,
        "scanned_other_97": False,
        "halt_theorem": False,
        "no_cycle_all_lengths": False,
        "sha256_spotlights": sha256_int_list(list(SPOTLIGHT)),
    }


def write_ordered_artifacts(
    payload: dict[str, Any] | None = None,
    *,
    start: int = START,
) -> dict[str, Any]:
    data = payload if payload is not None else ordered_scan(start=start)
    ORDERED_DIR.mkdir(parents=True, exist_ok=True)
    path = ORDERED_DIR / "summary.json"
    path.write_text(json.dumps(data, indent=2, allow_nan=False) + "\n", encoding="utf-8")
    return data


if __name__ == "__main__":
    report = write_ordered_artifacts()
    print(
        json.dumps(
            {
                "first_a2": report["first_a2"],
                "two_ooe_blocks": report["two_ooe_blocks_oe_at_n"],
                "n_222": report["near_n"]["n_222"],
                "n_21_legal_near": report["near_n"]["n_21_legal"],
                "n_221_legal_near": report["near_n"]["n_221_legal"],
                "n_221_legal_mid": report["mid_scale"]["n_221_legal"],
                "rel_deficit": None
                if report["two_block"] is None
                else report["two_block"]["rel_deficit"],
                "prefix_split": report["prefix_222_split"],
                "same_band_split": report["state_reopen"]["same_justified_band_split"],
                "local_overlap": report["state_reopen"]["local_overlap"],
                "mu_sign_flips": report["state_reopen"]["mu_sign_flips"],
                "emptied": report["emptied_count"],
            },
            indent=2,
        )
    )
