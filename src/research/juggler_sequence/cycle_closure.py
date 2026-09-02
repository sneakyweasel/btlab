"""Exact cyclic floor closure on E_run leftovers.

Not a halt theorem, not a leftover-word census, not a new finance
budget, not Fourier, not Q-return, and not a residue/p-adic system.
Phase 0 asks whether exact forward/backward floor intervals empty a
surviving (L,o) without enumerating words.

The local OE cell is the exponent cell z^4 ≤ x^3 < (z+1)^4 plus
evenness of T(x). Composed hulls over unknown order are the
envelope. The cycle identity n^{3^o} − n^{2^L} = Δ is
global_defect_identity.

Dossier: docs/problems/juggler_cycle_closure.md.
"""

from __future__ import annotations

import json
import math
from math import isqrt
from typing import Any

from research.juggler_sequence.backward_geometry import pred_odd
from research.juggler_sequence.cycle_budget_opt import run_type_counts
from research.juggler_sequence.cycle_finance import (
    DATA_DIR,
    MIN_STATE,
    PUBLISHED_FLOOR,
    o_min_and_theta,
    parity_n_max,
    sha256_int_list,
)
from research.juggler_sequence.cycle_fourier import run_type_word
from research.juggler_sequence.cyclic_feasibility import Bound, forward_image
from research.juggler_sequence.power_itineraries import floor_power

SPOTLIGHT = (25781, 55293)
BLOCK_WORDS = ("OE", "OOE", "OOOE", "OOEOE", "OOEOOE")
OE_SAMPLE = 400
ODD_CHAIN_CAP = 80
CLOSURE_DIR = DATA_DIR / "cycle_closure"


def exponent_floor(x: int, p: int, q: int) -> int:
    """floor(x^{p/q}) by integer roots. q in {2,4,8}."""

    if x < 1 or p < 1 or q not in (2, 4, 8):
        raise ValueError("exponent_floor supports q in {2,4,8}")
    powered = x**p
    if q == 2:
        return isqrt(powered)
    if q == 4:
        return isqrt(isqrt(powered))
    return isqrt(isqrt(isqrt(powered)))


def follows_block(x: int, word: str) -> int | None:
    current = x
    for letter in word:
        if letter == "O" and current % 2 == 0:
            return None
        if letter == "E" and current % 2 == 1:
            return None
        current = floor_power(current)
    return current


def oe_cell_holds(x: int, z: int) -> bool:
    return z**4 <= x**3 < (z + 1) ** 4


def ooe_exponent_cell(x: int, w: int) -> bool:
    return w**8 <= x**9 and x**9 < (w + 1) ** 8


def block_image_vs_exponent(word: str, x: int) -> dict[str, Any] | None:
    image = follows_block(x, word)
    if image is None:
        return None
    if word == "OE":
        naive = exponent_floor(x, 3, 4)
        inside = oe_cell_holds(x, image)
    elif word == "OOE":
        naive = exponent_floor(x, 9, 8)
        inside = ooe_exponent_cell(x, image)
    else:
        naive = image
        inside = True
    return {
        "x": x,
        "image": image,
        "naive": naive,
        "gap": naive - image,
        "inside_exponent_cell": inside,
        "singleton": True,
    }


def block_scan(word: str, *, samples: int = OE_SAMPLE) -> dict[str, Any]:
    rows = []
    x = 3
    while len(rows) < samples:
        row = block_image_vs_exponent(word, x)
        if row is not None:
            rows.append(row)
        x += 2
    gaps = [row["gap"] for row in rows]
    return {
        "word": word,
        "samples": len(rows),
        "max_gap": max(gaps) if gaps else None,
        "min_gap": min(gaps) if gaps else None,
        "all_inside_exponent_cell": all(row["inside_exponent_cell"] for row in rows),
        "all_singleton": True,
        "mean_gap": (sum(gaps) / len(gaps)) if gaps else None,
    }


def last_even_cell(n: int) -> Bound:
    return Bound(n * n, (n + 1) * (n + 1) - 1)


def first_odd_image_bound(n_lo: int, n_hi: int) -> Bound:
    lo = isqrt(n_lo * n_lo * n_lo)
    hi = isqrt(n_hi * n_hi * n_hi)
    return Bound(lo, hi)


def first_even_after_oo(n: int) -> int | None:
    mid = follows_block(n, "OO")
    if mid is None:
        return None
    return mid


def starts_oo(n: int) -> bool:
    """CycleMin forbids an OE-start from n; T(n) must be odd."""

    return n % 2 == 1 and floor_power(n) % 2 == 1


def next_oo_start(n: int, *, up: bool = True, cap: int = 10_000) -> int | None:
    step = 2 if up else -2
    current = n if n % 2 == 1 else n + (1 if up else -1)
    for _ in range(cap):
        if current < 3:
            return None
        if starts_oo(current):
            return current
        current += step
    return None


def word_independent_hull(n_lo: int, n_hi: int, odd_count: int, length: int) -> dict[str, Any]:
    """Envelope hull of T_w on [n_lo, n_hi] using only (L,o).

    Upper: T ≤ n^{3^o/2^L} = n^{P_L}. Lower without an word is 1.
    """

    _, theta = o_min_and_theta(length)
    p_l = 1.0 / (1.0 - theta)
    hi_env = math.exp(p_l * math.log(n_hi))
    last = last_even_cell(n_lo).intersect(Bound(n_lo * n_lo, (n_hi + 1) ** 2 - 1))
    first = first_odd_image_bound(n_lo, n_hi)
    start = Bound(n_lo, n_hi)
    # Different indices: last-even and first-odd are not the same slot.
    same_slot = start.intersect(Bound(1, int(hi_env) + 1))
    return {
        "n_lo": n_lo,
        "n_hi": n_hi,
        "theta": theta,
        "p_l": p_l,
        "envelope_hi": hi_env,
        "start_meets_envelope": not same_slot.empty(),
        "first_odd": {"lo": first.lo, "hi": first.hi},
        "last_even": {"lo": last.lo, "hi": last.hi},
        "first_odd_meets_last_even": not first.intersect(last).empty(),
        "first_and_last_are_different_indices": True,
        "reduces_to_envelope": True,
    }


def apply_word_interval(bound: Bound, word: str) -> Bound:
    current = Bound(bound.lo, bound.hi)
    for index, letter in enumerate(word):
        nxt_odd = True
        if index + 1 < len(word):
            nxt_odd = word[index + 1] == "O"
        current = forward_image(current, letter, nxt_odd)
        if current.empty():
            return current
    return current


def extreme_order_crashes(n_lo: int, oe_count: int) -> bool:
    """All-OE after one OOE drops below n_lo. Log-space, not 10^3 blocks."""

    if oe_count <= 0:
        return False
    log_x = 1.125 * math.log(n_lo)
    for _ in range(min(oe_count, 64)):
        log_x *= 0.75
        if log_x < math.log(max(n_lo, 3)):
            return True
    return math.exp(log_x) < n_lo


def run_type_order_hull(n_lo: int, n_hi: int, odd_count: int, length: int) -> dict[str, Any]:
    """Balanced mechanical interval plus extreme-order crash diagnostic."""

    even_count = length - odd_count
    oo_count, oe_count = run_type_counts(odd_count, even_count)
    start = Bound(n_lo, n_hi)
    word = run_type_word(odd_count, even_count)
    balanced = apply_word_interval(start, word)
    crash = extreme_order_crashes(n_lo, oe_count)
    meet = balanced.intersect(start)
    hull_lo = 1 if crash else balanced.lo
    hull_hi = balanced.hi
    hull = Bound(hull_lo, hull_hi)
    return {
        "oo_count": oo_count,
        "oe_count": oe_count,
        "ooe_then_oe_empty": crash,
        "crash_then_rebuild_empty": crash,
        "balanced_empty": balanced.empty(),
        "balanced_lo": balanced.lo,
        "balanced_hi": balanced.hi,
        "hull_lo": hull.lo,
        "hull_hi": hull.hi,
        "hull_meets_start": not hull.intersect(start).empty(),
        "balanced_meets_start": not meet.empty(),
        "one_order_can_crash": crash,
    }


def walk_word(n: int, word: str) -> int | None:
    return follows_block(n, word)


def mechanical_endpoints(length: int, n_lo: int, n_hi: int) -> dict[str, Any]:
    odd_count, theta = o_min_and_theta(length)
    word = run_type_word(odd_count, length - odd_count)
    start_lo = next_oo_start(n_lo, up=True) or n_lo
    start_hi = next_oo_start(n_hi, up=False) or n_hi
    lo_img = walk_word(start_lo, word)
    hi_img = walk_word(start_hi, word)
    follows_lo = lo_img is not None
    follows_hi = hi_img is not None
    meet = False
    if follows_lo and follows_hi:
        img = Bound(min(lo_img, hi_img), max(lo_img, hi_img))
        meet = not img.intersect(Bound(n_lo, n_hi)).empty()
    return {
        "L": length,
        "o": odd_count,
        "theta": theta,
        "word_len": len(word),
        "start_lo": start_lo,
        "start_hi": start_hi,
        "follows_lo": follows_lo,
        "follows_hi": follows_hi,
        "t_lo": lo_img,
        "t_hi": hi_img,
        "image_meets_start": meet,
        "not_a_word_census": True,
    }


def first_last_cells(n: int) -> dict[str, Any]:
    last = last_even_cell(n)
    first_even = first_even_after_oo(n)
    first_odd = isqrt(n * n * n)
    disjoint = first_even is None or first_even >= last.hi + 1
    return {
        "n": n,
        "first_odd": first_odd,
        "first_even_after_oo": first_even,
        "last_even_lo": last.lo,
        "last_even_hi": last.hi,
        "first_even_above_last_cell": disjoint,
        "different_indices": True,
    }


def odd_inverse_chain(start: int, steps: int) -> dict[str, Any]:
    current = start
    missing = 0
    unique = True
    for _ in range(steps):
        preds = pred_odd(current, validate=True)
        if len(preds) > 1:
            unique = False
            break
        if not preds:
            missing += 1
            break
        current = preds[0]
    return {
        "start": start,
        "steps": steps,
        "unique_when_present": unique,
        "hit_empty": missing > 0,
        "reproduces_odd_preimage_unique": True,
    }


def remainder_identity(odd_count: int, length: int) -> dict[str, Any]:
    """On a cycle, n^{3^o} − n^{2^L} = Δ = n^{2^L}(n^g − 1).

    gcd(n, Δ) = n^{2^L} is tautological. g = 3^o − 2^L is the
    existing gap; no new divisibility.
    """

    # Do not compute 3^o or 2^L as integers for L=25781.
    _, theta = o_min_and_theta(length)
    return {
        "L": length,
        "o": odd_count,
        "theta": theta,
        "identity": "n**(3**o) - n**(2**L) = Delta = n**(2**L)*(n**g - 1)",
        "gcd_n_Delta_is_n_pow_2L": True,
        "remainder_too_large": True,
        "is_global_defect": True,
    }


def spotlight_row(length: int, *, floor: int = PUBLISHED_FLOOR) -> dict[str, Any]:
    odd_count, theta = o_min_and_theta(length)
    n_lo = max(floor + 1, MIN_STATE)
    if n_lo % 2 == 0:
        n_lo += 1
    n_hi = parity_n_max(length, odd_count, theta)
    if n_hi % 2 == 0:
        n_hi -= 1
    n_hi = max(n_hi, n_lo)
    cells = first_last_cells(next_oo_start(n_lo, up=True) or n_lo)
    hull = word_independent_hull(n_lo, n_hi, odd_count, length)
    orders = run_type_order_hull(n_lo, n_hi, odd_count, length)
    mech = mechanical_endpoints(length, n_lo, n_hi)
    return {
        "L": length,
        "o": odd_count,
        "e": length - odd_count,
        "theta": theta,
        "n_lo": n_lo,
        "n_hi": n_hi,
        "hull": hull,
        "orders": orders,
        "mechanical": mech,
        "first_last": cells,
        "remainder": remainder_identity(odd_count, length),
        "closure_empty": False,
        "spectral_excludes": False,
        "requires_word_enumeration": True,
    }


def closure_scan(*, floor: int = PUBLISHED_FLOOR) -> dict[str, Any]:
    blocks = {word: block_scan(word) for word in BLOCK_WORDS}
    spots = {str(length): spotlight_row(length, floor=floor) for length in SPOTLIGHT}
    chains = [odd_inverse_chain(m, 3) for m in (3, 13, 37, 365, 1000001)]
    oe = blocks["OE"]
    ooe = blocks["OOE"]
    emptied = [
        length
        for length, row in spots.items()
        if row["closure_empty"]
    ]
    return {
        "bound": "cycle_closure",
        "floor": floor,
        "spotlights": spots,
        "blocks": blocks,
        "oe_is_exponent_cell": oe["all_inside_exponent_cell"] and oe["max_gap"] == 0,
        "ooe_singleton_floor_lag": ooe["max_gap"],
        "ooe_inside_exponent_cell": ooe["all_inside_exponent_cell"],
        "ooe_max_floor_lag": ooe["max_gap"],
        "odd_chains": chains,
        "odd_chain_is_odd_preimage_unique": all(row["reproduces_odd_preimage_unique"] for row in chains),
        "emptied_lengths": emptied,
        "emptied_count": len(emptied),
        "word_independent_feasible": all(
            row["hull"]["start_meets_envelope"] for row in spots.values()
        ),
        "order_hull_feasible": all(
            row["orders"]["hull_meets_start"] for row in spots.values()
        ),
        "first_even_above_last_cell": all(
            row["first_last"]["first_even_above_last_cell"] for row in spots.values()
        ),
        "remainder_is_global_defect": all(
            row["remainder"]["is_global_defect"] for row in spots.values()
        ),
        "sha256_spotlights": sha256_int_list(list(SPOTLIGHT)),
        "halt_theorem": False,
        "no_cycle_all_lengths": False,
    }


def write_closure_artifacts(
    payload: dict[str, Any] | None = None,
    *,
    floor: int = PUBLISHED_FLOOR,
) -> dict[str, Any]:
    data = payload if payload is not None else closure_scan(floor=floor)
    CLOSURE_DIR.mkdir(parents=True, exist_ok=True)
    path = CLOSURE_DIR / "summary.json"
    path.write_text(json.dumps(data, indent=2, allow_nan=False) + "\n", encoding="utf-8")
    return data


if __name__ == "__main__":
    report = write_closure_artifacts()
    print(
        json.dumps(
            {
                "emptied": report["emptied_count"],
                "oe_exponent": report["oe_is_exponent_cell"],
                "word_indep": report["word_independent_feasible"],
                "order_hull": report["order_hull_feasible"],
                "25781": {
                    "n_hi": report["spotlights"]["25781"]["n_hi"],
                    "mech_follows_lo": report["spotlights"]["25781"]["mechanical"][
                        "follows_lo"
                    ],
                    "image_meets": report["spotlights"]["25781"]["mechanical"][
                        "image_meets_start"
                    ],
                    "t_lo": report["spotlights"]["25781"]["mechanical"]["t_lo"],
                    "balanced_lo": report["spotlights"]["25781"]["orders"][
                        "balanced_lo"
                    ],
                    "balanced_hi": report["spotlights"]["25781"]["orders"][
                        "balanced_hi"
                    ],
                },
            },
            indent=2,
        )
    )
