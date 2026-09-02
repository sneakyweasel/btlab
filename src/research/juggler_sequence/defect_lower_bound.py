"""First-defect amplification. Not a termination theorem.

The smallest forced contribution of the first positive local remainder
is the cubic/even lift through the suffix with later remainders dropped.
"""

from __future__ import annotations

from collections import defaultdict
from typing import Any

from research.juggler_sequence.global_defect import (
    follows_itinerary,
    global_defect,
    image_after,
    itinerary_word,
    local_defect,
    odd_count,
    pow_gap,
)
from research.juggler_sequence.lean_paths import has_named, juggler_text
from research.juggler_sequence.power_itineraries import floor_power

LEAN_THEOREMS = (
    "firstDefect",
    "firstDefect_spec",
    "firstDefect_pos",
    "firstDefect_prefix_tight",
    "firstDefect_contribution",
    "odd_defect_lift",
    "odd_defect_lift_lower_bound",
    "amplifyDefect",
    "amplifyDefect_mono",
    "global_defect_lower_bound",
    "normalizedDefect",
    "normalizedDefect_step",
    "conditional_remainder_lower_bound",
    "expanding_defect_lower_bound",
    "residualStep_firstDefect",
    "residualStep_amplify",
)


def first_defect(n: int, word: str) -> int:
    """Index of the first positive remainder, or ``len(word)`` if none."""
    current = n
    for i, letter in enumerate(word):
        if letter == "E" and current % 2 != 0:
            raise ValueError(f"{n} does not follow {word}")
        if letter == "O" and current % 2 != 1:
            raise ValueError(f"{n} does not follow {word}")
        if local_defect(current) > 0:
            return i
        current = floor_power(current)
    return len(word)


def amplify_defect(current: int, d: int, k: int, word: str) -> int:
    """Lift an already-inserted defect; later remainders are dropped."""
    if not word:
        return d
    letter = word[0]
    nxt = floor_power(current)
    if letter == "E":
        return amplify_defect(nxt, d, k + 1, word[1:])
    if letter == "O":
        lifted = pow_gap(current ** (2**k), d, 3)
        return amplify_defect(nxt, lifted, k + 1, word[1:])
    raise ValueError(f"unknown letter {letter!r}")


def odd_defect_lift(scale: int, d: int) -> int:
    return 3 * scale * scale * d + 3 * scale * d * d + d * d * d


def first_defect_payload(n: int, word: str) -> tuple[int, int, int, int, str]:
    """Return ``(j, x_j, rho_j, D_after, suffix)``."""
    j = first_defect(n, word)
    current = n
    for _ in range(j):
        current = floor_power(current)
    if j == len(word):
        return j, current, 0, 0, ""
    rho = local_defect(current)
    y = floor_power(current)
    d_after = pow_gap(y * y, rho, 2**j)
    return j, current, rho, d_after, word[j + 1 :]


def amplify_from_first(n: int, word: str) -> int:
    j, current, rho, d_after, suffix = first_defect_payload(n, word)
    if j == len(word):
        return 0
    return amplify_defect(floor_power(current), d_after, j + 1, suffix)


def crude_first_contribution(n: int, word: str) -> int:
    j, _current, rho, _d_after, _suffix = first_defect_payload(n, word)
    if j == len(word):
        return 0
    return rho ** (2**j)


def formal_surplus(n: int, word: str) -> int:
    o = odd_count(word)
    k = len(word)
    return n ** (3**o) - n ** (2**k)


def ooe_structural_bound(n: int, word: str) -> int:
    """Closed-form F for OOE / OOEO / OOOE from first-defect location."""
    j, current, rho, _d_after, _suffix = first_defect_payload(n, word)
    if word.startswith("OOE") and j == 0:
        return 3 * floor_power(n) ** 4 * rho
    if word.startswith("OOE") and j == 1:
        return local_defect(floor_power(n)) ** 2
    if word == "OOOE" and j == 0:
        t = floor_power(n)
        t2 = floor_power(t)
        # O then O: D >= 3 t^4 rho, then O: >= 3 t2^8 * (3 t^4 rho)
        return 9 * (t2 ** 8) * (t ** 4) * rho
    if word == "OOOE" and j == 1:
        t = floor_power(n)
        return 3 * (t ** 4) * local_defect(t)
    if word == "OOOE" and j == 2:
        return local_defect(floor_power(floor_power(n))) ** 4
    return crude_first_contribution(n, word)


def remainder_residue_census(*, n_max: int = 4000) -> dict[str, Any]:
    even_by_mod4: dict[int, list[int]] = defaultdict(list)
    odd_by_mod8: dict[int, list[int]] = defaultdict(list)
    even_two_t_even: list[int] = []
    even_two_t_odd: list[int] = []
    for x in range(1, n_max + 1):
        y = floor_power(x)
        rho = local_defect(x)
        if x % 2 == 0:
            even_by_mod4[x % 4].append(rho)
            if x % 4 == 2:
                if y % 2 == 0:
                    even_two_t_even.append(rho)
                else:
                    even_two_t_odd.append(rho)
        else:
            odd_by_mod8[x % 8].append(rho)
    return {
        "n_max": n_max,
        "even_mod4_min": {m: min(vals) for m, vals in even_by_mod4.items()},
        "odd_mod8_min": {m: min(vals) for m, vals in odd_by_mod8.items()},
        "even_two_t_even_min": min(even_two_t_even) if even_two_t_even else None,
        "even_two_t_odd_min": min(even_two_t_odd) if even_two_t_odd else None,
        "odd_seven_min_pos": min((r for r in odd_by_mod8[7] if r > 0), default=None),
        "odd_three_min_pos": min((r for r in odd_by_mod8[3] if r > 0), default=None),
        "odd_one_zero_exists": 0 in odd_by_mod8[1],
    }


def frontier_scan(*, n_max: int = 250) -> dict[str, Any]:
    words = ("OOE", "OOEO", "OOOE")
    out: dict[str, Any] = {}
    for word in words:
        rows: list[dict[str, Any]] = []
        f_beats_surplus = 0
        f_gt_delta = 0
        amplify_gt_delta = 0
        expanding = 0
        contracting = 0
        loc_counts: dict[int, int] = defaultdict(int)
        min_r_expanding = None
        for n in range(3, n_max + 1, 2):
            if not follows_itinerary(n, word):
                continue
            end = image_after(n, word)
            delta = global_defect(n, word)
            surplus = formal_surplus(n, word)
            j, _x, rho, _d, _s = first_defect_payload(n, word)
            loc_counts[j] += 1
            amp = amplify_from_first(n, word)
            crude = crude_first_contribution(n, word)
            structural = ooe_structural_bound(n, word)
            if amp > delta:
                amplify_gt_delta += 1
            if structural > delta:
                f_gt_delta += 1
            expanding_here = end >= n
            if expanding_here:
                expanding += 1
                if surplus > 0:
                    ratio = delta / surplus
                    if min_r_expanding is None or ratio < min_r_expanding:
                        min_r_expanding = ratio
                if structural > surplus:
                    f_beats_surplus += 1
            else:
                contracting += 1
            if n <= n_max and (n <= 40 or expanding_here):
                rows.append(
                    {
                        "n": n,
                        "j": j,
                        "rho": rho,
                        "end": end,
                        "delta": delta,
                        "surplus": surplus,
                        "amp": amp,
                        "crude": crude,
                        "F": structural,
                        "R": (delta / surplus) if surplus > 0 else None,
                    }
                )
        out[word] = {
            "checked": expanding + contracting,
            "expanding": expanding,
            "contracting": contracting,
            "first_defect_locations": dict(loc_counts),
            "amplify_gt_delta": amplify_gt_delta,
            "F_gt_delta": f_gt_delta,
            "F_beats_surplus_expanding": f_beats_surplus,
            "min_R_expanding": min_r_expanding,
            "sample": rows[:12],
        }
    return out


def amplification_census(*, n_max: int = 60, k_max: int = 5) -> dict[str, Any]:
    amp_fail = 0
    crude_fail = 0
    mixed = 0
    expand_r: list[float] = []
    amp_over_crude: list[float] = []
    loc_by_j: dict[int, int] = defaultdict(int)
    for n in range(1, n_max + 1):
        for k in range(1, k_max + 1):
            word = itinerary_word(n, k)
            if not follows_itinerary(n, word):
                continue
            delta = global_defect(n, word)
            amp = amplify_from_first(n, word)
            crude = crude_first_contribution(n, word)
            if amp > delta:
                amp_fail += 1
            if crude > delta:
                crude_fail += 1
            j = first_defect(n, word)
            loc_by_j[j] += 1
            if j < k:
                mixed += 1
                if crude > 0:
                    amp_over_crude.append(amp / crude)
                surplus = formal_surplus(n, word)
                end = image_after(n, word)
                if end >= n and surplus > 0:
                    expand_r.append(delta / surplus)
    return {
        "amp_fail": amp_fail,
        "crude_fail": crude_fail,
        "mixed_with_defect": mixed,
        "min_amp_over_crude": min(amp_over_crude) if amp_over_crude else None,
        "min_R_expanding": min(expand_r) if expand_r else None,
        "max_R_expanding": max(expand_r) if expand_r else None,
        "first_defect_histogram": dict(sorted(loc_by_j.items())),
    }


def lean_api_present() -> dict[str, bool]:
    text = juggler_text()
    return {
        "sorry_free": "sorry" not in text and "admit" not in text,
        **{name: has_named(text, name) for name in LEAN_THEOREMS},
    }
