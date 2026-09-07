"""Cycle height forces a run alphabet.

A nontrivial Juggler cycle has a minimum ``m`` and a maximum ``M``.  Two elementary
bookkeeping facts bound its runs by the height ratio ``R = log M / log m``:

* an **odd** run of length ``r`` takes its bottom ``v`` to about ``v^{(3/2)^r}``, and the
  bottom is at least ``m`` while the top is at most ``M``, so ``(3/2)^r <= R``;
* an **even** run of length ``g`` takes its top ``w`` down to about ``w^{1/2^g}``, so
  ``2^g <= R``.

The letter counts are not free either.  A cycle closes, so ``o log(3/2) = e log 2`` up to
floor defects, giving ``o/e = log2/log(3/2) = 1.7095``.  In a *cyclic* word with no two
adjacent odd letters every odd letter is followed by an even one, so ``o <= e``.  Since
``1.7095 > 1`` that is impossible: **every nontrivial cycle contains two consecutive odd
steps**, hence ``M >= m^{9/4}``.

Push the height a little further and the itinerary collapses to a two-block alphabet.  If
``R < 27/8`` then odd runs have length at most two and even runs exactly one, so the cycle
word is a cyclic sequence over ``{OE, OOE}``.  Only ``OOE`` climbs, with log-exponent
``9/8``; ``OE`` falls with ``3/4``.  Closing the cycle pins their proportions exactly.

**The discrepancy sliver.**  Write ``s = o/L`` and ``D_t = o_t - t s`` for the count
discrepancy of a prefix.  With ``alpha = log(3/2)``, ``beta = log 2`` and closure
``o alpha = e beta``, the walk height is exactly ``u_t = (alpha + beta) D_t``, so
``log R = log 3 * Delta`` with ``Delta = max D - min D``.  Balanced (mechanical) words are
``Delta < 1``, i.e. ``R < 3``; the two-block band is ``Delta < log(27/8)/log 3 = 1.107``.
Between them sits a sliver of two-block words that close without being balanced.  A run
of ``k`` consecutive ``OOE`` blocks climbs exactly ``k(2-3s)+s`` in ``D``; a run of ``j``
consecutive ``OE`` spans ``(1-s)+j(2s-1)``.  At the forced slope that caps ``OOE``-runs at
``3`` for mechanical and ``4`` for the band, and ``OE``-runs at ``2`` for both.  An exact
census of necklaces near the forced mix finds exactly one balanced necklace per pair and a
sliver thinner than the band by orders of magnitude.

This is a statement about *shape*, not a halt theorem.  It says nothing about whether a
cycle exists; it says what one would have to look like while its height stays low.
"""

from __future__ import annotations

import json
from fractions import Fraction
from itertools import combinations
from math import log
from typing import Any

from research.juggler_sequence.lean_paths import DATA_ROOT

ARTIFACT = DATA_ROOT / "cycle_run_alphabet" / "summary.json"

N0_CERTIFIED = 350_000_000
"""The certified floor: every start at or below this reaches 1."""

LOG_RATIO_OE = log(2.0) / log(1.5)
"""``o/e`` for any cycle, from ``(3/2)^o (1/2)^e = 1``."""

FORCED_SLOPE = log(2.0) / log(3.0)
"""``o/L`` for any cycle: ``log 2 / log 3 = 0.6309``."""

BALANCED_CAP = 1.0
"""``Delta < 1`` is the balanced (mechanical) condition: ``R < 3``."""

BAND_CAP = log(27 / 8) / log(3.0)
"""``Delta < log(27/8)/log 3 = 1.107`` is the two-block band ``R < 27/8``."""


# --------------------------------------------------------------------------- run bounds


def max_odd_run(height_ratio: float) -> int:
    """Largest ``r`` with ``(3/2)^r < R``: an odd run cannot exceed it."""
    r = 0
    while 1.5 ** (r + 1) < height_ratio:
        r += 1
    return r


def max_even_run(height_ratio: float) -> int:
    """Largest ``g`` with ``2^g < R``."""
    g = 0
    while 2.0 ** (g + 1) < height_ratio:
        g += 1
    return g


def block_exponent(odd_run: int, even_run: int) -> float:
    """Log-exponent of the block ``O^r E^g``: ``(3/2)^r (1/2)^g``."""
    return (1.5 ** odd_run) * (0.5 ** even_run)


def admissible_blocks(height_ratio: float) -> list[tuple[int, int]]:
    """Blocks ``O^r E^g`` a cycle of this height ratio can contain, ``r, g >= 1``."""
    return [(r, g)
            for r in range(1, max_odd_run(height_ratio) + 1)
            for g in range(1, max_even_run(height_ratio) + 1)]


def two_block_mix() -> dict[str, float]:
    """In the band ``R < 27/8`` the alphabet is ``{OE, OOE}``; closure pins the mix.

    ``(3/4)^a (9/8)^b = 1`` with ``a`` copies of ``OE`` and ``b`` of ``OOE``.
    """
    a_over_b = log(9 / 8) / log(4 / 3)
    frac_ooe = 1.0 / (1.0 + a_over_b)
    return {
        "oe_per_ooe": a_over_b,
        "ooe_fraction_of_blocks": frac_ooe,
        "letter_ratio_check": (2 * frac_ooe + (1 - frac_ooe)) / 1.0,
        "ooe_start_fraction_of_letters": frac_ooe / (2 * (1 - frac_ooe) + 3 * frac_ooe),
    }


def forced_min_height(min_odd_run: int = 2) -> float:
    """``M >= m^{(3/2)^r}`` once a run of length ``r`` is forced."""
    return 1.5 ** min_odd_run


def floor_defect_bound(period: int, minimum: int) -> float:
    """Relative size of the accumulated floor defect in the closure equation."""
    absolute = period / minimum
    scale = period * log(1.5)
    return absolute / scale


def oo_integer_witness(x: int) -> dict[str, int] | None:
    """The clean integer chain for one ``OO``, checked on a concrete ``x``.

    ``x^9 <= (y^2 + 2y)^3 = y^3 (y+2)^3 <= 2 y^6 < 2 (z+1)^4`` for ``y >= 8``.
    """
    from math import isqrt

    if x % 2 == 0:
        return None
    y = isqrt(x ** 3)
    if y % 2 == 0 or y < 8:
        return None
    z = isqrt(y ** 3)
    return {"x": x, "y": y, "z": z,
            "x9": x ** 9, "two_z1_4": 2 * (z + 1) ** 4}


# --------------------------------------------------------------------------- discrepancy


def block_letters(blocks: str) -> str:
    """``'1'`` is ``OE`` and ``'2'`` is ``OOE``."""
    return "".join("OE" if b == "1" else "OOE" for b in blocks)


def letter_slope(a: int, b: int) -> Fraction:
    """``o/L`` for ``a`` copies of ``OE`` and ``b`` of ``OOE``."""
    return Fraction(a + 2 * b, 2 * a + 3 * b)


def discrepancy(word: str) -> Fraction:
    """``max D - min D`` over the cyclic word, ``D_t = o_t - t o/L``, exact."""
    L = len(word)
    o = word.count("O")
    s = Fraction(o, L)
    D = Fraction(0)
    lo = hi = D
    for c in word:
        D += (1 - s) if c == "O" else -s
        lo, hi = min(lo, D), max(hi, D)
    assert D == 0, "not a closed word"
    return hi - lo


def ooe_run_climb(k: int, s: Fraction | float) -> Fraction | float:
    """Exact climb in ``D`` of ``k`` consecutive ``OOE`` blocks from a boundary: ``k(2-3s)+s``."""
    return k * (2 - 3 * s) + s


def oe_run_range(j: int, s: Fraction | float) -> Fraction | float:
    """Exact range in ``D`` of ``j`` consecutive ``OE`` blocks: ``(1-s) + j(2s-1)``."""
    return (1 - s) + j * (2 * s - 1)


def max_ooe_run(delta_cap: float, s: float = FORCED_SLOPE) -> int:
    """Longest ``OOE``-run whose climb stays below the cap."""
    k = 0
    while ooe_run_climb(k + 1, s) < delta_cap:
        k += 1
    return k


def max_oe_run(delta_cap: float, s: float = FORCED_SLOPE) -> int:
    j = 0
    while oe_run_range(j + 1, s) < delta_cap:
        j += 1
    return j


def necklaces(a: int, b: int):
    """One representative per cyclic arrangement of ``a`` ``OE`` and ``b`` ``OOE``."""
    n = a + b
    seen: set[str] = set()
    for pos in combinations(range(n), a):
        w = ["2"] * n
        for p in pos:
            w[p] = "1"
        joined = "".join(w)
        canon = min(joined[i:] + joined[:i] for i in range(n))
        if canon in seen:
            continue
        seen.add(canon)
        yield canon


def _longest_cyclic_run(nk: str, ch: str) -> int:
    other = "1" if ch == "2" else "2"
    doubled = nk + nk
    best = max((len(seg) for seg in doubled.split(other)), default=0)
    return min(best, len(nk))


def necklace_census(a: int, b: int) -> dict[str, Any]:
    """Classify every necklace by ``Delta``: balanced, sliver, or above the band."""
    counts = {"balanced": 0, "sliver": 0, "above": 0}
    min_nonbalanced: Fraction | None = None
    max_delta = Fraction(0)
    runs: dict[str, dict[str, int]] = {"balanced": {}, "sliver": {}}
    for nk in necklaces(a, b):
        d = discrepancy(block_letters(nk))
        max_delta = max(max_delta, d)
        if d < 1:
            cls = "balanced"
        elif float(d) < BAND_CAP:
            cls = "sliver"
        else:
            cls = "above"
        if cls != "balanced":
            min_nonbalanced = d if min_nonbalanced is None else min(min_nonbalanced, d)
        counts[cls] += 1
        if cls in runs:
            key = f"ooe{_longest_cyclic_run(nk, '2')}_oe{_longest_cyclic_run(nk, '1')}"
            runs[cls][key] = runs[cls].get(key, 0) + 1
    return {
        "a": a, "b": b, "L": 2 * a + 3 * b, "slope": float(letter_slope(a, b)),
        "necklaces": sum(counts.values()), **counts,
        "min_nonbalanced_delta": (float(min_nonbalanced) if min_nonbalanced is not None else None),
        "max_delta": float(max_delta),
        "run_profile": runs,
    }


# --------------------------------------------------------------------------- summary


def summary() -> dict[str, Any]:
    bands = {}
    for name, ratio in (("two", 2.0), ("nine_quarters", 2.25),
                        ("twentyseven_eighths", 27 / 8), ("four", 4.0)):
        bands[name] = {
            "height_ratio": ratio,
            "max_odd_run": max_odd_run(ratio),
            "max_even_run": max_even_run(ratio),
            "blocks": [f"O^{r}E^{g}" for r, g in admissible_blocks(ratio)],
        }
    mix = two_block_mix()
    witnesses = [w for w in (oo_integer_witness(x) for x in range(9, 400, 2)) if w]
    census = [necklace_census(a, b) for a, b in ((2, 5), (3, 7), (4, 10), (5, 12))]
    return {
        "n0_certified": N0_CERTIFIED,
        "letter_ratio_o_over_e": LOG_RATIO_OE,
        "forced_slope_o_over_L": FORCED_SLOPE,
        "adjacent_odd_forced": LOG_RATIO_OE > 1.0,
        "forced_min_height_exponent": forced_min_height(2),
        "cycle_max_lower_bound": float(N0_CERTIFIED ** forced_min_height(2)),
        "bands": bands,
        "absolute_bands_at_floor": {
            "two_block_alphabet_below": float(N0_CERTIFIED ** (27 / 8)),
            "no_double_even_below": float(N0_CERTIFIED ** 4),
        },
        "two_block_mix": mix,
        "fair_ooe_start_density": 1 / 8,
        "ooe_start_mismatch": mix["ooe_start_fraction_of_letters"] / (1 / 8),
        "band_ceiling_exponent": 27 / 8,
        "band_ceiling_value": float(N0_CERTIFIED ** (27 / 8)),
        "floor_defect_relative": floor_defect_bound(780_239, N0_CERTIFIED),
        "oo_chain_holds_on_witnesses": all(w["x9"] < w["two_z1_4"] for w in witnesses),
        "oo_witnesses_checked": len(witnesses),
        "discrepancy": {
            "balanced_cap": BALANCED_CAP,
            "band_cap": BAND_CAP,
            "mechanical_height_ratio": 3.0,
            "ooe_run_cap_mechanical": max_ooe_run(BALANCED_CAP),
            "ooe_run_cap_band": max_ooe_run(BAND_CAP),
            "oe_run_cap_mechanical": max_oe_run(BALANCED_CAP),
            "oe_run_cap_band": max_oe_run(BAND_CAP),
            "four_ooe_height_ratio": float(3.0 ** ooe_run_climb(4, FORCED_SLOPE)),
            "census": census,
        },
    }


def main() -> None:
    s = summary()
    ARTIFACT.parent.mkdir(parents=True, exist_ok=True)
    ARTIFACT.write_text(json.dumps(s, indent=2) + "\n", encoding="utf-8")
    print(f"o/e = {s['letter_ratio_o_over_e']:.6f}; adjacent OO forced: "
          f"{s['adjacent_odd_forced']}")
    print(f"cycle max >= m^{s['forced_min_height_exponent']} >= "
          f"{s['cycle_max_lower_bound']:.4e}")
    for name, b in s["bands"].items():
        print(f"  R < {b['height_ratio']:6.3f}: odd run <= {b['max_odd_run']}, "
              f"even run <= {b['max_even_run']}, blocks {b['blocks']}")
    m = s["two_block_mix"]
    print(f"  band alphabet mix: OOE fraction {m['ooe_fraction_of_blocks']:.6f}, "
          f"letter ratio {m['letter_ratio_check']:.6f}")
    d = s["discrepancy"]
    print(f"  discrepancy caps: balanced < {d['balanced_cap']}, band < {d['band_cap']:.4f}")
    print(f"  OOE-run cap: {d['ooe_run_cap_mechanical']} mechanical, {d['ooe_run_cap_band']} band; "
          f"OE-run cap: {d['oe_run_cap_mechanical']} / {d['oe_run_cap_band']}")
    for c in d["census"]:
        print(f"  ({c['a']},{c['b']}) L={c['L']}: {c['necklaces']} necklaces, "
              f"{c['balanced']} balanced, {c['sliver']} sliver, {c['above']} above; "
              f"min non-balanced Delta {c['min_nonbalanced_delta']}")
    print(f"wrote {ARTIFACT}")


if __name__ == "__main__":
    main()
