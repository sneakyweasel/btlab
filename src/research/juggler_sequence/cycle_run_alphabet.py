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

This is a statement about *shape*, not a halt theorem.  It says nothing about whether a
cycle exists; it says what one would have to look like while its height stays low.
"""

from __future__ import annotations

import json
from math import log
from typing import Any

from research.juggler_sequence.lean_paths import DATA_ROOT

ARTIFACT = DATA_ROOT / "cycle_run_alphabet" / "summary.json"

N0_CERTIFIED = 350_000_000
"""The certified floor: every start at or below this reaches 1."""

LOG_RATIO_OE = log(2.0) / log(1.5)
"""``o/e`` for any cycle, from ``(3/2)^o (1/2)^e = 1``."""


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
    }


def forced_min_height(min_odd_run: int = 2) -> float:
    """``M >= m^{(3/2)^r}`` once a run of length ``r`` is forced."""
    return 1.5 ** min_odd_run


def floor_defect_bound(period: int, minimum: int) -> float:
    """Relative size of the accumulated floor defect in the closure equation.

    Each step loses at most ``1`` to the floor, so at most ``1/x_t`` in the log, and the
    closure equation's own terms are of size ``period * log(3/2)``.
    """
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
    return {
        "n0_certified": N0_CERTIFIED,
        "letter_ratio_o_over_e": LOG_RATIO_OE,
        "adjacent_odd_forced": LOG_RATIO_OE > 1.0,
        "forced_min_height_exponent": forced_min_height(2),
        "cycle_max_lower_bound": float(N0_CERTIFIED ** forced_min_height(2)),
        "bands": bands,
        "two_block_mix": mix,
        "band_ceiling_exponent": 27 / 8,
        "band_ceiling_value": float(N0_CERTIFIED ** (27 / 8)),
        "floor_defect_relative": floor_defect_bound(780_239, N0_CERTIFIED),
        "oo_chain_holds_on_witnesses": all(w["x9"] < w["two_z1_4"] for w in witnesses),
        "oo_witnesses_checked": len(witnesses),
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
    print(f"  floor defect relative size {s['floor_defect_relative']:.3e}")
    print(f"wrote {ARTIFACT}")


if __name__ == "__main__":
    main()
