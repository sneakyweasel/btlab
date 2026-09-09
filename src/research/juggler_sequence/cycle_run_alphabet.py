"""Exact run inequalities, separated from a floor-free word model.

The odd-run inequality is an UPPER growth bound, ``y^(2^r) <= v^(3^r)``;
it does not bound odd-run length from cycle height.  The even-run inequality
does imply ``2^g <= log(M)/log(m)``.  Two odd steps with intermediate at least
8 give ``x^9 < 2(z+1)^4``, retaining both the factor and shift.

Paper A gives strictly positive cycle drift ``o log(3/2) - e log 2 > 0``.
Thus the critical letter ratio is a lower bound, not an exact cycle ratio.
An OO exists by cyclic counting, so the integer maximum bound below applies
at the certified floor.  No two-block alphabet is deduced from cycle height.

Functions prefixed ``model_`` and the ``idealized_model`` output are only
floor-free arithmetic.  The necklace routines count prescribed abstract
words; their centered discrepancy is not actual Juggler cycle height.
This distinction repairs the withdrawn height-to-alphabet claim.  No halt
theorem or new cycle exclusion is claimed.
"""

from __future__ import annotations

import json
from fractions import Fraction
from itertools import combinations
from math import isqrt, log
from typing import Any

from research.juggler_sequence.lean_paths import DATA_ROOT

ARTIFACT = DATA_ROOT / "cycle_run_alphabet" / "summary.json"

N0_CERTIFIED = 350_000_000
"""The certified floor: every start at or below this reaches 1."""

LOG_RATIO_OE = log(2.0) / log(1.5)
"""Critical zero-drift ratio; an actual nontrivial cycle has strictly larger o/e."""

FORCED_SLOPE = log(2.0) / log(3.0)
"""Critical zero-drift slope, not an exact slope of a finite Juggler cycle."""

BALANCED_CAP = 1.0
"""The centered abstract-word condition Delta < 1; no actual height identification."""

BAND_CAP = log(27 / 8) / log(3.0)
"""A chosen abstract discrepancy cutoff; it does not force a Juggler alphabet."""


# --------------------------------------------------------------------------- run bounds


def model_max_odd_run(height_ratio: float) -> int:
    """Floor-free run cap for a STRICT height ceiling R, not a Juggler run bound."""
    r = 0
    while 1.5 ** (r + 1) < height_ratio:
        r += 1
    return r


def max_even_run_below(height_ratio: float) -> int:
    """Largest g with 2^g < R, for cycles with height STRICTLY BELOW R."""
    g = 0
    while 2.0 ** (g + 1) < height_ratio:
        g += 1
    return g


def block_exponent(odd_run: int, even_run: int) -> float:
    """Log-exponent of the block ``O^r E^g``: ``(3/2)^r (1/2)^g``."""
    return (1.5 ** odd_run) * (0.5 ** even_run)


def model_admissible_blocks(height_ratio: float) -> list[tuple[int, int]]:
    """Floor-free candidate blocks; not a certified alphabet for actual cycles."""
    return [(r, g)
            for r in range(1, model_max_odd_run(height_ratio) + 1)
            for g in range(1, max_even_run_below(height_ratio) + 1)]


def model_two_block_mix() -> dict[str, float]:
    """Zero-drift proportions in a prescribed floor-free {OE, OOE} model.

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


def oo_cycle_max_lower_bound(minimum: int) -> int:
    """Least integer M allowed by m^9 < 2(M+1)^4, conditional on an OO witness.

    The run must have intermediate at least 8 as in Lean ``oo_step_lower``.
    No floating-point rounding is used in this lower bound.
    """
    if minimum < 1:
        raise ValueError("minimum must be positive")
    return isqrt(isqrt(minimum ** 9 // 2))


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


CERTIFICATE_CLASSES = ("E", "OE", "OOEE", "OOOEE", "OOEOE")
"""Paper B Corollary 6.4: the depth-<=5 descent certificates, natural density 7/8."""


def certified_at(word: str, i: int) -> bool:
    """Does the depth-5 cyclic prefix at position ``i`` match a certificate?"""
    L = len(word)
    pre = "".join(word[(i + k) % L] for k in range(5))
    return any(pre.startswith(c) for c in CERTIFICATE_CLASSES)


def ooe_run_count(blocks: str) -> int:
    """Number of maximal cyclic runs of ``OOE`` blocks."""
    n = len(blocks)
    return sum(1 for i in range(n) if blocks[i] == "2" and blocks[(i - 1) % n] == "1")


def band_certificate_profile(a: int, b: int) -> dict[str, Any]:
    """Which certificates a band word can use, and how much of it stays uncertified.

    A band word has even runs of length one and odd runs of at most two, so ``OOEE`` and
    ``OOOEE`` can never occur: only three of the five classes are available.  The single
    uncertified depth-5 prefix is ``OOEOO``, the start of an ``OOE`` followed by another
    ``OOE``, so the uncertified count is exactly ``b - R`` for ``R`` the number of
    ``OOE``-runs.
    """
    L = 2 * a + 3 * b
    prefixes: dict[str, bool] = {}
    lo = hi = None
    formula_ok = True
    for nk in necklaces(a, b):
        w = block_letters(nk)
        unc = 0
        for i in range(L):
            pre = "".join(w[(i + k) % L] for k in range(5))
            ok = certified_at(w, i)
            prefixes.setdefault(pre, ok)
            unc += not ok
        if unc != b - ooe_run_count(nk):
            formula_ok = False
        f = Fraction(unc, L)
        lo = f if lo is None else min(lo, f)
        hi = f if hi is None else max(hi, f)
    return {
        "a": a, "b": b, "L": L,
        "prefixes_seen": sorted(prefixes),
        "uncertified_prefixes": sorted(k for k, v in prefixes.items() if not v),
        "classes_available": [c for c in CERTIFICATE_CLASSES
                              if any(pre.startswith(c) for pre in prefixes)],
        "min_uncertified_fraction": float(lo) if lo is not None else None,
        "max_uncertified_fraction": float(hi) if hi is not None else None,
        "count_formula_is_b_minus_runs": formula_ok,
    }


def band_uncertified_window() -> dict[str, float]:
    """Model uncertified fraction at zero drift, not a cycle-density theorem.

    ``R`` is the number of ``OOE``-runs.  In the band ``OE``-runs have length at most two,
    so ``R >= a/2``; ``OOE``-runs have length at most four, so ``R >= b/4``.  With
    ``a/b = 0.4094`` and ``L/b = 3.8188`` that windows the uncertified fraction.
    """
    r = log(9 / 8) / log(4 / 3)
    L_over_b = 2 * r + 3
    lo = (1 - r) / L_over_b
    hi = (1 - max(r / 2, 0.25)) / L_over_b
    return {
        "ooe_block_start_fraction": 1 / L_over_b,
        "uncertified_low": lo,
        "uncertified_high": hi,
        "fair_share": 0.125,
        "ratio_low": lo / 0.125,
        "ratio_high": hi / 0.125,
    }


# --------------------------------------------------------------------------- summary


def summary() -> dict[str, Any]:
    bands = {}
    for name, ratio in (("two", 2.0), ("nine_quarters", 2.25),
                        ("twentyseven_eighths", 27 / 8), ("four", 4.0)):
        bands[name] = {
            "height_ratio": ratio,
            "max_odd_run": model_max_odd_run(ratio),
            "max_even_run": max_even_run_below(ratio),
            "blocks": [f"O^{r}E^{g}" for r, g in model_admissible_blocks(ratio)],
        }
    mix = model_two_block_mix()
    witnesses = [w for w in (oo_integer_witness(x) for x in range(9, 400, 2)) if w]
    census = [necklace_census(a, b) for a, b in ((2, 5), (3, 7), (4, 10), (5, 12))]
    return {
        "scope": "exact integer bounds plus a separate idealized word model; no height-to-alphabet theorem",
        "n0_certified": N0_CERTIFIED,
        "cycle_drift": "o log(3/2) - e log 2 > 0 (Paper A), not equality",
        "cycle_max_lower_bound": oo_cycle_max_lower_bound(N0_CERTIFIED + 1),
        "cycle_max_lower_bound_inequality": "m^9 < 2(M+1)^4, using an OO with intermediate >= 8",
        "absolute_bands_at_floor": {
            "no_double_even_below": N0_CERTIFIED ** 4,
        },
        "oo_chain_holds_on_witnesses": all(w["x9"] < w["two_z1_4"] for w in witnesses),
        "oo_witnesses_checked": len(witnesses),
        "idealized_model": {
            "scope": "floor-free and prescribed-word calculations only; not realized cycle geometry",
            "critical_letter_ratio_o_over_e": LOG_RATIO_OE,
            "critical_slope_o_over_L": FORCED_SLOPE,
            "bands": bands,
            "two_block_mix": mix,
            "fair_ooe_start_density": 1 / 8,
            "ooe_start_mismatch": mix["ooe_start_fraction_of_letters"] / (1 / 8),
            "band_ceiling_exponent": 27 / 8,
            "band_ceiling_value": float(N0_CERTIFIED ** (27 / 8)),
            "certificates": {
                "classes": list(CERTIFICATE_CLASSES),
                "band_profile": [band_certificate_profile(a, b) for a, b in ((3, 7), (5, 12))],
                "window": band_uncertified_window(),
            },
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
        },
    }


def main() -> None:
    s = summary()
    ARTIFACT.parent.mkdir(parents=True, exist_ok=True)
    ARTIFACT.write_text(json.dumps(s, indent=2) + "\n", encoding="utf-8")
    print(s["scope"])
    print(f"Integer OO consequence at the certified floor: M >= {s['cycle_max_lower_bound']}")
    model = s["idealized_model"]
    for name, b in model["bands"].items():
        print(f"  MODEL R < {b['height_ratio']:6.3f}: odd run <= {b['max_odd_run']}, "
              f"even run <= {b['max_even_run']}, blocks {b['blocks']}")
    m = model["two_block_mix"]
    print(f"  zero-drift MODEL mix: OOE fraction {m['ooe_fraction_of_blocks']:.6f}, "
          f"letter ratio {m['letter_ratio_check']:.6f}")
    d = model["discrepancy"]
    print(f"  discrepancy caps: balanced < {d['balanced_cap']}, band < {d['band_cap']:.4f}")
    print(f"  OOE-run cap: {d['ooe_run_cap_mechanical']} mechanical, {d['ooe_run_cap_band']} band; "
          f"OE-run cap: {d['oe_run_cap_mechanical']} / {d['oe_run_cap_band']}")
    for c in d["census"]:
        print(f"  ({c['a']},{c['b']}) L={c['L']}: {c['necklaces']} necklaces, "
              f"{c['balanced']} balanced, {c['sliver']} sliver, {c['above']} above; "
              f"min non-balanced Delta {c['min_nonbalanced_delta']}")
    c = model["certificates"]["window"]
    print(f"  uncertified band fraction {c['uncertified_low']:.4f}-{c['uncertified_high']:.4f} "
          f"vs fair {c['fair_share']}: ratio {c['ratio_low']:.2f}-{c['ratio_high']:.2f}")
    prof = model["certificates"]["band_profile"][0]
    print(f"  band uses only {prof['classes_available']}; uncertified prefix "
          f"{prof['uncertified_prefixes']}")
    print(f"wrote {ARTIFACT}")


if __name__ == "__main__":
    main()
