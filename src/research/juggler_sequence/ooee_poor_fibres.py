"""Bounded census of actual OOEE fibres, with exact rational mass brackets.

No asymptotic equidistribution or exceptional-set estimate is assumed.
FateOOEEAssembly.lean checks the later contagion implication with the
actual odd-production bounds explicit; this census supplies no analytic proof.
Run with ``python -m research.juggler_sequence.ooee_poor_fibres``.
"""

from __future__ import annotations

import json
from fractions import Fraction
from math import fsum, isqrt, log1p


def ceil_cuberoot(value: int) -> int:
    """Least nonnegative integer r with value <= r**3, using integers only."""
    if value < 0:
        raise ValueError("value must be nonnegative")
    low, high = 0, 1 << ((value.bit_length() + 2) // 3)
    while low < high:
        middle = (low + high) // 2
        if middle**3 < value:
            low = middle + 1
        else:
            high = middle
    return low


def odd_inverse_boundary(target: int) -> int:
    """Least n with floor(n**(3/2)) >= target; no parity guard."""
    if target < 0:
        raise ValueError("target must be nonnegative")
    return ceil_cuberoot(target * target)


def source_interval(target: int) -> range:
    """Unguarded exact OOEE fibre, as a half-open integer interval."""
    if target < 1:
        raise ValueError("target must be positive")

    def boundary(m: int) -> int:
        return odd_inverse_boundary(odd_inverse_boundary(m**4))

    return range(boundary(target), boundary(target + 1))


def fibre(target: int) -> tuple[int, ...]:
    """Positive n whose actual first four Juggler letters are OOEE, J^4(n)=m."""
    interval = source_interval(target)
    first = interval.start + (1 - interval.start % 2)
    result = []
    for n in range(first, interval.stop, 2):
        u = isqrt(n**3)
        if u % 2 == 0:
            continue
        v = isqrt(u**3)
        if v % 2 == 0 and isqrt(v) % 2 == 0:
            result.append(n)
    return tuple(result)


def mass_ratio_bounds(target: int, sources: tuple[int, ...]) -> tuple[Fraction, Fraction]:
    """Rigorous bounds for sum w(n)/w(target), using log(1+x) brackets.

    Caller supplies an increasing tuple of positive odd sources.
    """
    if target < 1:
        raise ValueError("target must be positive")
    if not sources:
        return Fraction(0), Fraction(0)
    even = target + target % 2
    count = len(sources)
    return (Fraction(count * (even - 1), sources[-1] + 2),
            Fraction(count * (even + 1), sources[0]))


def inspect_target(target: int) -> dict:
    sources = fibre(target)
    lower, upper = mass_ratio_bounds(target, sources)
    even = target + target % 2
    ratio = fsum(log1p(2 / n) for n in sources) / log1p(2 / (even - 1))
    return {"target": target, "count": len(sources), "ratio_approx": ratio,
            "lower": lower, "upper": upper}


def guard_counts(target: int) -> dict:
    """Separate the three guards on all odd candidates, using exact integers."""
    interval = source_interval(target)
    counts = {"odd_candidates": 0, "first_image_odd": 0,
              "second_image_even": 0, "root_even": 0, "all_guards": 0}
    for n in range(interval.start + (1 - interval.start % 2), interval.stop, 2):
        u = isqrt(n**3)
        v = isqrt(u**3)
        root = isqrt(v)
        counts["odd_candidates"] += 1
        counts["first_image_odd"] += u % 2 == 1
        counts["second_image_even"] += v % 2 == 0
        counts["root_even"] += root % 2 == 0
        counts["all_guards"] += u % 2 == 1 and v % 2 == 0 and root % 2 == 0
    return {"target": target, "interval": [interval.start, interval.stop], **counts}


def resonance_census() -> list[dict]:
    """Five targets around each slow-slope integer a=4..16 and a=27.

    The center is floor((8a/9)**(9/2)), computed exactly. The smooth
    slope is diagnostic; all guard counts use the actual nested floors.
    """
    rows = []
    for slope in [*range(4, 17), 27]:
        center = isqrt((8 * slope)**9 // 9**9)
        for target in range(center - 2, center + 3):
            rows.append({"slope_integer": slope, "offset": target - center,
                         **guard_counts(target)})
    return rows


def census() -> dict:
    """Full blocks below 4096, then 64 deterministic midpoints per dyadic block.

    Large-block samples are diagnostics, not exhaustive density measurements.
    Every threshold classification uses exact rational bounds, not floats.
    """
    rows = []
    for exponent in range(1, 21):
        base = 1 << exponent
        exhaustive = exponent < 12
        targets = (range(base, 2 * base) if exhaustive else
                   [base + ((2 * j + 1) * base) // 128 for j in range(64)])
        records = [inspect_target(m) for m in targets]
        worst = min(records, key=lambda r: r["ratio_approx"])
        thresholds = {}
        for denominator in (18, 12, 10):
            threshold = Fraction(1, denominator)
            poor = [r for r in records if r["upper"] < threshold]
            unresolved = [r for r in records if r["lower"] < threshold <= r["upper"]]
            thresholds[f"1/{denominator}"] = {
                "certified_poor": len(poor), "unresolved": len(unresolved),
                "poor_reciprocal_mass_approx": fsum(1 / r["target"] for r in poor)}
        rows.append({"dyadic_exponent": exponent, "exhaustive": exhaustive,
                     "targets": len(records), "source_count": sum(r["count"] for r in records),
                     "mean_ratio_approx": fsum(r["ratio_approx"] for r in records) / len(records),
                     "min_ratio_approx": worst["ratio_approx"], "worst_target": worst["target"],
                     "worst_count": worst["count"],
                     "worst_exact_bracket": [str(worst["lower"]), str(worst["upper"])],
                     "thresholds": thresholds})
    return {"scope": "all targets 2..4095; 64 fixed midpoint targets in each [2^k,2^(k+1)), k=12..20",
            "reference_coefficient": "1/9", "census_proves_asymptotic_coefficient": False,
            "rows": rows}


if __name__ == "__main__":
    from research.juggler_sequence.lean_paths import DATA_ROOT

    result = {**census(), "resonance_diagnostic": resonance_census()}
    output = DATA_ROOT / "ooee_poor_fibres" / "summary.json"
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(output)
