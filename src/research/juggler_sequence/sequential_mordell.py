"""Consecutive odd near-Mordell steps. Not a termination theorem.

Two odd Juggler steps give x^3 = y^2+ρ and y^3 = z^2+σ. The
polynomial (x^3-ρ)^3 = (z^2+σ)^2 is y^6 = y^6. The sequential
defect Γ = x^9 - z^4 is globalDefect of the word OO. Peak slack
needs an even maximum, which a second odd step does not supply.
"""

from __future__ import annotations

from collections import Counter
from math import gcd
from typing import Any

from research.juggler_sequence.global_defect import global_defect, local_defect
from research.juggler_sequence.lean_paths import has_named, juggler_text
from research.juggler_sequence.power_itineraries import floor_power
from research.juggler_sequence.progress_coverage import is_odd_odd

N_MAX = 2000

LEAN_THEOREMS = (
    "oddMordellStep",
    "twoOddMordellSteps",
    "sequentialDefect",
    "oddMordellStep_add",
    "oddMordellStep_lt",
    "oddMordellStep_iff",
    "odd_remainder_even",
    "two_step_mordell_identity",
    "sequential_defect_eq_global",
    "sequential_power_identity",
    "peak_needs_even_max",
    "two_odd_steps_not_peak_shape",
)

OO_CHAIN = {
    "x": 365,
    "y": 6973,
    "z": 582276,
}


def v2(n: int) -> int:
    if n == 0:
        return -1
    return (n & -n).bit_length() - 1


def odd_mordell_row(x: int) -> dict[str, Any] | None:
    if x % 2 == 0 or x <= 1:
        return None
    y = floor_power(x)
    if y % 2 == 0:
        return None
    z = floor_power(y)
    rho = local_defect(x)
    sigma = local_defect(y)
    gamma = x**9 - z**4
    delta = global_defect(x, "OO")
    return {
        "x": x,
        "y": y,
        "z": z,
        "rho": rho,
        "sigma": sigma,
        "gamma": gamma,
        "delta_oo": delta,
        "rho_even": rho % 2 == 0,
        "sigma_even": sigma % 2 == 0,
        "y_odd": y % 2 == 1,
        "z_parity": z % 2,
        "gcd": gcd(rho, sigma),
        "v2_rho": v2(rho),
        "v2_sigma": v2(sigma),
        "rho_over_y": rho / y if y else None,
        "sigma_over_z": sigma / z if z else None,
        "rho_over_y2": rho / (y * y) if y else None,
        "sigma_over_z2": sigma / (z * z) if z else None,
        "identity": (x**3 - rho) ** 3 == (z**2 + sigma) ** 2,
        "gamma_eq_delta": gamma == delta,
        "peak_shape": y % 2 == 0,
    }


def sequential_mordell_census(*, n_max: int = N_MAX) -> dict[str, Any]:
    rows: list[dict[str, Any]] = []
    gcds: Counter[int] = Counter()
    v2_pairs: Counter[tuple[int, int]] = Counter()
    identity_fail = 0
    gamma_fail = 0
    odd_rho = 0
    peak_shape = 0
    for n in range(3, n_max + 1, 2):
        if not is_odd_odd(n):
            continue
        row = odd_mordell_row(n)
        if row is None:
            continue
        rows.append(row)
        gcds[row["gcd"]] += 1
        v2_pairs[(row["v2_rho"], row["v2_sigma"])] += 1
        if not row["identity"]:
            identity_fail += 1
        if not row["gamma_eq_delta"]:
            gamma_fail += 1
        if not row["rho_even"]:
            odd_rho += 1
        if row["peak_shape"]:
            peak_shape += 1

    gcd_vals = [row["gcd"] for row in rows]
    distinct_sigma_for_rho_mod = 0
    rho_mod8: dict[int, set[int]] = {}
    for row in rows:
        rho_mod8.setdefault(row["rho"] % 8, set()).add(row["sigma"] % 8)
    for residues in rho_mod8.values():
        if len(residues) > 1:
            distinct_sigma_for_rho_mod += 1

    return {
        "n_max": n_max,
        "pairs": len(rows),
        "identity_fail": identity_fail,
        "gamma_fail": gamma_fail,
        "odd_rho": odd_rho,
        "peak_shape": peak_shape,
        "gcd_most_common": dict(gcds.most_common(8)),
        "gcd_gt_2": sum(1 for g in gcd_vals if g > 2),
        "v2_pairs": {f"{a},{b}": c for (a, b), c in v2_pairs.most_common(8)},
        "rho_mod8_splits_sigma": distinct_sigma_for_rho_mod,
        "rho_mod8_classes": len(rho_mod8),
        "example": {
            "x": rows[0]["x"],
            "y": rows[0]["y"],
            "z": rows[0]["z"],
            "rho": rows[0]["rho"],
            "sigma": rows[0]["sigma"],
            "gamma": rows[0]["gamma"],
        }
        if rows
        else None,
    }


def lean_api_present() -> dict[str, bool]:
    text = juggler_text()
    return {
        "sorry_free": "sorry" not in text and "admit" not in text,
        **{name: has_named(text, name) for name in LEAN_THEOREMS},
    }
