"""Three fixed exact controls for terminal joint-cell obstructions.

The symbolic proofs are in the companion dossier. These are guarded open
blocks, not periodic orbits, terminal closures, or a source search.
"""
from __future__ import annotations

import argparse
from fractions import Fraction
import json
from math import isqrt
from pathlib import Path

from research.juggler_sequence.lean_paths import DATA_ROOT

FIXED_PARAMETERS = ((9, 5), (17, 17), (2**64 + 1, 2**128 + 1))


def fraction_record(value: Fraction) -> dict:
    return {"numerator": value.numerator, "denominator": value.denominator}


def mixed_cells(r: int) -> dict:
    if r < 9 or r % 4 != 1:
        raise ValueError("r must be at least nine and congruent to one modulo four")
    m, K = r*r, r*r-1
    h, M = K*K+1, K**3+3*K//2
    t, q = r**3-(3*r+1)//2, r**3
    low, high = m*m+1, m*m+2*m-1
    gap = q-t
    L = Fraction(r**3)-Fraction(3*r, 2)+Fraction(3, 4*r)
    negative_margin = M-L*L
    positive_bound = Fraction(3*(high-h), 4*(r+1))-gap
    deficit = m**3-M
    rho = Fraction(3**41, 2**65)
    checks = {
        "odd_sources_and_outputs": all(n % 2 for n in (m, h, t, q)),
        "even_sources_and_outputs": all(n % 2 == 0 for n in (M, low, high)),
        "O_h": isqrt(h**3) == M,
        "E_M": isqrt(M) == t,
        "E_s_low": isqrt(low) == m,
        "E_s_high": isqrt(high) == m,
        "O_m": isqrt(m**3) == q,
        "ordered_inside_cubic_band": m <= t < q < h < m*m < low < high < M < m**3,
        "mixed_gap_contracts_both": 0 < gap < low-h < high-h,
        "negative_sign_certificate": L > 0 and h**3 > M*M and negative_margin > 0,
        "positive_sign_certificate": high < (r+1)**4 and positive_bound > r,
        "height_deficit_gt_twice_m_squared": deficit > 2*m*m,
        "prior_smooth_strip": deficit**8 > m**15,
        "dc_smooth_strip": (2*deficit)**128 > m**253,
        "lr_clean_smooth_strip": (2*deficit)**64 > m**127,
        "lr_sharp_exponent_lt_two": Fraction(381, 128)-rho < 2,
    }
    assert all(checks.values())
    return {
        "r": r, "minimum": m, "h": h, "maximum": M, "t": t, "q": q,
        "s_low": low, "s_high": high, "output_gap": gap, "cube_deficit": deficit,
        "negative_certificate_margin": fraction_record(negative_margin),
        "positive_loss_lower_bound": fraction_record(positive_bound),
        "signed_loss_conclusions": ["Delta_B(s_low) < -1/2", "Delta_B(s_high) > r"],
        "cutoffs_active": {"dc": m >= 2**24, "lr": m >= 2**128},
        "checks": checks, "periodic_closure_asserted": False,
    }


def even_cells(a: int) -> dict:
    if a < 5 or a % 2 == 0:
        raise ValueError("a must be odd and at least five")
    b = a+2
    faces = (
        ("damping", a*a+1, (a+3)**2-2, Fraction(2, 3)),
        ("amplification", (a+1)**2-2, (a+2)**2+1, Fraction(2*(a+1), a+3)),
    )
    records = []
    for name, x, y, expected in faces:
        coefficient = Fraction((b-a)*(a+b), y-x)
        checks = {
            "actual_E_guards": x % 2 == y % 2 == 0,
            "odd_outputs": a % 2 == b % 2 == 1,
            "exact_root_cells": isqrt(x) == a and isqrt(y) == b,
            "strict_order": a < b < a*a < x < y,
            "surviving_height_margin": y < a**3-a*a,
            "exact_coefficient": coefficient == expected,
            "sharp_interval": Fraction(2, 3) <= coefficient < 2,
        }
        assert all(checks.values())
        records.append({
            "face": name, "x": x, "y": y, "outputs": [a, b],
            "remainders": [x-a*a, y-b*b],
            "cell_coefficient": fraction_record(coefficient), "checks": checks,
        })
    return {"minimum": a, "faces": records, "periodic_closure_asserted": False}


def report() -> dict:
    return {
        "scope": {
            "fixed_parameter_pairs": [list(p) for p in FIXED_PARAMETERS],
            "parameter_pairs": 3, "symbolic_families": 2,
            "source_census": False, "cycle_search": False, "rank_pair_scan": False,
            "trajectory_extension": False, "raised_floor": False,
        },
        "arithmetic": "integer square roots, exact fractions and integer power comparisons",
        "controls": [{"mixed": mixed_cells(r), "even": even_cells(a)} for r, a in FIXED_PARAMETERS],
        "decision": "PARK",
        "new_cycle_restriction": False,
        "full_joint_cell_comparison_proved": False,
        "no_cycle_proved": False,
        "new_lean_or_paper_claim": False,
        "proof_owner": "docs/problems/juggler_cycle_terminal_joint_cells.md",
        "proof_status": "symbolic written proofs; finite controls are consistency checks",
    }


def main(argv: list[str] | None = None) -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path,
                        default=DATA_ROOT/"cycle_terminal_joint_cells/summary.json")
    args = parser.parse_args(argv)
    data = report()
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(data, indent=2)+"\n", encoding="utf-8")
    print(json.dumps({"decision": data["decision"], "scope": data["scope"]}, indent=2))


if __name__ == "__main__":
    main()
