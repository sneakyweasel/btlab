"""Three exact controls of a symbolic two-face predecessor family.

All eight displayed edges use the actual Juggler branch. They form open
paths, not a periodic orbit or a full common-prefix/suffix realization.
"""
from __future__ import annotations

from fractions import Fraction
import json
from math import isqrt

from research.juggler_sequence.lean_paths import DATA_ROOT

FIXED_PARAMETERS = (67, 83, 2**32+3)

POSITIVITY_POLYNOMIALS = {
    "a_lower": {8: 48, 0: 512},
    "a_upper": {12: 2, 8: -48, 4: 24, 0: -511},
    "h_lower": {18: 2, 12: -216, 10: 36, 4: -2916, 2: 108, 0: -1},
    "h_upper": {12: 216, 4: 2916},
    "M_lower": {9: 2, 2: -27, 1: 18, 0: -2},
    "M_upper": {2: 27, 0: 1},
    "b_low_lower": {10: 12, 8: -21, 6: 56, 4: -144, 2: 144, 0: -56},
    "b_low_upper": {12: 2, 10: -12, 8: 33, 6: -68, 4: 162, 2: -168, 0: 73},
    "b_high_lower": {12: 2, 8: -12, 6: -4, 4: -72, 2: 120, 0: -105},
    "b_high_upper": {8: 24, 6: -8, 4: 96, 2: -144, 0: 132},
    "s_low_lower": {2: 6, 0: -1},
    "s_low_upper": {6: 2, 0: -4},
    "s_high_lower": {4: 3, 2: 6, 0: 4},
    "s_high_upper": {6: 2, 4: -3, 0: -9},
    "q_lower_scaled": {9: 16, 8: -864, 6: 216, 5: 72, 4: -3240,
                       3: -72, 2: 4455, 1: 54, 0: -1729},
    "q_upper_scaled": {9: 112, 8: 864, 6: -216, 5: 504, 4: 3240,
                       3: -504, 2: -4455, 1: 378, 0: 1777},
    "a_minus_m": {8: 1, 6: -1, 2: -3, 0: 11},
    "b_low_minus_a": {4: 4, 2: -4, 0: -6},
    "t_minus_b_high": {9: 1, 8: -1, 4: -4, 2: 4, 1: 9, 0: -5},
    "q_minus_t_scaled": {5: 36, 3: -36, 1: -45, 0: 7},
    "h_minus_q_scaled": {12: 8, 9: -8, 5: -36, 4: 96, 3: 36, 1: -27, 0: 1},
    "m_squared_minus_h": {8: 6, 6: -6, 4: -3, 2: -18, 0: 9},
    "M_minus_s_high": {18: 1, 12: -1, 10: 18, 8: -6, 6: 6,
                       4: -12, 2: 66, 0: -14},
    "height_margin": {14: 9, 12: -11, 10: 9, 8: -66, 6: 66,
                      4: -99, 2: 63, 0: -44},
    "left_loss_margin": {9: 16, 2: -1728, 1: 144, 0: -65},
}


def coefficient_certificates() -> list[dict]:
    """Uniform rational positivity certificates, not a parameter scan."""
    records = []
    for name, coefficients in POSITIVITY_POLYNOMIALS.items():
        degree = max(coefficients)
        leading = coefficients[degree]
        negative_budget = sum(
            (Fraction(-value, 67**(degree-power))
             for power, value in coefficients.items() if value < 0),
            Fraction(0),
        )
        ratio = negative_budget/leading
        assert 0 <= ratio < 1
        assert name == "q_lower_scaled" or ratio < Fraction(1, 2)
        records.append({
            "polynomial": name, "degree": degree,
            "negative_to_leading_ratio": fraction_record(ratio),
            "positive_for_every_r_at_least": 67,
        })
    return records


def ceil_cuberoot(n: int) -> int:
    if n < 0:
        raise ValueError("nonnegative radicand required")
    lo, hi = 0, 1 << ((n.bit_length()+2)//3)
    while lo < hi:
        mid = (lo+hi)//2
        if mid**3 >= n:
            hi = mid
        else:
            lo = mid+1
    return lo


def fraction_record(value: Fraction) -> dict:
    return {"numerator": value.numerator, "denominator": value.denominator}


def family(r: int) -> dict:
    if r < 67 or r % 16 != 3:
        raise ValueError("r must be at least 67 and congruent to 3 modulo 16")
    a = r**8+8
    h = r**12+12*r**4
    M = r**18+18*r**10+54*r*r-1
    t = r**9+9*r-1
    m = r**6+3*r*r-3
    q_numerator = 8*r**9+36*r**5-36*r**3+27*r-1
    assert q_numerator % 8 == 0
    q = q_numerator//8
    b_low = r**8+4*r**4-4*r*r+2
    b_high = b_low+2
    s_low = m*m+6*r*r-1
    s_high = s_low+3*r**4+5
    edges = [
        ("O", a, h), ("O", h, M), ("E", M, t),
        ("O", b_low, s_low), ("O", b_high, s_high),
        ("E", s_low, m), ("E", s_high, m), ("O", m, q),
    ]
    edge_records = []
    for branch, x, y in edges:
        n = 3 if branch == "O" else 1
        assert x % 2 == int(branch == "O")
        remainder = x**n-y*y
        assert isqrt(x**n) == y and 0 <= remainder < 2*y+1
        edge_records.append({
            "branch": branch, "source": x, "target": y,
            "square_remainder": remainder, "upper_margin": 2*y+1-remainder,
            "actual_guard": True,
        })
    deficit = m**3-M
    e_low_upper = Fraction(1, 8)-Fraction(9, 4*r)+Fraction(27, 8*r**3)
    e_left_lower = 1-Fraction(27, 2*r**7)
    positive_lower = Fraction(3*(s_high-m*m), 4*(r**3+1))-1
    checks = {
        "strict_local_order": m < a < b_low < b_high < t < q < h < m*m
                              < s_low < s_high < M < m**3,
        "all_lower_states_odd": all(x % 2 for x in (m, a, b_low, b_high, t, q, h)),
        "all_upper_states_even": all(x % 2 == 0 for x in (s_low, s_high, M)),
        "unique_predecessor_h": ceil_cuberoot(h*h) == a,
        "unique_predecessor_s_low": ceil_cuberoot(s_low*s_low) == b_low,
        "unique_predecessor_s_high": ceil_cuberoot(s_high*s_high) == b_high,
        "upper_alignment_ceiling": ceil_cuberoot(m**4) == b_low,
        "noncube_minimum": r**6 < m < (r*r+1)**3,
        "cube_deficit_gt_twice_m_squared": deficit > 2*m*m,
        "prior_height_strip": deficit**8 > m**15,
        "dc_height_strip": (2*deficit)**128 > m**253,
        "lr_clean_height_strip": (2*deficit)**64 > m**127,
        "lr_sharp_exponent_lt_two": Fraction(381, 128)-Fraction(3**41, 2**65) < 2,
        "negative_loss_certificate": e_low_upper < Fraction(1, 8)
                                     and e_left_lower > Fraction(7, 8),
        "negative_loss_below_minus_three_quarters":
            e_low_upper-e_left_lower < -Fraction(3, 4),
        "positive_loss_certificate": s_high < (m+1)**2
                                     and m+1 < (r**3+1)**2
                                     and positive_lower > 2*r-1,
    }
    assert all(checks.values()), checks
    return {
        "r": r, "minimum": m, "maximum": M, "a": a, "h": h, "t": t, "q": q,
        "b_low": b_low, "b_high": b_high, "s_low": s_low, "s_high": s_high,
        "cube_deficit": deficit, "edges": edge_records,
        "negative_loss_upper_bound": fraction_record(e_low_upper-e_left_lower),
        "positive_loss_lower_bound": fraction_record(positive_lower),
        "cutoffs_active": {"dc": m >= 2**24, "lr": m >= 2**128},
        "checks": checks,
        "periodic_orbit_asserted": False,
        "full_return_seam_asserted": False,
    }


def report() -> dict:
    return {
        "decision": "CLOSE",
        "scope": "simultaneous cut O-predecessors do not force a mixed-loss sign",
        "fixed_parameters": list(FIXED_PARAMETERS),
        "uniform_coefficient_certificates": coefficient_certificates(),
        "controls": [family(r) for r in FIXED_PARAMETERS],
        "source_search": False, "orbit_search": False, "raised_floor": False,
        "new_actual_cycle_bound": False, "no_cycle_proved": False,
        "new_lean_or_paper_claim": False,
        "proof_owner": "docs/problems/juggler_cycle_cut_predecessors.md",
        "proof_status": "AI-assisted symbolic proof with exact finite controls, not Lean",
    }


def main() -> None:
    data = report()
    destination = DATA_ROOT/"cycle_cut_predecessors/summary.json"
    destination.parent.mkdir(parents=True, exist_ok=True)
    destination.write_text(json.dumps(data, indent=2)+"\n", encoding="utf-8")
    print(json.dumps({
        "decision": data["decision"],
        "fixed_parameters": data["fixed_parameters"],
        "actual_edges_checked": sum(len(row["edges"]) for row in data["controls"]),
        "new_actual_cycle_bound": False,
    }, indent=2))


if __name__ == "__main__":
    main()
