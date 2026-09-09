"""Exact algebra and exponent controls for the offset-anchor written proof."""
from fractions import Fraction as F
from pathlib import Path
import argparse
import json


def fall(a, order):
    out = F(1)
    for i in range(order):
        out *= a-i
    return out


def validate():
    counts = {}
    c = F(3, 4)
    exponent_c = F(9, 8)
    offset = F(3, 2)
    exponent_g = F(3, 4)
    full = c*offset*fall(exponent_c+exponent_g, 2)
    frozen_floor = c*fall(exponent_c, 2)*offset
    cross = 2*c*exponent_c*offset*exponent_g
    second = c*offset*fall(exponent_g, 2)
    center_coefficient = c*F(3, 4)
    center_curvature = center_coefficient*F(3, 4)
    anchor = cross+second
    composite = anchor-center_curvature
    assert full == F(945, 512)
    assert frozen_floor == F(81, 512)
    assert full-frozen_floor == anchor == F(27, 16)
    assert center_coefficient == F(9, 16)
    assert center_curvature == F(27, 64)
    assert full-center_curvature == F(729, 512)  # The historical omission.
    assert composite == F(81, 64) == F(648, 512)
    assert F(729, 512)-composite == F(81, 512)
    # Coefficient centering changes values, never differentiation of N.
    assert center_coefficient*F(3, 8) == F(27, 128)
    assert F(3, 4)*3 == F(9, 4)  # Wave theta coefficient.
    assert F(9, 4)*F(-1, 4) == F(-9, 16)  # Moving leading derivative.
    assert F(3, 4)*F(-3, 4)*3 == F(-27, 16)  # Frozen derivative.
    assert F(3, 2)*fall(F(3, 4), 2)*3 == F(-27, 32)
    counts["frozen_coefficients_and_correction_controls"] = 13

    cases = 0
    for bnum in range(-43, 44):
        b = F(bnum, 7)
        for residual in (F(-3, 2), F(-1, 7), F(0), F(4, 3)):
            bstar = b-residual
            n = bstar//1
            d = b-n
            assert 0 <= bstar-n < 1
            assert abs(d) <= 1+abs(residual)
            for xnum in range(-7, 12):
                x = F(xnum, 5)
                theta = x-x//1
                phase_difference = -b*theta-(-n*x-d*theta)
                assert phase_difference == n*(x//1)
                assert phase_difference.denominator == 1
                cases += 1
    counts["signed_smooth_centering_cases"] = cases

    cases = 0
    for xnum in range(0, 35):
        x = F(xnum, 7)
        theta = x-x//1
        for gapnum in range(0, 33):
            gap = F(gapnum, 6)
            integer = gap//1
            residual = gap-integer
            carry = int(theta >= 1-residual)
            assert (x+gap)//1-x//1 == integer+carry
            for mode in (-5, -1, 1, 7):
                # Endpoint factor e(-mode*(1-residual)) combines with e(mode*x).
                difference = mode*x-mode*(1-residual)-mode*(x+gap)
                assert difference.denominator == 1
            cases += 1
    counts["carry_and_endpoint_cases"] = cases

    cases = 0
    for b0 in range(-3, 4):
        for b1 in range(1, 5):
            for b2 in range(1, 5):
                for j in (-2, -1, 1, 2):
                    for power in range(1, 5):
                        value = lambda z: F(z**power, 3)
                        m = F(19, 2)
                        shifted = (value(m+b0+b1+b2+j)-value(m+b0+b1)
                                   -value(m+b0+b2)+value(m+b0))
                        base = m+b0
                        frozen = (value(base+b1+b2+j)-value(base+b1)
                                  -value(base+b2)+value(base))
                        assert shifted == frozen
                        assert frozen == (value(base+b2+b1+j)-value(base+b2)
                                          -value(base+b1)+value(base))
                        assert (value(base+b1+b2+j)-value(base+b1+b2)
                                +value(base+b1+b2)-value(base+b1)-value(base+b2)
                                +value(base)) == frozen
                        cases += 1
    counts["offset_branch_decomposition_cases"] = cases

    costs = {
        "floor_mismatch": F(3, 4),
        "anchor_offset_taylor": F(1, 24)-F(1, 8),
        "anchor_zero_offset_taylor": F(1, 8)-F(5, 8),
        "wave_taylor": 1+F(1, 2)-F(7, 4),
        "slow_floor_replacement": F(1, 24)+F(1, 4),
        "fourier_endpoint_error": F(5, 6),
        "original_gap_runs": F(1, 24)+F(1, 2),
        "floor_and_input_partition": F(3, 4),
        "new_center_drift": F(1, 24)+F(3, 8),
        "retained_length": 1+F(1, 48)-F(1, 16),
        "retained_endpoints": F(3, 4)+F(1, 16),
        "D2_absolute_error": F(15, 16),
        "D2_original_runs": F(1, 24)+F(1, 2),
        "D2_coefficient_windows": F(1, 24)+F(1, 8)+F(1, 8),
    }
    assert costs["retained_length"] == F(23, 24)
    assert costs["retained_endpoints"] == F(13, 16)
    assert all(v <= F(23, 24) for v in costs.values())

    curvature = {
        "anchor_zero_offset": F(1, 8)-F(5, 8),
        "anchor_shift_remainder": F(1, 12)-F(9, 8),
        "floor_residual": F(1, 24)-F(7, 8),
        "all_signed_waves": F(1, 2)-F(3, 4),
        "center_wave": F(1, 2)-F(3, 4),
        "center_floor_rounding": F(-1, 2),
        "retained_fourier_mode": F(5, 16)-F(1, 2),
        "shifted_carry": F(1, 4)+F(1, 24)-F(3, 2),
        "slow_offset": F(1, 24)-F(5, 4),
        "slow_zero_offset": F(1, 24)+F(1, 12)-F(7, 4),
        "smooth_twist": F(-1, 4),
        "D2_curvature": F(-15, 16),
    }
    assert all(v <= F(-3, 16) for v in curvature.values())
    assert max(curvature.values())+F(1, 8) == F(-1, 16)
    center = {
        "anchor_value_shift_error": F(1, 12)-F(5, 8),
        "anchor_value_zero_offset_error": F(1, 8)-F(1, 8),
        "wave_value_rounding": F(1, 2)-F(3, 4),
        "wave_value_shift_error": F(1, 2)+F(1, 24)-F(5, 4),
        "anchor_derivative_zero_offset": F(1, 8)-F(9, 8),
        "wave_derivative_residual": F(1, 2)-F(5, 4),
        "residual_variation_on_gap_run": F(-3, 4)+F(1, 2),
        "center_derivative_competitor_ratio": F(1, 2)-F(5, 4)+F(5, 8),
        "fourier_cutoff_to_anchor_frequency": F(5, 16)-F(3, 8),
    }
    assert center["anchor_value_zero_offset_error"] == 0
    assert all(v <= 0 for v in center.values())
    assert center["residual_variation_on_gap_run"] < 0
    assert center["center_derivative_competitor_ratio"] == F(-1, 8)
    assert center["fourier_cutoff_to_anchor_frequency"] == F(-1, 16)
    counts["rational_exponent_controls"] = len(costs)+len(curvature)+len(center)+1
    return {
        "status": "PASS", "counts": counts,
        "corrected_composite_coefficient": str(composite),
        "historical_coefficient": "729/512",
        "omitted_frozen_floor_coefficient": str(frozen_floor),
        "cost_exponents": {k: str(v) for k, v in costs.items()},
        "curvature_error_exponents": {k: str(v) for k, v in curvature.items()},
        "centering_exponents": {k: str(v) for k, v in center.items()},
        "final_exponent": "23/24 + epsilon",
        "scope": "Finite algebra and exponent controls, not an analytic proof.",
        "independent_mathematical_review": False,
        "kernel_and_oooee": "UNPROVED",
    }


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    result = validate()
    data = json.dumps(result, indent=2)+"\n"
    if args.output:
        args.output.write_text(data, encoding="utf-8")
    print(data, end="")
