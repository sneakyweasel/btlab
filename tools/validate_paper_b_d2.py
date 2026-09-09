"""Exact controls for the D2 research supplement; not an analytic proof."""
from fractions import Fraction as F
from pathlib import Path
import argparse
import json

def validate():
    counts = {}
    cases = 0
    # Both signs, removable-integer cases, and fractional-part endpoints.
    for b_num in range(-24, 25):
        for g_num in range(-30, 31):
            b = F(b_num, 7)
            g = F(g_num, 5)
            n = b // 1
            beta = b - n
            fract_g = g - g // 1
            assert 0 <= beta < 1
            # Equality of exponentials is exact equality modulo an integer.
            difference = b * fract_g - n * g - beta * fract_g
            assert difference == -n * (g // 1)
            assert difference.denominator == 1
            # The smooth residual phase differentiates N as a fixed integer.
            for r in (-5, 0, 7):
                assert n + r - b == r - beta
            cases += 1
    counts["centering_cases"] = cases

    cases = 0
    for c_num in (-5, 0, 7):
        for cp_num in (-11, 2, 19):
            c, cp = F(c_num, 3), F(cp_num, 7)
            for g_num in range(-15, 16):
                for gp_num in range(-15, 16):
                    g, gp = F(g_num, 4), F(gp_num, 4)
                    a, ap = g // 1, gp // 1
                    original = -(cp * ap - c * a)
                    replaced = -(cp - c) * a
                    assert original - replaced == -cp * (ap - a)
                    if a == ap:
                        assert original == replaced
                    cases += 1
    counts["floor_difference_cases"] = cases

    cases = 0
    # Arbitrary rational sequence values: no Juggler or smoothness assumptions.
    for y0 in range(-5, 6):
        for y1 in range(-5, 6):
            for y2 in range(-5, 6):
                wave = F(y1 - y0, 7)
                for u in (-10, -2, 2, 10):
                    assert u * wave + (-u) * wave == 0
                    unequal = u * F(y1-y0, 7) - F(u, 2) * F(y2-y0, 7)
                    assert unequal == -F(u, 2) * F(y2-2*y1+y0, 7)
                cases += 1
    counts["signed_wave_cases"] = cases

    # Frozen beta values, before substituting beta_1 beta_2 ~ 9 h_1 h_2 x.
    assert F(3, 4) * F(-3, 4) == F(-9, 16)
    assert F(-9, 16) * F(-7, 4) == F(63, 64)
    assert F(3, 2) * F(3, 4) == F(9, 8)
    assert F(9, 8) * F(-1, 4) == F(-9, 32)
    counts["frozen_derivative_coefficients"] = 4

    # Every positive term retained in the slow-variable majorant count.
    checks = {
        "zero_offset_P_over_Q": F(1)-F(5,16),
        "zero_offset_D_over_aQ": F(1,2)+F(3,4)-F(5,16),
        "zero_offset_Pa": F(1,4)+F(1,12),
        "original_runs": F(1,2)+F(1,24),
        "nonzero_offset_D_over_aQ": F(1,2)+F(1,24)+F(1,4)-F(5,16),
        "nonzero_offset_Pa": F(3,4),
        "floor_crossings": F(1,8)+F(3,4),
        "shifted_run_boundaries": F(1,8)+F(1,2)+F(1,24),
        "coefficient_windows": F(1,24)+F(1,8)+F(1,8),
        "new_run_inverse_curvature": F(1,24)+F(7,8),
        "new_window_inverse_curvature": F(1,24)+F(1,16)+F(1,2),
        "literal_continuous_tail": F(1)+F(7,24)-F(5,16),
    }
    assert checks["zero_offset_D_over_aQ"] == F(15,16)
    assert checks["new_run_inverse_curvature"] == F(11,12)
    assert checks["literal_continuous_tail"] == F(47,48)
    assert all(v < 1 for v in checks.values())
    assert all(v <= F(15,16) for key,v in checks.items()
               if key != "literal_continuous_tail")

    ratios = [
        F(5,16)-F(1,2),
        F(5,16)+F(1,12)-1,
        F(1,24)-F(3,8),
        F(1,24)+F(1,12)-F(7,8),
    ]
    assert ratios == [F(-3,16), F(-29,48), F(-1,3), F(-3,4)]
    assert F(1,8)+F(1,8)+F(1,12)-F(3,4) == F(-5,12)
    counts["positive_error_exponents"] = len(checks)
    counts["curvature_ratio_exponents"] = len(ratios)
    counts["near_integer_increment_exponent"] = 1

    def propagate(inner):
        chain = [inner]
        for shift_exp in (F(1,12), F(1,24), F(1,48)):
            squared = max(2-shift_exp, 1+chain[-1])
            chain.append(squared/2)
        return chain
    assert propagate(F(15,16)) == [F(15,16), F(31,32), F(63,64), F(127,128)]
    assert propagate(F(47,48)) == [F(47,48), F(95,96), F(191,192), F(383,384)]
    counts["conditional_differencing_chains"] = 2

    # A formal exact model showing why the individual E_J increment error
    # cannot be charged as 1/J near an integer.
    for power in range(2, 18):
        p_scale = 2 ** (8 * power)
        j_cut = 2 ** power
        increment = F(1, 2 ** (6 * power))
        assert j_cut * increment < 1
        assert min(F(1), 1 / (j_cut * increment)) == 1
        assert p_scale > p_scale // j_cut
    counts["near_integer_majorant_controls"] = 16

    return {
        "status": "PASS",
        "scope": "Exact identities and exponent bookkeeping only; no proof of analytic cancellation.",
        "counts": counts,
        "error_exponents": {k:str(v) for k,v in checks.items()},
        "curvature_ratio_exponents": [str(v) for v in ratios],
        "conditional_centered_chain": [str(v) for v in propagate(F(15,16))],
        "conditional_literal_tail_chain": [str(v) for v in propagate(F(47,48))],
        "kernel_status": "UNPROVED",
        "oooee_status": "UNPROVED",
    }

if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    result = validate()
    rendered = json.dumps(result, indent=2) + "\n"
    if args.output:
        args.output.write_text(rendered, encoding="utf-8")
    print(rendered, end="")
