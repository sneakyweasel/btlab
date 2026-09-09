"""Exact controls for the wave-bearing supplement; not an analytic proof."""
from fractions import Fraction as F
from pathlib import Path
import argparse
import json


def falling(a, order):
    result = F(1)
    for j in range(order):
        result *= a-j
    return result


def difference(values, base, *steps):
    if not steps:
        return values[base]
    return (difference(values, base+steps[0], *steps[1:])
            - difference(values, base, *steps[1:]))


def validate():
    counts = {}
    offset_first = F(3, 2)*F(1, 2)
    zero_first = F(3, 4)*F(-1, 2)
    offset_second = F(3, 2)*falling(F(3, 4), 2)
    zero_second = F(3, 4)*falling(F(-3, 4), 2)
    assert (offset_first, zero_first) == (F(3, 4), F(-3, 8))
    assert (offset_second, zero_second) == (F(-9, 32), F(63, 64))
    main_second = F(3, 2)*3*falling(F(3, 4), 2)
    assert main_second == F(-27, 32)
    # First-order Taylor cancellation in A_h; d=2h at the last step.
    a1 = F(9, 4)-F(3, 2)*F(3, 2)
    a2 = falling(F(9, 4), 2)/2-F(3, 2)*(
        F(3, 2)*F(3, 4)+falling(F(3, 2), 2)/2)
    assert a1 == 0 and a2 == F(-27, 32)
    assert 4*a2*falling(F(1, 4), 2) == F(81, 128)
    # Chain rule exponents and the broadened twist budget.
    assert F(-1, 2)*F(3, 2) == F(-3, 4)
    assert F(-3, 2)*F(3, 2)+1 == F(-5, 4)
    assert F(9, 8)+F(3, 4)-3 == F(-9, 8)
    assert F(9, 8)-F(3, 4)-3+1 == F(-13, 8)
    counts["frozen_coefficients_and_derivative_identities"] = 12

    cases = 0
    # No analytic assumptions are used by this base-zero telescope.
    for coefficients in ((1, -1, 2), (-3, 2, 1), (0, 0, 4), (2, -5, 7)):
        for y0 in range(-4, 5):
            for y1 in range(-4, 5):
                for y2 in range(-4, 5):
                    values = [y0, y1, y2]
                    lhs = sum(q*y for q, y in zip(coefficients, values))
                    rhs = sum(coefficients)*y0+sum(
                        coefficients[i]*(values[i]-y0) for i in (1, 2))
                    assert lhs == rhs
                    # Also valid when base zero has no original coefficient.
                    assert coefficients[1]*y1+coefficients[2]*y2 == (
                        (coefficients[1]+coefficients[2])*y0
                        + coefficients[1]*(y1-y0)+coefficients[2]*(y2-y0))
                    cases += 1
    counts["shifted_wave_telescope_cases"] = cases

    cases = 0
    for h in range(1, 5):
        for r in range(1, 5):
            for e in (0, 2, 6):
                for power in range(0, 6):
                    values = {n: F(n**power, 7) for n in range(30)}
                    mixed = difference(values, e, 2*h, 2*r)
                    four = (values[e+2*h+2*r]-values[e+2*h]
                            - values[e+2*r]+values[e])
                    assert mixed == four
                    assert mixed == difference(values, e, 2*r, 2*h)
                    cases += 1
    counts["commuting_shift_and_four_corner_cases"] = cases

    cases = 0
    for xnum in range(-13, 32):
        x = F(xnum, 7)
        theta = x-x//1
        for dnum in range(0, 35):
            gap = F(dnum, 6)
            b = gap//1
            delta = gap-b
            carry = int(theta >= 1-delta)
            assert (x+gap)//1-x//1 == b+carry
            # theta_+ = theta + gap - beta.
            beta = (x+gap)//1-x//1
            assert x+gap-(x+gap)//1 == theta+gap-beta
            for v in (-7, -1, 1, 8):
                endpoint_phase = v*x-v*(1-delta)-v*(x+gap)
                assert endpoint_phase.denominator == 1
            cases += 1
    counts["carry_and_endpoint_phase_cases"] = cases

    costs = {
        "D1_floor_offset": F(1)+F(1, 2)-F(3, 4),
        "D1_floor_zero_offset": F(1)+F(1, 2)+F(1, 12)-F(5, 4),
        "main_theta": F(1, 24)+F(1, 12)+F(3, 4),
        "main_taylor": F(1, 24)+F(1, 4),
        "coarse_boundary_crossings": F(1, 12)+F(13, 24),
        "D2_original_runs": F(1, 24)+F(1, 2),
        "D2_coefficient_windows": F(1, 24)+F(1, 12)+F(1, 8),
        "common_partition_count": F(1, 12)+F(1, 2),
        "zero_mode_length": (F(1, 24)+F(1, 12))/2+F(5, 8),
        "zero_mode_h_endpoints": F(1, 24)+F(7, 8),
        "zero_mode_old_shift_endpoints": F(1, 24)+F(7, 8),
        "nonzero_mode_length": F(1, 8)+F(3, 4),
        "nonzero_mode_h_endpoints": F(1, 12)+F(3, 4),
        "nonzero_mode_old_shift_endpoints": F(1, 24)+F(3, 4),
        "discrepancy_diagonal": F(1)-F(1, 6),
        "discrepancy_length": F(3, 4)+F(1, 12),
        "D2_absolute_error": F(15, 16),
    }
    for name, exponent in costs.items():
        assert exponent <= F(15, 16), (name, exponent)
    assert costs["zero_mode_h_endpoints"] == F(11, 12)
    assert costs["main_theta"] == F(7, 8)
    assert costs["D2_coefficient_windows"] == F(1, 4)

    ratios = {
        "D1_zero_offset_to_main": F(1, 2)-F(7, 4)+F(3, 4),
        "twist_to_main": F(-13, 12)+F(3, 4),
        "D2_to_main": F(-15, 16)+F(3, 4),
        "main_to_nonzero_carry": F(1, 24)+F(1, 12)-F(1, 4),
        "main_smooth_remainder_to_main": F(1, 12)-1,
    }
    assert ratios["D1_zero_offset_to_main"] == F(-1, 2)
    assert ratios["twist_to_main"] == F(-1, 3)
    assert ratios["D2_to_main"] == F(-3, 16)
    assert ratios["main_to_nonzero_carry"] == F(-1, 8)
    assert all(v < 0 for v in ratios.values())
    # Offset/main ratio is O(1/(|t| h r)); it has no P saving.
    # The proof, not a false exponent assertion, removes fixed h<h0.

    transfer = {
        "small_shifted_seed_product": F(1, 24)+F(1, 24),
        "offset_cG_third": F(1, 24)-F(9, 8),
        "zero_cG_third": F(1, 8)-F(13, 8),
        "centered_X_third": F(5, 12)-F(3, 2),
    }
    assert transfer["small_shifted_seed_product"] <= F(1, 2)
    for name in ("offset_cG_third", "zero_cG_third", "centered_X_third"):
        assert transfer[name] <= F(-13, 12)
    diagonal = 2-F(1, 12)
    correlated = 1+F(15, 16)
    assert diagonal == F(23, 12) < correlated == F(31, 16)
    assert correlated/2 == F(31, 32) < 1
    counts["rational_exponent_controls"] = len(costs)+len(ratios)+len(transfer)+3
    return {
        "status": "PASS",
        "counts": counts,
        "absolute_cost_exponents": {k: str(v) for k, v in costs.items()},
        "curvature_ratio_exponents": {k: str(v) for k, v in ratios.items()},
        "transfer_exponents": {k: str(v) for k, v in transfer.items()},
        "final_exponent": "31/32 + epsilon",
        "scope": "Finite algebra and exponent controls; not an analytic proof.",
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

