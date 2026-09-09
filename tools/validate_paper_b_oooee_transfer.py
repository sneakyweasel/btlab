"""Exact OOOEE transfer controls; finite checks do not prove cancellation."""
from fractions import Fraction as F
from itertools import product
from math import isqrt
from pathlib import Path
import argparse
import json

from validate_paper_b_kernel_assembly import validate as validate_kernel


def frac(x):
    return x-x//1


def carry(a, b):
    return frac(a)+frac(b)-frac(a+b)


def falling(x, order):
    answer = F(1)
    for r in range(order):
        answer *= x-r
    return answer


def validate():
    counts = {}
    prior = validate_kernel()
    assert prior["status"] == "PASS"

    # New sign is negative. Original jY/2 contributes jD/2 exactly.
    values = [F(-3, 2), F(-1, 4), F(0), F(3, 5), F(7, 4)]
    corners = [(F(1), F(2), F(3), F(5)),
               (F(-2, 3), F(1, 7), F(2, 5), F(-3, 2))]
    cases = 0
    for y0, y1, y2, y12 in product(values, repeat=4):
        w1, w2 = y1-y0, y2-y0
        d = y12-y1-y2+y0
        k1, k2 = carry(y0, w1), carry(y0, w2)
        kp, ks = carry(y2, w1+d), carry(w1, d)
        for c0, c1, c2, c12 in corners:
            b2, b1 = c12-c1, c12-c2
            dd_c = c12-c1-c2+c0
            n2, n1 = b2//1, b1//1
            for original_j in (-3, 0, 4):
                lhs = F(original_j, 2)*d - (
                    c12*frac(y12)-c1*frac(y1)-c2*frac(y2)+c0*frac(y0))
                rhs = (F(original_j, 2)*d-dd_c*frac(y0)
                       -n2*w1-(b2-n2)*frac(w1)+b2*k1
                       -n1*w2-(b1-n1)*frac(w2)+b1*k2
                       -c12*frac(d)+c12*(ks+kp-k1))
                assert (lhs-rhs).denominator == 1  # equality modulo integers
                cases += 1
    counts["negative_centered_master_cases"] = cases

    # A signed four-corner jY/2 mode has zero undifferenced Y frequency.
    cases = 0
    for original_j in range(-9, 10):
        coeffs = [F(original_j, 2), -F(original_j, 2),
                  -F(original_j, 2), F(original_j, 2)]
        assert sum(coeffs) == 0
        assert coeffs[1]+coeffs[3] == coeffs[2]+coeffs[3] == 0
        for integer_q in range(-12, 13):
            q = integer_q+coeffs[3]
            assert (2*q).denominator == 1
            cases += 1
    counts["half_integer_D_inventory_cases"] = cases

    # Compute, rather than encode, the frozen leading coefficients.
    a = F(9, 4)
    base = F(3, 2)
    c = F(3, 4)
    cpow = F(9, 8)
    x_offset_power = base*(base-1)  # G offset has x^(3/4)
    g_offset = base

    pure_offset = (a/2)*falling(base*(a-1), 2)
    minus_anchor_offset = -(
        2*c*cpow*g_offset*x_offset_power
        +c*g_offset*falling(x_offset_power, 2))
    b_growing = a*(a-1)/2-c*base*(base-1)
    minus_center = -b_growing*falling(base, 2)
    mixed_offset = pure_offset+minus_anchor_offset+minus_center
    assert pure_offset == F(945, 512)
    assert minus_anchor_offset == F(-864, 512)
    assert b_growing == F(27, 32)
    assert minus_center == F(-324, 512)
    assert mixed_offset == F(-243, 512)

    # beta1*beta2 = 9 p x + lower terms is substituted AFTER differentiation.
    pure_zero = (a*(a-1)/2)*falling(base*(a-2), 2)*9
    g_zero_coeff = base*(base-1)
    g_zero_power = base*(base-2)
    minus_anchor_zero = -(2*c*cpow*g_zero_coeff*g_zero_power
                          +c*g_zero_coeff*falling(g_zero_power, 2))*9
    wave = base*falling(base*(base-1), 2)*3
    center_sum = 4*c*cpow
    negative_center_wave = -center_sum*wave
    mixed_zero = pure_zero+minus_anchor_zero+negative_center_wave
    assert pure_zero == F(-6075, 2048)
    assert minus_anchor_zero == F(243, 128)
    assert wave == F(-27, 32)
    assert center_sum == F(27, 8)
    assert negative_center_wave == F(729, 256)
    assert mixed_zero == F(3645, 2048)

    # Zero-offset theta coefficient: all three terms are bounded in range.
    pure_theta_zero = falling(a, 3)*9/2
    negative_anchor_theta_zero = -c*falling(base, 3)*9
    negative_wave_theta_zero = -center_sum*base*(base-1)*3
    theta_zero = pure_theta_zero+negative_anchor_theta_zero+negative_wave_theta_zero
    assert theta_zero == F(-243, 128)

    a5 = F(9, 8)
    small_l_curvature = falling(base*a5, 2)/2-(a5/2)*falling(base, 2)
    assert small_l_curvature == F(81, 512)
    counts["derived_frozen_coefficient_controls"] = 15

    # Formula exponents for each z-derivative and x-composition, with beta frozen.
    # Offset: a*b*z^(a-1). Zero offset: a(a-1)*beta1*beta2*z^(a-2).
    # beta1*beta2 has SIZE p*P, not a derivative factor.
    fifth = {
        "offset_z_derivative": base*(a5-2),
        "zero_z_derivative": 1+base*(a5-3),
        "offset_x_second": base*(a5-1)-2,
        "zero_x_second": 1+base*(a5-2)-2,
        "offset_x_third": base*(a5-1)-3,
        "zero_x_third": 1+base*(a5-2)-3,
    }
    assert list(fifth.values()) == [F(-21, 16), F(-29, 16),
                                   F(-29, 16), F(-37, 16),
                                   F(-45, 16), F(-53, 16)]
    first_shift_floor = F(1, 2)+base*(a5-2)
    first_shift_curvature = F(1, 2)+base*(a5-1)-2
    assert first_shift_floor == F(-13, 16)
    assert first_shift_curvature == F(-21, 16)
    counts["fifth_coordinate_derivative_exponents"] = len(fifth)+2

    freq, h1, h2 = F(1, 24), F(1, 48), F(1, 24)
    p, pi = h1+h2, freq+h1+h2
    budgets = {
        "initial_phase_error": freq+F(5, 8),
        "initial_fifth_error": freq+F(7, 16),
        "k0_small_shift_fifth_error": freq+F(1, 12)+F(3, 16),
        "k0_small_shift_relative_curvature": freq-F(9, 16),
        "k0_l_relative_i_curvature": freq-F(3, 16),
        "k0_l_relative_Fourier_curvature": F(1, 8)-F(3, 16),
        "k0_l_length_term": freq/2+F(27, 32),
        "k0_l_boundary_term": freq/2+F(11, 32),
        "k0_l_positive_error": 1-F(1, 8),
        "short_carry_error": 1-freq,
        "weighted_shift_product": pi,
        "moving_wave_product": pi+F(1, 8),
        "core_Taylor_offset_sum": freq-F(1, 8),
        "core_Taylor_zero_sum": pi-F(5, 8),
        "fifth_Taylor_offset_sum": freq-F(5, 16),
        "fifth_Taylor_zero_sum": freq+p-F(13, 16),
        "wave_Taylor_sum": pi+F(1, 8)-F(3, 4),
        "slow_D_replacement": freq+F(1, 4),
        "coarse_gap_density": h2-F(1, 2),
        "anchor_center_density": freq-F(5, 8),
        "Ni_density": freq+h2-F(7, 8),
        "twist_third_offset": freq-F(9, 8),
        "twist_third_zero": pi-F(13, 8),
        "twist_third_center": freq+F(3, 8)-F(3, 2),
        "fifth_third_offset": freq-F(45, 16),
        "fifth_third_zero": freq+p-F(53, 16),
        "offset_relative_Fourier_error": F(5, 16)-F(1, 2)+F(1, 8),
        "offset_length_term": freq/2+F(15, 16),
        "offset_boundary_term": F(3, 4)+F(1, 16),
        "zero_low_wave_relative": freq-F(1, 8),
        "zero_anchor_relative_integer": pi-F(1, 8),
        "zero_mode_length": pi/2+F(11, 16),
        "zero_mode_boundary": F(13, 24)+F(5, 16),
        "nonzero_mode_length": F(5, 32)+F(3, 4),
        "nonzero_mode_boundary": F(13, 24)+F(1, 4),
        "first_floor_errors": F(5, 6),
    }
    assert budgets["initial_phase_error"] == F(2, 3)
    assert budgets["wave_Taylor_sum"] == F(-25, 48)
    assert budgets["offset_length_term"] == F(23, 24)
    assert budgets["offset_relative_Fourier_error"] == F(-1, 16)
    assert max(budgets[k] for k in ("twist_third_offset", "twist_third_zero",
               "twist_third_center", "fifth_third_offset", "fifth_third_zero")) == F(-13, 12)
    assert max(budgets[k] for k in ("coarse_gap_density", "anchor_center_density",
                                    "Ni_density")) == F(-11, 24)
    assert budgets["zero_low_wave_relative"] == F(-1, 12)
    assert budgets["zero_anchor_relative_integer"] == F(-1, 48)
    zero = max(budgets[k] for k in ("zero_mode_length", "zero_mode_boundary",
                "nonzero_mode_length", "nonzero_mode_boundary", "first_floor_errors"))
    assert zero == F(29, 32)
    t2 = max(F(31, 32), budgets["offset_length_term"], zero,
             budgets["short_carry_error"])
    t1 = max(2-h2, 1+t2)/2
    mixed = max(2-h1, 1+t1)/2
    assert t2 == F(31, 32) and t1 == F(63, 64) and mixed == F(127, 128)
    assert mixed > F(95, 96) and mixed > F(47, 48)
    counts["rational_exponent_controls"] = len(budgets)+13

    # Finite exact test of formal signs vs actual map, never floating-point parity.
    census = {format(s, "04b"): 0 for s in range(16)}
    cases, oooee, full, sub = 0, 0, 0, 0
    minimal = ("E", "OE", "OOEE", "OOEOE", "OOOEE")
    for n in range(2, 20002):
        a_n, letters = n, []
        for _ in range(5):
            odd = a_n % 2
            letters.append("O" if odd else "E")
            a_n = isqrt(a_n**3) if odd else isqrt(a_n)
        word = "".join(letters)
        has_full = any(word.startswith(prefix) for prefix in minimal)
        has_sub = any(word.startswith(prefix) for prefix in minimal[:-1])
        assert has_full == (has_sub or word == "OOOEE")
        assert not (has_sub and word == "OOOEE")
        full += has_full
        sub += has_sub
        if n % 2:
            m = isqrt(n**3)
            v = isqrt(m**3)
            w = isqrt(v**3)
            u_floor = isqrt(w)
            signs = (m % 2, v % 2, w % 2, u_floor % 2)
            census["".join(map(str, signs))] += 1
            formal_oooee = signs == (1, 1, 0, 0)
            assert formal_oooee == (word == "OOOEE")
            oooee += formal_oooee
            cases += 1
    assert cases == 10000
    assert full == sub+oooee
    densities = [F(1, 2**len(w)) for w in minimal]
    assert sum(densities[:-1]) == F(27, 32)
    assert sum(densities) == F(7, 8)
    assert F(1, 2)*F(1, 16) == F(1, 32)
    counts["exact_formal_chain_equivalence_cases"] = cases
    counts["exact_certificate_union_cases"] = 20000

    # Orthogonality of all nonempty parity products on the sixteen formal signs.
    cases = 0
    for subset in product((0, 1), repeat=4):
        if not any(subset):
            continue
        total = sum((-1)**sum(a*b for a, b in zip(subset, bits))
                    for bits in product((0, 1), repeat=4))
        assert total == 0
        cases += 1
    counts["nonempty_sign_product_controls"] = cases

    return {
        "status": "PASS",
        "scope": "Exact finite algebra, derivative coefficients, and exponent controls; not an analytic proof.",
        "counts": counts,
        "prior_kernel_controls": prior["counts"],
        "coefficients": {"growing_theta_center": str(b_growing),
                         "mixed_nonzero_offset": str(mixed_offset),
                         "mixed_zero_offset": str(mixed_zero),
                         "zero_offset_theta": str(theta_zero),
                         "k0_l_curvature": str(small_l_curvature)},
        "fifth_coordinate_exponents": {k: str(v) for k, v in fifth.items()},
        "exponent_budgets": {k: str(v) for k, v in budgets.items()},
        "double_correlation_exponent": str(t2),
        "single_correlation_exponent": str(t1),
        "mixed_mode_exponent": str(mixed),
        "formal_chain_census_odd_3_through_20001": census,
        "finite_counts": {"oooee": oooee, "subfamily": sub, "full_certificates": full},
        "written_proof_density": "7/8",
        "historical_95_over_96_target": "UNPROVED",
        "independent_mathematical_review": False,
        "lean_verification": False,
    }


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    data = json.dumps(validate(), indent=2)+"\n"
    if args.output:
        args.output.write_text(data, encoding="utf-8")
    print(data, end="")

