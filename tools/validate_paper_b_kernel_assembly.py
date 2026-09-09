"""Exact assembly controls for Paper B; finite tests do not prove cancellation."""
from fractions import Fraction as F
from itertools import product
from pathlib import Path
import argparse
import json


def frac(x):
    return x-x//1


def carry(a, b):
    return frac(a)+frac(b)-frac(a+b)


def add(*vectors):
    return tuple(sum(v[i] for v in vectors) for i in range(4))


def scale(q, vector):
    return tuple(q*x for x in vector)


def validate():
    counts = {}
    values = [F(-3, 2), F(-1, 4), F(0), F(3, 5), F(7, 4)]
    weights = [
        (F(1), F(2), F(3), F(5)),
        (F(-2, 3), F(1, 7), F(2, 5), F(-3, 2)),
        (F(0), F(1), F(1), F(2)),
        (F(1), F(1), F(1), F(1)),
    ]
    cases = 0
    binary = 0
    for y0, y1, y2, y12 in product(values, repeat=4):
        w1, w2 = y1-y0, y2-y0
        d = y12-y1-y2+y0
        k1, k2 = carry(y0, w1), carry(y0, w2)
        kp, ks = carry(y2, y12-y2), carry(w1, d)
        assert w1+d == y12-y2
        assert y2+(w1+d) == y12
        for kap in (k1, k2, kp, ks):
            assert kap in (0, 1)
            # Equality of polynomials in z=e(g), valid for every real g.
            left = {int(kap): F(1)}
            right = {p: a for p, a in ((0, 1-kap), (1, kap)) if a}
            assert left == right
            binary += 1
        for c0, c1, c2, c12 in weights:
            b2, b1 = c12-c1, c12-c2
            lhs = c12*frac(y12)-c1*frac(y1)-c2*frac(y2)+c0*frac(y0)
            rhs = ((c12-c1-c2+c0)*frac(y0)
                   +b2*(frac(w1)-k1)+b1*(frac(w2)-k2)
                   +c12*(frac(d)-ks-kp+k1))
            assert lhs == rhs
            cases += 1
    counts["master_identity_cases"] = cases
    counts["binary_exponential_polynomial_cases"] = binary

    cases = 0
    for bnum in range(-43, 44):
        b = F(bnum, 7)
        n = b//1
        beta = b-n
        for wnum in range(-17, 24):
            w = F(wnum, 5)
            difference = b*frac(w)-(n*w+beta*frac(w))
            assert difference == -n*(w//1)
            assert difference.denominator == 1
            cases += 1
    counts["centered_growing_coefficient_cases"] = cases

    # All carry Fourier arguments in the exact basis (Y,W1,W2,D).
    y = (1, 0, 0, 0)
    w1 = (0, 1, 0, 0)
    w2 = (0, 0, 1, 0)
    d = (0, 0, 0, 1)
    y1, y2, y12 = add(y, w1), add(y, w2), add(y, w1, w2, d)
    shifted_w1 = add(w1, d)
    layers = [(y, w1, y1), (y, w2, y2), (w1, d, shifted_w1),
              (y2, shifted_w1, y12), (y, w1, y1)]
    cases = 0
    cutoff = 3
    for arguments in product(*layers):
        for signs in product((-1, 1), repeat=5):
            coeff = add(*(scale(cutoff*s, arg) for s, arg in zip(signs, arguments)))
            assert all(abs(v) <= 5*cutoff for v in coeff)
            for r1, r2 in ((-cutoff, -cutoff), (-cutoff, cutoff),
                           (cutoff, -cutoff), (cutoff, cutoff)):
                retained = add(coeff, scale(r1, w1), scale(r2, w2))
                assert max(map(abs, retained)) <= 6*cutoff
            cases += 1
    counts["carry_inventory_vertex_cases"] = cases

    cases = 0
    for q0, q1, q2, q12 in product(range(-2, 3), repeat=4):
        for vals in ((2, 7, -1, 11), (-3, 0, 4, 1), (0, 0, 0, 0)):
            z0, z1, z2, z12 = vals
            t = q0+q1+q2+q12
            lhs = q0*z0+q1*z1+q2*z2+q12*z12
            rhs = (t*z0+(q1+q12)*(z1-z0)+(q2+q12)*(z2-z0)
                   +q12*(z12-z1-z2+z0))
            assert lhs == rhs
            cases += 1
    counts["four_corner_telescope_cases"] = cases

    cases = 0
    for cutoff in (2, 3, 7, 13):
        def envelope(v):
            dist = min(frac(v), 1-frac(v))
            return min(F(1), 1/(cutoff*dist)) if dist else F(1)
        for tnum in range(-40, 41):
            t = F(tnum, 31)
            for delta in (-F(1, 2*cutoff), F(0), F(1, 2*cutoff)):
                assert envelope(t+delta) <= 2*envelope(t)
                cases += 1
    counts["positive_envelope_stability_cases"] = cases

    # Moving centers are substituted as values after frozen differentiation.
    cprime = F(3, 4)*F(9, 8)
    bcenter = 2*cprime
    assert bcenter == F(27, 16)
    sum_centers = 2*bcenter
    wave_curvature = F(3, 2)*F(3, 4)*F(-1, 4)*3
    anchor_curvature = F(-243, 128)
    combined = anchor_curvature+wave_curvature*sum_centers
    assert wave_curvature == F(-27, 32)
    assert sum_centers == F(27, 8)
    assert combined == F(-1215, 256)
    assert F(3, 4)*9 == F(27, 4)
    for k, h1, h2 in product(range(1, 9), repeat=3):
        assert h1+h2 <= 2*h1*h2 <= 2*k*h1*h2
    counts["moving_curvature_and_product_controls"] = 517

    budgets = {
        "shift_product": F(1, 48)+F(1, 24),
        "weighted_shift_product": F(1, 24)+F(1, 48)+F(1, 24),
        "first_master_term": F(5, 48)+F(1, 8),
        "carry_cutoff_error": 1-F(1, 24),
        "small_shift_positive_modes": F(7, 8)+F(1, 48),
        "D_value_approximation": F(1, 24)-F(1, 4),
        "D_error_times_cutoff": F(1, 24)+F(1, 24)-F(1, 4),
        "D_zero_inverse_slope_error": F(3, 4)-F(1, 24),
        "D_zero_lattice_cost": F(1, 16)+F(1, 4),
        "D_nonzero_lattice_cost": F(3, 4),
        "center_window_count": F(1, 24)+F(1, 24)+F(1, 8),
        "center_window_density": F(1, 24)+F(1, 24)-F(7, 8),
        "widened_product_used": F(5, 48)+F(1, 8),
        "wave_twist_third": F(1, 24)-F(9, 8),
        "wave_anchor_center_count": F(1, 24)+F(3, 8),
        "wave_anchor_center_density": F(1, 24)-F(5, 8),
        "original_gap_density": F(1, 24)-F(1, 2),
        "bounded_zero_anchor_coefficient": F(5, 48)-F(1, 8),
        "bounded_zero_low_wave_coefficient": F(1, 24)+F(1, 24)-F(1, 4),
        "zero_low_wave_to_anchor": F(1, 24)-F(1, 8),
        "anchor_to_nonzero_integer_mode": F(5, 48)-F(1, 8),
        "zero_mode_length": F(5, 96)+F(11, 16),
        "zero_mode_boundaries": F(13, 24)+F(5, 16),
        "nonzero_mode_length": F(5, 32)+F(3, 4),
        "nonzero_mode_boundaries": F(13, 24)+F(1, 4),
        "first_floor_fourier_errors": F(5, 6),
    }
    assert budgets["shift_product"] == F(1, 16)
    assert budgets["weighted_shift_product"] == F(5, 48)
    assert budgets["widened_product_used"] < F(1, 2)
    assert budgets["wave_twist_third"] == F(-13, 12)
    assert budgets["center_window_density"] <= F(-11, 24)
    assert budgets["wave_anchor_center_density"] <= F(-11, 24)
    assert budgets["bounded_zero_anchor_coefficient"] == F(-1, 48)
    assert budgets["anchor_to_nonzero_integer_mode"] == F(-1, 48)
    assert budgets["zero_low_wave_to_anchor"] == F(-1, 12)
    assert budgets["D_error_times_cutoff"] < 0
    zero_cost = max(budgets[k] for k in (
        "zero_mode_length", "zero_mode_boundaries",
        "nonzero_mode_length", "nonzero_mode_boundaries",
        "first_floor_fourier_errors"))
    assert zero_cost == F(29, 32)
    t2 = max(F(23, 24), F(31, 32), zero_cost)
    assert t2 == F(31, 32)
    t1_diagonal, kernel_diagonal = 2-F(1, 24), 2-F(1, 48)
    t1 = max(t1_diagonal, 1+t2)/2
    kernel = max(kernel_diagonal, 1+t1)/2
    assert t1_diagonal == F(47, 24)
    assert t1 == F(63, 64)
    assert kernel_diagonal == F(95, 48)
    assert kernel == F(127, 128)
    assert kernel > F(95, 96)  # A weaker result; the older target stays open.
    counts["rational_exponent_controls"] = len(budgets)+8
    return {
        "status": "PASS", "counts": counts,
        "moving_center_curvature_coefficient": str(combined),
        "exponent_budgets": {k: str(v) for k, v in budgets.items()},
        "zero_offset_specialization": str(zero_cost),
        "doubly_differenced_exponent": str(t2),
        "singly_differenced_exponent": str(t1),
        "dyadic_kernel_exponent": str(kernel),
        "historical_95_over_96_target": "UNPROVED",
        "oooee_and_decorated_transfer": "UNPROVED",
        "scope": "Finite exact algebra and exponent controls, not an analytic proof.",
        "independent_mathematical_review": False,
    }


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    data = json.dumps(validate(), indent=2)+"\n"
    if args.output:
        args.output.write_text(data, encoding="utf-8")
    print(data, end="")

