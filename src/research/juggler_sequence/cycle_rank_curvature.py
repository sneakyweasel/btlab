"""Outward interval control for one fixed rank tuple, never a cycle search.

The real-grid extension retains only the nonnegative total-defect relaxation.
The branch's later valuation/counting kernels are in CubicRemainderVariation.lean,
CubicConstraintFusion.lean, CubicCriticalLocation.lean and CriticalCostKernel.lean.
The certificate-to-gap wrapper is CubicRemainderAssembly.lean.
This interval probe does not establish their actual-cycle hypotheses.
"""
from __future__ import annotations

import argparse
import json
from decimal import Decimal, localcontext, ROUND_FLOOR, ROUND_CEILING
from fractions import Fraction
from functools import lru_cache
from math import isqrt
from research.juggler_sequence.lean_paths import DATA_ROOT

import mpmath
from mpmath.ctx_iv import MPIntervalContext

L, ODD_COUNT, EVEN_COUNT, M = 780239, 492276, 287963, 350000001
PRECISION = 120
FIRST_ODD = 350009697
SECOND_ODDS = (350019393, 350019395)
CAP_BLOCK_SIZE = 32
CAP_PRECISION = 70
CAP_K, CAP_H = 478245, 176251
KNOWN_MINIMUM_CUTOFF = 520000000


def dyadic(raw):
    sign, mantissa, exponent, _ = (int(part) for part in raw)
    value = Fraction(-mantissa if sign else mantissa)
    return value*2**exponent if exponent >= 0 else value/Fraction(2**(-exponent))


def bounds(value):
    return tuple(dyadic(raw) for raw in value._mpi_)


def decimal_bound(value, rounding):
    with localcontext() as context:
        context.prec = 40
        context.rounding = rounding
        return str(Decimal(value.numerator)/Decimal(value.denominator))


def enclosure(value):
    lower, upper = bounds(value)
    assert lower <= upper
    return {
        "lower": {"numerator": str(lower.numerator), "denominator": str(lower.denominator)},
        "upper": {"numerator": str(upper.numerator), "denominator": str(upper.denominator)},
        "decimal_lower": decimal_bound(lower, ROUND_FLOOR),
        "decimal_upper": decimal_bound(upper, ROUND_CEILING),
        "width_upper": decimal_bound(upper-lower, ROUND_CEILING),
    }


def positive(value):
    return bounds(value)[0] > 0


def less(left, right):
    return bounds(left)[1] < bounds(right)[0]


def intersect(left, right):
    a, b = bounds(left)
    c, d = bounds(right)
    return max(a, c) <= min(b, d)


def known_minimum_upper_cutoff() -> dict:
    """One numerical consequence of the existing absolute-cell bound, not a new theorem."""
    iv = MPIntervalContext()
    iv.dps = PRECISION
    I = iv.mpf
    T = iv.log(I(3))
    surplus = ODD_COUNT*T-L*iv.log(I(2))
    omega = (L-1)*surplus/L
    A = iv.log(I(KNOWN_MINIMUM_CUTOFF))*iv.exp(-omega)
    bound = iv.exp(-A)/A*(1+L/(T*(A+1)))
    clearance = surplus-bound
    assert bounds(clearance)[0] > 0
    return {
        "minimum_cutoff": KNOWN_MINIMUM_CUTOFF,
        "count_tuple": {"L": L, "o": ODD_COUNT, "e": EVEN_COUNT},
        "existing_bound_reference": "docs/problems/juggler_cycle_absolute_cells.md, Result 1, equation (1)",
        "A": enclosure(A), "existing_geometric_envelope": enclosure(bound),
        "surplus_minus_existing_envelope": enclosure(clearance),
        "envelope_strictly_below_surplus": True,
        "decreasing_bound_excludes_larger_minima_for_fixed_counts": True,
        "new_general_theorem_or_descent_floor": False,
        "minimum_sweep": False,
    }


def floor_sum(n, modulus, multiplier, offset):
    """Integer floor sum for n>=0, modulus>0; signed coefficients are allowed."""
    if any(not isinstance(value, int) or isinstance(value, bool)
           for value in (n, modulus, multiplier, offset)):
        raise ValueError("floor-sum arguments must be integers")
    if n < 0 or modulus <= 0:
        raise ValueError("floor sum requires n>=0 and modulus>0")
    multiplier_quotient, multiplier = divmod(multiplier, modulus)
    offset_quotient, offset = divmod(offset, modulus)
    result = multiplier_quotient*n*(n-1)//2+offset_quotient*n
    while True:
        if multiplier >= modulus:
            result += (n-1)*n*(multiplier//modulus)//2
            multiplier %= modulus
        if offset >= modulus:
            result += n*(offset//modulus)
            offset %= modulus
        top = multiplier*n+offset
        if top < modulus:
            return result
        n, offset = top//modulus, top % modulus
        modulus, multiplier = multiplier, modulus


def below_count(n, threshold):
    """Count target ranks j<n with (CAP_K*j mod L)<threshold."""
    if threshold <= 0:
        return 0
    if threshold >= L:
        return n
    return n-floor_sum(n, L, CAP_K, L-threshold)+floor_sum(n, L, CAP_K, 0)


def group_prefix_counts(n):
    # A source at chronological time t has target phase t+1, not t.
    zero = below_count(n, 1)
    through_h = below_count(n, CAP_H+1)
    through_k = below_count(n, CAP_K+1)
    p, q = through_h-zero, through_k-through_h
    return p, q, n-p-q


def full_capacity_envelopes() -> dict:
    """Bound all three fixed lower-envelope cap sums without actual-state enumeration."""
    iv = MPIntervalContext()
    iv.dps = CAP_PRECISION
    I = iv.mpf
    T, a = iv.log(I(3)), iv.log(I(M))
    lam = ODD_COUNT*T-L*iv.log(I(2))
    alpha = T/L
    omega = (L-1)*lam/L
    assert CAP_K*EVEN_COUNT % L == 1 and CAP_H == 2*CAP_K-L
    assert group_prefix_counts(L) == (CAP_H, CAP_K-CAP_H, L-CAP_K)

    @lru_cache(maxsize=None)
    def cap(rank):
        grid_log = a*iv.exp(rank*alpha-omega)
        packing = M+2*rank if rank < ODD_COUNT else M*M+1+2*(rank-ODD_COUNT)
        packing_log = iv.log(I(packing))
        if grid_log.a > packing_log.b:
            lower_log = grid_log
        elif packing_log.a > grid_log.b:
            lower_log = packing_log
        else:
            lower_log = I([max(grid_log.a, packing_log.a), max(grid_log.b, packing_log.b)])
        # eta(exp(b))=log(1+log(1+exp(-b))/b); no large subtraction.
        return iv.log(1+iv.log(1+iv.exp(-lower_log))/lower_log)

    sums = [I(0), I(0), I(0)]
    group_counts = [0, 0, 0]
    blocks = 0
    previous_counts = (0, 0, 0)
    previous_end = 0
    # Splitting at the odd/even cutoff avoids hiding its packing jump.
    for start, stop in ((0, ODD_COUNT), (ODD_COUNT, L)):
        assert previous_end == start
        for left in range(start, stop, CAP_BLOCK_SIZE):
            right = min(left+CAP_BLOCK_SIZE, stop)
            current_counts = group_prefix_counts(right)
            counts = [new-old for new, old in zip(current_counts, previous_counts)]
            assert all(n >= 0 for n in counts) and sum(counts) == right-left
            low, high = cap(right-1), cap(left)
            assert low.a <= high.b
            block_weight = I([low.a, high.b])
            for g, count in enumerate(counts):
                sums[g] += count*block_weight
                group_counts[g] += count
            previous_counts = current_counts
            previous_end = right
            blocks += 1
    assert previous_end == L and group_counts == [CAP_H, CAP_K-CAP_H, L-CAP_K]
    total = sum(sums, I(0))
    assert bounds(total)[1]-bounds(total)[0] < Fraction(1, 10**8)

    def minimum(x, y):
        return I([min(x.a, y.a), min(x.b, y.b)])

    def maximum(x, y):
        return I([max(x.a, y.a), max(x.b, y.b)])

    cp, cq, cr = sums
    lower = maximum(I(0), lam-cr-cp)-minimum(lam, cr)
    upper = minimum(lam, cq)-maximum(I(0), lam-cq-cp)
    assert total.a > lam.b
    y = 350009697
    H0 = iv.log(iv.log(I(2*y-M))*a/(iv.log(I(y))**2))
    H2 = iv.log(iv.log(I(2*y-M+2))*a/(iv.log(I(y))**2))
    assert lower.b < H0.a < H0.b < 0 < H2.a < H2.b < upper.a

    controls = []
    for c2 in (350019393, 350019395):
        w1 = iv.log(iv.log(I(y))/a)-alpha
        w2 = iv.log(iv.log(I(c2))/a)-2*alpha
        masses = [CAP_H*lam/L-w2, (CAP_K-CAP_H)*lam/L+w2-w1, (L-CAP_K)*lam/L+w1]
        slack = [capacity-mass for capacity, mass in zip(sums, masses)]
        assert all(mass.a > 0 and room.a > 0 for mass, room in zip(masses, slack))
        controls.append({"c1": y, "c2": c2, "curvature": c2-2*y+M,
                         "masses": {g: enclosure(z) for g, z in zip(("P", "Q", "R"), masses)},
                         "capacity_slacks": {g: enclosure(z) for g, z in zip(("P", "Q", "R"), slack)},
                         "aggregate_envelope_box_feasible": True,
                         "actual_cell_feasibility_asserted": False})

    # This is an UPPER estimate for how much these old compulsory lower
    # charges can alter the result, never a lower charge evaluated at M.
    old_charge_ceiling = L*iv.log(iv.log(I(M*M+1))/iv.log(I(M*M)))
    parity_cap_shave_ceiling = I(L)/(I(M*M)*a)
    twice_combined_ceiling = 2*(old_charge_ceiling+parity_cap_shave_ceiling)
    assert lower.b+twice_combined_ceiling.b < H0.a
    assert upper.a-twice_combined_ceiling.b > H2.b
    return {
        "scope": "fixed L,o,e; universal target upper caps from actual m>=M; not an admissible minimum claim",
        "tuple": {"L": L, "o": ODD_COUNT, "e": EVEN_COUNT, "m_lower": M, "k": CAP_K, "h": CAP_H},
        "method": {"backend": "mpmath.iv", "decimal_precision": CAP_PRECISION,
                   "block_size": CAP_BLOCK_SIZE, "blocks": blocks,
                   "envelope_points": cap.cache_info().currsize,
                   "exact_counts": "Euclidean modular floor sums; target phase=t+1",
                   "total_width_target": "1e-8", "actual_state_or_trajectory_enumeration": False,
                   "minimum_sweep": False, "lower_faces_for_universal_test": 0},
        "group_cardinalities": dict(zip(("P", "Q", "R"), group_counts)),
        "surplus": enclosure(lam),
        "capacities": {g: enclosure(z) for g, z in zip(("P", "Q", "R"), sums)},
        "total_capacity": enclosure(total), "total_minus_surplus": enclosure(total-lam),
        "RC9_lower_endpoint": enclosure(lower), "RC9_upper_endpoint": enclosure(upper),
        "curvature_window": {"H0": enclosure(H0), "H2": enclosure(H2)},
        "RC9_lower_to_H0_clearance": enclosure(H0-lower),
        "H2_to_RC9_upper_clearance": enclosure(upper-H2),
        "integer_controls": controls,
        "old_compulsory_charge_total_ceiling": enclosure(old_charge_ceiling),
        "twice_old_charge_ceiling": enclosure(2*old_charge_ceiling),
        "parity_cap_shave_total_ceiling": enclosure(parity_cap_shave_ceiling),
        "twice_combined_refinement_ceiling": enclosure(twice_combined_ceiling),
        "refined_lower_to_H0_clearance": enclosure(H0-lower-twice_combined_ceiling),
        "H2_to_refined_upper_clearance": enclosure(upper-H2-twice_combined_ceiling),
        "independent_parity_upper_faces_do_not_change_window_comparison": True,
        "no_curvature_exclusion_from_these_envelopes": True,
        "actual_caps_or_full_integer_cycle_feasible": False,
        "new_minimum_or_period_floor": False,
        "known_minimum_upper_cutoff": known_minimum_upper_cutoff(),
        "scope_flags": {
            "envelope_box_only": True,
            "all_actual_caps_satisfied": False,
            "full_potential_and_sortedness_simultaneously_asserted": False,
            "positive_lower_faces_evaluated_at_lower_minimum": False,
            "new_total_capacity_theorem": False,
        },
    }



def report() -> dict:
    """Compute the single fixed report without writing any files."""
    iv = MPIntervalContext()
    iv.dps = PRECISION
    I = iv.mpf
    k = pow(EVEN_COUNT, -1, L)
    h = 2*k-L
    assert L == ODD_COUNT+EVEN_COUNT and (k*EVEN_COUNT) % L == 1
    assert 0 < h < k < L
    T, log_two, log_m = iv.log(I(3)), iv.log(I(2)), iv.log(I(M))
    surplus = ODD_COUNT*T-L*log_two
    alpha, mean = T/L, surplus/L
    omega = (L-1)*surplus/L
    ideal = {i: iv.exp(log_m*iv.exp(i*alpha)) for i in (1, 2)}
    curvature = ideal[2]-2*ideal[1]+M
    eta_m = iv.log(iv.log(I(M+1))/log_m)
    eta_square = iv.log(iv.log(I(M*M+1))/iv.log(I(M*M)))
    actual_O = isqrt(M**3)
    defect_zero = iv.log((I(3)/2)*log_m/iv.log(I(actual_O)))
    assert actual_O % 2 == 0 and positive(defect_zero)
    assert positive(surplus) and positive(curvature) and less(curvature, I(2))
    assert bounds(curvature)[1]-bounds(curvature)[0] < Fraction(1, 10**100)
    assert less(I(FIRST_ODD-1), ideal[1]) and less(ideal[1], I(FIRST_ODD+1))

    positions = {}
    for i in (1, 2):
        low = iv.exp(log_m*iv.exp(i*alpha-omega))
        high = iv.exp(log_m*iv.exp(i*alpha+omega))
        positions[str(i)] = {
            "ideal": enclosure(ideal[i]), "lower_position": enclosure(low),
            "upper_position": enclosure(high),
            "downward_allowance": enclosure(ideal[i]-low),
            "upward_allowance": enclosure(high-ideal[i]),
        }

    y = FIRST_ODD
    H0 = iv.log(iv.log(I(2*y-M))*log_m/(iv.log(I(y))**2))
    H2 = iv.log(iv.log(I(2*y-M+2))*log_m/(iv.log(I(y))**2))
    window_width = iv.log(iv.log(I(2*y-M+2))/iv.log(I(2*y-M)))
    controls = []
    for c2 in SECOND_ODDS:
        w1 = iv.log(iv.log(I(y))/log_m)-alpha
        w2 = iv.log(iv.log(I(c2))/log_m)-2*alpha
        p = h*surplus/L-w2
        q = (k-h)*surplus/L+w2-w1
        r = (L-k)*surplus/L+w1
        chi = w2-2*w1
        expected_window = H0 if c2 == 2*y-M else H2
        assert intersect(chi, expected_window)
        assert all(positive(z) for z in (w1, w2-w1, p, q, r))
        assert positive(p-defect_zero) and positive(r-eta_square)
        assert less(w2, alpha-mean) and less(w2, omega)
        # A uniform group realization has 0<=W<=w2; these checks prove its
        # complete sorted rank order and cutoff without iterating any ranks.
        assert positive(alpha-w2)
        gap1, gap2 = y-M, c2-y
        assert gap1 >= 2 and gap2 >= 2 and gap1 % 2 == gap2 % 2 == 0
        D = c2-2*y+M
        assert D in (0, 2)
        controls.append({
            "c0": M, "c1": y, "c2": c2,
            "first_gap": gap1, "second_gap": gap2, "curvature": D,
            "w1": enclosure(w1), "w2": enclosure(w2), "chi": enclosure(chi),
            "group_masses": {name: enclosure(value) for name, value in (("p", p), ("q", q), ("r", r))},
            "p_minus_initial_defect": enclosure(p-defect_zero),
            "r_minus_terminal_lower_charge": enclosure(r-eta_square),
            "group_rates": {name: enclosure(value) for name, value in (
                ("p_per_edge", p/h), ("q_per_edge", q/(k-h)), ("r_per_edge", r/(L-k)))},
            "full_real_order_gap_lower": enclosure(alpha-w2),
            "cutoff_margin": enclosure(alpha-mean-w2),
            "window_identity_intervals_intersect": True,
            "nonnegative_total_defect_extension": True,
            "exact_initial_edge_realization_asserted": False,
            "all_integer_states_or_upper_unit_cells_asserted": False,
        })
    return {
        "scope": "one fixed formal rank-budget tuple; no actual cycle minimum claimed",
        "backend": {"name": "mpmath.iv", "version": mpmath.__version__, "decimal_precision": PRECISION,
                    "endpoint_storage": "exact outward binary endpoint converted to Fraction",
                    "formal_kernel_certificate": False},
        "full_capacity_envelopes": full_capacity_envelopes(),
        "tuple": {"L": L, "o": ODD_COUNT, "e": EVEN_COUNT, "m": M, "k": k, "h": h,
                  "group_lengths": [h, k-h, L-k]},
        "constants": {name: enclosure(value) for name, value in (
            ("log3", T), ("log2", log_two), ("log_m", log_m), ("surplus", surplus),
            ("alpha", alpha), ("mean_defect", mean), ("omega", omega),
            ("eta_m", eta_m), ("eta_m_square", eta_square))},
        "positions": positions, "ideal_curvature": enclosure(curvature),
        "positive_even_curvature_lower_bound": 2,
        "odd_spacing_alone_forces_positive_curvature": False,
        "curvature_windows": {"H0": enclosure(H0), "H2": enclosure(H2),
                              "H2_minus_H0": enclosure(window_width),
                              "minus_H0_over_eta_m": enclosure(-H0/eta_m)},
        "actual_minimum_edge": {"O_m": actual_O, "output_even": True,
                                "defect": enclosure(defect_zero),
                                "therefore_not_an_actual_cubic_cycle_minimum": True},
        "integer_controls": controls,
        "rank_source_or_orbit_census": False,
        "full_cycle_constraints_satisfied": False,
        "no_cycle_proved": False,
        "scope_flags": {
            "one_fixed_tuple": True, "only_first_three_integer_ranks": True,
            "nonnegative_total_defect_relaxation": True,
            "full_upper_unit_cells": False, "all_rank_parities": False,
            "all_rank_integrality": False, "actual_cycle": False,
            "new_floor_or_period_bound": False,
        },
    }


def main(argv: list[str] | None = None) -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--write", action="store_true", help="write the fixed interval control record")
    args = parser.parse_args(argv)
    data = report()
    if args.write:
        destination = DATA_ROOT / "cycle_rank_curvature" / "controls.json"
        destination.parent.mkdir(parents=True, exist_ok=True)
        destination.write_text(json.dumps(data, indent=2)+"\n", encoding="utf-8")
    print(json.dumps({
        "tuple": data["tuple"],
        "surplus": data["constants"]["surplus"]["decimal_lower"],
        "ideal_curvature": data["ideal_curvature"]["decimal_lower"],
        "curvature_width_upper": data["ideal_curvature"]["width_upper"],
        "integer_curvatures": [row["curvature"] for row in data["integer_controls"]],
        "full_capacity_total_width": data["full_capacity_envelopes"]["total_capacity"]["width_upper"],
        "record_written": args.write,
        "actual_cycle": False,
    }))


if __name__ == "__main__":
    main()
