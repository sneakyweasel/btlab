"""One fixed outward-interval replay; no full-cycle realization is tested."""
import json
from fractions import Fraction
from math import isqrt

import pytest

from research.juggler_sequence import cycle_rank_curvature as probe
from research.juggler_sequence.lean_paths import DATA_ROOT


def test_small_loss_square_started_returns():
    """Replay two fixed exact cells; the infinitude argument is analytic."""
    record = json.loads((DATA_ROOT / "cycle_rank_curvature" /
                         "small_loss_returns.json").read_text(encoding="utf-8"))
    assert len(record["controls"]) == 2
    for row in record["controls"]:
        t, denominator = row["t"], row["fractional_loss_denominator"]
        x, u, v, z = row["trace"]
        assert t % 2 == 1 and t >= 3 and denominator > 1
        assert x == t**2 and u == t**3
        assert [x % 2, u % 2, v % 2, z % 2] == [1, 1, 0, 1]
        assert isqrt(x**3) == u and isqrt(u**3) == v and isqrt(v) == z
        assert u*u == x**3
        assert v*v <= t**9 < (v+1)**2
        assert z**4 <= t**9 < (z+1)**4
        # Strict rational inequalities certify both smooth phase widths.
        assert denominator**2 * t**9 < (denominator*v+1)**2
        assert denominator**4 * t**9 < (denominator*z+1)**4
        # This also checks the actual final E loss directly.
        assert denominator**2 * v < (denominator*z+1)**2
        # The OOE block first returns to [x, O(x)) in its cubic band.
        assert x < z < u < x*x <= v < x**3


def test_remainder_variation_fixed_controls():
    """Replay integer thresholds and local donor obstruction, not a cycle."""
    record = json.loads((DATA_ROOT / "cycle_rank_curvature" /
                         "remainder_variation_controls.json").read_text(encoding="utf-8"))
    L = record["count_tuple"]["L"]
    H = record["maximum_gap_valuation"]
    assert record["upper_cube"] == record["strict_minimum_upper_bound"]**3
    assert record["upper_cube"] < record["strict_power_of_two_ceiling"] == 2**(H+1)
    T = record["minimum_nonzero_corrections"]
    S = record["minimum_three_block_deviations"]
    assert (H+1)*(T-1) < L <= (H+1)*T
    assert (H+1)*(3+2*(S-1)) < L <= (H+1)*(3+2*S)
    assert (T, S, record["minimum_total_excess_over_block_minima"]) == (8969, 4483, 2*S)
    for edge in record["parallel_oo_edges"]:
        x, y = edge["source"], edge["target"]
        assert x % 2 == y % 2 == 1 and isqrt(x**3) == y
        assert edge["lower_remainder"] == x**3-y*y
        assert edge["upper_complement"] == (y+1)**2-x**3
    assert [edge["upper_complement"] for edge in record["parallel_oo_edges"]] == [79, 687, 101]
    # The exact log bounds in Result 19's local control reduce to this comparison.
    assert Fraction(1, 3096)-Fraction(79, 1458000) > Fraction(1750, 16256875)
    assert record["whole_rise_paid_by_next_downcrossing"] is False
    control = record["generic_reset_bound_sharp_control"]
    levels, resets = control["levels"], control["reset_indices"]
    assert all(levels[(i+1) % len(levels)] < levels[i]
               for i in range(len(levels)) if i not in resets)
    assert len(levels) == (max(levels)+1)*len(resets)
    # Without nonincrease off resets, exceptional positions could replenish potential.
    control = record["omitted_exception_monotonicity_countercontrol"]
    levels, exceptions, resets = (control["levels"], control["exception_indices"],
                                  control["reset_indices"])
    assert all(levels[(i+1) % len(levels)] < levels[i]
               for i in range(len(levels)) if i not in exceptions and i not in resets)
    assert len(levels) > len(exceptions)+(max(levels)+1)*len(resets)


def test_constraint_fusion_integer_budget():
    """Replay the affine certificate and its adjacent threshold, with no cycle search."""
    row = json.loads((DATA_ROOT / "cycle_rank_curvature" /
                     "constraint_fusion_controls.json").read_text(encoding="utf-8"))
    L, e = row["counts"]["L"], row["counts"]["e"]
    N = row["counts"]["even_gap_population"]
    assert N == L-2
    maximum_m = row["budget"]["maximum_odd_minimum"]
    G = int(row["budget"]["gap_sum_upper"])
    assert maximum_m % 2 == 1 and G == maximum_m**3-maximum_m
    allowance = row["budget"]["odd_gap_lower_sum"]
    assert allowance == 4

    def cost(n):
        return sum(2**(d+1+max(d-1, 0)*e//L) for d in range(n))

    certificate = row["affine_certificate"]
    q = certificate["q"]
    f, f_next = cost(q), cost(q+1)
    assert (f, f_next) == (int(certificate["F53"]), int(certificate["F54"]))
    D, B = int(certificate["Dq"]), int(certificate["Bq"])
    assert D == f_next-f == 2**73 and B == q*D-f > 0
    numerator = allowance+N*D-G
    assert numerator == int(certificate["numerator"])
    C = (numerator+B-1)//B
    assert C == certificate["critical_lower"] == 14569
    for control in row["itinerary_controls"]:
        count = control["C"]
        q, r = divmod(N, count)
        required = allowance+(count-r)*cost(q)+r*cost(q+1)
        assert (q, r) == (control["q"], control["r"])
        assert required == int(control["minimum_gap_sum"])
        assert required-G == int(control["minimum_minus_budget"])
        assert (required > G) == control["exceeds_budget"]
    for control in row["elementary_controls"]:
        K = control["K"]
        q, r = divmod(N, K)
        required = allowance+2*((K+r)*2**q-K)
        assert required == int(control["minimum_gap_sum"])
        assert (required > G) == control["exceeds_budget"]
        assert control["T"] == K+2
    hierarchy = row["hierarchy"]
    S = (C-1+1)//2
    assert (C, C+2, S, 2*S) == (hierarchy["critical_lower"],
        hierarchy["reset_lower"], hierarchy["deviation_lower"], hierarchy["raw_excess_lower"])
    assert (hierarchy["old_deviation_lower"],
            hierarchy["elementary_run_deviation_lower"], S) == (4483, 5390, 7284)
    assert not any(row[key] for key in ("actual_cycle_constructed",
        "minimum_or_period_exclusion", "all_block_phases_claimed_realizable",
        "controls_are_cycle_witnesses"))


def test_constraint_fusion_critical_filter_and_rotation_counts():
    """Nonzero does not imply critical; the itinerary count uses orbit order."""
    row = json.loads((DATA_ROOT / "cycle_rank_curvature" /
                     "constraint_fusion_controls.json").read_text(encoding="utf-8"))

    def valuation(n):
        n = abs(n)
        assert n > 0
        return (n & -n).bit_length()-1

    for control in row["valuation_controls"]:
        n, b, gap, following = (control[key] for key in ("N", "B", "gap", "next_gap"))
        correction = n*gap-b*following
        assert correction == control["correction"]
        critical = correction != 0 and valuation(correction) == valuation(gap)
        assert critical == control["critical"]
        if not critical:
            assert valuation(gap) >= valuation(b)+valuation(following)
    assert any(c["correction"] != 0 and not c["critical"]
               for c in row["valuation_controls"])
    assert any(c["critical"] and c["next_gap"] >= c["gap"]
               for c in row["valuation_controls"])
    # Finite symbolic rotations, not actual Juggler state lists.
    for length, even_count in ((11, 4), (19, 7)):
        for start in (0, length//2, length-1):
            for steps in (0, 1, 3, length):
                visits = sum((start+j*even_count) % length >= length-even_count
                             for j in range(steps))
                assert visits == (start+steps*even_count)//length
                assert visits in (steps*even_count//length,
                                  (steps*even_count+length-1)//length)
    # The extra denominator cost requires a gap divisible by four.
    assert (6-2) % 4 == (6+2) % 4 == 0
    assert (4-2) % 4 != 0 and (4+2) % 4 != 0


def test_critical_location_scalar_caps():
    """Replay only the fixed final envelopes; no actual-cycle realization is tested."""
    import json
    from fractions import Fraction
    from mpmath.ctx_iv import MPIntervalContext

    row = json.loads((DATA_ROOT / "cycle_rank_curvature" /
                      "critical_location_controls.json").read_text(encoding="utf-8"))

    def bounds(item):
        lo, hi = (Fraction(int(item[k][0]), int(item[k][1])) for k in ("lower", "upper"))
        assert lo <= hi
        assert Fraction(item["decimal_lower"]) <= lo <= hi <= Fraction(item["decimal_upper"])
        assert all(x.denominator & (x.denominator-1) == 0 for x in (lo, hi))
        return lo, hi

    def replay(item, value):
        lo, hi = bounds(item)
        exact = []
        for raw in value._mpi_:
            sign, mantissa, exponent, _ = map(int, raw)
            exact.append(Fraction((-1 if sign else 1)*mantissa)*Fraction(2)**exponent)
        assert lo <= exact[0] <= exact[1] <= hi

    assert row["counts"] == {"length": 780239, "odd": 492276, "even": 287963}
    L, o, m = 780239, 492276, 519999999
    assert row["minimum_upper"] == m
    iv = MPIntervalContext()
    iv.dps = 100
    I = iv.mpf
    log3, log2 = iv.log(I(3)), iv.log(I(2))
    surplus = o*log3-L*log2
    alpha, omega = log3/L, (L-1)*surplus/L
    gamma = alpha+omega
    for key, value in (("surplus", surplus), ("alpha", alpha), ("omega", omega), ("gamma", gamma)):
        replay(row[key], value)
    assert bounds(row["surplus"])[0] > 0
    assert bounds(row["surplus"])[1] < Fraction(7, 2000000)
    assert bounds(row["alpha"])[1] < Fraction(3, 2000000)
    assert bounds(row["gamma"])[1] < Fraction(1, 200000)
    assert set(row["rank_envelope_bins"]) == {"204313", "83650"}
    for rank, power, height in ((204313, 26, 25), (83650, 20, 19)):
        item = row["rank_envelope_bins"][str(rank)]
        upper = iv.exp(iv.log(I(m))*iv.exp(rank*alpha+omega))
        replay(item["target_state_envelope"], upper)
        replay(item["gap_upper"], gamma*upper*iv.log(upper))
        assert bounds(item["gap_upper"])[1] < 2**power
        assert item["strict_power_of_two_upper"] == power
        assert item["valuation_upper"] == height == power-1
    assert row["scope"]["fixed_counts_and_two_rank_envelopes_only"]
    assert not row["scope"]["minimum_or_rank_or_state_scan"]
    assert not row["scope"]["actual_cycle_constructed"]
    assert row["scope"]["real_mean_value_and_actual_cycle_assembly_remain_written"]


def test_critical_location_counts_and_critical_control():
    """Check exact final cover arithmetic and one pre-existing parallel OO triple."""
    import json
    from fractions import Fraction
    from math import isqrt

    row = json.loads((DATA_ROOT / "cycle_rank_curvature" /
                      "critical_location_controls.json").read_text(encoding="utf-8"))
    L, e = row["counts"]["length"], row["counts"]["even"]
    a, b = L-2*e, 3*e-L
    phase = row["phase"]
    assert (a, b, e-a) == (204313, 83650, 83650)
    assert 2*e < L < 3*e  # The three inverse low-interval images cover all ranks.
    assert (phase["a"], phase["b"]) == (a, b)
    assert 20+18*e//L == 26 > phase["valuation_below_a"] == 25
    assert 16+14*e//L == 21 > phase["valuation_below_b"] == 19
    assert phase["small_low_maximum_suffix_nodes"] == 19
    assert phase["high_low_maximum_suffix_nodes"] == 2+15 == 17
    assert phase["maximum_even_block_length"] == 2+max(19, 17) == 21
    totals = row["count_consequences"]
    N, C, T, S = (totals[k] for k in
                  ("even_gap_population", "critical_lower", "nonzero_lower", "three_block_deviation_lower"))
    assert N == L-2 == 780237
    assert 21*(C-1) < N <= 21*C and C == 37155
    assert T == C+2 == 37157
    assert 1+2*(S-1) < C <= 1+2*S and S == 18577
    assert totals["raw_excess_over_type_minima_lower"] == 2*S == 37154
    loc = row["localized_pairs"]
    k, r, h = (loc[key] for key in ("inverse_even_count", "arc_length", "initial_arc_length"))
    assert (k, r, h) == (478245, 301994, 176251)
    assert k == pow(e, -1, L) and r == L-k and h == 2*k-L
    assert loc["Q"] == [h, k] and loc["R"] == [k, L]
    assert 0 < h < k < L and k-h == L-k == r
    assert (2*k) % L == h and (L-1+k) % L == k-1  # R+k is precisely Q.
    o = L-e
    ranks = [a-1, o-1, L-1]
    times = [(rank*k) % L for rank in ranks]
    assert loc["source_type_boundary_ranks"] == ranks
    assert loc["source_type_boundary_times"] == times == [r-2, r-1, r]
    assert h < r-2 < r < k  # Every type boundary is inside Q, outside R.
    count = loc["critical_pairs_lower"]
    assert loc["window_length"] == 21 and loc["disjoint_windows"] == count == 14380
    assert r == 21*count+loc["unused_tail"] and 0 <= loc["unused_tail"] == 14 < 21
    assert loc["deviations_in_Q_union_R_lower"] == count
    assert loc["absolute_raw_difference_lower"] == loc["raw_excess_in_Q_union_R_lower"] == 2*count == 28760
    control = row["critical_oo_control"]
    assert control["existing_parameter"] == 9
    sources, targets = control["sources"], control["targets"]
    assert sources == [77, 81, 85] and targets == [675, 729, 783]
    assert all(x % 2 == y % 2 == 1 and y*y <= x**3 < (y+1)**2
               and isqrt(x**3) == y for x, y in zip(sources, targets))
    rem = [x**3-y*y for x, y in zip(sources, targets)]
    comp = [(y+1)**2-x**3 for x, y in zip(sources, targets)]
    assert rem == control["remainders"] == [908, 0, 1036]
    assert comp == control["upper_complements"] == [443, 1459, 531]
    for j, sign in ((0, -1), (1, 1)):
        pair = control["pairs"][j]
        gap, change = sources[j+1]-sources[j], rem[j+1]-rem[j]
        assert gap == pair["source_gap"] == 4
        assert targets[j+1]-targets[j] == pair["target_gap"] == 54
        assert change == pair["correction"] == (-908 if j == 0 else 1036)
        assert ((gap & -gap).bit_length()-1) == pair["source_gap_valuation"] == 2
        magnitude = abs(change)
        assert ((magnitude & -magnitude).bit_length()-1) == pair["correction_valuation"] == 2
        assert pair["critical"] and pair["sign"] == sign
    # Integrating Z' gives the following rational bounds, all with factor 1/log(2).
    # The central slack is eta(729); outer upper bounds use their exact complements.
    assert 730 < 2**10 and 2**18 < 77**3 and 2**19 < 85**3
    rational = control["normalized_sign_rational_control"]
    lower = Fraction(*rational["center_slack_lower_coefficient"])
    outer = [Fraction(*parts) for parts in rational["outer_slack_upper_coefficients"]]
    assert lower == Fraction(1, 7300)
    assert outer == [Fraction(443, 77**3*18), Fraction(531, 85**3*19)]
    assert all(upper < lower for upper in outer)
    assert row["scope"]["critical_oo_control_is_parallel_edges_only"]
    assert not row["scope"]["whole_cycle_signed_orientation_proved"]


def test_equal_gap_oo_triple_identities():
    """Replay the Result 15 integer family at the t=9 control, not a cycle."""
    from math import gcd
    t = 9
    xm, x0, xp = t**2 - 4, t**2, t**2 + 4
    ym, y0, yp = t**3 - 6 * t, t**3, t**3 + 6 * t
    assert all(n % 2 == 1 for n in (xm, x0, xp, ym, y0, yp))
    assert isqrt(xm**3) == ym and isqrt(x0**3) == y0 and isqrt(xp**3) == yp
    assert xm**3 == ym**2 + (12 * t**2 - 64)
    assert x0**3 == y0**2
    assert xp**3 == yp**2 + (12 * t**2 + 64)
    assert (ym + 1)**2 == xm**3 + (2 * t**3 - 12 * t**2 - 12 * t + 65)
    assert (y0 + 1)**2 == x0**3 + (2 * t**3 + 1)
    assert (yp + 1)**2 == xp**3 + (2 * t**3 - 12 * t**2 + 12 * t - 63)
    assert x0 - xm == xp - x0 == 4
    assert y0 - ym == yp - y0 == 6 * t
    assert gcd(4, 6 * t) == 2
    assert 0 < 12 * t**2 + 12 * t - 64
    assert 0 < 12 * t**2 - 12 * t + 64
    assert (12 * t**2 + 12 * t - 64) + (2 * t**3 - 12 * t**2 - 12 * t + 65) == 2 * t**3 + 1
    assert (12 * t**2 - 12 * t + 64) + (2 * t**3 - 12 * t**2 + 12 * t - 63) == 2 * t**3 + 1


def test_critical_cost_actual_pairs():
    """Exact cells, critical cosets and guarded returns at the prescribed controls only."""
    from math import gcd, comb
    data = json.loads((DATA_ROOT / "cycle_rank_curvature" /
                       "critical_cost_controls.json").read_text(encoding="utf-8"))
    families, windows = data["families"], data["windows"]

    def v2(n):
        assert n != 0
        n = abs(n)
        return (n & -n).bit_length()-1

    def paired(x, xp, y, yp, exponent):
        assert 0 < x < xp and 0 < y < yp and exponent in (1, 3)
        assert x % 2 == xp % 2 == int(exponent == 3) and y % 2 == yp % 2
        assert y*y <= x**exponent < (y+1)**2 and yp*yp <= xp**exponent < (yp+1)**2
        d, D = xp-x, yp-y
        N, B = (1 if exponent == 1 else x*x+x*xp+xp*xp), y+yp
        r = (xp**exponent-yp*yp)-(x**exponent-y*y)
        h, w = v2(d), v2(B)+v2(D)
        assert N % 2 == 1 and r == N*d-B*D
        assert (r != 0 and v2(r) == h) == (h < w)
        assert (r-d) % (2*gcd(d, D)) == 0
        assert (r-d+(0 if y % 2 else 2*D)) % 8 == 0
        if h < w:
            assert (r//2**h-N*(d//2**h)) % 2**(w-h) == 0
            assert (r//2**h-N*(d//2**h)+2**(w-h)) % 2**(w-h+1) == 0
        return d, D, r, h, w

    assert [(r["s"], r["a"]) for r in families["fixed_controls"]] == [(3, 1), (8, 1), (4, 3)]
    for row in families["fixed_controls"]:
        s, a = row["s"], row["a"]
        x, xp = row["sources"]; y, yp = row["O_images"]
        assert [x, xp, y, yp] == [4*s*s-a, 4*s*s+a, 8*s**3-3*s*a, 8*s**3+3*s*a]
        d, D, r, h, w = paired(x, xp, y, yp, 3)
        rem = [x**3-y*y, xp**3-yp*yp]
        assert rem == row["remainders"] == [3*s*s*a*a-a**3, 3*s*s*a*a+a**3]
        assert row["upper_margins"] == [(y+1)**2-x**3, (yp+1)**2-xp**3]
        assert (d, D, r, h) == (row["source_gap"], row["target_gap"], row["critical_correction"], 1)
        assert row["source_gap_valuation"] == h
        assert r == 2*a**3 and h < w and row["target_gap_valuation"] == v2(D)
        assert row["height_restoration"] == v2(D)-h
        outputs = None if y % 2 else [isqrt(y), isqrt(yp)]
        assert outputs == row["actual_E_images_when_guarded"]
        compatible = outputs is not None and outputs[0] < outputs[1] and all(z % 2 for z in outputs)
        assert row["two_distinct_odd_E_returns"] == compatible
        if compatible:
            t, q = outputs
            paired(y, yp, t, q, 1)
            assert D >= q*q-(t+1)**2+3 >= 2*t+6
            assert 3*a*a > 2*s and 27*r*r > 32*s**3
            assert all(Fraction(R, 2*z+1) > Fraction(1, 23) for R, z in zip(rem, [y, yp]))
    positive = windows["compatible_symmetric_OE_control"]
    rows = windows["actual_OO_controls"]+windows["symmetric_OE_controls"]+[positive["O_pair"], positive["E_pair"]]
    for row in rows:
        d, D, r, h, w = paired(*row["states"], row["exponent"])
        assert (d, D, r, h, w) == tuple(row[k] for k in
            ("source_gap", "target_gap", "correction", "source_height", "target_product_height"))
        assert row["critical"] == (h < w)
    assert [r["E_outputs"] for r in windows["symmetric_OE_controls"]] == [[7, 8], [41, 41]]
    for row in windows["symmetric_OE_controls"]:
        assert row["E_outputs"] == [isqrt(z) for z in row["states"][2:]]
        assert not (row["E_outputs"][0] < row["E_outputs"][1] and all(z % 2 for z in row["E_outputs"]))
    assert positive["O_pair"]["states"] == [61, 67, 476, 548]
    assert positive["E_pair"]["states"] == [476, 548, 21, 23]
    legacy = families["legacy_RC61_pair"]
    for row in legacy["blocks"]:
        b, x, y, z = (row[k] for k in ("b", "source", "middle", "return"))
        assert [x, y, z] == [b**4+2, b**6+3*b*b, b**3]
        assert [x % 2, y % 2, z % 2] == [1, 0, 1] and isqrt(x**3) == y and isqrt(y) == z
        assert [row["O_remainder"], row["E_remainder"]] == [x**3-y*y, y-z*z] == [3*b**4+8, 3*b*b]
        assert [row["O_upper_gap"], row["E_upper_gap"]] == [(y+1)**2-x**3, (z+1)**2-y]
        assert 27 <= x < 729 <= y < 19683 and 27 <= z < 729
    left, right = legacy["blocks"]
    d, D, r, h, w = paired(left["source"], right["source"], left["middle"], right["middle"], 3)
    _, D2, r2, h2, w2 = paired(left["middle"], right["middle"], left["return"], right["return"], 1)
    assert (d, D, D2, r, r2) == (544, 14944, 98, 1632, 48)
    assert tuple(legacy["pair"][key] for key in ("source_gap", "O_target_gap", "return_gap", "O_correction", "E_correction")) == (d, D, D2, r, r2)
    assert tuple(legacy["pair"][key] for key in ("source_gap_valuation", "O_target_gap_valuation", "O_correction_valuation")) == (h, v2(D), v2(r))
    assert legacy["common_band"] == {"m": 27, "cutoff": 729, "ceiling": 19683}
    assert legacy["pair"]["O_critical"] == (h < w) and legacy["pair"]["E_critical"] == (h2 < w2)
    assert not families["scope"]["uniform_all_OE_charge_claimed"]
    assert not legacy["scope"]["cycle_membership_or_adjacency_asserted"]
    adjacent = families["fixed_regime_RC61_adjacency_exclusion"]
    assert adjacent["minimum_upper"] < adjacent["c_strict_upper"]**2 == 23000**2
    assert Fraction(*adjacent["gamma_strict_upper"]) == Fraction(1, 200000)
    assert adjacent["log_source_strict_upper"]*adjacent["adjacent_gap_ratio_denominator"] == 41*4800 < 200000
    assert adjacent["c_five_exact_gap"]*4800 > adjacent["c_five_upper_source"] == 627
    coefficients = [comb(4, j)*(7**(4-j)-5**(4-j))-(5*comb(3, j)*7**(3-j) if j <= 3 else 0) for j in range(5)]
    assert coefficients == adjacent["c_ge_seven_shifted_excess_coefficients_ascending"]+[0] == [61, 137, 39, 3, 0]
    assert adjacent["excludes_adjacent_source_ranks_only"] and adjacent["general_proof_is_written"]


def test_critical_cost_window_projection():
    """A shared mod-4 witness and three finite clause cases, not a full cell solution."""
    row = json.loads((DATA_ROOT / "cycle_rank_curvature" /
                      "critical_cost_controls.json").read_text(encoding="utf-8"))["windows"]
    L, o, e = 780239, 492276, 287963
    residue = lambda i: (1+2*i) % 4 if i < o else 2*(i-o) % 4
    for i in (0, 1, o-e, o-e+1, o-2, o, L-2):
        j, jp = (i+e) % L, (i+1+e) % L
        assert (residue(i+1)-residue(i)) % 4 == 2
        assert (residue(jp)**2-residue(j)**2) % 4 == 0  # h=1<w in the same four residues.
    audit = row["saved_domain_audit"]
    assert not audit["full_arrays_saved"] and audit["sample_count"] == 8
    assert audit["minimum_width"] == 169999990 > 2
    assert len(audit["sample_residue_support"]) == 8
    for item in audit["sample_residue_support"]:
        i, lo, hi, value = (item[k] for k in ("rank", "lower", "upper", "first_member"))
        assert value == lo+(residue(i)-lo) % 4 and lo <= value <= hi
        assert value % 4 == item["residue"] == residue(i)
        assert value % 2 == int(i < o) and hi-lo >= audit["minimum_width"]
        for phase in (0, 2):
            representative = lo+(residue(i)+phase-lo) % 4
            assert lo <= representative <= hi
    # These are clause specifications, not a duplicate propagation implementation.
    all_true = [True]*21
    assert any(all_true) and all(all_true)
    unit_domains = [{False}]*20+[{False, True}]
    assert [i for i, domain in enumerate(unit_domains) if True in domain] == [20]
    assert not any([False]*21) and any([False]*20+[True])
    assert all(row["boolean_controls"][key] for key in
               ("all_unknown_21_window_unchanged", "twenty_false_forces_remaining_true", "all_false_window_rejected"))
    assert row["scope"]["no_new_full_sweeps"] and row["scope"]["no_minimum_subdivision"]
    assert not row["scope"]["actual_domain_pruning_claimed"] and not row["scope"]["full_rank_domains_reconstructed"]
    assert row["scope"]["residue_pattern_is_not_a_full_cell_solution"] and row["scope"]["open_controls_are_not_cycles"]


@pytest.fixture(scope="module")
def fixed_report(tmp_path_factory):
    destination = tmp_path_factory.mktemp("curvature_purity") / "data"
    with pytest.MonkeyPatch.context() as patch:
        patch.setattr(probe, "DATA_ROOT", destination)
        result = probe.report()
        assert not destination.exists()
    return result


def rational(record):
    return Fraction(int(record["numerator"]), int(record["denominator"]))


def interval(record):
    return rational(record["lower"]), rational(record["upper"])


def intersects(left, right):
    a, b = left
    c, d = right
    return max(a, c) <= min(b, d)


def enclosures(value):
    if isinstance(value, dict):
        if "lower" in value and "upper" in value:
            yield value
        else:
            for item in value.values():
                yield from enclosures(item)
    elif isinstance(value, list):
        for item in value:
            yield from enclosures(item)


def test_exact_fixed_tuple_and_group_lengths(fixed_report):
    data = fixed_report["tuple"]
    assert data == {"L": 780239, "o": 492276, "e": 287963, "m": 350000001,
                    "k": 478245, "h": 176251, "group_lengths": [176251, 301994, 301994]}
    assert data["o"]+data["e"] == data["L"]
    assert data["e"]*data["k"] % data["L"] == 1
    assert data["h"] == 2*data["k"]-data["L"]
    assert sum(data["group_lengths"]) == data["L"]
    assert set(fixed_report["positions"]) == {"1", "2"}
    assert len(fixed_report["integer_controls"]) == 2


def test_exact_dyadic_storage_and_outward_decimal_displays(fixed_report):
    assert probe.dyadic((0, 3, 2, 2)) == 12
    assert probe.dyadic((1, 3, -2, 2)) == Fraction(-3, 4)
    assert probe.dyadic((0, 0, 0, 0)) == 0
    records = list(enclosures(fixed_report))
    assert len(records) > 40
    for record in records:
        lower, upper = interval(record)
        assert lower <= upper
        for value in (lower, upper):
            denominator = value.denominator
            assert denominator > 0 and denominator & (denominator-1) == 0
        assert Fraction(record["decimal_lower"]) <= lower
        assert Fraction(record["decimal_upper"]) >= upper
        assert Fraction(record["width_upper"]) >= upper-lower
    assert json.loads(json.dumps(fixed_report)) == fixed_report


def test_certified_ideal_curvature_survives_cancellation(fixed_report):
    lower, upper = interval(fixed_report["ideal_curvature"])
    assert Fraction("0.2822331861938527805381902958134042098747") < lower
    assert upper < Fraction("0.2822331861938527805381902958134042098749")
    assert 0 < lower < upper < 2
    assert upper-lower < Fraction(1, 10**100)
    lam_low, lam_high = interval(fixed_report["constants"]["surplus"])
    assert Fraction("0.0000034711981668939710") < lam_low < lam_high
    assert lam_high < Fraction("0.0000034711981668939711")


def test_exact_odd_lattice_controls_and_nearest_first_rank(fixed_report):
    first_ideal = interval(fixed_report["positions"]["1"]["ideal"])
    assert [row["curvature"] for row in fixed_report["integer_controls"]] == [0, 2]
    for row, c2 in zip(fixed_report["integer_controls"], (350019393, 350019395)):
        m, c1 = row["c0"], row["c1"]
        assert (m, c1, row["c2"]) == (350000001, 350009697, c2)
        assert all(x % 2 == 1 for x in (m, c1, c2))
        assert c1-1 < first_ideal[0] < first_ideal[1] < c1+1
        assert row["first_gap"] == c1-m == 9696
        assert row["second_gap"] == c2-c1 >= 2
        assert row["second_gap"] % 2 == 0
        assert row["curvature"] == c2-2*c1+m
    assert fixed_report["positive_even_curvature_lower_bound"] == 2
    assert not fixed_report["odd_spacing_alone_forces_positive_curvature"]


def test_shared_mass_and_order_certificates_are_strict(fixed_report):
    constants = fixed_report["constants"]
    alpha = interval(constants["alpha"])
    mean = interval(constants["mean_defect"])
    omega = interval(constants["omega"])
    lam_low, lam_high = interval(constants["surplus"])
    for row in fixed_report["integer_controls"]:
        masses = [interval(row["group_masses"][name]) for name in ("p", "q", "r")]
        assert all(low > 0 for low, high in masses)
        assert sum(low for low, high in masses) <= lam_low <= lam_high
        assert lam_high <= sum(high for low, high in masses)
        for name, mass, length in zip(("p_per_edge", "q_per_edge", "r_per_edge"),
                                      masses, fixed_report["tuple"]["group_lengths"]):
            rate = interval(row["group_rates"][name])
            assert rate[0] > 0 and intersects((length*rate[0], length*rate[1]), mass)
        w1, w2 = interval(row["w1"]), interval(row["w2"])
        assert 0 < w1[0] <= w1[1] < w2[0] <= w2[1]
        assert w2[1] < alpha[0]-mean[1] and w2[1] < omega[0]
        for name in ("full_real_order_gap_lower", "cutoff_margin",
                     "p_minus_initial_defect", "r_minus_terminal_lower_charge"):
            assert interval(row[name])[0] > 0
        assert row["nonnegative_total_defect_extension"]
        assert not row["exact_initial_edge_realization_asserted"]


def test_curvature_windows_are_distinct_and_match_the_exact_controls(fixed_report):
    windows = fixed_report["curvature_windows"]
    H0, H2 = interval(windows["H0"]), interval(windows["H2"])
    assert H0[1] < 0 < H2[0]
    width = interval(windows["H2_minus_H0"])
    assert width[0] > 0 and intersects(width, (H2[0]-H0[1], H2[1]-H0[0]))
    for row, target in zip(fixed_report["integer_controls"], (H0, H2)):
        w1, w2, chi = interval(row["w1"]), interval(row["w2"]), interval(row["chi"])
        assert intersects(chi, (w2[0]-2*w1[1], w2[1]-2*w1[0]))
        assert intersects(chi, target)
        assert row["window_identity_intervals_intersect"]
    ratio = interval(windows["minus_H0_over_eta_m"])
    assert Fraction("0.28224") < ratio[0] < ratio[1] < Fraction("0.28225")


def test_independent_grid_allowances_do_not_claim_shared_feasibility(fixed_report):
    for position in fixed_report["positions"].values():
        ideal = interval(position["ideal"])
        lower, upper = interval(position["lower_position"]), interval(position["upper_position"])
        assert lower[1] < ideal[0] <= ideal[1] < upper[0]
        for key in ("downward_allowance", "upward_allowance"):
            allowance = interval(position[key])
            assert 23900 < allowance[0] <= allowance[1] < 23905


def test_actual_minimum_guard_failure_is_exact(fixed_report):
    m = fixed_report["tuple"]["m"]
    edge = fixed_report["actual_minimum_edge"]
    image = edge["O_m"]
    assert image == 6547900454916 and image % 2 == 0 and m % 2 == 1
    assert image*image <= m*m*m < (image+1)*(image+1)
    assert edge["output_even"] and edge["therefore_not_an_actual_cubic_cycle_minimum"]
    assert interval(edge["defect"])[0] > 0


def test_scope_excludes_full_integer_cycle_claims(fixed_report):
    assert fixed_report["backend"]["name"] == "mpmath.iv"
    assert fixed_report["backend"]["decimal_precision"] == 120
    assert not fixed_report["backend"]["formal_kernel_certificate"]
    flags = fixed_report["scope_flags"]
    assert flags["one_fixed_tuple"] and flags["only_first_three_integer_ranks"]
    assert flags["nonnegative_total_defect_relaxation"]
    assert not any(flags[name] for name in ("full_upper_unit_cells", "all_rank_parities",
                                          "all_rank_integrality", "actual_cycle", "new_floor_or_period_bound"))
    assert not fixed_report["rank_source_or_orbit_census"]
    assert not fixed_report["full_cycle_constraints_satisfied"]
    assert not fixed_report["no_cycle_proved"]


def test_signed_floor_sums_match_small_exact_controls():
    # These small arithmetic cases validate the counting algorithm, not any orbit.
    for n, modulus in ((0, 1), (1, 2), (7, 5), (19, 11)):
        for multiplier, offset in ((0, 0), (3, 2), (-7, 4), (9, -13), (-9, -13)):
            expected = sum((multiplier*j+offset)//modulus for j in range(n))
            assert probe.floor_sum(n, modulus, multiplier, offset) == expected
    for args in ((-1, 3, 2, 1), (3, 0, 2, 1), (3, -1, 2, 1),
                 (3, 2, 1.5, 0), (True, 2, 1, 0)):
        with pytest.raises(ValueError):
            probe.floor_sum(*args)


def test_group_counts_use_target_phase_and_exact_full_cardinalities():
    for n in (0, 1, 2, 3, 17, 64, 137):
        phases = [(probe.CAP_K*j) % probe.L for j in range(n)]
        expected = (sum(1 <= phase <= probe.CAP_H for phase in phases),
                    sum(probe.CAP_H < phase <= probe.CAP_K for phase in phases),
                    sum(phase == 0 or phase > probe.CAP_K for phase in phases))
        assert probe.group_prefix_counts(n) == expected
        for threshold in (0, 1, probe.CAP_H, probe.CAP_H+1, probe.CAP_K+1, probe.L):
            assert probe.below_count(n, threshold) == sum(p < threshold for p in phases)
    assert probe.group_prefix_counts(1) == (0, 0, 1)
    assert probe.group_prefix_counts(2) == (0, 1, 1)
    assert probe.group_prefix_counts(3) == (1, 1, 1)
    assert probe.group_prefix_counts(probe.L) == (176251, 301994, 301994)


def test_full_capacity_enclosures_and_darboux_error(fixed_report):
    cap = fixed_report["full_capacity_envelopes"]
    assert cap["tuple"] == {"L": 780239, "o": 492276, "e": 287963,
                            "m_lower": 350000001, "k": 478245, "h": 176251}
    assert cap["group_cardinalities"] == {"P": 176251, "Q": 301994, "R": 301994}
    assert cap["method"]["blocks"] == 24383
    assert cap["method"]["envelope_points"] == 48766
    assert cap["method"]["block_size"] == 32
    assert cap["method"]["decimal_precision"] == 70
    capacities = [interval(cap["capacities"][g]) for g in ("P", "Q", "R")]
    for endpoints, expected_lower, expected_upper in zip(
            capacities, ("1.0788e-6", "1.8484e-6", "1.8485e-6"),
            ("1.0799e-6", "1.8503e-6", "1.8503e-6")):
        assert Fraction(expected_lower) < endpoints[0] <= endpoints[1] < Fraction(expected_upper)
    total = interval(cap["total_capacity"])
    assert intersects(total, (sum(x[0] for x in capacities), sum(x[1] for x in capacities)))
    assert Fraction("4.7758e-6") < total[0] < total[1] < Fraction("4.7804e-6")
    assert 0 < total[1]-total[0] < Fraction("4.503e-9") < Fraction("1e-8")
    assert interval(cap["total_minus_surplus"])[0] > Fraction("1.3e-6")


def test_full_capacity_RC9_window_and_aggregate_controls(fixed_report):
    cap = fixed_report["full_capacity_envelopes"]
    lower, upper = interval(cap["RC9_lower_endpoint"]), interval(cap["RC9_upper_endpoint"])
    H0, H2 = (interval(cap["curvature_window"][key]) for key in ("H0", "H2"))
    assert lower[1] < Fraction("-1.3e-6") < H0[0]
    assert H2[1] < Fraction("1.3e-6") < upper[0]
    for key in ("RC9_lower_to_H0_clearance", "H2_to_RC9_upper_clearance"):
        assert interval(cap[key])[0] > Fraction("1.3e-6")
    assert [row["curvature"] for row in cap["integer_controls"]] == [0, 2]
    for row, old in zip(cap["integer_controls"], fixed_report["integer_controls"]):
        assert row["c1"] == old["c1"] and row["c2"] == old["c2"]
        for key in ("P", "Q", "R"):
            assert interval(row["capacity_slacks"][key])[0] > 0
            assert intersects(interval(row["masses"][key]), interval(old["group_masses"][key.lower()]))
        assert row["aggregate_envelope_box_feasible"]
        assert not row["actual_cell_feasibility_asserted"]


def test_lower_charge_and_parity_upper_face_robustness(fixed_report):
    cap = fixed_report["full_capacity_envelopes"]
    old = interval(cap["old_compulsory_charge_total_ceiling"])
    shave = interval(cap["parity_cap_shave_total_ceiling"])
    combined = interval(cap["twice_combined_refinement_ceiling"])
    assert Fraction("1.6187e-13") < old[0] < old[1] < Fraction("1.6188e-13")
    assert Fraction("3.2375e-13") < shave[0] < shave[1] < Fraction("3.2376e-13")
    assert intersects(combined, (2*(old[0]+shave[0]), 2*(old[1]+shave[1])))
    assert 0 < combined[0] < combined[1] < Fraction("9.713e-13")
    for key in ("refined_lower_to_H0_clearance", "H2_to_refined_upper_clearance"):
        assert interval(cap[key])[0] > Fraction("1.3e-6")
    assert cap["independent_parity_upper_faces_do_not_change_window_comparison"]


def test_existing_absolute_cell_cutoff_and_capacity_scope(fixed_report):
    cap = fixed_report["full_capacity_envelopes"]
    cutoff = cap["known_minimum_upper_cutoff"]
    assert cutoff["minimum_cutoff"] == 520000000
    assert cutoff["existing_bound_reference"] == (
        "docs/problems/juggler_cycle_absolute_cells.md, Result 1, equation (1)")
    low, high = interval(cutoff["existing_geometric_envelope"])
    assert Fraction("3.2302932149555275e-6") < low < high < Fraction("3.2302932149555276e-6")
    assert interval(cutoff["surplus_minus_existing_envelope"])[0] > Fraction("2.4e-7")
    assert cutoff["envelope_strictly_below_surplus"]
    assert cutoff["decreasing_bound_excludes_larger_minima_for_fixed_counts"]
    assert not cutoff["new_general_theorem_or_descent_floor"] and not cutoff["minimum_sweep"]
    flags = cap["scope_flags"]
    assert flags["envelope_box_only"]
    assert not any(flags[key] for key in ("all_actual_caps_satisfied",
        "full_potential_and_sortedness_simultaneously_asserted",
        "positive_lower_faces_evaluated_at_lower_minimum", "new_total_capacity_theorem"))
    assert cap["method"]["lower_faces_for_universal_test"] == 0
    assert not cap["method"]["actual_state_or_trajectory_enumeration"]
    assert not cap["actual_caps_or_full_integer_cycle_feasible"]
    assert "elapsed_seconds" not in json.dumps(fixed_report)


def test_cli_is_read_only_unless_write_is_requested(fixed_report, tmp_path, monkeypatch, capsys):
    destination = tmp_path / "data"
    monkeypatch.setattr(probe, "DATA_ROOT", destination)
    monkeypatch.setattr(probe, "report", lambda: fixed_report)
    probe.main([])
    status = json.loads(capsys.readouterr().out)
    assert status["record_written"] is False and not destination.exists()
    assert status["integer_curvatures"] == [0, 2]
    probe.main(["--write"])
    status = json.loads(capsys.readouterr().out)
    assert status["record_written"] is True and not status["actual_cycle"]
    written = destination / "cycle_rank_curvature" / "controls.json"
    assert json.loads(written.read_text(encoding="utf-8")) == fixed_report


def test_ooe_rank_cost_packing():
    """Finite square packing from existing dyadics; no rerun of an interval probe."""
    data = json.loads((DATA_ROOT / "cycle_rank_curvature" /
                       "ooe_rank_cost_controls.json").read_text(encoding="utf-8"))["packing"]
    certificate = json.loads((DATA_ROOT / "cycle_rank_curvature" /
                              "critical_location_controls.json").read_text(encoding="utf-8"))
    assert data["source_certificate"] == "cycle_rank_curvature/critical_location_controls.json"
    L, o, e, a, b = (data["counts"][k] for k in ("L", "o", "e", "OOE_starts", "OE_starts"))
    assert (L, o, e, a, b) == (780239, 492276, 287963, 204313, 83650)
    assert a == o-e == L-2*e and b == 3*e-L and a+b == e
    assert 3*a+2*b == L and 2*a+b == o and 2*b < a
    lower, upper_minimum = data["minimum_interval"]
    assert (lower, upper_minimum) == (350000001, 519999999)
    first = data["first_odd_square_parameter"]
    assert first % 2 == 1 and (first-2)**2 < lower <= first**2
    assert first == isqrt(lower-1)+1 == 18709
    assert [row["rank_prefix_length"] for row in data["rank_controls"]] == [a, b]
    for row in data["rank_controls"]:
        rank = row["rank_prefix_length"]
        saved = certificate["rank_envelope_bins"][str(rank)]["target_state_envelope"]["upper"]
        assert row["state_upper_dyadic"] == saved
        cap = Fraction(*map(int, saved))
        root = row["last_integer_square_root"]
        assert root**2 <= cap < (root+1)**2
        last = row["last_odd_parameter"]
        assert last % 2 == 1 and last**2 <= cap < (last+2)**2
        assert last == root-(root-1) % 2
        count = (last-first)//2+1
        assert first+2*(count-1) == last and first+2*count > last
        assert row["odd_square_capacity"] == count
        assert row["positive_first_O_remainders_lower"] == max(0, rank-count)
    small = data["rank_controls"][1]
    assert (small["last_odd_parameter"], small["odd_square_capacity"]) == (79939, 30616)
    positive = small["positive_first_O_remainders_lower"]
    assert positive == b-30616 == 53034
    charge = data["first_loss_charge"]
    Y = charge["target_ceiling"]
    assert Fraction(*map(int, small["state_upper_dyadic"])) < 80000**2
    assert Y == 80000**3 == 512000000000000 and Y < 2**49
    assert Fraction(98*7, 10) < 69
    assert charge["positive_remainder_count"] == positive
    assert charge["raw_remainder_sum_lower"] == 2*positive == 106068
    bound = Fraction(*map(int, charge["strict_rational_lower"]))
    assert bound == Fraction(2*positive, 69*Y*Y) and 0 < bound < Fraction(1, 10**26)
    assert charge["surplus_lower_dyadic"] == certificate["surplus"]["lower"]
    assert Fraction(*map(int, charge["surplus_lower_dyadic"])) > Fraction(3, 10**6)
    assert data["scope"]["existing_enclosures_only"] and data["scope"]["exact_first_O_loss_only"]
    assert not any(data["scope"][key] for key in ("new_interval_evaluation", "rank_or_parameter_scan",
                   "type_minimum_deviation_count_claimed", "positive_return_E_cost_claimed", "cycle_excluded"))


def test_ooe_rank_cost_pairs():
    """Eight prescribed open pairs: exact cells, guards, and phase brackets."""
    report = json.loads((DATA_ROOT / "cycle_rank_curvature" /
                         "ooe_rank_cost_controls.json").read_text(encoding="utf-8"))
    pairs = report["pairs"]
    expected = [9355, 9999, 10001, 11111, 15587, 19999, 22221, 27501]
    assert pairs["parameters"] == expected
    assert [row["s"] for row in pairs["controls"]] == expected
    successes = []
    fixed_window_successes = []
    for row in pairs["controls"]:
        s = row["s"]
        assert s % 2 == 1 and s >= 5
        traces = [branch["states"] for branch in row["branches"]]
        assert [trace[0] for trace in traces] == [4*s*s-1, 4*s*s+1]
        assert [trace[1] for trace in traces] == [8*s**3-3*s, 8*s**3+3*s]
        first_remainders = []
        guards = []
        for branch, phase in zip(row["branches"], row["phases"]):
            x, y, v, z = branch["states"]
            assert x % 2 == y % 2 == 1
            assert y == isqrt(x**3)
            assert v == isqrt(y**3)
            assert z == isqrt(v) == isqrt(isqrt(y**3))
            remainders = [x**3-y*y, y**3-v*v, v-z*z]
            margins = [(y+1)**2-x**3, (v+1)**2-y**3, (z+1)**2-v]
            assert branch["residuals"] == remainders
            assert all(r >= 0 for r in remainders)
            assert branch["upper_cell_margins"] == margins
            assert all(margin > 0 for margin in margins)
            assert branch["parities"] == [n % 2 for n in (x, y, v, z)]
            guarded = v % 2 == 0 and z % 2 == 1
            assert branch["complete_actual_OOE"] is guarded
            guards.append(guarded)
            first_remainders.append(remainders[0])
            for key, radicand, degree, whole in (
                ("A_fraction", y**3, 2, v),
                ("B_fraction", y**3, 4, z),
                ("actual_E_fraction", v, 2, z),
            ):
                bracket = phase[key]
                scale = bracket["denominator"]
                lower = whole*scale + bracket["lower_numerator"]
                upper = whole*scale + bracket["upper_numerator"]
                assert scale == 2**48 and lower + 1 == upper
                assert bracket["upper_strict"] is True
                assert lower**degree <= radicand*scale**degree < upper**degree
        assert first_remainders == [3*s*s-1, 3*s*s+1]
        assert first_remainders[1]-first_remainders[0] == 2
        # The correction and source gap both have 2-adic valuation exactly one.
        assert traces[1][0]-traces[0][0] == 2
        assert traces[1][1]-traces[0][1] == 6*s
        m, xplus = traces[0][0], traces[1][0]
        ymin, ymax = traces[0][1], traces[1][1]
        vmin, vmax = traces[0][2], traces[1][2]
        zmin, zmax = traces[0][3], traces[1][3]
        assert m < xplus < zmin < zmax < ymin < ymax < m*m <= vmin < vmax < m**3
        assert row["exact_common_cubic_order"] is True
        assert row["common_band_minimum"] == m
        in_window = 350000000 < m < 520000000
        assert row["minimum_in_fixed_window"] is in_window
        assert row["both_complete_actual_OOE"] is all(guards)
        assert Fraction(4, s*s) < Fraction(1, 780239)
        assert row["coarse_bound_below_one_over_L"] is True
        phase_box = row["phase_box_certificate_if_guarded"]
        if all(guards):
            successes.append(s)
            if in_window:
                fixed_window_successes.append(s)
            numerator, scale = phase_box["epsilon_numerator"], phase_box["denominator"]
            assert 0 < numerator < scale
            for trace in traces:
                _, y, v, z = trace
                # These strict integer comparisons certify the fixed phase box.
                assert (v*scale)**2 < y**3*scale**2 < (v*scale+numerator)**2
                assert (z*scale)**4 < y**3*scale**4 < (z*scale+numerator)**4
                assert (z*scale)**2 < v*scale**2 < (z*scale+numerator)**2
        else:
            assert phase_box is None
    assert successes == pairs["guard_success_parameters"] == [19999]
    assert fixed_window_successes == pairs["guard_success_in_fixed_minimum_window"] == []
    success = next(row for row in pairs["controls"] if row["s"] == 19999)
    assert success["common_band_minimum"] == 1599840003
