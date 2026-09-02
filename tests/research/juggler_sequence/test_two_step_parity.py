"""Multi-step word-parity census. Not a halt test, not a frequency theorem."""

from __future__ import annotations

from fractions import Fraction
from math import isqrt

from research.juggler_sequence.power_itineraries import floor_power
from research.juggler_sequence.two_step_parity import (
    ANTI_OVERCLAIM,
    CONTRACTING_TARGET,
    SCALE,
    WORDS4,
    block_kernel_sum_census,
    block_m_affine_model_check,
    block_v_amplified_model_check,
    branch_freeze_scan,
    carry_multiplier_probe,
    level3_block_model_check,
    pure_model_census,
    shift_average_probe,
    deep_word_counts,
    differenced_kernel_probe,
    dispersion_spacing_census,
    double_gap_identity_check,
    fourth_letter_scan,
    fourth_letter_smoothing_check,
    gap_decomposition_check,
    kernel_reformulation_scan,
    identity_error_scaled,
    identity_scan,
    itinerary_word,
    juggler_step,
    kernel_probe,
    increment_j_derivative_scan,
    increment_linearization_scan,
    level3_inner_linearization_scan,
    level3_kernel_probe,
    level3_raw_gap_wildness,
    level3_reformulation_scan,
    differenced_level3_kernel_probe,
    oooo_indicator_identity_check,
    x_cell_increment_scan,
    x1_landing_gap_scan,
    v2_amplitude_drift_scan,
    ooeooee_indicator_identity_check,
    oooeoee_indicator_identity_check,
    sixth_ooeoo_scan,
    sixth_oooeo_scan,
    x1_remainder_reduction_scan,
    v_level_cell_scan,
    w_gap_freeze_scan,
    w_carry_run_scan,
    lemma_a_prime_scan,
    lemma_m_scan,
    level2_gap_check,
    m12_scan,
    oeo_indicator_identity_check,
    oeo_mode_probe,
    oeo_smoothing_scan,
    oe_indicator_identity_check,
    ooee_indicator_identity_check,
    ooo_indicator_identity_check,
    oooee_indicator_identity_check,
    oooee_mode_probe,
    oooee_smoothing_scan,
    ooeoe_indicator_identity_check,
    ooeoe_mode_probe,
    ooeoe_smoothing_scan,
    scan,
    second_gap_collision_check,
    second_order_scan,
    transport_block_variance,
    word_counts,
)

# Exact depth-4 counts over odd n in [3, 10^5], pinned from the census.
PINNED_COUNTS_1E5 = {
    "OEEE": 6453,
    "OEEO": 6053,
    "OEOE": 6086,
    "OEOO": 6423,
    "OOEE": 6176,
    "OOEO": 6291,
    "OOOE": 6332,
    "OOOO": 6185,
}


def test_juggler_step_matches_floor_power():
    for n in (2, 3, 7, 9, 16, 365, 3889, 10_000):
        assert juggler_step(n) == floor_power(n)


def test_itinerary_words_small():
    # 3 -> 5 -> 11 -> 36: OOOE. 9 -> 27 -> 140 -> 11: OOEO.
    assert itinerary_word(3, 4) == "OOOE"
    assert itinerary_word(9, 4) == "OOEO"
    # 15 -> 58 -> 7 -> 18: OEOE.
    assert itinerary_word(15, 4) == "OEOE"
    assert all(itinerary_word(n, 4)[0] == "O" for n in range(3, 51, 2))


def test_words4_enumeration():
    assert len(WORDS4) == 8
    assert all(w[0] == "O" and len(w) == 4 for w in WORDS4)
    assert CONTRACTING_TARGET in WORDS4


def test_pinned_counts_at_1e5():
    assert word_counts(100_000) == PINNED_COUNTS_1E5
    assert sum(PINNED_COUNTS_1E5.values()) == 49_999


def test_scan_small_window_flat_and_descending():
    row = scan(100_000)
    assert row["final"]["counts4"] == PINNED_COUNTS_1E5
    # No linear bias: every depth-4 class within 5% of the product density.
    odds = row["final"]["odds"]
    for w in WORDS4:
        assert abs(row["final"]["counts4"][w] - odds / 8) < 0.05 * odds / 8
    # Every census OOEE start satisfied the four-step descent T^4(n) < n.
    assert row["ooee"]["descent_violations"] == 0
    # Envelope exponents on this window stay well below 1.
    for d in ("2", "3", "4"):
        assert row["fitted_exponent"][d] is not None
        assert row["fitted_exponent"][d] < 0.9


def test_ooee_is_contracting_word():
    # 3^oddCount < 2^length for OOEE: the formal power bound contracts.
    assert 3**2 < 2**4
    # Exact spot check of a realized OOEE start.
    for n in range(3, 20_001, 2):
        if itinerary_word(n, 4) == "OOEE":
            x = n
            for _ in range(4):
                x = juggler_step(x)
            assert x < n
            # Exact certificate shape: x^16 <= n^9 forces x < n for n >= 2.
            assert x**16 <= n**9


def test_anti_overclaim_flags():
    assert ANTI_OVERCLAIM["parity_frequency_theorem"] is False
    assert ANTI_OVERCLAIM["global_termination"] is False
    assert ANTI_OVERCLAIM["predictive_state_claim"] is False
    # Flipped by the Phase-2 review pass (J-nested-parity-discrepancy).
    assert ANTI_OVERCLAIM["depth2_analytic_lemma_proved"] is True
    # Flipped by the Phase-3 review pass (J-triple-parity-discrepancy).
    assert ANTI_OVERCLAIM["depth4_even_branch_proved"] is True
    # Flipped by the Phase-9 review pass (J-kernel-cancellation,
    # J-depth4-complete): the tier-2 kernel bound and the depth-4
    # completion are theorems. Density one stays unclaimed (depth >= 5
    # equidistribution is open).
    assert ANTI_OVERCLAIM["tier2_analytic_lemma_proved"] is True
    assert ANTI_OVERCLAIM["kernel_bound_proved"] is True
    assert ANTI_OVERCLAIM["depth4_complete_proved"] is True
    assert ANTI_OVERCLAIM["density_one_claimed"] is False
    # Phase 17: Phase-0 falsifiers for the post-BB theories did not
    # fire (OBSERVATION); no K3 bound and no density-one claim.
    assert ANTI_OVERCLAIM["dispersion_phase0_alive"] is True
    assert ANTI_OVERCLAIM["transport_phase0_alive"] is True
    # Phase 18: dispersion closed as a completion route; the transport
    # substrate is exact but Conjecture EE and the K3 bound stay open.
    assert ANTI_OVERCLAIM["dispersion_count_route_refuted"] is True
    assert ANTI_OVERCLAIM["transport_substrate_exact"] is True
    # Phase 19: level-3 block model exact; in-block cancellation at
    # the random-phase scale (OBSERVATION). EE and the bound open.
    assert ANTI_OVERCLAIM["level3_block_model_exact"] is True
    assert ANTI_OVERCLAIM["in_block_cancellation_observed"] is True
    # Phase 20: the intra-block harmonic program is parked
    # (Proposition GG); the pure model cancels empirically
    # (Conjecture HH census). EE, V and the bound stay open.
    assert ANTI_OVERCLAIM["intra_block_harmonic_parked"] is True
    assert ANTI_OVERCLAIM["pure_model_cancellation_observed"] is True
    # Phase 21: shift-average square-root cancellation proved
    # (Lemma II); de-randomization to lambda = 0 parked
    # (Proposition JJ). HH deterministic stays open.
    assert ANTI_OVERCLAIM["pure_model_shift_average_proved"] is True
    assert ANTI_OVERCLAIM["hh_derandomization_parked"] is True
    assert ANTI_OVERCLAIM["depth5_kernel_bound_proved"] is False
    # Phase 26: length-8 counting theorem withdrawn (|E|<1 without
    # E'). Contraction-algebra flag stays True.
    assert ANTI_OVERCLAIM["depth8_engine_quartet_proved"] is False
    assert ANTI_OVERCLAIM["depth8_chains_subcritical"] is True
    assert ANTI_OVERCLAIM["length8_remainder_discard_proved"] is True
    assert ANTI_OVERCLAIM["harvest_counting_terminal"] is True


def test_smooth_cancellation_constant():
    # |A1''| n^{7/4} / h^2 -> 81/256 = 0.31640625 (j = 1).
    from research.juggler_sequence.two_step_parity import (
        smooth_cancellation_check,
    )

    for n, h in ((10_001, 1), (100_001, 3), (1_000_001, 10)):
        ratio = smooth_cancellation_check(n, h)
        assert abs(ratio - 81 / 256) < 0.01


def test_isqrt_agreement_on_odd_branch():
    for n in range(3, 501, 2):
        assert juggler_step(n) == isqrt(n * n * n)


def test_lemma_a_identity_bounds():
    # Lemma A: m^{3/2} = (3/2) m n^{3/4} - (1/2) n^{9/4} + E(n),
    # 0 <= E(n) <= (1/2) n^{-3/4}, exact scaled-integer check.
    samples = tuple(range(3, 1001, 2)) + (10**6 + 1, 10**9 + 1)
    result = identity_scan(samples)
    assert result["holds"] is True
    # The supremum of E / bound is 3/4, attained as theta -> 1.
    assert result["worst_ratio"] < 0.7501


def test_lemma_a_single_value_shape():
    err, bound = identity_error_scaled(101)
    assert 0 <= err <= bound
    # bound*scale = scale^2 // (2 n^{3/4} scale) is positive and small.
    assert 0 < bound < SCALE


def test_lemma_b_gap_decomposition():
    # g(n) = floor(delta) + [ {n^{3/2}} >= 1 - {delta} ] exactly.
    for h in (1, 2):
        result = gap_decomposition_check(100_001, 400, h)
        assert result["holds"] is True
        assert result["matches"] >= 398


def test_lemma_d_fourth_letter_smoothing():
    # Lemma D: v^{1/2} = n^{9/8} + D(n), -(3/4) n^{-3/8} - n^{-9/8} <= D <= 0.
    samples = tuple(range(3, 1001, 2)) + (10**6 + 1, 10**9 + 1)
    result = fourth_letter_scan(samples)
    assert result["holds"] is True
    # The supremum of |D| / bound is 1, approached as theta -> 1.
    assert result["worst_ratio"] < 1.0


def test_lemma_d_single_value_shape():
    diff, bound = fourth_letter_smoothing_check(101)
    assert -bound <= diff <= 0
    assert 0 < bound < SCALE


def test_ooee_indicator_identity():
    # itinerary_word(n,4) == "OOEE" iff (psi1, psi2, psi3) = (-1,+1,+1):
    # the branch-consistency claim behind Corollary F.
    result = ooee_indicator_identity_check(5001)
    assert result["holds"] is True


def test_lemma_g_coefficient_identities():
    # Both Lemma G identities and the Proposition H polynomial recover
    # the nominal value at (m, v) = (X, X^{3/2}).
    from fractions import Fraction as F

    assert F(5, 32) + F(15, 16) - F(3, 32) == 1
    assert F(5, 32) - F(9, 16) + F(45, 32) == 1
    assert (
        -F(5, 64) + F(9, 32) - F(45, 64) + F(15, 64) + F(45, 32) - F(9, 64)
    ) == 1


def test_lemma_g_second_order_scan():
    # Second-order linearization bricks, exact at scale 10^60.
    samples = tuple(range(5, 501, 2)) + (10**6 + 1, 10**9 + 1)
    result = second_order_scan(samples)
    assert result["holds"] is True


def test_ooo_indicator_identity():
    # itinerary_word(n,4) == "OOOE" iff (psi1, psi2, psi4) = (-1,-1,+1):
    # the branch-consistency claim for the tier-2 target class.
    result = ooo_indicator_identity_check(5001)
    assert result["holds"] is True


def test_composed_cell_obstruction():
    # Negative knowledge: on Lemma-B cells the second-level gap g2
    # takes a new value at essentially every point, so the naive
    # two-level cell composition fails. Do not retry that route.
    result = second_gap_collision_check(10**6 + 1, 1500, 1)
    assert result["distinct_ratio"] >= 0.99


def test_proposition_l_m12_smoothing():
    # OE-branch third-letter brick: m^{1/2} = n^{3/4} + D1 with
    # -(1/2)n^{-3/4} - n^{-9/4} <= D1 <= 0, exact at scale 10^30.
    samples = tuple(range(3, 1001, 2)) + (10**6 + 1, 10**9 + 1, 10**12 + 1)
    assert m12_scan(samples)["holds"] is True


def test_oe_indicator_identity():
    # itinerary_word(n,3) == "OEE" iff m even and isqrt(m) even: the
    # branch-consistency claim behind Proposition L (depth-3 closure).
    assert oe_indicator_identity_check(5001)["holds"] is True


def test_lemma_m_second_order_forms():
    # Plain and shifted second-order forms with realized gaps G;
    # poly - lhs = -R with R the positive Taylor remainder.
    samples = tuple(range(5, 501, 2)) + (10**6 + 1, 10**9 + 1)
    for h in (1, 2):
        assert lemma_m_scan(samples, h=h)["holds"] is True


def test_lemma_n_level2_gap():
    # g2 = floor(DY) + [theta2 >= 1 - {DY}]: exact on orbit data,
    # guard-band skips only.
    result = level2_gap_check(10**6 + 1, 400, 1)
    assert result["holds"] is True
    assert result["matches"] >= 390


def test_kernel_probe_cancels():
    # Conjecture O support: the isolated tier-2 kernel exhibits strong
    # cancellation (far below the trivial bound; loose threshold).
    result = kernel_probe(10**4)
    assert result["abs_sum"] < 0.1 * result["count"]


def test_kernel_reformulation_identity():
    # Lemma R1: (1/2)(m^{9/4} - v^{3/2}) - (3/4) v^{1/2} theta_2 lies
    # in [0, (3/16) v^{-1/2}]; exact scaled integers through 10^12.
    samples = tuple(range(5, 1001, 2)) + (10**6 + 1, 10**9 + 1, 10**12 + 1)
    assert kernel_reformulation_scan(samples)["holds"] is True


def test_double_gap_identity():
    # Lemma R2: D2 g2 = floor(D2 D1 Y) + kappa'' + D2 kappa_2, exact
    # on orbit data (Lean: seq_floor_gap_second).
    for h1, h2 in ((1, 1), (1, 3), (2, 5)):
        result = double_gap_identity_check(10**6 + 1, 200, h1, h2)
        assert result["holds"] is True
        assert result["matches"] >= 190


def test_branch_freeze():
    # Lemma R3: per-branch floors of D2 D1 Y are frozen at the drift
    # scale; the j = 0 branch is constant across the whole cell.
    result = branch_freeze_scan(10**6, 1, 1, 400)
    assert result["in_cell"] >= 10
    assert result["branch_0"]["distinct"] == 1
    for j in (-1, 1):
        assert result[f"branch_{j}"]["distinct"] <= 5


def test_differenced_kernel_cancels():
    # Theorem R support: the once-, twice- and thrice-differenced kernel
    # sums cancel far below the trivial bound (loose threshold). The
    # third difference backs the targeted extra differencing of the
    # Phase-9 review repair.
    t1 = differenced_kernel_probe(10**4, 1)
    t2 = differenced_kernel_probe(10**4, 1, 2)
    t3 = differenced_kernel_probe(10**4, 1, 2, 3)
    assert t1["abs_sum"] < 0.1 * t1["count"]
    assert t2["abs_sum"] < 0.1 * t2["count"]
    assert t3["abs_sum"] < 0.1 * t3["count"]


def test_lemma_a_prime_w_level_linearization():
    # Theorem Q brick: w^{3/2} = -(1/2)m^{3/4} + (3/2)w m^{1/4} + E,
    # 0 <= E <= (3/8)(U-1)^{-1/2}, exact at scale 10^30.
    samples = tuple(range(5, 1001, 2)) + (10**6 + 1, 10**9 + 1, 10**12 + 1)
    assert lemma_a_prime_scan(samples)["holds"] is True


def test_oeo_smoothing_identity():
    # Full OEO* smoothing: w^{3/2} = n^{9/8} - (3/2) m^{1/4} theta_w
    # + d2 with the asymmetric decaying window.
    samples = tuple(range(5, 1001, 2)) + (10**6 + 1, 10**9 + 1, 10**12 + 1)
    assert oeo_smoothing_scan(samples)["holds"] is True


def test_oeo_indicator_identity():
    # All four OE** depth-4 words match the sign data (m even, parity
    # of w, parity of the branch-correct fourth value): the branch
    # consistency behind Theorem Q.
    result = oeo_indicator_identity_check(5001)
    assert result["holds"] is True
    assert result["checked"] > 1000


def test_oeo_mode_probe_cancels():
    # Theorem Q's mode sum cancels strongly (empirically ~P^{5/8},
    # the coherent w-cell random-walk scale; loose threshold).
    result = oeo_mode_probe(10**4)
    assert result["abs_sum"] < 0.1 * result["count"]


def test_oooee_smoothing_identity():
    samples = tuple(range(5, 1001, 2)) + (10**6 + 1, 10**9 + 1, 10**12 + 1)
    assert oooee_smoothing_scan(samples)["holds"] is True


def test_ooeoe_smoothing_identity():
    samples = tuple(range(5, 1001, 2)) + (10**6 + 1, 10**9 + 1, 10**12 + 1)
    assert ooeoe_smoothing_scan(samples)["holds"] is True


def test_oooee_indicator_identity():
    result = oooee_indicator_identity_check(5001)
    assert result["holds"] is True
    assert result["checked"] > 100


def test_ooeoe_indicator_identity():
    result = ooeoe_indicator_identity_check(5001)
    assert result["holds"] is True
    assert result["checked"] > 100


def test_oooee_mode_probe_cancels():
    result = oooee_mode_probe(10**4)
    assert result["count"] > 100
    assert result["abs_sum"] < 0.1 * result["count"]


def test_ooeoe_mode_probe_cancels():
    result = ooeoe_mode_probe(10**4)
    assert result["count"] > 100
    assert result["abs_sum"] < 0.1 * result["count"]


def test_depth5_contracting_words_near_product():
    counts = deep_word_counts(100_000, 5)
    odds = sum(counts.values())
    expected = odds / 16
    for w in ("OOOEE", "OOEOE", "OOOEO", "OOEOO"):
        assert abs(counts[w] - expected) < 80
    # Guard: every OOOEE / OOEOE start in the window descends in 5 steps.
    for n in range(3, 10_001, 2):
        w = itinerary_word(n, 5)
        if w in ("OOOEE", "OOEOE"):
            x = n
            for _ in range(5):
                x = juggler_step(x)
            assert x < n


def test_anti_overclaim_depth5_flag():
    assert ANTI_OVERCLAIM["depth5_contracting_proved"] is True
    assert ANTI_OVERCLAIM["depth5_kernel_isolated"] is True
    assert ANTI_OVERCLAIM["depth5_kernel_bound_proved"] is False
    assert ANTI_OVERCLAIM["scale_invariant_R_extension_refuted"] is True
    assert ANTI_OVERCLAIM["depth7_engine_contracting_proved"] is False
    assert ANTI_OVERCLAIM["w_family_alpha_33_32_proved"] is True
    assert ANTI_OVERCLAIM["length7_remainder_engine_proved"] is True
    assert ANTI_OVERCLAIM["length7_passenger_theorem_t_refuted"] is True
    assert ANTI_OVERCLAIM["length7_vdc3_chirps_proved"] is True
    assert ANTI_OVERCLAIM["length7_x3_qr3_carry_refuted"] is True
    assert ANTI_OVERCLAIM["length7_integer_w_engine_line_refuted"] is True
    assert ANTI_OVERCLAIM["length8_remainder_discard_proved"] is True
    assert ANTI_OVERCLAIM["harvest_counting_terminal"] is True
    assert ANTI_OVERCLAIM["increment_first_k3_refuted"] is True
    assert ANTI_OVERCLAIM["x1_absorption_k3_refuted"] is True
    assert ANTI_OVERCLAIM["k3_toolkit_parked"] is True
    assert ANTI_OVERCLAIM["density_one_claimed"] is False


def test_level3_reformulation_identity():
    # Lemma V1: (1/2)(v^{9/4} - z^{3/2}) - (3/4) z^{1/2} theta_3 lies
    # in [0, (3/16) z^{-1/2}]; exact scaled integers through 10^12.
    samples = tuple(range(5, 1001, 2)) + (10**6 + 1, 10**9 + 1, 10**12 + 1)
    assert level3_reformulation_scan(samples)["holds"] is True


def test_level3_kernel_probe_cancels():
    # Conjecture V support: the isolated level-3 kernel exhibits
    # square-root-scale cancellation (loose threshold).
    result = level3_kernel_probe(10**4)
    assert result["count"] > 1000
    assert result["abs_sum"] < 0.1 * result["count"]


def test_differenced_level3_kernel_cancels():
    t1 = differenced_level3_kernel_probe(10**4, 1)
    t2 = differenced_level3_kernel_probe(10**4, 1, 2)
    t3 = differenced_level3_kernel_probe(10**4, 1, 2, 3)
    assert t1["abs_sum"] < 0.1 * t1["count"]
    assert t2["abs_sum"] < 0.1 * t2["count"]
    assert t3["abs_sum"] < 0.1 * t3["count"]


def test_level3_raw_gap_is_wild():
    # Negative knowledge: raw Δ⁴ Z is not frozen. The smooth model
    # G^{(4)} ≪ 1 does not descend to the discrete nested floor.
    result = level3_raw_gap_wildness(10**4, 80)
    assert result["raw_d4_wild"] is True
    assert result["d3_above_smooth"] is True


def test_oooo_indicator_identity():
    result = oooo_indicator_identity_check(5001)
    assert result["holds"] is True
    assert result["checked"] > 100


def test_level3_inner_linearization_identity():
    # Lemma V2: v^{3/2} = m^{9/4} - (3/2) m^{3/4} theta_2 + E,
    # 0 <= E <= (3/8) v^{-1/2}; exact scaled integers through 10^12.
    samples = tuple(range(5, 1001, 2)) + (10**6 + 1, 10**9 + 1, 10**12 + 1)
    assert level3_inner_linearization_scan(samples)["holds"] is True


def test_v_level_has_no_cells():
    # Proposition W: floor(ΔY) and Δv have run length 1 — there are
    # no v-level b-runs, so Lemma R3 cannot be copied one layer up.
    for p in (10**4, 10**5, 10**6):
        result = v_level_cell_scan(p, 400)
        assert result["no_v_level_cells"] is True
        assert result["floor_dY_mean_run"] == 1.0
        assert result["dv_mean_run"] == 1.0


def test_increment_linearization_identity():
    # Lemma Z1: F_J(v) = F_J(Y) - F_J'(Y) theta_2 + R, remainder
    # one-signed in (3/8) v^{-1/2}; exact scaled integers through 10^12.
    samples = tuple(range(5, 1001, 2)) + (10**6 + 1, 10**9 + 1, 10**12 + 1)
    assert increment_linearization_scan(samples)["holds"] is True


def test_increment_j_derivative_is_forty_five_sixteenths():
    # Unfreezing J by 1 reproduces the Phase-12 leftover:
    # c (F_{J+1}-F_J) / ((9/8) n^{45/16}) -> 1.
    samples = (10**4 + 1, 10**6 + 1, 10**8 + 1, 10**10 + 1)
    result = increment_j_derivative_scan(samples)
    assert result["holds"] is True
    assert result["count"] == 4


def test_x_cells_have_no_j_runs():
    # Increment-first falsifier: on genuine floor(ΔX) b-runs, both
    # the raw increment and the κ-fixed branch increment of Y have
    # run length 1. X-cells do not create v-level J-runs.
    for p in (10**4, 10**5, 10**6):
        result = x_cell_increment_scan(p, 400)
        assert result["no_j_runs_on_x_cells"] is True
        assert result["floor_dY_mean_run"] == 1.0
        assert result["dv_mean_run"] == 1.0
        assert result["branch_j_max_run"] == 1
        assert result["b_run_max"] >= 2
        assert result["mean_abs_d_floor_dY"] > result["pred_P14"]


def test_v2_amplitude_jumps_each_step():
    # The V2 leftover coefficient C ≍ n^{45/16} has
    # C(n+2)-C(n) ~ (405/64) n^{29/16} >> 1. R's windows
    # cannot be quasi-static at this α.
    samples = (10**4 + 1, 10**6 + 1, 10**8 + 1)
    result = v2_amplitude_drift_scan(samples)
    assert result["holds"] is True
    assert result["count"] == 3


def test_x1_landing_gaps_split_slow_from_fast():
    # X1 lands on floor(F). Slow F (v^{1/2}, m^{1/2}) freeze;
    # Y and every tested v-hybrid have run length 1.
    for p in (10**4, 10**5, 10**6):
        result = x1_landing_gap_scan(p, 400)
        assert result["slow_floors_frozen"] is True
        assert result["y_and_hybrids_unfrozen"] is True
        assert result["floor_dY"]["max"] == 1.0
        assert result["dv"]["max"] == 1.0


def test_sixth_ooeoo_identity():
    samples = tuple(range(5, 1001, 2)) + (10**6 + 1, 10**9 + 1, 10**12 + 1)
    assert sixth_ooeoo_scan(samples)["holds"] is True


def test_sixth_oooeo_identity():
    samples = tuple(range(5, 1001, 2)) + (10**6 + 1, 10**9 + 1, 10**12 + 1)
    assert sixth_oooeo_scan(samples)["holds"] is True


def test_w_gap_freezes_on_ooeo():
    result = w_gap_freeze_scan(10**4, 400)
    assert result["frozen"] is True
    assert result["mean_run"] >= 8


def test_ooeooee_indicator_identity():
    result = ooeooee_indicator_identity_check(5001)
    assert result["holds"] is True
    assert result["checked"] > 50


def test_oooeoee_indicator_identity():
    result = oooeoee_indicator_identity_check(5001)
    assert result["holds"] is True
    assert result["checked"] > 50


def test_depth7_engine_contractors_descend():
    assert 3**4 < 2**7
    counts = deep_word_counts(20_000, 7)
    odds = sum(counts.values())
    expected = odds / 128
    for w in ("OOEOOEE", "OOOEOEE"):
        assert abs(counts[w] - expected) < 1.5 * (20_000 ** (2 / 3))
    for n in range(3, 10_001, 2):
        w = itinerary_word(n, 7)
        if w in ("OOEOOEE", "OOOEOEE"):
            x = n
            for _ in range(7):
                x = juggler_step(x)
            assert x < n


def test_depth6_census_minimal_scale_envelope():
    # All 32 depth-6 words realized; deviations obey the two-regime
    # envelope max((N/2) N^{-gamma_min}, N^{2/3}) with constant <= 1.5.
    n_max = 100_000
    counts = deep_word_counts(n_max, 6)
    assert len(counts) == 32
    odds = sum(counts.values())
    expected = odds / 32

    def gamma_min(word: str) -> float:
        g, gm = 1.0, float("inf")
        for ch in word:
            g *= 1.5 if ch == "O" else 0.5
            gm = min(gm, g)
        return gm

    for w, c in counts.items():
        envelope = max((n_max / 2) * n_max ** (-gamma_min(w)), n_max ** (2 / 3))
        assert abs(c - expected) <= 1.5 * envelope


def test_block_carry_models():
    # Lemma DD: on blocks of L = P^{1/4} odd steps, (i) m is affine in
    # the block position up to a bounded defect, and (ii) v is the
    # floor of the affine base's 3/2-power plus the W-amplified carry
    # sequence, up to a bounded defect. Exact scaled integers.
    a = block_m_affine_model_check(10**4, n_blocks=30)
    assert a["max_defect"] <= 2
    b = block_v_amplified_model_check(10**4, n_blocks=30)
    assert b["max_defect"] <= 1
    a6 = block_m_affine_model_check(10**6, n_blocks=10)
    assert a6["max_defect"] <= 2
    b6 = block_v_amplified_model_check(10**6, n_blocks=10)
    assert b6["max_defect"] <= 1


def test_level3_block_model():
    # Lemma FF: theta_3 and the kernel phase u on DD-blocks are
    # explicit polynomials in (mu, s, d, {F}) with errors below the
    # predicted scales P^{-19/16} and ~P^{-9/16}. The product form
    # u = (3/4) z^{1/2} theta_3 forces the theta_3 model to precision
    # P^{-27/16} (the z^{1/2} amplification).
    r4 = level3_block_model_check(10**4, n_blocks=10)
    assert r4["max_theta3_err"] < r4["theta3_scale"]
    assert r4["max_u_err"] < r4["u_scale"]
    r6 = level3_block_model_check(10**6, n_blocks=5)
    assert r6["max_theta3_err"] < r6["theta3_scale"]
    assert r6["max_u_err"] < r6["u_scale"]


def test_block_kernel_sum_census():
    # Census gate for Conjecture EE (OBSERVATION guard, loose): the
    # in-block kernel sums sit at the random-phase scale R ~ Exp(1).
    r = block_kernel_sum_census(10**4, n_blocks=60, ks=(1,))
    assert r["k=1"]["mean_R"] < 3.0


def test_pure_model_census():
    # Conjecture HH census (OBSERVATION guard, loose): the pure
    # amplitude-product model sums sit at the random-phase scale.
    r = pure_model_census(10**4, n_blocks=60, k=1)
    assert r["mean_R"] < 3.0


def test_shift_average_probe():
    # Lemma II validator: the shift-averaged mean square sits at the
    # random-phase scale (two-sided), and the lambda-stability
    # increments grow with delta (JJ (iii)).
    r = shift_average_probe(10**4, n_lambda=16, n_blocks=30)
    assert abs(r["mean_R_over_shifts"] - 1.0) < 0.2
    st = r["stability_increments"]
    assert st["m=0.1"] < st["m=10"]


def test_carry_multiplier_probe():
    # Transport pair-decay multiplier equidistributes (OBSERVATION
    # guard, loose threshold).
    r = carry_multiplier_probe(10**4, sample_cap=5000)
    assert r["mean_abs"] < 0.1


def test_dispersion_spacing_census():
    # Phase-17 falsifier (a): the dispersion amplitude u = (3/4) z^{1/2}
    # theta_3 mod 1 has near-Poissonian pair statistics at scale 1/J and
    # no short-lag rigidity. OBSERVATION guard, loose thresholds.
    r = dispersion_spacing_census(10**4, sample_cap=3000, j_scale=32)
    assert r["count"] == 3000
    assert 0.9 < r["coincidence_ratio"] < 1.1
    for val in r["lag_concentration"].values():
        assert val < 0.1


def test_depth8_quartet_census():
    # Theorem AA guard: the four contracting length-8 words appear at
    # the product density N_odd/128 within a loose envelope, and every
    # member satisfies the eight-step certificate J^8(n) < n.
    from research.juggler_sequence.two_step_parity import (
        depth8_quartet_census,
    )

    r = depth8_quartet_census(50000)
    assert r["descent_violations"] == 0
    assert r["max_abs_normalized_deviation"] < 4.0
    for w, c in r["counts"].items():
        assert c > 0, w


def test_depth8_chain_scan():
    # Lemma AA1 validator: the OOEOOEO eighth-letter composite chain
    # identity holds exactly with one-signed envelopes, and every
    # sawtooth coefficient is subcritical (exponent < 1).
    from research.juggler_sequence.two_step_parity import (
        depth8_chain_scan,
    )

    samples = tuple(range(51, 300, 2)) + (10**4 + 1, 10**6 + 1)
    r = depth8_chain_scan(samples)
    assert r["holds"] is True
    assert r["max_exponent"] < 1.0


def test_depth8_mode_probe():
    # Theorem AA mode gate: eighth-wave sums on the four parent
    # cylinders cancel well below cylinder size (OBSERVATION guard).
    from research.juggler_sequence.two_step_parity import (
        depth8_mode_probe,
    )

    r = depth8_mode_probe(50000, k=1)
    for w in ("OOEOOEO", "OOEOOOE", "OOOEOEO", "OOOEOOE"):
        assert r[w]["members"] > 0
        assert r[w]["ratio"] < 0.25


def test_master_identity():
    # Phase-25 gate: the master identity DD(c theta_2) = (DD c) theta_2
    # + (D2 c)({W}-k2) + (D1 c)({W'}-k2') + c11({DDY}-k''-D2 k2),
    # exact scaled integers (Paper B, Lemma 5.1(iv)).
    from research.juggler_sequence.two_step_parity import (
        master_identity_check,
    )

    for h1, h2 in ((1, 1), (2, 3), (5, 7)):
        result = master_identity_check(10**6 + 1, 200, h1, h2)
        assert result["holds"] is True
        assert result["matches"] >= 180


def test_kernel_margin_scan():
    # Phase-25 gates m1/m2: the differenced-kernel main curvature is the
    # 3:2 composite -(9/32) beta n^{-5/4}, and the window-centre
    # composite (945/512 - 27/64) k j n^{-1/8} is single-signed at
    # ratio 4.375 (Paper B, standing estimate E6 and Step 5a).
    from research.juggler_sequence.two_step_parity import (
        kernel_margin_scan,
    )

    r = kernel_margin_scan(10**8)
    assert 0.9 < r["m1"]["ratio"] < 1.1
    assert abs(r["m2"]["ratio"] - 4.375) < 1e-9
    assert 1.41 < r["m2"]["sum_over_kj"] < 1.43


def test_sign_critical_domain_scan():
    # Phase-0 domain gate: actual interpolants on (C1)–(C3), not the
    # tautological m2 ratio 4.375 at one n. Fast grid P in {10^6,10^8}.
    from research.juggler_sequence.two_step_parity import (
        sign_critical_domain_scan,
    )

    r = sign_critical_domain_scan(fast=True)
    assert r["n_samples"] > 0
    for name in (
        "e6_step5a",
        "thm61_offset",
        "thm61_zero_offset",
        "lemma52_stage4",
        "lemma52_stage6",
    ):
        rec = r["pieces"][name]
        assert rec["first_sign_loss_P"] is None
        assert rec["worst_ratio"] is not None
        assert rec["n_loss"] == 0
    e6 = r["pieces"]["e6_step5a"]
    assert e6["worst_ratio"] != 4.375
    assert 3.5 < e6["worst_ratio"] < 4.375
    t61 = r["pieces"]["thm61_offset"]
    assert 1.5 < t61["worst_ratio"] < 1.75
    z = r["pieces"]["thm61_zero_offset"]
    assert 0.99 < z["worst_ratio"] < 1.01
    s4 = r["pieces"]["lemma52_stage4"]
    assert 0.99 < s4["worst_ratio"] < 1.01
    assert s4["n_band_fail"] == 0
    s6 = r["pieces"]["lemma52_stage6"]
    assert s6["worst_ratio"] < 1.0


def test_transport_block_variance():
    # Phase-17 falsifier (b): level-3 defects are block-random — mode and
    # fifth-letter block variances at the random-phase scale, autocorr at
    # noise. OBSERVATION guard, loose thresholds.
    r = transport_block_variance(10**4, block_len=64, max_blocks=40)
    assert r["n_blocks"] == 40
    for val in r["mode_variance_ratio"].values():
        assert 0.4 < val < 2.5
    assert 0.4 < r["letter_variance_ratio"] < 2.5
    for val in r["letter_autocorr"].values():
        assert abs(val) < 0.15


def test_w_family_33_32_algebra():
    """Phase-28 seals for Theorem R at alpha = 33/32. Exact fractions."""
    alpha = Fraction(33, 32)
    smooth = Fraction(12825, 8192)
    window = Fraction(27, 64)
    composite = smooth - window
    assert composite == Fraction(9369, 8192)
    assert composite > 0
    assert smooth / window == Fraction(12825, 3456)
    assert Fraction(1701, 1024) > 0
    for beta in (Fraction(1, 4), Fraction(3, 4)):
        prod = (
            alpha
            * (alpha - 1)
            * (alpha + beta - 2)
            * (alpha + beta - 3)
        )
        assert prod > 0
    exponents = {
        Fraction(5, 4),
        Fraction(41, 32),
        Fraction(3, 2),
        Fraction(57, 32),
    }
    assert len(exponents) == 4
    assert Fraction(2) not in exponents
    # Lemma 3.8 c_6 for the close pair (5/4, 41/32).
    assert Fraction(1, 55) > 0
    assert Fraction(24, 23) != 1
    assert ANTI_OVERCLAIM["w_family_alpha_33_32_proved"] is True
    assert ANTI_OVERCLAIM["length7_remainder_engine_proved"] is True
    assert ANTI_OVERCLAIM["length7_passenger_theorem_t_refuted"] is True
    assert ANTI_OVERCLAIM["length7_vdc3_chirps_proved"] is True
    assert ANTI_OVERCLAIM["length7_x3_qr3_carry_refuted"] is True
    assert ANTI_OVERCLAIM["length7_integer_w_engine_line_refuted"] is True
    assert ANTI_OVERCLAIM["length8_remainder_discard_proved"] is True
    assert ANTI_OVERCLAIM["harvest_counting_terminal"] is True
    assert ANTI_OVERCLAIM["depth7_engine_contracting_proved"] is False
    assert ANTI_OVERCLAIM["depth8_engine_quartet_proved"] is False


def test_x1_remainder_reduction():
    samples = tuple(range(5, 2001, 2)) + (10**4 + 1, 10**5 + 1, 10**6 + 1)
    result = x1_remainder_reduction_scan(samples)
    assert result["holds"] is True
    assert result["far_ok"] > 100
    # 1/24 + 27/32 = 85/96 < 23/24 = 92/96; Fresnel assembly room.
    assert Fraction(1, 24) + Fraction(27, 32) < Fraction(23, 24)
    assert Fraction(9, 32) < 1
    assert Fraction(9, 8) != 2


def test_length7_passenger_slots():
    """Phase-34 seals: sixth-letter ranges miss Stage 2 / (D3)."""
    quarter = Fraction(1, 4)
    assert Fraction(27, 32) > quarter
    assert Fraction(31, 96) > quarter
    assert Fraction(9, 32) > quarter
    assert Fraction(27, 16) != Fraction(3, 2)
    assert Fraction(9, 8) != Fraction(3, 2)
    assert Fraction(27, 16) != Fraction(9, 4)
    # Lemma 3.3 on the θ_p chirp is worse than trivial.
    assert Fraction(81, 64) > 1
    # (D3) miss: -53/96 > -60/96.
    assert Fraction(-53, 96) > Fraction(-5, 8)
    assert ANTI_OVERCLAIM["length7_passenger_theorem_t_refuted"] is True
    assert ANTI_OVERCLAIM["length7_vdc3_chirps_proved"] is True
    assert ANTI_OVERCLAIM["length7_x3_qr3_carry_refuted"] is True
    assert ANTI_OVERCLAIM["depth7_engine_contracting_proved"] is False


def test_length7_vdc3_chirps():
    """Phase-35 seals: A-process + Lemma 3.3 inside P^{23/24}."""
    # Natural sizes: N λ^{1/6} = P^{177/192} < P^{23/24} = P^{184/192}.
    assert Fraction(177, 192) < Fraction(23, 24)
    # Uniform in k ≤ P^{1/24}: P^{535/576} < P^{23/24} = P^{552/576}.
    assert Fraction(535, 576) < Fraction(23, 24)
    # Differencing window stays inside the block.
    assert Fraction(85, 96) < Fraction(21, 16)
    assert Fraction(103, 96) < Fraction(3, 2)
    # Spawned sawtooth from w^{3/2} = n^{27/16} − (9/8) n^{3/16} θ_2.
    assert Fraction(27, 32) + Fraction(3, 16) > 1
    assert Fraction(85, 96) + Fraction(3, 16) > 1
    # Not the Phase-9 mixed-piece per-run collapse (that summed to P).
    assert Fraction(177, 192) < 1
    assert ANTI_OVERCLAIM["length7_vdc3_chirps_proved"] is True
    assert ANTI_OVERCLAIM["length7_x3_qr3_carry_refuted"] is True
    assert ANTI_OVERCLAIM["depth7_engine_contracting_proved"] is False


def test_length7_x3_qr3_carry():
    """Phase-37 seals: X3 freezes J, not kappa; Q/R3 coefficient > n."""
    result = w_carry_run_scan(10**4, 400)
    assert result["kappa_binary"] is True
    assert result["j_mean_run"] >= 8
    assert result["no_affine_carry_freeze"] is True
    assert result["kappa_mean_run"] <= 4
    # Sawtooth B ~ |u| P^{9/16} exceeds n already at the natural size.
    assert Fraction(27, 32) + Fraction(9, 16) > 1
    assert Fraction(85, 96) + Fraction(9, 16) > 1
    # B' ~ |u| P^{-7/16} >> 1; Lemma 3.7 window T ~ P^{45/32} > P.
    assert Fraction(27, 32) - Fraction(7, 16) > 0
    assert Fraction(45, 32) > 1
    # Ignoring the accumulated carry on an X3-run costs phase P^{73/32}.
    assert Fraction(27, 32) + Fraction(9, 16) + Fraction(7, 8) > 1
    assert ANTI_OVERCLAIM["length7_x3_qr3_carry_refuted"] is True
    assert ANTI_OVERCLAIM["length7_integer_w_engine_line_refuted"] is True
    assert ANTI_OVERCLAIM["depth7_engine_contracting_proved"] is False


def test_length7_integer_w_engine_line():
    """Phase-38 seals: integer-w coefficient ξ ~ n^{45/32} > n."""
    # Naive X1 coefficient 9/4 v^{5/8} ~ n^{45/32} exceeds n.
    assert Fraction(45, 32) > 1
    # Derivative ξ' ~ n^{13/32} >> 1; X3-run drift ξ' P^{7/8} = P^{41/32}.
    assert Fraction(13, 32) > 0
    assert Fraction(13, 32) + Fraction(7, 8) > 1
    # Dual sawtooth e(w {ξ}): coefficient w ~ n^{9/8} > n.
    assert Fraction(9, 8) > 1
    # Smooth interpolant ξ U ~ n^{81/32} is the first-letter chirp:
    # Lemma 3.3 costs P^{81/64} > P (already Lemma X5 / Phase 34).
    assert Fraction(81, 64) > 1
    assert ANTI_OVERCLAIM["length7_integer_w_engine_line_refuted"] is True
    assert ANTI_OVERCLAIM["depth7_engine_contracting_proved"] is False
    assert ANTI_OVERCLAIM["depth8_engine_quartet_proved"] is False


def test_length8_remainder_discard():
    """Phase-40 seals: envelope discard of e(kE)-1 is legal."""
    from research.juggler_sequence.two_step_parity import (
        eighth_remainder_rate_scan,
    )

    # Leading envelope n^{-45/128} beats the Vaaler range P^{13/384}:
    # k|E| -> 0, discard cost P^{131/192} < P^{243/256} and P^{23/24}.
    assert Fraction(45, 128) > Fraction(13, 384)
    assert Fraction(13, 384) - Fraction(45, 128) + 1 == Fraction(131, 192)
    assert Fraction(131, 192) < Fraction(243, 256)
    assert Fraction(131, 192) < Fraction(23, 24)
    # Formal drift E' ≍ n^{-29/128} < 1; k E' -> 0 on the same range.
    assert Fraction(29, 128) > 0
    assert Fraction(13, 384) - Fraction(29, 128) < 0
    samples = tuple(range(51, 300, 2)) + (10**4 + 1, 10**6 + 1)
    r = eighth_remainder_rate_scan(samples)
    assert r["holds"] is True
    assert r["outside_envelope"] == 0
    assert r["max_size_ratio"] < 1.0
    assert r["max_drift_ratio"] < 1.0
    assert ANTI_OVERCLAIM["length8_remainder_discard_proved"] is True
    assert ANTI_OVERCLAIM["depth8_engine_quartet_proved"] is False
    assert ANTI_OVERCLAIM["depth7_engine_contracting_proved"] is False
    assert ANTI_OVERCLAIM["harvest_counting_terminal"] is True


def test_harvest_counting_terminal():
    """Phase-41 seals: leftover exponents stay above the engine line."""
    # Inventory sum e(u w^{3/2}): natural |u| ~ P^{27/32} exceeds
    # Stage 2 (P^{1/4}) and Lemma 3.3 costs P^{81/64} > P.
    assert Fraction(27, 32) > Fraction(1, 4)
    assert Fraction(81, 64) > 1
    # Reduction leftover |u| n^{3/16} at |u| ~ P^{27/32} is P^{33/32} > n.
    assert Fraction(27, 32) + Fraction(3, 16) > 1
    # Q/R3 / integer-w wall is the same 45/32 coefficient.
    assert Fraction(45, 32) > 1
    assert ANTI_OVERCLAIM["harvest_counting_terminal"] is True
    assert ANTI_OVERCLAIM["length7_passenger_theorem_t_refuted"] is True
    assert ANTI_OVERCLAIM["length7_x3_qr3_carry_refuted"] is True
    assert ANTI_OVERCLAIM["length7_integer_w_engine_line_refuted"] is True
    assert ANTI_OVERCLAIM["length7_vdc3_chirps_proved"] is True
    assert ANTI_OVERCLAIM["length8_remainder_discard_proved"] is True
    assert ANTI_OVERCLAIM["depth7_engine_contracting_proved"] is False
    assert ANTI_OVERCLAIM["depth8_engine_quartet_proved"] is False
