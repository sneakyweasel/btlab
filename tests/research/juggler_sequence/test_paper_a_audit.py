"""Paper A's numbers, recomputed from the printed criterion.

The chain under test is Theorem 4.4 -> Lemma 4.4b -> Corollary 4.5 -> the four certified floors.
Everything here is independent of the probes that produced the paper's own tables: ``n_max`` is
rebuilt from the parity comparison as the paper states it.
"""

from __future__ import annotations

import math

import pytest

from research.juggler_sequence import paper_a_audit as A


# --- the criterion itself ---


def test_o_min_is_the_least_expanding_odd_count() -> None:
    for L in (19, 84, 569, 1054, 25781, 50508, 176251):
        o = A.o_min(L)
        assert 3**o > 2**L
        assert 3 ** (o - 1) < 2**L


def test_theta_matches_exact_integer_arithmetic() -> None:
    """The float trap: theta must come from high precision, not from double-precision logs."""
    for L in (19, 84, 1054, 25781):
        o = A.o_min(L)
        exact = (3**o - (1 << L)) / 3**o
        assert abs(A.theta(L) - exact) <= 1e-15 * exact


def test_double_precision_theta_would_break_n_max() -> None:
    """Documents why: the naive float exponent moves n_max(25781) by one."""
    L, o = 25781, A.o_min(25781)
    naive = 1.0 - 2.0 ** (L - o * math.log2(3))
    exact = A.theta(L)
    assert abs(naive - exact) / exact > 1e-8          # naive is off by more than the margin
    # the naive value is too small, so it keeps the comparison alive one step too far
    assert A.parity_holds(L, o, exact, 26254995)
    assert not A.parity_holds(L, o, exact, 26254996)
    assert A.parity_holds(L, o, naive, 26254996)      # naive would print n_max = 26254996


# --- every printed number ---


@pytest.mark.parametrize("L,printed", A.RECORD_NMAX)
def test_record_n_max_values(L: int, printed: int) -> None:
    assert A.n_max(L) == printed


def test_the_50508_row_was_off_by_one() -> None:
    """A draft printed 162848325; that value fails the comparison."""
    L, o = 50508, A.o_min(50508)
    th = A.theta(L)
    assert A.parity_holds(L, o, th, 162848324)
    assert not A.parity_holds(L, o, th, 162848325)


def test_n_max_crossings_are_razor_thin() -> None:
    """Both headline thresholds sit within 3e-8 relative of the crossing."""
    for L, n in ((25781, 26254995), (50508, 162848324)):
        o = A.o_min(L)
        th = A.theta(L)
        assert A.parity_holds(L, o, th, n)
        assert not A.parity_holds(L, o, th, n + 1)


@pytest.mark.parametrize("N0,bound,site", A.FLOORS)
def test_period_bound_at_each_certified_floor(N0: int, bound: int, site: str) -> None:
    """The contiguous excluded prefix from finance and parity alone."""
    assert A.first_survivor(N0, 200000) == bound


def test_arithmetic_and_rhin_checks() -> None:
    for c in A.arithmetic_checks() + A.rhin_checks():
        assert c["ok"], c["check"]


def test_rhin_coefficient_is_915_not_916() -> None:
    assert 914 < 2 * math.exp(13.3 * 0.46057) < 915


# --- the asymptotic that a draft got wrong ---


def test_convergent_invariant_is_flat_with_one_log_not_two() -> None:
    rows = A.convergent_invariant()
    assert len(rows) >= 5
    flat = [r["nlogn_over_q_qnext"] for r in rows]
    assert 0.40 < min(flat) and max(flat) < 0.55           # constant: the printed form
    two = [r["nlog2n_over_q_qnext"] for r in rows]
    assert max(two) / min(two) > 3                         # log^2 drifts by more than a factor 3
    assert max(flat) / min(flat) < 1.5                     # log does not


def test_survivor_exponent_is_near_0_59_not_0_64() -> None:
    exps = [e["exponent"] for e in A.survivor_exponent()]
    assert 0.57 <= min(exps) and max(exps) <= 0.62
    assert all(e < 0.64 for e in exps)


# --- Section 5.8, the fan law ---


def test_fan_law() -> None:
    for c in A.fan_law_checks():
        assert c["ok"], c["check"]


def test_fan_is_affine_and_ends_on_a_convergent() -> None:
    lam0 = A.fan_lambda(0)
    step = A.fan_lambda(1) - A.fan_lambda(0)
    assert step < 0
    for k in range(A.FAN_LEN):
        assert abs(A.fan_lambda(k) - (lam0 + k * step)) < 1e-18
    assert A.fan_lambda(55) > 0 > A.fan_lambda(56)
    assert A.fan_length(55) == 16785921
    assert A.fan_odd(55) == 10590737


def test_the_papers_three_frontiers_are_the_first_three_fan_members() -> None:
    assert [A.fan_length(k) for k in range(3)] == [176251, 478245, 780239]


def test_fan_prices_increase_and_pin_the_next_step() -> None:
    prices = {r["k"]: r["n_max"] for r in A.fan_prices()}
    ks = sorted(prices)
    assert all(prices[a] < prices[b] for a, b in zip(ks, ks[1:]))
    # the next purely computational step past the paper's 780239
    assert prices[2] == 4479642886
    assert 12.7 < prices[2] / 350000000 < 12.9
    # exhausting the fan
    assert 4.8e12 < prices[55] < 4.9e12


def test_floor_at_a_fan_price_gives_the_next_fan_bound() -> None:
    """N_0 >= n_max(L_k) gives period >= L_{k+1}, for k >= 1."""
    for k in (1, 2, 3):
        N0 = A.n_max(A.fan_length(k))
        assert A.first_survivor(N0, A.fan_length(k + 1)) == A.fan_length(k + 1)


def test_k_zero_has_the_doubling_exception() -> None:
    """At k = 0 the doubled length 2 q_12 intervenes, just above n_max(q_12)."""
    n0 = A.n_max(A.Q12)
    nd = A.n_max(2 * A.Q12)
    assert n0 < nd < A.n_max(A.fan_length(1))
    assert nd - n0 == 1793
    assert A.first_survivor(n0, 400000) == 2 * A.Q12


def test_walk_charge_is_worth_a_factor_of_about_eight_in_floor() -> None:
    vals = {w["site"]: w for w in A.walk_charge_value()}
    assert 6.0 < vals["Cor 5.10"]["factor"] < 7.0
    assert 7.5 < vals["Cor 5.11"]["factor"] < 8.5


def test_summary_is_all_green() -> None:
    r = A.summary()
    assert r["record_n_max_all_ok"]
    assert r["period_bounds_all_ok"]
    assert r["arithmetic_checks_all_ok"]
    assert r["rhin_checks_all_ok"]
    assert r["fan_law_all_ok"]


# --- Lemma 5.13 and Corollary 5.14: the walk charge's efficiency, measured ---


def test_margin_scaling_law_is_consistent_across_two_lengths() -> None:
    """Lemma 5.13: beta = 1.047 from two independent same-L pairs."""
    b = A.margin_beta()
    assert len(b["betas"]) == 2
    assert 1.04 < b["beta"] < 1.06
    assert b["spread"] < 0.01                       # the two agree to under 1%


def test_scaling_law_predicts_the_measured_kill_floor() -> None:
    """It predicted 780239's kill floor to 0.3% before it was computed."""
    pred = A.predicted_kill_floor(780239, 350000000)
    err = abs(pred - A.WALK_KILL_FLOOR_780239) / A.WALK_KILL_FLOOR_780239
    assert err < 0.01
    # and the conclusion is robust to the fit: beta = 1 gives the same answer
    pred1 = A.predicted_kill_floor(780239, 350000000, beta=1.0)
    assert abs(pred1 - A.WALK_KILL_FLOOR_780239) / A.WALK_KILL_FLOOR_780239 < 0.03


def test_walk_charge_factor_is_stable_near_eight() -> None:
    """6.4, 7.9, 8.09 at the three successive frontiers -- it is not decaying."""
    factors = [w["factor"] for w in A.walk_charge_value()]
    factors.append(A.n_max(780239) / A.WALK_KILL_FLOOR_780239)
    assert factors == sorted(factors)               # increasing, not decaying
    assert 6.0 < min(factors) and max(factors) < 8.5
    assert 8.0 < factors[-1] < 8.2


def test_conditional_bound_chain_is_complete() -> None:
    """Corollary 5.14: at floor 554000000 every parity survivor below 1082233 is killed."""
    M = A.stored_margins()
    floor = A.CONDITIONAL_FLOOR
    parity = A.survivors(floor, A.CONDITIONAL_BOUND)
    assert parity[-1] == A.CONDITIONAL_BOUND
    above = [L for L in parity if 780239 < L < A.CONDITIONAL_BOUND]
    assert len(above) == 9
    for L in above:
        assert M[(L, floor)] > 1.0, (L, M.get((L, floor)))
    # and the next fan member is the one that survives
    assert M[(A.CONDITIONAL_BOUND, floor)] < 1.0


def test_the_new_bound_is_the_next_fan_member() -> None:
    assert A.CONDITIONAL_BOUND == A.fan_length(3)
    assert A.WALK_KILL_FLOOR_780239 < A.n_max(780239)
    assert A.CONDITIONAL_FLOOR / 350000000 < 1.6      # only 1.58x the present floor


# --- Section 5.6: the extended window, and the walk charge's ceiling ---


def test_certified_denominators_reach_q14() -> None:
    """OstrowskiSandwich.lean pins theta between 6195184/16785921 and 6306641/17087915."""
    q = A.theta_denominators()
    assert q[:15] == [1, 2, 3, 8, 19, 65, 84, 485, 1054, 24727, 50508,
                      125743, 176251, 301994, 16785921]
    assert A.WINDOW_HI == q[14] == A.fan_length(55)      # the window ends where the fan does


def test_digit_sum_cap_is_the_sum_of_quotients() -> None:
    """s(L) <= sum(a_1..a_13) = 47 below q_13; the paper's printed cap."""
    assert sum(A.THETA_QUOTIENTS[1:14]) == 47
    for L in (50508, 176251, 301993):
        assert A.ostrowski_digit_sum(L) <= 47


def test_window_maximum_is_at_the_small_end() -> None:
    """A large digit forces a large L, so 2 s(L)/L is worst near 50508, not near q_14."""
    w = A.window_scan(hi=400_000)
    assert w["argmax"] < 100_000
    assert w["tail_bound_above_q13"] < w["max_2s_over_L"]     # the tail is an order lower
    assert 9.3e-4 < w["max_2s_over_L"] < 9.4e-4


def test_window_criterion_reproduces_the_printed_value() -> None:
    """(2 ln n - 6)/(ln3 (ln n)^3) = 5.14e-3 at ln n = 17.07, as Theorem 5.8 prints."""
    assert abs(A.window_criterion(17.07) - 0.00514) < 1e-4


def test_extended_window_holds_at_every_certified_floor() -> None:
    for h in A.window_headroom():
        assert h["holds"], h
        assert h["headroom"] > 4.0
    # and it survives far beyond any floor contemplated
    assert A.window_criterion(math.log(2.0e18)) > 9.3766e-4
    assert A.window_criterion(math.log(1.0e19)) < 9.3766e-4


def test_walk_improvement_is_proportional_to_log_floor() -> None:
    """Remark 5.8a: parity/walk ~ 0.44 ln n', constant to 8% over ten orders."""
    law = A.walk_improvement_law()
    lo, hi = law["ratio_range"]
    assert 0.42 < lo and hi < 0.47
    assert law["spread"] < 0.10
    # monotone decreasing: the lower-order term in the u-window integral
    ratios = [r["ratio"] for r in law["rows"]]
    assert ratios == sorted(ratios, reverse=True)


def test_doubling_the_walk_charge_requires_squaring_the_floor() -> None:
    """The practical content of Remark 5.8a."""
    c = 0.44
    at_floor = c * math.log(3.5e8)
    at_square = c * math.log(3.5e8**2)
    assert abs(at_square / at_floor - 2.0) < 1e-12       # exactly, since ln(n^2) = 2 ln n
    # and the measured law agrees with the constant used here
    rows = {r["n0"]: r for r in A.walk_improvement_law()["rows"]}
    assert abs(rows[350000000]["improvement"] - c * math.log(350000000)) < 0.3
