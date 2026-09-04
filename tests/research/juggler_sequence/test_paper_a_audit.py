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
