"""Paper A's numbers, recomputed from the printed criterion.

The chain under test is Theorem 4.4 -> Lemma 4.4b -> Corollary 4.5 -> the four certified floors.
Everything here is independent of the probes that produced the paper's own tables: ``n_max`` is
rebuilt from the parity comparison as the paper states it.
"""

from __future__ import annotations

import hashlib
import json
import math

import pytest

from research.juggler_sequence import paper_a_audit as A
from research.juggler_sequence import run_suffix_law as R
from research.juggler_sequence.lean_paths import DATA_ROOT, DOCS_THEORY

APPENDIX_B_CHUNK = (
    DATA_ROOT / "cycle_finance" / "floor_verify" / "N26254995" / "chunks" / "3_250002.json"
)
APPENDIX_B_CHUNK_SHA256 = (
    "6303b62c9b1819deaf9715338f84899c1d75eb50dcab850a7b8fb28874ec19bc"
)


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


def test_endpoint_denominators_and_lean_subwindow_are_distinguished() -> None:
    """Lean pins the endpoint powers, but its named window instance stops at q_13."""
    q = A.theta_denominators()
    assert q[:15] == [1, 2, 3, 8, 19, 65, 84, 485, 1054, 24727, 50508,
                      125743, 176251, 301994, 16785921]
    assert A.LEAN_WINDOW_HI == q[13] == 301994
    assert A.WINDOW_HI == q[14] == A.fan_length(A.WINDOW_ENDPOINT_FAN_INDEX)


def test_half_open_window_excludes_the_fan_endpoint() -> None:
    assert A.WINDOW_LAST_INCLUDED_FAN_INDEX == 54
    assert A.fan_length(A.WINDOW_LAST_INCLUDED_FAN_INDEX) < A.WINDOW_HI
    assert not A.fan_length(A.WINDOW_ENDPOINT_FAN_INDEX) < A.WINDOW_HI


def test_upper_convergent_surplus_has_the_signed_decay_bound() -> None:
    rows = A.upper_convergent_decay()
    assert len(rows) >= 4
    for row in rows:
        assert A.o_min(row["q"]) == row["p"]
        assert 0 < row["theta"] < row["surplus"] < row["surplus_upper"]
    assert rows[-1]["surplus_upper"] < rows[0]["surplus_upper"]
    for p, q, _a_next in A.convergents():
        if 3**p < 2**q:
            assert A.o_min(q) == p + 1


def test_paper_companions_state_the_window_trust_boundary() -> None:
    paper = (DOCS_THEORY / "juggler_finite_dynamics_note.md").read_text(encoding="utf-8")
    packet = (DOCS_THEORY / "juggler_finite_dynamics_reviewer_packet.md").read_text(
        encoding="utf-8"
    )
    canonical_map = (DOCS_THEORY / "juggler_finite_dynamics_formalization.md").read_text(
        encoding="utf-8"
    )
    review_map = (
        DOCS_THEORY.parents[1] / "juggler_review" / "juggler_finite_dynamics_formalization.md"
    ).read_text(encoding="utf-8")
    barrel = (
        DOCS_THEORY.parents[1] / "formal" / "Problems" / "JugglerPaper.lean"
    ).read_text(encoding="utf-8")
    assert "The instantiated Lean theorem\n`theta_digitSum_le`" in paper
    assert "it covers precisely \\(L_0,\\ldots,L_{54}\\) and excludes \\(L_{55}\\)" in paper
    assert "what an anchor-normalized charge can exclude" in paper
    assert "upper convergents" in paper
    assert "what any charge can exclude" not in paper
    assert "Within the length-only charges finance is already" not in paper
    assert "using the explicit lower bound for the gap" in paper
    assert "Only the classical\nvariation-versus-integral inequality itself remains prose" not in paper
    assert "change of variables identifying that circle\nintegral" in paper
    assert "not \\(L_{55}=q_{14}\\)" in packet
    for formalization in (canonical_map, review_map):
        assert "no named lean theorem instantiat" in formalization.lower()
        assert "\\(L_0,\\ldots,L_{54}\\)" in formalization
    assert "named Lean instance" in barrel
    assert "scope `L < 301994`" in barrel


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


def test_window_criterion_reproduces_the_printed_lower_bound() -> None:
    """The certified gap lower bound is 5.14e-3 at ln n = 17.07."""
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


def test_stratification_scales_are_read_from_the_paper_and_reproduce():
    """The three floor-derived scales, checked against the text that prints them.

    These lived in ``paper_c_audit`` under a docstring naming Paper C's Section 6, but Paper C
    prints none of them.  Reading the mantissa and exponent out of Paper A closes the gap the
    laboratory named itself: the audit lags the manuscript because constants arrive first.
    """
    checks = A.stratification_checks()
    assert len(checks) == 3
    bad = [(c["name"], c["printed"], c["computed"]) for c in checks if not c["ok"]]
    assert bad == [], bad
    assert all(c["printed"] is not None for c in checks), "a scale vanished from the paper"


def test_paper_c_does_not_print_the_stratification_scales():
    """Guard the reason the checks moved: if Paper C ever prints them, revisit the split."""
    text = (DOCS_THEORY / "juggler_fate_almost_all_note.md").read_text(
        encoding="utf-8"
    )
    for mantissa in (r"2.5\cdot10^{11}", r"6.5\cdot10^{12}", r"1.2\cdot10^{17}"):
        assert mantissa not in text, f"Paper C now prints {mantissa}"


# --- Section 3.9 printed numbers and Appendix B's 10^6 certificate ---


def test_corollary_3_27_ten_suffixes_match_the_law() -> None:
    """Eleven statements, ten suffixes: least-a and n_u are run_suffix_law evaluations."""
    paper = (DOCS_THEORY / "juggler_finite_dynamics_note.md").read_text(encoding="utf-8")
    assert "eleven statements, ten suffixes" in paper
    least_a = [R.least_run(suffix) for suffix, _printed, _src in R.RECOVERIES]
    n_u = [R.threshold_exact(a, suffix) for (suffix, _p, _s), a in zip(R.RECOVERIES, least_a)]
    assert least_a == [2, 4, 3, 6, 5, 4, 3, 5, 4, 3]
    assert n_u == [1032, 205, 109, 73, 60, 45, 30, 60, 45, 30]
    assert "1032,205,109,73,60,45,30,60,45,30" in paper.replace(" ", "")


def test_corollary_3_30_sharp_thresholds_match_the_law() -> None:
    paper = (DOCS_THEORY / "juggler_finite_dynamics_note.md").read_text(encoding="utf-8")
    sharp = [
        R.threshold_sharp(R.least_run(suffix), suffix) for suffix, _p, _s in R.RECOVERIES
    ]
    assert sharp == [7, 6, 6, 5, 5, 5, 5, 5, 5, 5]
    assert r"7,\;6,\;6,\;5,\;5,\;5,\;5,\;5,\;5,\;5" in paper


def test_remark_3_32_census_counts_match_the_law() -> None:
    paper = (DOCS_THEORY / "juggler_finite_dynamics_note.md").read_text(encoding="utf-8")
    for e, words, closed_at in ((3, 16, 16), (4, 186, 16), (5, 2037, 16), (6, 25353, 16)):
        rec = R.closure(e)
        assert rec["words"] == words
        assert rec["closed_at"] == closed_at
        assert rec["still_open"] == []
    assert "325452" in paper.replace(",", "")
    assert r"7\cdot10^{-5}" in paper


def test_appendix_b_million_certificate_is_the_opening_chunk() -> None:
    """Prop 1.3's 253 steps at 78901 live in the N26254995 opening chunk, not floor.json."""
    raw = APPENDIX_B_CHUNK.read_bytes()
    digest = hashlib.sha256(raw).hexdigest()
    assert digest == APPENDIX_B_CHUNK_SHA256
    payload = json.loads(raw)
    assert payload["max_steps"] == 253
    assert payload["hardest_seed"] == 78901
    paper = (DOCS_THEORY / "juggler_finite_dynamics_note.md").read_text(encoding="utf-8")
    appendix_b = paper[paper.index("## Appendix B"):]
    assert APPENDIX_B_CHUNK_SHA256 in appendix_b
    assert "253" in appendix_b and "78901" in appendix_b
    assert "3_250002.json" in appendix_b
    assert "n_{\\mathrm{top}}=2\\cdot10^6" in appendix_b


def test_appendix_b_n_max_one_is_the_conservative_table() -> None:
    """Exact 6/5 crossing at L=1 is 2; the printed table keeps 3, same species as 50508."""
    assert A.n_max(1) == 2
    paper = (DOCS_THEORY / "juggler_finite_dynamics_note.md").read_text(encoding="utf-8")
    appendix_b = paper[paper.index("## Appendix B"):]
    assert r"| \(1\) | \(1\) | \(3\) |" in appendix_b
    assert r"exact \(6/5\) crossing is \(2\)" in appendix_b
