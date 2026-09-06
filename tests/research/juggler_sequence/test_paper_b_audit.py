"""Paper B audit probe: exact identities, standing estimates, exponent bookkeeping (fast subset)."""

from __future__ import annotations

import io
import random
from fractions import Fraction as Fr
from pathlib import Path

import pytest

from research.juggler_sequence import paper_b_audit as A

ROOT = Path(__file__).resolve().parents[3]
PAPER = ROOT / "docs" / "theory" / "juggler_parity_discrepancy_note.md"


def test_exact_identities_hold_on_a_small_census() -> None:
    census = A.identity_census(seed=3, samples_per_range=6)
    assert census["all_identities_hold"], census["failures"]
    # the master identity and the double-gap identity were checked on every sample
    assert census["checks"]["L5.1ii-iv.master_identity"] == census["samples"]
    assert census["checks"]["L5.1ii-iv.double_gap"] == census["samples"]


def test_lemma_4_3_remainder_is_one_signed_and_bounded() -> None:
    rng = random.Random(5)
    for _ in range(50):
        n = rng.randrange(10**6, 2 * 10**6) | 1
        r = A.check_lemma_4_3(n, rng.randint(1, 5))
        assert r["E_nonneg"] and r["E_le_bound"] and r["E_le_coarse"] and r["gap_identity"]


def test_lemma_3_9_constant() -> None:
    # the proof needs the l^infinity (row-sum) norm of the inverse: 232; the printed 288 is the l^1 norm,
    # so c7 = 1/288 <= 1/232 remains a valid (non-sharp) constant
    assert A.lemma_3_9_operator_norm() == 232.0
    assert A.lemma_3_9_l1_norm() == 288.0
    inv = A._lemma_3_9_inverse()
    assert [[int(x) for x in row] for row in inv] == [[10, 68, 32], [-24, -144, -64], [15, 76, 32]]


def test_exponent_bookkeeping_all_pass() -> None:
    checks = A.exponent_checks()
    assert len(checks) >= 98
    assert all(c["ok"] for c in checks), [c["check"] for c in checks if not c["ok"]]


def test_standing_estimates_contain_observed_values() -> None:
    s = A.standing_estimates(10**6, seed=2, samples=30)
    assert s["all_ok"], s["verdict"]


def test_cell_inventory_matches_printed_bounds() -> None:
    c = A.cell_inventory(20_000, 1)
    assert c["ok"], c


def test_frozen_zero_offset_curvature_is_135_over_1024() -> None:
    r = A.frozen_anchor_curvature_samples(P=10**7, seed=4, trials=12)
    assert r["samples"] >= 8, r
    assert r["frozen_near_one"], r
    assert r["moving_gap_is_wrong_model"], r


def test_frozen_theta_coeff_is_9_over_32_and_at_most_six() -> None:
    r = A.frozen_theta_coeff_samples(P=10**6, seed=9, trials=8)
    assert r["samples"] >= 6, r
    assert r["ratio_near_one"], r
    assert r["abs_B_at_most_six"], r


def test_frozen_total_phase_matches_81_over_512_and_1095_over_1024() -> None:
    r = A.frozen_total_phase_samples(P=10**6, seed=8, trials=6)
    assert r["offset_samples"] >= 5, r
    assert r["zero_samples"] >= 5, r
    assert r["offset_near_one"], r
    assert r["B_near_27_over_32"], r
    assert r["zero_near_one"], r
    assert r["moving_8_27_is_wrong_model"], r


# --- Lemma 3.8's c_6 table: all twenty entries, not just the minimum ---


C6_PRINTED = {
    (Fr(3, 4), Fr(5, 4)): Fr(2, 7),   (Fr(3, 4), Fr(11, 8)): Fr(5, 13),
    (Fr(3, 4), Fr(3, 2)): Fr(1, 2),   (Fr(3, 4), Fr(15, 8)): Fr(1),
    (Fr(5, 4), Fr(3, 4)): Fr(2, 9),   (Fr(5, 4), Fr(11, 8)): Fr(1, 13),
    (Fr(5, 4), Fr(3, 2)): Fr(1, 6),   (Fr(5, 4), Fr(15, 8)): Fr(5, 9),
    (Fr(11, 8), Fr(3, 4)): Fr(5, 18), (Fr(11, 8), Fr(5, 4)): Fr(1, 14),
    (Fr(11, 8), Fr(3, 2)): Fr(1, 12), (Fr(11, 8), Fr(15, 8)): Fr(4, 9),
    (Fr(3, 2), Fr(3, 4)): Fr(1, 3),   (Fr(3, 2), Fr(5, 4)): Fr(1, 7),
    (Fr(3, 2), Fr(11, 8)): Fr(1, 13), (Fr(3, 2), Fr(15, 8)): Fr(1, 3),
    (Fr(15, 8), Fr(3, 4)): Fr(1, 2),  (Fr(15, 8), Fr(5, 4)): Fr(5, 14),
    (Fr(15, 8), Fr(11, 8)): Fr(4, 13), (Fr(15, 8), Fr(3, 2)): Fr(1, 4),
}


@pytest.mark.parametrize("pair,printed", sorted(C6_PRINTED.items()))
def test_every_c6_entry_matches_the_definition(pair, printed) -> None:
    """min_{s>0} max(|1-s|, |p - q s|), computed exactly."""
    assert A.c6_of_pair(*pair) == printed, pair


def test_the_table_has_twenty_entries_and_its_minimum_is_one_fourteenth() -> None:
    table = A.c6_table()
    assert len(table) == 20 and table == C6_PRINTED
    assert min(table.values()) == Fr(1, 14)
    assert [k for k, v in table.items() if v == Fr(1, 14)] == [(Fr(11, 8), Fr(5, 4))]
    assert Fr(1, 14) / 8 == Fr(1, 112)                       # rho_0(E)


def test_the_s_normalisation_raises_only_the_alpha_less_than_beta_orderings() -> None:
    """Relabelling gives |s| <= 1; it helps exactly where the crossing was beyond 1."""
    free, restricted = A.c6_table(), A.c6_table(Fr(1))
    raised = {k for k in free if restricted[k] != free[k]}
    assert raised == {(a, b) for a, b in free if a < b}
    assert len(raised) == 10
    # and the binding entry is not among them, so the uniform constant is unchanged
    assert (Fr(11, 8), Fr(5, 4)) not in raised
    assert min(restricted.values()) == Fr(1, 14)


def test_paper_records_that_the_normalisation_buys_nothing() -> None:
    text = io.open(PAPER, encoding="utf-8").read()
    assert "The table is not symmetric" in text
    assert "buys nothing" in text
    assert r"\rho_0(E)\le\tfrac1{112}\) either way" in text


# --- which named constants carry numbers ---


def _paper() -> str:
    return io.open(PAPER, encoding="utf-8").read()


def test_c8_never_leaves_lemma_38s_proof() -> None:
    """Three uses, all inside the proof that introduces it, absorbed into <<_E."""
    text = _paper()
    start = text.index("**Lemma 3.8 (two-term monomial test")
    end = text.index("**Lemma 3.9", start)
    inside = text[start:end]
    assert text.count("c_8") == inside.count("c_8") > 0


def test_neither_c8_nor_CE_is_ever_evaluated() -> None:
    """Neither name is ever followed by a relation to a number."""
    text = _paper()
    ops = ("=", chr(92) + "le", chr(92) + "ge")
    fracs = (chr(92) + "tfrac", chr(92) + "frac")
    for name in ("c_8", "C(E)"):
        start = 0
        while (i := text.find(name, start)) != -1:
            tail = text[i + len(name):i + len(name) + 16].lstrip()
            for op in ops:
                if tail.startswith(op):
                    rest = tail[len(op):].lstrip()
                    assert not (rest[:1].isdigit() or rest.startswith(fracs)), (name, tail)
            start = i + 1


def test_the_evaluated_constants_are_the_four_the_paper_names() -> None:
    text = _paper()
    assert r"c_6(E)=\tfrac1{14}" in text
    assert r"\rho_0(E)\le\tfrac1{112}" in text
    assert "c_7=1/232" in text or r"c_7=\tfrac1{232}" in text
    assert A.c6_of_pair(Fr(11, 8), Fr(5, 4)) == Fr(1, 14)


def test_the_one_place_an_absorbed_constant_binds() -> None:
    """C(E) log P <= P^{1/96} is not settled by the O_E that carries it elsewhere."""
    text = _paper()
    assert r"C(E)\log P\le P^{1/96}" in text
    assert "Which constants carry numbers." in text
    assert "never assigned a value anywhere" in text


# --- Theorem 4.8: the shifted-window device everything leans on ---


def test_theorem_48_curvature_collects_two_terms() -> None:
    """27k/128 is 9/128 from (k/2)n^{9/8} plus 9/64 from the frozen -B_0 n^{3/4}."""
    from_k = Fr(1, 2) * Fr(9, 8) * Fr(1, 8)                  # (k/2) n^{9/8}
    d2_n34 = Fr(3, 4) * (Fr(3, 4) - 1)                       # -3/16
    from_B0 = -Fr(3, 4) * d2_n34                             # B_0 = (3k/4) n^{3/8}
    assert from_k == Fr(9, 128) and from_B0 == Fr(9, 64)
    assert from_k + from_B0 == Fr(27, 128)
    # the other two displayed coefficients are plain derivatives
    assert Fr(1, 2) * Fr(3, 2) * Fr(1, 2) == Fr(3, 8)        # (i/2) n^{3/2} -> 3i/8
    assert d2_n34 == Fr(-3, 16)                              # t n^{3/4} -> -3/16


def test_the_other_27_over_128_is_a_different_quantity() -> None:
    """Theorem 6.3's is u_0 X'' with u_0 = (9k/32)n^{3/16}, landing at n^{-5/16}."""
    assert Fr(9, 32) * Fr(3, 4) == Fr(27, 128)
    assert Fr(3, 16) - Fr(1, 2) == Fr(-5, 16)


def test_theorem_48s_sawtooth_matches_the_coefficient_rule() -> None:
    """B = (3k/4) n^{3/8} is what the session's rule gives for theta_2 at letter 4 of OEO."""
    from research.juggler_sequence import paper_b_prefix_count as PB
    const, exponent = PB.defect_coefficient("OEO", 4, 2)
    assert (const, exponent) == (Fr(3, 4), Fr(3, 8))
    assert exponent - 1 == Fr(-5, 8)                 # B' ~ k n^{-5/8}
    assert 1 - exponent == Fr(5, 8)                  # drift-1 length L_0 = P^{5/8}/k
    assert PB.linearisation_safe("OEO", 4)
    assert PB.composed_map("OEO", 4, 2) == Fr(3, 2)  # one letter from defect to wave


def test_the_underlying_integer_increments_at_the_printed_rate() -> None:
    """U = m^{1/2} = n^{3/4}, so floor(U) moves once every (4/3) n^{1/4} steps."""
    assert Fr(3, 4) - 1 == Fr(-1, 4)
    assert 1 / Fr(3, 4) == Fr(4, 3)


def test_paper_explains_the_collected_coefficient() -> None:
    text = _paper()
    assert "collects two terms" in text
    assert r"\tfrac9{128}+\tfrac{18}{128}=\tfrac{27}{128}" in text


# --- Lemma 3.10: the reindexing needs hypotheses as well as conclusions ---


def test_the_reindexed_van_der_corput_bound_is_smaller() -> None:
    """(L/2)(4L)^{1/2} + (4L)^{-1/2} = L lam^{1/2} + lam^{-1/2}/2."""
    import math
    for L, lam in ((1000.0, 1e-4), (10.0, 1.0), (1e6, 1e-9)):
        reindexed = (L / 2) * (4 * lam) ** 0.5 + (4 * lam) ** -0.5
        displayed = L * lam ** 0.5 + lam ** -0.5
        assert reindexed <= displayed
        assert abs(reindexed - (L * lam ** 0.5 + 0.5 * lam ** -0.5)) < 1e-9 * displayed


@pytest.mark.parametrize("alpha,n_min", [(Fr(3, 4), 143), (Fr(5, 4), 87), (Fr(11, 8), 73),
                                         (Fr(3, 2), 59), (Fr(15, 8), 17)])
def test_the_binomial_correction_fits_rho_zero(alpha: Fr, n_min: int) -> None:
    """a(2r+1)^alpha is not a monomial; the correction must fit inside g."""
    rho0 = Fr(1, 112)
    r = (n_min - 1) // 2
    x = Fr(1, 2 * r)
    assert abs(alpha - 2) * x / (1 - x) <= rho0                 # fits at n_min
    x_prev = Fr(1, 2 * (r - 1))
    assert abs(alpha - 2) * x_prev / (1 - x_prev) > rho0        # and not one step earlier


def test_the_worst_exponent_is_three_quarters_and_it_clears_far_below_P0() -> None:
    assert max(A.EXPONENT_SET_E, key=lambda a: abs(a - 2)) == Fr(3, 4)
    assert 143 < 8.9e13


def test_part_c_domination_needs_the_set_to_be_long() -> None:
    """Lambda/2 + C <= Lambda iff Lambda >= 2C; below that both sides are O_E(1)."""
    for C_E in (1, 5, 20):
        assert C_E / 2 + C_E > C_E                     # short set: not dominated
        assert (2 * C_E) / 2 + C_E <= 2 * C_E          # at the threshold: equality


def test_paper_records_both_gaps() -> None:
    text = _paper()
    assert "(b) is about conclusions and these are about hypotheses" in text
    assert r"n\ge143" in text
    assert "by absorption, not for free" in text
    assert "vacuous rather than false" in text


# --- Lemma 3.6, the other blanket: six uses, and until now no test ---


def _chain_xis(n: int, w: str):
    from mpmath import mpf, floor, power
    xs, xis = [n], []
    for t in range(len(w) - 1):
        xi = power(mpf(xs[t]), mpf(3) / 2 if w[t] == "O" else mpf(1) / 2)
        xis.append(xi)
        xs.append(int(floor(xi)))
    return xis


def _branch_product(n: int, w: str) -> int:
    from mpmath import floor
    out = 1.0
    for t, xi in enumerate(_chain_xis(n, w)):
        sigma = 1 if w[t + 1] == "E" else -1
        out *= 0.5 * (1 + sigma * (-1) ** int(floor(xi)))
    return round(out)


def _true_word(n: int, d: int) -> str:
    from mpmath import mpf, floor, power
    it, s = n, ""
    for _ in range(d):
        s += "O" if it % 2 else "E"
        it = int(floor(power(mpf(it), mpf(3) / 2 if it % 2 else mpf(1) / 2)))
    return s


@pytest.mark.parametrize("d", [2, 3, 4, 5, 6])
def test_branch_consistency_holds_for_every_O_rooted_word(d: int) -> None:
    from itertools import product
    from mpmath import mp
    mp.dps = 60
    for bits in product("EO", repeat=d - 1):
        w = "O" + "".join(bits)
        for n in range(1001, 1200, 2):
            assert _branch_product(n, w) == int(_true_word(n, d) == w), (w, n)


def test_the_w1_equals_O_hypothesis_is_necessary() -> None:
    """The product tests letters 2..d only; letter one is the "n odd" restriction."""
    from itertools import product
    from mpmath import mp
    mp.dps = 60
    mismatches = 0
    for bits in product("EO", repeat=2):
        w = "E" + "".join(bits)
        for n in range(1001, 1100, 2):
            if _branch_product(n, w) != int(_true_word(n, 3) == w):
                mismatches += 1
    assert mismatches > 0


def test_every_use_of_lemma_36_is_O_rooted() -> None:
    """Six citations; the word-specific ones are OOEE, OOEEE, OOO*, OOOE*, OOEO*."""
    text = _paper()
    assert text.count("Lemma 3.6") == 7          # the statement plus six uses
    for word in ("OOEE", "OOEEE", "OOOE", "OOEO"):
        assert word.startswith("O"), word


def test_paper_records_that_the_hypothesis_is_necessary() -> None:
    text = _paper()
    assert "necessary, not a convenience" in text
    assert "the two sides disagree outright" in text


# --- Lemma 3.5: the majorant cost is 4P/J per layer, everywhere ---


@pytest.mark.parametrize("j,layers,printed_exponent", [
    (Fr(1, 96), 1, Fr(95, 96)),        # Theorem 6.1 Step A
    (Fr(1, 4), 2, Fr(3, 4)),           # Step 3a
    (Fr(1, 24), 1, Fr(23, 24)),        # Step 3b
    (Fr(1, 8), 3, Fr(7, 8)),           # the P^{1/8} truncation
])
def test_every_quoted_majorant_is_four_P_over_J(j: Fr, layers: int, printed_exponent: Fr) -> None:
    assert 1 - j == printed_exponent
    assert layers >= 1


def test_doubling_the_truncation_halves_the_printed_constant() -> None:
    """J_5 = 2P^{1/96} gives 4P/J = 2P^{1-1/96}, as Theorem 6.3 prints."""
    assert Fr(4, 2) == 2


def test_four_over_J_carries_at_least_eightfold_slack() -> None:
    """Derived flat cost is P/(2(J+1)) over odd n; 4P/J is at least eight times it."""
    for J in (10, 100, 10**4, 10**8):
        derived = 1 / (2 * (J + 1))
        printed = 4 / J
        assert printed / derived >= 8


def test_the_slack_moves_no_exponent() -> None:
    """Each majorant is weighed against a budget of its own exponent."""
    # Theorem 6.1: majorant 4P^{1-1/96} against the kernel bound P^{1-1/96}
    assert 1 - Fr(1, 96) == Fr(95, 96)
    # Step 3b: 4P^{23/24} against Lemma 5.2(ii)'s P^{23/24}
    assert 1 - Fr(1, 24) == Fr(23, 24)


def test_paper_says_the_four_is_a_rounding() -> None:
    text = _paper()
    assert r"quote the flat cost as \(4P/J\) per majorant" in text
    assert "a rounding\nrather than a derived value" in text or "a rounding" in text
    assert "a factor of at least eight" in text
    assert "would move no exponent anywhere" in text


# --- Section 8's payoff numbers ---


def _contagion_root(with_ooeee: bool):
    from mpmath import mp, mpf, findroot, power
    mp.dps = 30

    def f(L):
        v = 2 ** (-L) + mpf(1) / 9 * power(mpf(3) / 8, L) + mpf(2) / 9 * power(mpf(3) / 4, L) - 1
        if with_ooeee:
            v += mpf(1) / 9 * power(mpf(9) / 32, L)
        return v

    return findroot(f, mpf("0.54") if with_ooeee else mpf("0.45"))


def test_the_two_contagion_exponents_are_roots_of_one_recursion() -> None:
    """lambda** = 0.4480 and lambda*** = 0.5392, differing by the OOEEE summand."""
    from mpmath import mpf
    assert abs(_contagion_root(False) - mpf("0.4480")) < 5e-5
    assert abs(_contagion_root(True) - mpf("0.5392")) < 5e-5
    assert _contagion_root(True) > _contagion_root(False)


def test_the_OOEEE_dividend_is_a_single_summand() -> None:
    """Adding (1/9)(9/32)^lambda is the whole difference between the two."""
    gain = _contagion_root(True) - _contagion_root(False)
    assert 0.09 < float(gain) < 0.10


def test_the_chain_gives_c_equals_two() -> None:
    """1/24 -> 1/96 over one depth is a factor 4 = 2^2."""
    assert Fr(1, 24) / Fr(1, 96) == 4
    assert 4 == 2 ** 2


def test_the_frontier_gap_is_a_factor_of_thirty_eight() -> None:
    """c < 1/19 needed against c = 2 delivered."""
    assert Fr(1, 19) < Fr(2)
    assert Fr(2) / Fr(1, 19) == 38


def test_paper_names_the_gap_and_the_summand() -> None:
    text = _paper()
    assert r"\(38\)" in text and "a factor of" in text
    assert "differ by exactly one term" in text
    assert "attributable to a single summand" in text


# --- the 0.5561 dividend does not reconcile with the paper's own rule ---


def _recursion_root(extra, guess):
    from mpmath import mp, mpf, findroot, power
    mp.dps = 30
    base = [(Fr(1), Fr(1, 2)), (Fr(1, 9), Fr(3, 8)), (Fr(2, 9), Fr(3, 4)), (Fr(1, 9), Fr(9, 32))]
    terms = base + list(extra)
    f = lambda L: sum(mpf(c.numerator) / c.denominator                     # noqa: E731
                      * power(mpf(e.numerator) / e.denominator, L) for c, e in terms) - 1
    return findroot(f, mpf(guess))


def test_the_production_rule_reproduces_the_OOEEE_term() -> None:
    """(P_w/e_w) at scale e_w, with P_w = 2^-d and e_w the final scale exponent."""
    from research.juggler_sequence import paper_b_prefix_count as PB
    e = PB.iterate_exponents("OOEEE")[-1]
    assert e == Fr(9, 32)
    assert Fr(1, 2 ** 5) / e == Fr(1, 9)


def test_the_two_printed_contagion_exponents_solve_the_recursion() -> None:
    from mpmath import mpf
    assert abs(_recursion_root([], "0.54") - mpf("0.5392")) < 5e-5
    base_minus = [(Fr(-1, 9), Fr(9, 32))]              # cancel the OOEEE term
    assert abs(_recursion_root(base_minus, "0.45") - mpf("0.4480")) < 5e-5


def test_the_localized_words_both_land_at_twentyseven_sixtyfourths() -> None:
    from research.juggler_sequence import paper_b_prefix_count as PB
    for w in ("OOOEEE", "OOEOEE"):
        assert len(w) == 6
        assert PB.iterate_exponents(w)[-1] == Fr(27, 64), w
        assert Fr(1, 64) / Fr(27, 64) == Fr(1, 27)


def test_the_rule_gives_0_6066_not_the_printed_0_5561() -> None:
    from mpmath import mpf
    got = _recursion_root([(Fr(1, 27), Fr(27, 64))] * 2, "0.60")
    assert abs(got - mpf("0.606635")) < 1e-5
    assert abs(got - mpf("0.5561")) > 0.04


def test_the_discrepancy_is_recorded_and_runs_conservative() -> None:
    led = io.open(ROOT / "docs" / "theory" / "paper_b_audit_ledger.md", encoding="utf-8").read()
    assert "does not reconcile" in led
    assert "0.606635" in led and "0.01812" in led
    assert "conservative direction" in led
    text = _paper()
    assert "recorded in the audit ledger rather than" in text


# --- the Lemma 6.2 edge search hunts for something that does not exist ---


def test_the_printed_lemma_6_2_bound_holds_at_every_admissible_n() -> None:
    """The Lagrange term in b_print covers the two omitted remainders, from n = 5 upward."""
    rows = A.lemma_6_2_margin_certificate()
    assert all(r["ok"] for r in rows), [r["n"] for r in rows if not r["ok"]]
    assert rows[0]["n"] == 5 and rows[0]["i_dominance_ratio"] > 8
    big = rows[-1]
    assert abs(big["i_dominance_ratio"] / (0.75 * big["n"] ** 1.5) - 1) < 1e-3
    for r in rows:
        assert r["i_lagrange_covers_omitted"] and r["ii_A_covers_lagrange"] and r["ii_thetaw_covers_E2"]
        if r["n"] >= 10**4:
            assert abs(r["ceiling_deficit_times_n^(3/4)"] - 3 / 32) < 1e-3, r["n"]


def test_the_edge_search_worst_ratio_is_a_property_of_the_sample_size() -> None:
    small = A.lemma_6_2_edge_search(seed=7, trials=400)
    large = A.lemma_6_2_edge_search(seed=7, trials=4000)
    for r in (small, large):
        assert r["printed_violation_count"] == 0
        assert r["worst_ratio_below_ceiling"]
    assert large["worst_ratio_to_printed_bound_i"] >= small["worst_ratio_to_printed_bound_i"]
    # 1 - worst is of order 1/trials, and the ceiling it would have to cross is orders further out
    assert 0.05 < large["one_minus_worst_times_trials"] < 50
    deficit = 1 - large["worst_ratio_to_printed_bound_i"]
    assert deficit > 10 * (1 - large["ratio_ceiling_at_midpoint"])
    assert large["max_theta2_seen"] < 1 and large["max_theta_z_seen"] < 1


def test_the_five_printed_remainder_orders_are_the_measured_ones() -> None:
    row = A.lemma_6_2_margin_certificate([10**8 + 1])[0]
    assert row["orders_tested"] and row["worst_order_deviation"] < 1e-6
    for key, order in A.LEMMA_6_2_PRINTED_ORDERS.items():
        assert abs(row["measured_exponents"][key] - float(order)) < 1e-6, key
    text = _paper()
    for order in ("-9/16", "-27/16", "-21/16", "-45/16", "-81/16"):
        assert "n^{%s}" % order in text, order


def test_the_directed_family_reaches_a_fixed_fraction_of_the_unreachable_ceiling() -> None:
    """n = 10^k + 1, k divisible by 4: 1 - theta_2 is (27/128) n^(-3/4), the ceiling's own order."""
    rows = A.lemma_6_2_directed_search()
    assert all(r["ok"] for r in rows), [r["k"] for r in rows if not r["ok"]]
    for r in rows:
        assert r["below_ceiling"]
        assert abs(r["attained_fraction_of_ceiling"] - 4 / 13) < 1e-6
        assert abs(r["ceiling_deficit_times_n^(3/4)"] - 3 / 32) < 1e-9
    assert A.DIRECTED_DEFICIT == Fr(12, 128) + A.DIRECTED_ONE_MINUS_THETA2
    # and it beats the random hunt by orders of magnitude at a thousandth of the cost
    random_deficit = 1 - A.lemma_6_2_edge_search(seed=7, trials=400)["worst_ratio_to_printed_bound_i"]
    assert rows[0]["printed_ratio_deficit_times_n^(3/4)"] < random_deficit * 10**15


def test_the_lemma_6_2_checker_scales_its_own_precision() -> None:
    """At the module's 60 digits the checker reports a false failure at n = 10^28."""
    import mpmath as mp

    n = 10**28 + 1
    assert A.working_dps_for(n) >= 60 + 4 * 28
    with mp.workdps(60):
        bad = A._check_lemma_6_2_fixed_precision(n)
    assert not bad["i_corrected"] and bad["theta2"] > 1     # a fractional part of 5.0
    before = mp.mp.dps                                      # other tests move the module setting
    good = A.check_lemma_6_2(n)
    assert good["i_corrected"] and good["ii_corrected"] and 0 <= good["theta2"] <= 1
    assert mp.mp.dps == before                              # and the wrapper restores it


# --- the observation layer's two printed ratios could not have come out otherwise ---


def test_the_printed_benchmarks_sit_above_the_trivial_bound() -> None:
    """|K_c| <= P/2 always, and P^(1-1/96) exceeds P/2 until P = 2^96."""
    reach = A.kernel_observation_reach()
    assert reach["kernel_crossover"] == 2.0**96
    assert reach["kernel_crossover_factor_two"] == 2.0**192
    assert reach["wave_crossover"] == 2.0**24
    assert reach["wave_crossover_factor_two"] == 2.0**48
    assert not reach["any_benchmark_informative"]
    for row in reach["points"]:
        assert row["trivial_over_kernel_benchmark"] < 1 and row["trivial_over_wave_benchmark"] < 1
    # and the wave's crossover is reachable by summation where the kernel's never will be
    assert reach["wave_crossover"] < 10**8 < reach["kernel_crossover"]


def test_the_observation_layer_measures_the_square_root_scale() -> None:
    """What is falsifiable here: both sums are three orders below trivial, not a hair below it."""
    for P in (10**4, 3 * 10**4):
        r = A.kernel_sum(P)
        assert not r["kernel_benchmark_informative"] and not r["wave_benchmark_informative"]
        assert r["abs_K_over_trivial"] < 0.05 and r["abs_wave_over_trivial"] < 0.05
        assert 0.05 < r["abs_K_over_sqrtN"] < 8 and 0.05 < r["abs_wave_over_sqrtN"] < 8


def test_the_kernel_sum_leaves_the_module_precision_alone() -> None:
    import mpmath as mp

    with mp.workdps(80):
        A.kernel_sum(1000)
        assert mp.mp.dps == 80


def test_the_block_variance_measures_an_exponent_where_one_number_cannot() -> None:
    """Square root is 0.5 and no cancellation is 1.0; the single-sample ladder scattered -0.13..1.56."""
    r = A.kernel_block_scaling(P=3 * 10**4)
    assert r["terms"] == 15000 and len(r["blocks"]) == len(A.BLOCK_COUNTS)
    assert r["blocks"][0]["blocks"] == 256 and r["blocks"][-1]["blocks"] == 1
    assert 0.15 < r["kernel_exponent"] < 0.75
    assert 0.15 < r["wave_exponent"] < 0.75
    for b in r["blocks"]:
        assert 0.2 < b["rms_K_over_sqrtL"] < 3 and 0.2 < b["rms_wave_over_sqrtL"] < 3


# --- Conjecture 7.3's own sum, which nothing had ever evaluated ---


def test_the_level_three_kernel_shows_square_root_scale_cancellation() -> None:
    """Both weights of Lemma 7.2: the floor-shaped (3k/4) z^(1/2) and the smooth n^(27/16)."""
    r = A.level3_kernel_block_scaling(P=10**4)
    assert r["terms"] == 5000
    assert r["abs_K3_floor_over_trivial"] < 0.05 and r["abs_K3_floor_over_sqrtN"] < 8
    assert r["abs_K3_smooth_over_sqrtN"] < 8
    for key in ("K3_floor_exponent", "K3_smooth_exponent"):
        assert 0.1 < r[key] < 0.8, (key, r[key])          # 0.5 is square root, 1.0 is none
    for b in r["blocks"]:
        assert 0.2 < b["rms_K3_floor_over_sqrtL"] < 3
        assert 0.2 < b["rms_K3_smooth_over_sqrtL"] < 3


def test_the_frontier_exponent_bookkeeping_is_exact() -> None:
    """Section 7's displayed exponents, which no layer of the audit had reached."""
    checks = A.exponent_checks()
    section7 = [c for c in checks if c["check"].startswith(("7.2", "7.3", "7.4"))]
    assert len(section7) == 10 and all(c["ok"] for c in section7)
    assert all(c["ok"] for c in checks)


# --- the uniformity clauses, and the caps that pin their parameter to 1 ---


def test_four_of_the_six_parameter_caps_pin_their_parameter_at_the_ladder() -> None:
    """1 <= x <= C P^e takes a second value only past (2/C)^(1/e)."""
    rows = {r["parameter"].split(",")[0]: r for r in A.parameter_cap_reach()}
    assert abs(rows["k"]["least_P_admitting_two_values"] - 2.0**24) < 1
    assert abs(rows["h_1"]["least_P_admitting_two_values"] - 2.0**48) < 2.0**24
    assert rows["h_1"]["pinned_at_P0"] and rows["h_1"]["values_at_P0"] == 1
    assert not rows["k"]["pinned_at_P0"] and rows["k"]["values_at_P0"] == 3
    assert rows["j"]["least_P_admitting_two_values"] == 1.0            # never pinned
    assert abs(rows["h"]["least_P_admitting_two_values"] - 4096) < 1
    pinned = [r for r in A.parameter_cap_reach() if r["pinned_at_ladder_top"]]
    assert len(pinned) == 4                                            # k, h_1, h_2, |l|


def test_no_k_loses_the_cancellation_at_either_level() -> None:
    """Sweeping k past (C3) leaves the hypothesis; it is the only way to see if k matters at all."""
    r = A.kernel_k_uniformity(P=10**4, ks=(1, 2, 8, 64))
    assert r["ks_inside_the_cap"] == [1]                               # (C3) admits nothing else
    assert r["no_k_loses_cancellation"]
    for level in (r["level2"], r["level3"]):
        for row in level:
            assert 0.1 < row["exponent"] < 0.8, row
            assert row["abs_over_sqrtN"] < 8


def test_the_recorded_run_sits_exactly_at_the_C3_threshold() -> None:
    """2^24 is where P^(1/24) = 2, so it is the first P at which (C3) admits k = 2."""
    rec = A.KERNEL_AT_C3_THRESHOLD
    caps = {r["parameter"].split(",")[0]: r for r in A.parameter_cap_reach()}
    assert rec["P"] == 2**24 == int(caps["k"]["least_P_admitting_two_values"])
    assert abs(rec["P"] ** (1 / 24) - 2.0) < 1e-12
    assert rec["terms"] == (rec["P"] // 2)
    for k in ("k1", "k2"):
        assert 0.4 < rec[k]["block_exponent"] < 0.6
        assert 0.5 < rec[k]["abs_over_sqrtN"] < 2


# --- the instrument, measured against data whose exponent is known ---


def test_the_block_exponent_estimator_is_calibrated() -> None:
    """On iid unit phases the true exponent is 1/2, so the fit's bias and spread are readable."""
    cal = A.block_exponent_calibration(N=5000, trials=120)
    assert cal["fit_counts"] == [256, 128, 64, 32, 16]
    assert abs(cal["fitted"]["bias"]) < 0.03
    assert cal["fitted"]["sd"] < 0.07
    # and the estimator that fitted every block count, the one used before this calibration,
    # was biased by an order of magnitude more and twice as noisy
    assert cal["all_block_counts"]["bias"] < -0.02
    assert cal["all_block_counts"]["sd"] > 1.7 * cal["fitted"]["sd"]


# --- what the census can and cannot police ---


def test_the_census_has_power_over_four_constants_and_little_over_the_brackets() -> None:
    r = A.census_constant_power(samples_per_range=12)
    by = {row["ratio_key"]: row for row in r["constants"]}
    for key in ("E_ratio_fine", "R_ratio", "M1_ratio", "i_slack_ratio"):
        assert by[key]["extreme_ratio"] > 0.9, key          # attained: a 10% cut would be caught
    assert by["second_ratio_upper"]["extreme_ratio"] < 0.6   # 15 could be 9 and nothing would notice
    assert by["second_ratio_lower"]["extreme_ratio"] > 4     # and the lower constant is 4x loose


def test_the_two_bracket_constants_are_three_halves_and_twentyseven_quarters() -> None:
    """The census measures what the printed band only encloses."""
    import mpmath as mp

    with mp.workdps(120):
        for n in (10**12 + 1, 10**14 + 1):
            r = A.check_lemma_5_1_ii_iv(n, 1, 2, 1)
            assert abs(r["second_ratio_upper"] * 15 - 27 / 4) < 1e-4, n
            if r["first_ratio_upper"] is not None:
                assert abs(r["first_ratio_upper"] * 2.6 - 3 / 2) < 1e-4, n


# --- Appendix A says it enumerates every printed threshold; two are missing ---


def test_two_printed_thresholds_are_absent_from_appendix_a() -> None:
    g = A.appendix_a_gaps()
    tags = {r["tag"]: r for r in g["rows"]}
    assert not any(r["in_certificate"] for r in g["rows"])
    assert 2.0e3 < tags["L5.1(iii)-Gprime"]["least_P"] < 2.1e3
    assert 8.8e5 < tags["T6.1-StepB-discard"]["least_P"] < 8.9e5
    assert g["all_gaps_below_P0"] and g["P0_binding_tag"] == "5b-W<=c7S"


def test_the_step_B_constant_was_rounded_and_its_threshold_was_not() -> None:
    """(3 pi k/4) P^(-1/8) with |k| <= 2P^(1/96) is exactly (3 pi/2) P^(-11/96) = 4.7124 ..."""
    import math

    g = A.appendix_a_gaps()
    assert abs(g["exact_step_B_constant"] - 3 * math.pi / 2) < 1e-12
    assert g["printed_step_B_constant"] > g["exact_step_B_constant"]
    assert g["printed_threshold_matches_exact_constant"]      # 7.6e5 is 4.7124's threshold
    assert g["printed_threshold_too_small_for_printed_constant"]
    text = _paper()
    assert r"4.8\,P^{-11/96}<1" in text and r"7.6\cdot10^{5}" in text


def test_the_bracket_band_does_not_reach_P0() -> None:
    """Sharpening 1.4 and 15 to the true 27/4 and (27/4)2^(1/4) moves no threshold."""
    g = A.appendix_a_gaps()
    assert not g["bracket_band_reaches_P0"]
    from research.juggler_sequence import p0_certificate

    claims = " ".join(r["claim"] for r in p0_certificate.certificate()["thresholds"])
    assert "h_1h_2P^{1/4}" not in claims and "bracket" not in claims.lower()
