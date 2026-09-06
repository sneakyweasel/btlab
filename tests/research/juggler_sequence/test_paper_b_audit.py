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
    assert len(rows) >= 5                       # an empty ladder would satisfy every all() below
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
            # the ratios are now against the strict (n/2) denominators, so the constants in n are
            # recovered by multiplying by 15 * 2^(-1/4) and 2.6 * 2^(-3/4)
            assert abs(r["second_ratio_upper"] * 15 * 2 ** -0.25 - 27 / 4) < 1e-4, n
            if r["first_ratio_upper"] is not None:
                assert abs(r["first_ratio_upper"] * 2.6 * 2 ** -0.75 - 3 / 2) < 1e-4, n


# --- Appendix A says it enumerates every printed threshold; two are missing ---


def test_two_printed_thresholds_are_absent_from_appendix_a() -> None:
    g = A.appendix_a_gaps()
    tags = {r["tag"]: r for r in g["rows"]}
    assert not any(r["in_certificate"] for r in g["rows"])
    assert 2.0e3 < tags["L5.1(iii)-Gprime"]["least_P"] < 2.1e3
    assert 4.9e6 < tags["L5.2(b)-drift"]["least_P"] < 5.0e6
    assert g["scanned_candidates"] == 12 and g["missing"] == 2 and g["in_certificate"] == 2
    # the binding row and P_0 itself are under revision in p0_certificate, so assert the margin
    # rather than the identity: what matters is that neither gap is anywhere near the maximum
    assert g["all_gaps_below_P0"] and g["P0_binding_tag"].startswith("5")
    assert g["largest_gap_orders_below_P0"] > 5          # nothing near P_0


def test_the_step_B_constant_was_rounded_and_its_threshold_was_not() -> None:
    """(3 pi k/4) P^(-1/8) with |k| <= 2P^(1/96) is exactly (3 pi/2) P^(-11/96) = 4.7124 ..."""
    import math

    g = A.appendix_a_gaps()
    assert g["step_B_row_present"]                       # the appendix does carry this one
    assert abs(g["step_B_certificate_P_min"] - (3 * math.pi / 2) ** (96 / 11)) < 1  # at the exact constant
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


# --- P_0's binding row pairs two bounds at settings no cell realizes together ---


def test_the_binding_row_charges_the_interpolant_at_an_unreachable_setting() -> None:
    """k h1 h2 = 1 forces k = h1 = h2 = 1, and then k(h1+h2) = 2, not 2 P^(1/12)."""
    r = A.p0_pairing_check()
    tags = {x["tag"]: x for x in r["rows"]}
    assert set(tags) == {"5b-W<=c7S", "5a-W<=c7S", "5b-E<=c7S"}
    for x in r["rows"]:
        assert x["certified_least_P"] > x["same_cell_least_P"]      # the pairing only over-charges
        assert x["factor"] > 2
    assert r["direction_is_safe"]                                   # the printed P_0 is the safe side
    assert r["P0_over_estimate_factor"] > 2
    assert r["P0_with_the_pairing_fixed"] > r["largest_untouched_row_P"]


def test_the_pairing_coefficients_are_read_from_the_certificate_not_copied() -> None:
    """They are under revision; the P^(1/12) is not."""
    from research.juggler_sequence import p0_certificate

    r = A.p0_pairing_check()
    a, b = r["interpolant_first_coefficient"], r["interpolant_second_coefficient"]
    for P in (1e7, 1e11):
        rebuilt = a * P ** (-25 / 24) + b * P ** (-5 / 6)
        assert abs(rebuilt / p0_certificate.interpolant_error(P) - 1) < 1e-9, P
    assert r["ratio_exponent_gap"] == Fr(1, 12)


def test_the_same_mismatch_appears_at_st5b_qpp_and_not_at_the_c_rows() -> None:
    """h cancels between 1.85 k h P^(1/8) and 0.35 u h P^(-3/4); the c-rows cancel k correctly."""
    r = A.p0_pairing_sweep()
    assert set(r["mispaired"]) == {"5b-W<=c7S", "5a-W<=c7S", "5b-E<=c7S", "st5b-qpp"}
    assert set(r["correctly_paired"]) == {"39-c2", "39-c3", "39-c4"}
    assert r["st5b_qpp_factor"] > 20
    assert r["st5b_qpp_fixed"] < r["st5b_qpp_certified"]
    # fixing every pairing still leaves the maximum with the interpolant row, well clear of the rest
    assert r["P0_with_every_pairing_fixed"] > 10 * r["largest_untouched_row_P"]
    assert r["P0_with_every_pairing_fixed"] < r["certified_P0"]


def test_the_prose_percentages_are_current_and_the_repair_inverts_them() -> None:
    """Step 5b's "55% and 45% ... 70:30" holds under the constants now in the tree."""
    r = A.step5b_budget_split()
    assert r["prose_is_current"]
    text = _paper()
    assert r"\(55\%\)" in text and r"\(45\%\)" in text and r"\(70{:}30\)" in text
    # and the repair moves both: V takes about three quarters, and inside E the parameter-free
    # term overtakes the k(h1+h2) term, so the row stops being interpolant-dominated
    assert r["repair_inverts_the_E_split"] and r["repair_makes_the_row_V_dominated"]
    assert r["after_the_pairing_repair"]["P"] < r["as_printed"]["P"]
    for d in (r["as_printed"], r["after_the_pairing_repair"]):
        assert abs(d["W_over_budget"] - 1.0) < 1e-6      # both are evaluated at their thresholds


def test_the_kappa_optimum_does_not_move_under_the_pairing_repair() -> None:
    """kappa is pinned by P_1, where the interpolant error is 12% of W rather than 46%."""
    r = A.kappa_optimum_check()
    assert not r["optimum_moves"]
    assert abs(r["optimum_printed"]["kappa_denominator"] - 11.5) < 0.5
    assert abs(r["operating_kappa_denominator"] - 12) < 1e-9        # the paper operates at 1/12
    assert r["P0_gain_factor"] > 5 and r["P1_gain_factor"] < 1.2
    assert r["error_share_at_P0"] > 3 * r["error_share_at_P1"]
    assert r["P1_over_P0"] > 1e4                                    # P_1 is five orders above P_0
    text = _paper()
    assert r"P_1=9.8\cdot10^{18}" in text                           # the paper quotes both


def test_the_piece_boundary_term_binds_P1_and_its_constant_is_loose() -> None:
    """3.5 against a piece count of 3.0015 at P_1, amplified by the 96/7 power."""
    r = A.p1_cost_split()
    assert r["binds_at_P1"] == "boundaries"
    at19 = next(x for x in r["points"] if x["log10_P"] == 19.0)
    assert at19["boundary_share"] > 0.5
    assert abs(at19["piece_count"] - 3.0) < 0.01
    assert 0.15 < at19["piece_slack"] < 0.2
    assert r["amplification_exponent"] == Fr(96, 7)
    # and it is worth more than the interpolant repair, on the number that decides reach
    assert r["P1_gain"] > 2 > r["interpolant_repair_gain_on_P1"]
    assert r"P^{13/24}V^{-1/2}" in _paper()


def test_the_two_transition_constants_cannot_share_one_C_of_E() -> None:
    """Lemma 3.9(i) has one C(E); A.5's two terms imply 928 and 15.2."""
    r = A.p1_constant_provenance()
    assert not r["one_C_of_E_fits_both"]
    assert abs(r["C_of_E_implied_by_the_r3_term"] - 928) < 1
    assert abs(r["C_of_E_implied_by_the_r4_term"] - 15.23) < 0.05
    assert r["direction_is_against_the_paper"] and r["orders_between_them"] > 4
    text = _paper()
    assert "is never assigned a value anywhere in the paper" in text
    assert r"\le8P\,(V/(c_7S))^{1/2}" in text          # the proof's r=4 constant
    assert r"\le4PV/(c_7S)" in text                    # and its r=3 one, which A.5 does carry


def test_no_internal_threshold_reaches_the_conclusions_own_crossover() -> None:
    """P_0 and both readings of P_1 sit below 2^96, so last entry's discrepancy cannot move reach."""
    import math

    r = A.reach_ladder()
    assert r["every_internal_threshold_below_the_bare_crossover"]
    assert r["orders_of_headroom"] > 1
    assert abs(r["bare_exponent_crossover_log10"] - 96 * math.log10(2)) < 1e-9
    assert r["sharp_form_crossover_log10"] > 200          # the log form is 200 orders further out
    internal = [x for x in r["rungs"] if x["internal"]]
    assert len(internal) == 4 and max(x["log10_P"] for x in internal) < 28


# --- the coverage gap in Section 4, and the density that had no probe ---


def test_the_certified_descent_densities_check_by_direct_count() -> None:
    """Corollary 4.9's 13/16 and Theorem 6.3's 7/8, counted rather than transcribed."""
    r = A.certified_descent_density(N=3 * 10**4)
    assert r["E_count_is_exactly_floor_half"]
    assert r["all_inside_the_printed_errors"]
    assert abs(r["depth4_error"]) < 3e-3 and abs(r["depth5_error"]) < 3e-3
    assert r["thirteen_sixteenths_plus_two_thirtyseconds_is_seven_eighths"]


def test_only_the_two_asymptotic_theorems_are_left_unprobed() -> None:
    """Every checkable result of Sections 4-6 now has a probe."""
    c = A.audit_coverage()
    assert c["total"] == 21 and c["probed"] == 17
    assert set(c["uncovered"]) == {"Theorem 4.11", "Theorem 4.12"}
    assert set(c["threshold_only"]) == {"Theorem 4.1", "Proposition 4.5"}


def test_lemma_4_6_holds_at_both_ends_and_the_lower_one_saturates_at_theta() -> None:
    """The sign claim has total census power; the lower constant has 1 - max theta."""
    r = A.lemma_4_6_census(samples_per_range=15)
    assert r["both_ends_hold"] and r["sign_failures"] == 0 and r["lower_bound_failures"] == 0
    assert r["power_is_of_order_one_over_samples"]
    assert r["residual_constant_is_three_thirtyseconds"]
    for x in r["ranges"]:
        assert abs(x["max_ratio_to_lower"] - x["max_theta"]) < 3e-3, x["lo"]
    assert "Lemma 4.6" not in A.audit_coverage()["uncovered"]   # the count lives in the coverage test


# --- the level-1 kernel of OOOEOEE, measured ---


def test_the_level_one_kernel_cancels_at_square_root() -> None:
    """K_1 = sum e((27k/32) n^{33/32} {n^{3/2}}): block sums grow like sqrt(L), not like L."""
    r = A.level1_kernel_block_scaling(P=3 * 10**4, k=1)
    assert r["weight"] == "(27k/32) n^{33/32}"
    assert r["defect"] == "{n^{3/2}}"
    fitted = [b for b in r["blocks"] if b["blocks"] >= A.BLOCK_FIT_MIN_SAMPLES]
    ratios = [b["rms_K1_over_sqrtL"] for b in fitted]
    # flat in L is the signature; the instrument's own 90% interval is [0.432, 0.575]
    assert max(ratios) / min(ratios) < 1.15, ratios
    assert 0.43 < r["level1_exponent"] < 0.58, r["level1_exponent"]


def test_the_weight_is_what_makes_it_cancel() -> None:
    """On the same pass the unweighted defect e(n^{3/2}) grows like L, the kernel like sqrt(L)."""
    r = A.level1_kernel_block_scaling(P=10**5, k=1)
    fitted = [b for b in r["blocks"] if b["blocks"] >= A.BLOCK_FIT_MIN_SAMPLES]
    k1 = [b["rms_K1_over_sqrtL"] for b in fitted]
    wave = [b["rms_wave_over_sqrtL"] for b in fitted]
    # the kernel is flat, the control climbs: that contrast is the finding
    assert max(k1) / min(k1) < 1.2, k1
    assert wave[-1] / wave[0] > 1.5, wave
    assert r["wave_exponent"] > r["level1_exponent"] + 0.15


def test_the_drift_that_blocks_the_window_is_the_drift_that_decorrelates() -> None:
    """c(n) = (27k/32) n^{33/32} has c' >> 1, which is both the obstruction and the mechanism."""
    from research.juggler_sequence import paper_b_prefix_count as B

    alpha = Fr(33, 32)
    assert alpha > B.DRIFT_THRESHOLD                       # no shifted-window interval exists
    assert (3, alpha, "3/2") in [(s, g, sp) for s, g, sp in B.blocked_profile("OOOEOEE", 6)]         or alpha in [g for _s, g, _sp in B.blocked_profile("OOOEOEE", 6)]
    # c' ~ n^{1/32}: the window 1/c' is shorter than the lattice spacing at every P >= 1
    assert float(alpha) - 1 > 0
    # and the measurement says the sum cancels anyway
    r = A.level1_kernel_block_scaling(P=3 * 10**4, k=2)
    assert 0.43 < r["level1_exponent"] < 0.58, r["level1_exponent"]


def test_the_reading_is_stable_in_k() -> None:
    """The weight constant scales c but not the drift exponent, so the reading should not move."""
    xs = [A.level1_kernel_block_scaling(P=2 * 10**4, k=k)["level1_exponent"] for k in (1, 2, 4)]
    assert all(0.40 < x < 0.60 for x in xs), xs
    assert max(xs) - min(xs) < 0.15, xs


def test_paper_records_the_measurement_and_disclaims_it() -> None:
    text = io.open(PAPER, encoding="utf-8").read()
    assert "And the same drift is what makes the sum cancel" in text
    assert "paper_b_audit.level1_kernel_block_scaling" in text
    assert "0.943,0.948,0.947,0.963,0.981" in text
    assert "This is an observation and nothing" in text
    assert "no bound on \\(K_1\\) is claimed anywhere in this paper" in text


def test_corollary_4_13_holds_structurally_and_its_error_term_does_not_reach() -> None:
    """J^4 lands even in [m'^2, (m'+1)^2); the density's printed error is half the block here."""
    r = A.corollary_4_13_check(m_prime=60, nesting_samples=120)
    assert r["structural_claim_holds"] and r["structural_failures"] == 0
    assert r["nesting_failures"] == 0
    assert abs(r["nesting_worst_ratio_to_printed"] - 3 / 8) < 0.02      # the sharp constant
    assert abs(r["density"] - 1 / 16) < 3e-3
    assert r["printed_error_is_vacuous_here"]                            # m'^(-4/27) = 0.55
    assert r["m_prime_for_a_ten_percent_error"] > 1e6
    assert "Corollary 4.13" not in A.audit_coverage()["uncovered"]   # count lives in the coverage test


# --- one Weyl differencing carries the weight across the drift threshold ---


def test_the_differencing_identity_is_exact() -> None:
    """Delta_h phi = (Delta_h c) theta_1 + c(n+h)({Delta_h X} - kappa), kappa in {0,1}."""
    r = A.level1_differencing_identity(P=10**6, trials=24)
    assert r["identity_exact"], r["worst_residual"]
    assert r["worst_residual"] < 1e-40
    assert r["kappa_characterisation_mismatches"] == 0
    # kappa is genuinely bimodal, not a degenerate branch
    assert 0.1 < r["kappa_one_fraction"] < 0.9, r["kappa_one_fraction"]


def test_differencing_crosses_the_drift_threshold() -> None:
    """The weight goes from 33/32, above the threshold, to 1/32, below it."""
    from research.juggler_sequence import paper_b_prefix_count as B

    r = A.level1_differencing_identity(P=10**5, trials=8)
    assert r["weight_exponent"] == Fr(33, 32) > B.DRIFT_THRESHOLD
    assert r["differenced_weight_exponent"] == Fr(1, 32) < B.DRIFT_THRESHOLD
    assert r["differencing_crosses_the_threshold"]
    # the differenced weight is the derivative of the original, times h
    assert Fr(27, 32) * Fr(33, 32) == Fr(891, 1024)
    assert Fr(33, 32) - 1 == Fr(1, 32)


def test_the_frozen_defect_is_slow_where_the_original_is_fast() -> None:
    """{Delta_h X} moves at h P^{-1/2}; theta_1 wraps every step. That is the whole gain."""
    P = 1.5 * 10**6
    theta_drift = 3 * P**0.5                 # X'(n) * 2 over odd n
    beta_drift = 0.75 * P**-0.5              # d/dn of Delta_1 X
    assert theta_drift > 3000                # theta wraps thousands of times per step
    assert beta_drift < 1e-3                 # beta is constant on runs of ~1/beta_drift
    assert 1 / beta_drift > 1000
    # the run length is the b-run of Lemma 5.1(iii), P^{1/2}/h
    assert abs((1 / beta_drift) / (P**0.5 / 0.75) - 1) < 1e-9


def test_paper_records_the_route_and_the_gap() -> None:
    text = io.open(PAPER, encoding="utf-8").read()
    assert "What one differencing does" in text
    assert "It is Weyl differencing" in text
    assert "carries the weight" in text and "across the very threshold" in text
    assert "This is an accounting and not a proof" in text
    assert "P^{1-1/48}" in text                 # what one differencing would have to reach
    assert "Step 1 followed by Lemma 3.5" in text


def test_lemma_4_10s_constant_is_sharp_and_free_where_it_is_used() -> None:
    """1 + 2 pi TV is attained in the limit, and TV is 1.5e-5 at P_0."""
    r = A.lemma_4_10_sharpness(random_trials=150)
    assert r["constant_is_sharp"] and r["best_adversarial_ratio"] > 0.999
    assert r["random_search_would_miss_it"]                  # random reaches about 0.92
    assert r["the_twist_is_free_in_application"] and r["factor_at_P0"] < 1.001
    assert r["TV_exponent"] == Fr(-5, 16)
    for x in r["adversarial"]:
        assert x["ratio"] <= 1 + 1e-9, x                     # and the lemma holds on every one


# --- Section 3's classical inputs, at the constants the paper prints for them ---


def test_the_two_classical_inputs_hold_at_their_printed_constants() -> None:
    """The A-process display and Erdos-Turan, both used throughout Sections 4-6."""
    r = A.classical_inputs_check(P=800, H=20)
    assert r["a_process_holds_everywhere"]
    assert r["a_process_dominates_the_classical_form"]
    assert r["looseness_factorises_as_two_times_four"]          # 1/2 times 1/4 at a_n = 1
    assert abs(r["extremal_lhs_over_classical"] - 0.5) < 0.06
    assert abs(r["extremal_printed_over_classical"] - 4) < 0.6
    assert r["erdos_turan_constant_below_one"]
    assert r["erdos_turan_worst_implied_constant"] < 0.5


# --- the one-differencing balance, and the curvature it turns on ---


def test_the_run_carries_kh_not_c_double_prime() -> None:
    """What a b-run freezes is the integer floor(Delta_h X), so lambda ~ k h P^(-15/32)."""
    r = A.level1_run_curvature(P=10**6, trials=8)
    assert r["tracks_the_run_scale"], r["ratio_to_kh_Pm15_32"]
    assert r["cpp_is_wrong_by_the_run_length"], r["ratio_to_k_Pm31_32"]
    lo, hi = r["ratio_to_kh_Pm15_32"]
    assert 0.98 < lo <= hi < 1.0
    # the gap between the two candidates is the run length P^{1/2}/h
    assert Fr(-15, 32) - Fr(-31, 32) == Fr(1, 2)


def test_the_balance_reaches_the_requirement() -> None:
    """With the run curvature the smooth term has 41/12 times the room it needs."""
    r = A.level1_one_differencing_balance()
    assert r["stationary_points_per_cell"] == Fr(1, 32) > 0   # the test is the right one
    assert r["U_bound"] == (Fr(49, 64), Fr(1, 2))
    assert r["H_exponent"] == Fr(5, 32)
    assert r["K1_exponent"] == Fr(59, 64)
    assert r["saving_at_k_one"] == Fr(5, 64)
    assert r["saving_uniform_in_k"] == Fr(41, 576)
    assert r["required_after_one_differencing"] == Fr(1, 48) == Fr(12, 576)
    assert r["room"] == Fr(41, 12)
    assert r["reaches_the_requirement"]


def test_the_posed_accounting_falls_short_and_why() -> None:
    """With c'' as the curvature the same machine returns 1/256, short by 16/3."""
    r = A.level1_one_differencing_balance(lam_P=Fr(-31, 32), lam_h=Fr(0))
    assert r["saving_at_k_one"] == Fr(1, 256)
    assert not r["reaches_the_requirement"]
    assert Fr(1, 48) / Fr(1, 256) == Fr(16, 3)
    # and the reason: fewer than one stationary point per cell, so lambda^(-1/2) is
    # charging for a stationary point the cell does not contain
    assert r["stationary_points_per_cell"] == Fr(-15, 32) < 0
    assert r["U_bound"][0] == Fr(63, 64)                      # against 49/64 corrected


def test_the_saving_is_not_where_this_stands_or_falls() -> None:
    """The balance prices the smooth term only; the two non-smooth ones are the problem."""
    r = A.level1_one_differencing_balance()
    # one differencing halves the saving, so the differenced sum reaches P^{1-2*saving}
    assert 2 * r["saving_at_k_one"] == Fr(5, 32)
    assert r["saving_uniform_in_k"] > Fr(1, 48)
    text = io.open(PAPER, encoding="utf-8").read()
    assert "So the balance is not where this stands or falls" in text
    assert "prices only that term" in text


# --- what the audit as a whole would and would not notice ---


def test_the_audit_knows_what_a_one_percent_cut_would_set_off() -> None:
    """Three regimes: total power on identities, 1/samples on saturating bounds, none on loose ones."""
    r = A.perturbation_sensitivity(samples_per_range=8)
    assert r["policed_total"] == 11
    assert 1 <= r["policed_detecting"] <= 5
    assert len(r["saturating"]) >= 2 and len(r["structurally_loose"]) >= 1
    # the two bracket bands cannot be policed at any sample size: their extremes do not move
    brackets = [x for x in r["policed_constants"]
                if x["constant"].startswith("L5.1(iii)") and x["side"] == "upper"]
    assert len(brackets) == 2
    # neither moves with sampling, but they are not both loose: under the strict pointwise
    # transcription the first is sharp to 3% and only the second is far from its true value
    for x in brackets:
        assert not x["moved_with_sampling"], x["constant"]
    first = next(x for x in brackets if x["constant"].startswith("L5.1(iii) first"))
    second = next(x for x in brackets if x["constant"].startswith("L5.1(iii) second"))
    assert first["smallest_detectable_cut"] < 0.05 and first["regime"] == "structurally sharp"
    assert second["smallest_detectable_cut"] > 0.3 and second["regime"] == "structurally loose"
    # P_0 is a solved threshold, so every constant moves it past the two-figure boundary
    assert r["every_P0_constant_moves_it_past_the_boundary"]
    assert r["P0_two_figure_resolution_at_a_boundary"] < 0.02


# --- the r=4 reading, settled on instances rather than passages ---


def test_A5s_transition_bound_survives_on_admissible_instances() -> None:
    """A.5's (4, 1) holds on every instance that satisfies Lemma 3.9's own hypothesis."""
    r = A.lemma_3_9_admissible_search(trials=120, grid=400)
    assert r["admissible"] > 0.8 * r["trials"]
    assert r["nonempty_sublevel"] == r["admissible"]
    assert r["A5_bound_holds_on_every_admissible_instance"]
    assert r["worst_measure_over_A5_bound"] < 0.6
    assert r["r4_branch_fires"]          # not surviving by the branch never firing
    assert r["room_left"] > 1.5


def test_the_r3_length_separates_A6s_constant_from_the_proofs() -> None:
    """The local bound is 2 V n/(c_7 S): A.6's 2 P is the bottom of the block, the proof's 4 P the top."""
    r = A.lemma_3_9_admissible_search(trials=400, grid=1000)
    assert r["worst_over_the_local_r3_form"] < 1.05          # the local form is the real bound
    assert r["worst_over_the_local_r3_form"] > 0.5           # 0.95 at 1500 trials; sampling-limited
    assert r["A6_r3_constant_is_exceeded"]                   # 2 P V/(c_3 S) is not safe over (P, 2P]
    assert r["proof_r3_constant_holds"]                      # 4 P V/(c_7 S) is, with a factor of two
    assert abs(r["worst_over_the_proof_r3_constant"] - 0.5 * r["worst_over_A6_r3_constant"]) < 1e-6


# --- every P-stated pointwise bound, and the end of the block it must assume ---


def test_every_P_stated_bound_uses_its_strict_transcription() -> None:
    """Three bounds are stated in P; the brackets need n below and n/2 above, M_1 neither."""
    r = A.pointwise_bound_inventory(samples_per_range=8)
    assert r["count"] == 5 and r["all_respect_their_side"]
    assert r["did_not_go_blind"] and r["samples_inspected"] >= 100
    assert r["surface_unchanged"]           # a new P-dependent bound has to update the table
    by = {x["bound"]: x for x in r["bounds"]}
    assert abs(by["L5.1(iii) first bracket, lower"]["extreme_ratio"] - 1.0) < 2e-3   # attained
    assert by["L5.1(iii) first bracket, upper"]["extreme_ratio"] < 1.0
    assert by["L5.1(iii) second bracket, lower"]["extreme_ratio"] > 4
    assert by["L5.1(iv) M_1"]["strict_transcription"].startswith("P = n")
    assert by["L5.1(iv) M_1"]["exponent"] == "-7/8"


# --- the draft-history family, and where each member sits ---


def test_the_draft_history_family_is_where_it_belongs() -> None:
    """The referee's phrase is gone; the family around it is mostly the appendix's own subject."""
    r = A.draft_history_markers()
    assert r["the_referees_phrase_is_gone"]
    assert r["total"] >= 8
    assert r["in_appendix"] >= 5                     # A.5 and A.6 exist to compare choices
    assert r["in_body"] <= 4 and r["body_mathematical"] >= 2
    # two body sentences are status rather than mathematics; a third would want looking at
    assert len(r["body_needing_a_look"]) <= 2, r["body_needing_a_look"]


# --- the trust-boundary table, read as data ---


def test_section_four_and_the_trust_table_agree() -> None:
    """Five identifiers, all in the Lemma 5.1 row and all declared in MasterIdentity.lean."""
    r = A.trust_boundary_rows()
    assert len(r["section4_identifiers"]) == 5
    assert r["section4_all_in_the_table"] and r["section4_all_declared"]
    assert r["largest_lean_row"].startswith("Lem. 5.1") and r["largest_lean_count"] >= 14


def test_the_table_has_no_sampled_warrant_and_flags_where_the_proof_stands_alone() -> None:
    r = A.trust_boundary_rows()
    assert r["table_has_no_sampled_column"]          # its warrants are proof, Lean, classical
    assert r["row_count"] == r["rows_with_lean"] + len(r["rows_on_the_human_proof_alone"]) + len(
        r["rows_quoted_from_elsewhere"])
    assert set(r["flagged_rows"]) == {"Lem. 5.2(i), (ii), (iii)", "Thm. 5.3 kernel cancellation"}
    assert "Lem. 5.2(i), (ii), (iii)" in r["rows_on_the_human_proof_alone"]
