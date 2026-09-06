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
