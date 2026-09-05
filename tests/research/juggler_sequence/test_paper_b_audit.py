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
