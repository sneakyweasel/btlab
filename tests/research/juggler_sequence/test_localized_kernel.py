"""The kernel theorem localizes: exponents unchanged, only the length is new."""

from __future__ import annotations

from fractions import Fraction as F

from research.juggler_sequence import localized_kernel as L


def test_the_cost_tables_reproduce_the_printed_exponents() -> None:
    """The audit is only worth as much as its inputs: the tabulated maxima must be
    exactly the manuscript's P^{15/16} for Lemma 5.2(i) and P^{23/24} for T_2."""
    assert L.max_dyadic(L.LEMMA_52i) == F(15, 16) == L.PRINTED_LEMMA_52i
    assert L.max_dyadic(L.THEOREM_53) == F(23, 24) == L.PRINTED_T2
    assert L.summary()["cost_tables_reproduce_printed"]["ok"] is True


def test_every_cost_is_classified_and_absolute_costs_are_never_lengths() -> None:
    for costs in (L.LEMMA_52i, L.THEOREM_53):
        for c in costs:
            assert c.source, c.name
            assert c.proportional == c.dyadic - 1
            if c.absolute is not None:
                # a unit cost is an inverse root or a transition term, never a length:
                # it stays below the interval the theorem is stated on
                assert 0 < c.absolute < L.COMPANION_Y, (c.name, c.absolute)
                assert c.absolute <= c.dyadic, (c.name, c.absolute)


def test_the_dyadic_specialization_returns_the_paper() -> None:
    """At y = 1 the localized bookkeeping must give back P^{23/24}, P^{47/48}, P^{95/96}."""
    ch = L.chain(F(1))
    assert F(1) + ch["T2"][0] == F(23, 24)
    assert F(1) + ch["T1"][0] == F(1) - F(1, 48)
    assert F(1) + ch["K"][0] == F(1) - F(1, 96)
    assert L.summary()["dyadic_specialization"]["reproduces_printed"] is True


def test_the_claim_c_balance_is_against_the_shift_average_and_is_unique() -> None:
    """H_3 = t^{1/3}P^{1/12} balances 2P^2/H_3 against the h_3-average of printed term 2,
    and against that term alone; this is what makes the chain degree-one homogeneous."""
    cb = L.claim_c_balance()
    assert cb["balancing_terms"] == ["2: (h/u)^{1/2} P^{7/8}"]
    assert cb["unique_balancing_term"] is True
    assert cb["all_dominated"] is True
    assert cb["output_is_printed"] is True


def test_the_saving_is_the_printed_exponent_at_the_companion_length() -> None:
    ch = L.chain(L.COMPANION_Y)
    assert ch["K"][0] == F(-1, 96)
    assert ch["lemma_52ii"][0] == F(-1, 24)
    assert ch["T1"][0] == F(-1, 48)


def test_the_absolute_chain_is_the_geometric_mean_recursion() -> None:
    """Each A-process sends an absolute A to (Y A)^{1/2}; three of them give (7y+A_1)/8."""
    y = L.COMPANION_Y
    a1 = L.absolute_exponent(L.LEMMA_52i)
    assert a1 == F(25, 48)
    a = a1
    for _ in range(3):
        a = (y + a) / 2
    assert a == L.absolute_tail(y) == F(533, 768)
    assert L.chain(y)["K"][1] == F(533, 768)


def test_the_companion_length_clears_the_threshold_with_margin() -> None:
    assert L.threshold() == F(29, 48)
    assert L.COMPANION_Y == F(23, 32) > F(29, 48)
    ch = L.chain(L.COMPANION_Y)
    assert ch["absolute_dominated"] is True
    assert ch["target"] == F(17, 24)
    assert ch["margin"] == F(11, 768) > 0


def test_the_threshold_is_sharp_for_this_bookkeeping() -> None:
    """At 29/48 the two exponents are exactly equal, so the theorem needs a delta:
    above the threshold the absolute term is dominated, below it is not."""
    thr = L.threshold()
    assert L.absolute_tail(thr) == thr - F(1, 96)
    assert L.chain(thr)["margin"] == 0
    for y, ok in ((thr + F(1, 1000), True), (thr, False), (thr - F(1, 1000), False)):
        assert L.chain(y)["absolute_dominated"] is ok, y


def test_the_kernel_does_not_localize_as_far_as_the_depth_three_theorems() -> None:
    """Section 3.5 reaches P^{1/2}; the kernel stops at P^{29/48} because of the
    transition term. The companion's intervals are longer, so nothing it needs is lost."""
    assert F(1, 2) < L.threshold() == F(29, 48) < L.COMPANION_Y
    assert L.chain(F(1, 2))["absolute_dominated"] is False
    assert L.summary()["threshold_above_one_half"] is True


def test_the_slow_twist_costs_a_factor_one_plus_little_o() -> None:
    tv = L.twist_total_variation(L.COMPANION_Y)
    assert tv == F(1, 48) + F(23, 32) + F(1, 24) - F(23, 16) == F(-21, 32)
    assert tv < 0
    assert L.summary()["twist"]["negligible"] is True


def test_the_largest_absolute_cost_is_the_transition_term() -> None:
    """Lemma 3.8's third term carries no window-length factor, so one window's worth of
    it does not scale. That single cost sets the threshold."""
    worst = L.worst_absolute(L.LEMMA_52i)
    assert worst.absolute == F(25, 48)
    assert "transition term" in worst.name
    assert L.threshold() == worst.absolute + 8 * L.SAVING
    # at the outer level the middle band's piece boundaries are the worst, and smaller
    # than what Lemma 5.2(i) already contributes through the nesting
    assert L.worst_absolute(L.THEOREM_53).absolute == F(37, 96)
    assert F(37, 96) < (L.COMPANION_Y + F(25, 48)) / 2


def test_the_summary_records_the_statement_and_what_it_unlocks() -> None:
    s = L.summary()
    assert s["companion_above_threshold"] is True
    assert s["saving_is_printed_exponent"] is True
    assert s["absolute_tail_matches_closed_form"] is True
    assert s["unlocks"] == ["OOOEEE", "OOEOEE"]
    assert s["balancing_choices_unchanged"] == {"H1": "1/48", "H2": "1/24", "H3": "1/12"}


def test_every_displayed_exponent_that_could_bind_is_accounted_for() -> None:
    """The completeness of the cost tables is the one non-mechanical input, so it is
    checked: every P-exponent at least 1/4 displayed in either proof is either a
    tabulated cost or is named as a count, length, parameter, hypothesis or an
    intermediate step. Nothing is left over."""
    s = L.summary()
    assert s["coverage_complete"] is True
    for which in ("lemma_52i", "theorem_53"):
        c = L.coverage(which)
        assert c["unexplained"] == [], (which, c["unexplained"])
        assert c["displayed_at_or_above_floor"] >= 15
        assert c["tabulated_as_a_cost"] >= 10


def test_the_extraction_reads_the_manuscript_and_finds_the_landmarks() -> None:
    """The coverage check is only meaningful if it is reading the right text."""
    for which, landmarks in (("lemma_52i", (F(29, 32), F(37, 48), F(5, 16))),
                             ("theorem_53", (F(23, 24), F(89, 96), F(37, 96)))):
        seen = L.displayed_exponents(which)
        assert len(seen) > 25, which
        for m in landmarks:
            assert m in seen, (which, m)
