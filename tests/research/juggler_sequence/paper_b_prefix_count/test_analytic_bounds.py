"""Historical Paper B prefix audit: analytic bounds."""
from __future__ import annotations
import math
from fractions import Fraction
import pytest
from research.juggler_sequence import paper_b_prefix_count as B



@pytest.mark.slow
@pytest.mark.parametrize("seed", [0, 1, 2])
def test_off_diagonal_integral_obeys_the_two_arc_bound(seed: int) -> None:
    """``A{x+l} - B{y+l}`` has three pieces on [0,1) but two arcs on the circle.

    The first and last pieces carry the same linear branch -- their constants differ by
    exactly the slope -- so the bound is ``2/(pi|A-B|)``, not ``3/(pi|A-B|)``.
    """
    import numpy as np

    rng = np.random.default_rng(seed)
    n = 200_000
    lam = (np.arange(n) + 0.5) / n
    worst = 0.0
    for _ in range(40):
        a, b = rng.uniform(-500, 500, 2)
        if abs(a - b) < 1:
            continue
        x, y = rng.random(2)
        phase = a * ((x + lam) % 1.0) - b * ((y + lam) % 1.0)
        worst = max(worst, abs(np.exp(2j * np.pi * phase).mean()) * abs(a - b))
    assert worst <= 2 / math.pi + 1e-3, worst


def test_the_sawtooth_fourier_modes_are_the_monomial_waves() -> None:
    """e(r{x}) = e(rx) for integer r, since r*floor(x) is an integer."""
    from mpmath import mp, mpf, pi, floor, power, exp
    mp.dps = 40
    for x in (mpf("3.7"), mpf("1234.56789"), power(mpf(1000003), mpf(3) / 2)):
        for r in (1, 2, -5, 37):
            lhs = exp(2j * pi * r * (x - floor(x)))
            rhs = exp(2j * pi * r * x)
            assert abs(lhs - rhs) < mpf(10) ** -25, (x, r)


def test_the_gap_is_a_frequency_range_of_P_95_over_96() -> None:
    """Theorems 4.4/4.7 reach P^{1/24}; the kernel's mass sits at P^{33/32}."""
    _, exponent = B.defect_coefficient("OOOEOEE", 6, 1)
    assert exponent == Fraction(33, 32)
    assert exponent - Fraction(1, 24) == Fraction(95, 96)


def test_the_drift_threshold_is_a_sub_lattice_window() -> None:
    """Coefficient exponent c gives a window of length P^{1-c}; above 1 it holds no integer."""
    _, exponent = B.defect_coefficient("OOOEOEE", 6, 1)
    assert 1 - exponent == Fraction(-1, 32)
    assert exponent > B.DRIFT_THRESHOLD
    # and the unblocked coefficients of the same word do give windows of positive length
    for s in (2, 4):
        _, e2 = B.defect_coefficient("OOOEOEE", 6, s)
        assert e2 < B.DRIFT_THRESHOLD and 1 - e2 > 0, s


def test_the_generator_reproduces_the_classical_pairs() -> None:
    pairs = B.van_der_corput_pairs()
    assert (Fraction(0), Fraction(1)) in pairs                 # trivial
    assert (Fraction(1, 2), Fraction(1, 2)) in pairs           # B of trivial
    assert (Fraction(1, 6), Fraction(2, 3)) in pairs           # AB of trivial
    assert all(k >= 0 and l >= 0 for k, l in pairs)


def test_the_best_pair_at_the_kernel_frequency() -> None:
    """Phase size P^{81/32} is e(r n^{3/2}) at r ~ k P^{33/32}."""
    pair, value, saving = B.best_monomial_bound(Fraction(81, 32))
    assert pair == (Fraction(1, 11), Fraction(3, 4))
    assert value == Fraction(313, 352)
    assert saving == Fraction(39, 352)
    assert value < 1                                            # nontrivial


def test_a_quarter_of_the_mode_saving_clears_one_over_ninetysix() -> None:
    """The chain quarters a saving, so it needs 1/24 to reach P^{1-1/96}."""
    _, _, saving = B.best_monomial_bound(Fraction(81, 32))
    assert saving / 4 > Fraction(1, 96)
    assert saving > Fraction(1, 24)
    assert abs(float(saving / 4 / Fraction(1, 96)) - 2.66) < 0.01
    # and the chain's own arithmetic agrees
    assert B.differencing_chain(saving)["saving"] == saving / 4


def test_the_phase_size_is_the_wave_exponent() -> None:
    """P^{81/32} is e_5 of both winners -- the size is not an extra assumption."""
    for word in ("OOOEOEE", "OOOEOEOE"):
        assert B.iterate_exponents(word)[4] == Fraction(81, 32), word
        _, coeff_exp = B.defect_coefficient(word, 6, 1)
        assert coeff_exp + Fraction(3, 2) == Fraction(81, 32), word


def test_the_closed_forms_return_every_printed_constant() -> None:
    """At alpha = 9/8 the forms are the paper's own rationals, corrected one included."""
    a = Fraction(3, 4)                                   # c(nu) = (3k/4) nu^{9/8}
    assert a * B.composite("5a", Fraction(9, 8)) == Fraction(729, 512)
    assert a * B.composite("E", Fraction(9, 8)) == Fraction(-243, 512)
    # the anchor 2c'G' + cG'' -- the corrected constant of the erratum
    assert a * Fraction(3, 4) * B.composite("anchor", Fraction(9, 8)) == Fraction(-27, 128)
    assert 9 * a * Fraction(3, 4) * B.composite("anchor", Fraction(9, 8)) == Fraction(-243, 128)
    # the three-term (cG_F)'' -- what the manuscript printed
    assert a * Fraction(3, 4) * B.composite("cG", Fraction(9, 8)) == Fraction(-135, 1024)
    assert 9 * a * Fraction(3, 4) * B.composite("cG", Fraction(9, 8)) == Fraction(-1215, 1024)
    # the printed two-way splits
    assert [a * x for x in B.composite_terms("5a", Fraction(9, 8))] \
        == [Fraction(945, 512), -Fraction(27, 64)]
    assert [a * x for x in B.composite_terms("E", Fraction(9, 8))] \
        == [Fraction(81, 512), -Fraction(81, 128)]


def test_the_anchor_is_the_three_term_form_less_c2_G() -> None:
    """(c(G-J))'' = (cG)'' - c''J_F, and c''G_F is the 81/1024 that separates them."""
    for num in range(17, 60):
        alpha = Fraction(num, 16)
        assert B.composite("cG", alpha) - B.composite("anchor", alpha) == alpha * (alpha - 1)
        assert B.composite("cG", alpha) == (alpha - Fraction(3, 4)) * (alpha - Fraction(7, 4))
    a = Fraction(3, 4)
    c2G = a * Fraction(3, 4) * Fraction(9, 8) * (Fraction(9, 8) - 1)
    assert c2G == Fraction(81, 1024)
    assert Fraction(-135, 1024) - c2G == Fraction(-216, 1024) == Fraction(-27, 128)


def test_the_zeros_separate_the_two_objects() -> None:
    """The anchor is linear with the single zero 7/8; (cG)'' is the quadratic with 3/4 and 7/4."""
    assert B.composite_roots("anchor") == [0.875]
    assert B.composite("anchor", Fraction(7, 8)) == 0
    assert B.composite_roots("cG") == [0.75, 1.75]
    for name in ("5a", "E"):
        for r in B.composite_roots(name):
            near = Fraction(r).limit_denominator(10 ** 7)
            assert B.composite(name, near) != 0
            assert abs(float(B.composite(name, near))) < 1e-5
    assert abs(B.composite_roots("5a")[1] - (10 ** 0.5 - 1) / 4) < 1e-12
    assert abs(B.composite_roots("E")[1] - (2 + 13 ** 0.5) / 4) < 1e-12
    # every blocked exponent exceeds 1, so no zero is reachable
    assert min(B.composite_screen(9)) is not None
    assert all(g > 1 for d in range(4, 10) for w in B.surviving_words(d) if len(w) == d
               for t in range(2, d + 1) for _s, g, _sp in B.blocked_profile(w, t))


def test_the_level_one_exponent_stays_the_same_order() -> None:
    """33/32 does not vanish on any composite: better on Step E, half again worse on the anchor."""
    a = Fraction(27, 32)                                 # c(nu) = (27k/32) nu^{33/32}
    assert a * B.composite("5a", Fraction(33, 32)) == Fraction(84321, 65536)
    assert a * B.composite("E", Fraction(33, 32)) == Fraction(-43983, 65536)
    assert 9 * a * Fraction(3, 4) * B.composite("anchor", Fraction(33, 32)) == Fraction(-10935, 8192)
    proved = [B.cancellation_factor(n, Fraction(9, 8)) for n in B.COMPOSITES]
    level1 = [B.cancellation_factor(n, Fraction(33, 32)) for n in B.COMPOSITES]
    assert [round(float(x), 2) for x in proved] == [1.59, 1.67, 8.00]
    assert [round(float(x), 2) for x in level1] == [1.74, 1.12, 12.20]
    assert level1[1] < proved[1]                          # Step E: 1.12 against 1.67
    assert max(level1) < 1.6 * max(proved)                # same order, not the same number


@pytest.mark.slow
def test_no_frontier_exponent_is_composite_degenerate() -> None:
    """222 blocked exponents to depth 13, none a zero, all inside the errors the proofs carry."""
    worst = B.composite_screen(13)
    assert worst["5a"][0] == Fraction(4131, 4096)
    assert worst["E"][0] == Fraction(45, 32)             # OOEOOEE's blocked exponent
    assert worst["anchor"][0] == Fraction(4131, 4096)
    assert round(float(worst["5a"][1]), 2) == 1.78
    assert float(worst["E"][1]) == 129.0
    assert round(float(worst["anchor"][1]), 2) == 14.10
    p0 = 8.9e13
    assert float(worst["5a"][1]) < p0 ** 0.25
    assert float(worst["E"][1]) < p0 ** 0.25 < 3072
    assert float(worst["anchor"][1]) < p0 ** (15 / 16)


def test_the_hard_word_is_the_one_with_the_worst_composite() -> None:
    """45/32 is OOEOOEE's, and its Step E factor is 77 times the proved exponent's."""
    assert (3, Fraction(45, 32), "sqrt") in B.blocked_profile("OOEOOEE", 6)
    ratio = B.cancellation_factor("E", Fraction(45, 32)) / B.cancellation_factor("E", Fraction(9, 8))
    assert 76 < float(ratio) < 78
    worst = {a: max(B.cancellation_factor(n, a) for n in B.COMPOSITES)
             for a in (Fraction(9, 8), Fraction(33, 32), Fraction(27, 16), Fraction(45, 32))}
    order = sorted(worst, key=lambda a: worst[a])
    assert order == [Fraction(27, 16), Fraction(9, 8), Fraction(33, 32), Fraction(45, 32)]
    # the first three are within a factor of four; the fourth is an order of magnitude out
    assert float(worst[order[2]] / worst[order[0]]) < 4
    assert float(worst[order[3]] / worst[order[2]]) > 10


def test_the_vaaler_budget_reaches_the_requirement() -> None:
    """J = P^{5/22} and a saving of 5/22, against the 1/48 the differenced sum needs."""
    r = B.vaaler_truncation_budget()
    assert r["J_exponent"] == Fraction(5, 22)
    assert r["saving"] == Fraction(5, 22)
    assert r["required"] == Fraction(1, 48)
    assert r["room"] == Fraction(120, 11)
    assert r["reaches_the_requirement"]
    # the classical pair alone already clears it eight times over
    assert r["classical_pair_saving"] == Fraction(1, 6)
    assert r["classical_pair_saving"] / r["required"] == 8


def test_the_budget_formula_is_the_balance() -> None:
    """delta = (1 - k/2 - l)/(k+1) is P/J against J^k P^{k/2+l}, and the trivial pair gives none."""
    for kap, ell in B.van_der_corput_pairs(6):
        num = 1 - kap / 2 - ell
        if num <= 0:
            continue
        d = num / (kap + 1)
        # at J = P^d the two sides of the balance agree
        assert 1 - d == d * kap + kap / 2 + ell
    assert 1 - Fraction(0) / 2 - Fraction(1) == 0          # trivial pair: no saving, as it must


def test_both_unpriced_terms_are_one_family() -> None:
    """(Delta_h c) theta_1 shifts j by at most k h P^{1/32}, which J dominates."""
    r = B.vaaler_truncation_budget()
    assert r["shift_from_delta_h_c"] == Fraction(11, 96) == Fraction(1, 24) * 2 + Fraction(1, 32)
    assert r["J_dominates_the_shift"]
    assert r["J_exponent"] - r["shift_from_delta_h_c"] == Fraction(119, 1056)


def test_the_shifted_window_works_on_beta_where_it_failed_on_c() -> None:
    """beta drifts at exponent -1/2, far below the threshold that 33/32 sat above."""
    r = B.vaaler_truncation_budget()
    assert r["window_reach"] == Fraction(71, 264) < Fraction(1, 2)
    assert r["window_holds_integers"]
    assert r["window_margin"] == Fraction(61, 264)
    # the contrast: c has coefficient exponent 33/32, above the drift threshold; beta has -1/2
    assert Fraction(33, 32) > B.DRIFT_THRESHOLD > Fraction(-1, 2)


def test_this_requirement_is_inside_the_hull() -> None:
    """delta >= 1/48 is 25p + 48q <= 47, against a hull minimum of 34.5."""
    r = B.two_monomial_requirement()
    assert r["here_line"] == 47
    assert r["here_hull_min"] == Fraction(69, 2)
    assert r["here_is_inside_the_hull"]
    assert abs(float(r["here_margin"]) - 0.266) < 0.001
    # the rearrangement itself: delta = (1 - p/2 - q)/(p+1) >= 1/48
    for p, q in ((Fraction(1, 6), Fraction(2, 3)), (Fraction(13, 84), Fraction(55, 84))):
        delta = (1 - p / 2 - q) / (p + 1)
        assert (delta >= Fraction(1, 48)) == (25 * p + 48 * q <= 47)


def test_the_notes_requirement_is_below_its_hull() -> None:
    """(5/4)p + q < 2/3 against a hull minimum of 0.8606: a subconvexity ask."""
    r = B.two_monomial_requirement()
    assert r["note_line"] == Fraction(2, 3)
    assert r["note_hull_min"] == Fraction(1673, 1944)
    assert not r["note_is_inside_the_hull"]
    assert r["note_literature_min"] == Fraction(95, 112)
    assert Fraction(95, 112) > Fraction(2, 3)          # even with Huxley and Bourgain
    for d in r["named"].values():
        assert not d["clears_note"] or d["phi"] < Fraction(2, 3)
    assert not r["named"]["Bourgain"]["clears_note"]
    assert r["named"]["Bourgain"]["clears_here"]


def test_only_the_trivial_neighbourhood_fails_here() -> None:
    """Three of fifty-six fail, and they are the trivial pair and what crawls back to it."""
    r = B.two_monomial_requirement()
    assert len(r["failing_pairs"]) == 3
    assert (Fraction(0), Fraction(1)) in r["failing_pairs"]
    assert r["failures_are_the_trivial_neighbourhood"]
    assert all(q >= Fraction(251, 255) for _p, q in r["failing_pairs"])
    assert r["named"]["trivial"]["psi"] == 48 and not r["named"]["trivial"]["clears_here"]
    for nm in ("van der Corput", "Weyl", "Bourgain"):
        assert r["named"][nm]["clears_here"], nm


def test_domination_is_not_what_separates_them() -> None:
    """Both problems are led by one monomial; that resemblance is not the difference."""
    d = B.two_monomial_domination()
    assert d["here_worst_corner"] == Fraction(41, 96) > 0
    assert d["here_top_of_range"] == Fraction(691, 1056)
    assert d["note_ratio"] == Fraction(71, 60) > 0
    assert d["here_dominated"] and d["note_dominated"]
    # the worst corner is j = 1 with k at its cap
    assert Fraction(3, 2) - Fraction(1, 24) - Fraction(33, 32) == Fraction(41, 96)
