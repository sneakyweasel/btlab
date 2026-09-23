"""Historical Paper B prefix audit: counting."""
from __future__ import annotations
import math
import pytest
from research.juggler_sequence import paper_b_prefix_count as B

from .helpers import (
    surviving_words,
)


def test_count_agrees_with_direct_enumeration() -> None:
    for d in range(1, 15):
        assert B.non_contracting(d) == len(surviving_words(d)), d


def test_depth_five_reproduces_corollary_6_4() -> None:
    """The four survivors give certificate density 7/8, which Corollary 6.4 reaches by
    counting contractors rather than words.  Two of the four are the open OOOO* split."""
    words = surviving_words(5)
    assert words == ["OOOOO", "OOOOE", "OOOEO", "OOEOO"]
    assert 1 - len(words) / 2 ** 5 == 7 / 8
    assert sum(1 for w in words if w.startswith("OOOO")) == 2


def test_depth_six_buys_nothing_without_depth_five() -> None:
    """All eight children of the depth-five survivors survive, so the density is 7/8 again."""
    assert B.non_contracting(6) == 8
    assert 1 - 8 / 2 ** 6 == 7 / 8


def test_every_e_rooted_word_contracts_immediately() -> None:
    """The step the proposition opens with: 3^0 < 2."""
    for d in range(1, 12):
        assert all(w.startswith("O") for w in surviving_words(d))


def test_hoeffding_is_an_upper_bound_at_every_depth() -> None:
    for d in range(1, 41):
        assert B.non_contracting(d) <= B.hoeffding_bound(d), d


def test_two_losses_compound_and_neither_touches_the_rate() -> None:
    rows = {r["d"]: r for r in B.table(40)}
    # loss 1: dropping the prefix constraint
    assert abs(rows[5]["endpoint_only"] / rows[5]["N_d"] - 1.50) < 0.01
    assert abs(rows[24]["endpoint_only"] / rows[24]["N_d"] - 4.44) < 0.01
    # both together
    for d, want in ((5, 6.7), (10, 11.4), (40, 43.6)):
        got = rows[d]["density_hoeffding"] / rows[d]["density_exact"]
        assert abs(got - want) < 0.1, (d, got)
    # the exponential rate is essentially unchanged
    assert abs(2 * B.chernoff_rate() - 1.9318) < 5e-4
    assert abs(2 * math.exp(-B.HOEFFDING_C) - 1.9326) < 5e-4
    assert 2 * B.chernoff_rate() < 2 * math.exp(-B.HOEFFDING_C)
    # and N_d is far below its own asymptote in the operative range
    assert abs(rows[40]["N_d"] ** (1 / 40) - 1.7586) < 1e-3


@pytest.mark.slow
def test_the_discarded_factor_is_polynomial_of_order_three_halves() -> None:
    """``N_d/2^d ~ C rho^d d^(-3/2)`` with ``C`` about 11.

    That exponent is the content of the improvement: ``d^(-1/2)`` for staying nonnegative
    under the zero-drift tilt, and a further ``d^(-1)`` because the tilted endpoint sits at
    height ``~sqrt(d)`` rather than at the origin.  The test is that the sequence converges;
    a wrong exponent would make it drift by a power of ``d``.
    """
    c = B.meander_constant((400, 800, 1600))
    assert all(8 < x < 13 for x in c), c
    assert c == sorted(c), c                       # increasing towards its limit
    assert (c[2] - c[1]) < (c[1] - c[0])           # and the increments are shrinking


@pytest.mark.slow
def test_observed_rate_matches_the_theorem_ledger() -> None:
    """The ledger records this count independently at d = 200; the two agree.

    Row ``J-rate-free-density-one`` states "never-negative word count C_200/2^200 = 3.06e-6
    (empirical rate 0.0635/letter, Hoeffding majorizes at 0.0343)".  Both numbers are the
    polynomial factor at work, not a different exponential rate.
    """
    assert abs(B.non_contracting(200) / 2 ** 200 - 3.06e-6) < 0.01e-6
    assert abs(B.observed_rate(200) - 0.0635) < 5e-5
    for d, want in ((24, 0.1696), (1600, 0.0401)):
        assert abs(B.observed_rate(d) - want) < 5e-4, d
    # monotone decrease towards the asymptote, never below it
    rates = [B.observed_rate(d) for d in (24, 50, 100, 200, 400, 800, 1600)]
    assert rates == sorted(rates, reverse=True)
    assert rates[-1] > -math.log(B.chernoff_rate())


def test_error_term_improvement_is_the_same_factor() -> None:
    """Proposition 7.1's error term carries N_d, not 2^d."""
    for d, factor in ((5, 8.0), (16, 31.0)):
        assert abs(2 ** d / B.non_contracting(d) - factor) < 0.05, d


def test_bias_threshold_is_the_contraction_line_from_the_other_side() -> None:
    """beta_* = 1 - log2/log3: the bias at which a node-wise O-share stops forcing the odd
    count below the contraction line.  The two constants in Proposition 7.7 are one constant."""
    assert abs(B.BIAS_THRESHOLD - 0.369070) < 1e-6
    assert abs(B.BIAS_THRESHOLD + B.BETA - 1.0) < 1e-15


def test_chernoff_rate_is_positive_exactly_above_the_threshold() -> None:
    assert B.biased_chernoff_rate(B.BIAS_THRESHOLD) == 0.0
    assert B.biased_chernoff_rate(0.36) == 0.0
    for bias in (0.37, 0.40, 0.45, 0.50):
        assert B.biased_chernoff_rate(bias) > 0, bias
    rates = [B.biased_chernoff_rate(b) for b in (0.37, 0.40, 0.45, 0.50)]
    assert rates == sorted(rates), rates


def test_biased_dp_reduces_to_the_unbiased_count_at_one_half() -> None:
    """The check that the two accountings are one computation."""
    for d in (5, 10, 20, 30):
        assert abs(B.never_contracting_measure(d, 0.5) - B.non_contracting(d) / 2 ** d) < 1e-12


def test_just_above_the_threshold_the_rate_is_useless_at_any_feasible_depth() -> None:
    """At bias 0.37 the asymptotic rate is 1.85e-6 per letter while the extremal measure
    decays at 0.0841, 0.0274 and 0.0154 at d = 24, 100, 200 -- the finite-depth prefactor
    again, as in the unbiased count's d^(-3/2)."""
    assert abs(B.biased_chernoff_rate(0.37) - 1.85487e-06) < 1e-11
    for d, want in ((24, 0.0841), (100, 0.0274), (200, 0.0154)):
        assert abs(B.observed_biased_rate(d, 0.37) - want) < 5e-5, d
    rates = [B.observed_biased_rate(d, 0.37) for d in (24, 50, 100, 200, 400)]
    assert rates == sorted(rates, reverse=True)
    assert rates[-1] > B.biased_chernoff_rate(0.37)


def test_at_the_critical_bias_the_drift_is_exactly_zero() -> None:
    """1 - beta_* = log2/log3, so o_t - t log2/log3 has mean step zero, not merely small."""
    g = B.BETA
    assert B.BIAS_THRESHOLD == 1.0 - g
    assert g * (1 - g) + (1 - g) * (-g) == 0.0


@pytest.mark.slow
def test_critical_bias_decays_like_d_to_the_minus_half() -> None:
    """Chernoff returns rate 0 at beta_*, but a zero-drift walk still fails to stay
    nonnegative.  The measure times sqrt(d) settles, and each doubling multiplies by 2^(-1/2)."""
    ds = (50, 100, 200, 400, 800, 1600, 3200)
    ms = [B.never_contracting_measure(d, B.BIAS_THRESHOLD) for d in ds]
    scaled = [m * math.sqrt(d) for m, d in zip(ms, ds)]
    assert all(0.66 < s < 0.67 for s in scaled), scaled
    assert abs(scaled[-1] - scaled[-2]) < 1e-4, scaled[-2:]
    for a, b in zip(ms, ms[1:]):
        assert abs(b / a - 2 ** -0.5) < 0.01, (a, b)
    assert B.biased_chernoff_rate(B.BIAS_THRESHOLD) == 0.0    # and Chernoff says nothing


@pytest.mark.slow
def test_below_the_threshold_the_mass_does_not_vanish() -> None:
    """The hypothesis cannot be weakened: at bias 0.30 the drift is positive and the extremal
    measure keeps the same mass at d = 200 and d = 3200."""
    a = B.never_contracting_measure(200, 0.30)
    b = B.never_contracting_measure(3200, 0.30)
    assert a > 0.2 and abs(a - b) < 1e-3, (a, b)
