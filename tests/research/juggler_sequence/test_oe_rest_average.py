"""Phase-0 checks for the 1/3 vs 1/2 rest-average gap."""

from __future__ import annotations

import math

from research.juggler_sequence.fate_contagion import fiber_stats

import pytest

from pathlib import Path

from research.juggler_sequence.fate_contagion import lambda_root
from research.juggler_sequence.oe_rest_average import (
    IDEAL,
    PAIRING,
    POOR_SHARE,
    alpha_of,
    averaging_payoff,
    fd_placement,
    is_resonant,
    resonance_density,
    share_law_error,
    step_is_weyl,
    weyl_discrepancy,
    classify,
    dyadic_logmass,
    exact_even_share,
    is_low_even,
    model_matches_fiber,
    poor_mask,
    summary,
)


def test_pairing_and_ideal_roots() -> None:
    assert abs(lambda_root(PAIRING) - 0.4480) < 5e-3
    assert abs(lambda_root(IDEAL) - 0.4927) < 5e-3
    assert lambda_root(PAIRING) < lambda_root(IDEAL)


def test_model_tracks_known_witness() -> None:
    rec = model_matches_fiber(1003635)
    assert rec["exact"] < 0.34
    assert rec["low_even"] is True
    assert is_low_even(rec["exact"], cutoff=0.35)


def test_poor_set_has_positive_logmass_fraction() -> None:
    mask = poor_mask(8_000)
    mid = dyadic_logmass(mask, 2_048, 4_095)
    hi = dyadic_logmass(mask, 4_096, 8_000)
    assert mid["fraction"] > 0.03
    assert hi["fraction"] > 0.03
    assert mid["n_set"] > 20


def test_alpha_defined_on_ordinary_m() -> None:
    a = alpha_of(10_000)
    assert 0.0 <= a < 1.0
    sh = exact_even_share(10_000)
    assert 0.2 <= sh <= 0.8


def test_classify_sharp_and_drowned() -> None:
    sharp = classify(
        [0.08, 0.09],
        {"weighted_even_share": 0.34, "rest_over_range": 0.4},
        {"weighted_even_share": 0.50},
    )
    drowned = classify(
        [0.08, 0.09],
        {"weighted_even_share": 0.49, "rest_over_range": 0.4},
        {"weighted_even_share": 0.50},
    )
    assert sharp.endswith("SHARP")
    assert drowned.endswith("DROWNED")


def test_small_summary_runs() -> None:
    rec = summary(limit=12_000)
    assert rec["n_poor"] > 0
    assert rec["classification"] in {
        "OE_REST_AVERAGE_SHARP",
        "OE_REST_AVERAGE_DROWNED",
        "OE_REST_AVERAGE_MIXED",
    }
    assert rec["lambda_roots"]["ideal"] > rec["lambda_roots"]["pairing"]
    assert rec["poor_logmass_fraction_min"] is not None
    assert rec["poor_logmass_fraction_min"] > 0.02


def test_dossier_headings() -> None:
    root = Path(__file__).resolve().parents[3]
    dossier = (root / "docs" / "problems" / "juggler_oe_rest_average.md").read_text(encoding="utf-8")
    for heading in (
        "## Problem",
        "## Exact statement",
        "## Current literature",
        "## Branch budget",
        "## Balanced-ternary formulation",
        "## Why BT may be relevant",
        "## Candidate operations / invariants",
        "## Experiments",
        "## Conjectures",
        "## Counterexamples",
        "## Formalization",
        "## Results",
        "## Open questions",
        "## Decision",
        "## Publication assessment",
    ):
        assert heading in dossier
    decision = dossier.split("## Decision", 1)[1].split("## ", 1)[0]
    assert any(word in decision for word in ("PROMOTE", "PARK", "CLOSE"))

def test_reopening_pays_only_at_essentially_the_mean() -> None:
    """The park stands, but the prize it was weighed against was the wrong one.

    The two-production inequality is the whole unconditional chain, and its
    root moves steeply in the OE coefficient: `2/9` gives `0.326121`, the mean
    share `1/3` gives `0.492658`. The coefficient matching `lambda**` on two
    productions alone is `0.3332760`, a share of `0.4999140` -- essentially the
    mean. So an averaged argument delivering the mean would reach the headline
    exponent with two productions, making the block-average family and the
    six-word ladder unnecessary for it, and taking Proposition 4.4's two
    exponential-sum bounds -- Paper C's largest unformalized gap -- off the
    critical path.

    The prize is therefore not a better exponent but the same exponent with the
    analytic core removed. That is a different prize from the one the PARK was
    weighed against, which is why the branch's "best next question: none on
    this line" is now recorded as arguable rather than settled.

    What still vindicates the park: the target is narrow. Break-even against
    the three-production base `0.448017`, which the block average ALREADY
    gives, is share `0.4555`. An averaged argument landing below that is a
    regression, not progress. Recovering "better than the worst case" is worth
    nothing here; only "essentially the mean" pays.
    """
    p = averaging_payoff()
    curve = {round(r["coefficient"], 6): r["root"] for r in p["two_production_curve"]}
    assert curve[round(2 / 9, 6)] == pytest.approx(0.326121, abs=1e-6)
    assert curve[0.3] == pytest.approx(0.442499, abs=1e-6)
    assert curve[round(1 / 3, 6)] == pytest.approx(0.492658, abs=1e-6)

    # the two anchors that decide whether reopening is worth anything
    assert p["matching_share"] == pytest.approx(0.499914, abs=1e-5)
    assert p["break_even_share"] == pytest.approx(0.455508, abs=1e-5)

    # and the shape of the answer: an intermediate coefficient can LOSE
    assert curve[0.3] < p["three_production_base"], (
        "share 0.45 is below what the block average already gives"
    )
    assert p["break_even_share"] < p["matching_share"] < 0.5

def test_the_missing_lemma_sits_below_hypothesis_fd() -> None:
    """The question that decides whether the averaging route is worth anything.

    `J-oe-low-share-weight-decays-polynomially` needs an equidistribution
    statement about the fibre step `alpha_m` across `m`. If that is Hypothesis
    FD in disguise, the bootstrap trades Proposition 4.4's two exponential-sum
    bounds for an open hypothesis and buys nothing. It is not.

    FD asks for joint equidistribution of parity words along a Juggler ORBIT,
    and is open because an orbit is not an arithmetic sequence. This asks about
    `alpha_m` as `m` runs over every integer in a dyadic block, and `alpha_m` is
    `frac((3/2) m^(2/3))` up to `O(m^(-2/3))` -- measured here, the gap falling
    `4.1e-04` to `1.5e-06` from `1e5` to `1e9`.

    For `f(m) = (3/2) m^(2/3)`: `f -> infinity`, `f'(m) = m^(-1/3) -> 0`
    monotonically, `m f'(m) = m^(2/3) -> infinity`. Those are Fejer's
    conditions, so equidistribution is unconditional, and van der Corput gives
    a polynomial rate -- measured star discrepancy falls about like `N^(-1/2)`.

    So the first ingredient is a theorem. What remains open is the JOINT law of
    `(beta_m, theta_m)`, since `J-oe-fiber-share-law` makes the share a function
    of both and not of `alpha_m` alone. That is still a Weyl-sums question about
    explicit functions of `m`, which is the class the sweep machinery already
    works in -- not the orbit question FD is.
    """
    placement = fd_placement(exponents=(4, 5, 6))
    weyl = placement["step_is_weyl"]
    assert weyl["gap_falls"], "alpha_m must converge to the Weyl sequence"
    assert weyl["rows"][0]["circle_gap"] < 1e-3
    assert weyl["rows"][-1]["circle_gap"] < 1e-5

    # the residual is the fibre's curvature, so it should track m^(-2/3)
    first, last = weyl["rows"][0], weyl["rows"][-1]
    decades = math.log10(last["m"] / first["m"])
    slope = math.log10(last["circle_gap"] / first["circle_gap"]) / decades
    assert -0.85 < slope < -0.5, f"expected about -2/3, got {slope:.3f}"

    assert placement["decays_polynomially"]
    assert all(s < -0.25 for s in placement["slopes_per_decade"])
    assert weyl_discrepancy(10**4) > weyl_discrepancy(10**6)

def test_the_capacity_exponent_is_the_resonance_window_and_the_share_law_cannot_see_it() -> None:
    """Where the measured `m^(-1/3)` comes from, and what is still missing.

    Two ingredients, both already settled, give the exponent without any new
    hypothesis. The resonant window has width `C/H_m`, and `H_m = (2/3)m^(1/3)
    + O(1)` is Lemma 3.2 two-sided. And `alpha_m` equidistributes by Fejer with
    star discrepancy about `N^(-1/2)` (`fd_placement`). So the resonant count
    below `N` is `c N^(2/3) + O(N^(1/2))`, main term dominating, and the
    density is `Theta(m^(-1/3))` -- measured flat to within 8 per cent across
    ten octaves. That is exactly the exponent
    `J-oe-low-share-weight-decays-polynomially` reports for the LOW-SHARE set.

    And the tool that looked like it should close the remaining step does not.
    `J-oe-fiber-share-law` carries error `H^(-1/2) + (1+|beta|)/H` with
    `beta = alpha (H-1)`, and the second piece tends to `alpha` -- it never
    decays. At the four fibres that attain the pairing floor the bound is
    between 2.4 and 4.3 times the deviation from `1/2` it would have to
    explain, at every scale. The law is vacuous for `alpha` of order one, which
    is precisely where the low shares live.

    STATUS. The exponent is explained and is not a coincidence. The open step
    is the inclusion `low share implies resonant`, and it cannot come from the
    share law.
    """
    density = resonance_density(exponents=(14, 18, 22), samples=1500)
    assert density["is_cube_root"], density["scaled_spread"]
    assert density["rows"][0]["density"] > 4 * density["rows"][-1]["density"]

    # the attaining fibres are resonant, which is the evidence for the inclusion
    for m in (1018590, 10001831, 100001607, 1000011666):
        assert is_resonant(m), m

    # and the share law cannot explain any of them
    for m in (1018590, 10001831, 100001607, 1000011666):
        st = fiber_stats(m)
        size = st["size"]
        deviation = abs(min(st["good"], size - st["good"]) / size - 0.5)
        assert share_law_error(st["alpha"], size) > 2.0 * deviation, m

    # the error tends to alpha rather than to zero: that is the structural point
    for alpha in (1 / 3, 2 / 3):
        tail = [share_law_error(alpha, h) - h**-0.5 for h in (10**3, 10**4, 10**5)]
        assert all(abs(t - alpha) < 2e-3 for t in tail), alpha
