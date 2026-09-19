"""Phase-0 checks for the 1/3 vs 1/2 rest-average gap."""

from __future__ import annotations

import pytest

from pathlib import Path

from research.juggler_sequence.fate_contagion import lambda_root
from research.juggler_sequence.oe_rest_average import (
    IDEAL,
    PAIRING,
    POOR_SHARE,
    alpha_of,
    averaging_payoff,
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
