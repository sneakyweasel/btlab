"""Phase-0 checks for the 1/3 vs 1/2 rest-average gap."""

from __future__ import annotations

from pathlib import Path

from research.juggler_sequence.fate_contagion import lambda_root
from research.juggler_sequence.oe_rest_average import (
    IDEAL,
    PAIRING,
    POOR_SHARE,
    alpha_of,
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
