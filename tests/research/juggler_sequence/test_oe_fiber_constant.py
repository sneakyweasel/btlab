"""Pairing check for the OE-fiber constant 1/7 -> 1/3."""

from __future__ import annotations

from pathlib import Path

from research.juggler_sequence.fate_contagion import fiber_stats, lambda_root
from research.juggler_sequence.oe_fiber_constant import (
    PAIRING_SLACK,
    THIRD_RECURSION,
    adversarial_three_one_lock,
    pairing_ok,
    scarcer_count,
    summary,
    synthetic_census,
    synthetic_orbit,
)


def test_period_three_split_is_one_third() -> None:
    fracs = synthetic_orbit(1.0 / 3.0, 0.0, 66, 0.0)
    h, n_lo, n_hi = scarcer_count(fracs)
    assert h == 66
    assert min(n_lo, n_hi) / h > 0.32
    assert pairing_ok(n_lo, n_hi, h)


def test_pairing_slack_covers_known_witness() -> None:
    st = fiber_stats(1003635)
    assert st["size"] == 67
    assert st["good"] == 22
    assert pairing_ok(st["good"], st["size"] - st["good"], st["size"])
    assert min(st["good"], st["size"] - st["good"]) + PAIRING_SLACK >= st["size"] / 3.0


def test_third_recursion_root_is_near_448() -> None:
    root = lambda_root(THIRD_RECURSION)
    assert abs(root - 0.448) < 5e-3
    sweep = lambda_root([(1.0, 0.5), (5.0 / 21.0, 3.0 / 8.0), (2.0 / 21.0, 0.75)])
    ideal = lambda_root([(1.0, 0.5), (1.0 / 3.0, 0.75)])
    assert sweep < root < ideal


def test_adversarial_three_one_is_not_monotone() -> None:
    adv = adversarial_three_one_lock()
    assert adv["steps_in_lemma_31"]
    assert not adv["monotone"]
    assert adv["proportion"] < 0.30
    assert not adv["pairing_ok"]


def test_synthetic_and_spot_census_obey_pairing() -> None:
    syn = synthetic_census()
    assert syn["n_fail"] == 0
    assert syn["n_ok"] > 100
    result = summary()
    assert result["classification"] == "OE_FIBER_PAIRING_CONSISTENT"
    spot = result["fibers"]["spot_1e6"]
    assert spot["n_below_pairing"] == 0
    assert spot["min_scarcer_on_good"] > 0.32
    assert abs(result["lambda_roots"]["block_average_plus_third"] - 0.448) < 5e-3


def test_dossier_headings_and_promote() -> None:
    root = Path(__file__).resolve().parents[3]
    dossier = (root / "docs" / "problems" / "juggler_oe_fiber_constant.md").read_text(
        encoding="utf-8"
    )
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
    assert "PROMOTE" in decision
