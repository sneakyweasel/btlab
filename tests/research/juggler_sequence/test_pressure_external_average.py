"""Classification pin for the external-averaging readings of P_θ / M_{θ,q}."""

from __future__ import annotations

from pathlib import Path

DOSSIER = (
    Path(__file__).resolve().parents[3]
    / "docs"
    / "problems"
    / "juggler_pressure_external_average.md"
)
NEGATIVE = Path(__file__).resolve().parents[3] / "docs" / "negative_knowledge.md"


def test_dossier_headings_and_close() -> None:
    dossier = DOSSIER.read_text(encoding="utf-8")
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
    assert "CLOSE" in decision
    assert "Not a halt theorem" in dossier or "not a halt theorem" in dossier


def test_identity_a_is_cylinder_weighted_nested_phase() -> None:
    dossier = DOSSIER.read_text(encoding="utf-8")
    assert "completed single sum" in dossier.lower() or "Completed single sum" in dossier
    assert "cylinder-weighted nested" in dossier
    assert "Vaaler" in dossier
    assert "§10.4(e)" in dossier or "10.4(e)" in dossier
    assert "cC<1" in dossier or "cC < 1" in dossier


def test_identity_b_is_free_term_or_does_not_suffice() -> None:
    dossier = DOSSIER.read_text(encoding="utf-8")
    assert "does not suffice" in dossier
    assert "J-tao-free-term-is-live-mass" in dossier
    assert "S-fairness" in dossier or "$S$-fairness" in dossier
    assert "third formulation" in dossier.lower()


def test_parseval_is_pointed_at_not_rederived() -> None:
    dossier = DOSSIER.read_text(encoding="utf-8")
    assert "J-tao-cylinder-forms-reparameterization" in dossier
    assert "Not re-derived" in dossier or "not re-derived" in dossier
    assert "J-pressure-direct-routes" in dossier


def test_negative_knowledge_cites_the_close() -> None:
    text = NEGATIVE.read_text(encoding="utf-8")
    assert "juggler_pressure_external_average" in text
    assert "J-pressure-external-average" in text
