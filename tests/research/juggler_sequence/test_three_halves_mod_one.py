"""Geometric {(3/2)^n} placement: literature and CLOSE pin."""

from __future__ import annotations

from pathlib import Path

from research.literature import get_reference

DOSSIER = Path("docs/problems/juggler_three_halves_mod_one.md")
NEGATIVE = Path("docs/negative_knowledge.md")

LIT_IDS = (
    "vijayaraghavan-1940-fractional-parts-powers",
    "flatto-lagarias-pollington-1995-range-fractional-parts",
    "mahler-1968-powers-of-3-2",
    "kuipers-niederreiter-1974-uniform-distribution",
)


def test_literature_ids_resolve():
    for ref_id in LIT_IDS:
        rec = get_reference(ref_id)
        assert rec["id"] == ref_id


def test_dossier_headings_and_close():
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
    assert "no new ledger row" in dossier.lower() or "No new ledger row" in dossier
    for ref_id in LIT_IDS:
        assert ref_id in dossier
    assert "research/three_halves" in dossier
    assert "Not a halt theorem" in dossier or "not a halt theorem" in dossier


def test_negative_knowledge_cites_the_close():
    text = NEGATIVE.read_text(encoding="utf-8")
    assert "juggler_three_halves_mod_one" in text
    assert "Do not reopen" in text
