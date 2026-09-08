"""Paper C's Lean surface agrees with itself: barrel, axiom artifact, and the paper's column."""

from __future__ import annotations

import json

import pytest

from research.juggler_sequence.paper_c_formal_layer import (
    AXIOM_EXPECTED,
    BARREL,
    CITED_MODULES,
    DATA_DIR,
    MATHLIB_AXIOMS,
    appendix_a_names,
    audit,
    axiom_check_names,
    axiom_check_results,
    barrel_imports,
    verification_table,
)


def test_the_barrel_imports_exactly_the_cited_modules() -> None:
    assert BARREL.is_file()
    assert barrel_imports() == list(CITED_MODULES)
    body = BARREL.read_text(encoding="utf-8")
    assert "laboratory target, not a claim" in body
    assert "lake build Problems.JugglerFatePaper" in body
    for token in ("sorry", "admit", "axiom "):
        assert token not in body, token


def test_every_asked_declaration_rests_on_at_most_mathlibs_three() -> None:
    asked, results = axiom_check_names(), axiom_check_results()
    assert len(asked) >= 90
    assert set(asked) == set(results), set(asked) ^ set(results)
    for name, axioms in results.items():
        assert set(axioms) <= set(MATHLIB_AXIOMS), (name, axioms)
    text = AXIOM_EXPECTED.read_text(encoding="utf-8")
    assert "sorryAx" not in text
    assert "ofReduceBool" not in text


def test_the_four_new_results_are_asked_about() -> None:
    asked = set(axiom_check_names())
    for name in ("recursion_lemma", "minimal_failure_odd_odd", "first_letter_trichotomy",
                 "sweep_fract_lt_half", "sweep_fract_ge_half", "sweep_rep_le_half",
                 "sweep_rep_gt_half", "Sweep.sweep_cell", "weightGen_le_pressure",
                 "reachesOne_of_lt_two_hundred_sixty_one"):
        assert name in asked, name


def test_the_papers_table_carries_the_lean_rows() -> None:
    lean = [r[0] for r in verification_table() if r[1].startswith("Lean")]
    joined = " ".join(lean)
    for key in ("Lemma 4.1)", "Lemma 5.1", "Proposition 9.3", "Lemma 4.7", "Theorem 6.1"):
        assert key in joined, key
    human = [r[0] for r in verification_table() if r[1].startswith("human")]
    joined_h = " ".join(human)
    assert "Theorem 5.3" in joined_h
    assert "Proposition 4.4" in joined_h
    assert "4.1'" in joined_h


def test_appendix_a_names_are_declared_reachable_and_kernel_checked() -> None:
    result = audit()
    assert len(appendix_a_names()) >= 70
    assert result["problems"] == [], result["problems"]
    assert result["surface"]["compiler_trusted"] == []
    assert result["surface"]["compiler_dependent"] == []
    assert result["surface"]["open"] == []


def test_stored_summary_matches_a_fresh_run() -> None:
    stored = DATA_DIR / "summary.json"
    if not stored.is_file():
        pytest.skip("run python -m research.juggler_sequence.paper_c_formal_layer first")
    data = json.loads(stored.read_text(encoding="utf-8"))
    assert data["classification"]["clean"]
    fresh = audit()
    assert data["artifact"] == fresh["artifact"]
    assert data["barrel_imports"] == fresh["barrel_imports"]
    assert data["table"] == fresh["table"]
