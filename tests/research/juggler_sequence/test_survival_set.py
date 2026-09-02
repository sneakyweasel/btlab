"""Survival-set inverse mass. Not a halt test."""

from __future__ import annotations

from pathlib import Path

from research.juggler_sequence.atlas.schema import LANGUAGE_IDS
from research.juggler_sequence.survival_set import (
    CLASS_CLOSED,
    CLASS_GREEN,
    CLASS_INCOMPLETE,
    CLASS_PARK,
    EXISTING_LEAN,
    FORBIDDEN_NEW_API,
    FORBIDDEN_THEOREMS,
    TEST_K_MAX,
    TEST_WINDOWS,
    classify,
    even_leak_count,
    interval_inverse_mass,
    lean_api_present,
    probe_payload,
    render_markdown,
    tau_n,
)


def test_tau_and_even_leak():
    assert tau_n(4, 3, k_max=TEST_K_MAX, bit_cap=256) == (0, "RETURNED")
    assert tau_n(9, 3, k_max=TEST_K_MAX, bit_cap=256)[0] >= 1
    assert even_leak_count(3, 20) == 3
    assert even_leak_count(10, 80) == even_leak_count(10, 80)


def test_interval_inverse_and_s1():
    payload = probe_payload()
    row = next(
        item
        for item in payload["scan"]["profiles"]
        if item["N"] == 3 and item["X"] == min(TEST_WINDOWS)
    )
    total = row["X"] - row["N"] + 1
    assert row["S"][0] == total
    assert row["S"][1] == total - row["even_leak"]
    assert row["S"] == sorted(row["S"], reverse=True)
    inv = interval_inverse_mass(3, min(TEST_WINDOWS))
    assert inv["A"] == total
    assert inv["P_E"] >= 0
    assert inv["P_O"] >= 0
    assert inv["P_E"] + inv["P_O"] <= total


def test_tiny_window_reproduces():
    first = probe_payload()
    second = probe_payload()
    assert first["scan"]["only_even_s1"] is True
    assert first["scan"]["only_even_s1"] == second["scan"]["only_even_s1"]
    assert first["scan"]["profiles"][0]["S"] == second["scan"]["profiles"][0]["S"]
    assert first["anti_overclaim"]["density_is_emptiness"] is False


def test_probe_and_classify_vocabulary():
    payload = probe_payload()
    assert payload["experiment"] == "juggler_survival_set"
    assert payload["engine_control_layer_modified"] is False
    assert payload["decision"]["classification"] in {
        CLASS_CLOSED,
        CLASS_GREEN,
        CLASS_PARK,
        CLASS_INCOMPLETE,
    }
    assert payload["decision"]["classification"] != CLASS_INCOMPLETE
    text = render_markdown(payload)
    assert "NOT_OBSERVED_WITHIN_BOUND" in text
    lean = lean_api_present()
    assert classify(payload["scan"], lean)["classification"] == payload["decision"][
        "classification"
    ]


def test_lean_api_without_new_layer():
    lean = lean_api_present()
    assert lean["sorry_free"] is True
    for name in EXISTING_LEAN:
        assert lean[name] is True, name
    for name in FORBIDDEN_THEOREMS:
        assert lean[f"has_{name}"] is False, name
    for name in FORBIDDEN_NEW_API:
        assert lean[f"has_api_{name}"] is False, name
    assert lean["new_lean_file"] is False
    assert lean["not_in_paper_barrel"] is True
    assert lean["no_atlas_lang"] is True
    assert "LANG_SURVIVAL" not in LANGUAGE_IDS


def test_dossier_boundary():
    repo = Path(__file__).resolve().parents[3]
    dossier = (repo / "docs" / "problems" / "juggler_survival_set.md").read_text(
        encoding="utf-8"
    )
    paper = (repo / "formal" / "Problems" / "JugglerPaper.lean").read_text(
        encoding="utf-8"
    )
    assert "## Branch budget" in dossier
    assert "## Decision" in dossier
    assert "## Publication assessment" in dossier
    assert "SURVIVOR_PHASE_CLOSED" in dossier
    assert "even_itinerary_contracts" in dossier
    assert "**CLOSE**" in dossier
    assert "SurvivalSet" not in paper
    assert "theorem no_juggler_escape" not in dossier
    assert "LANG_SURVIVAL" not in dossier
