"""Cyclic word feasibility. Not a halt test."""

from __future__ import annotations

from math import isqrt
from pathlib import Path

from research.juggler_sequence.atlas.schema import LANGUAGE_IDS
from research.juggler_sequence.cyclic_feasibility import (
    A001037,
    CLASS_CLOSED,
    CLASS_CYCLE,
    CLASS_FAMILY,
    CLASS_INCOMPLETE,
    CLASS_NEAR,
    CLASS_PARK_BOUND,
    CLASS_PARK_OPEN,
    CLASS_UNIVERSAL,
    EXISTING_LEAN,
    FORBIDDEN_NEW_API,
    FORBIDDEN_THEOREMS,
    TEST_K,
    TEST_N,
    all_odd_phi_contradiction,
    classify,
    cyc_real,
    exponent_ok,
    follows_image,
    leftover_shape,
    lean_api_present,
    necklace_key,
    plus_one_w,
    primitive_necklaces,
    probe_payload,
    propagate_cycle,
    render_markdown,
    word_class,
    write_artifacts,
)
from research.juggler_sequence.power_itineraries import floor_power


def test_primitive_counts_match_a001037():
    for k in range(1, 9):
        words = primitive_necklaces(k)
        assert len(words) == A001037[k]
        assert len({necklace_key(w) for w in words}) == len(words)
        assert all(len(w) == k and set(w) <= {"O", "E"} for w in words)


def test_ooe_is_the_length_three_expanding_class():
    words = primitive_necklaces(3)
    expanding = [w for w in words if exponent_ok(w) and word_class(w) == "expanding"]
    assert necklace_key("OOE") in {necklace_key(w) for w in expanding}
    assert plus_one_w("OOE") == 18
    assert not leftover_shape("OOE")
    assert follows_image(5, "OOE") == 6
    assert cyc_real(5, "OOE") is False
    assert cyc_real(3, "OOE") is False


def test_all_odd_phi_and_interval_on_ooe():
    assert all_odd_phi_contradiction() is True
    finite, finite_empty = propagate_cycle("OOE", 20)
    assert finite_empty is True
    bounds, empty = propagate_cycle("OOE", None)
    assert empty is False
    assert all(not b.empty() for b in bounds)
    assert all(b.hi is None for b in bounds)


def test_floor_cells_match_propagation_edges():
    x = 11
    y = floor_power(x)
    assert y == isqrt(x * x * x)
    assert y * y <= x * x * x < (y + 1) * (y + 1)


def test_tiny_probe_reproduces():
    first = probe_payload()
    second = probe_payload()
    assert first["experiment"] == "juggler_cyclic_feasibility"
    assert first["engine_control_layer_modified"] is False
    assert first["scan"]["census_matches_A001037"] is True
    assert first["scan"]["direct"]["cycle_count"] == 0
    assert first["scan"]["summary"] == second["scan"]["summary"]
    assert first["scan"]["k_max"] == TEST_K
    assert first["scan"]["n_max"] == TEST_N
    leftover_k = [row["k"] for row in first["scan"]["census"] if row["leftover_residue"]]
    assert leftover_k == []


def test_probe_and_classify_vocabulary():
    payload = probe_payload()
    assert payload["decision"]["classification"] in {
        CLASS_UNIVERSAL,
        CLASS_FAMILY,
        CLASS_NEAR,
        CLASS_CLOSED,
        CLASS_PARK_OPEN,
        CLASS_PARK_BOUND,
        CLASS_CYCLE,
        CLASS_INCOMPLETE,
    }
    assert payload["decision"]["classification"] == CLASS_CLOSED
    assert payload["decision"]["classification"] != CLASS_INCOMPLETE
    written = write_artifacts(payload)
    assert written["decision"]["classification"] == CLASS_CLOSED
    text = render_markdown(payload)
    assert "NOT OBSERVED WITHIN SEARCH BOUND" in text
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
    assert "LANG_CYC_REAL" not in LANGUAGE_IDS


def test_dossier_boundary():
    repo = Path(__file__).resolve().parents[3]
    dossier = (repo / "docs" / "problems" / "juggler_cyclic_feasibility.md").read_text(
        encoding="utf-8"
    )
    paper = (repo / "formal" / "Problems" / "JugglerPaper.lean").read_text(
        encoding="utf-8"
    )
    assert "## Branch budget" in dossier
    assert "## Decision" in dossier
    assert "## Publication assessment" in dossier
    assert "cycle_itinerary_length_ge_eleven" in dossier
    assert "no_cycle_itinerary_even_count_le_three" in dossier
    assert "**CLOSE**" in dossier
    assert "CycReal" not in paper
    assert "theorem no_juggler_escape" not in dossier
    assert "LANG_CYC_REAL" not in dossier
