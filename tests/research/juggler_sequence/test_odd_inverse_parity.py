"""Fast checks for the odd-inverse-parity cube-block calibration."""

from __future__ import annotations

import json
from pathlib import Path

from research.juggler_sequence.empty_odd_cell import odd_cell_kind
from research.juggler_sequence.odd_inverse_parity import (
    CLASS_REPARAM,
    EXISTING_LEAN,
    FORBIDDEN_THEOREMS,
    JSON_PATH,
    ODD_HITS,
    backward_odd_spine,
    block_identity,
    inverse_candidate,
    lean_api_present,
    named_hit_row,
    offset_hunt,
)
from research.juggler_sequence.power_words import floor_power

CONJECTURE = Path("conjectures/refuted/juggler_odd_inverse_parity.json")
DOSSIER = Path("docs/problems/juggler_odd_inverse_parity.md")


def test_cube_block_identity_small_m() -> None:
    for m in (1, 2, 3, 5, 10):
        row = block_identity(m)
        assert row["identity_ok"] is True, m
        assert row["n_type2"] == row["n_odds"]


def test_named_hits_are_type2_self_preimages() -> None:
    expected = {
        3: (5, 1, 4),
        37: (225, 6, 9),
        365: (6973, 19, 114),
        761: (20993, 27, 1310),
    }
    for x in ODD_HITS:
        row = named_hit_row(x)
        image, m, r = expected[x]
        assert row["T_x"] == image
        assert row["m"] == m
        assert row["r"] == r
        assert row["k"] == x
        assert row["kind"] == 2
        assert row["self_preimage"] is True
        assert inverse_candidate(image) == x
        assert odd_cell_kind(image) == 2
        assert floor_power(x) == image


def test_offsets_are_not_an_ap_or_deciding_class() -> None:
    for m in (5, 10):
        hunt = offset_hunt(m)
        assert hunt["n_type2"] >= 3
        assert hunt["is_ap"] is False
        assert hunt["deciding_residue"] is False
        assert hunt["n_unique_gaps"] >= 3


def test_m1_mod4_congruence_is_not_a_law() -> None:
    hunt = offset_hunt(1)
    assert hunt["n_type2"] == 2
    assert hunt["deciding_residue"] is False
    mod4 = next(row for row in hunt["residues"] if row["modulus"] == 4)
    assert mod4["occupied"] == [0]
    assert mod4["deciding"] is False


def test_backward_spines_descend_and_die() -> None:
    for x in ODD_HITS:
        row = backward_odd_spine(floor_power(x))
        assert row["descends"] is True
        assert row["depth"] == 1
        assert row["chain"][-1] == x
        assert row["terminal_kind"] == 0
        start = backward_odd_spine(x)
        assert start["depth"] == 0
        assert start["terminal_kind"] == 0


def test_artifact_is_reparameterization() -> None:
    summary = json.loads(JSON_PATH.read_text(encoding="utf-8"))
    assert summary["classification"] == CLASS_REPARAM
    assert summary["identity_all_ok"] is True
    assert summary["any_ap"] is False
    assert summary["any_deciding_residue"] is False
    assert all(row["identity_ok"] for row in summary["identity"])
    hits = summary["named_hits"]
    assert all(row["kind"] == 2 and row["self_preimage"] for row in hits)
    assert summary["nest"]["all_descend"] is True
    assert summary["nest"]["max_depth"] == 3
    assert summary["nest"]["n_type2"] == 17
    anti = summary["anti_overclaim"]
    assert anti["halt_theorem"] is False
    assert anti["paper_a_modified"] is False
    assert anti["odd_landing_sets_rerun"] is False
    assert anti["odd_tower_rerun"] is False
    assert anti["n_window_raised"] is False


def test_lean_boundaries() -> None:
    lean = lean_api_present()
    assert lean["sorry_free"] is True
    for name in EXISTING_LEAN:
        assert lean[name] is True, name
    for name in FORBIDDEN_THEOREMS:
        assert lean[f"has_{name}"] is False, name
    assert lean["new_lean_file"] is False


def test_conjecture_and_dossier() -> None:
    conj = json.loads(CONJECTURE.read_text(encoding="utf-8"))
    assert conj["id"] == "juggler_odd_inverse_parity"
    assert conj["status"] == "REFUTED"
    dossier = DOSSIER.read_text(encoding="utf-8")
    assert "## Branch budget" in dossier
    assert "## Decision" in dossier
    assert "## Publication assessment" in dossier
    assert "CLOSE" in dossier
    assert "J-odd-pred-empty-cube" in dossier
    assert "Paper A" in dossier
    assert "odd_cell_unique" in dossier
