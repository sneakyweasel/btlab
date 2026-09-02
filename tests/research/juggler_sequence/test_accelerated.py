"""First-return-to-odd accelerated Juggler map. Not a halt test."""

from __future__ import annotations

import json
from pathlib import Path

from research.juggler_sequence.accelerated import (
    CLASS_COMPLEX,
    CLASS_REPACK,
    DATA_DIR,
    DOSSIER_PATH,
    FORBIDDEN_ENGINES,
    JSON_PATH,
    LEAN_THEOREMS,
    exact_macro_defect,
    first_return_vs_odd_return,
    lean_api_present,
    macro_predecessors,
    macro_step,
    macro_trajectory,
    residual_relation,
    validate_step,
)
from research.juggler_sequence.global_defect import global_defect, image_after, local_defect
from research.juggler_sequence.power_itineraries import ANTI_OVERCLAIM, floor_power
from research.juggler_sequence.residual_chain import residual_excursion


def test_three_is_one_odd_step():
    row = macro_step(3)
    assert row["validation_status"] == "OK"
    assert row["a"] == 1
    assert row["b"] == 0
    assert row["r"] == 1
    assert row["word"] == "O"
    assert row["target"] == 5
    assert row["target"] == floor_power(3)
    assert row["j_image_parity"] == 1


def test_seven_is_smallest_even_return_before_odd():
    row = macro_step(7)
    assert row["validation_status"] == "OK"
    assert row["word"] == "OEEE"
    assert row["target"] == 1
    ret = first_return_vs_odd_return(row)
    assert ret["return_before_odd"] is True
    assert ret["tau_within_macro"] == 2
    assert ret["return_state"] == 4
    assert ret["return_state_parity"] == 0


def test_sixty_three_even_tail_returns_before_odd():
    row = macro_step(63)
    assert row["validation_status"] == "OK"
    assert row["a"] == 1
    assert row["b"] == 4
    assert row["word"] == "OEEEE"
    assert row["target"] == 1
    ret = first_return_vs_odd_return(row)
    assert ret["return_before_odd"] is True
    assert ret["tau_within_macro"] == 2
    assert ret["return_state"] == 22
    assert ret["return_state_parity"] == 0


def test_fifteen_return_is_the_odd_landing():
    row = macro_step(15)
    assert row["word"] == "OE"
    assert row["target"] == 7
    ret = first_return_vs_odd_return(row)
    assert ret["return_at_odd"] is True
    assert ret["return_before_odd"] is False


def test_validation_matches_direct_j():
    for n in (3, 9, 15, 37, 63, 365):
        row = macro_step(n)
        assert validate_step(row) == "OK"
        assert image_after(n, row["word"]) == row["target"]
        current = n
        for _ in range(row["r"]):
            current = floor_power(current)
        assert current == row["target"]
        assert current % 2 == 1


def test_residual_agrees_only_when_j_even():
    even_row = macro_step(15)
    rel_even = residual_relation(even_row)
    assert rel_even["j_even"] is True
    assert rel_even["agrees_with_residual"] is True
    residual = residual_excursion(15)
    assert residual is not None
    assert residual["a"] == 1
    assert residual["y"] == 7

    odd_row = macro_step(37)
    rel_odd = residual_relation(odd_row)
    assert rel_odd["j_even"] is False
    assert rel_odd["differs_from_residual"] is True
    residual_37 = residual_excursion(37)
    assert residual_37 is not None
    assert residual_37["a"] == 4
    assert residual_37["y"] == 9317
    assert odd_row["target"] == 225


def test_a_is_identically_one_on_small_window():
    for n in range(3, 201, 2):
        row = macro_step(n)
        assert row["validation_status"] == "OK"
        assert row["a"] == 1
        assert row["target"] % 2 == 1


def test_defect_is_existing_global_defect():
    for n in (3, 9, 15, 63):
        row = macro_step(n)
        delta = exact_macro_defect(n, row["a"], row["b"], row["target"])
        assert delta == global_defect(n, row["word"])
        if row["b"] == 0:
            assert delta == local_defect(n)


def test_macro_predecessors_contain_start():
    row = macro_step(15)
    rec = macro_predecessors(row["target"], row["a"], row["b"])
    assert rec["ok"] is True
    assert 15 in rec["predecessors"]
    odd = macro_predecessors(5, 1, 0)
    assert odd["predecessors"] == [3]


def test_macro_trajectory_is_odd_subsequence():
    traj = macro_trajectory(3)
    assert traj["states"][0] == 3
    assert traj["states"][1] == 5
    assert all(state % 2 == 1 for state in traj["states"])
    assert traj["macro_word"][0] == (1, 0)


def test_lean_api():
    lean = lean_api_present()
    assert lean["sorry_free"] is True
    for name in LEAN_THEOREMS:
        assert lean[name] is True, name
    assert lean["no_global_termination_theorem"] is True
    for name in FORBIDDEN_ENGINES:
        assert name != "ResidualStep"


def test_anti_overclaim_stays_false():
    assert ANTI_OVERCLAIM["global_termination"] is False
    assert ANTI_OVERCLAIM["global_divergence"] is False


def test_dossier_headings():
    text = DOSSIER_PATH.read_text(encoding="utf-8")
    for heading in ("## Branch budget", "## Decision", "## Publication assessment"):
        assert heading in text
    assert "CLOSE" in text.split("## Decision", 1)[1]


def test_committed_artifacts_if_present():
    if not JSON_PATH.is_file():
        return
    payload = json.loads(JSON_PATH.read_text(encoding="utf-8"))
    assert payload["engine_control_layer_modified"] is False
    assert payload["anti_overclaim"]["A_replaces_J"] is False
    assert payload["anti_overclaim"]["reopen_pe_factors"] is False
    assert payload["anti_overclaim"]["second_acceleration"] is False
    assert payload["decision"]["classification"] in {CLASS_COMPLEX, CLASS_REPACK}
    assert payload["scan"]["a_always_one"] is True
    assert payload["scan"]["domain_complete"] is True
    assert payload["scan"]["smallest_return_before_odd"] == 7
    if (DATA_DIR / "manifest.json").is_file():
        manifest = json.loads((DATA_DIR / "manifest.json").read_text(encoding="utf-8"))
        assert manifest["ok"] == payload["scan"]["ok"]
        assert (DATA_DIR / "macro_edges.csv").is_file()
        assert (DATA_DIR / "macro_branch_summary.csv").is_file()
