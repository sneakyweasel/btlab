"""Q first-return sections. Not a Q-descriptor or ReturnBelow test."""

from __future__ import annotations

import json

from research.experiments.outputs import artifact_path
from research.juggler_sequence.block_map_q import CONTROLS
from research.juggler_sequence.q_return_section import (
    CLASS_PARK,
    EXISTING_LEAN,
    FORBIDDEN_NEW_API,
    FORBIDDEN_THEOREMS,
    classify,
    in_section,
    lean_api_present,
    leftover_tables,
    q_section_orbit,
    render_markdown,
    run_probe,
    section_row,
    section_verdict,
    write_artifacts,
)


def test_membership_is_exact():
    assert in_section(365, 4447, 2, 3) is True
    assert in_section(365, 12707, 2, 3) is False
    assert in_section(365, 12707, 1, 2) is True
    assert in_section(501, 582916, 1, 2) is False
    assert in_section(501, 133347, 1, 2) is True


def test_365_orbit_and_three_halves_return():
    orbit = q_section_orbit(365)
    assert orbit == [365, 763, 1749, 4447, 12707, 1196]
    row = section_row(365, "3/2", 2, 3)
    assert row["n_multiblock"] == 1
    multi = [item for item in row["returns"] if item["tau"] == 2]
    assert multi == [
        {
            "x": 4447,
            "tau": 2,
            "R": 1196,
            "kind": "I",
            "peak": 12707,
            "band_descends": False,
        }
    ]
    plus = [item for item in row["returns"] if item["kind"] == "plus"]
    assert [item["x"] for item in plus] == [365, 763, 1749]
    assert row["has_type_II"] is False
    assert row["record_low"]["any_ascent"] is True
    assert row["record_low"]["strict_descents"] == 0


def test_square_section_rejected_on_365_and_1517():
    row_365 = section_row(365, "2", 1, 2)
    row_1517 = section_row(1517, "2", 1, 2)
    assert row_365["n_multiblock"] == 0
    assert row_1517["n_multiblock"] == 0
    assert row_365["rejected"] is True
    assert row_1517["rejected"] is True
    assert row_365["typical_tau_one"] is True


def test_501_square_has_one_multiblock_descent():
    row = section_row(501, "2", 1, 2)
    assert row["rejected"] is False
    multi = [item for item in row["returns"] if item["tau"] and item["tau"] >= 2]
    assert multi[0]["x"] == 133347
    assert multi[0]["R"] == 763
    assert multi[0]["kind"] == "I"
    assert multi[0]["peak"] == 582916


def test_thick_sections_rejected_on_leftovers():
    tables = leftover_tables()
    verdict = section_verdict(tables)
    assert verdict["by_section"]["9/4"]["rejected"] is True
    assert verdict["by_section"]["8/3"]["rejected"] is True
    assert verdict["by_section"]["3"]["rejected"] is True
    assert verdict["surviving"] == ["3/2", "2"]
    for n in CONTROLS:
        assert tables["9/4"][str(n)]["n_multiblock"] == 0


def test_no_exact_recurrence_or_permanent_escape():
    tables = leftover_tables()
    for name in ("3/2", "2", "9/4", "8/3", "3"):
        for n in CONTROLS:
            assert tables[name][str(n)]["has_type_II"] is False
            assert tables[name][str(n)]["has_type_III"] is False


def test_probe_and_classify_park():
    scan = run_probe()
    lean = lean_api_present()
    decision = classify(scan, lean)
    assert decision["classification"] == CLASS_PARK
    assert scan["all_sections_rejected"] is False
    assert scan["mixed_on_survivor"] is True
    assert scan["record_low_fails"] is True
    assert scan["has_type_II"] is False
    assert scan["letter_chain"] is False
    assert scan["q_descriptor_reopen"] is False
    assert scan["return_section_lean"] is False


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


def test_classify_render_and_artifacts(tmp_path):
    payload = write_artifacts(output_root=tmp_path)
    text = render_markdown(payload)
    assert CLASS_PARK in text
    from research.juggler_sequence.q_return_section import JSON_PATH

    data = json.loads(artifact_path(JSON_PATH, tmp_path).read_text(encoding="utf-8"))
    assert data["experiment"] == "juggler_q_return_section"
    assert data["decision"]["classification"] == CLASS_PARK
    assert data["anti_overclaim"]["return_section_lean"] is False


def test_dossier_boundary():
    from pathlib import Path

    repo = Path(__file__).resolve().parents[3]
    dossier = (repo / "docs" / "problems" / "juggler_q_return_section.md").read_text(
        encoding="utf-8"
    )
    paper = (repo / "formal" / "Problems" / "JugglerPaper.lean").read_text(
        encoding="utf-8"
    )
    assert "## Branch budget" in dossier
    assert "## Decision" in dossier
    assert "PARK" in dossier
    assert "tau_S=1" in dossier or "\\tau_S=1" in dossier
    assert "ReturnSection" not in paper
    assert "theorem no_juggler_escape" not in dossier
