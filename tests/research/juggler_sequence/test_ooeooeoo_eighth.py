"""OOEOOEOO first cube-odd lifts are not a forced n^8 lower cell."""

from __future__ import annotations

import json

from research.experiments.outputs import artifact_path
from research.juggler_sequence.first_lift_eighth import (
    UNSAFE_WORD,
    WITNESS_4309,
    WITNESS_5791,
)
from research.juggler_sequence.ooeooeoo_eighth import (
    CENSUS_LIMIT,
    CLASS_PARKED,
    EXTENDED_LIMIT,
    FORBIDDEN_THEOREMS,
    LEAN_THEOREMS,
    LPB_BITS,
    actual_milli,
    census,
    classify,
    first_lift_row,
    formal_milli,
    lean_api_present,
    lower_denom_too_weak,
    ooeooeoo_first_cube,
    render_markdown,
    run_probe,
    witness_tracks_envelope,
    write_artifacts,
)


def test_4309_hugs_upper_envelope():
    n, word, x = WITNESS_4309
    row = ooeooeoo_first_cube(n)
    assert row is not None
    assert row["x"] == x
    assert word == UNSAFE_WORD
    assert row["y_even"] is True
    assert row["x3_lt_n8"] is False
    track = witness_tracks_envelope(n, x)
    assert track["below_formal"] is True
    assert track["near_envelope"] is True
    assert track["far_above_boundary"] is True
    assert actual_milli(n, x) == 94024
    assert formal_milli(n) == 94048


def test_5791_and_565_also_above():
    row = ooeooeoo_first_cube(WITNESS_5791[0])
    assert row is not None
    assert row["y_even"] is True
    assert row["x3_lt_n8"] is False
    odd = ooeooeoo_first_cube(565)
    assert odd is not None
    assert odd["y_even"] is False
    assert odd["x3_lt_n8"] is False
    assert odd["milli"] > 1000


def test_365_first_lift_is_not_the_gap_word():
    row = first_lift_row(365)
    assert row is not None
    assert row["word"] == "OOEOOEOOEO"
    assert ooeooeoo_first_cube(365) is None


def test_lower_denom_is_too_weak():
    lpb = lower_denom_too_weak()
    assert lpb["bits"] == LPB_BITS
    assert lpb["too_weak"] is True
    assert lpb["laboratory_n_bits"] < lpb["log2_n_threshold"]


def test_census_window_has_no_safe_hit():
    scan = census(CENSUS_LIMIT)
    assert scan["no_safe"] is True
    assert scan["even_unsafe"] > 0
    assert scan["closest"]["n"] == 565 or scan["closest"]["n"] == 4309
    assert scan["closest"]["x3_lt_n8"] is False


def test_extended_census_has_no_safe_hit():
    scan = census(EXTENDED_LIMIT)
    assert scan["no_safe"] is True
    assert scan["even_unsafe"] == 185
    assert scan["odd_unsafe"] == 201


def test_probe_and_classify_parked():
    scan = run_probe()
    lean = lean_api_present()
    decision = classify(scan, lean)
    assert decision["classification"] == CLASS_PARKED
    assert scan["no_safe_in_window"] is True
    assert scan["lpb_too_weak"] is True
    assert scan["hugs_upper_envelope"] is True
    assert scan["letter_chain"] is False
    assert scan["q_return"] is False
    assert scan["defect_census"] is False


def test_lean_api_without_halt():
    lean = lean_api_present()
    assert lean["sorry_free"] is True
    for name in LEAN_THEOREMS:
        assert lean[name] is True, name
    for name in FORBIDDEN_THEOREMS:
        assert lean[f"has_{name}"] is False, name
    assert lean["in_laboratory_barrel"] is True
    assert lean["not_in_paper_barrel"] is True
    assert lean["no_new_ooeooeoo_eighth_lean"] is True


def test_classify_render_and_artifacts(tmp_path):
    payload = write_artifacts(output_root=tmp_path)
    text = render_markdown(payload)
    assert CLASS_PARKED in text
    from research.juggler_sequence.ooeooeoo_eighth import JSON_PATH

    data = json.loads(artifact_path(JSON_PATH, tmp_path).read_text(encoding="utf-8"))
    assert data["experiment"] == "juggler_ooeooeoo_eighth"
    assert data["decision"]["classification"] == CLASS_PARKED
    assert data["anti_overclaim"]["ooeooeoo_forced_eighth"] is False


def test_dossier_boundary():
    from pathlib import Path

    repo = Path(__file__).resolve().parents[3]
    dossier = (repo / "docs" / "problems" / "juggler_ooeooeoo_eighth.md").read_text(
        encoding="utf-8"
    )
    paper = (repo / "formal" / "Problems" / "JugglerPaper.lean").read_text(
        encoding="utf-8"
    )
    assert "## Branch budget" in dossier
    assert "## Decision" in dossier
    assert "PARK" in dossier
    assert "729/256" in dossier
    assert "odd_even_eighth_lt_sq" not in paper
    assert "theorem no_juggler_escape" not in dossier
