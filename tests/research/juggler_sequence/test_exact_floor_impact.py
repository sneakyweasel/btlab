"""Fast checks for the exact-floor impact census. Not a halt test."""

from __future__ import annotations

from pathlib import Path

from research.juggler_sequence.exact_floor_impact import (
    CLASS_KNOWN,
    DOSSIER_PATH,
    EXISTING_LEAN,
    FORBIDDEN_THEOREMS,
    JSON_PATH,
    NEW_LEAN_FILES,
    anti_overclaim,
    first_descent_path,
    fixture_nine,
    fixture_sixteen,
    fixture_thirty_six,
    lean_api_present,
    pe_census,
    scan_first_descent,
)
from research.juggler_sequence.power_algebra import is_square, local_tight
from research.juggler_sequence.power_words import floor_power

DOSSIER = Path("docs/problems/juggler_exact_floor_impact.md")


def test_fixture_nine_is_exact_odd() -> None:
    row = fixture_nine()
    assert row["state"] == 9
    assert row["image"] == 27
    assert floor_power(9) == 27
    assert row["letter"] == "O"
    assert row["next_letter"] == "O"
    assert row["crumb"] == 0
    assert row["isolated"] is True
    assert row["letter_forced"] is True
    assert local_tight(9) and is_square(9)


def test_fixture_thirty_six_on_orbit_of_three() -> None:
    path = first_descent_path(3)
    assert 36 in path["states"]
    assert path["word"] == "OOOEE"
    row = fixture_thirty_six()
    assert row["state"] == 36
    assert row["image"] == 6
    assert row["letter"] == "E"
    assert row["next_letter"] == "E"
    assert row["crumb"] == 0
    assert row["isolated"] is True
    assert is_square(36) and not is_square(6)


def test_fixture_sixteen_is_even_tower() -> None:
    row = fixture_sixteen()
    assert row["state"] == 16
    assert row["image"] == 4
    assert row["isolated"] is False
    assert row["tower_len"] >= 2
    assert row["path_states"] == [16, 4]
    assert floor_power(4) == 2


def test_identity_audit_small() -> None:
    census = scan_first_descent(n_max=400)
    assert census["identity_ok"] is True
    assert census["n_mismatches"] == 0
    assert census["letter_fail"] == 0
    assert census["walk_fail"] == 0
    assert census["density_ok"] is True
    assert census["e_ok"] is True
    assert census["n_exact_events"] >= 1
    assert census["n_isolated"] >= 1


def test_pe_continuation_is_cube_or_root() -> None:
    pe = pe_census(n_max=200)
    assert pe["continuation_ok"] is True
    assert pe["not_square"] == 0
    assert pe["extra_continuation"] == 0
    for hit in pe["hits"]:
        assert hit["square"] is True
        assert hit["image"] == hit["expected"]


def test_anti_overclaim_and_no_atlas_lean() -> None:
    anti = anti_overclaim()
    assert anti["halt_theorem"] is False
    assert anti["paper_a_modified"] is False
    assert anti["n0_raised"] is False
    assert anti["atlas_recensus"] is False
    assert anti["floor_boundary_reopened"] is False
    assert anti["new_lean_file"] is False
    assert anti["companion_edited"] is False
    lean = lean_api_present()
    assert lean["sorry_free"] is True
    for name in EXISTING_LEAN:
        assert lean[name] is True, name
    for name in FORBIDDEN_THEOREMS:
        assert lean[f"has_{name}"] is False, name
    assert lean["new_lean_file"] is False
    for path in NEW_LEAN_FILES:
        assert path.exists() is False
    source = Path("src/research/juggler_sequence/exact_floor_impact.py").read_text(
        encoding="utf-8"
    )
    assert "research.juggler_sequence.atlas" not in source
    assert "gpu_census" not in source
    assert "word_atlas.sqlite" not in source


def test_dossier_headings_exist() -> None:
    text = DOSSIER.read_text(encoding="utf-8")
    assert "## Branch budget" in text
    assert "## Decision" in text
    assert "## Publication assessment" in text
    assert "CLOSE" in text
    assert "Paper A" in text
    assert "atlas recensus" in text.lower() or "word-atlas recensus" in text


def test_science_artifact_when_present() -> None:
    if not JSON_PATH.exists():
        return
    import json

    summary = json.loads(JSON_PATH.read_text(encoding="utf-8"))
    assert summary["classification"] == CLASS_KNOWN
    assert summary["descent"]["identity_ok"] is True
    assert summary["pe"]["continuation_ok"] is True
    assert summary["anti_overclaim"]["atlas_recensus"] is False
    assert summary["anti_overclaim"]["paper_a_modified"] is False
    assert DOSSIER_PATH.exists()
