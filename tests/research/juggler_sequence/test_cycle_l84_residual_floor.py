"""L=84 residual-floor leftover census. Not a halt test."""

from __future__ import annotations

import json
from pathlib import Path

from research.juggler_sequence.cycle_l84_residual_floor import (
    CLASS_PARK,
    FAMILY_LENGTHS,
    GLOBAL_CONST1_FLOOR,
    HEIGHT_ALL_M_FLOOR,
    LIVE_FLOOR,
    census_at_floor,
    cite_n162_certificate,
    classify_census,
    is_84_family,
)
from research.juggler_sequence.cycle_position_finance import (
    CURRENT_LEAN_RESIDUAL_FLOOR,
    l84_exclusion_floors,
)
from research.juggler_sequence.lean_paths import (
    JUGGLER_DIR,
    JUGGLER_PAPER_BARREL,
)

REPO = Path(__file__).resolve().parents[3]
ARTIFACT = (
    REPO
    / "data"
    / "research"
    / "juggler"
    / "cycle_position_finance"
    / "leftover_at_floors.json"
)


def _artifact() -> dict:
    return json.loads(ARTIFACT.read_text(encoding="utf-8"))


def test_l84_kill_floors_unchanged():
    table = l84_exclusion_floors()
    assert table["current_lean_floor"] == LIVE_FLOOR
    assert LIVE_FLOOR == CURRENT_LEAN_RESIDUAL_FLOOR
    assert table["const_1"]["joint_all_m"] == HEIGHT_ALL_M_FLOOR == 1981
    assert table["const_1"]["height_all_m"] == 1981
    assert table["const_1"]["global"] == GLOBAL_CONST1_FLOOR == 4756


def test_height_at_1981_renames_to_168():
    scan = census_at_floor(HEIGHT_ALL_M_FLOOR, const=1.0)
    assert scan["named"]["global"]["L"] == 84
    assert scan["named"]["height"]["L"] == 168
    assert scan["named"]["joint"]["L"] == 168
    assert 84 not in scan["height_survivors"]
    assert 168 in scan["height_survivors"]
    assert 569 in scan["height_survivors"]
    assert is_84_family(168) is True


def test_global_at_4756_renames_to_168_height_jumps():
    scan = census_at_floor(GLOBAL_CONST1_FLOOR, const=1.0)
    assert scan["named"]["global"]["L"] == 168
    assert scan["named"]["height"]["L"] == 569
    assert scan["named"]["joint"]["L"] == 569
    assert 84 not in scan["global_survivors"]
    assert 168 in scan["global_survivors"]
    assert scan["height_survivors"] == [569]


def test_classify_is_park_rename():
    decision = classify_census(
        {"named_height_leftover_at_1981": {"L": 168}}
    )
    assert decision["classification"] == CLASS_PARK
    assert decision["named_leftover"] == 168
    assert "rename" in decision["reason"]


def test_artifact_pins_family_floors_and_certificates():
    data = _artifact()
    assert data["named_height_leftover_at_1981"]["L"] == 168
    assert data["even_lt_sq_unchanged_at_1981"] is True
    by_l = {row["L"]: row for row in data["family_kill_floors"]["const_1"]}
    assert tuple(FAMILY_LENGTHS) == (84, 168, 252, 336, 420, 504, 569, 588)
    assert by_l[84]["height_all_m"] == 1981
    assert by_l[168]["height_all_m"] == 1983
    assert by_l[168]["global"] == 4761
    assert by_l[569]["height_all_m"] == 19975
    assert by_l[588]["height_all_m"] == 1991
    n162 = cite_n162_certificate()
    assert n162["present"] is True
    assert n162["covers_1981"] is True
    assert n162["covers_4756"] is True
    checksums = data["certificates"]["checksums"]
    assert checksums["1981"]["verified"] is True
    assert checksums["1981"]["max_bits"] == 900
    assert checksums["4756"]["verified"] is True
    assert checksums["4756"]["max_bits"] == 19694
    assert data["certificates"]["harvest"]["backend"] == "cuda"
    assert data["decision"]["classification"] == CLASS_PARK


def test_companion_certificates_exist():
    for n_top in (1981, 4756):
        cert = json.loads(
            (
                REPO
                / "data"
                / "research"
                / "juggler"
                / "cycle_finance"
                / "floor_verify"
                / f"N{n_top}"
                / "certificate.json"
            ).read_text(encoding="utf-8")
        )
        assert cert["verified"] is True
        assert cert["N0"] == n_top
        assert cert["halt_theorem"] is False


def test_dossier_park_and_no_lean_factory():
    dossier = (
        REPO / "docs" / "problems" / "juggler_cycle_l84_residual_floor.md"
    ).read_text(encoding="utf-8")
    paper = JUGGLER_PAPER_BARREL.read_text(encoding="utf-8")
    assert "## Branch budget" in dossier
    assert "## Decision" in dossier
    assert "## Publication assessment" in dossier
    assert "**PARK**" in dossier
    assert "168" in dossier
    assert "Not a halt theorem" in dossier
    assert "reachesOne_of_lt_1981" in dossier
    assert (JUGGLER_DIR / "CyclePositionFinance.lean").is_file() is False
    assert "CyclePositionFinance" not in paper
    assert "theorem no_cycle_itinerary_any_length" not in dossier
    assert "juggler_cycle_finance_note.md" in dossier
