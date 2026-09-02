"""Position-dependent m-finance. Not a halt test."""

from __future__ import annotations

import json
from pathlib import Path

from research.conjectures import get_conjecture
from research.juggler_sequence.cycle_m_finance import steiner_rhs
from research.juggler_sequence.cycle_position_finance import (
    CLASS_CLOSED,
    CLASS_GREEN,
    CLASS_INCOMPLETE,
    CLASS_PARK,
    COMPARE_FLOOR,
    CURRENT_LEAN_RESIDUAL_FLOOR,
    EXISTING_LEAN,
    FOCUS_LENGTHS,
    FORBIDDEN_LEAN_FILES,
    FORBIDDEN_NEW_API,
    FORBIDDEN_THEOREMS,
    LEAN_CYCLE_FLOOR,
    classify,
    height_allocation,
    l84_exclusion_floors,
    lean_api_present,
    leftover_table,
    odd_run_heights,
    position_kills_at_floor,
    position_rhs,
    probe_payload,
    render_markdown,
)

REPO = Path(__file__).resolve().parents[3]


def test_odd_run_heights_at_257():
    heights = odd_run_heights(LEAN_CYCLE_FLOOR)
    assert heights[0] == 257
    assert heights[1] == 4121
    assert heights[2] == 264547
    assert all(height % 2 == 1 for height in heights)


def test_height_allocation_is_at_most_m_per_level():
    assert height_allocation(0, 3) == []
    assert height_allocation(5, 3) == [3, 2]
    assert height_allocation(6, 3) == [3, 3]
    assert height_allocation(7, 1) == [1] * 7


def test_position_rhs_beats_joint_when_climbs_exceed_m():
    joint = steiner_rhs(LEAN_CYCLE_FLOOR, 84, 53, 1)
    pos = position_rhs(LEAN_CYCLE_FLOOR, 84, 53, 1)
    assert pos < joint
    assert position_kills_at_floor(84, 53, 0.00208595, 1) is True
    assert 0.00208595 < joint


def test_position_matches_joint_when_every_climb_can_sit_at_t1():
    # L=38, o=24, m=14: 10 climbs, 14 circuits, so all climbs at tau_1.
    joint = steiner_rhs(LEAN_CYCLE_FLOOR, 38, 24, 14)
    pos = position_rhs(LEAN_CYCLE_FLOOR, 38, 24, 14)
    assert abs(pos - joint) / joint < 0.01


def test_leftover_table_kills_thirty_eight_and_eighty_four_small_m():
    leftovers = {row["L"]: row for row in leftover_table()}
    thirty_eight = leftovers[38]
    assert thirty_eight["global_n_max"] > LEAN_CYCLE_FLOOR
    assert thirty_eight["joint_kills_all_m"] is True
    assert thirty_eight["new_exclusions"] == []
    eighty_four = leftovers[84]
    assert eighty_four["joint_kills_m1"] is False
    assert eighty_four["position_kills_m1"] is True
    assert eighty_four["new_exclusions"] == [1, 2]
    assert eighty_four["position_kills_all_m"] is False


def test_l84_exclusion_floors_height_kills_first():
    """Joint/height kill all of L=84 before a 4756 residual-floor raise."""

    table = l84_exclusion_floors()
    assert table["current_lean_floor"] == CURRENT_LEAN_RESIDUAL_FLOOR
    assert table["at_current_floor"]["joint_kills_m_const1"] == []
    assert table["at_current_floor"]["height_kills_m_const1"] == [1, 2]
    assert table["at_current_floor"]["height_kills_m_six_fifths"] == [1, 2]
    const1 = table["const_1"]
    assert const1["global"] == 4756
    assert const1["joint_all_m"] == const1["height_all_m"] == 1981
    assert const1["height_m1"] == 121
    assert const1["height_m2"] == 199
    assert const1["height_m3"] == 273
    assert const1["joint_m1"] == 271
    assert const1["height_m1"] < CURRENT_LEAN_RESIDUAL_FLOOR < const1["height_m3"]
    assert const1["joint_all_m"] < const1["global"]
    six = table["six_fifths"]
    assert six["global_n_max"] == 5599
    assert six["global"] == 5600
    assert six["joint_all_m"] == six["height_all_m"] == 2325
    artifact = json.loads(
        (
            REPO
            / "data"
            / "research"
            / "juggler"
            / "cycle_position_finance"
            / "l84_floors.json"
        ).read_text(encoding="utf-8")
    )
    assert artifact["const_1"]["global"] == const1["global"]
    assert artifact["const_1"]["joint_all_m"] == const1["joint_all_m"]
    assert artifact["at_floor_261"]["height_kills_m"] == [1, 2]
    refuted = get_conjecture("juggler_cycle_finance_l84_floor_4756")
    assert refuted["status"] == "REFUTED"


def test_floor_53_kills_thirty_eight_small_m_only_by_height():
    leftovers = {row["L"]: row for row in leftover_table(n0=COMPARE_FLOOR)}
    thirty_eight = leftovers[38]
    assert thirty_eight["joint_kills_all_m"] is False
    assert 3 in thirty_eight["new_exclusions"]
    assert 4 in thirty_eight["new_exclusions"]


def test_probe_and_classify_vocabulary():
    payload = probe_payload()
    assert payload["experiment"] == "juggler_cycle_position_finance"
    assert payload["engine_control_layer_modified"] is False
    assert payload["decision"]["classification"] in {
        CLASS_GREEN,
        CLASS_PARK,
        CLASS_CLOSED,
        CLASS_INCOMPLETE,
    }
    assert payload["decision"]["classification"] == CLASS_GREEN
    assert payload["anti_overclaim"]["halt_theorem"] is False
    assert payload["anti_overclaim"]["new_paper"] is False
    assert payload["anti_overclaim"]["new_lean"] is False
    assert payload["scan"]["kills_length_thirty_eight_all_m_joint"] is True
    assert payload["scan"]["kills_length_eighty_four_m1_position"] is True
    assert payload["scan"]["joint_misses_eighty_four_m1"] is True
    text = render_markdown(payload)
    assert "Not a new paper" in text
    assert "Not a halt theorem" in text
    lean = lean_api_present()
    assert classify(payload["scan"], lean)["classification"] == CLASS_GREEN


def test_lean_api_forbids_new_position_layer():
    lean = lean_api_present()
    assert lean["sorry_free"] is True
    for name in EXISTING_LEAN:
        assert lean[name] is True, name
    for name in FORBIDDEN_THEOREMS:
        assert lean[f"has_{name}"] is False, name
    for name in FORBIDDEN_NEW_API:
        assert lean[f"has_api_{name}"] is False, name
    assert lean["cycle_finance_present"] is True
    assert lean["no_extra_position_file"] is True
    assert lean["not_in_paper_barrel"] is True
    for path in FORBIDDEN_LEAN_FILES:
        assert path.is_file() is False


def test_science_summary_is_green():
    summary = json.loads(
        (
            REPO
            / "data"
            / "research"
            / "juggler"
            / "cycle_position_finance"
            / "summary.json"
        ).read_text(encoding="utf-8")
    )
    assert summary["classification"] == CLASS_GREEN
    assert summary["kills_length_thirty_eight_all_m_joint"] is True
    assert summary["kills_length_eighty_four_m1_position"] is True


def test_dossier_boundary():
    dossier = (
        REPO / "docs" / "problems" / "juggler_cycle_position_finance.md"
    ).read_text(encoding="utf-8")
    paper = (REPO / "formal" / "Problems" / "JugglerPaper.lean").read_text(
        encoding="utf-8"
    )
    assert "## Branch budget" in dossier
    assert "## Decision" in dossier
    assert "## Publication assessment" in dossier
    assert "**PROMOTE**" in dossier
    assert "not a new paper" in dossier
    assert "simons-de-weger-2005-collatz-m-cycles" in dossier
    assert tuple(FOCUS_LENGTHS) == (19, 38, 84, 168)
    assert "theorem no_cycle_itinerary_any_length" not in dossier
    assert "cycle_itinerary_length_eighty_four_m_ge_three_or_ge_eighty_five" in dossier
    assert "CycleHeightFinance.lean" in dossier
    assert "juggler_cycle_finance_note.md" in dossier
    assert "CyclePositionFinance" not in paper
    assert "cycle_position_finance" not in paper
