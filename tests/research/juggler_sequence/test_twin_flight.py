"""Twin-flight pair object. Not a halt test."""

from __future__ import annotations

import json
from pathlib import Path

from research.juggler_sequence.twin_flight import (
    CALIBRATION_STATE,
    CLASS_CAP_SEPARATE,
    CLASS_CAP_SHADOW,
    CLASS_CLOSED,
    CLASS_EXACT,
    CLASS_GREEN,
    CLASS_INCOMPLETE,
    CLASS_PARK,
    CLASS_SEPARATE,
    CLASS_SHADOW,
    CLASS_SHIFT,
    EXISTING_LEAN,
    FORBIDDEN_NEW_API,
    FORBIDDEN_THEOREMS,
    HARD_LABS,
    NEW_LEAN_FILES,
    PAIR_CLASSES,
    compare_pair,
    first_step_delta,
    lean_api_present,
    probe_payload,
    render_markdown,
    walk_trajectory,
    window_starts,
    write_artifacts,
)


def _orbit(n: int, states: list[int], status: str = "HIT_ONE") -> dict:
    peak = max(states)
    return {
        "n": n,
        "states": tuple(states),
        "H": peak,
        "H_bits": peak.bit_length(),
        "status": status,
        "tau": len(states) - 1 if states[-1] == 1 else None,
        "word": "",
        "steps": len(states) - 1,
    }


def test_first_step_delta_is_order_three_over_n():
    row = first_step_delta(37)
    assert row["T_n"] == 225
    assert row["T_n_plus_2"] == 243
    assert row["d_1"] == 18
    assert abs(row["delta_1"] - 18 / 243) < 1e-12
    assert 0.02 <= row["delta_1"] <= 0.2
    assert abs(row["approx_3_over_n"] - 3 / 37) < 1e-12


def test_window_preserves_odd_parity():
    starts = window_starts(37)
    assert starts == (27, 29, 31, 33, 35, 37, 39, 41, 43, 45, 47)
    assert all(n % 2 == 1 for n in starts)
    assert 37 in HARD_LABS
    assert 33391 in HARD_LABS


def test_365_and_501_share_763():
    left = walk_trajectory(365)
    right = walk_trajectory(501)
    assert CALIBRATION_STATE in left["states"]
    assert CALIBRATION_STATE in right["states"]
    row = compare_pair(left, right)
    assert row["class"] in CONTACT_OR_SHIFT
    assert row["common"] is not None
    assert row["common"]["state"] == CALIBRATION_STATE


CONTACT_OR_SHIFT = {CLASS_EXACT, CLASS_SHIFT}


def test_three_enters_five_as_shifted_flight():
    row = compare_pair(walk_trajectory(3), walk_trajectory(5))
    assert row["class"] == CLASS_SHIFT
    assert row["common"]["state"] == 5
    assert row["common"]["r"] != 0
    assert row["tau_merge"] is None


def test_sink_one_is_not_a_merge():
    left = _orbit(15, [15, 58, 7, 18, 4, 2, 1])
    right = _orbit(21, [21, 96, 9, 27, 140, 11, 36, 6, 2, 1])
    row = compare_pair(left, right)
    assert row["class"] == CLASS_SEPARATE
    assert row["tau_merge"] is None
    assert row["common"] is None


def test_classification_exclusivity():
    exact = compare_pair(
        _orbit(9, [9, 27, 140, 16, 4, 2, 1]),
        _orbit(11, [11, 36, 6, 16, 4, 2, 1]),
    )
    assert exact["class"] == CLASS_EXACT
    assert exact["tau_merge"] == 3
    assert exact["even_reset"] is True

    shifted = compare_pair(
        _orbit(10, [10, 20, 30, 40]),
        _orbit(12, [12, 30, 40, 50]),
    )
    assert shifted["class"] == CLASS_SHIFT
    assert shifted["tau_merge"] is None
    assert shifted["common"]["state"] == 30
    assert shifted["common"]["r"] != 0

    shadow = compare_pair(
        _orbit(100, [100, 200, 300, 400, 500, 600, 700, 800, 810]),
        _orbit(102, [102, 204, 306, 408, 510, 612, 714, 816, 826]),
        shadow_min_steps=8,
    )
    assert shadow["class"] == CLASS_SHADOW
    assert shadow["common"] is None
    assert shadow["max_delta"] < 0.05

    capped = compare_pair(
        _orbit(7, [7, 18, 4], status="STEP_CAP"),
        _orbit(9, [9, 27, 140], status="STEP_CAP"),
    )
    assert capped["class"] == CLASS_CAP_SEPARATE
    assert capped["capped"] is True

    close_capped = compare_pair(
        _orbit(50, [50, 60, 70], status="BIT_CAP"),
        _orbit(52, [52, 62, 72], status="BIT_CAP"),
    )
    assert close_capped["class"] == CLASS_CAP_SHADOW

    seen = {
        exact["class"],
        shifted["class"],
        shadow["class"],
        capped["class"],
        close_capped["class"],
        CLASS_SEPARATE,
    }
    assert seen <= set(PAIR_CLASSES)
    assert len(seen) == 6


def test_probe_and_classify_vocabulary():
    payload = probe_payload()
    assert payload["experiment"] == "juggler_twin_flight"
    assert payload["engine_control_layer_modified"] is False
    assert payload["anti_overclaim"]["coalescence_is_not_termination"] is False
    assert payload["anti_overclaim"]["global_termination"] is False
    assert payload["decision"]["classification"] in {
        CLASS_CLOSED,
        CLASS_GREEN,
        CLASS_PARK,
        CLASS_INCOMPLETE,
    }
    assert payload["decision"]["classification"] != CLASS_INCOMPLETE
    scan = payload["scan"]
    assert scan["cross_lab"]["calibration_365_501_at_763"] is True
    assert scan["first_step_ok"] is True
    assert scan["control"]["pairs"] == 999
    assert scan["hard_adjacent"]["pairs"] == 90
    text = render_markdown(payload)
    assert "NOT_OBSERVED_WITHIN_BOUND" in text
    assert "coalescence_is_not_termination" in text


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
    for path in NEW_LEAN_FILES:
        assert path.is_file() is False


def test_write_artifacts_and_dossier_boundary():
    payload = write_artifacts()
    repo = Path(__file__).resolve().parents[3]
    dossier = (repo / "docs" / "problems" / "juggler_twin_flight.md").read_text(
        encoding="utf-8"
    )
    json_path = repo / "docs" / "research" / "juggler_twin_flight.json"
    md_path = repo / "docs" / "research" / "juggler_twin_flight.md"
    summary = repo / "data" / "research" / "juggler" / "twin_flight" / "summary.json"
    assert json_path.is_file()
    assert md_path.is_file()
    assert summary.is_file()
    stored = json.loads(json_path.read_text(encoding="utf-8"))
    assert payload["decision"]["classification"] == stored["decision"]["classification"]
    assert "## Branch budget" in dossier
    assert "## Decision" in dossier
    assert "## Publication assessment" in dossier
    assert "oeis-A007320" in dossier
    assert "high_merge" in dossier
    assert "**CLOSE**" in dossier
    assert "TWIN_FLIGHT_CLOSED" in dossier
    assert "TwinFlight" not in (
        repo / "formal" / "Problems" / "JugglerPaper.lean"
    ).read_text(encoding="utf-8")
    assert "theorem no_juggler_escape" not in dossier
    assert "10^9" in dossier
