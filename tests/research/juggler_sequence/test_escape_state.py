"""Escape-state margin. Not an engine-control or halt test."""

from __future__ import annotations

from research.juggler_sequence.escape_state import (
    CLASS_COMPLEX,
    CLASS_COUNTER,
    HARD_STARTS,
    LEAN_NEW,
    classify,
    escape_row,
    image_margin,
    lean_api_present,
    render_markdown,
    run_probe,
    walk_prefixes,
)
from research.juggler_sequence.near_extremal_prefixes import exponent_gap
from research.juggler_sequence.power_itineraries import ANTI_OVERCLAIM, floor_power, odd_count


def test_margin_identity_on_nonpositive_gap():
    row = escape_row(5, 3)
    assert row["word"] == "OOE"
    assert row["exponent_gap"] <= 0
    assert row["margin_from_gap"] == row["margin_from_image"] == 1288991
    assert row["identity_holds"] is True
    assert row["image_ge_n"] is True
    assert row["escape"] is True


def test_margin_sign_is_image_versus_start():
    for n, k, ge in ((5, 3, True), (5, 4, False), (9, 3, True)):
        row = escape_row(n, k)
        margin = image_margin(n, row["image"], k)
        if margin is None:
            continue
        assert (margin >= 0) is ge
        assert row["image_ge_n"] is ge


def test_thirty_seven_escape_images_recede():
    walk = walk_prefixes(37)
    escape = [row for row in walk if row["escape"]]
    assert escape[0]["word"] == "OOOOE"
    assert escape[0]["image"] == 9317
    assert escape[-1]["image"] == 24906114455136
    assert escape[-1]["image"] - 37 > escape[0]["image"] - 37


def test_margin_zero_is_return():
    row = escape_row(1, 1)
    assert row["margin_zero"] is True
    assert row["image"] == 1
    scan = run_probe()
    assert scan["window"]["margin_zero"] == []


def test_hard_starts_and_window():
    scan = run_probe()
    assert [item["n"] for item in scan["hard"]] == list(HARD_STARTS)
    assert scan["window"]["identity_failures"] == []
    assert scan["window"]["sign_failures"] == []
    assert scan["window"]["image_not_approaching"]
    assert scan["window"]["escape_count"] == 187
    assert scan["explicit_L"] is False
    assert scan["residual_step_extended"] is False
    assert scan["adversarial_engine"] is False


def test_lean_gate_adds_no_file():
    lean = lean_api_present()
    assert lean["sorry_free"] is True
    assert lean["EscapeState_absent"] is True
    assert lean["power_bound_compensated_contracts"] is True
    assert lean["ResidualStep_not_extended"] is True
    assert not LEAN_NEW.is_file()


def test_classify_complex():
    scan = run_probe()
    lean = lean_api_present()
    decision = classify(scan["window"], lean)
    assert decision["classification"] == CLASS_COMPLEX
    assert CLASS_COUNTER in decision["secondary"]
    text = render_markdown(
        {
            "decision": decision,
            "scan": scan,
            "lean": lean,
            "engine_control_layer_modified": False,
            "anti_overclaim": {
                **dict(ANTI_OVERCLAIM),
                "escape_margin_is_new_progress": False,
                "search_horizon_is_L": False,
            },
        }
    )
    assert CLASS_COMPLEX in text
    assert "escape_margin_is_new_progress" in text


def test_committed_artifacts_schema():
    import json

    from research.juggler_sequence.escape_state import DATA_DIR, JSON_PATH

    assert JSON_PATH.is_file()
    data = json.loads(JSON_PATH.read_text(encoding="utf-8"))
    assert data["experiment"] == "juggler_escape_state"
    assert data["engine_control_layer_modified"] is False
    assert data["decision"]["classification"] == CLASS_COMPLEX
    assert data["anti_overclaim"]["escape_margin_is_new_progress"] is False
    assert data["lean"]["EscapeState_absent"] is True
    assert data["scan"]["adversarial_engine"] is False
    assert (DATA_DIR / "analysis" / "window.json").is_file()


def test_floor_power_unchanged():
    assert floor_power(1) == 1
    assert floor_power(5) == 11
    assert floor_power(37) == 225
    assert exponent_gap(3, odd_count("OOE")) == -1
