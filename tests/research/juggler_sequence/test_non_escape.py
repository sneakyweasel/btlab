"""Non-escape spine: cycle-or-escape and the CE OOEOOE trap."""

from __future__ import annotations

import json

from research.juggler_sequence.cycle_itinerary import follows_itinerary, image_after
from research.juggler_sequence.non_escape import (
    CLASS_GREEN,
    ESCAPE_PREFIX,
    FORBIDDEN_THEOREMS,
    LEAN_THEOREMS,
    classify,
    eventually_cycles,
    iterate_floor,
    lean_api_present,
    ooeooe_row,
    render_markdown,
    run_probe,
    write_artifacts,
)
from research.juggler_sequence.odd_ooe_landing import first_event
from research.juggler_sequence.power_itineraries import ANTI_OVERCLAIM, floor_power


def test_one_cycles_and_is_not_escape():
    assert eventually_cycles(1) is True
    assert floor_power(1) == 1
    assert iterate_floor(1, 5) == 1


def test_ooeooe_even_landing_drops():
    row = ooeooe_row(69)
    assert row is not None
    assert row["x"] == 212
    assert row["x_even"] is True
    assert row["x_below_sq"] is True
    assert row["even_landing_drop"] is True


def test_ooeooe_odd_landing_case_a_drops():
    row = ooeooe_row(89)
    assert row is not None
    assert row["x"] == 291
    assert row["x_even"] is False
    assert row["z"] % 2 == 0
    assert row["z_below_sq"] is True
    assert row["even_z_drop"] is True
    event = first_event(89)
    assert event is not None
    assert event["case"] == "A"
    assert event["drop"] is True


def test_ooeooe_forces_oo_on_365():
    row = ooeooe_row(365)
    assert row is not None
    assert row["x"] == 1749
    assert row["forced_oo"] is True
    assert row["z_below_sq"] is True
    assert follows_itinerary(365, "OOEOOE")
    assert image_after(365, "OOEOOE") == 1749


def test_365_chain_is_a_finite_escape_prefix():
    chain = list(ESCAPE_PREFIX)
    assert chain == [365, 763, 1749, 4447]
    current = chain[0]
    for nxt in chain[1:]:
        assert follows_itinerary(current, "OOE")
        assert image_after(current, "OOE") == nxt
        assert nxt > current
        current = nxt
    assert follows_itinerary(365, "OOEOOE")


def test_probe_and_classify_green():
    scan = run_probe()
    lean = lean_api_present()
    decision = classify(scan, lean)
    assert decision["classification"] == CLASS_GREEN
    window = scan["window"]
    assert window["even_survive"] == 0
    assert window["a_survive"] == 0
    assert window["x_ge_sq"] == 0
    assert window["follows"] > 0
    assert window["case_b"] > 0
    assert scan["escape_prefix"]["unbounded_orbit"] is False
    assert scan["escape_prefix"]["monotone"] is True
    assert scan["finite_coeff_stop_theorem"] is False
    assert scan["escape_margin_m"] is False


def test_lean_api_without_halt():
    lean = lean_api_present()
    assert lean["sorry_free"] is True
    for name in LEAN_THEOREMS:
        assert lean[name] is True, name
    for name in FORBIDDEN_THEOREMS:
        assert lean[f"has_{name}"] is False, name
    assert lean["in_laboratory_barrel"] is True
    assert lean["not_in_paper_barrel"] is True
    assert lean["no_halt_theorem"] is True
    assert lean["no_coeff_stop_theorem"] is True


def test_classify_render_and_artifacts():
    payload = write_artifacts()
    text = render_markdown(payload)
    assert CLASS_GREEN in text
    from research.juggler_sequence.non_escape import JSON_PATH

    data = json.loads(JSON_PATH.read_text(encoding="utf-8"))
    assert data["experiment"] == "juggler_non_escape"
    assert data["decision"]["classification"] == CLASS_GREEN
    assert data["anti_overclaim"]["no_escape"] is False
    assert data["anti_overclaim"]["cycles_impossible"] is False
    assert dict(ANTI_OVERCLAIM)["global_termination"] is False


def test_dossier_boundary():
    from pathlib import Path

    repo = Path(__file__).resolve().parents[3]
    dossier = (repo / "docs" / "problems" / "juggler_non_escape.md").read_text(
        encoding="utf-8"
    )
    residual = (repo / "docs" / "problems" / "juggler_residual_path.md").read_text(
        encoding="utf-8"
    )
    assert "## Branch budget" in dossier
    assert "## Decision" in dossier
    assert "PROMOTE" in dossier
    assert "not a halt theorem" in dossier.lower() or "not a halt" in dossier
    assert "EscapesToInfinity" in dossier
    assert "unbounded" in residual
