"""Minimal first-OO corridor OOEOOE."""

from __future__ import annotations

import json

from research.juggler_sequence.cycle_itinerary import follows_itinerary, image_after
from research.juggler_sequence.first_internal_oo import first_oo_decompose
from research.juggler_sequence.minimal_ooe_corridor import (
    CLASS_GREEN,
    EVEN_DROP_WITNESS,
    FORBIDDEN_THEOREMS,
    LEAN_THEOREMS,
    ODD_CONTINUE_WITNESS,
    WORD,
    classify,
    corridor_states,
    lean_api_present,
    ooe_map,
    ooe_ob_square_cell_gap,
    ooe_square_cell_gap,
    render_markdown,
    run_probe,
    square_cell_gap,
    write_artifacts,
)
from research.juggler_sequence.power_itineraries import ANTI_OVERCLAIM, floor_power


def test_square_cell_comparison():
    assert square_cell_gap(6, 4) is True
    assert ooe_square_cell_gap(2) is True
    assert ooe_square_cell_gap(5) is True
    assert ooe_square_cell_gap(6) is False
    assert ooe_ob_square_cell_gap(2) is True
    assert ooe_ob_square_cell_gap(3) is True
    assert ooe_ob_square_cell_gap(4) is False
    assert (1 << 7) > 3**4
    assert (1 << 8) > 3**5
    assert not ((1 << 9) > 3**6)


def test_corridor_is_minimal_first_oo():
    assert first_oo_decompose(WORD) == (2, 0, 2, "")
    assert first_oo_decompose("OOEOOEE") == (2, 0, 2, "E")
    assert first_oo_decompose("OOEOOEOE") == (2, 0, 2, "OE")


def test_named_witnesses():
    even = corridor_states(EVEN_DROP_WITNESS["n"])
    assert even is not None
    assert even["x3"] == EVEN_DROP_WITNESS["x3"]
    assert even["x6"] == EVEN_DROP_WITNESS["x6"]
    assert even["x6"] < EVEN_DROP_WITNESS["n"] ** 2
    assert even["x6"] % 2 == 0
    assert floor_power(even["x6"]) < EVEN_DROP_WITNESS["n"]
    odd = corridor_states(ODD_CONTINUE_WITNESS["n"])
    assert odd is not None
    assert odd["x3"] == ODD_CONTINUE_WITNESS["x3"]
    assert odd["x6"] == ODD_CONTINUE_WITNESS["x6"]
    assert odd["x6"] % 2 == 1
    assert odd["x6"] < ODD_CONTINUE_WITNESS["n"] ** 2
    assert ooe_map(ODD_CONTINUE_WITNESS["n"]) == odd["x3"]
    assert ooe_map(odd["x3"]) == odd["x6"]


def test_power_bound_implies_below_square():
    n = 69
    assert follows_itinerary(n, WORD)
    x6 = image_after(n, WORD)
    assert x6 ** 64 <= n ** 81
    assert x6 < n * n


def test_probe_and_classify_green():
    scan = run_probe()
    lean = lean_api_present()
    decision = classify(scan, lean)
    assert decision["classification"] == CLASS_GREEN
    window = scan["window"]
    assert window["ge_sq"] == 0
    assert window["even_survive"] == 0
    assert window["hit_n"] == 0
    assert window["below_sq"] == window["follows"]
    assert window["even_drop"] == window["even_land"]
    assert window["odd_land"] > 0
    assert scan["gaps"]["k2_forbids"] is True
    assert scan["gaps"]["b4_forbids"] is False
    assert scan["length_eleven_census"] is False
    assert scan["terminal_cluster_reopen"] is False


def test_lean_api_without_halt_or_z5():
    lean = lean_api_present()
    assert lean["sorry_free"] is True
    for name in LEAN_THEOREMS:
        assert lean[name] is True, name
    for name in FORBIDDEN_THEOREMS:
        assert lean[f"has_{name}"] is False, name
    assert lean["not_in_paper_barrel"] is True
    assert lean["no_new_lean"] is True


def test_classify_render_and_artifacts():
    payload = write_artifacts()
    text = render_markdown(payload)
    assert CLASS_GREEN in text
    assert "n^2" in text or "square" in text.lower()
    from research.juggler_sequence.minimal_ooe_corridor import JSON_PATH

    data = json.loads(JSON_PATH.read_text(encoding="utf-8"))
    assert data["experiment"] == "juggler_minimal_ooe_corridor"
    assert data["decision"]["classification"] == CLASS_GREEN
    assert data["anti_overclaim"]["cycles_impossible"] is False
    assert dict(ANTI_OVERCLAIM)["global_termination"] is False


def test_dossier_boundary():
    from pathlib import Path

    repo = Path(__file__).resolve().parents[3]
    dossier = (repo / "docs" / "problems" / "juggler_minimal_ooe_corridor.md").read_text(
        encoding="utf-8"
    )
    parent = (repo / "docs" / "problems" / "juggler_first_internal_oo.md").read_text(
        encoding="utf-8"
    )
    note = (repo / "docs" / "theory" / "juggler_finite_dynamics_note.md").read_text(
        encoding="utf-8"
    )
    assert "## Branch budget" in dossier
    assert "## Decision" in dossier
    assert "PROMOTE" in dossier
    assert "OOEOOE" in dossier
    assert "juggler_minimal_ooe_corridor" in parent
    assert "theorem no_cycle_itinerary_length_eleven" not in note
    assert "theorem no_juggler_cycle" not in note
