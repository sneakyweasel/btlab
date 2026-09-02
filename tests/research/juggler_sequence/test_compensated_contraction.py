"""Defect-compensated contraction. Not an engine-control test."""

from __future__ import annotations

from research.juggler_sequence.lean_paths import juggler_text

from research.juggler_sequence.compensated_contraction import (
    CLASS_FOUND,
    LEAN_THEOREMS,
    classify,
    eoo_witnesses,
    first_defect_sufficient,
    follows_itinerary,
    formal_gap,
    image_after,
    lean_api_present,
    render_markdown,
    run_probe,
    scan_word,
    word_row,
)
from research.juggler_sequence.envelope_defect import local_defect
from research.juggler_sequence.power_itineraries import ANTI_OVERCLAIM, LEAN_PATH, floor_power


def test_eoo_witnesses_contract_and_first_defect_fails():
    assert follows_itinerary(2, "EOO")
    assert follows_itinerary(12, "EOO")
    assert follows_itinerary(14, "EOO")
    assert follows_itinerary(10, "EOO")
    assert image_after(2, "EOO") == 1
    assert image_after(12, "EOO") == 11
    assert image_after(14, "EOO") == 11
    assert image_after(10, "EOO") == 11
    for n, image in ((2, 1), (12, 11), (14, 11)):
        row = word_row(n, "EOO")
        assert row is not None
        assert row["actual_contraction"] is True
        assert row["image"] == image
        assert row["first_defect_certifies"] is False
        assert first_defect_sufficient(n, "EOO") is False
        gap = formal_gap(n, 3, 2)
        assert gap is not None
        assert local_defect(n) < gap
    ten = word_row(10, "EOO")
    assert ten is not None
    assert ten["actual_contraction"] is False


def test_ooe_oeo_no_contraction_on_small_window():
    ooe = scan_word("OOE", 400, n_min=3, step=2)
    oeo = scan_word("OEO", 400, n_min=3, step=2)
    assert ooe["realized"] >= 1
    assert oeo["realized"] >= 1
    assert ooe["contract_count"] == 0
    assert oeo["contract_count"] == 0
    assert follows_itinerary(5, "OOE")
    assert image_after(5, "OOE") == 6
    assert follows_itinerary(15, "OEO")
    assert image_after(15, "OEO") == 18


def test_eoo_scan_finds_only_the_three_witnesses():
    scan = scan_word("EOO", 200, n_min=2, step=2)
    ns = [row["n"] for row in scan["contracts"]]
    assert ns == [2, 12, 14]
    assert scan["first_defect_sufficient_count"] == 0


def test_examples_and_lean_api():
    witnesses = eoo_witnesses()
    assert [row["n"] for row in witnesses] == [2, 12, 14]
    assert witnesses[0]["actual_deficit"] == 511
    assert witnesses[0]["envelope_gap_to_contraction"] == 256
    lean = lean_api_present()
    assert lean["sorry_free"] is True
    for name in LEAN_THEOREMS:
        assert lean[name] is True
    text = juggler_text()
    assert "PowerHeight" not in text
    assert "theorem mixed_word_power_lt" not in text
    assert "sorry" not in text
    assert "admit" not in text


def test_classify_found_when_lean_present():
    scan = run_probe(n_max=80, eoo_even_max=40, k4_n_max=40)
    lean = lean_api_present()
    decision = classify(scan, lean)
    assert decision["classification"] == CLASS_FOUND
    payload = {
        "decision": decision,
        "scan": scan,
        "lean": lean,
        "engine_control_layer_modified": False,
        "anti_overclaim": dict(ANTI_OVERCLAIM),
    }
    text = render_markdown(payload)
    assert CLASS_FOUND in text
    assert "global_termination" in text
    assert all(v is False for v in ANTI_OVERCLAIM.values())


def test_run_probe_small_has_eoo_family_only():
    scan = run_probe(n_max=80, eoo_even_max=40, k4_n_max=40)
    assert scan["length3"]["EOO"]["contract_count"] == 3
    assert scan["length3"]["OOE"]["contract_count"] == 0
    assert scan["length3"]["OEO"]["contract_count"] == 0
    assert scan["eoo_witnesses"][0]["word"] == "EOO"


def test_committed_artifacts_schema():
    import json
    from research.juggler_sequence.compensated_contraction import JSON_PATH

    assert JSON_PATH.is_file()
    data = json.loads(JSON_PATH.read_text(encoding="utf-8"))
    assert data["experiment"] == "juggler_compensated_contraction"
    assert data["engine_control_layer_modified"] is False
    assert data["decision"]["classification"] == CLASS_FOUND
    assert data["lean"]["sorry_free"] is True
    for name in LEAN_THEOREMS:
        assert data["lean"][name] is True
    ns = [row["n"] for row in data["scan"]["eoo_witnesses"]]
    assert ns == [2, 12, 14]


def test_floor_power_unchanged():
    assert floor_power(2) == 1
    assert floor_power(12) == 3
    assert floor_power(3) == 5
    assert floor_power(5) == 11
