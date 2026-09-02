"""EOO square-root cell mechanism. Not an engine-control test."""

from __future__ import annotations

from research.juggler_sequence.lean_paths import juggler_text

from research.juggler_sequence.compensated_contraction import follows_itinerary, image_after
from research.juggler_sequence.eoo_cell_mechanism import (
    CLASS_GREEN,
    CLASS_PATTERN,
    LEAN_THEOREMS,
    classify,
    eoo_cell_output,
    eoo_witness_table,
    follows_eoo_sqrt,
    lean_api_present,
    render_markdown,
    residue,
    run_probe,
    scan_eoo_cells,
    scan_first_even_cells,
    scan_word_sqrt_cells,
    sqrt_cell,
)
from research.juggler_sequence.power_itineraries import ANTI_OVERCLAIM, LEAN_PATH, floor_power


def test_eoo_cell_output_and_threshold():
    assert eoo_cell_output(1) == 1
    assert eoo_cell_output(3) == 11
    assert eoo_cell_output(5) == 36
    assert sqrt_cell(1) == (1, 4)
    assert sqrt_cell(3) == (9, 16)
    assert follows_eoo_sqrt(2)
    assert follows_eoo_sqrt(10)
    assert follows_eoo_sqrt(12)
    assert follows_eoo_sqrt(14)
    assert not follows_eoo_sqrt(4)
    assert not follows_eoo_sqrt(16)
    for n in (2, 10, 12, 14):
        assert follows_itinerary(n, "EOO") == follows_eoo_sqrt(n)
        q, _r = residue(n)
        assert image_after(n, "EOO") == eoo_cell_output(q)
        assert (image_after(n, "EOO") < n) == (n > eoo_cell_output(q))


def test_witness_table_residues_are_not_a_pattern():
    rows = {row["n"]: row for row in eoo_witness_table()}
    assert rows[2]["q"] == 1 and rows[2]["r"] == 1
    assert rows[10]["q"] == 3 and rows[10]["r"] == 1
    assert rows[12]["q"] == 3 and rows[12]["r"] == 3
    assert rows[14]["q"] == 3 and rows[14]["r"] == 5
    assert rows[2]["contracts"] is True
    assert rows[10]["contracts"] is False
    assert rows[12]["contracts"] is True
    assert rows[14]["contracts"] is True
    assert rows[10]["T3_n"] == rows[12]["T3_n"] == 11


def test_eoo_cells_recover_exactly_three_starts():
    scan = scan_eoo_cells(q_max=40)
    assert scan["constancy_failures"] == []
    assert scan["threshold_failures"] == []
    assert scan["contracting_starts"] == [2, 12, 14]
    by_q = {cell["q"]: cell for cell in scan["cells"]}
    assert by_q[1]["output"] == 1 and by_q[1]["contracts"] == [2]
    assert by_q[3]["output"] == 11 and by_q[3]["contracts"] == [12, 14]
    assert by_q[3]["realized"] == [10, 12, 14]
    assert by_q[5]["output"] == 36
    assert by_q[5]["output_lt_cell_end"] is False
    assert by_q[5]["contracts"] == []
    for cell in scan["cells"]:
        if cell["q"] >= 5 and cell["realized"]:
            assert cell["output"] >= (cell["q"] + 1) ** 2
            assert cell["contracts"] == []


def test_ooe_oeo_vary_on_n_sqrt_cells():
    ooe = scan_word_sqrt_cells("OOE", q_max=40, n_parity=1)
    oeo = scan_word_sqrt_cells("OEO", q_max=40, n_parity=1)
    assert ooe["varying_cells"] >= 1
    assert oeo["varying_cells"] >= 1
    assert ooe["varying_cells"] > ooe["constant_cells"]
    assert oeo["varying_cells"] > oeo["constant_cells"]
    assert follows_itinerary(5, "OOE")
    assert image_after(5, "OOE") == 6


def test_eooo_same_freeze_only_n_two():
    eooo = scan_first_even_cells("EOOO", q_max=40)
    assert eooo["constancy_failures"] == []
    assert eooo["contracting_starts"] == [2]
    by_q = {cell["q"]: cell for cell in eooo["cells"]}
    assert by_q[1]["output"] == 1
    assert by_q[3]["output"] == 36
    assert by_q[3]["output_lt_cell_end"] is False


def test_examples_and_lean_api():
    lean = lean_api_present()
    assert lean["sorry_free"] is True
    for name in LEAN_THEOREMS:
        assert lean[name] is True
    assert lean["eooCellOutput_present"] is True
    assert lean["certificate_present"] is True
    text = juggler_text()
    assert "PowerHeight" not in text
    assert "theorem mixed_word_power_lt" not in text
    assert "sorry" not in text
    assert "admit" not in text
    assert "theorem power_bound_compensated_contracts" in text


def test_classify_green_on_small_probe():
    scan = run_probe(q_max=20, length4_n_max=40)
    lean = lean_api_present()
    decision = classify(scan, lean)
    assert decision["classification"] == CLASS_GREEN
    assert decision.get("secondary") == CLASS_PATTERN
    payload = {
        "decision": decision,
        "scan": scan,
        "lean": lean,
        "engine_control_layer_modified": False,
        "anti_overclaim": dict(ANTI_OVERCLAIM),
    }
    text = render_markdown(payload)
    assert CLASS_GREEN in text
    assert "global_termination" in text
    assert all(v is False for v in ANTI_OVERCLAIM.values())


def test_committed_artifacts_schema():
    import json

    from research.juggler_sequence.eoo_cell_mechanism import JSON_PATH

    assert JSON_PATH.is_file()
    data = json.loads(JSON_PATH.read_text(encoding="utf-8"))
    assert data["experiment"] == "juggler_eoo_cell_mechanism"
    assert data["engine_control_layer_modified"] is False
    assert data["decision"]["classification"] == CLASS_GREEN
    assert data["lean"]["sorry_free"] is True
    for name in LEAN_THEOREMS:
        assert data["lean"][name] is True
    assert data["scan"]["eoo_cells"]["contracting_starts"] == [2, 12, 14]


def test_floor_power_unchanged():
    assert floor_power(2) == 1
    assert floor_power(12) == 3
    assert floor_power(3) == 5
    assert floor_power(5) == 11
    assert floor_power(11) == 36
