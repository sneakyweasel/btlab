"""First-even freeze and floor cells. Not an engine-control test."""

from __future__ import annotations

from research.juggler_sequence.lean_paths import juggler_text

from math import isqrt

from research.juggler_sequence.compensated_contraction import follows_itinerary, image_after
from research.juggler_sequence.floor_preimages import (
    CLASS_FREEZE,
    LEAN_THEOREMS,
    cell_regime,
    classify,
    eeo_oooo_witnesses,
    even_preimage,
    even_preimage_width,
    first_even_image,
    lean_api_present,
    odd_preimage_integers,
    render_markdown,
    run_probe,
    scan_first_even_cells,
    scan_first_even_freeze,
    scan_odd_preimage_widths,
)
from research.juggler_sequence.power_itineraries import ANTI_OVERCLAIM, LEAN_PATH, floor_power


def test_even_and_odd_primitive_cells():
    assert even_preimage(1) == (1, 4)
    assert even_preimage(3) == (9, 16)
    assert even_preimage_width(1) == 3
    assert even_preimage_width(100) == 201
    assert odd_preimage_integers(0) in ([], [0])
    assert odd_preimage_integers(1) == [1]
    widths = scan_odd_preimage_widths(m_max=80)
    assert widths["multi"] == 0
    assert widths["singleton"] >= 1


def test_first_even_freeze_and_eoo_threshold():
    freeze = scan_first_even_freeze(q_max=20)
    assert freeze["failures"] == []
    for n in (2, 10, 12, 14):
        assert follows_itinerary(n, "EOO")
        assert image_after(n, "EOO") == first_even_image(n, "OO")
        q = isqrt(n)
        assert (image_after(n, "EOO") < n) == (first_even_image(n, "OO") < n)
        assert cell_regime(q, image_after(q, "OO")) in {"mixed", "all_expand", "all_contract"}
    assert image_after(2, "EOO") == 1
    assert image_after(10, "EOO") == 11
    assert image_after(12, "EOO") == 11


def test_eeoooo_entire_cell():
    rows = {row["n"]: row for row in eeo_oooo_witnesses()}
    for n in (4, 6, 8):
        assert rows[n]["follows"] is True
        assert rows[n]["image"] == 1
        assert rows[n]["frozen"] == 1
        assert rows[n]["regime"] == "all_contract"
        assert n > 1
    assert isqrt(4) == isqrt(6) == isqrt(8) == 2
    assert cell_regime(2, image_after(2, "EOOOO")) == "all_contract"


def test_positive_drift_cells_are_finite_and_small():
    scan = scan_first_even_cells(q_max=40, k_max=6)
    eoo = next(rec for rec in scan["words"] if rec["word"] == "EOO")
    assert eoo["contracting_starts"] == [2, 12, 14]
    eeo = next(rec for rec in scan["words"] if rec["word"] == "EEOOOO")
    assert eeo["contracting_starts"] == [4, 6, 8]
    for rec in scan["interesting"]:
        qs = {note["q"] for note in rec["non_expanding_cells"]}
        assert qs <= {1, 2, 3}


def test_examples_and_lean_api():
    lean = lean_api_present()
    assert lean["sorry_free"] is True
    for name in LEAN_THEOREMS:
        assert lean[name] is True
    assert lean["certificate_present"] is True
    assert lean["no_cell_tree"] is True
    text = juggler_text()
    assert "PowerHeight" not in text
    assert "theorem mixed_word_power_lt" not in text
    assert "sorry" not in text
    assert "admit" not in text


def test_classify_freeze_on_small_probe():
    scan = run_probe(q_max=20, k_max=6, m_max=40)
    lean = lean_api_present()
    decision = classify(scan, lean)
    assert decision["classification"] == CLASS_FREEZE
    payload = {
        "decision": decision,
        "scan": scan,
        "lean": lean,
        "engine_control_layer_modified": False,
        "anti_overclaim": dict(ANTI_OVERCLAIM),
    }
    text = render_markdown(payload)
    assert CLASS_FREEZE in text
    assert "global_termination" in text
    assert all(v is False for v in ANTI_OVERCLAIM.values())


def test_committed_artifacts_schema():
    import json

    from research.juggler_sequence.floor_preimages import JSON_PATH

    assert JSON_PATH.is_file()
    data = json.loads(JSON_PATH.read_text(encoding="utf-8"))
    assert data["experiment"] == "juggler_floor_cells"
    assert data["engine_control_layer_modified"] is False
    assert data["decision"]["classification"] == CLASS_FREEZE
    assert data["lean"]["sorry_free"] is True
    for name in LEAN_THEOREMS:
        assert data["lean"][name] is True
    assert data["scan"]["odd_cell_widths"]["multi"] == 0


def test_floor_power_unchanged():
    assert floor_power(2) == 1
    assert floor_power(4) == 2
    assert floor_power(8) == 2
    assert floor_power(12) == 3
