"""Backward predecessor geometry. Not an engine-control or halt test."""

from __future__ import annotations

import json
from pathlib import Path

from research.juggler_sequence.backward_geometry import (
    CLASS_COMPLEX,
    JSON_PATH,
    classify_predecessor,
    compose_report,
    even_pred_range,
    lean_api_present,
    pred,
    pred_even,
    pred_odd,
    pred_summary,
)
from research.juggler_sequence.power_itineraries import floor_power


def test_pred_one_is_fixed_point_and_two():
    assert pred(1) == [2, 1]
    assert pred_even(1) == [2]
    assert pred_odd(1) == [1]
    assert floor_power(1) == 1
    assert floor_power(2) == 1


def test_pred_two_is_even_cell_only():
    assert pred_even(2) == [4, 6, 8]
    assert pred_odd(2) == []
    assert pred(2) == [4, 6, 8]
    assert all(floor_power(n) == 2 for n in pred(2))


def test_pred_five_has_odd_three():
    assert 3 in pred_odd(5)
    assert floor_power(3) == 5
    assert classify_predecessor(3, 5) == "unique_odd"


def test_even_count_formula():
    for m in (1, 2, 3, 4, 5, 10, 11, 100, 101):
        bounds = even_pred_range(m)
        assert bounds is not None
        expected = m + 1 if m % 2 == 0 else m
        assert bounds[2] == expected
        assert pred_summary(m)["e_formula_ok"] is True


def test_every_listed_pred_maps_forward():
    for m in range(1, 80):
        for n in pred(m):
            assert floor_power(n) == m
            assert n >= 1


def test_even_preds_ascend_and_odd_descend():
    for m in range(1, 200):
        for n in pred_even(m):
            assert n > m
        for n in pred_odd(m):
            if m == 1:
                assert n == 1
            else:
                assert n < m


def test_compose_e_matches_even_cell():
    rec = compose_report(2, "E")
    assert rec["empty"] is False
    assert rec["min"] == 4
    assert rec["max"] == 8
    assert rec["exact_inside_parity"] is True


def test_compose_o_from_five_is_three():
    rec = compose_report(5, "O")
    assert rec["sample"] == [3]
    assert rec["kind"] == "singleton"


def test_module_does_not_import_collatz():
    from research.juggler_sequence import backward_geometry as module

    source = Path(module.__file__).read_text(encoding="utf-8")
    assert "research.collatz" not in source
    assert "from research.collatz" not in source
    assert "import research.collatz" not in source


def test_lean_api():
    lean = lean_api_present()
    assert lean["sorry_free"] is True
    assert lean["even_preimage_iff"] is True
    assert lean["odd_preimage_unique"] is True
    assert lean["no_global_termination_theorem"] is True


def test_committed_artifacts_if_present():
    if not JSON_PATH.is_file():
        return
    payload = json.loads(JSON_PATH.read_text(encoding="utf-8"))
    assert payload["engine_control_layer_modified"] is False
    assert payload["anti_overclaim"]["collatz_inverse"] is False
    assert payload["anti_overclaim"]["reopen_preimage_cylinders"] is False
    assert payload["anti_overclaim"]["new_lyapunov_scalar"] is False
    if payload["decision"]["classification"] == CLASS_COMPLEX:
        assert payload["scan"]["questions"]["Q1_pred_e_formula"]["holds"] is True
        assert payload["scan"]["questions"]["Q2_pred_o_unique"]["holds"] is True
        assert payload["scan"]["questions"]["Q5_composition_is_cell_nest"]["holds"] is True
        assert payload["scan"]["questions"]["Q6_hard_preds_ordinary"]["holds"] is True
        assert payload["scan"]["composition"]["new_scale_law"] is False
