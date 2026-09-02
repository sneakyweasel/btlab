"""Realization-set geometry. Not an engine-control test."""

from __future__ import annotations

import json

from research.juggler_sequence.compensated_contraction import follows_itinerary, image_after
from research.juggler_sequence.realization_geometry import (
    CLASS_COMPLEX,
    FIRST_HOLES,
    FIRST_UNARY,
    JSON_PATH,
    LEAN_THEOREMS,
    amplification_laws,
    atlas_available,
    child_sets,
    classify_missing_child,
    collect_realizing,
    corridor_recurrence,
    even_tower,
    interval_label,
    lean_api_present,
    prefix_row,
    reproduce_atlas,
)


def test_even_tower_and_follows():
    assert even_tower(1) == 2
    assert even_tower(2) == 4
    assert even_tower(3) == 16
    assert even_tower(4) == 256
    assert even_tower(5) == 65536
    assert even_tower(6) == 4294967296
    for r in range(1, 6):
        assert follows_itinerary(even_tower(r), "E" * r)
        assert image_after(even_tower(r), "E" * r) == 1


def test_child_split_is_landing_parity():
    realizing = collect_realizing(n_max=200, k_max=6)
    starts = realizing["OOE"]
    assert starts[0] == 5
    child_o, child_e, uncovered = child_sets("OOE", starts)
    assert uncovered == []
    assert 5 in child_e
    assert image_after(5, "OOE") % 2 == 0
    for n in child_o:
        assert image_after(n, "OOE") % 2 == 1
    for n in child_e:
        assert image_after(n, "OOE") % 2 == 0


def test_nested_realizing_sets():
    realizing = collect_realizing(n_max=80, k_max=5)
    for word, starts in realizing.items():
        if len(word) == 1:
            continue
        parent = realizing[word[:-1]]
        assert set(starts) <= set(parent)
        row = prefix_row(word[:-1], parent, n_max=80)
        assert row["uncovered"] == 0


def test_square_amplification_fails_after_odd_letters():
    realizing = collect_realizing(n_max=4000, k_max=6)
    laws = amplification_laws(realizing)
    assert laws["tower_identity_in_window"] is True
    cex = laws["square_law_counterexample"]
    assert cex is not None
    assert cex["m_wE"] < cex["m_w"] ** 2
    odd = laws["odd_landing_square_counterexample"]
    assert odd is not None
    assert odd["landing"] % 2 == 1
    assert odd["m_wE"] < odd["m_w"] ** 2
    assert laws["even_landing_identity_fail"] is None
    even_hit = laws["square_law_counterexample"]
    assert even_hit["m_wE"] == even_hit["m_w"]


def test_first_holes_need_certificates():
    tower = classify_missing_child("EEEEE", "E")
    assert tower["status"] == "SCALE_LIMITED"
    assert tower["certificate_type"] == "EVEN_TOWER"
    assert tower["min_root"] == even_tower(6)
    mixed = classify_missing_child("EEEEO", "E")
    assert mixed["status"] == "SEARCH_UNOBSERVED"
    assert mixed["child"] in FIRST_HOLES
    assert FIRST_UNARY == ("EEEEE", "EEEEO", "EEEOE")


def test_prepend_E_closed_prepend_O_leaks():
    realizing = collect_realizing(n_max=400, k_max=6)
    rec = corridor_recurrence(realizing, n_max=400, k_max=6)
    assert rec["empty_prepend_E_exact"] is True
    assert rec["even_tower_prepend_exact"] is True
    assert rec["prepend_E_mismatches"] == 0
    assert rec["empty_prepend_O_exact"] is False
    assert rec["empty_prepend_O_leak"] > 0
    assert rec["prepend_O_mismatches"] > 0


def test_interval_label_and_odd_fragmentation():
    realizing = collect_realizing(n_max=80, k_max=3)
    odd = prefix_row("O", realizing["O"], n_max=80)
    assert odd["interval_class"] == "FRAGMENTED"
    assert interval_label({"size": 4, "n_components": 1, "largest_frac": 1.0}) == "SINGLE_INTERVAL"


def test_lean_api_no_halt_or_forbidden_engines():
    lean = lean_api_present()
    assert lean["sorry_free"] is True
    for name in LEAN_THEOREMS:
        assert lean[name] is True
    assert lean["no_global_termination_theorem"] is True
    assert lean["no_forbidden_engines"] is True


def test_atlas_reproduction_if_present():
    if not atlas_available():
        return
    atlas = reproduce_atlas()
    assert atlas["available"] is True
    for row in atlas["tower"]:
        if row["r"] <= 5:
            assert row["min_realizer"] == row["tower"]
            assert row["status"] == "FOUND"
        if row["r"] == 6:
            assert row["status"] == "NOT_FOUND_WITHIN_BOUND"
    assert [row["word"] for row in atlas["first_unary"]] == list(FIRST_UNARY)
    assert all(row["class"] in {"UNARY_O", "UNARY_E"} for row in atlas["first_unary"])
    assert all(row["status"] == "NOT_FOUND_WITHIN_BOUND" for row in atlas["first_holes"])
    ee = atlas["ee_prefix_length_12"]
    assert ee["count"] == 37
    assert ee["unary"] == 37


def test_window_landing_parity_and_no_uncovered():
    from research.juggler_sequence.realization_geometry import window_census

    realizing = collect_realizing(n_max=4000, k_max=8)
    census = window_census(realizing, n_max=4000, k_max=8)
    assert census["uncovered_total"] == 0
    assert census["unary_total"] > 0
    assert census["unary_monochrome"] == census["unary_total"]
    assert amplification_laws(realizing)["square_law_counterexample"] is not None


def test_selected_roots_small_window():
    from research.juggler_sequence.realization_geometry import selected_root_scan

    rec = selected_root_scan(n_max=300, words=("E", "EE", "EEEEEE"))
    assert rec["words"]["E"]["min"] == 2
    assert rec["words"]["EE"]["min"] == 4
    assert rec["words"]["EEEEEE"]["size"] == 0


def test_committed_artifacts_complex():
    if not JSON_PATH.is_file():
        return
    payload = json.loads(JSON_PATH.read_text(encoding="utf-8"))
    assert payload["engine_control_layer_modified"] is False
    assert payload["anti_overclaim"]["reopen_pe_factors"] is False
    assert payload["anti_overclaim"]["reopen_residual_quotient"] is False
    assert payload["anti_overclaim"]["automaton"] is False
    assert payload["decision"]["classification"] == CLASS_COMPLEX
    scan = payload["scan"]
    assert scan["diagnostic"]["uncovered_total"] == 0
    assert scan["corridor"]["prepend_E_mismatches"] == 0
    assert scan["corridor"]["empty_prepend_O_leak"] > 0
    for row in scan["missing_children"]:
        assert row["status"] == "SCALE_LIMITED"
        assert row["child"] in FIRST_HOLES
