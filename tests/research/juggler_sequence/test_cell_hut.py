"""Cell-hut quotient. Not an engine-control or halt test."""

from __future__ import annotations

import json
from pathlib import Path

from research.juggler_sequence.backward_geometry import pred_odd
from research.juggler_sequence.cell_hut import (
    CLASS_COMPLEX,
    JSON_PATH,
    VERSIONS,
    GeometryCache,
    analyze_transitions,
    anti_overclaim,
    certify_even_predecessor,
    certify_odd_predecessor,
    even_fan_row,
    hut_geometry,
    identifying_values,
    lean_api_present,
    odd_predecessor_of,
    odd_spine,
    signature_id,
    signature_tuple,
    signature_uses_identifier,
)
from research.juggler_sequence.power_itineraries import floor_power


def test_geometry_one_two_five():
    g1 = hut_geometry(1)
    assert g1["even_cell_lower"] == 2
    assert g1["even_cell_upper"] == 2
    assert g1["odd_predecessor"] == 1
    assert g1["order_type"] == "fixed_1"
    assert certify_odd_predecessor(1, 1)
    assert certify_even_predecessor(2, 1)

    g2 = hut_geometry(2)
    assert g2["odd_predecessor"] is None
    assert g2["even_cell_lower"] == 4
    assert g2["even_cell_upper"] == 8
    assert g2["even_cell_size"] == 3
    assert pred_odd(2) == []

    g5 = hut_geometry(5)
    assert g5["odd_predecessor"] == 3
    assert certify_odd_predecessor(3, 5)
    assert floor_power(3) == 5
    assert g5["order_type"] == "o_lt_m_lt_E"


def test_odd_predecessor_matches_pred_odd():
    for m in range(1, 201):
        odd = odd_predecessor_of(m)
        listed = pred_odd(m)
        if odd is None:
            assert listed == []
        else:
            assert listed == [odd]
            assert certify_odd_predecessor(odd, m)


def test_even_count_formula():
    for m in (1, 2, 3, 4, 5, 10, 11, 100, 101, 365, 4000):
        geo = hut_geometry(m)
        expected = m + 1 if m % 2 == 0 else m
        assert geo["even_cell_size"] == expected
        assert certify_even_predecessor(geo["even_cell_lower"], m)
        assert certify_even_predecessor(geo["even_cell_upper"], m)


def test_signatures_omit_identifying_coordinates():
    for m in (1, 2, 5, 9, 37, 365, 2183):
        geo = hut_geometry(m)
        banned = identifying_values(geo)
        for version in VERSIONS:
            tup = signature_tuple(geo, version)
            assert geo["m"] not in tup or geo["m"] <= 3
            assert geo["even_cell_lower"] not in tup
            assert geo["even_cell_upper"] not in tup
            if geo["odd_predecessor"] is not None and geo["odd_predecessor"] > 3:
                assert geo["odd_predecessor"] not in tup
            assert signature_uses_identifier(geo, version) is False
            assert signature_id(version, tup).startswith(version + ":")
            assert banned  # geometry still stores the exact object


def test_raw_hut_determines_m():
    for m in range(1, 80):
        geo = hut_geometry(m)
        recovered = int(geo["square_lo"] ** 0.5) if geo["square_lo"] == m * m else None
        assert geo["square_lo"] == m * m
        assert recovered == m


def test_frozen_versions_are_exactly_the_ladder():
    assert VERSIONS == (
        "v1_occupancy",
        "v2_type",
        "v3_oddpos",
        "v4_mod3",
        "vB_border",
        "vC_valuation",
    )


def test_small_window_has_merge_pairs():
    cache = GeometryCache()
    for m in range(1, 81):
        cache.get(m)
    report = analyze_transitions(range(1, 81), cache, "v1_occupancy")
    assert report["n_classes"] <= 2
    assert report["n_states"] == 80
    assert report["merge_pair"] is not None
    assert report["merge_pair"]["kind"] == "same_class_different_successor"
    assert report["merge_pair"]["x"] < report["merge_pair"]["y"]


def test_odd_spine_five_is_three_then_empty_or_fixed():
    cache = GeometryCache()
    spine = odd_spine(5, cache)
    assert spine["node_sequence"][0] == 5
    assert spine["node_sequence"][1] == 3
    assert spine["termination_status"] in {"empty_odd_cell", "fixed_point"}


def test_even_fan_two_is_the_even_cell():
    row = even_fan_row(2, "v2_type")
    assert row["fan_size"] == 3
    assert row["distinct_child_hut_classes"] >= 1
    assert row["distinct_child_hut_classes"] <= 3


def test_module_does_not_import_collatz():
    from research.juggler_sequence import cell_hut as module

    source = Path(module.__file__).read_text(encoding="utf-8")
    assert "from research.collatz" not in source
    assert "import research.collatz" not in source
    assert "collatz_predecessors" not in source


def test_lean_api():
    lean = lean_api_present()
    assert lean["sorry_free"] is True
    assert lean["even_preimage_iff"] is True
    assert lean["odd_preimage_unique"] is True
    assert lean["no_global_termination_theorem"] is True
    assert lean["no_collatz_inverse"] is True
    assert lean["no_new_lean_module"] is True


def test_anti_overclaim_walls():
    anti = anti_overclaim()
    assert anti["collatz_inverse"] is False
    assert anti["reopen_backward_geometry"] is False
    assert anti["reopen_pe_factors"] is False
    assert anti["reopen_residual_quotient"] is False
    assert anti["reopen_sum_rho"] is False
    assert anti["reopen_accelerated"] is False
    assert anti["automaton"] is False
    assert anti["new_lyapunov_scalar"] is False
    assert anti["hut_descent_is_termination"] is False
    assert anti["engine_control_layer_modified"] is False
    assert anti["scalar_hut_score"] is False


def test_committed_artifacts_if_present():
    if not JSON_PATH.is_file():
        return
    payload = json.loads(JSON_PATH.read_text(encoding="utf-8"))
    assert payload["experiment"] == "juggler_cell_hut"
    assert payload["engine_control_layer_modified"] is False
    assert payload["anti_overclaim"]["collatz_inverse"] is False
    assert payload["anti_overclaim"]["reopen_backward_geometry"] is False
    assert payload["anti_overclaim"]["hut_descent_is_termination"] is False
    assert payload["decision"]["classification"] == CLASS_COMPLEX
    assert payload["branch_status"] == "CLOSE"
    v3 = payload["scan"]["transitions"]["v3_oddpos"]
    assert v3["merge_pair"]["x"] == 2
    assert v3["merge_pair"]["y"] == 4
    for version, report in payload["scan"]["transitions"].items():
        assert report["merge_pair"] is not None
        assert report["n_classes"] < report["n_states"]
        assert report["rule"] is None
        _ = version
