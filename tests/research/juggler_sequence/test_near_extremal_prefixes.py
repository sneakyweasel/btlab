"""Near-extremal non-contracting prefixes. Not an engine-control test."""

from __future__ import annotations

import json

from research.juggler_sequence.near_extremal_prefixes import (
    CLASS_STRUCTURE,
    DOC_PATH,
    JSON_PATH,
    combinatorial_census,
    exponent_gap,
    first_contracting_prefix,
    lean_api_present,
    prefix_noncontracting,
    prefix_row,
    probe_payload,
    render_markdown,
    scan_realized,
)
from research.juggler_sequence.power_itineraries import ANTI_OVERCLAIM, word_of, itinerary


def test_exponent_gap_and_prefix_nc():
    assert exponent_gap(1, 0) == 1
    assert exponent_gap(1, 1) == -1
    assert exponent_gap(2, 1) == 1
    assert exponent_gap(3, 2) == -1
    assert prefix_noncontracting("E") is False
    assert prefix_noncontracting("OE") is False
    assert prefix_noncontracting("OOE") is True
    assert prefix_noncontracting("OOOE") is True
    assert prefix_noncontracting("EOO") is False
    assert first_contracting_prefix("EOO") == 1
    assert first_contracting_prefix("OE") == 2
    assert first_contracting_prefix("OOE") is None


def test_three_realizes_oooe_not_ooe():
    word = word_of(itinerary(3, 4))
    assert word.startswith("OOOE")
    rec = prefix_row(3, "OOOE")
    assert rec["prefix_nc"] is True
    assert rec["monochrome"] is False
    assert rec["actual_contraction"] is False
    assert rec["exponent_gap"] < 0


def test_combinatorial_language_shape():
    comb = combinatorial_census(8)
    assert comb["starts_with_o"] is True
    assert comb["len_ge_2_starts_with_oo"] is True
    assert comb["ooe_prefix_nc"] is True
    assert comb["oke_count"] == 6
    assert comb["other_mixed_count"] > 0
    from research.juggler_sequence.near_extremal_prefixes import prefix_nc_words

    assert "OOEO" in prefix_nc_words(6)


def test_realized_scan_records_horizon_and_skips_eoo():
    scan = scan_realized(80, 6)
    assert scan["mixed_prefix_count"] > 0
    assert scan["defect_contract_count"] == 0
    words = {row["word"] for row in scan["longest_mixed"]}
    assert all(not word.startswith("E") for word in words)
    assert first_contracting_prefix("EOO") == 1


def test_probe_and_committed_artifacts():
    payload = probe_payload(n_max=80, k_real=6, k_comb=8)
    assert payload["engine_control_layer_modified"] is False
    assert payload["decision"]["classification"] == CLASS_STRUCTURE
    assert payload["lean"]["power_bound_compensated_contracts"] is True
    assert payload["lean"]["two_pow_succ_le_three_pow_iff"] is True
    assert payload["lean"]["new_defect_structure_absent"] is True
    text = render_markdown(payload)
    assert CLASS_STRUCTURE in text
    assert "EOO" in text
    assert all(v is False for v in ANTI_OVERCLAIM.values())
    lean = lean_api_present()
    assert lean["sorry_free"] is True
    assert JSON_PATH.is_file()
    data = json.loads(JSON_PATH.read_text(encoding="utf-8"))
    assert data["decision"]["classification"] == CLASS_STRUCTURE
    assert data["engine_control_layer_modified"] is False
    md = DOC_PATH.read_text(encoding="utf-8")
    assert "not a termination theorem" in md
    assert "OOOE" in md
