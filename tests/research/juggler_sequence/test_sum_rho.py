"""Naive pathDefectSum / word-statistics probe. Not a halt test."""

from __future__ import annotations

import json

from research.juggler_sequence.global_defect import global_defect, local_defect
from research.juggler_sequence.power_itineraries import floor_power
from research.juggler_sequence.sum_rho import (
    CLASS_COMPLEX,
    DATA_DIR,
    JSON_PATH,
    classify,
    identity_checks,
    lean_api_present,
    path_pows_and_next_sq,
    same_word_variation,
    telescope_search,
    walk,
)


def test_rho_is_existing_local_defect_sum():
    rec = walk(13, 4)
    expected = 0
    current = 13
    for rho in rec["rhos"]:
        assert rho == local_defect(current)
        expected += rho
        current = floor_power(current)
    assert rec["rho_sum"] == expected


def test_path_identity_and_delta_ge_rho():
    for n in (9, 10, 13, 37, 365):
        rec = walk(n, 6)
        checks = identity_checks(rec)
        assert checks["path_identity"] is True
        assert checks["compose_additive"] is True
        assert checks["delta_ge_rho"] is True
        pows, nxt = path_pows_and_next_sq(rec["states"])
        assert pows == nxt + rec["rho_sum"]
        assert global_defect(n, rec["word"]) >= rec["rho_sum"]


def test_length_one_delta_equals_rho():
    assert walk(10, 1)["rho_sum"] == local_defect(10) == global_defect(10, "E")
    assert walk(15, 1)["rho_sum"] == local_defect(15) == global_defect(15, "O")


def test_no_new_state_potential():
    tel = telescope_search(37, 6)
    assert tel["known_path_identity"] is True
    assert tel["all_zero"]["id"] is False
    assert tel["all_zero"]["sq"] is False
    assert tel["all_zero"]["cube"] is False
    assert tel["all_zero"]["local_defect"] is False


def test_ooe_rho_varies_with_n():
    row = same_word_variation("OOE", n_max=200)
    assert row["n_realizers"] > 2
    assert row["varies"] is True
    assert row["min"]["rho_sum"] != row["max"]["rho_sum"]


def test_lean_keeps_existing_rho():
    lean = lean_api_present()
    assert lean["sorry_free"] is True
    assert lean["pathDefectSum"] is True
    assert lean["pathPows_eq_next_add_defects"] is True
    assert lean["globalDefect"] is True
    assert lean["no_new_rho"] is True
    assert lean["no_ResidualState"] is True
    assert lean["no_global_termination_theorem"] is True


def test_floor_power_unchanged():
    assert floor_power(1) == 1
    assert floor_power(9) == 27
    assert floor_power(37) == 225
    assert floor_power(365) == 6973


def test_committed_artifacts_complex():
    assert JSON_PATH.is_file()
    data = json.loads(JSON_PATH.read_text(encoding="utf-8"))
    assert data["experiment"] == "juggler_sum_rho"
    assert data["anti_overclaim"]["new_rho"] is False
    assert data["anti_overclaim"]["pe_factor_reopened"] is False
    assert data["anti_overclaim"]["residual_quotient_reopened"] is False
    decision = classify(data["scan"], lean_api_present())
    assert decision["classification"] == CLASS_COMPLEX
    summary = json.loads((DATA_DIR / "summary.json").read_text(encoding="utf-8"))
    assert summary["decision"]["classification"] == CLASS_COMPLEX
