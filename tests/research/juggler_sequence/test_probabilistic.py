"""Probabilistic Juggler diagnostics. Not a halt test."""

from __future__ import annotations

import json
import math
from pathlib import Path

from research.juggler_sequence.power_itineraries import floor_power
from research.juggler_sequence.probabilistic import (
    ANTI,
    CLASS_STAT_ONLY,
    CLOSED_IMPORT_TOKENS,
    DATA_DIR,
    DOSSIER_PATH,
    JSON_PATH,
    LOG_1_2,
    LOG_3_2,
    MIN_L,
    exact_increment,
    increment_identity_holds,
    loglog,
    replay_record,
    walk_return,
)


def test_delta_l_does_not_define_the_map():
    for n in (16, 17, 36, 37, 193):
        rec = exact_increment(n)
        assert rec["y"] == floor_power(n)
        assert increment_identity_holds(n)


def test_branch_terms_match_the_log_log_heuristic():
    assert abs(LOG_3_2 - math.log(1.5)) < 1e-15
    assert abs(LOG_1_2 - math.log(0.5)) < 1e-15
    odd = exact_increment(25)
    even = exact_increment(36)
    assert odd["branch"] == "O"
    assert even["branch"] == "E"
    assert abs(odd["delta_loglog"] - LOG_3_2) < 0.05
    assert abs(even["delta_loglog"] - LOG_1_2) < 0.05


def test_even_starts_return_in_one_step():
    for n in range(2, 80, 2):
        rec = walk_return(n, promote=False)
        assert rec["returned"]
        assert rec["H"] == 1
        assert rec["word"] == "E"


def test_known_records_replay_on_cpu():
    three = replay_record(3, expected_tau=5, expected_word="OOOEE")
    assert three["tau_match"] and three["word_match"]
    rec193 = replay_record(193, expected_tau=70)
    assert rec193["returned"]
    assert rec193["tau"] == 70
    rec3889 = replay_record(3889, expected_tau=77)
    assert rec3889["tau"] == 77
    rec2183 = walk_return(2183)
    assert rec2183["returned"]
    assert rec2183["peak_bits"] == 19694


def test_loglog_is_undefined_as_a_map():
    assert loglog(16) > 0
    rec = exact_increment(3)
    assert rec["delta_loglog"] is None or 3 < MIN_L


def test_anti_overclaim_and_closed_imports():
    assert ANTI["global_termination"] is False
    assert ANTI["negative_drift_implies_halt"] is False
    assert ANTI["automaton"] is False
    assert ANTI["cuda_defines_map"] is False
    text = Path(__file__).resolve().parents[3] / "src" / "research" / "juggler_sequence" / "probabilistic.py"
    source = text.read_text(encoding="utf-8")
    for token in CLOSED_IMPORT_TOKENS:
        assert f"juggler_sequence.{token}" not in source


def test_records_and_data_products():
    assert JSON_PATH.is_file()
    data = json.loads(JSON_PATH.read_text(encoding="utf-8"))
    assert data["cuda_used"] is False
    assert data["anti_overclaim"]["global_termination"] is False
    assert data["decision"]["classification"] == CLASS_STAT_ONLY
    assert data["decision"]["branch"] in ("PARK", "CLOSE")
    assert data["records"][0]["n"] == 3
    assert data["walk_4000"]["returned"] == data["walk_4000"]["starts"]
    assert data["walk_4000"]["max_H"] == 77
    assert data["walk_4000"]["max_H_n"] == 3889
    assert data["one_step"]["weighted_mean_delta"] < 0
    assert data["log_uniform"]["weighted_mean_delta"] < 0
    text = DOSSIER_PATH.read_text(encoding="utf-8")
    assert "## Branch budget" in text
    assert "## Decision" in text
    assert "## Publication assessment" in text
    decision = text.split("## Decision", 1)[1]
    assert "PARK" in decision or "CLOSE" in decision
    assert (DATA_DIR / "manifest.json").is_file()
    for name in (
        "scale_drift.csv",
        "transition_statistics.csv",
        "run_statistics.csv",
        "excursion_distribution.csv",
        "large_deviation.csv",
        "model_comparison.csv",
        "exceptional_paths.jsonl",
        "record_excursions.csv",
    ):
        assert (DATA_DIR / name).is_file()
