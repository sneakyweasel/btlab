"""Extremal control versus exact Juggler. Not a halt test."""

from __future__ import annotations

import json
import math
from pathlib import Path

from research.juggler_sequence.extremal_control import (
    ANTI,
    CLASS_FRONTIER,
    CLOSED_IMPORT_TOKENS,
    DATA_DIR,
    DOSSIER_PATH,
    JSON_PATH,
    LOG_3_2,
    analyze_trajectory,
    bang_bang_word,
    corridor_holds,
    dp_matches_closed_form,
    first_return_odd_count,
    follows_itinerary,
    is_ideal_first_return,
    ld_balanced_word,
    word_operations,
)
from research.juggler_sequence.power_itineraries import floor_power


def test_landing_corridor_is_integer():
    assert first_return_odd_count(1) == 0
    assert first_return_odd_count(2) == 1
    assert first_return_odd_count(3) is None
    assert first_return_odd_count(4) == 2
    assert first_return_odd_count(5) == 3
    assert first_return_odd_count(6) is None
    assert bang_bang_word(5) == "OOOEE"
    assert bang_bang_word(4) == "OOEE"
    assert bang_bang_word(2) == "OE"
    assert corridor_holds(3, 5)
    assert not corridor_holds(2, 5)


def test_dp_reproduces_bang_bang():
    rows = dp_matches_closed_form(20)
    assert all(row["match"] for row in rows)
    assert is_ideal_first_return("OOOEE")
    assert is_ideal_first_return("OOEOE")
    assert not is_ideal_first_return("OOOOE")


def test_ld_optimizer_is_not_the_control_optimizer():
    for k in (2, 4, 5, 7, 8, 10):
        ld = ld_balanced_word(k)
        assert not is_ideal_first_return(ld)
        assert ld != bang_bang_word(k)


def test_canonical_realizers():
    three = analyze_trajectory(3)
    assert three["returned"]
    assert three["word"] == "OOOEE"
    assert three["is_bang_bang"]
    assert three["peak_gap"] < 0.04
    five = analyze_trajectory(5)
    assert five["word"] == "OOEE"
    assert five["is_bang_bang"]
    seven = analyze_trajectory(7)
    assert seven["word"] == "OE"
    assert seven["is_bang_bang"]
    nine = analyze_trajectory(9)
    assert nine["word"] == "OOEOE"
    assert nine["is_ideal_first_return_word"]
    assert not nine["is_bang_bang"]
    assert follows_itinerary(271, "OOOOEEE")
    assert analyze_trajectory(271)["is_bang_bang"]


def test_word_operation_on_oooee_hits_n9():
    ops = word_operations("OOOEE")
    later = next(op for op in ops if op["mutant"] == "OOEOE")
    assert later["mutant_is_ideal_first_return"]
    assert later["ideal_peak_delta"] == round(-LOG_3_2, 9)
    assert analyze_trajectory(9)["word"] == "OOEOE"


def test_hard_records_are_not_bang_bang():
    rec = analyze_trajectory(3889)
    assert rec["tau"] == 77
    assert rec["hamming_to_bang_bang"] == 30
    assert rec["peak_gap"] > 10
    rec193 = analyze_trajectory(193)
    assert rec193["tau"] == 70
    assert rec193["hamming_to_bang_bang"] > 0


def test_delta_l_does_not_define_the_map():
    for n in (3, 16, 36, 193):
        y = floor_power(n)
        assert y >= 1
        if n >= 3 and y >= 3:
            rec = analyze_trajectory(n)
            assert rec["validation_status"] in {"RETURNED", "BIT_CAP", "HORIZON_EXCEEDED"}


def test_anti_overclaim_and_closed_imports():
    assert ANTI["global_termination"] is False
    assert ANTI["finite_gap_implies_halt"] is False
    assert ANTI["ld_optimizer_is_control_optimizer"] is False
    assert ANTI["reopen_statistical_fitting"] is False
    source = Path(
        __file__
    ).resolve().parents[3] / "src" / "research" / "juggler_sequence" / "extremal_control.py"
    text = source.read_text(encoding="utf-8")
    for token in CLOSED_IMPORT_TOKENS:
        assert f"juggler_sequence.{token}" not in text


def test_records_and_data_products():
    assert JSON_PATH.is_file()
    data = json.loads(JSON_PATH.read_text(encoding="utf-8"))
    assert data["cuda_used"] is False
    assert data["anti_overclaim"]["global_termination"] is False
    assert data["dp_matches_closed_form"] is True
    assert data["decision"]["classification"] == CLASS_FRONTIER
    assert data["decision"]["branch"] == "PARK"
    assert data["bang_bang_realizers"]["5"]["n"] == 3
    assert data["bang_bang_realizers"]["2"]["n"] == 7
    assert "15" not in data["bang_bang_realizers"]
    hard = {row["n"]: row for row in data["hard_paths"]}
    assert hard[3]["is_bang_bang"] is True
    assert hard[3889]["hamming_to_bang_bang"] == 30
    text = DOSSIER_PATH.read_text(encoding="utf-8")
    assert "## Branch budget" in text
    assert "## Decision" in text
    assert "## Publication assessment" in text
    decision = text.split("## Decision", 1)[1]
    assert "PARK" in decision
    assert (DATA_DIR / "manifest.json").is_file()
    for name in (
        "ideal_frontier.csv",
        "actual_frontier.csv",
        "control_gap.csv",
        "near_optimal_paths.jsonl",
        "o_run_records.csv",
        "model_comparison.csv",
    ):
        assert (DATA_DIR / name).is_file()
    assert math.log(1.5) == LOG_3_2
