"""Later ReturnBelow after even-y overshoot. Not a halt or K3 test."""

from __future__ import annotations

import json

from research.juggler_sequence.lean_paths import EVEN_COUNT_THREE, JUGGLER_PAPER_BARREL
from research.juggler_sequence.odd_odd_frontier import first_even_residual
from research.juggler_sequence.overshoot_return import (
    CLASS_SCATTER,
    JSON_PATH,
    LEAN_THEOREMS,
    N_PIN,
    classify,
    first_return_below,
    lean_api_present,
    overshoot_return_census,
    overshoot_row,
    render_markdown,
    suffix_after_oa_ee,
)
from research.juggler_sequence.power_itineraries import ANTI_OVERCLAIM
from research.juggler_sequence.progress_coverage import is_odd_odd


def test_easy_even_y_replays_paper_b_words():
    five = overshoot_row(5)
    assert five is not None
    assert five["a"] == 2
    assert five["y_even"] is True
    assert five["first_exc_lt"] is True
    assert five["first_kind"] == "CAPTURE"
    assert five["return"]["word"] == "OOEE"
    twenty_five = overshoot_row(25)
    assert twenty_five is not None
    assert twenty_five["a"] == 3
    assert twenty_five["y_even"] is True
    assert twenty_five["first_exc_lt"] is True
    assert twenty_five["return"]["word"] == "OOOEE"


def test_thirty_seven_is_odd_y_not_the_hard_class():
    assert is_odd_odd(37)
    fe = first_even_residual(37)
    assert fe is not None
    assert fe["a"] == 4
    assert fe["e"] % 2 == 1
    row = overshoot_row(37)
    assert row is not None
    assert row["y_even"] is False
    assert row["first_kind"] == "STAY"
    assert row["second_exc_lt"] is False
    assert row["suffix"] is None
    ret = first_return_below(37)
    assert ret == {"step": 15, "value": 8, "word": "OOOOEOOOEEOOEEE"}


def test_first_hard_even_y_is_one_hundred_fifteen():
    row = overshoot_row(115)
    assert row is not None
    assert row["a"] == 5
    assert row["y_even"] is True
    assert row["first_kind"] == "STAY"
    assert row["second_exc_lt"] is True
    assert row["suffix"] == "OEE"
    assert suffix_after_oa_ee(row["return"]["word"], 5) == "OEE"


def test_pin_window_has_no_hard_even_y():
    pin = overshoot_return_census(n_max=N_PIN)
    assert pin["overshoot_count"] == 18
    assert pin["easy_even_y_count"] == 13
    assert pin["hard_even_y_count"] == 0
    assert pin["odd_y_count"] == 5
    assert pin["easy_first_exc_all_lt"] is True
    assert pin["easy_a_values"] == [2, 3]
    assert pin["odd_y_two_excursion_stay"] == [37, 77]


def test_lean_overshoot_corollary_and_boundaries():
    lean = lean_api_present()
    assert lean["sorry_free"] is True
    for name in LEAN_THEOREMS:
        assert lean[name] is True, name
    assert lean["paper_a_has_no_overshoot_return"] is True
    assert lean["no_return_below_universal"] is True
    assert lean["no_two_excursion_progress"] is True
    assert lean["no_global_termination_theorem"] is True
    assert lean["Progress_unchanged"] is True
    even = EVEN_COUNT_THREE.read_text(encoding="utf-8")
    paper = JUGGLER_PAPER_BARREL.read_text(encoding="utf-8")
    assert "theorem minimal_first_even_overshoots" in even
    assert "theorem cycleMin_first_even_overshoots" in even
    assert "sorry" not in even
    assert "admit" not in even
    assert "theorem minimal_first_even_overshoots" not in paper
    assert "theorem juggler_reaches_one" not in even
    assert "theorem overshoot_return_below" not in even


def test_classify_scatter_from_committed_window():
    assert JSON_PATH.is_file()
    data = json.loads(JSON_PATH.read_text(encoding="utf-8"))
    assert data["experiment"] == "juggler_overshoot_return"
    assert data["engine_control_layer_modified"] is False
    lean = lean_api_present()
    decision = classify(data["scan"]["census"], lean)
    assert decision["classification"] == CLASS_SCATTER
    assert data["decision"]["classification"] == CLASS_SCATTER
    hard = data["scan"]["census"]["hard"]
    assert hard["count"] == 317
    assert hard["first_exc_stay_count"] == 170
    assert hard["second_exc_all_lt"] is False
    assert hard["suffix_count"] == 96
    assert hard["family_by_a"] is False
    assert hard["suffixes_are_paper_b"] is False
    assert hard["return_len_min"] == 7
    assert hard["return_len_max"] == 115
    assert data["scan"]["census"]["easy_first_exc_all_lt"] is True
    assert data["anti_overclaim"]["finite_progress_for_all"] is False
    assert data["anti_overclaim"]["return_below_universal"] is False
    assert data["anti_overclaim"]["cycle_impossible"] is False
    assert data["anti_overclaim"]["density_one_claimed"] is False
    text = render_markdown(data)
    assert CLASS_SCATTER in text
    assert "return_below_universal" in text
    for key in ANTI_OVERCLAIM:
        assert key in data["anti_overclaim"]
