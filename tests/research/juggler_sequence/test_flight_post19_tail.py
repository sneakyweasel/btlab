"""Fast checks for the post-19 tail split probe."""

from __future__ import annotations

import json

from research.juggler_sequence.flight_divergent_structure import trajectory
from research.juggler_sequence.flight_fan_concat import hug_letters
from research.juggler_sequence.flight_post19_tail import (
    CLASS_SPLIT_CONFIRMED,
    JSON_PATH,
    first_hug_split,
    tail_scan,
)
from research.juggler_sequence.flight_return_quantization import (
    LOG2_3,
    return_set,
    theta_p,
)


def test_o12_forces_near_return() -> None:
    # Dichotomy arithmetic: o = 12 implies delta <= theta_19 < 0.05.
    assert abs(theta_p(19) - (12 * LOG2_3 - 19)) < 1e-12
    assert theta_p(19) < 0.05
    assert hug_letters(19)[2] == "E"


def test_first_hug_split_at_letter_three() -> None:
    hug = hug_letters(19)
    assert first_hug_split(hug, hug) is None
    assert first_hug_split("OOO" + hug[3:], hug) == 3


def test_tail_scan_on_small_orbit() -> None:
    xs = trajectory(37)
    scan = tail_scan(xs, 0, return_set(250, 0.05))
    assert scan["next_len"] >= 0
    assert scan["kind"] in {
        "dies_immediately",
        "dies_before_19",
        "overshoot",
        "hug_minimal_19",
    }


def test_artifact_certifies_split() -> None:
    summary = json.loads(JSON_PATH.read_text(encoding="utf-8"))
    assert summary["classification"] == CLASS_SPLIT_CONFIRMED
    wt = summary["window"]["tally"]
    ft = summary["flyers"]["tally"]
    assert wt["kinds"]["dies_immediately"] == 27
    assert wt["kinds"]["dies_before_19"] == 16
    assert wt["kinds"]["overshoot"] == 1
    assert wt["hug_minimal_19"] == 0
    assert wt["lemma_holds_on_long"] is True
    assert wt["long_witnesses"][0]["n"] == 761
    assert wt["long_witnesses"][0]["o19"] == 14
    assert wt["long_witnesses"][0]["delta19"] > 0.05
    assert wt["long_witnesses"][0]["first_hug_split"] == 3
    assert wt["first_hug_split_ge3"]["None"] == 5
    assert wt["first_hug_split_ge3"]["3"] == 5
    assert ft["kinds"]["overshoot"] == 1
    assert ft["hug_minimal_19"] == 0
    assert ft["long_witnesses"][0]["n"] == 1245741
    assert ft["long_witnesses"][0]["o19"] == 15
    assert ft["long_witnesses"][0]["delta19"] > 0.05
    assert ft["long_witnesses"][0]["first_hug_split"] == 3
    assert ft["first_hug_split_ge3"]["None"] == 2
    anti = summary["anti_overclaim"]
    assert anti["halt_theorem"] is False
    assert anti["overshoot_forced"] is False
    assert anti["n_window_raised"] is False
    assert anti["glue_reopened"] is False
