"""Fast checks for the (19,12) landing-cell probe."""

from __future__ import annotations

import json

from pathlib import Path

from research.juggler_sequence.flight_fan_landing import (
    CLASS_NO_LAW,
    JSON_PATH,
    _launch_class,
    _safe_cell,
)

CONJECTURE = Path("conjectures/refuted/juggler_fan_landing_two_way.json")
from research.juggler_sequence.flight_post19_tail import tail_scan
from research.juggler_sequence.flight_divergent_structure import trajectory
from research.juggler_sequence.flight_return_quantization import return_set


def test_safe_cell_small_odd() -> None:
    rec = _safe_cell(365)
    assert rec["odd"] is True
    assert rec["pos"] is not None
    assert 0.0 <= rec["pos"] < 1.0


def test_launch_class_hug_follow_is_holdout() -> None:
    assert (
        _launch_class({"kind": "dies_before_19", "first_hug_split": None}, True)
        == "hug_follow_die"
    )
    assert (
        _launch_class({"kind": "overshoot", "first_hug_split": 3}, True) == "extra_O"
    )
    assert _launch_class({"kind": "hug_minimal_19", "first_hug_split": None}, True) == (
        "r05_block"
    )


def test_tail_scan_import_smoke() -> None:
    scan = tail_scan(trajectory(37), 0, return_set(250, 0.05))
    assert "kind" in scan


def test_artifact_refutes_two_way_law() -> None:
    summary = json.loads(JSON_PATH.read_text(encoding="utf-8"))
    assert summary["classification"] == CLASS_NO_LAW
    wt = summary["window"]["tally"]
    ft = summary["flyers"]["tally"]
    assert wt["n19"] == 44
    assert wt["two_way_false"] is True
    assert wt["hug_follow_die"] == 12
    assert wt["r05_block"] == 0
    assert wt["odd_cell_mixed"] >= 1
    assert wt["cross_ooe"]["extra_O"] == {"True": 5}
    assert wt["cross_ooe"]["hug_follow_die"]["True"] == 5
    assert wt["overshoot_cells"][0]["n"] == 761
    assert wt["overshoot_cells"][0]["ooe_legal"] is True
    assert ft["hug_follow_die"] == 5
    assert ft["overshoot_cells"][0]["n"] == 1245741
    anti = summary["anti_overclaim"]
    assert anti["halt_theorem"] is False
    assert anti["landing_law_proved"] is False
    assert anti["xi_cocycle_reopened"] is False
    assert anti["n_window_raised"] is False
    conj = json.loads(CONJECTURE.read_text(encoding="utf-8"))
    assert conj["status"] == "REFUTED"
    assert conj["id"] == "juggler_fan_landing_two_way"
