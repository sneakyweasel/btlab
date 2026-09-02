"""Predecessor cylinders. Not a termination test."""

from __future__ import annotations

from research.juggler_sequence.expansion_slack import walk_pe_run
from research.juggler_sequence.global_defect import follows_itinerary, image_after
from research.juggler_sequence.landing_parity import theta
from research.juggler_sequence.lean_paths import juggler_text
from research.juggler_sequence.power_itineraries import floor_power
from research.juggler_sequence.preimage_cylinders import (
    CHAIN_365,
    LEAN_THEOREMS,
    OOE_SPLIT,
    cylinder_census,
    lean_api_present,
    next_landing,
    next_square_gap,
    word_cylinder,
)
from research.juggler_sequence.progress_coverage import is_odd_odd
from research.juggler_sequence.two_block_residual import sequel_of


def test_word_cylinder_matches_follows_and_image():
    even = OOE_SPLIT["even"]
    odd = OOE_SPLIT["odd"]
    assert word_cylinder(even["x"], "OOE", even["y"])
    assert word_cylinder(odd["x"], "OOE", odd["y"])
    assert follows_itinerary(even["x"], "OOE")
    assert image_after(odd["x"], "OOE") == odd["y"]
    src = even["y"] ** 3
    t = next_landing(even["y"])
    assert t * t <= src < (t + 1) * (t + 1)
    assert next_square_gap(even["y"]) == src - t * t


def test_ooe_cylinder_splits_next_parity_at_same_residue():
    even = OOE_SPLIT["even"]
    odd = OOE_SPLIT["odd"]
    assert even["y"] % 8 == odd["y"] % 8 == 1
    assert next_landing(even["y"]) % 2 == 0
    assert next_landing(odd["y"]) % 2 == 1
    assert abs(theta(even["y"]) - theta(odd["y"])) < 0.01
    assert not is_odd_odd(even["y"])
    assert is_odd_odd(odd["y"])


def test_365_and_4447_are_same_word_same_residue_opposite_parity():
    xs = []
    x = CHAIN_365["xs"][0]
    for _ in range(3):
        x = floor_power(floor_power(floor_power(x)))
        xs.append(x)
    assert tuple(xs) == CHAIN_365["xs"][1:]
    assert word_cylinder(365, "OOE", 763)
    assert word_cylinder(4447, "OOE", 12707)
    assert 763 % 8 == 12707 % 8 == 3
    assert next_landing(763) % 2 == 1
    assert next_landing(12707) % 2 == 0
    seq = sequel_of(4447)
    assert seq is not None
    assert seq["y"] == CHAIN_365["exit_y"]
    assert not seq["persistent"]


def test_sampled_pe_words_do_not_force_next_parity():
    report = cylinder_census(n_max=400)
    assert report["overshoots"] >= 40
    assert report["sampled_words"] >= 2
    assert report["sampled_both_parities"] == report["sampled_words"]
    ooe = next(w for w in report["words_detail"] if w["w"] == "OOE")
    assert ooe["even"] >= 5 and ooe["odd"] >= 5
    assert ooe["theta_even_span"][0] <= 0.3
    assert ooe["theta_even_span"][1] >= 0.7
    assert ooe["theta_odd_span"][0] <= 0.3
    assert ooe["theta_odd_span"][1] >= 0.7
    assert len(report["ooe_shared_mod8"]) >= 1


def test_long_pe_run_exits_without_a_cylinder_law():
    run = walk_pe_run(365, cap=6)
    assert [row["y"] for row in run] == [763, 1749, 4447]
    assert all(row["word"] == "OOE" for row in run)
    assert all(next_landing(row["y"]) % 2 == 1 for row in run)
    seq = sequel_of(4447)
    assert seq is not None
    assert seq["word"] == "OOE"
    assert next_landing(seq["y"]) % 2 == 0


def test_lean_api_and_sorry_free():
    lean = lean_api_present()
    assert lean["sorry_free"]
    text = juggler_text()
    assert "sorry" not in text
    assert "admit" not in text
    for name in LEAN_THEOREMS:
        assert lean[name], name
    assert "import Problems.Juggler.PreimageCylinders" in text
