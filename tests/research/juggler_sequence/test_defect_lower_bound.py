"""First-defect amplification. Not a termination test."""

from __future__ import annotations

from research.juggler_sequence.defect_lower_bound import (
    LEAN_THEOREMS,
    amplification_census,
    amplify_from_first,
    crude_first_contribution,
    first_defect,
    frontier_scan,
    lean_api_present,
    odd_defect_lift,
    ooe_structural_bound,
    remainder_residue_census,
)
from research.juggler_sequence.global_defect import pow_gap
from research.juggler_sequence.lean_registry import juggler_text


def test_odd_lift_is_the_cubic_expansion():
    assert odd_defect_lift(5, 2) == pow_gap(5, 2, 3)
    assert odd_defect_lift(5, 2) == 3 * 25 * 2 + 3 * 5 * 4 + 8
    assert 3 * 25 * 2 <= odd_defect_lift(5, 2)


def test_residue_remainders_are_scale_free():
    report = remainder_residue_census(n_max=2000)
    assert report["even_mod4_min"][2] == 1
    assert report["even_two_t_even_min"] == 2
    assert report["even_two_t_odd_min"] == 1
    assert report["odd_mod8_min"][3] >= 2
    assert report["odd_mod8_min"][7] >= 3
    assert report["odd_one_zero_exists"] is True


def test_amplify_never_exceeds_delta():
    report = amplification_census(n_max=40, k_max=4)
    assert report["amp_fail"] == 0
    assert report["crude_fail"] == 0
    assert report["min_amp_over_crude"] == 1.0


def test_ooe_first_defect_is_before_the_even_letter():
    report = frontier_scan(n_max=120)
    for word, row in report.items():
        assert row["amplify_gt_delta"] == 0, word
        assert row["F_gt_delta"] == 0, word
        assert row["F_beats_surplus_expanding"] == 0, word
        assert row["checked"] > 0, word
        locations = set(row["first_defect_locations"])
        if word in {"OOE", "OOEO"}:
            assert locations <= {0, 1}
        if word == "OOOE":
            assert locations <= {0, 1, 2}


def test_ooe_structural_bound_on_seed():
    assert first_defect(5, "OOE") == 0
    assert ooe_structural_bound(5, "OOE") <= amplify_from_first(5, "OOE")
    assert crude_first_contribution(5, "OOE") == 4
    assert first_defect(9, "OOE") == 1
    assert ooe_structural_bound(9, "OOE") == crude_first_contribution(9, "OOE")


def test_lean_api_and_sorry_free():
    lean = lean_api_present()
    assert lean["sorry_free"]
    text = juggler_text()
    assert "sorry" not in text
    assert "admit" not in text
    for name in LEAN_THEOREMS:
        assert lean[name], name
    assert "residualStep_firstDefect" in text
    assert "residualStep_amplify" in text
