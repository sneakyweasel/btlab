"""Floor-boundary Diophantine geometry. Not a halt test."""

from __future__ import annotations

import json

from research.juggler_sequence.floor_boundary import (
    CLASS_COMPLEX,
    DATA_DIR,
    DOSSIER_PATH,
    JSON_PATH,
    anti_overclaim,
    cell_position,
    lean_api_present,
    next_gap_implication,
    profile_of,
    unique_state_census,
)
from research.juggler_sequence.global_defect import local_defect
from research.juggler_sequence.power_itineraries import floor_power
from research.juggler_sequence.realization_geometry import even_tower


def test_pair_is_local_defect_and_complement():
    for n in (2, 3, 4, 5, 9, 15, 16, 36, 37):
        rec = cell_position(n)
        assert rec["e"] == local_defect(n)
        assert rec["e"] + rec["u"] == rec["width"]
        assert rec["width"] == 2 * rec["m"] + 1
        assert rec["m"] == floor_power(n)


def test_even_position_is_inert():
    assert floor_power(36) == floor_power(38) == 6
    assert cell_position(36)["e"] == 0
    assert cell_position(38)["e"] == 2
    census = unique_state_census(n_max=80)
    assert census["even_position_inert"] is True


def test_odd_exact_hits_are_squares():
    rec = cell_position(9)
    assert rec["exact"] is True
    assert rec["m"] == 27
    assert cell_position(3)["e"] == 2
    assert cell_position(5)["e"] == 4
    assert all(cell_position(n)["e"] != 1 for n in range(1, 200, 2))


def test_small_odd_next_gap_is_generic():
    nxt = next_gap_implication(n_max=4000)
    assert nxt["OE_both_small"] == []
    assert 0.2 < nxt["odd_small_next_theta"]["mean"] < 0.8
    assert nxt["odd_small"] >= 2


def test_same_word_splits_and_hard_is_not_a_wall():
    ooe5 = profile_of(5, steps=3)
    ooe1991 = profile_of(1991, steps=3)
    assert abs(ooe5["steps"][0]["theta"] - ooe1991["steps"][0]["theta"]) > 0.2
    hard = profile_of(193)
    assert hard["theta"]["mean"] > 0.2
    assert hard["theta"]["mean"] < 0.8


def test_root_interior_shares_even_cell_image():
    root = even_tower(6)
    assert floor_power(root) == floor_power(4294972782) == 65536
    assert cell_position(root)["exact"] is True
    assert cell_position(4294972782)["exact"] is False


def test_lean_and_anti_overclaim():
    lean = lean_api_present()
    assert lean["sorry_free"]
    assert lean["localDefectEven_eq_zero_iff"]
    assert lean["even_preimage_iff"]
    assert lean["odd_preimage_unique"]
    assert lean["no_forbidden_engines"]
    anti = anti_overclaim()
    assert anti["theta_is_an_invariant"] is False
    assert anti["new_scalar_distance"] is False
    assert anti["reopen_sum_rho"] is False


def test_records_close():
    assert JSON_PATH.is_file()
    data = json.loads(JSON_PATH.read_text(encoding="utf-8"))
    assert data["decision"]["classification"] == CLASS_COMPLEX
    assert data["unique"]["even_position_inert"] is True
    assert data["small_odd"]["no_e1"] is True
    assert data["small_odd"]["only_3_has_e2"] is True
    assert data["next_gaps"]["OE_both_small"] == []
    text = DOSSIER_PATH.read_text(encoding="utf-8")
    assert "## Branch budget" in text
    assert "CLOSE" in text.split("## Decision", 1)[1]
    assert "## Publication assessment" in text
    assert (DATA_DIR / "manifest.json").is_file()
    assert (DATA_DIR / "boundary_profiles.csv").is_file()
    assert (DATA_DIR / "diophantine_hits.csv").is_file()
    assert (DATA_DIR / "counterexamples.jsonl").is_file()
