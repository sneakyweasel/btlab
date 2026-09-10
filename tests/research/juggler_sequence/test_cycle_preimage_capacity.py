"""Exact replay of selected capacity witnesses; no fibre or parameter census."""
import json
from math import isqrt

import pytest

from research.juggler_sequence import cycle_preimage_capacity as probe


@pytest.fixture(scope="module")
def report():
    return probe.report()


def test_only_three_existing_controls_and_four_selected_pairs(report):
    expected = (2**32+65, 2**40+65, 2**64+65)
    assert probe.FIXED_PARAMETERS == expected
    assert report["fixed_parameters"] == list(expected)
    assert tuple(row["u"] for row in report["controls"]) == expected
    for row in report["controls"]:
        r = row["r"]
        expected_pairs = []
        for v in (r*r+2, 2*r*r-1):
            upper = (v-1)//2
            expected_pairs.extend(((v,1),(v,upper if upper % 2 else upper-1)))
        pairs = [(pair["v"],pair["j"]) for pair in row["selected_pairs"]]
        assert pairs == expected_pairs and len(set(pairs)) == 4


def test_B_cells_guards_and_both_band_domains(report):
    for row in report["controls"]:
        m, M = row["minimum"], row["maximum"]
        for pair in row["selected_pairs"]:
            v,j,x,H,y = (pair[k] for k in ("v","j","source","intermediate","target"))
            assert v % 2 == j % 2 == 1 and 0 < 2*j < v
            assert x == v**4+2*j and H == v**6+3*v*v*j and y == v**3
            assert x % 2 == y % 2 == 1 and H % 2 == 0
            assert isqrt(x**3) == H and isqrt(H) == y
            assert x**3-H*H == pair["O_lower_margin"] == 3*v**4*j*j+8*j**3 > 0
            assert (H+1)**2-x**3 == pair["O_upper_margin"] > 0
            assert H-y*y == pair["E_lower_margin"] == 3*v*v*j > 0
            assert (y+1)**2-H == pair["E_upper_margin"] > 0
            assert row["b_low"] < row["b_high"] < x < row["t"] < H < M
            assert m < y < row["w"] and H > m*m
            assert pair["actual_guards"] and pair["inside_both_face_domains"]


def test_collision_multiplicity_and_closed_counts_without_enumeration(report):
    for row in report["controls"]:
        r, counts = row["r"], row["closed_form_counts"]
        n, singleton = counts["exhibited_supported_targets"], counts["singleton_preimages_lower_bound"]
        sources = counts["exhibited_sources"]
        assert 2*n == r*r-1 and 4*singleton == r*r+3 and n % 2 == 0
        assert 16*sources == 3*r**4-2*r*r-1
        # Sum floor(i/2), i=0,...,n-1, in closed form; no index enumeration.
        half = n//2
        assert sources == n*singleton+half*(half-1)
        assert counts["singleton_supported_targets"] == 1 < singleton
        low1,low2,high1,high2 = row["selected_pairs"]
        assert low1["target"] == low2["target"] < high1["target"] == high2["target"]
        assert low1["source"] < low2["source"] < high1["source"] < high2["source"]
        assert row["target_interval"] == {"lower": (r*r+2)**3, "upper": (2*r*r-1)**3}
        assert row["minimum"] < row["target_interval"]["lower"] < row["target_interval"]["upper"] < row["w"]
        assert not counts["complete_interval_support_asserted"] and not counts["all_preimages_counted"]


def test_unique_prescribed_A_preimage_has_wrong_final_guard(report):
    for row in report["controls"]:
        r, hole = row["r"], row["A_support_hole"]
        x,y,p,H = (hole[k] for k in ("unique_prescribed_source","target","first_O_output","second_O_output"))
        assert (x,p,H,y) == (r**8,r**12,r**18,r**9)
        assert row["minimum"] < x < row["a"] and row["z"] < y < row["t"]
        assert isqrt(x**3) == p and isqrt(p**3) == H and isqrt(H) == y
        assert x % 2 == p % 2 == H % 2 == y % 2 == 1
        assert hole["prescribed_A_output"] == y
        assert not hole["actual_final_E_guard"] and hole["exact_guarded_support"] == 0
        # The lower side follows from the ideal A upper bound. These two exact
        # cells and the last inequality put every larger source above y.
        assert y**8-(x-1)**9 == int(hole["left_ideal_power_upper_hex"], 16) > 0
        assert (x+1)**3-(r**12+r**4)**2 == hole["right_first_lower_margin"] > 0
        assert (r**12+r**4)**3-(r**18+r**10)**2 == hole["right_second_lower_margin"] > 0
        assert r**18+r**10-(y+1)**2 == hole["right_final_lower_margin"] > 0
        assert not hole["target_in_retained_set_asserted"]


def test_scope_closes_only_ordinary_capacity_gate(report):
    assert report["decision"] == "CLOSE" and report["counts_by_formula_only"]
    assert report["selected_pairs_per_parameter"] == 4
    assert report["proof_owner"] == "docs/problems/juggler_cycle_preimage_capacity.md"
    assert not any(report[key] for key in (
        "source_search","orbit_search","rank_search","residue_search","fibre_enumeration",
        "new_local_prefix","new_period_or_height_bound","strict_shared_support_deficit","full_matching_asserted",
        "no_cycle_proved","new_lean_or_paper_claim"))
    for row in report["controls"]:
        assert row["all_inherited_checks"]
        assert not row["full_matching_asserted"] and not row["periodic_orbit_asserted"]


def test_exact_record_round_trips_through_json(report):
    # The largest proof margin exceeds the default decimal conversion limit.
    assert json.loads(json.dumps(report)) == report
