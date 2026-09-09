"""Exact checks and negative controls for cubic-band order rigidity."""
import json
from itertools import permutations
from math import gcd

import pytest

from research.juggler_sequence.cycle_cubic_band import (
    all_small_cycles, branch_step, certify_cycle, counterexamples,
    orbit_cycle, threshold_step,
)
from research.juggler_sequence.lean_paths import DATA_ROOT


@pytest.mark.parametrize("b", [3, 4, 5, 9, 17, 30])
def test_invariant_interval_and_no_fixed_point(b):
    for x in range(b, b**3):
        y = threshold_step(x, b)
        assert b <= y < b**3 and y != x
        radicand = x**3 if x < b*b else x
        assert y*y <= radicand < (y+1)*(y+1)
    # Four points straddling the two branches, at scales far beyond floats.
    for big in [10**20+3, 10**80+7]:
        for x in [big, big*big-1, big*big, big**3-1]:
            y = threshold_step(x, big)
            assert big <= y < big**3 and y != x


def test_exact_complete_graph_controls():
    for b, expected_count, expected_period in [(3, 2, 3), (5, 1, 14), (9, 2, 11), (30, 4, 19)]:
        cycles = all_small_cycles(b)
        assert len(cycles) == expected_count
        for states, row in cycles.items():
            assert row["period"] == expected_period
            assert not row["juggler_cycle"]
            assert row["parity_mismatches"] > 0
            # Verify cells directly; do not reuse the root evaluator.
            for k, x in enumerate(states):
                y = states[(k+1) % len(states)]
                h = 3 if x < b*b else 1
                assert y*y <= x**h < (y+1)*(y+1)


def test_abstract_sorted_permutation_argument():
    # Exhaust all permutations through size 7, independently of threshold
    # dynamics. The separated increasing blocks must be the rank rotation.
    hits = 0
    for length in range(2, 8):
        for p in permutations(range(length)):
            for odd in range(1, length):
                lo, hi = p[:odd], p[odd:]
                if not (all(lo[i] < lo[i+1] for i in range(len(lo)-1))
                        and all(hi[i] < hi[i+1] for i in range(len(hi)-1))
                        and max(hi) < min(lo)):
                    continue
                even = length-odd
                assert p == tuple((i+even) % length for i in range(length))
                orbit, k = set(), 0
                while k not in orbit:
                    orbit.add(k)
                    k = p[k]
                assert len(orbit) == length // gcd(length, even)
                hits += 1
    assert hits == sum(length-1 for length in range(2, 8))


def test_parity_is_a_separate_requirement():
    narrow, tall = counterexamples()
    assert narrow["parity_mismatch_states"] == [36, 14, 52]
    assert narrow["maximum"] < narrow["minimum"]**3
    assert 3*len(narrow["parity_mismatch_states"]) < narrow["period"]
    assert branch_step(36, False) == 6
    assert threshold_step(36, 9) == 216
    assert tall["parity_mismatch_states"] == [6]
    assert tall["gcd"] == 2
    assert tall["maximum"] > tall["minimum"]**3
    assert not narrow["actual_juggler_cycle"] and not tall["actual_juggler_cycle"]


def test_floor_ties_are_excluded_only_on_the_cycle():
    # The image blocks need not be strictly separated on the whole interval.
    # The proof must use injectivity on a primitive cycle to remove this tie.
    assert threshold_step(3, 3) == threshold_step(25, 3) == 5
    for states in all_small_cycles(3):
        assert not ({3, 25} <= set(states))


def test_invalid_inputs_and_corrupted_cycles_are_rejected():
    with pytest.raises(ValueError):
        orbit_cycle(2)
    with pytest.raises(ValueError):
        orbit_cycle(3, start=27)
    with pytest.raises(ValueError):
        orbit_cycle(3, cap=0)
    assert orbit_cycle(9, cap=2) is None
    with pytest.raises(AssertionError):
        certify_cycle(9, [9, 27, 141])
    with pytest.raises(AssertionError):
        certify_cycle(9, [9, 27, 140, 9])


def test_archived_scope_and_capped_results():
    data = json.loads((DATA_ROOT / "cycle_cubic_band" / "summary.json").read_text(encoding="utf-8"))
    done = [row for row in data["rows"] if "period" in row]
    capped = [row for row in data["rows"] if "unresolved_at_step_cap" in row]
    assert len(done) == 9998 and len(capped) == 4
    assert sum(row["cycles"] for row in data["complete_graphs"]) == 38
    assert all(row["minimum_mismatches"] > 0 for row in data["complete_graphs"])
    assert max(row["period"] for row in done) == 16631
    assert sum(row["transient"] == 0 for row in done) == 1355
    assert all(not row["juggler_cycle"] for row in done)
    assert all("juggler_cycle" not in row for row in capped)
    assert data["counterexamples"] == counterexamples()


def test_periodic_union_has_one_period_and_interlaces():
    from research.juggler_sequence.cycle_cubic_band import periodic_union_record
    for b, points, count, length, upper in [(3, 6, 2, 3, 1), (9, 22, 2, 11, 4), (29, 57, 3, 19, 7)]:
        row = periodic_union_record(b)
        assert (row["periodic_points"], row["cycles"], row["common_period"], row["common_upper_count"]) == (points, count, length, upper)
        assert row["interlacing_verified"]


@pytest.mark.parametrize("b", [3, 9, 11, 29, 101])
def test_rounded_cycles_keep_source_parity_but_change_exact_edges(b):
    from research.juggler_sequence.cycle_cubic_band import rounding_cycle, rounding_cycle_record
    cy = rounding_cycle(b)
    assert cy is not None
    row = rounding_cycle_record(b, cy)
    assert row["one_unit_corrections"] > 0
    assert not row["actual_juggler_cycle"]
    if b == 11:
        assert cy == [13, 45, 300, 17, 69, 572, 23, 109, 1136, 33, 188]


@pytest.mark.parametrize("b", [3, 11, 101, 10**30+1, 10**100+1])
def test_projection_seam_and_one_unit_error_exactly(b):
    from research.juggler_sequence.cycle_cubic_band import project_parity_down, rounding_step
    for n in (b, b+1, b*b-2, b*b-1, b*b, b*b+1, b*b+2, b**3-1, b**3):
        y = project_parity_down(n, b)
        assert n-y in (0, 1)
        assert (y % 2 == 1 and b <= y <= b*b) or (y % 2 == 0 and b*b+1 <= y < b**3)
    assert project_parity_down(b*b, b) == b*b
    assert project_parity_down(b*b+1, b) == b*b+1
    assert rounding_step(b*b, b) == b**3-1
    for x in (b, b*b, b*b+1, b**3-1):
        y = rounding_step(x, b)
        rad = x**3 if x % 2 else x
        assert y*y <= rad < (y+2)**2
        assert branch_step(x, bool(x % 2))-y in (0, 1)
        assert y != x


def test_projection_rejects_wrong_domain_and_even_threshold():
    from research.juggler_sequence.cycle_cubic_band import project_parity_down, rounding_step
    for n, b in [(3, 2), (4, 4), (2, 3), (28, 3)]:
        with pytest.raises(ValueError):
            project_parity_down(n, b)
    with pytest.raises(ValueError):
        rounding_step(4, 3)
    with pytest.raises(ValueError):
        rounding_step(11, 3)


def test_sorted_grid_identities_numerically_on_exact_cycles():
    from decimal import Decimal
    from research.juggler_sequence.cycle_cubic_band import sorted_grid_record
    for b in (3, 9, 29):
        for cy, record in all_small_cycles(b).items():
            row = sorted_grid_record(list(cy), record["odd_branch_count"])
            assert Decimal(row["defect_sum_residual"]) < Decimal("1e-65")
            assert Decimal(row["lift_relation_residual"]) < Decimal("1e-65")


def test_same_branch_gap_information_cannot_see_the_shift():
    from research.juggler_sequence.cycle_cubic_band import branch_offset_record
    row = branch_offset_record()
    assert row["period"] == 11 and row["one_unit_corrections"] == 7
    cells = {c["x"]: c for c in row["floor_cells"]}
    for x, cx in cells.items():
        # Independent bounds around the asserted true root.
        rad = x**3 if x % 2 else x
        jx = cx["J_x"]
        assert jx*jx <= rad < (jx+1)*(jx+1)
        for z, cz in cells.items():
            if x % 2 == z % 2:
                assert cz["G_x"]-cx["G_x"] == cz["J_x"]-cx["J_x"]
    assert cells[13]["J_x"] == 46 and cells[13]["G_x"] == 45
    assert row["maximum"] < row["minimum"]**3


def test_followup_archive_has_exact_declared_scope():
    from research.juggler_sequence.cycle_cubic_band import branch_offset_record
    data = json.loads((DATA_ROOT / "cycle_cubic_band/followup.json").read_text(encoding="utf-8"))
    assert [r["b"] for r in data["common_period"]] == [3, 9, 29]
    assert [r["b"] for r in data["rounding_cycles"]] == [3, 9, 11, 29, 101]
    assert len(data["grid_checks"]) == 12
    assert data["branch_offset_control"] == branch_offset_record()
    assert data["no_cycle_proved"] is False


def test_absolute_phase_controls_use_strict_integer_square_bounds():
    from research.juggler_sequence.cycle_cubic_band import phase_plateau_record
    rows = [phase_plateau_record(b) for b in (3, 9)]
    assert [r["states_checked"] for r in rows] == [24, 720]
    assert [r["minimum_integer_margin"] for r in rows] == [2377, 2047033]
    for row in rows:
        b, denominator = row["b"], row["phase_denominator"]
        assert denominator == 2*b**3 and row["all_square_comparisons_strict"]
        # Check the claimed boundary using only the independently certified roots.
        for x in (b, b*b-1, b*b, b**3-1):
            rad, q = (x**3 if x < b*b else x), threshold_step(x, b)
            assert q*q <= rad < (q+1)**2
            assert denominator**2*rad < (denominator*(q+1)-1)**2
    with pytest.raises(ValueError):
        phase_plateau_record(2)


def test_largest_odd_strip_checks_strictness_and_sign_before_squaring():
    from research.juggler_sequence.cycle_cubic_band import largest_odd_strip_holds
    assert largest_odd_strip_holds(3, 5)
    assert largest_odd_strip_holds(9, 75)
    # sqrt(9)=3 makes the exact strict boundary u=81-4=77.
    assert not largest_odd_strip_holds(9, 77)
    assert not largest_odd_strip_holds(9, 79)
    # Squaring alone would incorrectly accept this negative gap.
    assert not largest_odd_strip_holds(9, 101)
    with pytest.raises(ValueError):
        largest_odd_strip_holds(9, 76)


def test_absolute_anchors_do_not_hide_the_false_unit_cell():
    from research.juggler_sequence.cycle_cubic_band import absolute_anchor_controls
    rounded, two_edges = absolute_anchor_controls()
    assert rounded["minimum_anchor_exact"] and rounded["maximum_anchor_exact"]
    assert rounded["closed_cycle"] and not rounded["actual_juggler_cycle"]
    assert [c["exact_juggler_edge"] for c in rounded["cells"]] == [True, False, True]
    broken = rounded["cells"][1]
    assert (broken["x"], broken["y"], broken["radicand"]) == (5, 10, 125)
    assert broken["lower_cell_holds"] and not broken["strict_upper_cell_holds"]
    assert broken["upper_cell_slack"] == -4
    assert branch_step(5, True) == 11
    assert rounded["largest_odd_strip"]["coefficient"] == "4/3"
    assert two_edges["M"] == two_edges["maximum_ceiling"] == 674
    assert two_edges["top_landing"] == 25 and two_edges["both_anchor_cells_exact"]
    assert not two_edges["closed_cycle"] and not two_edges["actual_juggler_cycle"]


def test_absolute_cell_report_only_reuses_seven_archived_cycles(monkeypatch):
    from decimal import Decimal
    import research.juggler_sequence.cycle_cubic_band as cubic

    def forbidden_search(*args, **kwargs):
        raise AssertionError("the absolute-cell verifier must not search for cycles")

    monkeypatch.setattr(cubic, "all_small_cycles", forbidden_search)
    monkeypatch.setattr(cubic, "orbit_cycle", forbidden_search)
    monkeypatch.setattr(cubic, "rounding_cycle", forbidden_search)
    data = cubic.absolute_cells_report()
    assert data["scope"]["phase_states_checked"] == 744
    assert data["scope"]["archived_threshold_cycle_counts"] == {"3": 2, "9": 2, "29": 3}
    assert len(data["grid_controls"]) == 7
    assert [r["minimum"] for r in data["grid_controls"]] == [3, 4, 9, 10, 35, 31, 34]
    for row in data["grid_controls"]:
        assert row["decimal_precision"] == 80 and not row["interval_certificate"]
        assert Decimal(row["Lambda"]) < Decimal(row["actual_inverse_log_sum"])
        assert Decimal(row["actual_inverse_log_sum"]) <= Decimal(row["finite_geometric_bound"])
        assert Decimal(row["finite_geometric_bound"]) < Decimal(row["closed_bound"])
        assert Decimal(row["G2_left"]) < Decimal(row["G2_right"])
        assert row["parity_mismatches"] > 0 and not row["actual_juggler_cycle"]
    assert not data["uniform_wrong_parity_proved"] and not data["no_cycle_proved"]
    archive = json.loads((DATA_ROOT / "cycle_cubic_band/absolute_cells_controls.json").read_text(encoding="utf-8"))
    assert archive == data
