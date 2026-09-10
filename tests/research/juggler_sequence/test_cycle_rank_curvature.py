"""One fixed outward-interval replay; no full-cycle realization is tested."""
import json
from fractions import Fraction

import pytest

from research.juggler_sequence import cycle_rank_curvature as probe


@pytest.fixture(scope="module")
def fixed_report(tmp_path_factory):
    destination = tmp_path_factory.mktemp("curvature_purity") / "data"
    with pytest.MonkeyPatch.context() as patch:
        patch.setattr(probe, "DATA_ROOT", destination)
        result = probe.report()
        assert not destination.exists()
    return result


def rational(record):
    return Fraction(int(record["numerator"]), int(record["denominator"]))


def interval(record):
    return rational(record["lower"]), rational(record["upper"])


def intersects(left, right):
    a, b = left
    c, d = right
    return max(a, c) <= min(b, d)


def enclosures(value):
    if isinstance(value, dict):
        if "lower" in value and "upper" in value:
            yield value
        else:
            for item in value.values():
                yield from enclosures(item)
    elif isinstance(value, list):
        for item in value:
            yield from enclosures(item)


def test_exact_fixed_tuple_and_group_lengths(fixed_report):
    data = fixed_report["tuple"]
    assert data == {"L": 780239, "o": 492276, "e": 287963, "m": 350000001,
                    "k": 478245, "h": 176251, "group_lengths": [176251, 301994, 301994]}
    assert data["o"]+data["e"] == data["L"]
    assert data["e"]*data["k"] % data["L"] == 1
    assert data["h"] == 2*data["k"]-data["L"]
    assert sum(data["group_lengths"]) == data["L"]
    assert set(fixed_report["positions"]) == {"1", "2"}
    assert len(fixed_report["integer_controls"]) == 2


def test_exact_dyadic_storage_and_outward_decimal_displays(fixed_report):
    assert probe.dyadic((0, 3, 2, 2)) == 12
    assert probe.dyadic((1, 3, -2, 2)) == Fraction(-3, 4)
    assert probe.dyadic((0, 0, 0, 0)) == 0
    records = list(enclosures(fixed_report))
    assert len(records) > 40
    for record in records:
        lower, upper = interval(record)
        assert lower <= upper
        for value in (lower, upper):
            denominator = value.denominator
            assert denominator > 0 and denominator & (denominator-1) == 0
        assert Fraction(record["decimal_lower"]) <= lower
        assert Fraction(record["decimal_upper"]) >= upper
        assert Fraction(record["width_upper"]) >= upper-lower
    assert json.loads(json.dumps(fixed_report)) == fixed_report


def test_certified_ideal_curvature_survives_cancellation(fixed_report):
    lower, upper = interval(fixed_report["ideal_curvature"])
    assert Fraction("0.2822331861938527805381902958134042098747") < lower
    assert upper < Fraction("0.2822331861938527805381902958134042098749")
    assert 0 < lower < upper < 2
    assert upper-lower < Fraction(1, 10**100)
    lam_low, lam_high = interval(fixed_report["constants"]["surplus"])
    assert Fraction("0.0000034711981668939710") < lam_low < lam_high
    assert lam_high < Fraction("0.0000034711981668939711")


def test_exact_odd_lattice_controls_and_nearest_first_rank(fixed_report):
    first_ideal = interval(fixed_report["positions"]["1"]["ideal"])
    assert [row["curvature"] for row in fixed_report["integer_controls"]] == [0, 2]
    for row, c2 in zip(fixed_report["integer_controls"], (350019393, 350019395)):
        m, c1 = row["c0"], row["c1"]
        assert (m, c1, row["c2"]) == (350000001, 350009697, c2)
        assert all(x % 2 == 1 for x in (m, c1, c2))
        assert c1-1 < first_ideal[0] < first_ideal[1] < c1+1
        assert row["first_gap"] == c1-m == 9696
        assert row["second_gap"] == c2-c1 >= 2
        assert row["second_gap"] % 2 == 0
        assert row["curvature"] == c2-2*c1+m
    assert fixed_report["positive_even_curvature_lower_bound"] == 2
    assert not fixed_report["odd_spacing_alone_forces_positive_curvature"]


def test_shared_mass_and_order_certificates_are_strict(fixed_report):
    constants = fixed_report["constants"]
    alpha = interval(constants["alpha"])
    mean = interval(constants["mean_defect"])
    omega = interval(constants["omega"])
    lam_low, lam_high = interval(constants["surplus"])
    for row in fixed_report["integer_controls"]:
        masses = [interval(row["group_masses"][name]) for name in ("p", "q", "r")]
        assert all(low > 0 for low, high in masses)
        assert sum(low for low, high in masses) <= lam_low <= lam_high
        assert lam_high <= sum(high for low, high in masses)
        for name, mass, length in zip(("p_per_edge", "q_per_edge", "r_per_edge"),
                                      masses, fixed_report["tuple"]["group_lengths"]):
            rate = interval(row["group_rates"][name])
            assert rate[0] > 0 and intersects((length*rate[0], length*rate[1]), mass)
        w1, w2 = interval(row["w1"]), interval(row["w2"])
        assert 0 < w1[0] <= w1[1] < w2[0] <= w2[1]
        assert w2[1] < alpha[0]-mean[1] and w2[1] < omega[0]
        for name in ("full_real_order_gap_lower", "cutoff_margin",
                     "p_minus_initial_defect", "r_minus_terminal_lower_charge"):
            assert interval(row[name])[0] > 0
        assert row["nonnegative_total_defect_extension"]
        assert not row["exact_initial_edge_realization_asserted"]


def test_curvature_windows_are_distinct_and_match_the_exact_controls(fixed_report):
    windows = fixed_report["curvature_windows"]
    H0, H2 = interval(windows["H0"]), interval(windows["H2"])
    assert H0[1] < 0 < H2[0]
    width = interval(windows["H2_minus_H0"])
    assert width[0] > 0 and intersects(width, (H2[0]-H0[1], H2[1]-H0[0]))
    for row, target in zip(fixed_report["integer_controls"], (H0, H2)):
        w1, w2, chi = interval(row["w1"]), interval(row["w2"]), interval(row["chi"])
        assert intersects(chi, (w2[0]-2*w1[1], w2[1]-2*w1[0]))
        assert intersects(chi, target)
        assert row["window_identity_intervals_intersect"]
    ratio = interval(windows["minus_H0_over_eta_m"])
    assert Fraction("0.28224") < ratio[0] < ratio[1] < Fraction("0.28225")


def test_independent_grid_allowances_do_not_claim_shared_feasibility(fixed_report):
    for position in fixed_report["positions"].values():
        ideal = interval(position["ideal"])
        lower, upper = interval(position["lower_position"]), interval(position["upper_position"])
        assert lower[1] < ideal[0] <= ideal[1] < upper[0]
        for key in ("downward_allowance", "upward_allowance"):
            allowance = interval(position[key])
            assert 23900 < allowance[0] <= allowance[1] < 23905


def test_actual_minimum_guard_failure_is_exact(fixed_report):
    m = fixed_report["tuple"]["m"]
    edge = fixed_report["actual_minimum_edge"]
    image = edge["O_m"]
    assert image == 6547900454916 and image % 2 == 0 and m % 2 == 1
    assert image*image <= m*m*m < (image+1)*(image+1)
    assert edge["output_even"] and edge["therefore_not_an_actual_cubic_cycle_minimum"]
    assert interval(edge["defect"])[0] > 0


def test_scope_excludes_full_integer_cycle_claims(fixed_report):
    assert fixed_report["backend"]["name"] == "mpmath.iv"
    assert fixed_report["backend"]["decimal_precision"] == 120
    assert not fixed_report["backend"]["formal_kernel_certificate"]
    flags = fixed_report["scope_flags"]
    assert flags["one_fixed_tuple"] and flags["only_first_three_integer_ranks"]
    assert flags["nonnegative_total_defect_relaxation"]
    assert not any(flags[name] for name in ("full_upper_unit_cells", "all_rank_parities",
                                          "all_rank_integrality", "actual_cycle", "new_floor_or_period_bound"))
    assert not fixed_report["rank_source_or_orbit_census"]
    assert not fixed_report["full_cycle_constraints_satisfied"]
    assert not fixed_report["no_cycle_proved"]


def test_signed_floor_sums_match_small_exact_controls():
    # These small arithmetic cases validate the counting algorithm, not any orbit.
    for n, modulus in ((0, 1), (1, 2), (7, 5), (19, 11)):
        for multiplier, offset in ((0, 0), (3, 2), (-7, 4), (9, -13), (-9, -13)):
            expected = sum((multiplier*j+offset)//modulus for j in range(n))
            assert probe.floor_sum(n, modulus, multiplier, offset) == expected
    for args in ((-1, 3, 2, 1), (3, 0, 2, 1), (3, -1, 2, 1),
                 (3, 2, 1.5, 0), (True, 2, 1, 0)):
        with pytest.raises(ValueError):
            probe.floor_sum(*args)


def test_group_counts_use_target_phase_and_exact_full_cardinalities():
    for n in (0, 1, 2, 3, 17, 64, 137):
        phases = [(probe.CAP_K*j) % probe.L for j in range(n)]
        expected = (sum(1 <= phase <= probe.CAP_H for phase in phases),
                    sum(probe.CAP_H < phase <= probe.CAP_K for phase in phases),
                    sum(phase == 0 or phase > probe.CAP_K for phase in phases))
        assert probe.group_prefix_counts(n) == expected
        for threshold in (0, 1, probe.CAP_H, probe.CAP_H+1, probe.CAP_K+1, probe.L):
            assert probe.below_count(n, threshold) == sum(p < threshold for p in phases)
    assert probe.group_prefix_counts(1) == (0, 0, 1)
    assert probe.group_prefix_counts(2) == (0, 1, 1)
    assert probe.group_prefix_counts(3) == (1, 1, 1)
    assert probe.group_prefix_counts(probe.L) == (176251, 301994, 301994)


def test_full_capacity_enclosures_and_darboux_error(fixed_report):
    cap = fixed_report["full_capacity_envelopes"]
    assert cap["tuple"] == {"L": 780239, "o": 492276, "e": 287963,
                            "m_lower": 350000001, "k": 478245, "h": 176251}
    assert cap["group_cardinalities"] == {"P": 176251, "Q": 301994, "R": 301994}
    assert cap["method"]["blocks"] == 24383
    assert cap["method"]["envelope_points"] == 48766
    assert cap["method"]["block_size"] == 32
    assert cap["method"]["decimal_precision"] == 70
    capacities = [interval(cap["capacities"][g]) for g in ("P", "Q", "R")]
    for endpoints, expected_lower, expected_upper in zip(
            capacities, ("1.0788e-6", "1.8484e-6", "1.8485e-6"),
            ("1.0799e-6", "1.8503e-6", "1.8503e-6")):
        assert Fraction(expected_lower) < endpoints[0] <= endpoints[1] < Fraction(expected_upper)
    total = interval(cap["total_capacity"])
    assert intersects(total, (sum(x[0] for x in capacities), sum(x[1] for x in capacities)))
    assert Fraction("4.7758e-6") < total[0] < total[1] < Fraction("4.7804e-6")
    assert 0 < total[1]-total[0] < Fraction("4.503e-9") < Fraction("1e-8")
    assert interval(cap["total_minus_surplus"])[0] > Fraction("1.3e-6")


def test_full_capacity_RC9_window_and_aggregate_controls(fixed_report):
    cap = fixed_report["full_capacity_envelopes"]
    lower, upper = interval(cap["RC9_lower_endpoint"]), interval(cap["RC9_upper_endpoint"])
    H0, H2 = (interval(cap["curvature_window"][key]) for key in ("H0", "H2"))
    assert lower[1] < Fraction("-1.3e-6") < H0[0]
    assert H2[1] < Fraction("1.3e-6") < upper[0]
    for key in ("RC9_lower_to_H0_clearance", "H2_to_RC9_upper_clearance"):
        assert interval(cap[key])[0] > Fraction("1.3e-6")
    assert [row["curvature"] for row in cap["integer_controls"]] == [0, 2]
    for row, old in zip(cap["integer_controls"], fixed_report["integer_controls"]):
        assert row["c1"] == old["c1"] and row["c2"] == old["c2"]
        for key in ("P", "Q", "R"):
            assert interval(row["capacity_slacks"][key])[0] > 0
            assert intersects(interval(row["masses"][key]), interval(old["group_masses"][key.lower()]))
        assert row["aggregate_envelope_box_feasible"]
        assert not row["actual_cell_feasibility_asserted"]


def test_lower_charge_and_parity_upper_face_robustness(fixed_report):
    cap = fixed_report["full_capacity_envelopes"]
    old = interval(cap["old_compulsory_charge_total_ceiling"])
    shave = interval(cap["parity_cap_shave_total_ceiling"])
    combined = interval(cap["twice_combined_refinement_ceiling"])
    assert Fraction("1.6187e-13") < old[0] < old[1] < Fraction("1.6188e-13")
    assert Fraction("3.2375e-13") < shave[0] < shave[1] < Fraction("3.2376e-13")
    assert intersects(combined, (2*(old[0]+shave[0]), 2*(old[1]+shave[1])))
    assert 0 < combined[0] < combined[1] < Fraction("9.713e-13")
    for key in ("refined_lower_to_H0_clearance", "H2_to_refined_upper_clearance"):
        assert interval(cap[key])[0] > Fraction("1.3e-6")
    assert cap["independent_parity_upper_faces_do_not_change_window_comparison"]


def test_existing_absolute_cell_cutoff_and_capacity_scope(fixed_report):
    cap = fixed_report["full_capacity_envelopes"]
    cutoff = cap["known_minimum_upper_cutoff"]
    assert cutoff["minimum_cutoff"] == 520000000
    assert cutoff["existing_bound_reference"] == (
        "docs/problems/juggler_cycle_absolute_cells.md, Result 1, equation (1)")
    low, high = interval(cutoff["existing_geometric_envelope"])
    assert Fraction("3.2302932149555275e-6") < low < high < Fraction("3.2302932149555276e-6")
    assert interval(cutoff["surplus_minus_existing_envelope"])[0] > Fraction("2.4e-7")
    assert cutoff["envelope_strictly_below_surplus"]
    assert cutoff["decreasing_bound_excludes_larger_minima_for_fixed_counts"]
    assert not cutoff["new_general_theorem_or_descent_floor"] and not cutoff["minimum_sweep"]
    flags = cap["scope_flags"]
    assert flags["envelope_box_only"]
    assert not any(flags[key] for key in ("all_actual_caps_satisfied",
        "full_potential_and_sortedness_simultaneously_asserted",
        "positive_lower_faces_evaluated_at_lower_minimum", "new_total_capacity_theorem"))
    assert cap["method"]["lower_faces_for_universal_test"] == 0
    assert not cap["method"]["actual_state_or_trajectory_enumeration"]
    assert not cap["actual_caps_or_full_integer_cycle_feasible"]
    assert "elapsed_seconds" not in json.dumps(fixed_report)


def test_cli_is_read_only_unless_write_is_requested(fixed_report, tmp_path, monkeypatch, capsys):
    destination = tmp_path / "data"
    monkeypatch.setattr(probe, "DATA_ROOT", destination)
    monkeypatch.setattr(probe, "report", lambda: fixed_report)
    probe.main([])
    status = json.loads(capsys.readouterr().out)
    assert status["record_written"] is False and not destination.exists()
    assert status["integer_curvatures"] == [0, 2]
    probe.main(["--write"])
    status = json.loads(capsys.readouterr().out)
    assert status["record_written"] is True and not status["actual_cycle"]
    written = destination / "cycle_rank_curvature" / "controls.json"
    assert json.loads(written.read_text(encoding="utf-8")) == fixed_report
