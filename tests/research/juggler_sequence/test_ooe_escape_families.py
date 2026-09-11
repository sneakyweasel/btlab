"""Exact finite replay tests; these do not prove a uniform escape statement."""
import json

import pytest

from research.juggler_sequence import ooe_escape_families as probe
from research.juggler_sequence.lean_paths import DATA_ROOT


@pytest.fixture(scope="module")
def fixed_report():
    return probe.report()


def assert_square_cell(radicand, root):
    # Independent adjacent-square verification, without the probe's isqrt.
    assert root >= 0
    assert root*root <= radicand < (root+1)*(root+1)


def assert_actual_ooe(block):
    x, h, p, z = (block[key] for key in ("x", "h", "p", "z"))
    assert (x % 2, h % 2, p % 2, z % 2) == (1, 1, 0, 1)
    assert_square_cell(x*x*x, h)
    assert_square_cell(h*h*h, p)
    assert_square_cell(p, z)


def test_actual_valuation_counterexample_has_exact_cells():
    block = probe.validate(199)
    assert block == {"valid": True, "x": 199, "h": 2807, "p": 148718, "z": 385}
    assert_actual_ooe(block)
    assert [199**3-2807**2, 2808**2-199**3,
            2807**3-148718**2, 148719**2-2807**3,
            148718-385**2, 386**2-148718] == [1350, 4265, 8419, 289018, 493, 278]
    assert probe.valuation(199-1) == 1 < 7 == probe.valuation(385-1)


def test_five_block_trace_and_first_failed_guard(fixed_report):
    longest, = fixed_report["ordinary"]["longest_traces"]
    assert longest["start"] == 7939 and longest["validated_returns"] == 5
    assert [block["x"] for block in longest["blocks"]] + [longest["blocks"][-1]["z"]] == [
        7939, 24391, 86225, 356933, 1764655, 10653499]
    for block in longest["blocks"]:
        assert_actual_ooe(block)
    stop = longest["stop"]
    assert stop == {"valid": False, "reason": "second_O_source_even",
                    "x": 10653499, "h": 34772699236}
    assert_square_cell(stop["x"]**3, stop["h"])
    assert stop["h"] % 2 == 0 and not longest["cap_hit"]


def test_fixed_scope_counts_and_all_caps_unhit(fixed_report):
    assert (probe.START_MIN, probe.START_MAX, probe.RETURN_CAP) == (5, 20001, 20)
    ordinary = fixed_report["ordinary"]
    assert ordinary["start_interval"] == [5, 20001]
    assert ordinary["odd_starts"] == 9999
    assert ordinary["block_observations"] == 1436
    assert ordinary["distinct_observed_edges"] == 1371
    assert ordinary["length_counts"] == {"0": 8748, "1": 1097, "2": 129, "3": 20, "4": 4, "5": 1}
    assert ordinary["stop_counts"] == {"return_endpoint_even": 1394,
                                      "second_O_source_even": 5724, "E_source_odd": 2881}
    assert sum(ordinary["length_counts"].values()) == 9999
    assert sum(int(k)*v for k, v in ordinary["length_counts"].items()) == 1436
    assert ordinary["cap_hits"] == 0
    assert all(not row["cap_hit"] for row in fixed_report["family"]["controls"])


def test_valuation_directions_skip_zero_without_monotonicity_claim(fixed_report):
    assert probe.valuation(0) is None
    assert probe.valuation(-48) == probe.valuation(48) == 4
    ordinary = fixed_report["ordinary"]
    assert ordinary["valuation_directions"] == {
        "-1": {"decrease": 513, "equal": 453, "increase": 470},
        "1": {"increase": 497, "equal": 465, "decrease": 474},
        "-9": {"skipped_zero": 1, "decrease": 508, "equal": 449, "increase": 478}}
    for offset, directions in ordinary["valuation_examples"].items():
        for direction, examples in directions.items():
            assert examples
            for block in examples:
                assert_actual_ooe(block)
                before, after = block["before"], block["after"]
                assert before == probe.valuation(block["x"]+int(offset))
                assert after == probe.valuation(block["z"]+int(offset))
                assert (after > before if direction == "increase" else
                        after < before if direction == "decrease" else after == before)


def test_fixed_family_departures_are_guard_failures_not_trajectory_results(fixed_report):
    family = fixed_report["family"]
    assert family["parameters"] == list(range(3, 32, 2))
    assert probe.FAMILY_RETURN_CAP == family["total_return_cap"] == 12
    expected = {
        "second_O_source_even": {5, 7, 11, 15, 19, 21, 23, 27, 31},
        "E_source_odd": {3, 17, 25, 29}, "return_endpoint_even": {9, 13}}
    for row in family["controls"]:
        s = row["parameter"]
        assert row["start"] == s**8+8
        assert row["validated_returns"] == row["departure_after_return"] == 1
        assert row["validated_returns_after_departure"] == 0
        block, = row["blocks"]
        assert_actual_ooe(block)
        assert block["z"] == s**9+9*s-1
        assert block["source_family_parameter"] == s
        assert block["endpoint_family_parameter"] is None
        assert s in expected[row["stop"]["reason"]]


def test_residue_formula_exact_fixed_controls(fixed_report):
    expected = [(q, a, k) for q in (2, 6, 16, 48, 64)
                for a in sorted({1, q-1}) for k in (1, 3)]
    rows = fixed_report["residue_fixtures"]
    assert len(rows) == 18
    assert [(row["modulus"], row["oddresidue"], row["multiplier"]) for row in rows] == expected
    for row in rows:
        q, a, k, t, x, u = (row[key] for key in (
            "modulus", "oddresidue", "multiplier", "t", "source", "first_O_output"))
        assert t == 2*q*k and t >= 4 and 2*a < t
        assert x == t**8+a and 2*u == 2*t**12+3*a*t**4
        assert x % q == a and x % 2 == 1 and u % 2 == 0
        assert_square_cell(x**3, u)
        assert 4*(x**3-u*u) == 3*a*a*t**8+4*a**3
        assert row["O_lower_margin"] == x**3-u*u > 0
        assert row["O_upper_margin"] == (u+1)**2-x**3 > 0
        assert not row["second_O_guard"]
        assert not row["actual_OOE_return_asserted"] and not row["periodic_orbit_asserted"]


@pytest.mark.parametrize("args", [
    (0, 1, 1), (-2, 1, 1), (3, 1, 1), (6, 0, 1), (6, 2, 1),
    (6, 6, 1), (6, 7, 1), (6, -1, 1), (6, 1, 0), (6, 1, -1),
    (6.0, 1, 1), (6, 1.0, 1), (6, 1, True)])
def test_residue_formula_rejects_invalid_arguments(args):
    with pytest.raises(ValueError):
        probe.residue_counterexample(*args)


def test_report_is_json_stable_and_explicit_about_finite_scope(fixed_report):
    assert json.loads(json.dumps(fixed_report)) == fixed_report
    flags = fixed_report["scope_flags"]
    assert flags["bounded_return_search"]
    assert not any(flags[key] for key in (
        "generic_orbit_search", "escape_proved", "no_cycle_proved", "raised_floor",
        "finite_tests_prove_uniform_theorem"))


def test_report_and_default_cli_are_read_only_write_is_explicit(tmp_path, monkeypatch, capsys):
    data_root = tmp_path / "data"
    monkeypatch.setattr(probe, "DATA_ROOT", data_root)
    report = probe.report()
    assert not data_root.exists()
    probe.main([])
    status = json.loads(capsys.readouterr().out)
    assert status["record_written"] is False and not data_root.exists()
    probe.main(["--write"])
    status = json.loads(capsys.readouterr().out)
    assert status["record_written"] is True
    written = data_root / "ooe_escape_families" / "controls.json"
    assert json.loads(written.read_text(encoding="utf-8")) == report


def test_sparse_invariant_paired_seed_failures():
    """Two prior seeds leave the template and fail the next OOE guard."""
    report = json.loads((DATA_ROOT / "ooe_escape_families" /
                         "sparse_invariant_controls.json").read_text(encoding="utf-8"))["paired"]
    assert report["parameter"] == 19999
    assert report["seeds"] == [1599840003, 1599840005]
    assert report["maximum_prescribed_blocks"] == 8
    controls = report["controls"]
    assert len(controls) == 2
    expected_returns = [22624871477, 22624871509]
    expected_next_O = [3403135028556724, 3403135035776676]
    returned = []
    for index, row in enumerate(controls):
        assert row["seed"] == report["seeds"][index]
        assert row["valid_blocks"] == 1
        assert row["cap_reached"] is False
        assert len(row["blocks"]) == 2
        first, failed = row["blocks"]
        assert [first["block_index"], failed["block_index"]] == [0, 1]
        assert first["full_repeated_OOE_guard"] is True
        assert first["first_failed_guard"] is None
        assert first["actual_prefix_edges"] == 3
        assert first["parities"] == [1, 1, 0, 1]
        assert first["phase_box_epsilon_three_quarters"] is True
        x, u, v, z = first["prescribed_states"]
        assert x == 4*19999**2 + (-1 if index == 0 else 1)
        assert z == expected_returns[index]
        returned.append(z)
        # This verifies the fixed rational phase box without floating point.
        assert v*v < u**3 and 16*u**3 < (4*v+3)**2
        assert z**4 < u**3 and 256*u**3 < (4*z+3)**4
        assert first["source_template"]["member"] is True
        assert first["source_template"]["representations"] == [
            {"t": 19999, "sign": -1 if index == 0 else 1}]
        assert z % 32 == first["return_template"]["residue_mod_32"] == 21
        # Every odd t has t²=1 mod8, so 4t²±1 is 3 or5 mod32.
        assert z % 32 not in (3, 5)
        assert first["return_template"]["member"] is False
        assert first["return_template"]["representations"] == []
        assert failed["prescribed_states"][0] == z
        assert failed["prescribed_states"][1] == expected_next_O[index]
        assert expected_next_O[index] % 2 == 0
        assert failed["full_repeated_OOE_guard"] is False
        assert failed["first_failed_guard"] == "second_O_requires_odd_u"
        assert failed["actual_prefix_edges"] == 1
        for block in row["blocks"]:
            a, b, c, d = block["prescribed_states"]
            assert block["parities"] == [n % 2 for n in (a, b, c, d)]
            radicands, roots = (a**3, b**3, c), (b, c, d)
            for radicand, root in zip(radicands, roots):
                assert root*root <= radicand < (root+1)**2
            assert block["residuals"] == [n-r*r for n, r in zip(radicands, roots)]
            assert block["upper_margins"] == [(r+1)**2-n for n, r in zip(radicands, roots)]
            assert all(margin > 0 for margin in block["upper_margins"])
        # Only the first edge of the failed prescribed block is an actual edge.
        assert failed["parities"][0:2] == [1, 0]
    gap = returned[1]-returned[0]
    assert gap == 32 and gap > 2
    assert gap*gap < 64*returned[0]


def test_sparse_invariant_inverse_cells():
    """Replay fixed exact cells, not a search or an infinitude test."""
    import json
    from math import isqrt

    data = json.loads((DATA_ROOT / "ooe_escape_families" /
                       "sparse_invariant_controls.json").read_text(encoding="utf-8"))["inverse"]

    def ceiling_cube(n):
        lo, hi = 0, 1 << ((n.bit_length() + 2) // 3)
        while lo < hi:
            mid = (lo + hi) // 2
            if mid**3 < n:
                lo = mid + 1
            else:
                hi = mid
        assert (lo == 0 or (lo - 1)**3 < n) and n <= lo**3
        return lo

    def threshold(y):
        return ceiling_cube(ceiling_cube(y**4)**2)

    expected = [[9, 11], [199, 385],
                [7939, 24391, 86225, 356933, 1764655, 10653499]]
    assert [row["known_return_trace"] for row in data["known_chain_controls"]] == expected
    for row in data["known_chain_controls"]:
        trace = row["known_return_trace"]
        assert len(row["actual_blocks"]) == len(trace) - 1
        for (x, h, p, y), source, target in zip(row["actual_blocks"], trace, trace[1:]):
            assert (x, y) == (source, target) and x < y
            assert [x % 2, h % 2, p % 2, y % 2] == [1, 1, 0, 1]
            assert h*h <= x**3 < (h + 1)**2
            assert p*p <= h**3 < (p + 1)**2
            assert y*y <= p < (y + 1)**2
            assert (threshold(y), threshold(y + 1)) == (x, x + 1)
        lo, hi = trace[-1], trace[-1] + 1
        for _ in range(len(trace) - 1):
            lo, hi = threshold(lo), threshold(hi)
        assert [lo, hi] == row["terminal_inverse_interval"] == [trace[0], trace[0] + 1]

    assert data["last_known_chain_next_O_guard_fails"]
    assert isqrt(expected[-1][-1]**3) == 34772699236
    assert 34772699236 % 2 == 0
    assert data["empty_prescribed_target"] == {"target": 9, "inverse_interval": [8, 8]}
    assert threshold(9) == threshold(10) == 8
    hole = data["guard_hole"]
    x, y = hole["source"], hole["target"]
    assert (x, y) == (3**8, 3**9)
    assert [threshold(y), threshold(y + 1)] == hole["prescribed_inverse_interval"] == [x, x + 1]
    assert isqrt(isqrt(x**3)**3) == 3**18
    assert hole["second_O_output_odd"] and 3**18 % 2 == 1
    for row in data["abstract_nested_residue_controls"]:
        n, modulus, representative = row["depth"], row["modulus"], row["representative"]
        assert n in (1, 2, 5) and modulus == 4**n
        assert 3*representative + 1 == modulus and representative > 0 and representative % 2 == 1
        assert ((4**(n + 1) - 1)//3 - representative) % modulus == 0
    assert data["scope"] == {
        "fixed_known_chains_only": True, "new_seed_search": False,
        "infinite_actual_chain_constructed": False,
        "profinite_control_is_not_an_actual_cell_model": True,
        "finite_controls_prove_infinitude": False,
    }
