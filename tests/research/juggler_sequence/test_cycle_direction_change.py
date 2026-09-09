"""Bounded independent trace, seam, and ceiling checks for the new written result."""
import json
from fractions import Fraction

import pytest

from research.juggler_sequence import cycle_direction_change as direction


@pytest.fixture(scope="module")
def data():
    return direction.report()


def test_archived_report_matches_recomputed_controls(data):
    archived = direction.DATA_ROOT / "cycle_direction_change/summary.json"
    assert json.loads(archived.read_text(encoding="utf-8")) == data


def test_every_stage_partitions_the_original_cells_and_mismatches(data):
    for row in data["archived_cycles"]:
        expected = row["original_cells"]
        for stage in row["stages"]:
            cells = [cell for tower in stage["towers"] for cell in tower["cells"]]
            assert sorted(cells, key=lambda cell: cell["source"]) == expected
            assert len({cell["source"] for cell in cells}) == row["period"]
            assert sorted(cell["source"] for cell in cells if cell["wrong_parity"]) == row["wrong_parity_sources"]
            for tower in stage["towers"]:
                retained = set(stage["retained_bases"])
                assert tower["states"][0] in retained and tower["states"][-1] in retained
                assert not retained.intersection(tower["states"][1:-1])
                for cell in tower["cells"]:
                    radicand = cell["source"]**(3 if cell["branch"] == "O" else 1)
                    y = cell["image"]
                    assert y*y <= radicand < (y+1)**2
                    assert cell["square_remainder"] == radicand-y*y
                    assert cell["wrong_parity"] == (bool(cell["source"] % 2) != (cell["branch"] == "O"))
        assert row["wrong_parity_sources"] and not row["actual_juggler_cycle"]


def test_left_recycles_right_transports_and_terminal_removes_upper_endpoint(data):
    directions = set()
    for row in data["archived_cycles"]:
        for transition in row["transitions"]:
            kind = transition["direction"]
            directions.add(kind)
            old, new = transition["old_seam"], transition["new_seam"]
            if kind == "left":
                assert old == new and transition["same_two_values"]
            elif kind == "right":
                pairs = transition["adjacent_intermediate_pairs"]
                assert pairs[0] == [old["w"], old["z"]]
                assert pairs[-1] == [new["w"], new["z"]]
                ordered = sorted(cell["source"] for cell in row["original_cells"])
                for x, y in pairs:
                    assert ordered.index(y) == ordered.index(x)+1
                for source_pair, image_pair, letter in zip(pairs, pairs[1:], transition["transfer_word"]):
                    for x, y in zip(source_pair, image_pair):
                        radicand = x**3 if letter == "O" else x
                        assert y*y <= radicand < (y+1)**2
            else:
                assert kind == "terminal" and new is None
                assert transition["upper_seam_point_removed"]
                assert not transition["extra_seam_transfer"]
        assert not row["terminal_extra_seam_edge"]
    assert directions == {"left", "right", "terminal"}


def test_singletons_are_excluded_and_small_controls_do_not_validate_large_minimum_claim(data):
    excluded = [row for row in data["archived_cycles"] if row["rank_induction_excluded"]]
    assert [row["minimum"] for row in excluded] == [3, 4]
    assert all(row["OE_count"] == 0 and not row["stages"] for row in excluded)
    for row in data["archived_cycles"]:
        assert not row["large_minimum_theorem_applies"]
        if not row["rank_induction_excluded"]:
            terminal = row["stages"][-1]
            assert len(terminal["retained_bases"]) == 1 and terminal["seam"] is None
            assert all(t["base"] == t["image"] for t in terminal["towers"])


def test_conditional_ceilings_have_exact_minimal_gap_and_maximal_odd_base(data):
    assert [row["minimum"] for row in data["conditional_ceilings"]] == list(direction.CEILING_MINIMA)
    for row in data["conditional_ceilings"]:
        m, G, z, T = (row[k] for k in ("minimum", "least_even_seam_gap", "odd_projected_return", "max_retained_odd_base"))
        assert G >= 6 and G % 2 == 0
        assert (59049*G)**128 > 26240**128*m**13
        assert G == 6 or (59049*(G-2))**128 <= 26240**128*m**13
        assert z % 2 == T % 2 == 1 and z**8 <= m**9 < (z+2)**8
        assert T**3+2 <= ((z-G)*(z-G+2))**2 < (T+2)**3+2
        cap = row["new_maximum_ceiling"]
        assert cap == (T+1)**2-2 < row["previous_periodic_ceiling"] < m**3
        assert (2*(m**3-cap))**128 > m**253
        assert row["periodicity"].startswith("not asserted")


def test_exact_constant_certificate_and_scope_labels(data):
    constants = data["constant_checks"]
    assert sum(map(Fraction, constants["dyadic_majorants"])) == Fraction(63121, 524288) < Fraction(1, 8)
    assert Fraction(constants["two_transfer_gap_coefficient"]) == Fraction(26240, 59049)
    assert Fraction(constants["height_strip_exponent"]) == Fraction(253, 128)
    assert data["proof_status"].startswith("written mathematical proof")
    for key in ("new_theorem_formalized_in_lean", "uniform_gap_propagation_proved",
                "universal_wrong_parity_proved", "tall_cycles_excluded", "new_period_bound", "no_cycle_proved"):
        assert not data[key]


def test_only_archived_rank_pairs_and_two_declared_minima_are_evaluated(monkeypatch):
    import research.juggler_sequence.cycle_cubic_band as cubic
    import research.juggler_sequence.cycle_cubic_induction as induction

    def forbidden(*args, **kwargs):
        raise AssertionError("direction-change controls must not run a census or search")
    for name in ("all_small_cycles", "orbit_cycle", "rounding_cycle"):
        monkeypatch.setattr(cubic, name, forbidden)
    monkeypatch.setattr(induction, "source_controls", forbidden)
    monkeypatch.setattr(induction, "report", forbidden)
    calls = []
    original = direction.rank_induction
    def bounded_induction(a, b):
        calls.append((a, b))
        return original(a, b)
    monkeypatch.setattr(direction, "rank_induction", bounded_induction)
    got = direction.report()
    assert calls == [(3, 1), (3, 1), (5, 2), (5, 2), (5, 2)]
    assert got["scope"]["ceiling_minima"] == [214358889, 10828567056280809]
    for key in ("cycle_search", "source_census", "rank_pair_scan", "trajectory_extension", "descent_floor_increase"):
        assert not got["scope"][key]


def test_domain_checks_and_explicit_output_path(tmp_path, capsys, data):
    for m in (3, 2**24-1, 2**24, -1):
        with pytest.raises(ValueError):
            direction.ceiling_record(m)
    with pytest.raises(ValueError):
        direction.least_even_seam_gap(2**24-1)
    with pytest.raises(ValueError):
        direction.exact_cells([3, 5], "OO")
    output = tmp_path / "direction-change.json"
    direction.main(["--output", str(output)])
    assert json.loads(output.read_text(encoding="utf-8")) == data
    assert not json.loads(capsys.readouterr().out)["no_cycle_proved"]
