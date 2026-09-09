import json

import pytest

from research.juggler_sequence import cycle_periodic_carries as periodic
from research.juggler_sequence.lean_paths import DATA_ROOT


def test_exact_normalization_and_complete_return_towers():
    for b, cyclic in periodic.ABSOLUTE_CELL_THRESHOLD_CYCLES:
        row = periodic.periodic_record(b, cyclic)
        covered = []
        for block in row["returns"]:
            covered.extend(block["states"][:-1])
            for x, y, letter in zip(block["states"], block["states"][1:], block["word"]):
                rad = x**3 if letter == "O" else x
                assert y*y <= rad < (y+1)**2
        assert sorted(covered) == sorted(cyclic)
        assert sorted(r["endpoint"] for r in row["returns"]) == row["retained_bases"]
        assert all(n < row["q"] for n in row["retained_bases"])
        assert row["q"] not in row["retained_bases"]


def test_small_fixed_return_exceptions_and_mixed_partition_are_explicit():
    rows = [periodic.periodic_record(b, c) for b, c in periodic.ABSOLUTE_CELL_THRESHOLD_CYCLES]
    for row in rows[:2]:
        assert row["minimum"] in (3, 4)
        assert row["OOE_count"] == 1 and row["OE_count"] == 0
        assert row["seam"] is None
    for row in rows[2:]:
        assert row["OOE_count"] > 0 and row["OE_count"] > 0
        assert row["returns"][0]["word"] == "OOE"
        assert row["returns"][-1]["word"] == "OE"


def test_adjacent_return_seam_and_hypothesis_sensitive_integer_faces():
    for b, c in periodic.ABSOLUTE_CELL_THRESHOLD_CYCLES:
        row = periodic.periodic_record(b, c)
        seam = row["seam"]
        if seam is None:
            continue
        assert row["retained_bases"][row["OE_count"]-1:row["OE_count"]+1] == [seam["w"], seam["z"]]
        if seam["strong_seam_local_parity_hypotheses"]:
            assert row["t"]**3 <= seam["seam_cubic_radicand"]
    # The old S_9 cycle passes the new seam but still has wrong parities elsewhere.
    row = periodic.periodic_record(9, periodic.ABSOLUTE_CELL_THRESHOLD_CYCLES[2][1])
    assert row["seam"]["strong_seam_local_parity_hypotheses"]
    assert (row["t"], row["seam"]["z"], row["seam"]["w"]) == (19, 11, 9)
    assert row["maximum"] == 374 and row["parity_mismatches"] > 0
    assert not row["all_retained_bases_odd"]


def test_carry_sums_do_not_make_the_full_guard_automatic():
    rows = [periodic.periodic_record(b, c) for b, c in periodic.ABSOLUTE_CELL_THRESHOLD_CYCLES]
    assert [r["carry_sum"] for r in rows] == [2, 6, 53, 51, 649, 362, 361]
    assert [r["all_retained_bases_odd"] for r in rows] == [True, False, False, False, False, False, False]
    for row in rows:
        for block in row["returns"]:
            n = block["E_displacement"]
            assert (block["peak"]-block["endpoint"]**2) == n
            if row["all_retained_bases_odd"]:
                R = block["first_O_remainder"]
                valid = (R is None or R % 2 == 0) and n % 2 == 1
                assert valid == (block["parity_mismatches"] == 0)
        assert not row["actual_juggler_cycle"]


def test_conditional_ceilings_and_smooth_strip_use_only_exact_certificates():
    for m in periodic.CEILING_MINIMA:
        row = periodic.ceiling_record(m)
        z, T = row["odd_projected_return"], row["max_retained_odd_base"]
        assert z % 2 == T % 2 == 1
        assert z**8 <= m**9 < (z+2)**8
        assert T**3 <= row["seam_cubic_radicand"] < (T+2)**3
        cap = row["new_maximum_ceiling"]
        assert cap == (T+1)**2-2 < row["old_extrema_ceiling"]
        assert (m**3-cap)**8 > m**15
        assert row["periodicity"].startswith("not asserted")
    row = periodic.ceiling_record(9)
    assert row["new_maximum_ceiling"] == 482
    assert row["old_extrema_ceiling"] == 674


def test_integer_root_boundaries_and_domain_contract():
    for n in (0, 1, 2, 7, 8, 9, 26, 27, 28, 10**60-1, 10**60):
        c = periodic.cube_root_floor(n)
        assert c**3 <= n < (c+1)**3
    for m in (3, 5, 8, -1):
        with pytest.raises(ValueError):
            periodic.ceiling_record(m)


def test_archived_replay_does_not_search_or_expand_the_domain(monkeypatch):
    import research.juggler_sequence.cycle_cubic_band as cubic
    import research.juggler_sequence.cycle_cubic_induction as induction

    def forbidden(*args, **kwargs):
        raise AssertionError("periodic carry gate must not run a census")

    for name in ("all_small_cycles", "orbit_cycle", "rounding_cycle"):
        monkeypatch.setattr(cubic, name, forbidden)
    monkeypatch.setattr(induction, "source_controls", forbidden)
    data = periodic.report()
    assert data["scope"]["archived_threshold_cycles"] == 7
    assert data["scope"]["ceiling_evaluations"] == 5
    assert not data["universal_wrong_parity_proved"]
    assert not data["tall_cycles_excluded"] and not data["new_period_bound"]
    assert not data["no_cycle_proved"]
    path = DATA_ROOT / "cycle_periodic_carries/summary.json"
    assert data == json.loads(path.read_text(encoding="utf-8"))
