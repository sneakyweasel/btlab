import json

import pytest

from research.juggler_sequence import cycle_guard_residues as residues
from research.juggler_sequence.lean_paths import DATA_ROOT


def test_closed_form_cells_and_opposite_hidden_guards():
    for Q in residues.MODULI:
        pair = residues.closed_form_pair(Q)
        assert pair["b"] % 4 == 3
        assert pair["b"]**2 > 504*(Q-1)**5
        assert [r["guard_valid"] for r in pair["blocks"]] == [False, True]
        for row in pair["blocks"]:
            x, u, v, z = row["states"]
            assert x**3 == u*u
            assert v*v <= u**3 < (v+1)**2
            assert z*z <= v < (z+1)**2
            assert x % 2 == u % 2 == z % 2 == 1
            assert (v % 2 == 0) == row["guard_valid"]


def test_same_record_including_exact_first_remainder_and_aggregate_valuation():
    for Q in residues.MODULI:
        pair = residues.closed_form_pair(Q)
        p, m = pair["blocks"]
        assert p["R_first"] == m["R_first"] == 0
        assert p["aggregate_v2"] == m["aggregate_v2"] == 3
        for index in (0, 1, 3):
            assert (p["states"][index]-m["states"][index]) % Q == 0
        assert (p["aggregate"]-m["aggregate"]) % Q == 0
        assert p["states"][0] != m["states"][0]
        assert p["states"][-1] != m["states"][-1]
    # One common even multiple simultaneously covers nonbinary moduli.
    pair = residues.closed_form_pair(210)
    p, m = pair["blocks"]
    for modulus in (2, 3, 5, 7, 10, 15, 21, 35):
        assert (p["states"][0]-m["states"][0]) % modulus == 0
        assert (p["states"][-1]-m["states"][-1]) % modulus == 0
        assert (p["aggregate"]-m["aggregate"]) % modulus == 0


def test_both_are_first_returns_in_the_same_absolute_threshold_section():
    for Q in residues.MODULI:
        pair = residues.closed_form_pair(Q)
        B, cut = pair["threshold"], pair["section_upper_exclusive"]
        for row in pair["blocks"]:
            x, u, v, z = row["states"]
            assert B <= x < cut and B <= z < cut
            assert cut <= u < B*B <= v < B**3
        assert pair["both_periodic"] == "not asserted"


def test_existing_absolute_quotient_repair_distinguishes_the_pair():
    from research.juggler_sequence.cycle_remainder_transport import corrected_record

    for Q in residues.MODULI:
        for row in residues.closed_form_pair(Q)["blocks"]:
            x, u, v, z = row["states"]
            recovered = corrected_record(x)
            assert recovered["R"] == 0
            assert recovered["recovered_v"] == v
            assert recovered["odd_endpoint_ooe_guard"] == row["guard_valid"]


def test_dyadic_collapse_and_mismatch_energy_on_only_archived_cycles():
    rows = residues.archived_cycle_controls()
    assert len(rows) == 7
    for row in rows:
        assert row["odd_fixed_point_aggregate_v2"] == row["minimum_minus_one_v2"]
        assert (row["odd_fixed_point_aggregate_v2"] is not None) == row["odd_minimum"]
        assert row["parity_mismatches"] > 0
        assert row["mismatch_transitions"] % 2 == 0
        assert not row["actual_juggler_cycle"]


def test_invalid_moduli_and_zero_valuation_are_rejected():
    for Q in (0, 1, 3, -2):
        with pytest.raises(ValueError):
            residues.closed_form_pair(Q)
    for n in (0, -1):
        with pytest.raises(ValueError):
            residues.v2(n)


def test_archive_scope_replays_without_a_census(monkeypatch):
    import research.juggler_sequence.cycle_cubic_band as cubic
    import research.juggler_sequence.cycle_cubic_induction as induction

    def forbidden(*args, **kwargs):
        raise AssertionError("this gate must not run a census")

    for name in ("all_small_cycles", "orbit_cycle", "rounding_cycle"):
        monkeypatch.setattr(cubic, name, forbidden)
    monkeypatch.setattr(induction, "source_controls", forbidden)
    data = residues.report()
    assert data["scope"]["closed_form_blocks"] == 12
    assert not data["full_absolute_remainder_closure_refuted"]
    assert not data["periodic_point_guard_closure_refuted"]
    assert not data["no_cycle_proved"]
    archived = DATA_ROOT / "cycle_guard_residues/summary.json"
    assert data == json.loads(archived.read_text(encoding="utf-8"))
