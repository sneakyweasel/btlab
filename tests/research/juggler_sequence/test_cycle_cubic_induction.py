"""Independent cell and first-return checks for the bounded induction gate."""
import json
from math import isqrt

from research.juggler_sequence.cycle_cubic_induction import (
    WORDS, parity_guard, rank_induction, report, trace_word,
)
from research.juggler_sequence.lean_paths import DATA_ROOT


def test_oe_and_ooe_cells_include_perfect_power_boundaries():
    for x in range(1, 1025):
        oe = trace_word(x, "OE")[-1]
        assert oe**4 <= x**3 < (oe+1)**4
        ooe = trace_word(x, "OOE")[-1]
        # Exact version of floor(x^(9/8))-OOE(x) in {0,1}.
        assert ooe**8 <= x**9 < (ooe+2)**8
    # The one-integer allowance is actually needed, on a parity-valid block.
    states = trace_word(201, "OOE")
    assert states == [201, 2849, 152068, 389]
    assert parity_guard(states, "OOE")
    assert 390**8 <= 201**9 < 391**8


def test_ooeoe_odd_endpoint_projection_without_assuming_internal_parity():
    for x in range(3, 1025):
        y = trace_word(x, "OOEOE")[-1]
        if y % 2:
            assert y**32 <= x**27 < (y+2)**32


def test_endpoint_parity_does_not_transport_the_hidden_guard():
    for s in (3, 5, 101, 10**20+1):
        b, x = s**3, s**4
        states = trace_word(x, "OE")
        assert states == [x, b*b, b]
        assert b <= x < b*b < b**3
        assert all(v % 2 for v in states)
        assert not parity_guard(states, "OE")
        assert isqrt(states[1]**3) == s**9 != b
        assert b**4 <= x**3 < (b+1)**4


def test_terminal_towers_keep_original_length_and_nonprimitive_cycles():
    for a, b, terminal_word, towers in ((2, 1, "OOE", 1),
                                      (7, 4, "OOEOOEOOEOE", 1),
                                      (4, 2, "OOE", 2),
                                      (2, 5, "OEEOEEE", 1)):
        stages = rank_induction(a, b)
        end = stages[-1]
        assert len(end["towers"]) == towers
        assert all(t["word"] == terminal_word for t in end["towers"])
        assert all(t["image"] == t["base"] for t in end["towers"])
        assert sum(len(t["ranks"]) for t in end["towers"]) == a+b


def test_exact_report_replays_only_declared_scope_and_existing_cycles(monkeypatch):
    import research.juggler_sequence.cycle_cubic_band as cubic

    def forbidden(*args, **kwargs):
        raise AssertionError("induction control must not run a cycle search")

    for name in ("all_small_cycles", "orbit_cycle", "rounding_cycle"):
        monkeypatch.setattr(cubic, name, forbidden)
    data = report()
    assert data["scope"]["odd_source_range"] == [3, 65535]
    assert data["scope"]["rank_pairs"] == 1024
    assert [r["word"] for r in data["sources"]] == list(WORDS)
    assert [r["parity_valid_odd_endpoints"] for r in data["sources"]] == [16379, 8181, 4125, 1002, 152, 14, 0]
    assert all(r["also_cubic_height"] == r["parity_valid_odd_endpoints"] for r in data["sources"])
    assert all(not r["projection_failures"] for r in data["sources"])
    assert len(data["archived_cycles"]) == 7
    assert all(r["parity_mismatches_at_every_stage"] > 0 for r in data["archived_cycles"])
    assert not data["uniform_endpoint_closure_proved"]
    assert not data["uniform_parity_closure_proved"]
    assert not data["no_cycle_proved"]
    assert data == json.loads((DATA_ROOT / "cycle_cubic_induction/controls.json").read_text(encoding="utf-8"))


def test_square_cell_normal_form_has_three_sharp_corrections():
    from research.juggler_sequence.cycle_cubic_induction import square_cell_carry
    import pytest
    # Independent true roots, including the fourth-power cell boundaries.
    for y in (1, 2, 3, 29, 10**20+1):
        for N in (y**4, y**4+1, (y+1)**4-2, (y+1)**4-1):
            got = square_cell_carry(N, y)
            u = isqrt(N)
            assert got["u"] == u and got["c"] == u-y*y
            assert 0 <= got["h"]-got["c"] <= 2
    got = square_cell_carry(93**3, 29)
    assert (got["d"], got["h"], got["c"], got["kappa"]) == (57, 57, 55, 2)
    for N, y in ((0, 0), (15, 2), (81, 2)):
        with pytest.raises(ValueError):
            square_cell_carry(N, y)


def test_valid_ooe_family_retains_cells_parity_and_exposes_unbounded_carry():
    from research.juggler_sequence.cycle_cubic_induction import valid_ooe_carry_family
    for r in (3, 5, 11, 101, 10**6+1, 10**20+1):
        row = valid_ooe_carry_family(r)
        x, u, v, z = row["states"]
        assert x**3-u*u == 48*r**8+512
        for a, y, exponent in ((x, u, 3), (u, v, 3), (v, z, 1)):
            assert y*y < a**exponent < (y+1)**2
        assert [n % 2 for n in row["states"]] == [1, 1, 0, 1]
        # Independent exact comparison of the real quotient delta against both bounds.
        denominator = 2*z*z
        low = u**3+36*r*r*denominator
        high = low+denominator
        assert low*low < x**9 < high*high
        assert row["clipped_offset_error"] == 27*r*r
        assert row["ordinary_power_endpoint"] == z+1
        assert not row["substitution_preserves_unit_endpoint_cell"]
        assert not row["closed_cycle"]


def test_guard_carry_report_reuses_only_the_declared_exact_controls(monkeypatch):
    import research.juggler_sequence.cycle_cubic_induction as induction
    import research.juggler_sequence.cycle_cubic_band as cubic

    def forbidden(*args, **kwargs):
        raise AssertionError("carry verification must not search or rerun a source census")

    for name in ("all_small_cycles", "orbit_cycle", "rounding_cycle"):
        monkeypatch.setattr(cubic, name, forbidden)
    monkeypatch.setattr(induction, "source_controls", forbidden)
    got = induction.guard_carry_report()
    assert got["normal_form_corrections_seen"] == [0, 1, 2]
    assert got["scope"]["square_cell_boundary_instances"] == 4351
    assert [r["sources_checked"] for r in got["cube_fiber_controls"]] == [3, 4, 8, 68]
    assert got["uniform_bounded_additive_substitution_refuted"]
    assert not got["general_arithmetic_parity_closure_refuted"]
    assert not got["no_cycle_proved"]
    archive = DATA_ROOT / "cycle_cubic_induction/guard_carries.json"
    assert got == json.loads(archive.read_text(encoding="utf-8"))
