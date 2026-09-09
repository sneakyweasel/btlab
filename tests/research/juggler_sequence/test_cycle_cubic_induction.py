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
