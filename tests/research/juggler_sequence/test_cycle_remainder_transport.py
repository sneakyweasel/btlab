import json
from math import isqrt

import pytest

from research.juggler_sequence import cycle_remainder_transport as transport
from research.juggler_sequence.cycle_cubic_induction import trace_word, parity_guard
from research.juggler_sequence.lean_paths import DATA_ROOT


def valuation(n, p):
    assert n > 0
    a = 0
    while n % p == 0:
        a += 1
        n //= p
    return a


def test_corrected_quotient_and_recovered_cells_are_exact():
    for x in list(range(3, 129))+[r**8+8 for r in transport.PARAMETERS]:
        got = transport.corrected_record(x)
        u, v, z, R = got["actual_u"], got["actual_v"], got["z"], got["R"]
        assert u*u+R == x**3 and 0 <= R <= 2*u
        assert z**8 <= (x**3-R)**3 < (z+1)**8
        assert got["true_quotient"]-got["q"] in (0, 1)
        assert got["recovered_v"] == v
        assert v**4 <= (x**3-R)**3 < (v+1)**4
        assert 0 <= got["kappa"] <= 3
        # Directly certify the radical numerator used by the corrected floor.
        k = got["K"]
        root = isqrt(k*k*x**3)
        assert root*root <= k*k*x**3 < (root+1)**2
        assert got["q"] == (root-2*z**4)//(4*z*z)


def test_candidate_endpoint_validation_precedes_hidden_guard():
    x = 5
    R = x**3-isqrt(x**3)**2
    # The odd projected candidate is5, while the actual OOE endpoint is6.
    with pytest.raises(ValueError, match="endpoint"):
        transport.corrected_suffix(x, R, 5)
    actual = transport.corrected_suffix(x, R, 6)
    assert not actual["odd_endpoint_ooe_guard"]
    for x in list(range(3, 129, 2))+[201, 263]:
        states = trace_word(x, "OOEOE")
        R = x**3-isqrt(x**3)**2
        expected = parity_guard(states, "OOEOE") and bool(states[-1] % 2)
        assert transport.guard_ooeoe(x, states[-1], R) == expected
    assert transport.guard_ooeoe(263, 109, 263**3-4265**2)
    assert not transport.guard_ooeoe(263, 111, 263**3-4265**2)


def test_all_six_literal_fates_have_independent_square_certificates():
    data = json.loads((DATA_ROOT / "cycle_remainder_transport/summary.json").read_text(encoding="utf-8"))
    assert [r["steps_recorded"] for r in data["family_fates"]] == [28, 13, 64, 24, 60, 54]
    assert [r["maximum_decimal_digits"] for r in data["family_fates"]] == [111, 13, 129, 41, 468, 1480]
    for row in data["family_fates"]:
        states = [int(n, 16) for n in row["states_hex"]]
        assert states[0] == row["r"]**8+8
        assert states[-1] == 1 and 1 not in states[:-1]
        for x, y in zip(states, states[1:]):
            radicand = x**3 if x % 2 else x
            assert y*y <= radicand < (y+1)**2
        assert row["status"] == "reached_one"
        assert max(states).bit_length() == row["maximum_bits"]
        assert row["immediate_reentry_excluded_by_mod48"]
        assert row["r"] % 3 != 1
        assert not row["terminal_ooe_reenters_family"]


def test_caps_are_reported_as_unresolved_not_as_escape(monkeypatch):
    monkeypatch.setattr(transport, "MAX_STEPS", 3)
    row = transport.exact_family_trace(5)
    assert row["status"] == "step_cap" and row["steps_recorded"] == 3
    assert row["first_below_start_step"] is None
    monkeypatch.setattr(transport, "MAX_STEPS", 500)
    monkeypatch.setattr(transport, "MAX_BITS", 20)
    row = transport.exact_family_trace(3)
    assert row["status"] == "bit_cap" and row["steps_recorded"] == 1
    assert row["next_step"] == 2 and row["next_value_bits"] == 29


def test_family_factorizations_and_chain_bound_do_not_assert_returns_exist():
    for a in range(4, 13):
        r = 1+2**a
        Q = sum(r**j for j in range(1, 9))+10
        assert r**9+9*r-10 == (r-1)*Q
        assert valuation(Q, 2) == 1
        assert valuation(r**9+9*r-10, 2) == a+1
        assert transport.family_chain_bound(r) == (a-2)//2
    for s in (17, 33, 49, 65, 97):
        assert valuation(s**8-1, 2) == valuation(s-1, 2)+3
    for r in range(3, 130, 2):
        F = r**9+9*r-9
        if r % 3 == 0:
            assert valuation(F, 3) == 2
        elif r % 3 == 2:
            assert F % 3 == 2
        if r % 16 != 1:
            assert F % 32 != 1
    assert [transport.family_chain_bound(r) for r in (3, 5, 9, 17, 65)] == [0, 0, 0, 1, 2]


def test_archived_scope_replays_without_any_source_or_cycle_census(monkeypatch):
    import research.juggler_sequence.cycle_cubic_band as cubic
    import research.juggler_sequence.cycle_cubic_induction as induction

    def forbidden(*args, **kwargs):
        raise AssertionError("the remainder gate must not run a census")

    for name in ("all_small_cycles", "orbit_cycle", "rounding_cycle"):
        monkeypatch.setattr(cubic, name, forbidden)
    monkeypatch.setattr(induction, "source_controls", forbidden)
    got = transport.report()
    assert got["scope"]["repair_instances"] == 132
    assert got["scope"]["ooeoe_guard_instances"] == 65
    assert got["scope"]["max_steps"] == 500
    assert got["scope"]["max_state_bits"] == 16384
    assert not got["scope"]["caps_enlarged"]
    assert not got["universal_family_termination_proved"]
    assert not got["escaping_orbit_proved"]
    assert not got["uniform_word_guard_closure_proved"]
    archive = DATA_ROOT / "cycle_remainder_transport/summary.json"
    assert got == json.loads(archive.read_text(encoding="utf-8"))
