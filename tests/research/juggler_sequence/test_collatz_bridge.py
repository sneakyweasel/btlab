"""The Juggler/Collatz bridge: verified both ways, and the audit it forces."""

from __future__ import annotations

import json
import math

import pytest

from research.juggler_sequence.collatz_bridge import (
    CLASS_BRIDGE,
    JSON_PATH,
    STEP_EVEN,
    STEP_ODD,
    big_log,
    collatz,
    collatz_reachable,
    juggler,
    loglog_increments,
    parity_map_is_bijective,
    parity_word,
    probe_payload,
    undecided_classes,
)
from research.juggler_sequence.jump_spectrum import survivor_counts


def test_the_two_walks_have_the_same_steps() -> None:
    """`log(3/2)` and `-log 2`, on `log x` for Collatz and `log log n` for Juggler."""
    assert STEP_ODD == pytest.approx(math.log(1.5), abs=1e-15)
    assert STEP_EVEN == pytest.approx(-math.log(2.0), abs=1e-15)
    # the drift is the same too, which is why both have the same survival rate
    assert 0.5 * (STEP_ODD + STEP_EVEN) == pytest.approx(0.5 * math.log(0.75), abs=1e-15)


def test_juggler_increments_hit_those_steps_from_a_large_seed() -> None:
    """The floor costs `O(1)` in `n`, so the agreement is only as good as `n` is large.

    At `n = 7` the error is a percent; from twenty-one digits it is at the last bit.
    Asserting both keeps the size condition visible instead of implied.
    """
    small = loglog_increments(7, steps=2, floor=3)
    assert small and max(abs(m - t) for _, m, t in small) > 1e-3

    large = loglog_increments(10**20 + 1, steps=2)
    assert len(large) == 2
    assert max(abs(m - t) for _, m, t in large) < 1e-14


def test_big_log_survives_values_past_the_float_range() -> None:
    """Juggler values are doubly exponential, so `float(n)` is not an option.

    A seed can still descend -- `10^20 + 1` reaches eight digits in three steps -- so
    the guard is tested on a value chosen to be large rather than on an orbit.
    """
    n = 10**400
    with pytest.raises(OverflowError):
        float(n)
    assert big_log(n) == pytest.approx(400 * math.log(10), rel=1e-12)
    assert big_log(7) == pytest.approx(math.log(7), rel=1e-15)


def test_the_parity_map_is_bijective_which_juggler_has_no_analogue_of() -> None:
    """Terras. This is the asymmetry: Collatz's word statistics are free, Juggler's
    are Hypothesis FD."""
    for depth in (4, 6, 8):
        assert parity_map_is_bijective(depth), depth
    assert parity_word(1, 4) == (1, 0, 1, 0)   # 1 -> 2 -> 1 -> 2
    assert collatz(7) == 11 and collatz(8) == 4


def test_the_survivor_count_is_the_undecided_collatz_class_count() -> None:
    """Checked by running Collatz, not by quoting OEIS.

    A class whose word has already dropped gives every member the same stopping time;
    a class whose word never drops does not. The second kind is counted by `N_d`.
    """
    counts = survivor_counts(10)
    for depth in range(4, 11):
        assert undecided_classes(depth) == counts[depth], depth
    assert [counts[d] for d in range(4, 11)] == [3, 4, 8, 13, 19, 38, 64]


def test_the_audit_separates_shared_results_from_juggler_ones() -> None:
    """Results that use only word densities belong to Collatz too.

    This is the uncomfortable half of the identification and the reason it is recorded:
    a Juggler-shaped wording does not make a claim Juggler-specific.
    """
    assert collatz_reachable("the survivor count recursion N_(d+1) + M_(d+1) = 2 N_d")
    assert collatz_reachable("the jump spectrum amplitude a_1")
    assert collatz_reachable("the certificate word count at each barrier")
    assert not collatz_reachable("Hypothesis FD gives equidistribution of parity words")
    assert not collatz_reachable("the Weyl differencing kernel bound")


def test_committed_artifact_records_the_bridge_and_its_limits() -> None:
    data = json.loads(JSON_PATH.read_text(encoding="utf-8"))
    assert data["decision"]["classification"] == CLASS_BRIDGE
    assert data["shared_count"]["agree"] is True
    assert data["shared_walk"]["worst_increment_error"] < 1e-8
    text = data["anti_overclaim"]
    assert "not an equivalence and not a conjugacy" in text
    assert "moves no bound in either problem" in text
    assert "not an easier Collatz" in text


def test_a_cheap_run_reaches_the_same_answer() -> None:
    payload = probe_payload(max_depth=7)
    assert payload["decision"]["classification"] == CLASS_BRIDGE
    assert payload["shared_count"]["agree"] is True
