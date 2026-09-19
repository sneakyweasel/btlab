"""The Lemma 8 floor on the negative side: sign-symmetric, tight, and slack at the leftovers.

The bridge makes a negative Collatz cycle word a Paper A CycleMin word letter for letter, so the
negative side is where the Juggler's missing pointwise floor can be priced. These tests pin the
floor, its tightness at every known cycle of the Z map, the window against `neg_cycle_finance`,
and the run bound that goes slack exactly at the record near-convergent lengths.
"""

from __future__ import annotations

import json
import math
from fractions import Fraction

import pytest

from research.juggler_sequence.negative_lemma_eight_window import (
    CLASS_WINDOW,
    JSON_PATH,
    PAPER_A_EVEN_FLOOR,
    cycle_from,
    even_charge,
    known_cycles,
    leading_odd_run,
    leftover_slack,
    first_admissible_length,
    shape_words,
    shortcut,
    sieve,
    v2,
    window,
    word_of,
)


def odd_run_from(x: int) -> int:
    run = 0
    while x % 2 != 0:
        run += 1
        x = shortcut(x)
    return run


def test_the_congruence_holds_on_both_signs() -> None:
    """`a` consecutive odd states force `x = -1 mod 2^a`, over Z."""
    for x in list(range(1, 4000, 2)) + list(range(-4001, -1, 2)):
        a = odd_run_from(x)
        assert (x + 1) % 2**a == 0


def test_the_negative_floor_is_two_units_the_other_way() -> None:
    """`x >= 2^a - 1` on the positive side, `x <= -(2^a + 1)` on the negative."""
    for x in range(1, 4000, 2):
        assert x >= 2 ** odd_run_from(x) - 1
    for x in range(-4001, -2, 2):
        assert x <= -(2 ** odd_run_from(x) + 1)


def test_every_known_cycle_sits_on_its_floor() -> None:
    data = known_cycles()
    assert data["all_attain"]
    assert data["all_odd_parts_are_the_gap"]
    rows = {row["x"]: row for row in data["rows"]}
    assert rows[1]["floor"] == 1 and rows[1]["leading_odd_run"] == 1
    assert rows[-5]["floor"] == 5 and rows[-5]["u"] == -4
    assert rows[-17]["floor"] == 17 and rows[-17]["u"] == -16
    assert rows[-5]["u_is_minus_a_power_of_two"]
    assert rows[-17]["u_is_minus_a_power_of_two"]
    # -1 is the degenerate case the hypothesis x <= -2 excludes
    assert not rows[-1]["attains_floor"] and rows[-1]["u"] == 0


def test_the_ooe_window_pins_minus_five() -> None:
    """Floor 5, ceiling 11/2: the only integer in the window is 5."""
    floor, ceiling = window("OOE", 2, 3)
    assert floor == 5
    assert ceiling == Fraction(11, 2)
    assert [n for n in range(1, 40) if floor <= n <= ceiling] == [5]


def test_neither_known_cycle_word_is_excluded() -> None:
    """The falsifier that mattered: a sieve that kills a real cycle is wrong."""
    for word, odds, length in (("OOE", 2, 3), ("OOOOEOOOEEE", 7, 11)):
        floor, ceiling = window(word, odds, length)
        assert floor <= ceiling


def test_the_sieve_is_strong_on_short_words() -> None:
    data = sieve(max_len=14)
    assert data["excluded_share"] > 0.5
    assert 13 in data["empty_lengths"]
    assert 3 not in data["empty_lengths"] and 11 not in data["empty_lengths"]
    assert data["paper_a_even_floor"] == PAPER_A_EVEN_FLOOR
    # below length 22 every shape word already fails e >= 8, so the window adds nothing there
    assert data["window_only"] == 0


def test_paper_a_forces_length_twenty_two_so_the_comparison_starts_there() -> None:
    """`e >= 8` with `3^o > 2^K` forces `o >= 14`, hence `K >= 22`."""
    assert first_admissible_length(14)["paper_a_forces_length_at_least"] == 22
    assert first_admissible_length(14)["paper_a_admissible"] == 0
    for word, odds, length in shape_words(21):
        assert length - odds < PAPER_A_EVEN_FLOOR


def test_emptiness_is_the_run_bound() -> None:
    """An empty window is `2^(a+1) theta_J > e`, i.e. `a <= log2(e/theta_J) - 1`."""
    for word, odds, length in shape_words(12):
        evens = length - odds
        theta = 1 - Fraction(2**length, 3**odds)
        floor, ceiling = window(word, odds, length)
        empty = floor > ceiling
        assert empty == (2 ** (leading_odd_run(word) + 1) * theta > evens)
        if not empty:
            assert leading_odd_run(word) <= math.log2(evens / float(theta)) - 1


def test_the_bound_goes_slack_at_the_leftovers() -> None:
    rows = {row["length"]: row for row in leftover_slack()["rows"]}
    assert rows[3]["run_bound"] < rows[11]["run_bound"] < rows[19]["run_bound"]
    assert rows[19]["run_bound"] < rows[84]["run_bound"] < rows[1054]["run_bound"]
    assert rows[3]["run_bound"] < 3 and rows[1054]["run_bound"] > 22
    assert rows[1054]["theta_J"] < rows[3]["theta_J"]


def test_even_charge_matches_the_cycle_equation() -> None:
    """`(x+1)(2^K - 3^o) = evenCharge(w)` on both negative cycles."""
    for start in (-5, -17):
        cycle = cycle_from(start)
        assert cycle is not None
        least = max(cycle)
        rotation = cycle[cycle.index(least) :] + cycle[: cycle.index(least)]
        w = word_of(rotation)
        odds = w.count("O")
        assert (least + 1) * (2 ** len(w) - 3**odds) == even_charge(w)
        assert v2(even_charge(w)) == leading_odd_run(w)


@pytest.mark.skipif(not JSON_PATH.exists(), reason="probe artifact not built")
def test_committed_artifact_is_green() -> None:
    data = json.loads(JSON_PATH.read_text(encoding="utf-8"))
    assert data["decision"]["classification"] == CLASS_WINDOW
    assert data["decision"]["branch"] == "CLOSE"
    assert data["known_cycles"]["all_attain"]
    assert data["sieve"]["not_subsumed"]
    assert data["sieve"]["empty_lengths"] == [1, 2, 4, 5, 7, 8, 10, 13, 16]
    first = data["first_admissible_length"]
    assert first["length"] == 22 and first["paper_a_forces_length_at_least"] == 22
    assert first["window_kills"] == 4787 and first["paper_a_admissible"] == 17637
    assert first["least_run_killed"] == 6 and first["greatest_run_surviving"] == 5
