"""The 3x-1 verification floor, and the period bound it makes unconditional.

The bridge makes a negative Collatz cycle word a Paper A CycleMin word letter for letter, and
neg_cycle_finance is kernel-checked, so a verification floor on the 3x-1 map converts directly into
a period bound. These tests pin the map, the three cycles, the descent rule against full iteration,
the committed certificate, and the bound the lab's own finance function returns at that floor.
"""

from __future__ import annotations

import json

import pytest

from research.juggler_sequence.negative_floor_3x1 import (
    CLASS_FLOOR,
    CYCLE_ELEMENTS,
    CYCLES,
    FLOOR_LOG2,
    JSON_PATH,
    certificate,
    descent_verify,
    period_bounds,
    reaches_known_cycle,
    reference_agrees,
    shortcut,
)


def test_the_three_cycles_are_cycles() -> None:
    for cycle in CYCLES:
        for i, y in enumerate(cycle):
            assert shortcut(y) == cycle[(i + 1) % len(cycle)], (cycle, y)
    assert shortcut(1) == 1
    assert len(CYCLE_ELEMENTS) == 15


def test_descent_and_full_iteration_agree() -> None:
    """The fast rule (stop below y) and the slow rule (iterate to a cycle) give the same verdict."""
    data = reference_agrees(limit=20_000)
    assert data["agree"]
    assert data["disagreements"] == []
    assert all(reaches_known_cycle(y) for y in range(3, 5000, 2))


def test_descent_verify_is_clean_on_a_small_window() -> None:
    data = descent_verify(3, 200_000)
    assert data["clean"]
    assert data["fails"] == [] and data["new_cycles"] == []
    assert data["max_steps"] < 4000


def test_descent_verify_reports_a_planted_cycle() -> None:
    """Sanity: the cycle branch fires on a known cycle element rather than silently passing."""
    data = descent_verify(5, 6)
    assert data["clean"]          # 5 is a known cycle element, so not reported as new
    assert data["new_cycles"] == []


def test_committed_certificate_covers_two_to_the_fortieth() -> None:
    cert = certificate()
    assert cert["clean"]
    assert cert["fails"] == 0 and cert["new_cycles"] == 0
    assert cert["covered_to"] == 2**FLOOR_LOG2
    assert cert["covered_to_is_two_pow"]
    assert cert["chunks"] == 16
    assert cert["odd_starts"] == 549_755_813_864
    assert cert["max_steps"] == 544
    assert cert["max_excursion"] < 2**127        # the __int128 state never came near overflow
    assert cert["max_excursion"] > 2**64         # but it did leave 64 bits, so the width mattered


def test_the_floor_buys_the_period_bound() -> None:
    rows = {r["floor"]: r for r in period_bounds(
        floors=((2**38, "2^38"), (10**11, "10^11"), (2**40, "2^40")))}
    assert rows["2^40"]["least_period"] == 9_538_065
    assert rows["2^40"]["odd_steps"] == 6_017_849
    assert rows["2^40"]["verified"]
    assert rows["2^38"]["least_period"] == 4_404_167
    assert rows["2^38"]["odd_steps"] == 2_778_720
    assert rows["10^11"]["least_period"] == 1_988_215
    # the bound is monotone in the floor: a higher floor forbids more lengths
    assert (rows["2^40"]["least_period"] > rows["2^38"]["least_period"]
            > rows["10^11"]["least_period"])


@pytest.mark.skipif(not JSON_PATH.exists(), reason="probe artifact not built")
def test_committed_artifact_is_green() -> None:
    data = json.loads(JSON_PATH.read_text(encoding="utf-8"))
    assert data["decision"]["classification"] == CLASS_FLOOR
    assert data["decision"]["branch"] == "PROMOTE"
    assert data["certificate"]["clean"]
    assert "9538065" in data["statement"]
