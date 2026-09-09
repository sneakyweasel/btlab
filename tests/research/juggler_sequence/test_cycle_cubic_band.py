"""Exact checks and negative controls for cubic-band order rigidity."""
import json
from itertools import permutations
from math import gcd

import pytest

from research.juggler_sequence.cycle_cubic_band import (
    all_small_cycles, branch_step, certify_cycle, counterexamples,
    orbit_cycle, threshold_step,
)
from research.juggler_sequence.lean_paths import DATA_ROOT


@pytest.mark.parametrize("b", [3, 4, 5, 9, 17, 30])
def test_invariant_interval_and_no_fixed_point(b):
    for x in range(b, b**3):
        y = threshold_step(x, b)
        assert b <= y < b**3 and y != x
        radicand = x**3 if x < b*b else x
        assert y*y <= radicand < (y+1)*(y+1)
    # Four points straddling the two branches, at scales far beyond floats.
    for big in [10**20+3, 10**80+7]:
        for x in [big, big*big-1, big*big, big**3-1]:
            y = threshold_step(x, big)
            assert big <= y < big**3 and y != x


def test_exact_complete_graph_controls():
    for b, expected_count, expected_period in [(3, 2, 3), (5, 1, 14), (9, 2, 11), (30, 4, 19)]:
        cycles = all_small_cycles(b)
        assert len(cycles) == expected_count
        for states, row in cycles.items():
            assert row["period"] == expected_period
            assert not row["juggler_cycle"]
            assert row["parity_mismatches"] > 0
            # Verify cells directly; do not reuse the root evaluator.
            for k, x in enumerate(states):
                y = states[(k+1) % len(states)]
                h = 3 if x < b*b else 1
                assert y*y <= x**h < (y+1)*(y+1)


def test_abstract_sorted_permutation_argument():
    # Exhaust all permutations through size 7, independently of threshold
    # dynamics. The separated increasing blocks must be the rank rotation.
    hits = 0
    for length in range(2, 8):
        for p in permutations(range(length)):
            for odd in range(1, length):
                lo, hi = p[:odd], p[odd:]
                if not (all(lo[i] < lo[i+1] for i in range(len(lo)-1))
                        and all(hi[i] < hi[i+1] for i in range(len(hi)-1))
                        and max(hi) < min(lo)):
                    continue
                even = length-odd
                assert p == tuple((i+even) % length for i in range(length))
                orbit, k = set(), 0
                while k not in orbit:
                    orbit.add(k)
                    k = p[k]
                assert len(orbit) == length // gcd(length, even)
                hits += 1
    assert hits == sum(length-1 for length in range(2, 8))


def test_parity_is_a_separate_requirement():
    narrow, tall = counterexamples()
    assert narrow["parity_mismatch_states"] == [36, 14, 52]
    assert narrow["maximum"] < narrow["minimum"]**3
    assert 3*len(narrow["parity_mismatch_states"]) < narrow["period"]
    assert branch_step(36, False) == 6
    assert threshold_step(36, 9) == 216
    assert tall["parity_mismatch_states"] == [6]
    assert tall["gcd"] == 2
    assert tall["maximum"] > tall["minimum"]**3
    assert not narrow["actual_juggler_cycle"] and not tall["actual_juggler_cycle"]


def test_invalid_inputs_and_corrupted_cycles_are_rejected():
    with pytest.raises(ValueError):
        orbit_cycle(2)
    with pytest.raises(ValueError):
        orbit_cycle(3, start=27)
    with pytest.raises(ValueError):
        orbit_cycle(3, cap=0)
    assert orbit_cycle(9, cap=2) is None
    with pytest.raises(AssertionError):
        certify_cycle(9, [9, 27, 141])
    with pytest.raises(AssertionError):
        certify_cycle(9, [9, 27, 140, 9])


def test_archived_scope_and_capped_results():
    data = json.loads((DATA_ROOT / "cycle_cubic_band" / "summary.json").read_text(encoding="utf-8"))
    done = [row for row in data["rows"] if "period" in row]
    capped = [row for row in data["rows"] if "unresolved_at_step_cap" in row]
    assert len(done) == 9998 and len(capped) == 4
    assert sum(row["cycles"] for row in data["complete_graphs"]) == 38
    assert all(row["minimum_mismatches"] > 0 for row in data["complete_graphs"])
    assert max(row["period"] for row in done) == 16631
    assert sum(row["transient"] == 0 for row in done) == 1355
    assert all(not row["juggler_cycle"] for row in done)
    assert all("juggler_cycle" not in row for row in capped)
    assert data["counterexamples"] == counterexamples()
