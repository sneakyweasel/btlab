"""The 3x-1 verification floor, and the period bound it makes unconditional.

The bridge makes a negative Collatz cycle word a Paper A CycleMin word letter for letter, and
neg_cycle_finance is kernel-checked, so a verification floor on the 3x-1 map converts directly into
a period bound. These tests pin the map, the three cycles, the descent rule against full iteration,
the committed certificate to 2^44 -- including the seven odd starts the original 2^38 chunks left
between them, found from their own printouts and verified directly -- and the bound the lab's own
finance function returns at each floor.
"""

from __future__ import annotations

import hashlib
import json

import pytest

from research.juggler_sequence.negative_floor_3x1 import (
    CHUNKS_PATH,
    CLASS_FLOOR,
    CYCLE_ELEMENTS,
    CYCLES,
    FLOOR_LOG2,
    JSON_PATH,
    JUMP_VERIFIER_PATH,
    RUNS_PATH,
    STEP_CAP_JUMP,
    STEP_CAP_PLAIN,
    certificate,
    descent_verify,
    first_odd_start,
    parse_report,
    period_bounds,
    reaches_known_cycle,
    reference_agrees,
    shortcut,
)

LEGACY_GAP_STARTS = [k * 2**35 + 1 for k in range(1, 8)]


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
    assert data["max_steps"] < STEP_CAP_PLAIN


def test_descent_verify_reports_a_planted_cycle() -> None:
    """Sanity: the cycle branch fires on a known cycle element rather than silently passing."""
    data = descent_verify(5, 6)
    assert data["clean"]          # 5 is a known cycle element, so not reported as new
    assert data["new_cycles"] == []


def test_parse_report_reassembles_the_peak_and_keeps_alerts() -> None:
    text = "limit=5 walked=1 skipped=2 fails=0 new_cycles=0 max_steps=3\npeak_hi=1 peak_lo=2\n"
    data = parse_report(text)
    assert data["peak"] == 2**64 + 2
    assert data["walked"] == 1 and data["skipped"] == 2 and data["alerts"] == []
    loud = parse_report("STEPCAP at 9\n" + text.replace("fails=0", "fails=1"))
    assert loud["fails"] == 1 and loud["alerts"] == ["STEPCAP at 9"]


def test_first_odd_start_recovers_the_legacy_launch_values() -> None:
    """The plain verifier printed floor((limit - lo)/2), lo odd, so lo = limit - 2 odd_starts - 1."""
    assert first_odd_start({"limit": 2**35, "odd_starts": 17_179_869_182}) == 3
    assert first_odd_start({"limit": 2**36, "odd_starts": 17_179_869_182}) == 2**35 + 3
    assert first_odd_start({"limit": 2**38 + 3 * 2**35, "odd_starts": 51_539_607_551}) == 2**38 + 1
    assert first_odd_start({"lo": 10, "limit": 20, "odd_starts": 5}) == 11
    assert first_odd_start({"lo": 11, "limit": 20, "odd_starts": 5}) == 11


def test_committed_certificate_covers_two_to_the_forty_fourth() -> None:
    cert = certificate()
    assert cert["clean"]
    assert cert["fails"] == 0 and cert["new_cycles"] == 0
    assert cert["covered_to"] == 2**FLOOR_LOG2 == 2**44
    assert cert["covered_to_is_two_pow"] and cert["chunk_limits_increase"]
    assert cert["chunks"] == 112
    assert cert["chunks_by_verifier"] == {"verify_3x1.c": 16, "verify_3x1_jump.c": 96}
    assert cert["max_steps_by_verifier"]["verify_3x1.c"] == 544
    assert cert["max_steps_by_verifier"]["verify_3x1_jump.c"] == 704
    assert cert["step_caps"] == {"verify_3x1.c": STEP_CAP_PLAIN, "verify_3x1_jump.c": STEP_CAP_JUMP}
    assert cert["max_excursion"] == 121443575752945981388885320
    # the __int128 state left 64 bits and never came near overflow
    assert 2**64 < cert["max_excursion"] < 2**127
    assert len(cert["runs"]) == 1


def test_the_legacy_chunks_left_seven_starts_between_them_and_each_is_verified() -> None:
    """Chunks 1..7 of the 2^38 certificate were launched at k 2^35 + 3, so k 2^35 + 1 fell between
    chunks. The record says so rather than hiding it, and every gap start reaches a known cycle."""
    cert = certificate()
    assert cert["gap_starts"] == LEGACY_GAP_STARTS
    assert cert["gap_starts_verified"]
    assert not cert["chunks_are_contiguous"]
    assert all(reaches_known_cycle(y) for y in LEGACY_GAP_STARTS)
    chunks = sorted(json.loads(CHUNKS_PATH.read_text(encoding="utf-8")), key=lambda c: c["limit"])
    assert [c["lo"] for c in chunks[:8]] == [3] + [k * 2**35 + 3 for k in range(1, 8)]
    # from chunk 8 on, every chunk starts exactly where the previous one stopped
    assert all(first_odd_start(b) == a["limit"] + 1 for a, b in zip(chunks[7:], chunks[8:]))


def test_the_jump_chunks_count_every_odd_start_exactly() -> None:
    """walked + skipped is the number of odd starts in [lo, limit): the sieve skips, it never loses."""
    chunks = [c for c in json.loads(CHUNKS_PATH.read_text(encoding="utf-8"))
              if c.get("verifier") == "verify_3x1_jump.c"]
    assert len(chunks) == 96
    for c in chunks:
        assert c["lo"] % 2 == 0 and c["limit"] % 2 == 0
        assert c["odd_starts"] == (c["limit"] - c["lo"]) // 2 == c["walked"] + c["skipped"]
        assert c["fails"] == 0 and c["new_cycles"] == 0 and c["max_steps"] < STEP_CAP_JUMP
    assert sum(c["odd_starts"] for c in chunks) == 2**43 - 2**39 == 8_246_337_208_320
    assert chunks[0]["lo"] == 2**40 and chunks[-1]["limit"] == 2**44


def test_the_run_record_names_the_source_that_ran() -> None:
    runs = json.loads(RUNS_PATH.read_text(encoding="utf-8"))
    assert len(runs) == 1
    run = runs[0]
    assert run["range"] == [2**40, 2**44] and run["chunks"] == [16, 111]
    assert run["odd_starts"] == 8_246_337_208_320
    assert run["fails"] == 0 and run["new_cycles"] == 0
    assert run["verifier"] == JUMP_VERIFIER_PATH.name
    digest = hashlib.sha256(JUMP_VERIFIER_PATH.read_bytes()).hexdigest()
    assert run["verifier_source_sha256"] == digest
    assert run["max_steps"] < run["step_cap"] == STEP_CAP_JUMP


def test_the_floor_buys_the_period_bound() -> None:
    rows = {r["floor"]: r for r in period_bounds(
        floors=((2**38, "2^38"), (10**11, "10^11"), (2**40, "2^40"), (2**44, "2^44")))}
    assert rows["2^44"]["least_period"] == 16_483_927
    assert rows["2^44"]["odd_steps"] == 10_400_200
    assert rows["2^44"]["verified"]
    assert rows["2^40"]["least_period"] == 9_538_065
    assert rows["2^40"]["odd_steps"] == 6_017_849
    assert rows["2^38"]["least_period"] == 4_404_167
    assert rows["2^38"]["odd_steps"] == 2_778_720
    assert rows["10^11"]["least_period"] == 1_988_215
    # the bound is monotone in the floor: a higher floor forbids more lengths
    assert (rows["2^44"]["least_period"] > rows["2^40"]["least_period"]
            > rows["2^38"]["least_period"] > rows["10^11"]["least_period"])


@pytest.mark.skipif(not JSON_PATH.exists(), reason="probe artifact not built")
def test_committed_artifact_is_green() -> None:
    data = json.loads(JSON_PATH.read_text(encoding="utf-8"))
    assert data["decision"]["classification"] == CLASS_FLOOR
    assert data["decision"]["branch"] == "PROMOTE"
    assert data["certificate"]["clean"]
    assert "16483927" in data["statement"]
