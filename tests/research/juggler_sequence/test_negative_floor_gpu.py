"""The GPU verifier of the 3x-1 descent floor: its procedure checked in Python at small size,
its known-bad input, and its calibration against the CPU certificate read from the archived
reports (the binary is needed only for the last test, which skips without it).

Calibration of 21 September 2026 on the RTX 5090: [3, 2^35) and [3, 2^40) reproduce the plain
walker's max_steps (508, 544) and peaks exactly; [2^40, 2^44) reproduces the odd-start count
8246337208320, zero failures, the landing peak 121443575752945981388885320 exactly, and
max_steps 703 against the jump walker's granular 704, in 26 s against the CPU's 1628 s wall on
24 threads."""
from __future__ import annotations

import json

import pytest

from research.juggler_sequence import negative_floor_gpu as gpu


def test_python_walker_matches_the_c_map_step_by_step() -> None:
    """The run identity is exact: the double-step walker and single steps of g agree."""
    for y0 in range(3, 3000, 2):
        w = gpu.walk(y0)
        y, steps = y0, 0
        while True:
            y = gpu.g(y)
            steps += 1
            if y < y0:
                assert w.status == "drop" and w.steps == steps, y0
                break
            if y == y0:
                assert w.status == "cycle", y0
                break
            if y <= 136 and y in gpu.KNOWN and y % 2 == 1:
                # the kernel tests known elements at the end of an even run only (odd y); the
                # cycle minima 5 and 17 come back to themselves before that test fires
                assert w.status == "drop" or y0 in (5, 17), y0
                break
            if y <= 136 and y in gpu.KNOWN:
                break  # the C walkers stop at an even known element; the kernel halves on
            assert steps < 5000


def test_survivors_and_walk_reproduce_the_gpu_report_on_2000() -> None:
    """The archived GPU run of [3, 2000): 32 walked starts, max_steps 62, peak 413344, one
    known cycle return (5; the start 17 stops at 41, a known element)."""
    surv = gpu.survivors_below(2000)
    assert len(surv) == 32
    walks = {y: gpu.walk(y) for y in surv}
    assert max(w.steps for w in walks.values()) == 62
    assert max(w.peak for w in walks.values()) == 413344
    assert [y for y, w in walks.items() if w.status == "cycle"] == [5]


def test_known_bad_input_the_forgotten_17_cycle_is_a_cycle() -> None:
    known = tuple(k for k in gpu.KNOWN if k not in gpu.CYCLE17)
    assert gpu.walk(17, known=known).status == "cycle"
    assert gpu.walk(17).status == "drop"
    assert gpu.walk(5).status == "cycle"


def test_odd_count_convention() -> None:
    assert gpu.odd_count(3, 2 ** 35) == 2 ** 34 - 1
    assert gpu.odd_count(2 ** 40, 2 ** 44) == 15 * 2 ** 39 == 8246337208320
    assert gpu.odd_count(4, 5) == 0 and gpu.odd_count(4, 6) == 1


def test_archived_calibration_agrees_with_the_certificate() -> None:
    s = json.loads(gpu.SUMMARY.read_text(encoding="utf-8"))
    c = s["comparison"]
    assert c["all_agree"], c
    assert c["sieve_classes_A076227_24"] and c["known_bad_forgotten_17_reported"]
    assert c["3_2p35"]["max_steps"] == [508, 508] and c["3_2p40"]["max_steps"] == [544, 544]
    assert c["2p40_2p44"]["odd_starts"] == [8246337208320, 8246337208320]
    assert c["2p40_2p44"]["max_steps"] == [703, 704]
    assert c["peak_2p40_2p44_equal_to_landing_peak"]
    assert c["2p40_2p44"]["peak"][0] == 121443575752945981388885320
    assert c["timing"]["speedup_vs_24_threads"] > 30
    # the recomputation from the archived reports agrees with the recorded comparison
    fresh = json.loads(json.dumps(gpu.compare_with_certificate({name: rep for name, rep in s["reports"].items()})))
    assert fresh["all_agree"] and fresh["2p40_2p44"] == c["2p40_2p44"]


def test_projection_is_monotone_and_starts_from_the_calibrated_rate() -> None:
    s = json.loads(gpu.SUMMARY.read_text(encoding="utf-8"))
    hours = [p["hours"] for p in s["projections_hours_from_2p44"]]
    assert hours == sorted(hours) and hours[0] > 0
    assert abs(s["projections_hours_from_2p44"][-1]["hours"] - ((2 ** 60 - 2 ** 44) / 2) / s["rate_odd_starts_per_second"] / 3600) < 1e-6


@pytest.mark.skipif(not gpu.gpu_available(), reason="GPU verifier not buildable or no GPU")
def test_gpu_binary_agrees_with_the_python_walker_on_2000() -> None:
    rep = gpu.run(3, 2000)
    assert rep["walked"] == 32 and rep["max_steps"] == 62 and gpu.peak_of(rep) == 413344
    assert rep["fails"] == 0 and rep["new_cycles"] == 0 and rep["known_cycle_returns"] == 1
    bad = gpu.run(3, 2000, forget_17=True)
    assert bad["new_cycles"] == 1 and bad["new_cycle_starts"] == [17] and bad["exit_code"] == 1
