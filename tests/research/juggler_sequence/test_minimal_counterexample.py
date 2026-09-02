"""Minimal-counterexample well-ordering phase. Not a halt test."""

from __future__ import annotations

import json
from pathlib import Path

from research.juggler_sequence.lean_paths import MINIMAL_CLOSURE, has_named
from research.juggler_sequence.minimal_counterexample import (
    ANTI,
    CLASS_COMPLEX,
    CLOSED_IMPORT_TOKENS,
    DATA_DIR,
    DOSSIER_PATH,
    JSON_PATH,
    LEAN_THEOREMS,
    barrier_walk,
    closure_matches_window_basin,
    closure_versus_stopping_time,
    ee_stays_above,
    eo_stays_above,
    good_closure,
    lean_api_present,
    odd_predecessor,
    oe_stays_above,
    orbit_inside_window,
    stopping_times,
    two_step,
    two_step_census,
    u_set_formula_count,
    u_set_scan,
)
from research.juggler_sequence.power_itineraries import floor_power


def test_odd_predecessor_is_unique_and_validated():
    assert odd_predecessor(1) == 1
    assert floor_power(1) == 1
    assert odd_predecessor(5) == 3
    assert floor_power(3) == 5
    assert odd_predecessor(11) == 5
    assert odd_predecessor(36) == 11
    assert odd_predecessor(2) is None
    seen = {}
    for m in range(1, 80):
        n = odd_predecessor(m)
        if n is None:
            continue
        assert n % 2 == 1
        assert floor_power(n) == m
        assert n not in seen
        seen[n] = m


def test_u_set_formula_matches_scan():
    for B in (2, 11, 12, 36, 63, 100):
        assert u_set_scan(B, 400) == u_set_formula_count(B, 400)
    # All odds above B are uncovered; evens below (B+1)^2 are not.
    B = 12
    for n in range(B + 1, 80):
        uncovered = B < floor_power(n)
        if n % 2 == 1:
            assert uncovered
        elif n < (B + 1) ** 2:
            assert not uncovered
        else:
            assert uncovered


def test_two_step_barrier_identities():
    for n in range(2, 200):
        word, _y, z = two_step(n)
        if word == "OE":
            assert (n <= z) == oe_stays_above(n, n)
        elif word == "EE":
            assert (n <= z) == ee_stays_above(n, n)
        elif word == "EO":
            assert (n <= z) == eo_stays_above(n, n)
        elif n >= 3:
            assert z > n
    census = two_step_census(200)
    assert census["ok"]
    assert sum(census["counts"].values()) == 199


def test_closure_is_the_window_restricted_inverse_basin():
    n_max, depth = 80, 8
    tau = stopping_times(n_max, horizon=10_000)
    closure = good_closure(n_max, depth)
    vs = closure_matches_window_basin(
        closure["certified"], closure["added_round"], depth
    )
    assert vs["ok"], vs["mismatches"]
    vs_tau = closure_versus_stopping_time(closure["certified"], tau, depth)
    assert vs_tau["equal"] is False
    assert 9 in vs_tau["tau_le_depth_but_orbit_left_window"]
    assert tau[1] == 0
    assert tau[2] == 1
    assert tau[3] == 6
    assert tau[13] == 4
    assert tau[9] == 7
    assert closure["added_round"][3] == 6
    assert closure["certified"][3] is True
    assert closure["certified"][9] is False
    assert floor_power(27) == 140
    assert 140 > n_max
    assert 27 in closure["upward_reentry"]["would_certify"]


def test_n25_leaves_the_phase0_window():
    assert floor_power(25) == 125
    assert floor_power(125) == 1397
    assert floor_power(1397) == 52214
    assert orbit_inside_window(25, 4000, 12) is None
    assert orbit_inside_window(3, 4000, 12) == 6


def test_even_start_drops_immediately_odd_may_grow():
    even = barrier_walk(8)
    assert even["first_drop"] == 1
    assert even["word"] == "E"
    three = barrier_walk(3)
    assert three["word"].startswith("OOO")
    assert three["first_drop"] == 5
    assert three["peak"] == 36
    assert floor_power(3) == 5


def test_anti_overclaim_and_closed_imports():
    assert ANTI["global_termination"] is False
    assert ANTI["finite_horizon_is_bad"] is False
    assert ANTI["closure_from_one_is_new_induction"] is False
    assert ANTI["visited_ge_nstar_is_automatically_good"] is False
    source = Path(__file__).resolve().parents[3] / "src" / "research" / "juggler_sequence" / "minimal_counterexample.py"
    text = source.read_text(encoding="utf-8")
    for token in CLOSED_IMPORT_TOKENS:
        assert f"juggler_sequence.{token}" not in text


def test_lean_api_and_no_halt_theorem():
    lean = lean_api_present()
    assert lean["sorry_free"]
    for name in LEAN_THEOREMS:
        assert lean[name], name
    src = MINIMAL_CLOSURE.read_text(encoding="utf-8")
    assert "sorry" not in src
    assert "admit" not in src
    assert "theorem predClosure_iff_reachesOne" in src
    assert "theorem minimal_bad_impossible" not in src
    assert has_named(src, "PredClosure")


def test_dossier_and_artifacts_if_present():
    text = DOSSIER_PATH.read_text(encoding="utf-8") if DOSSIER_PATH.is_file() else ""
    if text:
        assert "## Branch budget" in text
        assert "## Decision" in text
        assert "## Publication assessment" in text
        assert "CLOSE" in text.split("## Decision", 1)[1]
    if not JSON_PATH.is_file():
        return
    data = json.loads(JSON_PATH.read_text(encoding="utf-8"))
    assert data["experiment"] == "juggler_minimal_counterexample"
    assert data["cuda_used"] is False
    assert data["anti_overclaim"]["global_termination"] is False
    assert data["closure_vs_window"]["ok"] is True
    assert data["closure_vs_tau"]["equal"] is False
    assert data["u_set"]["formula_ok"] is True
    assert data["decision"]["classification"] == CLASS_COMPLEX
    assert data["decision"]["branch"] == "CLOSE"
    for name in (
        "manifest.json",
        "good_closure.csv",
        "closure_layers.csv",
        "uncovered.csv",
        "minimality_constraints.csv",
        "barrier_words.jsonl",
        "counterexamples.jsonl",
    ):
        assert (DATA_DIR / name).is_file(), name
