"""Exact almost-cycle search. Not a halt test."""

from __future__ import annotations

import json
from pathlib import Path

from research.conjectures import get_conjecture
from research.juggler_sequence.cycle_almost_search import (
    PHASE1_L,
    compatible_oe_preimages,
    cube_root_ceil,
    distinguished_words,
    envelope_error,
    exact_return_error,
    follow_word,
    leftover_row,
    packed_block_word,
    phase1_report,
    run_preimages,
    run_stats,
    word_bundle,
)
from research.juggler_sequence.cycle_budget_opt import run_type_counts
from research.juggler_sequence.cycle_finance import PUBLISHED_FLOOR, o_min_and_theta
from research.juggler_sequence.cycle_ordered_excursion import excursion_map
from research.juggler_sequence.power_itineraries import floor_power

REPO = Path(__file__).resolve().parents[3]
SUMMARY = (
    REPO
    / "data"
    / "research"
    / "juggler"
    / "cycle_finance"
    / "almost_search"
    / "summary.json"
)


def test_phase1_length_is_the_finance_frontier():
    odd, theta = o_min_and_theta(PHASE1_L)
    assert PHASE1_L == 25781
    assert odd == 16266
    assert 2.5e-5 < theta < 2.6e-5


def test_distinguished_words_are_prefix_legal_and_two_type():
    odd, _ = o_min_and_theta(PHASE1_L)
    bundle = word_bundle(PHASE1_L, odd)
    oo, oe = run_type_counts(odd, PHASE1_L - odd)
    for name in ("extremal", "christoffel", "packed_block"):
        row = bundle[name]
        assert row["prefix_ok"]
        assert row["a0"] >= 2
        assert row["two_type"]
        assert row["n_ooe"] == oo
        assert row["n_oe"] == oe
        assert row["n_other"] == 0
        assert row["length"] == PHASE1_L
        assert row["odd"] == odd
    assert bundle["extremal_eq_christoffel"]


def test_packed_blocks_sum_to_length():
    odd, _ = o_min_and_theta(19)
    word = packed_block_word(19, odd)
    stats = run_stats(word)
    assert stats["length"] == 19
    assert stats["odd"] == odd
    assert stats["two_type"]


def test_envelope_error_matches_expm1():
    theta = 2.546e-5
    n = 1_000_001
    err = envelope_error(n, theta)
    assert abs(err - (n**theta - 1.0)) < 1e-12
    assert exact_return_error(n + 3, n) == 3 / n


def test_cube_root_and_oe_cell():
    assert cube_root_ceil(8) == 2
    assert cube_root_ceil(9) == 3
    assert cube_root_ceil(1) == 1
    for y in (13, 25, 101, 365, 1000001):
        for valley, peak in compatible_oe_preimages(y):
            assert valley % 2 == 1
            assert peak % 2 == 0
            assert floor_power(valley) == peak
            assert floor_power(peak) == y
            assert y * y <= peak < (y + 1) * (y + 1)


def test_run_preimages_invert_realized_blocks():
    seed = 365
    rec = excursion_map(seed, 2)
    assert rec is not None
    _peak, landing = rec
    assert seed in run_preimages(landing, 2)
    rec1 = excursion_map(1000001, 1)
    if rec1 is not None:
        assert 1000001 in run_preimages(rec1[1], 1)


def test_l19_christoffel_has_no_complete_follower_in_window():
    odd, _ = o_min_and_theta(19)
    word = distinguished_words(19, odd)["christoffel"]
    complete = 0
    max_depth = 0
    for n in range(13, 4001, 2):
        rec = follow_word(n, word)
        max_depth = max(max_depth, rec["depth"])
        if rec["complete"]:
            complete += 1
    assert complete == 0
    assert 1 <= max_depth < 19


def test_l19_report_is_envelope_scale():
    report = phase1_report(
        length=19,
        floor=12,
        forward_lo=13,
        forward_hi=4001,
        follow_hi=2001,
        backward_count=12,
        workers=1,
        bit_cap=4096,
        beam=8,
        include_calibration=False,
    )
    assert report["L"] == 19
    assert report["exact_cycle"] is False
    assert report["leftover_killer"] is False
    assert report["halt_theorem"] is False
    assert report["no_cycle_all_lengths"] is False
    assert report["forward"]["n_at_L"] == 0 or report["forward"]["best_E_at_L"] != 0.0
    assert all(row["complete"] == 0 for row in report["follow"].values())
    assert all(row["complete"] == 0 for row in report["backward"].values())


def test_leftover_row_flags_only_unusually_close_returns():
    env = 3.5e-4
    far = leftover_row(25781, min_e=env, envelope=env, complete_word=False, survived=0)
    close = leftover_row(
        25781, min_e=env / 200.0, envelope=env, complete_word=True, survived=1
    )
    zero = leftover_row(25781, min_e=0.0, envelope=env, complete_word=True, survived=1)
    assert far["unusually_close"] is False
    assert far["exact_cycle"] is False
    assert close["unusually_close"] is True
    assert zero["exact_cycle"] is True
    assert far["kills"] is False


def test_science_artifact_schema():
    payload = json.loads(SUMMARY.read_text(encoding="utf-8"))
    assert payload["bound"] == "almost_search"
    assert payload["phase"] == 1
    assert payload["L"] == PHASE1_L
    assert payload["o"] == 16266
    assert payload["e"] == 9515
    assert payload["floor"] == PUBLISHED_FLOOR
    assert payload["n_max_run"] == 19010076
    assert payload["words"]["extremal_eq_christoffel"] is True
    assert payload["words"]["christoffel_eq_packed"] is True
    assert payload["forward"]["n_at_L"] == 0
    assert payload["forward"]["survived"] == 0
    assert payload["forward"]["max_steps"] == 257
    assert payload["forward"]["hardest"] == 6127057
    assert payload["min_E"] is None
    assert payload["exact_cycle"] is False
    assert payload["unusually_close"] is False
    assert payload["envelope_dominated"] is True
    assert payload["dominant_fail_block"] == "2,1"
    assert payload["leftover_killer"] is False
    assert payload["halt_theorem"] is False
    assert payload["no_cycle_all_lengths"] is False
    assert payload["requires_word_enumeration"] is False
    assert all(row["complete"] == 0 for row in payload["backward"].values())
    assert all(row["complete"] == 0 for row in payload["follow"].values())


def test_dossier_and_conjecture_record_close():
    dossier = (
        REPO / "docs" / "problems" / "juggler_cycle_almost_search.md"
    ).read_text(encoding="utf-8")
    assert "## Branch budget" in dossier
    assert "## Decision" in dossier
    assert "## Publication assessment" in dossier
    assert "**CLOSE**" in dossier
    assert "Do not open Phase 2 or" in dossier
    assert "juggler_cycle_almost_search" in dossier
    rec = get_conjecture("juggler_cycle_almost_search")
    assert rec["status"] == "REFUTED"
    assert rec["counterexamples"]
