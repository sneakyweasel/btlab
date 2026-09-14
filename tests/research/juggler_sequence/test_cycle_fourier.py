"""Closed peak-valley Fourier discovery. Not a halt test."""

from __future__ import annotations

import json
import math
from pathlib import Path

from research.conjectures import get_conjecture
from research.juggler_sequence.cycle_budget_opt import budget_rhs
from research.juggler_sequence.cycle_finance import (
    PUBLISHED_FLOOR,
    o_min_and_theta,
    sha256_int_list,
)
from research.juggler_sequence.cycle_fourier import (
    BUNCHED_WITNESS,
    CONTROLS,
    MOMENT_TARGET,
    abstract_row,
    bunched_word,
    closed_increment_wave,
    control_row,
    cyclic_valleys,
    increments,
    oe_increment_identity,
    parseval_increment_holds,
    run_type_word,
    sign_changes,
    spectral_moment,
    tail_energy_frac,
)
from research.juggler_sequence.cycle_run_extremum import survivor_lengths

REPO = Path(__file__).resolve().parents[3]
START = PUBLISHED_FLOOR + 1
SUMMARY = (
    REPO
    / "data"
    / "research"
    / "juggler"
    / "cycle_finance"
    / "cycle_fourier"
    / "summary.json"
)


def test_parseval_and_oe_identities_on_expanding_word():
    wave = closed_increment_wave("OOEOOE", math.log(START))
    assert wave["ok"]
    assert parseval_increment_holds(wave["t"])
    assert oe_increment_identity(wave["t"], "OOEOOE", float(wave["eps"]))
    moment = spectral_moment(wave["t"])["moment"]
    assert abs(moment - MOMENT_TARGET) < 5e-4


def test_sign_changes_equal_two_m_independent_of_bunching():
    odd_count, _ = o_min_and_theta(BUNCHED_WITNESS)
    even_count = BUNCHED_WITNESS - odd_count
    run_word = run_type_word(odd_count, even_count)
    bunch = bunched_word(odd_count, even_count)
    run_wave = closed_increment_wave(run_word, math.log(START))
    bunch_wave = closed_increment_wave(bunch, math.log(START))
    assert run_wave["ok"] and bunch_wave["ok"]
    run_m = len(cyclic_valleys(run_word))
    bunch_m = len(cyclic_valleys(bunch))
    assert bunch_m == 1
    assert run_m == even_count
    assert run_m > bunch_m
    assert sign_changes(increments(run_wave["t"], cyclic=True)) == 2 * run_m
    assert sign_changes(increments(bunch_wave["t"], cyclic=True)) == 2 * bunch_m
    assert (
        abs(spectral_moment(run_wave["t"])["moment"] - MOMENT_TARGET) < 1e-6
    )
    assert (
        abs(spectral_moment(bunch_wave["t"])["moment"] - MOMENT_TARGET) < 1e-6
    )
    assert tail_energy_frac(run_wave["t"], max(1, len(run_word) // 12)) >= 0.05
    assert tail_energy_frac(bunch_wave["t"], max(1, len(bunch) // 12)) >= 0.05


def test_spotlight_25781_spectrum_does_not_beat_run_type():
    odd_count, theta = o_min_and_theta(25781)
    row = abstract_row(25781, n=START)
    assert row["o"] == odd_count
    assert row["e"] == 9515
    assert row["run_type_valleys"] == 9515
    assert row["bunched_valleys"] == 1
    assert row["sign_changes"] == row["two_m"] == 19030
    assert row["closed_ok"]
    assert row["closed_hits_target"]
    assert row["packed_matches_budget"]
    # Same quantity by two code paths, so compare as reals rather than bit
    # patterns: they agree exactly on Windows and differ by ~500 ulp (relative
    # 1.1e-13) on the Linux CI runner, which failed this test on 14 September
    # 2026. The claim being made is that the packed row carries the budget, not
    # that two float expressions round identically on every libm.
    assert math.isclose(
        row["packed_rhs"], budget_rhs(START, 25781, odd_count), rel_tol=1e-12
    )
    assert theta < row["budget_rhs"]
    assert not row["spectral_excludes"]
    assert not row["budget_excludes"]


def test_controls_hit_moment_without_bandlimit():
    for seed in CONTROLS:
        row = control_row(seed)
        assert row["dropped"]
        assert row["near_target_cyclic"]
        assert row["bandlimit_fails"]
        assert row["tail_L12"] >= 0.05


def test_fourier_scan_closes():
    payload = json.loads(SUMMARY.read_text(encoding="utf-8"))
    assert payload["survivor_count"] == 99
    assert payload["parseval_identity_small"] is True
    assert payload["all_closed_ok"] is True
    assert payload["all_packed_match_budget"] is True
    assert payload["all_both_hit_target"] is True
    assert payload["all_signs_match"] is True
    assert payload["bunched_has_as_many_valleys"] is False
    assert payload["spectral_killed"] == []
    assert payload["spectral_killed_count"] == 0
    assert payload["first_survivor"] == 25781
    assert payload["control_moments_near_target"] is True
    assert payload["control_bandlimit_fails"] is True
    assert payload["halt_theorem"] is False
    assert payload["no_cycle_all_lengths"] is False
    assert payload["sha256_survivors"] == sha256_int_list(survivor_lengths())
    assert payload["spotlights"]["25781"]["spectral_excludes"] is False
    assert payload["spotlights"]["55293"]["spectral_excludes"] is False
    assert payload["bunched_witness"]["same_moment"] is True
    assert payload["bunched_witness"]["bunched_valleys"] == 1
    assert payload["small_84"]["bandlimit_fails"] is True
    assert payload["small_84"]["parseval_closed"] is True


def test_dossier_and_conjecture_record_close():
    dossier = (
        REPO / "docs" / "problems" / "juggler_cycle_fourier.md"
    ).read_text(encoding="utf-8")
    assert "## Branch budget" in dossier
    assert "## Decision" in dossier
    assert "## Publication assessment" in dossier
    assert "**CLOSE**" in dossier
    assert "cycle_fourier/summary.json" in dossier
    assert "juggler_cycle_fourier_leftover_killer" in dossier
    rec = get_conjecture("juggler_cycle_fourier_leftover_killer")
    assert rec["status"] == "REFUTED"
