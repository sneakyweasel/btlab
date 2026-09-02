"""Fast checks for the walk coboundary / Lyapunov phase probe."""

from __future__ import annotations

import json
import math
from pathlib import Path

from research.conjectures import get_conjecture
from research.juggler_sequence.power_itineraries import floor_power
from research.juggler_sequence.walk_coboundary import (
    CLASS_DEFEATED,
    JSON_PATH,
    MIN_X,
    adversary_prefix_report,
    drift_of,
    even_dphase_wings,
    family_report,
    frac_sqrt,
    frac_three_halves,
    leading_drift,
    log2_ln,
    one_step_bounded_psi_obstruction,
    universe_one_steps,
)

REPO = Path(__file__).resolve().parents[3]
DOSSIER = REPO / "docs" / "problems" / "juggler_walk_coboundary.md"


def test_log2_ln_increments_match_the_walk() -> None:
    assert abs(leading_drift(17, floor_power(17)) - math.log2(1.5)) < 0.05
    assert abs(leading_drift(200, floor_power(200)) + 1.0) < 0.05
    assert log2_ln(16) == math.log2(math.log(16))


def test_even_square_leading_is_exactly_minus_one() -> None:
    for k in (4, 6, 8, 10, 12, 16):
        assert leading_drift(k * k, k) == -1.0


def test_even_square_tower_kills_bounded_psi() -> None:
    rec = one_step_bounded_psi_obstruction(4, 4)
    assert rec["leading_sum"] == -4.0
    assert rec["bounded_psi_impossible"] is True
    assert all(v == -1.0 for v in rec["leadings"])


def test_sqrt_phase_vanishes_on_even_fourth_powers() -> None:
    assert frac_sqrt(16) == 0.0
    assert frac_sqrt(4) == 0.0
    assert drift_of(16, 4, frac_sqrt, 2.0) == -1.0
    assert frac_three_halves(16) == 0.0
    assert frac_three_halves(4) == 0.0


def test_adversary_1999_has_fan_and_collapse() -> None:
    rec = adversary_prefix_report(1999)
    assert rec["both_signs"] is True
    assert rec["n_fan"] >= 1
    assert rec["n_collapse"] >= 1
    assert rec["fan_min_leading"] is not None
    assert rec["collapse_min_leading"] is not None
    assert 0.01 < rec["fan_min_leading"] < 0.05
    assert rec["collapse_min_leading"] < -1.0


def test_even_phase_increments_have_both_wings() -> None:
    wings = even_dphase_wings(MIN_X, 400)
    for name in ("sqrt", "three_halves", "fourth", "pi_log2"):
        assert wings[name]["both_wings"] is True


def test_small_universe_search_stays_negative() -> None:
    pairs = universe_one_steps(MIN_X, 240)
    rep = family_report(pairs)
    assert rep["baseline"]["min_drift"] < -0.5
    assert rep["best"]["min_drift"] < 0.0
    assert not (
        rep["best"]["min_drift"] >= 0.0
        and rep["baseline"]["min_drift"] < 0.0
    )


def test_artifact_defeats_the_correction() -> None:
    payload = json.loads(JSON_PATH.read_text(encoding="utf-8"))
    assert payload["classification"] == CLASS_DEFEATED
    assert payload["decision"] == "CLOSE"
    depth = payload["obstruction"]["depth"]
    assert payload["obstruction"]["leading_sum"] == -depth
    assert payload["obstruction"]["bounded_psi_impossible"] is True
    families = payload["families"]
    assert families["universe_one"]["best"]["min_drift"] < 0.0
    assert families["prefix_one"]["best"]["min_drift"] < 0.0
    assert families["slide19"]["best"]["min_drift"] < 0.0
    assert families["first_oe"]["best"]["min_drift"] < 0.0
    assert families["slide19"]["baseline"]["min_drift"] < -1.0
    assert families["slide19_fan"]["baseline"]["min_drift"] > 0.0
    adv = {row["n"]: row for row in payload["adversaries"]}
    assert adv[1999]["both_signs"] is True
    assert adv[761]["both_signs"] is True
    anti = payload["anti_overclaim"]
    assert anti["halt_theorem"] is False
    assert anti["dk_tightened"] is False
    assert anti["n0_raised"] is False
    assert anti["paper_a_modified"] is False


def test_dossier_and_conjecture_record_close() -> None:
    text = DOSSIER.read_text(encoding="utf-8")
    assert "## Branch budget" in text
    assert "Mathematical target" in text
    assert "## Decision" in text
    assert "**CLOSE**" in text
    assert "Do **not** raise" in text
    rec = get_conjecture("juggler_walk_phase_correction")
    assert rec["status"] == "REFUTED"
    assert rec["counterexamples"]
