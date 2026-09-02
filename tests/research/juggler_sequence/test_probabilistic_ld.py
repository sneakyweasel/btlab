"""Exact-versus-LD geometry. Not a halt test."""

from __future__ import annotations

import json
import math
from pathlib import Path

from research.juggler_sequence.power_itineraries import floor_power
from research.juggler_sequence.probabilistic_ld import (
    ANTI,
    A_STAR,
    CLOSED_IMPORT_TOKENS,
    DOSSIER_PATH,
    EXCEPTIONAL_P_DEV,
    EXCEPTIONAL_Z_DEV,
    GAMMA,
    I0,
    JSON_PATH,
    MODEL_DOC,
    P0,
    P_STAR,
    DATA_DIR,
    delta_and_floor,
    model_parameters,
    safe_log,
    safe_loglog,
    summarize_walk,
    walk_coordinates,
)


def test_optimizer_identities():
    assert P_STAR == 0.75
    assert abs(A_STAR - (0.75 * math.log(3.0) - math.log(2.0))) < 1e-15
    assert abs(P0 - math.log(2.0) / math.log(3.0)) < 1e-15
    assert abs(I0 * GAMMA - 1.0) < 1e-12
    assert abs(GAMMA - 28.828259) < 1e-5
    i_star = P_STAR * math.log(2.0 * P_STAR) + (1.0 - P_STAR) * math.log(2.0 * (1.0 - P_STAR))
    assert abs(i_star - A_STAR) < 1e-12


def test_safe_log_matches_math_on_small_ints():
    for n in (3, 16, 37, 3889):
        assert abs(safe_log(n) - math.log(n)) < 1e-12
        assert abs(safe_loglog(n) - math.log(math.log(n))) < 1e-12
    huge = 1 << 2000
    ln = safe_log(huge)
    assert abs(ln - 2000 * math.log(2.0)) < 1e-6
    assert safe_loglog(huge) is not None


def test_n3_is_oooee_and_coordinates_are_diagnostic():
    walk = walk_coordinates(3)
    rec = summarize_walk(walk)
    assert rec["word"] == "OOOEE"
    assert rec["tau"] == 5
    assert rec["returned"] is True
    assert rec["peak"] == 36
    assert rec["Z_peak"] is not None
    assert rec["t_peak"] is not None
    assert floor_power(3) == 5
    delta, floor_err = delta_and_floor(3, 5, "O")
    assert delta is None or floor_err is None or abs(delta - math.log(1.5) - floor_err) < 1e-9


def test_even_start_is_not_an_ld_witness():
    rec = summarize_walk(walk_coordinates(2))
    assert rec["returned"] is True
    assert rec["tau"] == 1
    assert rec["word"] == "E"


def test_exceptional_cuts_are_declared_a_priori():
    assert EXCEPTIONAL_Z_DEV == 0.20
    assert EXCEPTIONAL_P_DEV == 0.25
    params = {row["parameter"]: row for row in model_parameters()}
    assert params["a_star"]["assumption_status"] == "DERIVED_FROM_M0"
    assert params["gamma"]["assumption_status"] == "DERIVED_FROM_M0"
    assert params["P_O_M0"]["assumption_status"] == "MODEL_ASSUMPTION"
    assert params["exceptional_Z_dev"]["value"] == 0.20


def test_anti_overclaim_and_closed_imports():
    assert ANTI["global_termination"] is False
    assert ANTI["negative_drift_implies_halt"] is False
    assert ANTI["automaton"] is False
    assert ANTI["paper_constant_is_a_theorem"] is False
    assert ANTI["new_loglog_energy"] is False
    source = Path(__file__).resolve().parents[3] / "src" / "research" / "juggler_sequence" / "probabilistic_ld.py"
    text = source.read_text(encoding="utf-8")
    for token in CLOSED_IMPORT_TOKENS:
        assert f"juggler_sequence.{token}" not in text


def test_artifacts_if_present():
    assert MODEL_DOC.is_file()
    if not JSON_PATH.is_file():
        return
    data = json.loads(JSON_PATH.read_text(encoding="utf-8"))
    assert data["experiment"] == "juggler_probabilistic_ld"
    assert data["cuda_used"] is False
    assert data["anti_overclaim"]["global_termination"] is False
    assert data["model"]["exceptional_threshold"]["declared_before_scan"] is True
    assert data["decision"]["branch"] in ("PARK", "CLOSE")
    text = DOSSIER_PATH.read_text(encoding="utf-8")
    assert "## Branch budget" in text
    assert "## Decision" in text
    assert "## Publication assessment" in text
    for name in (
        "model_parameters.json",
        "scale_parity_statistics.csv",
        "increment_statistics.csv",
        "correlation_statistics.csv",
        "excursion_statistics.csv",
        "record_comparison.csv",
        "extremal_word_statistics.csv",
        "model_residuals.csv",
        "exceptional_paths.jsonl",
    ):
        assert (DATA_DIR / name).is_file()
