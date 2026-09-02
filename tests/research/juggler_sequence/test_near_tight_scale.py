"""Scale-induced near-tightness. Not a termination test."""

from __future__ import annotations

from research.juggler_sequence.expansion_slack import NEAR_TIGHT
from research.juggler_sequence.global_defect import follows_itinerary
from research.juggler_sequence.lean_paths import juggler_text
from research.juggler_sequence.near_tight_scale import (
    LEAN_THEOREMS,
    OOE_PRED_START,
    eta_window,
    exact_q_positive,
    lean_api_present,
    near_tight_prediction,
    ooe_scale_census,
    ooe_weighted_etas,
    pe_pair_census,
    q_exact,
)
from research.juggler_sequence.normalized_defect import eta_pair
from research.juggler_sequence.power_itineraries import floor_power


def test_eta_stays_inside_successor_window():
    report = eta_window(n_max=400)
    assert report["bound_fail"] == 0
    assert report["checked"] > 0
    assert report["tight"] >= 1
    rho, t2 = eta_pair(12)
    t = floor_power(12)
    assert rho < 2 * t + 1
    assert rho / t2 < 2 / t + 1 / (t * t)


def test_ooe_last_even_remainder_dominates_and_tracks_scale():
    report = ooe_scale_census(n_max=800)
    assert report["checked"] >= 20
    assert report["last_even_frac"] > 0.8
    assert report["median_q_over_scale"] is not None
    assert 1.0 < report["median_q_over_scale"] < 10.0


def test_large_lambda_successor_matches_y_scale():
    pred = near_tight_prediction()
    assert pred["x"] == OOE_PRED_START
    assert pred["u"] == "OOOOOOOOE"
    assert pred["y"] == NEAR_TIGHT["x"]
    assert pred["lam_u"] > 10
    assert pred["exact_positive"]
    assert 1.0 < pred["q_over_scale"] < 8.0
    assert pred["q"] < 1e-30
    w0, w1, w2 = pred["weights"]
    assert w2 > w0 and w2 > w1
    assert exact_q_positive(pred["y"], "OOE")
    assert follows_itinerary(pred["y"], "OOE")


def test_pe_successor_q_tracks_image_scale():
    report = pe_pair_census(n_max=800)
    assert report["ooe_sequels"] >= 5
    assert report["ooe_q_over_y_scale_min"] > 0
    assert report["ooe_q_over_y_scale_max"] < 12
    if report["large_y_max_q2"] is not None:
        assert report["large_y_max_q2"] < 1e-6


def test_mixed_ooe_can_be_near_tight_without_equality():
    y = NEAR_TIGHT["x"]
    assert q_exact(y, "OOE") > 0
    assert q_exact(y, "OOE") < 1e-30
    assert follows_itinerary(y, "OOE")


def test_lean_api_and_sorry_free():
    lean = lean_api_present()
    assert lean["sorry_free"]
    text = juggler_text()
    assert "sorry" not in text
    assert "admit" not in text
    for name in LEAN_THEOREMS:
        assert lean[name], name
    assert "import Problems.Juggler.NearTightScale" in text
