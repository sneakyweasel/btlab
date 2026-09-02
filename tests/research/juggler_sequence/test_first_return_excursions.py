"""First-return maximality. Not an engine-control or halt test."""

from __future__ import annotations

import json

from research.juggler_sequence.excursions import STATUS_RETURNED, _walk_returns
from research.juggler_sequence.first_return_excursions import (
    CLASS_COMPLEX,
    JSON_PATH,
    LEAN_THEOREMS,
    lean_api_present,
    record,
    slack_profile,
)
from research.juggler_sequence.power_itineraries import floor_power


def test_even_return_is_one_even_step():
    rec = record(2)
    assert rec["returned"] is True
    assert rec["word"] == "E"
    assert rec["margin"] == 1
    assert rec["final_E"] is True


def test_odd_return_ends_with_E_and_y_in_square():
    for n in (3, 7, 9, 37):
        rec = record(n)
        assert rec["returned"] is True
        assert rec["final_E"] is True
        assert rec["y_in_even_square"] is True
        assert rec["prefix_nonneg"] is True
        assert rec["final_neg"] is True


def test_maximality_of_walk():
    path, status, tau, _ = _walk_returns(9, 100, 4096)
    assert status == STATUS_RETURNED
    assert tau is not None
    assert all(state >= 9 for state in path[:-1])
    assert path[-1] < 9


def test_h1_margin_one_is_attained():
    rec = record(3)
    assert rec["margin"] == 1
    assert rec["word"] == "OOOEE"


def test_slack_profile_oooee():
    gaps = slack_profile("OOOEE")
    assert all(g <= 0 for g in gaps[:-1])
    assert gaps[-1] > 0


def test_odd_step_cannot_return():
    for y in (3, 5, 7, 9, 15):
        assert y % 2 == 1
        assert floor_power(y) >= y


def test_lean_api():
    lean = lean_api_present()
    assert lean["sorry_free"] is True
    for name in LEAN_THEOREMS:
        assert lean[name] is True
    assert lean["no_global_termination_theorem"] is True


def test_committed_artifacts_if_present():
    if not JSON_PATH.is_file():
        return
    payload = json.loads(JSON_PATH.read_text(encoding="utf-8"))
    assert payload["engine_control_layer_modified"] is False
    assert payload["anti_overclaim"]["tau_always_finite"] is False
    assert payload["anti_overclaim"]["reopen_sum_rho"] is False
    if payload["decision"]["classification"] == CLASS_COMPLEX:
        assert payload["scan"]["coverage"]["horizon_miss"] == 0
        assert payload["scan"]["H1"]["holds"] is False
        assert payload["scan"]["H4"]["novelty"] == "REPARAMETERIZATION"
        assert payload["scan"]["pareto"]["count"] >= 1
        assert payload["scan"]["same_run"]["groups_split"] >= 1
