"""Stopping-time prefix phase. Not a halt test."""

from __future__ import annotations

import json
from pathlib import Path

from research.juggler_sequence.lean_paths import MINIMAL_CLOSURE, has_named
from research.juggler_sequence.minimal_counterexample import stopping_times
from research.juggler_sequence.power_itineraries import floor_power
from research.juggler_sequence.stopping_prefix import (
    ANTI,
    CLASS_COMPLEX,
    CLOSED_IMPORT_TOKENS,
    DATA_DIR,
    DOSSIER_PATH,
    JSON_PATH,
    LEAN_THEOREMS,
    even_successor_holds,
    first_gaps_odd_when_f_ge_2,
    lean_api_present,
    prefix_from_tau,
    running_max_tau,
)


def _hand_tau() -> list[int | None]:
    """τ on 1..9 from exact floor_power walks, padded as a full list."""

    return [None, 0, 1, 6, 2, 5, 2, 4, 2, 7]


def test_prefix_inverts_running_max():
    tau = _hand_tau()
    running = running_max_tau(tau)
    assert running == [0, 1, 6, 6, 6, 6, 6, 6, 7]
    rows = prefix_from_tau(tau)
    by_r = {row["r"]: row for row in rows}
    assert by_r[0]["F_tau"] == 1
    assert by_r[0]["b_r"] == 2
    assert by_r[1]["F_tau"] == 2
    assert by_r[5]["F_tau"] == 2
    assert by_r[6]["F_tau"] == 8
    assert by_r[7]["F_tau"] == 9
    for row in rows:
        f_val = row["F_tau"]
        r = row["r"]
        assert max(tau[1 : f_val + 1]) <= r
        if f_val < len(tau) - 1:
            assert tau[f_val + 1] > r
            assert row["b_r"] == f_val + 1


def test_hand_tau_matches_stopping_times():
    computed = stopping_times(9, horizon=100)
    assert computed[1:] == _hand_tau()[1:]
    assert floor_power(3) == 5
    assert floor_power(9) == 27


def test_even_successor_bound_on_hand_tau():
    tau = _hand_tau()
    rows = prefix_from_tau(tau)
    for row in rows:
        assert even_successor_holds(tau, row["F_tau"], row["r"])


def test_first_gaps_with_f_ge_2_are_odd_on_hand_tau():
    tau = _hand_tau()
    rows = prefix_from_tau(tau)
    check = first_gaps_odd_when_f_ge_2(rows, 9)
    assert check["checked"] >= 1
    assert check["all_odd"]
    assert check["exceptions"] == []
    assert rows[0]["b_r"] == 2
    assert rows[0]["F_tau"] == 1


def test_anti_overclaim_and_closed_imports():
    assert ANTI["global_termination"] is False
    assert ANTI["computed_F_tau_is_a_theorem"] is False
    assert ANTI["interval_amplification"] is False
    assert ANTI["reopen_windowed_closure"] is False
    source = (
        Path(__file__).resolve().parents[3]
        / "src"
        / "research"
        / "juggler_sequence"
        / "stopping_prefix.py"
    )
    text = source.read_text(encoding="utf-8")
    for token in CLOSED_IMPORT_TOKENS:
        assert f"juggler_sequence.{token}" not in text
    assert "def good_closure" not in text
    assert "from research.juggler_sequence.minimal_counterexample import stopping_times" in text


def test_lean_api_cited_not_extended():
    lean = lean_api_present()
    assert lean["sorry_free"]
    for name in LEAN_THEOREMS:
        assert lean[name], name
    src = MINIMAL_CLOSURE.read_text(encoding="utf-8")
    assert "sorry" not in src
    assert "admit" not in src
    assert has_named(src, "even_good_of_sqrt_le")
    assert has_named(src, "odd_not_pred_of_le")
    assert "goodAt_interval_amplification" not in src
    assert "prefix_growth_theorem" not in src


def test_dossier_headings():
    text = DOSSIER_PATH.read_text(encoding="utf-8")
    assert "## Branch budget" in text
    assert "## Decision" in text
    assert "## Publication assessment" in text
    section = text.split("## Decision", 1)[1]
    assert any(word in section for word in ("PROMOTE", "PARK", "CLOSE"))


def test_artifacts_if_present():
    if not JSON_PATH.is_file():
        return
    data = json.loads(JSON_PATH.read_text(encoding="utf-8"))
    assert data["experiment"] == "juggler_stopping_prefix"
    assert data["cuda_used"] is False
    assert data["anti_overclaim"]["global_termination"] is False
    assert data["anti_overclaim"]["computed_F_tau_is_a_theorem"] is False
    assert data["all_reach_one"] is True
    assert data["even_successor_ok"] is True
    assert data["first_gaps_odd"]["all_odd"] is True
    assert data["decision"]["classification"] == CLASS_COMPLEX
    assert data["decision"]["branch"] == "CLOSE"
    for name in ("manifest.json", "prefix.csv", "first_gaps.jsonl"):
        assert (DATA_DIR / name).is_file(), name
