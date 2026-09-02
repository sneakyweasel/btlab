"""m-cycle finance. Not a halt test, not a no-cycle-of-any-length test."""

from __future__ import annotations

import json
from pathlib import Path

from research.juggler_sequence.cycle_m_finance import (
    CLASS_CLOSED,
    CLASS_GREEN,
    CLASS_INCOMPLETE,
    CLASS_PARK,
    EXISTING_LEAN,
    FORBIDDEN_LEAN_FILES,
    FORBIDDEN_NEW_API,
    FORBIDDEN_THEOREMS,
    LEAN_CYCLE_FLOOR,
    LEFTOVER_LENGTHS,
    analytic_kills_at_floor,
    circuit_census,
    classify,
    extract_circuits,
    lean_api_present,
    leftover_table,
    probe_payload,
    render_markdown,
    steiner_rhs,
)

REPO = Path(__file__).resolve().parents[3]


def test_nine_is_one_ooe_circuit():
    circuits = extract_circuits(9)
    assert len(circuits) == 1
    circuit = circuits[0]
    assert circuit["n_i"] == 9
    assert circuit["k"] == 2
    assert circuit["y"] == 140
    assert circuit["l"] == 1
    assert circuit["n_next"] == 11
    assert circuit["L_k"] == 3
    assert circuit["mu"] == 9


def test_terminal_collapse_inflates_raw_ratio_not_cycle_like():
    row = circuit_census(365)
    assert row["m"] == 5
    assert row["cycle_like_m"] == 4
    assert row["full_over_minima"] > 10.0
    assert row["cycle_like_full_over_minima"] < 2.0
    assert row["cycle_like_steiner_ok"] is True
    assert row["circuits"][-1]["n_next"] == 5


def test_analytic_bound_kills_nineteen_m1_and_thirty_all_m():
    leftovers = {row["L"]: row for row in leftover_table()}
    nineteen = leftovers[19]
    assert nineteen["o"] == 12
    assert nineteen["lean_survives_floor_53"] is True
    assert nineteen["analytic_kills_m1"] is True
    assert nineteen["analytic_kills_all_m"] is False
    assert nineteen["new_exclusions"] == [1]
    thirty = leftovers[30]
    assert thirty["o"] == 19
    assert thirty["analytic_kills_all_m"] is True
    assert thirty["new_exclusions"] == list(range(1, 12))
    eighty_four = leftovers[84]
    assert eighty_four["analytic_kills_m1"] is False
    assert eighty_four["analytic_kills_all_m"] is False
    assert eighty_four["new_exclusions"] == []


def test_steiner_rhs_monotone_in_m():
    rhs = [steiner_rhs(LEAN_CYCLE_FLOOR, 19, 12, m) for m in range(1, 8)]
    assert rhs == sorted(rhs)
    assert analytic_kills_at_floor(19, 12, 0.01345963145485576, 1) is True
    assert analytic_kills_at_floor(19, 12, 0.01345963145485576, 7) is False


def test_probe_and_classify_vocabulary():
    payload = probe_payload()
    assert payload["experiment"] == "juggler_cycle_m_finance"
    assert payload["engine_control_layer_modified"] is False
    assert payload["decision"]["classification"] in {
        CLASS_GREEN,
        CLASS_PARK,
        CLASS_CLOSED,
        CLASS_INCOMPLETE,
    }
    assert payload["decision"]["classification"] == CLASS_GREEN
    assert payload["anti_overclaim"]["halt_theorem"] is False
    assert payload["anti_overclaim"]["no_cycle_all_lengths"] is False
    assert payload["anti_overclaim"]["new_lean"] is False
    assert payload["scan"]["kills_length_nineteen_m1"] is True
    assert payload["scan"]["kills_length_thirty_all_m"] is True
    assert 30 in payload["scan"]["lean_surviving_scan"]["killed_all_m"]
    assert payload["scan"]["max_cycle_like_ratio"] < 2.0
    text = render_markdown(payload)
    assert "Not a halt theorem" in text
    lean = lean_api_present()
    assert classify(payload["scan"], lean)["classification"] == CLASS_GREEN


def test_lean_api_forbids_new_m_finance_layer():
    lean = lean_api_present()
    assert lean["sorry_free"] is True
    for name in EXISTING_LEAN:
        assert lean[name] is True, name
    for name in FORBIDDEN_THEOREMS:
        assert lean[f"has_{name}"] is False, name
    for name in FORBIDDEN_NEW_API:
        assert lean[f"has_api_{name}"] is False, name
    assert lean["cycle_finance_present"] is True
    assert lean["no_extra_m_finance_file"] is True
    assert lean["not_in_paper_barrel"] is True
    for path in FORBIDDEN_LEAN_FILES:
        assert path.is_file() is False


def test_science_summary_is_green():
    summary = json.loads(
        (
            REPO / "data" / "research" / "juggler" / "cycle_m_finance" / "summary.json"
        ).read_text(encoding="utf-8")
    )
    assert summary["classification"] == CLASS_GREEN
    assert summary["kills_length_nineteen_m1"] is True
    assert summary["kills_length_thirty_all_m"] is True
    assert 30 in summary["killed_all_m"]


def test_dossier_boundary():
    dossier = (
        REPO / "docs" / "problems" / "juggler_cycle_m_finance.md"
    ).read_text(encoding="utf-8")
    paper = (REPO / "formal" / "Problems" / "JugglerPaper.lean").read_text(
        encoding="utf-8"
    )
    assert "## Branch budget" in dossier
    assert "## Decision" in dossier
    assert "## Publication assessment" in dossier
    assert "**PROMOTE**" in dossier
    assert "simons-de-weger-2005-collatz-m-cycles" in dossier
    assert "cycleMin_finance" in dossier
    assert "juggler_cycle_finance_note.md" in dossier
    assert tuple(LEFTOVER_LENGTHS) == (19, 30, 84)
    assert "theorem no_cycle_itinerary_any_length" not in dossier
    assert "CycleMFinance" not in paper
    assert "cycle_m_finance" not in paper
    assert "CircuitFinance" not in paper
