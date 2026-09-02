"""CycleMin entry excursion. Not a halt test."""

from __future__ import annotations

import json
from pathlib import Path

from research.conjectures import get_conjecture
from research.juggler_sequence.cycle_budget_opt import oe_start_min
from research.juggler_sequence.cycle_entry_excursion import (
    entry_even_preimage,
    entry_row,
    finance_classes,
    packed_closing,
    run_layer,
)
from research.juggler_sequence.cycle_ordered_excursion import first_a2

REPO = Path(__file__).resolve().parents[3]
DOSSIER = REPO / "docs" / "problems" / "juggler_cycle_entry_excursion.md"
SUMMARY = (
    REPO
    / "data"
    / "research"
    / "juggler"
    / "cycle_finance"
    / "entry_excursion"
    / "summary.json"
)

N = 1_000_001


def test_dossier_has_triage_and_closed_gates():
    text = DOSSIER.read_text(encoding="utf-8")
    assert "## Branch budget" in text
    assert "Mathematical target" in text
    assert "## Closed-bridge gates" in text
    assert "## Decision" in text
    assert "## Publication assessment" in text
    assert "**CLOSE**" in text
    assert "oe_start_min" in text
    assert "Do **not** raise" in text


def test_entry_cell_skips_odd_square():
    cell = entry_even_preimage(N)
    assert cell["lo"] == N * N
    assert cell["first_even"] == N * N + 1
    assert cell["first_even"] % 2 == 0
    assert cell["contains_n2"] is False
    assert cell["count"] == N
    assert cell["width"] == 2 * N + 1


def test_cheapest_entry_is_oe_start():
    oe = oe_start_min(N)
    assert oe == 100000135
    layer = run_layer(N, 1)
    assert layer["n_ge_n"] == 33
    assert layer["min_v"] == oe
    row = entry_row(oe, 1, N)
    assert row is not None
    assert row["tube_ge_n"] is True
    assert row["landing"] == N
    assert row["tax_vs_oe"] == 0.0
    assert N * N < row["peak"] < (N + 1) * (N + 1)


def test_deeper_runs_do_not_enter_while_ge_n():
    for a in (2, 3, 4):
        layer = run_layer(N, a)
        assert layer["n_ge_n"] == 0
        assert layer["envelope_below_n"] is True


def test_cheap_ooe_classes_do_not_enter():
    rows = {row["name"]: row for row in finance_classes(N)}
    assert rows["cyclemin"]["enters_n"] is False
    assert rows["unique_visit_next"]["enters_n"] is False
    assert rows["oe_start"]["enters_n"] is True


def test_packed_word_already_ends_oe():
    closing = packed_closing()
    assert closing["ends_oe"] is True
    assert closing["ends_21"] is True
    assert closing["n_oe"] == 2764


def test_first_ooe_overshoots_return_cell():
    v = first_a2(N)
    assert v == 1_000_057
    rec = entry_row(v, 2, N)
    assert rec is None


def test_science_artifact_closes():
    payload = json.loads(SUMMARY.read_text(encoding="utf-8"))
    assert payload["bound"] == "entry_excursion"
    assert payload["L"] == 25781
    assert payload["n"] == N
    assert payload["entry_cell"]["first_even"] == N * N + 1
    decision = payload["decision"]
    assert decision["decision"] == "CLOSE"
    assert decision["classification"] == "ENTRY_EXCURSION_CLOSED"
    assert decision["only_oe_entry"] is True
    assert decision["tax_zero"] is True
    assert decision["at_oe_scale"] is True
    assert decision["all_valleys_compatible"] is False
    assert decision["cheap_ooe_enters_n"] is False
    assert decision["packed_ends_oe"] is True
    assert decision["closing_conflict"] is False
    assert decision["leftover_killer"] is False
    assert decision["false_all_would_kill"] is False
    assert decision["halt_theorem"] is False
    assert decision["raise_n0"] is False
    assert decision["open_55293"] is False
    assert payload["finance"]["min_v"] == payload["finance"]["oe_start"]
    assert payload["charged_excludes"]["parity_excludes"] is False
    assert payload["charged_excludes"]["budget_excludes"] is False
    assert payload["ooe_overshoot"]["peak_overshoots_return"] is True
    assert payload["slack"]["one_entry_inside_slack"] is True


def test_dossier_and_conjecture_record_close():
    dossier = DOSSIER.read_text(encoding="utf-8")
    assert "**CLOSE**" in dossier
    rec = get_conjecture("juggler_cycle_entry_excursion")
    assert rec["status"] == "REFUTED"
    assert rec["counterexamples"]
