"""Prefix growth / retention balance. Not a halt or envelope-census test."""

from __future__ import annotations

import json

from research.juggler_sequence.growth_balance import (
    CLASS_CLOSED,
    CONTROLS,
    EXISTING_LEAN,
    FORBIDDEN_NEW_API,
    FORBIDDEN_THEOREMS,
    classify,
    exact_retention_compare,
    gamma_noncontracting,
    lean_api_present,
    leftover_tables,
    prefix_table,
    render_markdown,
    retention_required_holds,
    run_probe,
    write_artifacts,
)
from research.juggler_sequence.power_itineraries import floor_power


def test_retention_required_is_above_anchor():
    assert retention_required_holds(365, 1196) is True
    assert retention_required_holds(365, 34) is False
    assert exact_retention_compare(365, 1196, 2) is True
    assert exact_retention_compare(365, 34, 2) is False
    current = 9
    for k in range(1, 6):
        current = floor_power(current)
        assert exact_retention_compare(9, current, k) == (current >= 9)


def test_gamma_is_integer_exponent_compare():
    assert gamma_noncontracting(9, 14) is True
    assert gamma_noncontracting(9, 15) is False
    assert 3**9 == 19683
    assert 2**14 == 16384
    assert 2**15 == 32768


def test_365_stays_noncontracting_until_formal_drop():
    table = prefix_table(365)
    assert table["word"] == "OOEOOEOOEOOEOEE"
    assert table["runs"] == [2, 2, 2, 2, 1]
    assert table["above_gamma_fail"] == []
    assert table["identity_fail"] == []
    assert table["drop_formally_contracting"] is True
    last = table["last_above"]
    assert last["x"] == 1196
    assert last["k"] == 14
    assert last["three_pow_O"] == 19683
    assert last["two_pow_k"] == 16384
    drop = table["drop"]
    assert drop["x"] == 34
    assert drop["k"] == 15
    assert drop["three_pow_O"] == 19683
    assert drop["two_pow_k"] == 32768


def test_leftovers_obey_envelope_identity():
    tables = leftover_tables()
    for n in CONTROLS:
        row = tables[str(n)]
        assert row["above_gamma_fail"] == []
        assert row["identity_fail"] == []
        assert row["drop_formally_contracting"] is True
        assert row["last_above"]["gamma_ok"] is True
        assert row["drop"]["above"] is False


def test_probe_and_classify_close():
    scan = run_probe()
    lean = lean_api_present()
    decision = classify(scan, lean)
    assert decision["classification"] == CLASS_CLOSED
    assert scan["leftover_identity_fail"] is False
    assert scan["leftover_gamma_fail"] is False
    assert scan["leftover_formal_drop"] is True
    assert scan["sample_identity_ok"] is True
    assert scan["window_identity_ok"] is True
    assert scan["window_gamma_ok"] is True
    assert scan["halt_theorem"] is False
    assert scan["growth_balance_lean"] is False


def test_lean_api_without_new_layer():
    lean = lean_api_present()
    assert lean["sorry_free"] is True
    for name in EXISTING_LEAN:
        assert lean[name] is True, name
    for name in FORBIDDEN_THEOREMS:
        assert lean[f"has_{name}"] is False, name
    for name in FORBIDDEN_NEW_API:
        assert lean[f"has_api_{name}"] is False, name
    assert lean["new_lean_file"] is False
    assert lean["not_in_paper_barrel"] is True


def test_classify_render_and_artifacts():
    payload = write_artifacts()
    text = render_markdown(payload)
    assert CLASS_CLOSED in text
    from research.juggler_sequence.growth_balance import JSON_PATH

    data = json.loads(JSON_PATH.read_text(encoding="utf-8"))
    assert data["experiment"] == "juggler_growth_balance"
    assert data["decision"]["classification"] == CLASS_CLOSED
    assert data["anti_overclaim"]["independent_retention_budget"] is False


def test_dossier_boundary():
    from pathlib import Path

    repo = Path(__file__).resolve().parents[3]
    dossier = (repo / "docs" / "problems" / "juggler_growth_balance.md").read_text(
        encoding="utf-8"
    )
    paper = (repo / "formal" / "Problems" / "JugglerPaper.lean").read_text(
        encoding="utf-8"
    )
    assert "## Branch budget" in dossier
    assert "## Decision" in dossier
    assert "CLOSE" in dossier
    assert "REPARAMETERIZATION" in dossier
    assert "x_k >= n" in dossier or "x_k\\ge n" in dossier or "x_k\\ge n" in dossier
    assert "GrowthBalance" not in paper
    assert "theorem no_juggler_escape" not in dossier
