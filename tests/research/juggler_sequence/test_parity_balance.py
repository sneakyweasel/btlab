"""Shared AboveAnchor parity-balance language. Not a halt test."""

from __future__ import annotations

import json

from research.experiments.outputs import artifact_path
from research.juggler_sequence.first_internal_oo import isolated_oe_exponent_ok
from research.juggler_sequence.parity_balance import (
    CLASS_CLOSED,
    CONTROLS,
    EXISTING_LEAN,
    FORBIDDEN_NEW_API,
    FORBIDDEN_THEOREMS,
    N_OPT,
    classify,
    isolated_equals_prefix_envelope,
    isolated_exponents,
    lean_api_present,
    o_star,
    o_then_e,
    ooe_repeat,
    optimize,
    prefix_survives,
    ratio_pair,
    render_markdown,
    run_probe,
    two_pow_le_three_pow,
    write_artifacts,
)


def test_survival_is_integer_exponent_compare():
    assert two_pow_le_three_pow(1, 1) is True
    assert two_pow_le_three_pow(1, 0) is False
    assert two_pow_le_three_pow(3, 2) is True
    assert two_pow_le_three_pow(4, 2) is False
    assert 2**3 == 8
    assert 3**2 == 9
    assert 2**4 == 16


def test_prefix_envelope_forbids_e_and_oe():
    assert prefix_survives("O") is True
    assert prefix_survives("E") is False
    assert prefix_survives("OE") is False
    assert prefix_survives("OOE") is True
    assert prefix_survives("OOEE") is False
    assert prefix_survives("O" * 8) is True


def test_isolated_bound_is_the_prefix_envelope():
    for a in range(0, 8):
        for r in range(0, 8):
            length, odd_count = isolated_exponents(a, r)
            assert length == a + 1 + 2 * r
            assert odd_count == a + r
            assert isolated_equals_prefix_envelope(a, r) is True
            assert isolated_oe_exponent_ok(a, r) == two_pow_le_three_pow(
                length, odd_count
            )


def test_optimizer_max_is_all_odd():
    for length in range(1, 9):
        opt = optimize(length)
        assert opt["max_odd"] == length
        assert opt["max_word"] == o_star(length)
        assert prefix_survives(opt["max_word"]) is True
        if length >= 3:
            assert opt["max_mixed_odd"] == length - 1
            assert opt["max_mixed_word"] == o_then_e(length)
            assert prefix_survives(opt["max_mixed_word"]) is True


def test_ooe_family_is_shared_admissible():
    block = ratio_pair("OOE")
    assert block["two_pow"] == 8
    assert block["three_pow"] == 9
    assert block["survives"] is True
    assert block["prefix_survives"] is True
    word = ooe_repeat(12)
    assert word == "OOE" * 4
    assert prefix_survives(word) is True
    assert ratio_pair(word)["odd_count"] == 8
    assert (1 << 12) <= 3**8


def test_probe_and_classify_close():
    scan = run_probe()
    lean = lean_api_present()
    decision = classify(scan, lean)
    assert decision["classification"] == CLASS_CLOSED
    assert scan["max_odd_equals_length"] is True
    assert scan["mixed_max_is_n_minus_one"] is True
    assert scan["isolated"]["identity_holds"] is True
    assert scan["falsifier_a"] is True
    assert scan["falsifier_c"] is True
    assert scan["leftover_envelope_ok"] is True
    assert scan["ooe"]["two_pow"] == 8
    assert scan["ooe"]["three_pow"] == 9
    assert scan["halt_theorem"] is False
    assert scan["cyclemin_in_language"] is False
    assert scan["parity_balance_lean"] is False
    assert scan["n_opt"] == N_OPT


def test_leftovers_stay_above_the_envelope_until_drop():
    scan = run_probe()
    for n in CONTROLS:
        row = scan["leftovers"][str(n)]
        assert row["last_survives"] is True
        assert row["drop_contracts"] is True
        assert row["last_two_pow"] <= row["last_three_pow"]
        assert row["drop_three_pow"] < row["drop_two_pow"]


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


def test_classify_render_and_artifacts(tmp_path):
    payload = write_artifacts(output_root=tmp_path)
    text = render_markdown(payload)
    assert CLASS_CLOSED in text
    from research.juggler_sequence.parity_balance import JSON_PATH

    data = json.loads(artifact_path(JSON_PATH, tmp_path).read_text(encoding="utf-8"))
    assert data["experiment"] == "juggler_parity_balance"
    assert data["decision"]["classification"] == CLASS_CLOSED
    assert data["anti_overclaim"]["independent_odd_density_upper_bound"] is False
    assert data["anti_overclaim"]["universal_odd_density"] is False


def test_dossier_boundary():
    from pathlib import Path

    repo = Path(__file__).resolve().parents[3]
    dossier = (repo / "docs" / "problems" / "juggler_parity_balance.md").read_text(
        encoding="utf-8"
    )
    paper = (repo / "formal" / "Problems" / "JugglerPaper.lean").read_text(
        encoding="utf-8"
    )
    assert "## Branch budget" in dossier
    assert "## Decision" in dossier
    assert "CLOSE" in dossier
    assert "2^{|w|}" in dossier or "2^{|w|}" in dossier
    assert "ParityBalance" not in paper
    assert "theorem no_juggler_escape" not in dossier
    assert "CycleMin" in dossier
