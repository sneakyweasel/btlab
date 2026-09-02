"""First leftover cube-odd lift is not forced below n^8."""

from __future__ import annotations

import json

from research.juggler_sequence.first_lift_eighth import (
    CLASS_REFUTED,
    FORBIDDEN_THEOREMS,
    LEAN_THEOREMS,
    UNSAFE_WORD,
    WITNESS_4309,
    WITNESS_5791,
    boundary_perfect_power,
    classify,
    envelope_gap,
    envelope_implies_eighth,
    first_lift_row,
    lean_api_present,
    leftover_first_eighth,
    render_markdown,
    run_probe,
    smaller_unsafe_first_even,
    witness_4309,
    witness_501_later,
    witness_5791,
    write_artifacts,
)
from research.juggler_sequence.power_itineraries import floor_power


def test_named_leftovers_are_safe_and_enveloped():
    rows = leftover_first_eighth()
    expected = {
        365: "OOEOOEOOEO",
        501: "OOEOO",
        1517: "OOEOOEOOEOEOO",
        6187: "OOEOO",
    }
    for n, word in expected.items():
        row = rows[n]
        assert row["hit"] is True
        assert row["word"] == word
        assert row["y_even"] is True
        assert row["x3_lt_n8"] is True
        assert row["z_lt_sq"] is True
        assert row["envelope_implies_eighth"] is True
        assert row["x"] ** 3 < n**8


def test_4309_is_first_lift_falsifier():
    n, word, x = WITNESS_4309
    row = witness_4309()
    assert row["n"] == n
    assert row["x"] == x
    assert row["word"] == word
    assert row["is_first_lift"] is True
    assert row["y_even"] is True
    assert row["x3_lt_n8"] is False
    assert row["z_lt_sq"] is False
    assert row["envelope_implies_eighth"] is False
    assert x**3 >= n**8
    assert floor_power(x) % 2 == 0


def test_5791_is_long_leftover_falsifier():
    n, word, x = WITNESS_5791
    row = witness_5791()
    assert row["x"] == x
    assert row["word"] == word
    assert row["refutes_first_eighth"] is True
    assert row["long_above_anchor"] is True
    assert row["drop_at"] == 42


def test_501_later_is_not_first():
    row = witness_501_later()
    assert row["is_first_lift"] is False
    assert row["first_x3_lt_n8"] is True
    assert row["x3_lt_n8"] is False
    assert row["y_even"] is True
    assert row["z_lt_sq"] is False


def test_envelope_gap_is_the_ooeooeoo_loss():
    assert envelope_implies_eighth(2, 2) is True  # OO
    assert envelope_implies_eighth(5, 4) is True  # OOEOO
    assert envelope_implies_eighth(8, 6) is False  # OOEOOEOO
    assert envelope_implies_eighth(10, 7) is True  # OOEOOEOOEO
    assert envelope_implies_eighth(13, 9) is True  # 1517 word
    assert envelope_gap(8, 6) == 2187 - 2048
    assert envelope_gap(5, 4) == 243 - 256
    assert UNSAFE_WORD == "OOEOOEOO"


def test_boundary_equality_has_odd_image():
    for m in (3, 5, 7):
        row = boundary_perfect_power(m)
        assert row["equal"] is True
        assert row["x_odd"] is True
        assert row["in_cube_band"] is True
        assert row["y_even"] is False
        assert row["y_is_m12"] is True


def test_predecessor_of_first_cube_odd_is_odd():
    for n in (365, 501, 1517, 6187, 4309, 5791):
        row = first_lift_row(n)
        assert row is not None
        assert row["pred_even"] is False


def test_no_smaller_odd_unsafe_first_lift():
    assert smaller_unsafe_first_even(WITNESS_4309[0]) == []


def test_probe_and_classify_refuted():
    scan = run_probe()
    lean = lean_api_present()
    decision = classify(scan, lean)
    assert decision["classification"] == CLASS_REFUTED
    assert scan["falsifier_a"] is True
    assert scan["leftovers_safe_and_enveloped"] is True
    assert scan["first_is_not_later"] is True
    assert scan["letter_chain"] is False
    assert scan["q_return"] is False


def test_lean_api_without_halt():
    lean = lean_api_present()
    assert lean["sorry_free"] is True
    for name in LEAN_THEOREMS:
        assert lean[name] is True, name
    for name in FORBIDDEN_THEOREMS:
        assert lean[f"has_{name}"] is False, name
    assert lean["in_laboratory_barrel"] is True
    assert lean["not_in_paper_barrel"] is True
    assert lean["no_new_first_lift_lean"] is True


def test_classify_render_and_artifacts():
    payload = write_artifacts()
    text = render_markdown(payload)
    assert CLASS_REFUTED in text
    from research.juggler_sequence.first_lift_eighth import JSON_PATH

    data = json.loads(JSON_PATH.read_text(encoding="utf-8"))
    assert data["experiment"] == "juggler_first_lift_eighth"
    assert data["decision"]["classification"] == CLASS_REFUTED
    assert data["anti_overclaim"]["first_lift_always_eighth"] is False


def test_dossier_boundary():
    from pathlib import Path

    repo = Path(__file__).resolve().parents[3]
    dossier = (repo / "docs" / "problems" / "juggler_first_lift_eighth.md").read_text(
        encoding="utf-8"
    )
    paper = (repo / "formal" / "Problems" / "JugglerPaper.lean").read_text(
        encoding="utf-8"
    )
    assert "## Branch budget" in dossier
    assert "## Decision" in dossier
    assert "PARK" in dossier
    assert "22357213525" in dossier
    assert "odd_even_eighth_lt_sq" not in paper
    assert "theorem no_juggler_escape" not in dossier
