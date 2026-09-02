"""Minimal-bad survival signatures. Not a halt test."""

from __future__ import annotations

import json
from pathlib import Path

from research.juggler_sequence.lean_paths import MINIMAL, MINIMAL_CLOSURE, PROGRESS, has_named
from research.juggler_sequence.power_itineraries import floor_power
from research.juggler_sequence.minimal_survival import (
    ANTI,
    CLASS_COMPLEX,
    CLOSED_IMPORT_TOKENS,
    DATA_DIR,
    DOSSIER_PATH,
    JSON_PATH,
    LEAN_THEOREMS,
    even_one_step_all,
    lean_api_present,
    leftover_equals_odd_odd,
    odd_one_step_none,
    signature_row,
)


def test_even_is_one_step_odd_is_not():
    even = signature_row(8)
    assert even["parity"] == "even"
    assert even["one_step"] is True
    assert even["leftover"] is False
    assert floor_power(8) == 2
    odd = signature_row(9)
    assert odd["parity"] == "odd"
    assert odd["word2"] == "OO"
    assert odd["one_step"] is False
    assert odd["two_step"] is False
    assert odd["leftover"] is True
    oe = signature_row(7)
    assert oe["word2"] == "OE"
    assert oe["one_step"] is False
    assert oe["two_step"] is True
    assert oe["leftover"] is False


def test_leftover_equals_oo_on_small_range():
    rows = [signature_row(n) for n in range(2, 200)]
    assert leftover_equals_odd_odd(rows)["ok"]
    assert even_one_step_all(rows)
    assert odd_one_step_none(rows)
    leftover = [row for row in rows if row["leftover"]]
    assert leftover
    assert all(row["word2"] == "OO" for row in leftover)


def test_anti_overclaim_and_closed_imports():
    assert ANTI["global_termination"] is False
    assert ANTI["minimality_plus_inverse_is_new"] is False
    assert ANTI["pred_closure_is_new_induction"] is False
    assert ANTI["even_map_is_half_square"] is False
    assert ANTI["reopen_minimal_counterexample"] is False
    assert ANTI["reopen_stopping_prefix"] is False
    source = (
        Path(__file__).resolve().parents[3]
        / "src"
        / "research"
        / "juggler_sequence"
        / "minimal_survival.py"
    )
    text = source.read_text(encoding="utf-8")
    for token in CLOSED_IMPORT_TOKENS:
        assert f"juggler_sequence.{token}" not in text
    assert "def good_closure" not in text
    assert "T(2k)=k^2" not in text or "not `T(2k)=k^2`" in text


def test_lean_api_cited_not_extended():
    lean = lean_api_present()
    assert lean["sorry_free"]
    for names in LEAN_THEOREMS.values():
        for name in names:
            assert lean[name], name
    assert has_named(MINIMAL.read_text(encoding="utf-8"), "MinimalNonTerm")
    assert has_named(MINIMAL_CLOSURE.read_text(encoding="utf-8"), "predClosure_iff_reachesOne")
    assert has_named(PROGRESS.read_text(encoding="utf-8"), "unresolved_is_odd_odd")
    src = MINIMAL_CLOSURE.read_text(encoding="utf-8")
    assert "minimal_bad_impossible" not in src
    assert "predecessor_cover_complete" not in src


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
    assert data["experiment"] == "juggler_minimal_survival"
    assert data["cuda_used"] is False
    assert data["anti_overclaim"]["global_termination"] is False
    assert data["leftover_eq_oo"]["ok"] is True
    assert data["even_one_step_all"] is True
    assert data["odd_one_step_none"] is True
    assert data["leftover_descents"]["all_dropped"] is True
    assert data["novelty"]["new_Phi"] == "REFUTED"
    assert data["decision"]["classification"] == CLASS_COMPLEX
    assert data["decision"]["branch"] == "CLOSE"
    for name in ("manifest.json", "signatures.csv", "leftover.jsonl"):
        assert (DATA_DIR / name).is_file(), name
