"""CycleMin necklace slack. Not a length-11 census, Z5, or halt test."""

from __future__ import annotations

import json
from pathlib import Path

from research.juggler_sequence.cyclemin_fudge import (
    FAMILY_SLACK,
    chain_n0,
    prefix_cell_exponents,
)
from research.juggler_sequence.cyclemin_necklace import (
    CLASS_REFUTED,
    EXTRA_COUNT,
    FUDGE_A_MAX,
    FUDGE_COUNT,
    FORBIDDEN_THEOREMS,
    LEAN_THEOREMS,
    PIN_WORDS,
    classify,
    elementary_comparisons,
    lean_api_present,
    necklace_params,
    necklace_rows,
    probe_payload,
    render_markdown,
    write_artifacts,
)
from research.juggler_sequence.first_e_e4 import word_e4
from research.juggler_sequence.power_itineraries import ANTI_OVERCLAIM


def test_fifty_six_params_and_slack_identity():
    params = necklace_params()
    assert len(params) == 56
    assert all(a0 + a1 + a2 + a3 == 7 and a0 >= 2 for a0, a1, a2, a3 in params)
    elem = elementary_comparisons()
    assert all(elem.values()), elem
    for a0, a1, a2, a3 in params:
        word = word_e4(a0, a1, a2, a3)
        _a, _b, _g, _right, slack = prefix_cell_exponents(word)
        assert slack == FAMILY_SLACK == 139


def test_two_extra_words_miss_the_pin():
    rows = {row["word"]: row for row in necklace_rows()}
    assert len(rows) == 56
    assert sum(1 for row in rows.values() if row["in_fudge"]) == FUDGE_COUNT
    assert sum(1 for row in rows.values() if not row["in_fudge"]) == EXTRA_COUNT
    miss = PIN_WORDS
    for word in miss:
        row = rows[word]
        assert row["in_fudge"] is False
        assert row["slack"] == 139
        assert row["A"] > FUDGE_A_MAX
        assert row["first_start"] is not None
        assert row["chain_n0"] is not None
        assert row["chain_n0"] > row["first_start"]
        assert row["pin"] == [row["first_start"]]
        assert row["fires_at_first"] is False
    assert rows["OOEEEOOOOOE"]["first_start"] == 5
    assert rows["OOEEEOOOOOE"]["chain_n0"] == 55
    assert rows["OOOEEEOOOOE"]["first_start"] == 3
    assert rows["OOOEEEOOOOE"]["chain_n0"] == 42
    late = [row["word"] for row in rows.values() if not row["fires_at_first"]]
    assert set(late) == set(miss)


def test_early_even_word_has_large_A():
    a_exp, _b, _g, right, slack = prefix_cell_exponents("OOEEEOOOOOE")
    assert slack == 139
    assert a_exp == 30705
    assert chain_n0(a_exp, right) == 55


def test_lean_has_fudge_and_no_census():
    lean = lean_api_present()
    assert lean["sorry_free"] is True
    for name in LEAN_THEOREMS:
        assert lean[name] is True, name
    for name in FORBIDDEN_THEOREMS:
        assert lean[name] is True, name
    assert lean["paper_a_has_no_necklace"] is True


def test_classify_render_and_artifacts():
    data = probe_payload()
    assert classify(data["scan"], data["lean"])["classification"] == CLASS_REFUTED
    summary = data["scan"]["summary"]
    assert summary["word_count"] == 56
    assert summary["all_slack_family"] is True
    assert summary["late_words"] == ["OOEEEOOOOOE", "OOOEEEOOOOE"]
    assert summary["pin_hits"][0][0] == "OOEEEOOOOOE"
    text = render_markdown(data)
    assert CLASS_REFUTED in text
    assert "OOEEEOOOOOE" in text
    write_artifacts(data)
    stored = json.loads(
        Path(__file__).resolve().parents[3]
        .joinpath("docs/research/juggler_cyclemin_necklace.json")
        .read_text(encoding="utf-8")
    )
    assert stored["experiment"] == "juggler_cyclemin_necklace"
    assert stored["decision"]["classification"] == CLASS_REFUTED
    assert stored["anti_overclaim"]["length_eleven_census"] is False
    assert stored["scan"]["twenty_six_word_rescue"] is False
    assert dict(ANTI_OVERCLAIM)["global_termination"] is False
    dossier = (
        Path(__file__).resolve().parents[3]
        / "docs"
        / "problems"
        / "juggler_cyclemin_necklace.md"
    ).read_text(encoding="utf-8")
    assert "CLOSE" in dossier
    assert "no_cycle_itinerary_length_eleven" in dossier
    assert "OOEEEOOOOOE" in dossier
