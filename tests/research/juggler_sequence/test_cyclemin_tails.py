"""CycleMin tails. Not a length-11 census, Z5, or halt test."""

from __future__ import annotations

import json
from pathlib import Path

from research.juggler_sequence.cyclemin_fudge import (
    chain_n0,
    prefix_cell_exponents,
)
from research.juggler_sequence.cyclemin_tails import (
    A0_HI,
    CHAIN_N0_MAX,
    CLASS_PROVED,
    FORBIDDEN_THEOREMS,
    LEAN_THEOREMS,
    PIN_MAX,
    classify,
    elementary_comparisons,
    family_slack,
    lean_api_present,
    pin_hits,
    probe_payload,
    render_markdown,
    write_artifacts,
)
from research.juggler_sequence.first_e_e4 import (
    first_expanding_a0,
    remainder_shapes,
    word_e4,
)
from research.juggler_sequence.power_itineraries import ANTI_OVERCLAIM


def test_slack_identity_and_o8eeee():
    assert family_slack(7) == 139
    assert family_slack(8) == 2465
    a_exp, _b, _g, right, slack = prefix_cell_exponents(word_e4(8, 0, 0, 0))
    assert slack == 2465
    assert chain_n0(a_exp, right) == 5
    elem = elementary_comparisons()
    assert all(elem.values()), elem


def test_first_tail_layer_and_pin():
    shapes = remainder_shapes()
    assert len(shapes) == 30
    n0s = []
    firsts = []
    for shape in shapes:
        a1 = int(shape["a1"])
        a2 = int(shape["a2"])
        a3 = int(shape["a3"])
        a0_star = first_expanding_a0(a1, a2, a3)
        assert a0_star is not None
        word = word_e4(a0_star + 1, a1, a2, a3)
        a_exp, _b, _g, right, slack = prefix_cell_exponents(word)
        odds = a0_star + 1 + a1 + a2 + a3
        assert odds == 8
        assert slack == family_slack(8) == 2465
        n0 = chain_n0(a_exp, right)
        assert n0 is not None
        assert 5 <= n0 <= CHAIN_N0_MAX
        assert pin_hits(word, PIN_MAX) == []
        n0s.append(n0)
        firsts.append(word)
    assert min(n0s) == 5
    assert max(n0s) == 7
    assert len(firsts) == 30


def test_scan_through_sixteen_pin_empty():
    for shape in remainder_shapes():
        a1 = int(shape["a1"])
        a2 = int(shape["a2"])
        a3 = int(shape["a3"])
        a0_star = first_expanding_a0(a1, a2, a3)
        assert a0_star is not None
        for a0 in range(a0_star + 1, A0_HI + 1):
            word = word_e4(a0, a1, a2, a3)
            a_exp, _b, _g, right, slack = prefix_cell_exponents(word)
            odds = a0 + a1 + a2 + a3
            assert slack == family_slack(odds)
            n0 = chain_n0(a_exp, right)
            assert n0 is not None
            assert n0 <= CHAIN_N0_MAX
            assert pin_hits(word, PIN_MAX) == []


def test_lean_has_fudge_and_no_assembler():
    lean = lean_api_present()
    assert lean["sorry_free"] is True
    for name in LEAN_THEOREMS:
        assert lean[name] is True, name
    for name in FORBIDDEN_THEOREMS:
        assert lean[name] is True, name
    assert lean["paper_a_has_no_tails"] is True


def test_classify_render_and_artifacts():
    data = probe_payload()
    assert classify(data["scan"], data["lean"])["classification"] == CLASS_PROVED
    summary = data["scan"]["summary"]
    assert summary["row_count"] == 367
    assert summary["all_slack_identity"] is True
    assert summary["max_chain_n0"] == CHAIN_N0_MAX
    assert summary["pin_hits"] == []
    assert summary["first_layer_all_fire"] is True
    assert summary["leftover_unused"] is True
    text = render_markdown(data)
    assert CLASS_PROVED in text
    assert "OOOOOOOOEEEE" in text
    write_artifacts(data)
    stored = json.loads(
        Path(__file__).resolve().parents[3]
        .joinpath("docs/research/juggler_cyclemin_tails.json")
        .read_text(encoding="utf-8")
    )
    assert stored["experiment"] == "juggler_cyclemin_tails"
    assert stored["decision"]["classification"] == CLASS_PROVED
    assert stored["anti_overclaim"]["length_eleven_census"] is False
    assert stored["scan"]["z5_cell"] is False
    assert dict(ANTI_OVERCLAIM)["global_termination"] is False
    dossier = (
        Path(__file__).resolve().parents[3]
        / "docs"
        / "problems"
        / "juggler_cyclemin_tails.md"
    ).read_text(encoding="utf-8")
    assert "PROMOTE" in dossier
    assert "no_cycle_itinerary_length_eleven" in dossier
    assert "no_cycleMin_four_even" in dossier
    assert "slack_of_four_even" in dossier
    assert "J-cyclemin-slack" in dossier
