"""CycleMin (n+1)/n fudge. Not a length-11 census or halt test."""

from __future__ import annotations

import json
from pathlib import Path

from research.juggler_sequence.cyclemin_fudge import (
    CHAIN_N0_MAX,
    CLASS_PROVED,
    FAMILY_SLACK,
    FORBIDDEN_THEOREMS,
    LEAN_THEOREMS,
    PIN_MAX,
    absorb_even,
    absorb_odd,
    chain_beats,
    chain_n0,
    classify,
    elementary_comparisons,
    exponents_after,
    first_prefix_start,
    lean_api_present,
    pin_below,
    prefix_cell_exponents,
    render_markdown,
    trailing_even_run,
    write_artifacts,
)
from research.juggler_sequence.first_e_e4 import (
    first_expanding_a0,
    remainder_shapes,
    word_e4,
)
from research.juggler_sequence.power_itineraries import ANTI_OVERCLAIM


def _layer_words() -> list[str]:
    words = []
    for shape in remainder_shapes():
        a0 = first_expanding_a0(int(shape["a1"]), int(shape["a2"]), int(shape["a3"]))
        assert a0 is not None
        words.append(word_e4(a0, int(shape["a1"]), int(shape["a2"]), int(shape["a3"])))
    return words


def test_exponent_machine_matches_o7_and_o6():
    assert absorb_odd((0, 0, 0)) == (3, 0, 2)
    assert absorb_even((0, 0, 0)) == (1, 0, 2)
    assert exponents_after("OOOOOOO") == (6177, 3990, 128)
    assert exponents_after("OOOOOO") == (1995, 1266, 64)
    assert prefix_cell_exponents("OOOOOOOEEEE") == (6177, 3990, 128, 6038, 139)
    assert trailing_even_run("OOOOOOOEEEE") == 4
    assert trailing_even_run("OOOOOOEOEEE") == 3
    assert chain_n0(6177, 6038) == 16
    assert chain_beats(16, 6177, 6038) is True
    assert chain_beats(15, 6177, 6038) is False
    elem = elementary_comparisons()
    assert all(elem.values()), elem


def test_slack_is_identically_139_and_n0_below_thirty():
    words = _layer_words()
    assert len(words) == 30
    n0s = []
    firsts = []
    for word in words:
        a_exp, _b, _gamma, right, slack = prefix_cell_exponents(word)
        assert slack == FAMILY_SLACK == 139
        assert right == a_exp - 139
        n0 = chain_n0(a_exp, right)
        assert n0 is not None
        assert 16 <= n0 <= CHAIN_N0_MAX
        assert chain_beats(n0, a_exp, right)
        assert not chain_beats(n0 - 1, a_exp, right)
        first = first_prefix_start(word)
        assert first is not None
        assert first >= 37
        assert n0 < first
        n0s.append(n0)
        firsts.append(first)
    assert min(n0s) == 16
    assert max(n0s) == CHAIN_N0_MAX
    assert min(firsts) == 37
    assert max(firsts) == 2935
    assert pin_below(words, PIN_MAX) == []


def test_lean_has_o7_and_no_census():
    lean = lean_api_present()
    assert lean["sorry_free"] is True
    for name in LEAN_THEOREMS:
        assert lean[name] is True, name
    for name in FORBIDDEN_THEOREMS:
        assert lean[name] is True, name


def test_classify_render_and_artifacts():
    from research.juggler_sequence.cyclemin_fudge import JSON_PATH, probe_payload

    data = probe_payload()
    assert classify(data["scan"], data["lean"])["classification"] == CLASS_PROVED
    assert data["scan"]["summary"]["all_slack_family"] is True
    assert data["scan"]["pin"] == []
    text = render_markdown(data)
    assert CLASS_PROVED in text
    assert "OOOOOOOEEEE" in text
    write_artifacts(data)
    stored = json.loads(JSON_PATH.read_text(encoding="utf-8"))
    assert stored["experiment"] == "juggler_cyclemin_fudge"
    assert stored["decision"]["classification"] == CLASS_PROVED
    assert stored["anti_overclaim"]["length_eleven_census"] is False
    assert stored["scan"]["twenty_three_word_scan"] is False
    assert dict(ANTI_OVERCLAIM)["global_termination"] is False
    repo = Path(__file__).resolve().parents[3]
    dossier = (repo / "docs" / "problems" / "juggler_cyclemin_fudge.md").read_text(
        encoding="utf-8"
    )
    assert "PROMOTE" in dossier
    assert "no_cycle_itinerary_length_eleven" in dossier
