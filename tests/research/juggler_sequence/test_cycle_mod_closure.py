"""Exact modular cycle closure. Not a halt test."""

from __future__ import annotations

import json
from pathlib import Path

from research.conjectures import get_conjecture
from research.juggler_sequence.cycle_closure import follows_block, oe_preimage_holds
from research.juggler_sequence.cycle_mod_closure import (
    MODULI,
    SPOTLIGHT,
    START,
    defect_width_collapses,
    even_preimage_realizable,
    first_last_mod,
    pair_meta,
    r_nec_pair_count,
    r_nec_source_count,
    r_wit_step,
    source_parity_ok,
)
from research.juggler_sequence.cycle_finance import PUBLISHED_FLOOR

REPO = Path(__file__).resolve().parents[3]
SUMMARY = (
    REPO
    / "data"
    / "research"
    / "juggler"
    / "cycle_finance"
    / "mod_closure"
    / "summary.json"
)


def test_oe_cell_is_the_exponent_cell():
    hits = 0
    x = 3
    while hits < 40:
        image = follows_block(x, "OE")
        if image is not None:
            assert oe_preimage_holds(x, image)
            hits += 1
        x += 2


def test_r_nec_is_parity_mod_8():
    assert r_nec_source_count(8, True) == 4
    assert r_nec_source_count(8, False) == 4
    assert r_nec_pair_count(8, True) == 32
    assert r_nec_pair_count(8, False) == 32
    for residue in range(8):
        assert source_parity_ok(residue, 8, True) is (residue % 2 == 1)
        assert source_parity_ok(residue, 8, False) is (residue % 2 == 0)
    assert r_nec_pair_count(9, True) == 81
    assert r_nec_source_count(9, True) == 9


def test_even_cell_full_at_finance_scale():
    assert not defect_width_collapses(1296)
    y = START + 8
    for src in range(8):
        if src % 2 == 1:
            continue
        for dst in range(8):
            lift = y + ((dst - y) % 8)
            assert even_preimage_realizable(src, dst, 8, lift)


def test_odd_wit_hits_every_target_mod_8():
    pairs = r_wit_step(8, odd=True, per_class=24)
    assert len(pairs) == 32
    sources = {src for src, _ in pairs}
    targets = {dst for _, dst in pairs}
    assert sources == {1, 3, 5, 7}
    assert targets == set(range(8))


def test_spotlight_pairs():
    row = pair_meta(25781)
    assert row["L"] == 25781
    assert row["o"] == 16266
    assert row["e"] == 9515
    assert row["ooe_count"] == 6751
    assert row["oe_count"] == 2764
    tight = pair_meta(55293)
    assert tight["L"] == 55293
    assert tight["o"] == 34886
    assert tight["ooe_count"] == 14479
    assert tight["oe_count"] == 5928


def test_first_last_are_different_indices():
    row = first_last_mod(START, 8)
    assert row["same_slot"] is False
    assert row["reduces_to_overshoot"] is True
    assert row["last_even_covers_all"] is True


def test_mod_closure_scan_closes():
    payload = json.loads(SUMMARY.read_text(encoding="utf-8"))
    assert payload["emptied_count"] == 0
    assert payload["emptied_lengths"] == []
    assert payload["oe_is_exponent_cell"] is True
    assert payload["all_spotlights_diagonal"] is True
    assert payload["all_spotlights_nec_diagonal"] is True
    assert payload["all_reduces_to_parity"] is True
    assert payload["all_counts_return"] is True
    assert payload["no_defect_width_collapse"] is True
    assert payload["scanned_other_97"] is False
    assert payload["level_c"] is False
    assert payload["halt_theorem"] is False
    assert payload["no_cycle_all_lengths"] is False
    assert payload["moduli"] == list(MODULI)
    assert payload["floor"] == PUBLISHED_FLOOR
    for length in SPOTLIGHT:
        spot = payload["spotlights"][str(length)]
        assert spot["all_diagonal_nonempty"] is True
        assert spot["all_reduces_to_parity"] is True
        assert spot["level_c"] is False
        assert spot["first_last_mod8"]["reduces_to_overshoot"] is True
        assert len(spot["moduli"]) == len(MODULI)
        for row in spot["moduli"]:
            assert row["nec_diagonal_nonempty"] is True
            assert row["diagonal_nonempty"] is True
            assert row["local"]["nec_is_first_letter_parity"] is True
            assert row["defect_width_collapses"] is False


def test_dossier_and_conjecture_record_close():
    dossier = (
        REPO / "docs" / "problems" / "juggler_cycle_mod_closure.md"
    ).read_text(encoding="utf-8")
    assert "## Branch budget" in dossier
    assert "## Decision" in dossier
    assert "## Publication assessment" in dossier
    assert "**CLOSE**" in dossier
    assert "mod_closure/summary.json" in dossier
    assert "juggler_cycle_mod_closure_leftover_killer" in dossier
    rec = get_conjecture("juggler_cycle_mod_closure_leftover_killer")
    assert rec["status"] == "REFUTED"
