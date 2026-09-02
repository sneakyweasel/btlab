"""25781 finance-extremizer discrepancy. Not a halt test."""

from __future__ import annotations

import json
from pathlib import Path

from research.conjectures import get_conjecture
from research.juggler_sequence.cycle_almost_search import PHASE1_L
from research.juggler_sequence.cycle_budget_opt import budget_sum_terms, run_type_counts
from research.juggler_sequence.cycle_extremizer_discrepancy import (
    ARCHIVED_TAGS,
    START,
    charged_excludes,
    extra_even_word,
    extra_odd_word,
    first_oe_letter_index,
    graded_words,
    packed_necklace,
    walk_first_blocks,
    word_sum_terms,
)
from research.juggler_sequence.cycle_finance import MIN_STATE, PUBLISHED_FLOOR, o_min_and_theta
from research.juggler_sequence.cycle_ordered_excursion import excursion_map, ooe_preimage_holds

REPO = Path(__file__).resolve().parents[3]
DOSSIER = REPO / "docs" / "problems" / "juggler_cycle_extremizer_discrepancy.md"
SUMMARY = (
    REPO
    / "data"
    / "research"
    / "juggler"
    / "cycle_finance"
    / "extremizer_discrepancy"
    / "summary.json"
)


def test_dossier_has_triage_and_closed_bridge_gates():
    text = DOSSIER.read_text(encoding="utf-8")
    assert "## Branch budget" in text
    assert "Mathematical target" in text
    assert "## Closed-bridge gates" in text
    assert "juggler_cycle_finance_cell_bridge" in text
    assert "Do **not** raise \\(N_0\\)" in text or "Do **not** raise $N_0$" in text or "Do **not** raise" in text
    assert "1054" in text
    assert "55293" in text
    assert "No N0" in text or "no N0" in text or "not raise" in text


def test_packed_necklace_is_the_two_type_extremizer():
    neck = packed_necklace()
    odd, _ = o_min_and_theta(PHASE1_L)
    n_ooe, n_oe = run_type_counts(odd, PHASE1_L - odd)
    assert neck["L"] == 25781
    assert neck["o"] == 16266
    assert neck["n_ooe"] == n_ooe == 6751
    assert neck["n_oe"] == n_oe == 2764
    assert neck["all_equal"]
    assert neck["stats"]["two_type"]
    assert neck["first_blocks"][0] == (2, 1)


def test_packed_and_bunched_have_zero_finance_slack():
    odd, _ = o_min_and_theta(PHASE1_L)
    start = max(START, MIN_STATE)
    s_max = budget_sum_terms(start, PHASE1_L, odd)
    for spec in graded_words(PHASE1_L, odd):
        if spec["two_type"]:
            assert spec["delta_fin"] == 0.0
            assert spec["s"] == s_max
        else:
            assert spec["delta_fin"] > 0.0
            assert spec["s"] < s_max


def test_extra_depth_words_preserve_length_and_odd_count():
    odd, _ = o_min_and_theta(PHASE1_L)
    n_ooe, n_oe = run_type_counts(odd, PHASE1_L - odd)
    for word in (
        extra_odd_word(n_ooe, n_oe, 50, front=False),
        extra_odd_word(n_ooe, n_oe, 500, front=True),
        extra_even_word(n_ooe, n_oe, 50, front=False),
    ):
        assert word.count("O") == odd
        assert len(word) == PHASE1_L


def test_word_sum_terms_matches_budget_on_the_packed_word():
    neck = packed_necklace()
    start = max(START, MIN_STATE)
    assert word_sum_terms(start, neck["word"]) == budget_sum_terms(
        start, neck["L"], neck["o"]
    )


def test_first_oe_on_bunched_ooe_is_after_all_ooe():
    odd, _ = o_min_and_theta(PHASE1_L)
    n_ooe, _n_oe = run_type_counts(odd, PHASE1_L - odd)
    bunched = "OOE" * n_ooe + "OE"
    rec = first_oe_letter_index(bunched)
    assert rec["letter"] == 3 * n_ooe
    assert rec["block"] == n_ooe


def test_walk_records_envelope_and_cell_geometry():
    neck = packed_necklace()
    walk = walk_first_blocks(START, neck["word"])
    assert walk["n"] == START
    assert walk["x_tag"] in ARCHIVED_TAGS or walk["x_tag"] == "new"
    assert walk["follow_depth"] < 20
    if walk["completed"] >= 1:
        row = walk["rows"][0]
        assert row["v"] == START
        assert row["a"] == 2
        rec = excursion_map(START, 2)
        assert rec is not None
        assert row["F"] == rec[1]
        assert row["env"] >= rec[1]
        assert row["deficit"] == row["env"] - rec[1]
        assert ooe_preimage_holds(START, rec[1])
        assert row["defects"]
        assert row["even_preimage_width"] == 2 * rec[1] + 1


def test_zero_tax_does_not_kill_25781_at_the_published_floor():
    rec = charged_excludes(0.0, floor=PUBLISHED_FLOOR)
    assert rec["untaxed_budget_excludes"] is False
    assert rec["parity_excludes"] is False
    assert rec["budget_excludes"] is False


def test_archived_tags_are_the_closed_bridge_set():
    assert ARCHIVED_TAGS == (
        "ooe_cell",
        "f2_expanding",
        "two_block_243",
        "cheap_ooe",
        "shared_ooe_prefix",
        "power_bound_word",
    )


def test_science_artifact_closes():
    payload = json.loads(SUMMARY.read_text(encoding="utf-8"))
    assert payload["bound"] == "extremizer_discrepancy"
    assert payload["L"] == 25781
    assert payload["table"]["modal_x"] == "shared_ooe_prefix"
    assert payload["table"]["all_archived"] is True
    assert payload["table"]["x_hist"]["shared_ooe_prefix"] == payload["table"]["n"]
    assert payload["table"]["mean_rel_deficit"] == 0.0
    assert payload["table"]["completed"].get("3") is None
    assert payload["graded"]["uncorrelated"] is True
    assert payload["decision"]["decision"] == "CLOSE"
    assert payload["decision"]["kills_25781_at_published_floor"] is False
    assert payload["decision"]["raise_n0"] is False
    assert payload["decision"]["open_1054"] is False
    assert payload["decision"]["open_k11"] is False
    assert payload["decision"]["open_55293"] is False
    assert payload["decision"]["leftover_killer"] is False
    assert payload["decision"]["halt_theorem"] is False


def test_realized_first_a2_hits_the_integer_envelope():
    payload = json.loads(SUMMARY.read_text(encoding="utf-8"))
    row = payload["table"]["spotlight_ok"][0]
    assert row["n"] == 1000057
    first, second = row["blocks"][0], row["blocks"][1]
    assert first["F"] == 5623773
    assert first["env"] == 5623773
    assert first["deficit"] == 0
    assert first["ooe_cell"] is True
    assert second["F"] == 39244721
    assert second["env"] == 39244721
    assert second["deficit"] == 0
    assert row["died_before_first_oe"] is True


def test_dossier_and_conjecture_record_close():
    dossier = DOSSIER.read_text(encoding="utf-8")
    assert "## Branch budget" in dossier
    assert "## Closed-bridge gates" in dossier
    assert "## Decision" in dossier
    assert "## Publication assessment" in dossier
    assert "**CLOSE**" in dossier
    rec = get_conjecture("juggler_cycle_extremizer_discrepancy")
    assert rec["status"] == "REFUTED"
    assert rec["counterexamples"]
