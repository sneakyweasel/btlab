"""Lemma 4.1': the printed proof step is false on an exact witness, the statement survives."""

from __future__ import annotations

import json
from fractions import Fraction

import pytest

from research.juggler_sequence.monotone_pairing import (
    DATA_DIR,
    later_at_most_one_fuller,
    occupancies,
    search,
    witness,
)


def test_the_witness_refutes_the_printed_pair_claim_but_not_the_lemma() -> None:
    w = witness()
    assert w["steps_nondecreasing"]
    assert w["hypotheses"]
    assert (3, 1) in w["pairs_violating_min_ge_sum_over_three"]
    assert w["conclusion_holds"]


def test_fact_a_holds_on_the_witness_and_fails_on_a_non_monotone_profile() -> None:
    w = witness()
    assert later_at_most_one_fuller(w["occupancies"])
    # steps 1/2, 1/10, 1/5, 1/5, 1/5, 1/5 are not monotone: an interior 1-cell then a 3-cell
    x = [Fraction(9, 20)]
    for s in [Fraction(1, 2), Fraction(1, 10), Fraction(1, 5), Fraction(1, 5), Fraction(1, 5),
              Fraction(1, 5)]:
        x.append(x[-1] + s)
    occ = occupancies(x)
    assert occ == [1, 1, 3, 2]
    assert not later_at_most_one_fuller(occ)


def test_fast_search_finds_no_violation() -> None:
    s = search(x_max=3.0, x_step=0.1, extra_H=8, phases=16)
    assert not s["violations"], s["worst"]
    assert s["fact_a_failures"] == 0
    assert s["worst"]["slack"] >= 1.0


def test_stored_summary_is_the_full_search() -> None:
    stored = DATA_DIR / "summary.json"
    if not stored.is_file():
        pytest.skip("run python -m research.juggler_sequence.monotone_pairing first")
    data = json.loads(stored.read_text(encoding="utf-8"))
    assert data["classification"]["label"] == "PRINTED_PROOF_STEP_FALSE_STATEMENT_SUPPORTED"
    assert not data["search"]["violations"]
    assert data["search"]["profiles"] > 10**6
