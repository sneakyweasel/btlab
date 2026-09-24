"""Tests for the word-family complexity pricing."""

from __future__ import annotations

import json
from fractions import Fraction

from research.juggler_sequence import word_family_complexity as wfc
from research.juggler_sequence.lean_paths import DATA_ROOT

TABLE = DATA_ROOT / "depth_five_production" / "word_families" / "classes.json"


def test_words_ending_in_odd_are_not_productions() -> None:
    assert not wfc.admissible("OOEEO")
    assert wfc.admissible("OOEE") and wfc.admissible("OOEEE")


def test_growing_factors_match_the_known_difficulty_order() -> None:
    assert wfc.growing_factors("OOEE") == []
    assert wfc.growing_factors("OOEOE") == [Fraction(9, 16)]
    assert wfc.growing_factors("OOOEE") == [Fraction(9, 8)]
    assert wfc.growing_factors("OOOEOEE")[0] == Fraction(9, 8)
    assert wfc.growing_factors("OOOOEEE")[0] == Fraction(45, 16)


def test_committed_classes_pick_first_descent_words() -> None:
    rows = {r["class"]: r for r in json.loads(TABLE.read_text(encoding="utf-8"))["classes"]}
    assert rows["no nested growing factor"]["first_words"] == ["OE", "OOEE"]
    assert rows["one factor <= 9/8"]["first_words"] == ["OE", "OOEE", "OOEOE", "OOOEE"]
    assert abs(rows["one factor <= 9/8"]["root"] - 0.7512) < 1e-3
    roots = [r["root"] for r in rows.values()]
    assert roots[:3] == sorted(roots[:3])
