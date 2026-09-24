"""Tests for ``depth_five_production``."""

from __future__ import annotations

import json
from fractions import Fraction

import pytest

from research.juggler_sequence import depth_five_production as dfp
from research.juggler_sequence.lean_paths import BRANCHES_ROOT


def test_dossier_exists() -> None:
    assert (BRANCHES_ROOT / "juggler_depth_five_production.md").is_file()


def test_first_descent_words_through_depth_five() -> None:
    words = dfp.first_descent_words(5)
    assert words == ["E", "OE", "OOEE", "OOEOE", "OOOEE"]


def test_ideal_coefficient_is_three_to_minus_odd_count() -> None:
    for word in dfp.first_descent_words(8):
        assert dfp.ideal_coefficient(word) == Fraction(1, 3 ** word.count("O"))


def test_window_exponents() -> None:
    assert 1 - dfp.rho("OOEE") == Fraction(7, 16)
    assert 1 - dfp.rho("OOOEE") == Fraction(5, 32)
    assert 1 - dfp.rho("OOEOE") == Fraction(5, 32)


def test_prices() -> None:
    table = dfp.price(8)
    by_depth = {row["depth"]: row for row in table["depths"]}
    assert by_depth[4]["ideal_root"] == pytest.approx(0.6328, abs=1e-4)
    assert by_depth[5]["ideal_root"] == pytest.approx(0.7512, abs=1e-4)
    assert by_depth[5]["new_words"] == ["OOEOE", "OOOEE"]
    assert table["certified_depth_four_root"] >= 5 / 8


def test_run_writes_under_tmp(tmp_path) -> None:
    manifest = dfp.run(output_root=tmp_path)
    assert manifest.is_file()
    written = json.loads((manifest.parent / "pricing.json").read_text(encoding="utf-8"))
    assert written["depths"][4]["depth"] == 5
