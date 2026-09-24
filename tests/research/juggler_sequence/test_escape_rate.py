"""Tests for ``escape_rate``."""

from __future__ import annotations

import json
from fractions import Fraction

from research.juggler_sequence import escape_rate as er
from research.juggler_sequence.lean_paths import BRANCHES_ROOT


def test_dossier_exists() -> None:
    assert (BRANCHES_ROOT / "juggler_escape_rate.md").is_file()


def test_multiplier_is_a_fair_martingale() -> None:
    for odd in range(4):
        for even in range(4):
            here = er.rho(odd, even)
            assert (er.rho(odd + 1, even) + er.rho(odd, even + 1)) / 2 == here


def test_small_depth_counts_exactly() -> None:
    # Depth 2, threshold 2: only OO reaches 9/4 >= 2; O alone gives 3/2.
    assert er.hitting_fraction(2, 2) == Fraction(1, 4)
    assert er.hitting_fraction(0, 2) == 0


def test_ville_bound_holds_and_depth_is_monotone() -> None:
    for threshold in (2, 4, 16):
        previous = Fraction(0)
        for depth in (5, 10, 20, 30):
            frac = er.hitting_fraction(depth, threshold)
            assert previous <= frac <= Fraction(1, threshold)
            previous = frac


def test_run_writes_under_tmp(tmp_path) -> None:
    manifest = er.run(output_root=tmp_path)
    rows = json.loads((manifest.parent / "ville.json").read_text(encoding="utf-8"))
    assert all(row["within_bound"] for row in rows)
