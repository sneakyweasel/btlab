"""Tests for the structural check of Lemma E7's U-carry decomposition."""

from __future__ import annotations

import json

from research.juggler_sequence import depth_five_structural as dfs
from research.juggler_sequence.lean_paths import DATA_ROOT

TABLE = DATA_ROOT / "depth_five_production" / "e7_structural" / "residuals.json"


def charged(P: int, d: int, l: int, k: int) -> float:
    """E7's charged orders once the B replacement is restored."""
    return abs(k) * (d * P ** (-13 / 16) + P ** (-9 / 16)) + abs(l) * P ** (-3 / 8)


def test_committed_residuals_stay_within_charged_orders() -> None:
    rows = json.loads(TABLE.read_text(encoding="utf-8"))["rows"]
    assert len(rows) == 18
    for r in rows:
        i, _, l, k = r["frequency"]
        assert r["corrected_max"] <= charged(r["P"], r["d"], l, k), r
        # The raw model misses exactly the B replacement, of order k d P^(-7/16).
        assert r["raw_max"] <= 2 * abs(k) * r["d"] * r["P"] ** (-7 / 16) + charged(r["P"], r["d"], l, k), r


def test_committed_mismatch_rate_is_small() -> None:
    counts = json.loads(TABLE.read_text(encoding="utf-8"))["mismatch_counts"]
    for c in counts:
        assert c["carry_mismatches"] <= c["points"] * c["P"] ** (-3 / 8), c


def test_small_instance_matches_the_model() -> None:
    r = dfs.residuals(10 ** 6, 3, 0, 0, 1, 40)
    assert r["corrected_max"] <= charged(10 ** 6, 3, 0, 1)
    assert r["corrected_max"] < r["raw_max"]
