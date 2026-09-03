"""Coupled exponent-walk charge. Not a halt test."""

from __future__ import annotations

import hashlib
import json
import math
from pathlib import Path

from research.juggler_sequence.cycle_walk_charge import (
    MU,
    STEP,
    brute_force_budget,
    classify,
    deficit_D,
    transport_bound,
    walk_budget,
)

ARTIFACT = Path("data/research/juggler/cycle_walk_charge/summary.json")
DOSSIER = Path("docs/problems/juggler_cycle_walk_charge.md")
CONJECTURE = Path("conjectures/active/juggler_cycle_walk_charge.json")


def test_lattice_constants():
    assert math.isclose(MU, math.log2(1.5))
    assert math.isclose(STEP, 1.0 + MU)


def test_dp_matches_brute_force_on_tiny_lengths():
    for length, odd_count in [(5, 4), (8, 6), (11, 7), (12, 8)]:
        dp = walk_budget(length, odd_count, 1000)["walk_sum"]
        bf = brute_force_budget(length, odd_count, 1000)
        assert math.isclose(dp, bf, rel_tol=1e-12)


def test_transport_bound_is_small_at_the_certified_floor():
    eta = transport_bound(50_508, 31_867, 26_254_996)
    assert 0 < eta < 1e-4


def test_deficit_reduced_base_is_fourth_digit():
    deficit = deficit_D(50_508, 31_867, 26_254_996)
    assert 0 < deficit < 1e-3
    # e/n dominates; the odd contribution is ~2e-4 relative.
    assert math.isclose(
        deficit, 1.05 * 18_641 / 26_254_996, rel_tol=1e-3
    )


def test_committed_certified_target_kills_50508():
    payload = json.loads(ARTIFACT.read_text(encoding="utf-8"))
    cert = payload["certified_target"]
    assert cert["length"] == 50_508
    assert cert["floor"] == 26_254_995
    assert cert["certified_excludes"] is True
    assert cert["kill_margin"] > 1.1
    assert cert["deficit_D"] < 1e-3


def test_committed_target_is_green_with_margin():
    payload = json.loads(ARTIFACT.read_text(encoding="utf-8"))
    target = payload["target"]
    assert target["length"] == 50_508
    assert target["floor"] == 26_254_995
    assert target["improvement_over_parity"] > 6.87
    for row in target["eta_rows"]:
        assert row["walk_excludes"] is True
        assert row["kill_margin"] > 1.0
    assert payload["classification"]["label"] == "WALK_CHARGE_GREEN"
    assert classify(target)["label"] == "WALK_CHARGE_GREEN"
    assert payload["not_a_halt_theorem"] is True


def test_calibration_reproduces_archived_necklace_value():
    payload = json.loads(ARTIFACT.read_text(encoding="utf-8"))
    calib = payload["calibration"]
    assert calib["length"] == 25_781
    assert calib["floor"] == 1_000_000
    row0 = calib["eta_rows"][0]
    assert math.isclose(row0["walk_rhs"], 1.2984e-4, rel_tol=1e-3)
    assert row0["walk_excludes"] is False
    assert row0["kill_margin"] < 0.2


N350_KILLS = (
    478245,
    504026,
    528753,
    579261,
    629769,
    654496,
    680277,
    705004,
    730785,
    755512,
)
N350_KILL_DIR = Path("data/research/juggler/cycle_walk_charge/N350000000_kills")
N350_LEFTOVERS = Path(
    "data/research/juggler/cycle_walk_charge/N350000000_parity_leftovers.json"
)
N350_KILL_SHA = "d16ccfed52757d4a44368a6549a8149ccbc926472737276c577912346db854ab"
N350_BELOW_SURVIVOR = (
    176251,
    226759,
    352502,
    403010,
    453518,
    *N350_KILLS,
)


def test_n350_walk_kills_ten_and_leaves_780239():
    blob = b"".join(
        (N350_KILL_DIR / f"L{length}.json").read_bytes() for length in N350_KILLS
    )
    assert hashlib.sha256(blob).hexdigest() == N350_KILL_SHA
    for length in N350_KILLS:
        report = json.loads(
            (N350_KILL_DIR / f"L{length}.json").read_text(encoding="utf-8")
        )
        assert report["length"] == length
        assert report["floor"] == 350_000_000
        assert report["certified_excludes"] is True
        assert report["kill_margin"] > 1.0
    blocker = json.loads(
        (N350_KILL_DIR / "L780239.json").read_text(encoding="utf-8")
    )
    assert blocker["certified_excludes"] is False
    assert blocker["floor"] == 350_000_000
    assert 0.60 < blocker["kill_margin"] < 0.61
    leftovers = json.loads(N350_LEFTOVERS.read_text(encoding="utf-8"))
    assert leftovers["floor"] == 350_000_000
    assert leftovers["l_max"] == 800_000
    lengths = [row["L"] for row in leftovers["leftovers"]]
    assert lengths[0] == 176251
    assert 780239 in lengths
    assert [L for L in lengths if L < 780239] == list(N350_BELOW_SURVIVOR)
    summary = json.loads(
        (N350_KILL_DIR / "summary.json").read_text(encoding="utf-8")
    )
    assert summary["first_survivor"] == 780239
    assert summary["all_ten_exclude"] is True
    assert summary["survivor_excludes"] is False
    assert summary["sha256_ten_kill_records"] == N350_KILL_SHA


def test_dossier_and_conjecture_record_are_consistent():
    dossier = DOSSIER.read_text(encoding="utf-8")
    assert "WALK_CHARGE_GREEN" in dossier
    assert "PROMOTE" in dossier
    assert "not claimed" in dossier
    record = json.loads(CONJECTURE.read_text(encoding="utf-8"))
    assert record["status"] == "COMPUTATIONALLY_SUPPORTED"
    assert "COMPUTATIONALLY VERIFIED" in record["notes"]
    assert "kill margin 1.1204" in record["statement"]
    assert record["not_a_halt_theorem"] is True
