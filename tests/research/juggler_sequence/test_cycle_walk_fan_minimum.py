"""Fan-minimum balance law Phase 0. Arithmetic only, not a halt test."""

from __future__ import annotations

import json
import math
from pathlib import Path

from research.juggler_sequence.cycle_walk_fan_minimum import (
    balance_law_exact,
    eps_of_theta,
    probe_payload,
)

DOSSIER = Path("docs/problems/juggler_cycle_walk_fan_minimum.md")
CONJECTURE = Path("conjectures/proved/juggler_walk_fan_minimum_law.json")
ARTIFACT = Path("data/research/juggler/cycle_walk_fan_minimum/summary.json")


def test_eps_conversion():
    # theta = 1 - e^{-eps ln 3}: exact round trip
    for eps in (1e-9, 3.28e-6, 0.1):
        theta = -math.expm1(-eps * math.log(3.0))
        assert abs(eps_of_theta(theta) - eps) < 1e-15 * max(1.0, eps)


def test_fan_minimum_artifact():
    payload = json.loads(ARTIFACT.read_text(encoding="utf-8"))
    fans = {f["tag"]: f for f in payload["fans"]}
    fan_a = fans["fanA"]
    # A ~ the certified quotient 55; k* ~ 27.6; minimum matches the
    # competition schedule value 1.0735 at survivor 8632083
    assert 55.0 < fan_a["A"] < 56.5
    assert 27.0 < fan_a["k_star"] < 28.5
    assert abs(fan_a["R_min_pred"] - fan_a["R_min_measured"]) < 5e-4
    assert fan_a["argmin_survivor_exact"] == 8_632_083
    assert fan_a["argmin_matches"] is True
    fan_b = fans["fanB"]
    assert 4.0 < fan_b["A"] < 4.6
    assert fan_b["argmin_survivor_exact"] == 50_961_751
    assert fan_b["within_second_order_exact"] is True
    assert payload["classification"]["label"] == "WALK_FAN_MINIMUM_GREEN"
    # future-fan table: certified rows only through a16
    for row in payload["future_fans"]:
        assert row["R_min_lower"] > 1.0
        if row["quotient_index"] > 16:
            assert row["certified"] is False


def test_anti_overclaim_and_dossier_headings():
    dossier = DOSSIER.read_text(encoding="utf-8")
    for heading in (
        "## Problem",
        "## Exact statement",
        "## Branch budget",
        "## Decision",
        "## Publication assessment",
    ):
        assert heading in dossier
    assert "not claimed" in dossier
    assert "OPEN" in dossier
    record = json.loads(CONJECTURE.read_text(encoding="utf-8"))
    assert record["id"] == "juggler_walk_fan_minimum_law"
    assert record["status"] == "EXACT — HUMAN PROOF"
    # the Diophantine input is what stays open, and the record must say so
    assert "classical problem" in record["statement"]
    assert record["not_a_halt_theorem"] is True
    payload = json.loads(ARTIFACT.read_text(encoding="utf-8"))
    assert payload["not_a_halt_theorem"] is True
    assert payload["no_new_period_bound"] is True


NOTE = (
    Path(__file__).resolve().parents[3]
    / "docs"
    / "theory"
    / "juggler_near_convergent_diophantine_note.md"
)


def test_the_fan_law_is_an_identity_not_a_first_order_model():
    """Theorem 3 reproduces the stored theta data, to ten digits, on both fans.

    The manuscript's claim is that ``eps_k = eps_0 - k*eta`` is the linear form
    ``o_k - L_k x`` and so holds identically, which makes
    ``R_k = (A-k)/(A-k-1) * (B+k+1)/(B+k)`` an identity. If that is right, the
    closed form evaluated at the integer minimiser must equal the minimum of
    the R_k computed from the stored thetas -- not merely bracket it.
    """

    for fan in probe_payload()["fans"]:
        law = fan["exact_law"]
        assert law["R_min_integer"] is not None, fan["tag"]
        # closed form vs the theta-derived minimum: 1e-8 relative, which is the
        # theta <-> eps conversion and nothing else
        rel = abs(law["R_min_integer"] - fan["R_min_exact"]) / fan["R_min_exact"]
        assert rel < 1e-8, (fan["tag"], rel)
        # and the continuous minimum is a strict lower bound for it
        assert law["R_min_continuous"] < law["R_min_integer"], fan["tag"]


def test_the_exact_law_beats_the_first_order_one_where_it_matters():
    """Both are fine at a = 55; only the exact law is fine at a = 4."""

    fans = {f["tag"]: f for f in probe_payload()["fans"]}
    errors = {}
    for tag, fan in fans.items():
        law = fan["exact_law"]
        target = fan["R_min_exact"]
        errors[tag] = (
            abs(law["first_order_R_min"] - target) / target,
            abs(law["R_min_continuous"] - target) / target,
        )
    # fan A: the expansion is harmless
    assert errors["fanA"][0] < 1e-5
    # fan B: the expansion costs more than a percent, the exact law a quarter of one
    assert errors["fanB"][0] > 1e-2
    assert errors["fanB"][1] < 3e-3
    # the exact law is better on both
    for tag, (first_order, exact) in errors.items():
        assert exact < first_order, tag


def test_corollary_five_is_a_rational_bracket():
    """((a+3)/(a+1))^2 < R_min < ((a+1)/(a-1))^2, with no exponential in it."""

    for fan in probe_payload()["fans"]:
        law = fan["exact_law"]
        assert law["bracket_holds"], fan["tag"]
        # the lower bound also bounds every realised R_k, not just the minimum
        for tr in fan["transitions"]:
            assert tr["R_exact"] > law["lower_rational"], (fan["tag"], tr["k_from"])
    # a = 1 leaves the upper bound vacuous and the lower bound at 4
    single = balance_law_exact(1.5, 0.5, closing=1)
    assert single["upper_rational"] is None
    assert math.isclose(single["lower_rational"], 4.0)
    # and the bound tends to 1 exactly as the quotient grows -- Corollary 6
    prev = 0.0
    for a in (1, 4, 15, 55, 1000):
        lo = ((a + 3.0) / (a + 1.0)) ** 2
        assert lo > 1.0
        assert lo < prev or prev == 0.0
        prev = lo
    assert ((10**6 + 3.0) / (10**6 + 1.0)) ** 2 < 1.00001


def test_manuscript_states_what_is_identity_and_what_is_open():
    text = NOTE.read_text(encoding="utf-8")
    flat = " ".join(text.split())
    # the status contract, and the three labels it has to keep apart
    for claim in (
        "What is proved, what is measured, what is open",
        "There is no error term",
        "classical OPEN",
        "not a halt theorem",
    ):
        assert claim.lower() in flat.lower(), claim
    # the exact law, and the correction of the earlier draft
    assert "A+B+1" in flat and "A+B-1" in flat
    assert "there is no second order" in flat.lower()
    # the certified sandwich is named by its two integer comparisons
    assert "3^{171928773}<2^{272500658}" in flat.replace(" ", "")
    assert "3^{53715833}>2^{85137581}" in flat.replace(" ", "")
    # and no claim of a kill
    assert "does not exclude" in flat
