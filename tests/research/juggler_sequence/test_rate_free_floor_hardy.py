"""Rate-free floor-Hardy door: literature, parity identity, finite β tent."""

from __future__ import annotations

from math import floor, log
from pathlib import Path

from research.literature import get_reference

DOSSIER = Path("docs/problems/juggler_rate_free_floor_hardy.md")
CONJECTURE = Path(
    "conjectures/active/juggler_tower_rate_free_equidistribution.json"
)

LIT_IDS = (
    "boshernitzan-1994-hardy-fields",
    "frantzikinakis-2009-sparse-nilmanifolds",
    "richter-2023-hardy-nilmanifolds",
    "tsinas-2023-pointwise-hardy-nilmanifolds",
    "bergelson-leibman-2007-generalized-polynomials",
    "host-kra-2005-nilmanifolds",
    "kuipers-niederreiter-1974-uniform-distribution",
)

BETA_STAR = 1.0 - log(2.0) / log(3.0)


def test_literature_ids_resolve():
    for ref_id in LIT_IDS:
        rec = get_reference(ref_id)
        assert rec["id"] == ref_id
        assert rec["project_relationship"] == "known"


def test_dossier_headings_and_close():
    dossier = DOSSIER.read_text(encoding="utf-8")
    for heading in (
        "## Problem",
        "## Exact statement",
        "## Current literature",
        "## Branch budget",
        "## Decision",
        "## Publication assessment",
    ):
        assert heading in dossier
    decision = dossier.split("## Decision", 1)[1].split("## ", 1)[0]
    assert "CLOSE" in decision
    assert "UNBUILT_DOOR" in dossier
    assert "no new ledger row" in dossier.lower() or "No new ledger row" in dossier
    assert "J-nil-pet-reentry" in dossier
    assert "J-nested-floor-without-W-family" in dossier
    for ref_id in LIT_IDS:
        assert ref_id in dossier


def test_next_letter_is_half_interval_of_one_phase():
    """floor(α) even iff {α/2} < 1/2. Algebra, not a census."""

    for alpha in (0.0, 0.1, 0.49, 0.5, 0.99, 1.0, 2.3, 17.8, 100.0, 1000.25):
        even = floor(alpha) % 2 == 0
        half = (alpha / 2.0) - floor(alpha / 2.0) < 0.5
        assert even is half


def test_tent_integral_beats_beta_star():
    """Continuous tent under 1_{[0,1/2)} has integral 1/2 - ε.

    ε = 0.12 gives 0.38 > β* ≈ 0.36907. Finite Weyl of that tent
    is then a KNOWN sufficient condition for the β-fallback, of
    the same composition species.
    """

    eps = 0.12
    tent_mass = 0.5 - eps
    assert tent_mass > BETA_STAR
    assert 0.369 < BETA_STAR < 0.370
    assert tent_mass == 0.38


def test_taylor_transfer_threshold_is_alpha_lt_one():
    """|v^α - X^α| = O(X^{α-1}) is o(1) iff α < 1.

    For α = 9/4 the leftover exponent is (3/2)(9/4 - 1) = 15/8.
    """

    alpha = 9.0 / 4.0
    leftover_exp = (3.0 / 2.0) * (alpha - 1.0)
    assert leftover_exp == 15.0 / 8.0
    assert leftover_exp > 0.0
    assert alpha > 1.0


def test_pairing_constant_misses_lemma_b():
    """Monotone pairing is 1/3; Lemma B needs β > 1 - log 2 / log 3.

    The comparison is 8 < 9: log 2 / log 3 < 2/3 iff 8 < 9.
    """

    assert 8 < 9
    assert (1.0 / 3.0) < BETA_STAR
    assert (1.0 / 7.0) < (1.0 / 3.0)
    dossier = DOSSIER.read_text(encoding="utf-8")
    assert "8<9" in dossier or "8 < 9" in dossier
    assert "pairing" in dossier.lower()
    assert "Lemma B" in dossier


def test_conjecture_stays_active():
    text = CONJECTURE.read_text(encoding="utf-8")
    assert '"status": "ACTIVE"' in text or '"status":"ACTIVE"' in text
    assert "juggler_rate_free_floor_hardy" in text or "irreducible door" in text
