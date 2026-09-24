"""Tests for the E5/E7 curvature certificates and the critical-path exponent ledger."""

from __future__ import annotations

import json
from fractions import Fraction

from research.juggler_sequence import critical_path_ledger as cpl
from research.juggler_sequence import curvature_certificates as cc
from research.juggler_sequence.lean_paths import DATA_ROOT

CERTS = DATA_ROOT / "depth_five_production" / "curvature_certificates" / "certificates.json"
LEDGER = DATA_ROOT / "depth_five_production" / "critical_path_ledger" / "ledger.json"


def test_decompositions_give_the_lemma_constants() -> None:
    assert cc.leading_constants() == {"E7": "-1701/4096", "E5": "243/4096"}


def test_committed_certificates_agree_with_sympy_and_hold() -> None:
    data = json.loads(CERTS.read_text(encoding="utf-8"))
    assert data["sympy_constants"] == data["leading_constants"]
    assert data["e7"]["1"]["threshold_log10_X"] == 8
    assert data["e7"]["1"]["at_1e12"]["negative"] is True
    assert data["e5"]["1"]["threshold_log10_X"] == 18
    assert data["e5"]["1"]["at_1e30"]["positive"] is True
    # A cutoff P^(1/16) (Result 34) lowers E5's certified range to 10^11.
    assert data["e5_cutoff_1_16"]["1"]["threshold_log10_X"] == 11


def test_e5_is_not_certified_below_its_threshold() -> None:
    assert cc.e5_certificate(10 ** 12, 1)["positive"] is None


def test_certificate_fails_on_a_sign_error() -> None:
    # Arb certifies the sign of the decomposition it is given; the SymPy test above
    # is what checks the decomposition itself. A flipped centring term must fail.
    saved = cc.E5_TERMS
    try:
        cc.E5_TERMS = ((Fraction(297, 256), Fraction(-5, 16)), (Fraction(27, 32), Fraction(-1, 2)))
        assert cc.e5_certificate(10 ** 30, 1)["positive"] is not True
    finally:
        cc.E5_TERMS = saved


def test_committed_ledger_passes() -> None:
    data = json.loads(LEDGER.read_text(encoding="utf-8"))
    assert all(row["ok"] for row in data["bounds"])
    derived = data["derived"]
    assert derived["tail_claims_ok"] and derived["coefficient_ok"] and derived["assembly_loss_ok"]
    assert derived["tail_exponent_OOOEE"] == "1/54"
    assert derived["sigma_OOOEE"] == "1/64"  # E5 at cutoff P^(1/16) does not bind
    assert derived["tail_exponent_OOEOE"] == "2/81"


def test_ledger_catches_a_cost_above_its_claim() -> None:
    saved = cpl.BOUNDS
    try:
        cpl.BOUNDS = saved + [("bad", Fraction(7, 8), [("too big", Fraction(15, 16))])]
        assert not all(row["ok"] for row in cpl.check_bounds())
    finally:
        cpl.BOUNDS = saved
