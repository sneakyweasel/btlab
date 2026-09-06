"""Every numeral in a Paper B Lean statement is classified, and every pairing holds.

`p0_certificate.LEAN_ROWS` pairs the thirty-eight threshold rows with their theorems and
rational witnesses.  Nothing paired the rest, and that is how `interpolant_step_i` proved the
superseded cap `186` while the display three lines above it in the manuscript carried the
corrected `300`.  This is the missing half of that table.

The guard is deliberately not "does the numeral appear in the manuscript": `186` and `106` both
appear there, inside the erratum's own list of what replaced them.  It is a value check against
`p0_certificate`'s constants or exact rational arithmetic, plus a completeness requirement, so
that a new numeral in a Paper B statement has to be classified before the suite is green.
"""

from __future__ import annotations

import importlib.util
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parents[3]
_spec = importlib.util.spec_from_file_location("lean_numeral_audit",
                                               ROOT / "tools" / "lean_numeral_audit.py")
A = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(A)


def test_every_numeral_is_classified() -> None:
    rows = A.audit()
    stray = A.unclassified(rows)
    assert stray == [], [(r["module"], r["theorem"], r["numeral"]) for r in stray]


def test_every_pairing_holds() -> None:
    bad = A.failing()
    assert bad == [], [(r["theorem"], r["numeral"], r["role"]) for r in bad]


def test_the_table_actually_covers_something() -> None:
    """A guard that classifies nothing would also report nothing unclassified."""
    cov = A.coverage()
    assert cov["numerals"] > 300
    assert cov["paired"] > 50
    assert cov["structural"] > 200
    assert cov["unclassified"] == 0 and cov["failing"] == []
    assert cov["certificate_rows_covered_elsewhere"] == 38


def test_the_guard_fires_on_the_bug_it_was_built_for(monkeypatch) -> None:
    """Put the superseded cap back into interpolant_step_i and the audit must complain."""
    real = A.statements

    def doctored(module: str) -> dict[str, str]:
        out = dict(real(module))
        if module == "PaperBAssembly":
            out["interpolant_step_i"] = (out["interpolant_step_i"]
                                         .replace("300", "186").replace("84.38", "52.32"))
        return out

    monkeypatch.setattr(A, "statements", doctored)
    stray = {(r["theorem"], r["numeral"]) for r in A.unclassified()}
    assert ("interpolant_step_i", "186") in stray
    assert ("interpolant_step_i", "52.32") in stray


def test_the_two_anchors_are_kept_apart() -> None:
    """The corrected chain and the superseded one are both present, and are not confused."""
    pa = A.statements("PaperBAssembly")
    assert "300" in pa["interpolant_step_i"] and "186" not in pa["interpolant_step_i"]
    assert "186" in pa["interpolant_step_i_precorrection"]
    assert "170.6" in pa["interpolant_assembly"]
    assert "106" in pa["interpolant_assembly_precorrection"]
    # and the pairing for each names the anchor it belongs to
    corrected = A.PAIRINGS[("PaperBAssembly", "interpolant_step_i")]["300"]
    superseded = A.PAIRINGS[("PaperBAssembly", "interpolant_step_i_precorrection")]["186"]
    assert "4.2" in corrected[1] and "2.6" in superseded[1]
    assert corrected[2]() and superseded[2]()


def test_stage4_curvature_is_named_separately_from_the_old_lambda0_floor() -> None:
    """Both are 0.35 and they are different constants; the audit must not reach for the wrong one."""
    from research.juggler_sequence import p0_certificate as C
    assert A.STAGE4_CURVATURE == 0.35 == C.ANCHOR_CONSTANTS_PRECORRECTION[0]
    assert C.ANCHOR_CONSTANTS[0] == 0.56
    # every 0.35 in the table is attributed to Theorem 4.1's Stage-4 curvature, not to lambda_0
    for (_mod, thm), table in A.PAIRINGS.items():
        entry = table.get("0.35")
        if entry is not None:
            assert "Stage-4" in entry[1], (thm, entry[1])


@pytest.mark.parametrize("theorem,numeral,expected", [
    ("interpolant_step_i", "84.38", 84.375),        # (9/32) * 300
    ("interpolant_step_i_precorrection", "52.32", 52.3125),  # (9/32) * 186
    ("interpolant_assembly", "170.6", 170.58),      # (84.38 + 0.91) * 2
    ("interpolant_assembly_precorrection", "106", 105.78),
])
def test_the_rounded_constants_round_the_right_way(theorem, numeral, expected) -> None:
    assert expected <= float(numeral)
    assert A.PAIRINGS[("PaperBAssembly", theorem)][numeral][2]()


# --- the same failure, in prose ---


def test_no_lean_prose_claim_about_the_manuscript_is_stale() -> None:
    bad = A.stale_claims()
    assert bad == [], [(r["module"], r["description"],
                        "anchor gone" if not r["anchor_present"] else "manuscript disagrees")
                       for r in bad]


def test_every_claim_has_an_anchor_still_in_its_file() -> None:
    """Rewording a sentence must retire its row loudly, not silently."""
    for r in A.claim_audit():
        assert r["anchor_present"], (r["module"], r["anchor"][:50])


def test_the_predicates_discriminate() -> None:
    """A claim that holds against an empty manuscript is not checking anything."""
    for _mod, _anchor, desc, pred in A.MANUSCRIPT_CLAIMS:
        assert pred("") is False, desc


def test_the_claim_guard_fires_on_the_two_it_was_built_for(monkeypatch) -> None:
    """Both BranchFreeze remarks had been adopted into the manuscript and said otherwise."""
    text = A.paper_text()
    # the cancellation: strip it from the manuscript and the row must go stale
    doctored = text.replace(r"\tfrac{99}{64}\cdot19=29.4", "REMOVED")
    monkeypatch.setattr(A, "paper_text", lambda: doctored)
    stale = {r["description"] for r in A.stale_claims()}
    assert "the cancellation is in the manuscript, with both Lean names cited" in stale
    # the beta-product: the manuscript printing 18 instead of 19 must also fire
    doctored2 = text.replace(r"\beta_1\beta_2\le19h_1h_2P", r"\beta_1\beta_2\le18h_1h_2P")
    monkeypatch.setattr(A, "paper_text", lambda: doctored2)
    stale2 = {r["description"] for r in A.stale_claims()}
    assert "the manuscript carries 19 for the beta-product, not 18" in stale2


def test_the_two_branchfreeze_headers_no_longer_claim_sole_custody() -> None:
    src = A.statements  # keep the module import honest
    assert src is not None
    text = (A.LEAN_DIR / "BranchFreeze.lean").read_text(encoding="utf-8")
    assert "One thing this file records that the manuscript does not" not in text
    assert "A cancellation the printed `25` depends on" in text
    assert "neither is the sole record" in text
    # and the arithmetic in the header now matches the manuscript's 29.4, not 27.8
    assert "29.4 h\u2081h\u2082P^(-7/4)" in text
    assert "27.8" not in text
    assert abs((81 / 64 + 9 / 32) * 19 - 29.390625) < 1e-9
