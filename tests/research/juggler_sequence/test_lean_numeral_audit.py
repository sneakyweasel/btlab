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


# --- and the same failure, in the manuscript's citations of the probes ---


def test_every_probe_citation_resolves_and_holds() -> None:
    bad = A.broken_citations()
    assert bad == [], [(r["module"], r["function"],
                        "anchor gone" if not r["anchor_present"]
                        else "does not resolve" if not r["resolves"]
                        else "returns something else") for r in bad]


def test_every_citation_anchor_is_still_in_the_manuscript() -> None:
    """A reworded sentence must retire its row, not leave the check guarding nothing."""
    for r in A.citation_audit(run_checks=False):
        assert r["anchor_present"], (r["module"], r["function"])
        assert r["resolves"], (r["module"], r["function"])


def test_the_calibration_figure_is_the_one_at_the_stated_setting() -> None:
    """0.500 is what the instrument gives at trials=120; its default 200 gives 0.497."""
    from research.juggler_sequence import paper_b_audit as PB
    default = PB.block_exponent_calibration()["fitted"]
    at120 = PB.block_exponent_calibration(trials=120)["fitted"]
    assert abs(default["mean"] - 0.497) < 5e-4
    assert abs(at120["mean"] - 0.500) < 5e-4
    assert abs(default["sd"] - 0.043) < 5e-4 and abs(at120["sd"] - 0.043) < 5e-4
    # the manuscript now names the setting it quotes
    text = A.paper_text()
    assert r"\(0.497\pm0.043\) at its default \(200\) trials" in text
    assert r"0.500\pm0.043" not in text


def test_the_beta_census_no_longer_claims_to_be_exact_throughout() -> None:
    """Its integers are exact; the ratios reported beside them are not."""
    import inspect
    from research.juggler_sequence import decoration_budget as DB
    src = inspect.getsource(DB.beta_inventory_attained)
    assert "**0.5" in src or "**-1.75" in src        # there are float operations
    text = A.paper_text()
    assert "integer arithmetic throughout" not in text
    assert "the ratios to the" in text and "printed forms in floating point" in text
    # while the ladder, which really is exact, still says so
    assert r"integer arithmetic through" in text
    assert r"\(\lfloor n^{3/2}\rfloor=\lfloor\sqrt{n^3}\rfloor\)) finds" in text


def test_the_citation_guard_fires_when_a_probe_is_renamed(monkeypatch) -> None:
    """The motivating case: branch_offset was renamed to offset_at under a live citation."""
    real = A._probe

    class Missing:
        pass

    def doctored(module: str):
        return Missing() if module == "decoration_budget" else real(module)

    monkeypatch.setattr(A, "_probe", doctored)
    broken = {(r["module"], r["function"]) for r in A.broken_citations()}
    assert ("decoration_budget", "branch_offset_ladder") in broken
    assert ("decoration_budget", "beta_inventory_attained") in broken
    assert ("p0_certificate", "interpolant_error") not in broken


# --- and the ranges, which are arguments with defaults ---


def test_every_printed_range_is_the_cited_function_s_default() -> None:
    bad = A.mismatched_ranges()
    assert bad == [], [(r["module"], r["function"],
                        "printed text gone" if not r["printed_present"] else "default moved")
                       for r in bad]


def test_the_range_guard_fires_when_a_default_moves(monkeypatch) -> None:
    """A default that moves rescopes a printed claim silently; that is the whole point."""
    import inspect
    from research.juggler_sequence import decoration_budget as DB
    real = inspect.signature

    def doctored(fn):
        s = real(fn)
        if fn is DB.branch_offset_ladder:
            p = dict(s.parameters)
            p["multiples"] = p["multiples"].replace(default=(1, 2, 3))
            return s.replace(parameters=list(p.values()))
        return s

    monkeypatch.setattr(inspect, "signature", doctored)
    bad = {(r["module"], r["function"]) for r in A.mismatched_ranges()}
    assert ("decoration_budget", "branch_offset_ladder") in bad
    assert ("decoration_budget", "beta_inventory_attained") not in bad


def test_the_offset_term_range_is_exact_and_the_lower_end_is_attained() -> None:
    """[3/2, (3/2)2^(3/4)] against a printed [1.5, 2.6]: sharp below, 3% above."""
    from research.juggler_sequence import decoration_budget as DB
    r = DB.offset_term_attained(10**5)
    lo, hi = r["attained"]
    assert abs(lo - 1.5) < 2e-3                      # attained, not merely bounded
    assert abs(hi - 1.5 * 2**0.75) < 3e-3
    assert r["closed_form"] == [1.5, 1.5 * 2**0.75]
    assert r["printed"] == [1.5, 2.6]
    assert 1.02 < r["headroom_at_top"] < 1.04
    text = A.paper_text()
    assert r"\bigl[\tfrac32,\ \tfrac32\cdot2^{3/4}\bigr]=[1.5000,\,2.5227]" in text
    # the sampled figures are kept, labelled as what a grid missed, not as the claim
    assert "which is the same" + chr(10) + "statement with the endpoints missed by a sampling grid" in text
    assert "the printed ranges" not in text.split("(iv) By (ii)")[0][-1200:]


def test_the_unanchored_measurements_are_named_not_assumed() -> None:
    """Three printed numbers cite no function; the count is recorded rather than hidden."""
    un = A.unanchored_measurements()
    assert len(un) == 3, [r["printed"] for r in un]
    why = " ".join(r["why"] for r in un)
    assert "no sweep exists" in why and "20,000-sample" in why and "ten-sample" in why
    # and the one that could be anchored, was
    assert all("offset" not in r["why"] for r in un)


def test_level1_block_scaling_really_has_no_sweep() -> None:
    """The twelve exponents are four P values times three k, and the P values are not stated."""
    import inspect
    from research.juggler_sequence import paper_b_audit as PB
    sig = inspect.signature(PB.level1_kernel_block_scaling)
    assert set(sig.parameters) == {"P", "k", "bins"}
    assert sig.parameters["P"].default == 10**5      # one point, not a range
    assert not [n for n in dir(PB) if "level1_kernel_block" in n and n.endswith("sweep")]
