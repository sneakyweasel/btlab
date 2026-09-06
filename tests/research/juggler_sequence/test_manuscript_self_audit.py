"""The manuscript against itself.

Every other audit here compares the manuscript with something outside it -- Lean declarations,
probe functions, the certificate.  None compared it with itself, and three of this audit's
findings were of that kind: the `0.35` conflation, the interpolant chain that kept the
constants its own lemma's erratum had replaced, and a count attributed to the wrong theorem.

Two directions, because the failure runs both ways: a named constant printed with more than
one value, and a value naming more than one constant.
"""

from __future__ import annotations

import importlib.util
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
_spec = importlib.util.spec_from_file_location("manuscript_self_audit",
                                               ROOT / "tools" / "manuscript_self_audit.py")
M = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(M)


def test_no_named_constant_carries_an_undeclared_value() -> None:
    bad = M.failures()["constants"]
    assert bad == [], [(r["name"], r["undeclared"]) for r in bad]


def test_the_canonical_values_are_the_ones_the_certificate_computes() -> None:
    from research.juggler_sequence import p0_certificate as C
    rows = {r["name"]: r for r in M.constant_audit()}
    assert abs(C.certificate()["P0"] / 3.6e13 - 1) < 0.02
    assert abs(10 ** C.log10_P1(C.KAPPA) / 9.8e18 - 1) < 0.02
    assert abs(C.C7 - 1 / 232) < 1e-15 and rows["c_7"]["canonical"] == "1/232"
    assert abs(C.KAPPA - 1 / 12) < 1e-15
    assert abs(C.R0_EXPONENT - 5 / 16) < 1e-15 and rows["R_0"]["canonical"] == "5/16"


def test_the_declared_alternatives_are_each_present_and_each_explained() -> None:
    """A hundred percent of the multiplicities here are legitimate, which is the design point."""
    text = M.paper_text()
    for name, _pat, canonical, alts in M.CONSTANT_VALUES:
        assert canonical
        for value, why in alts.items():
            assert why and len(why) > 12, (name, value)
    # c_7 is the busy one: the value, the weaker printed one, and two crossovers
    rows = {r["name"]: r for r in M.constant_audit()}
    assert set(rows["c_7"]["values"]) >= {"1/232", "1/288", "1/61"}
    assert "1/288" in text and "1/61" in text


def test_every_shared_value_is_listed_in_the_manuscript() -> None:
    bad = M.failures()["shared"]
    assert bad == [], [r["value"] for r in bad]
    rows = {r["value"]: r for r in M.shared_value_audit()}
    assert len(rows["0.11"]["roles"]) == 3
    assert len(rows["0.35"]["roles"]) == 2
    assert len(rows["1.1"]["roles"]) == 3
    assert len(rows["1.2"]["roles"]) == 4
    for v in ("0.11", "0.35", "1.1", "1.2", "1.5"):
        assert rows[v]["occurrences"] > 10, v


def test_the_guard_fires_when_a_value_leaves_the_table(monkeypatch) -> None:
    text = M.paper_text().replace("*Constants that share a value.*", "REMOVED")
    monkeypatch.setattr(M, "paper_text", lambda: text)
    bad = {r["value"] for r in M.failures()["shared"]}
    assert bad == {"0.11", "0.35", "1.1", "1.2", "1.5"}


def test_the_guard_fires_on_a_stale_named_value(monkeypatch) -> None:
    """What a figure left behind after a correction would look like."""
    text = M.paper_text().replace(r"P_0=3.6\cdot10^{13}", r"P_0=8.9\cdot10^{13}", 1)
    monkeypatch.setattr(M, "paper_text", lambda: text)
    bad = {r["name"] for r in M.failures()["constants"]}
    assert "P_0" in bad


def test_the_paper_carries_the_table_and_says_none_is_an_error() -> None:
    text = M.paper_text()
    assert "*Constants that share a value.*" in text
    assert "None of these is an error" in text
    assert "reading across them" in text
    assert "`tools/manuscript_self_audit.py`" in text
    for v in ("0.35", "0.11", "1.2", "1.5"):
        assert v in text


# --- generating the list rather than curating it ---


def test_the_clusterer_scans_math_mode_only() -> None:
    """Section numbers and prose cross-references vanish; 356 math-mode decimals remain."""
    c = M.cluster_coverage()
    assert 300 < c["numerals_scanned"] < 420
    assert 10 <= len(c["flagged"]) <= 20
    # "Theorem 4.7" and "Section 1.2 Related work" are prose, not math
    flagged = set(c["flagged"])
    assert "4.7" not in flagged and "4.4" not in flagged


def test_the_clusterer_found_what_curation_missed() -> None:
    """1.1 and 1.2's fourth role were found by clustering, not by eye."""
    c = M.cluster_coverage()
    assert "1.1" in c["genuinely_detected"]
    assert "1.1" in M.SHARED_VALUES and len(M.SHARED_VALUES["1.1"]) == 3
    assert len(M.SHARED_VALUES["1.2"]) == 4
    rows = {r["value"]: r for r in M.cluster_numerals()}
    assert rows["1.1"]["cluster_count"] == 3
    assert set(rows["0.11"]["clusters"]) == {"uhP^{-1/4}", "P^{-5/6}", "kP^{-7/8}"}


def test_two_rows_are_flagged_for_the_wrong_reason() -> None:
    """0.35 and 1.5 agree with curation by coincidence, not by detection."""
    c = M.cluster_coverage()
    wrong = c["flagged_for_the_wrong_reason"]
    assert set(wrong) == {"0.35", "1.5"}
    for v, why in wrong.items():
        assert "one quantity" in why or "multiplies nothing" in why or "fraction" in why
    rows = {r["value"]: r for r in M.cluster_numerals()}
    # both clusters of 0.35 are the Stage-4 curvature, in two notations
    assert set(rows["0.35"]["clusters"]) == {"uhP^{-3/4}", "uh"}
    assert set(rows["1.5"]["clusters"]) == {"hP^{1/2}", "hY"}
    assert "0.35" not in c["genuinely_detected"] and "1.5" not in c["genuinely_detected"]


def test_the_generator_cannot_replace_the_curated_list() -> None:
    """Which is the point: they miss opposite things."""
    c = M.cluster_coverage()
    assert c["curated_only"] == []          # every curated value is flagged, some by luck
    assert len(c["genuinely_detected"]) < len(c["curated"])
    assert len(c["flagged"]) > len(c["curated"])   # and the generator over-flags


def test_the_table_is_excluded_from_its_own_scan() -> None:
    """The table quotes the collisions it documents; counting those is self-agreement."""
    import re
    text = M.paper_text()
    assert M.SHARED_TABLE_ANCHOR in text
    before = len(M.cluster_numerals())
    stripped = text.replace(M.SHARED_TABLE_ANCHOR, "REMOVED")
    assert stripped != text
    assert before == len(M.cluster_numerals())     # deterministic, table already excluded


def test_the_paper_says_which_rows_are_coincidence() -> None:
    text = M.paper_text()
    assert "but for the wrong reason" in text
    assert "two notations for one quantity" in text
    assert "is a coincidence" in text
    assert "miss opposite things" in text
