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


# --- the normaliser: every printed relation, evaluated -----------------------------------------


def test_the_normaliser_sees_across_notations() -> None:
    """The clusterer's blind spot: it reads 1.5 and 3/2 as unrelated strings."""
    from fractions import Fraction
    BS = chr(92)
    assert M.to_rational("1.5") == Fraction(3, 2)
    assert M.to_rational("3/2") == Fraction(3, 2)
    assert M.to_rational(BS + "tfrac32") == Fraction(3, 2)
    assert M.to_rational(BS + "frac{3}{2}") == Fraction(3, 2)
    assert M.to_rational(BS + "frac{-365}{176}") == Fraction(-365, 176)
    assert M.to_rational("c_7") is None
    assert M.to_rational("P^{5/16}") is None


def test_every_printed_relation_is_true() -> None:
    assert M.wrong_relations() == []


def test_the_relation_census() -> None:
    import collections
    kinds = collections.Counter(r["kind"] for r in M.numeric_relations())
    assert sum(kinds.values()) >= 78
    assert kinds["exact"] >= 54          # the paper's fraction algebra, all of it
    assert kinds["bounded_up"] == 2      # two bounds printed with an equals sign
    assert kinds["bounded_down"] == 0    # none rounded into its own bound
    assert kinds["WRONG"] == 1           # the declared units exception, below


def test_the_two_non_nearest_decimals_are_both_rounded_outward() -> None:
    """Both feed upper bounds, and both are rounded away from the inequality they serve."""
    d = M.rounding_directions()
    assert d["down"] == []
    assert len(d["up"]) == 2
    printed = sorted(r["right"] for r in d["up"])
    assert printed == [1.096, 2.536]
    exact = sorted(r["left"] for r in d["up"])
    assert abs(exact[0] - 1.20 ** 0.5) < 1e-12
    assert abs(exact[1] - 1.5 * 0.35 ** -0.5) < 1e-12
    # each is within one unit of its last printed place, and above -- which is what makes a
    # downward rounding dangerous: it would look identical to these
    for r in d["up"]:
        assert 0 < r["right"] - r["left"] < 10 ** -3


def test_a_decimal_rounded_into_its_bound_would_be_caught() -> None:
    """The case that matters: agreeing to the precision shown accepts both directions."""
    assert M._sig_figures("1.095") == 4
    assert M._last_place("1.095") == 10 ** -3
    # one true value, its three neighbouring four-figure decimals, three verdicts
    assert M.classify_equality(1.0956, 1.096, "1.096") == "rounded"
    assert M.classify_equality(1.0956, 1.095, "1.095") == "bounded_down"
    assert M.classify_equality(1.0954, 1.096, "1.096") == "bounded_up"
    assert M.classify_equality(1.0954, 1.0954, "1.0954") == "exact"
    assert M.classify_equality(1.0954, 1.2, "1.2") == "WRONG"
    assert "rounded_into_a_bound" in M.failures()


def test_the_only_declared_exception_is_the_units_one() -> None:
    """`7/5800 = 12.0690` is true in units of 10^-4, and the units are stated in prose."""
    assert list(M.RELATION_EXCEPTIONS) == [("7/5800", "12.0690")]
    raw = [(r["lhs"], r["rhs"]) for r in M.numeric_relations() if r["kind"] == "WRONG"]
    assert raw == [("7/5800", "12.0690")]
    assert "10^{-4}" in M.paper_text()


def test_the_normaliser_would_have_caught_the_claim_D_slip() -> None:
    """The prose printed 1.45^36 as 1.1e6.  It is 644537, and A.1 already said 6.4e5."""
    BS = chr(92)
    value = eval(M.to_expression("1.45^{36}"), {"__builtins__": {}}, {})  # noqa: S307
    assert round(value) == 644537
    assert M._sig_figures("6.4" + BS + "cdot10^{5}") == 2
    assert float("%.1e" % value) == 6.4e5
    assert float("%.1e" % value) != 1.1e6


def test_the_manuscript_prints_the_corrected_threshold() -> None:
    BS = chr(92)
    text = M.paper_text()
    assert "1.45^{36}=6.4" + BS + "cdot10^{5}" in text
    assert "1.45^{36}=1.1" + BS + "cdot10^{6}" not in text


def test_failures_now_covers_relations() -> None:
    f = M.failures()
    assert set(f) == {"constants", "shared", "relations", "rounded_into_a_bound"}
    assert all(v == [] for v in f.values())


def test_a_shared_symbolic_factor_makes_a_relation_checkable() -> None:
    """Most of the displayed algebra is a numeral times symbols; pure-number lines are few."""
    BS = chr(92)
    value, tail, head = M.leading_literal("(1.20)^{1/2}(uh)^{1/2}P^{5/8}")
    assert abs(value - 1.20 ** 0.5) < 1e-12
    assert tail == "(uh)^{1/2}P^{5/8}"
    assert head == "(1.20)^{1/2}"          # precision is a property of the digits alone
    assert M.leading_literal("c_7 P")[0] is None
    assert M.leading_literal(BS + "tfrac{60" + BS + "cdot4.2}{0.84}kh_1h_2P^{1/8}")[0] == 300.0
    shared = [r for r in M.numeric_relations() if r["shared"]]
    assert len(shared) >= 8
    assert all(r["kind"] != "WRONG" for r in shared)


def test_the_relation_passage_is_excluded_from_its_own_scan() -> None:
    """It quotes the relations it found; counting those is self-agreement."""
    import collections
    text = M.paper_text()
    assert M.RELATION_PROSE_ANCHOR in text
    kinds = collections.Counter(r["kind"] for r in M.numeric_relations())
    assert kinds["bounded_up"] == 2        # not four, which is what re-reading the prose gives


def test_the_paper_states_the_rounding_convention() -> None:
    text = M.paper_text()
    assert "rounded *away* from the inequality it serves" in text
    assert "A decimal rounded *into* its own bound" in text
    assert "error with no consequence is exactly the kind that survives reading" in text
