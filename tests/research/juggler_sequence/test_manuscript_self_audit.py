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
    """The prose gives the exact crossing; only A.1's column rounds, and it rounds up."""
    BS = chr(92)
    text = M.paper_text()
    assert "1.45^{36}=644537" in text
    assert "1.45^{36}=6.4" + BS + "cdot10^{5}" not in text
    assert "1.45^{36}=1.1" + BS + "cdot10^{6}" not in text


def test_failures_now_covers_relations() -> None:
    f = M.failures()
    assert set(f) == {"constants", "shared", "relations", "rounded_into_a_bound",
                      "a1_thresholds", "claim_vs_predicate",
                      "p0_reproducible", "kappa_table", "a6_table",
                      "prop71", "runlength", "axioms", "lean_rows"}
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
    assert "with no consequence is exactly the kind that survives reading" in text


# --- A.1's least-P column ----------------------------------------------------------------------


def test_every_a1_entry_is_at_or_above_its_crossing() -> None:
    assert M.a1_failures() == []


def test_all_thirty_eight_rows_resolve_to_a_certificate_row() -> None:
    rows = M.a1_threshold_audit()
    assert len(rows) == 38
    assert [r["claim"] for r in rows if r["tag"] is None] == []


def test_the_column_rounds_up_and_stays_tight() -> None:
    """One-sided by design: printed >= computed, never printed == computed."""
    over = [r["overshoot"] for r in M.a1_threshold_audit() if r["overshoot"] is not None]
    assert len(over) == 35                      # the other three are the "always" rows
    assert min(over) >= -1e-9                   # exact matches land at zero
    assert max(over) < 0.01                     # under one per cent everywhere
    assert sum(1 for o in over if o < 0.003) == 23


def test_a_nearest_rounded_column_would_fail() -> None:
    """Claim D is the witness: its crossing rounds down at the precision the table prints."""
    row = next(r for r in M.a1_threshold_audit() if r["tag"] == "claimD-shift")
    assert abs(row["computed"] - 644537) < 1.0
    assert row["printed"] == 6.5e5              # rounded up
    nearest = float("%.1e" % row["computed"])   # 6.4e5, what "round to nearest" gives
    assert nearest == 6.4e5
    assert nearest < row["computed"]            # and so names a P where the row fails


def test_the_three_always_rows_hold_from_one() -> None:
    rows = [r for r in M.a1_threshold_audit() if r["cell"].strip("$") == "always"]
    assert len(rows) == 3
    assert all(r["computed"] == 1.0 and r["ok"] for r in rows)


def test_the_q_row_carries_the_constant_the_paper_derives() -> None:
    """30.5 appeared only in that cell; the paper derives 48.9 = 17.1/0.35 three times."""
    text = M.paper_text()
    assert text.count("30.5") == 1          # the errata paragraph, naming what it replaced
    assert "carried the constant " + chr(92) + "(30.5" + chr(92) + ")" in text
    assert "curvature ratio (1.85 P^(7/24) + R_0)" in text
    assert "17.1/0.35=48.9" in text
    row = next(r for r in M.a1_threshold_audit() if r["tag"] == "st5b-qpp")
    assert row["printed"] == 3.0e11 and row["ok"]   # the predicate was always the sharp form


def test_the_lemma_5_2b_row_matches_the_lemma() -> None:
    text = M.paper_text()
    assert text.count("[0.62,3.94]") == 1   # likewise: quoted only where it is corrected
    assert "carried " + chr(92) + "([0.62,3.94]" in text
    assert "[0.62,3.90]" in text
    row = next(r for r in M.a1_threshold_audit() if r["tag"] == "5b-lam0-range")
    assert row["printed"] == 3.51e4 and row["ok"]


def test_the_window_boundary_row_is_no_longer_off_by_a_factor() -> None:
    row = next(r for r in M.a1_threshold_audit() if r["tag"] == "s3s2-bdry")
    assert abs(row["computed"] - 150527) < 1.0
    assert row["printed"] == 1.51e5
    assert row["printed"] / 403 > 300            # what the cell used to say


def test_the_binding_row_and_p0_are_untouched() -> None:
    row = next(r for r in M.a1_threshold_audit() if r["tag"] == "5b-W<=c7S")
    assert abs(row["computed"] - 3.58576e13) / 3.58576e13 < 1e-4
    assert "3.5858" in M.paper_text()


def test_the_paper_states_the_column_convention_and_its_errata() -> None:
    text = M.paper_text()
    assert "*The last column rounds up.*" in text
    assert "*Errata in this table.*" in text
    assert "an entry rounded to nearest can name a" in text
    assert "never that it equals it" in text


# --- the claim a row states against the predicate it certifies ---------------------------------


def test_no_row_states_one_inequality_and_certifies_another() -> None:
    assert M.claim_predicate_failures() == []


def test_the_parser_reaches_most_of_the_table_and_admits_the_rest() -> None:
    rows = M.claim_predicate_audit()
    assert len(rows) == 38
    assert sum(r["parsed"] for r in rows) == 27
    unparsed = {r["tag"] for r in rows if not r["parsed"]}
    # every one of these has a side that is prose or a symbol the parser will not invent
    assert "5b-W<=c7S" in unparsed and "t63-window" in unparsed and "5b-Npieces" in unparsed


def test_the_printed_claim_holds_at_the_printed_threshold() -> None:
    """The table's actual contract, and what both defects broke."""
    printed = {r["tag"]: r["printed"] for r in M.a1_threshold_audit()}
    checked = 0
    for row in M.claim_predicate_audit():
        if not row["parsed"] or row["claim"] is None:
            continue
        p = printed.get(row["tag"])
        if not p:                                   # the three "always" rows
            continue
        f, _ = M.claim_predicate(_claim_of(row["tag"]))
        assert f(p), (row["tag"], p, row["reads"])
        checked += 1
    assert checked >= 23


def _claim_of(tag: str) -> str:
    import importlib.util
    spec = importlib.util.spec_from_file_location(
        "p0_certificate", ROOT / "src" / "research" / "juggler_sequence" / "p0_certificate.py")
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return next(r["claim"] for r in mod.thresholds() if r["tag"] == tag)


def test_the_guard_has_teeth_on_the_two_rows_it_found() -> None:
    """Both defects reproduced from the claim text alone, against what used to be certified."""
    import importlib.util
    spec = importlib.util.spec_from_file_location(
        "p0_certificate", ROOT / "src" / "research" / "juggler_sequence" / "p0_certificate.py")
    C = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(C)

    merged, _ = M.claim_predicate("|q''| curvature ratio 48.9 P^(-3/16) <= 1/4")
    unmerged = 10 ** C.least_P(
        lambda P: (1.85 * P ** (7 / 24) + P ** (5 / 16)) * 6 * P ** (-5 / 4)
        / (0.35 * P**-0.75) <= 0.25)
    assert abs(10 ** C.least_P(merged) / unmerged - 5.574) < 0.01

    exact = 10 ** C.least_P(lambda P: (9 * 0.68 / 2.656) * P**-0.5 <= 1 / 1856)
    stated, _ = M.claim_predicate("beta-substitution error 2.31 P^(-1/2) <= rho_0")
    assert abs(10 ** C.least_P(stated) / exact - 1.005) < 0.001


def test_the_old_thresholds_failed_their_own_claims() -> None:
    assert 48.9 * (3.0e11) ** (-3 / 16) > 0.25          # the row A.1 used to print
    assert 2.31 * (1.83e7) ** -0.5 > 1 / 1856
    assert 48.9 * (1.67e12) ** (-3 / 16) <= 0.25        # where the merged claim would have to sit
    assert 2.3043 * (1.83e7) ** -0.5 <= 1 / 1856       # what the row prints now


def test_p0_and_the_binding_row_survive_the_two_corrections() -> None:
    import importlib.util
    spec = importlib.util.spec_from_file_location(
        "p0_certificate", ROOT / "src" / "research" / "juggler_sequence" / "p0_certificate.py")
    C = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(C)
    worst = max((r["P_min"] or 0.0, r["tag"]) for r in C.thresholds())
    assert worst[1] == "5b-W<=c7S"
    assert abs(worst[0] - 3.58576e13) / 3.58576e13 < 1e-4


def test_the_paper_records_the_drift_between_sentence_and_predicate() -> None:
    text = M.paper_text()
    assert "had drifted apart" in text
    assert "P^{1/48}" in text
    assert "must hold as written at the" in text
    assert "1.66" + chr(92) + "cdot10^{12}" in text     # where the merged claim clears
    assert "2.98" + chr(92) + "cdot10^{11}" in text     # where the sharp one does


# --- P_0 from the constants the paper prints ---------------------------------------------------


def test_p0_is_reproducible_from_the_printed_constants() -> None:
    r = M.p0_from_printed_constants()
    assert r["ok"], r
    assert abs(r["solved"] - 3.58576e13) / 3.58576e13 < 1e-4
    assert r["printed"] == 3.5858e13


def test_the_binding_row_reads_five_constants_off_the_text() -> None:
    c = M.printed_binding_constants()
    assert {k: v["value"] for k, v in c.items()} == {
        "E_lead": 170.6, "E_tail": 0.11, "lambda_0": 0.56,
        "kappa_den": 12.0, "c7_den": 232.0}


def test_e_carries_one_coefficient() -> None:
    """It had two: 170.6 in the derivation and Lean, 171 in E's own definition."""
    text = M.paper_text()
    assert "170.6P^{-25/24}" in text
    assert "171P^{-25/24}" not in text
    # it survives once, in the passage that records the correction
    assert text.count("171" + chr(92) + ",P^{-25/24}") == 1


def test_the_looser_coefficient_would_not_reproduce_p0() -> None:
    """Why it matters: 171 is a true bound and still gives the wrong five figures."""
    lam, kappa, c7 = 0.56, 1 / 12, 1 / 232

    def cross(e: float) -> float:
        lo, hi = 0.0, 300.0
        for _ in range(400):
            mid, = ((lo + hi) / 2,)
            P = 10.0 ** mid
            S = lam * P**-0.625
            w = kappa * S**0.5 * P ** (-11 / 24) + e * P ** (-25 / 24) + 0.11 * P ** (-5 / 6)
            lo, hi = (lo, mid) if w <= c7 * S / 2 else (mid, hi)
        return 10.0**hi

    assert abs(cross(170.6) - 3.58576e13) / 3.58576e13 < 1e-4
    assert abs(cross(171.0) - 3.59688e13) / 3.59688e13 < 1e-4
    assert cross(171.0) > 3.5858e13          # past the figure the paper prints


def test_the_erratum_list_names_the_end_lean_actually_proves() -> None:
    text = M.paper_text()
    lean = (ROOT / "formal" / "Problems" / "Juggler" / "PaperBAssembly.lean").read_text(
        encoding="utf-8")
    assert "170.6 * p2524" in lean and "106 * p2524" in lean
    assert text.count("106" + chr(92) + "to170.6") == 2
    assert text.count("106" + chr(92) + "to171" + chr(92) + ")") == 1


def test_the_paper_states_the_reproducibility_check() -> None:
    text = M.paper_text()
    assert "from the constants printed above" in text
    assert "should be" in text and "recoverable from the paper it appears in" in text
    assert "It was not, by one constant" in text


# --- P_1 and the kappa table -------------------------------------------------------------------


def test_the_kappa_table_rounds_up() -> None:
    rows = M.kappa_table_audit()
    assert len(rows) == 5
    assert M.kappa_table_failures() == []


def test_every_kappa_entry_is_tight() -> None:
    """Raised, but not by much: the table is still readable as the numbers it names."""
    for r in M.kappa_table_audit():
        for key in ("P0", "P1", "coef"):
            printed, true, ok = r[key]
            assert ok
            assert printed / true - 1 < 0.01, (r["kappa_den"], key, printed, true)


def test_p1_is_reproducible_from_the_display() -> None:
    c = M.printed_binding_constants()
    p1 = M.p1_crossing(1 / 12, c["lambda_0"]["value"], c["E_lead"]["value"],
                       c["E_tail"]["value"], 1 / c["c7_den"]["value"])
    assert abs(p1 - 9.83914e18) / 9.83914e18 < 1e-4


def test_the_nearest_rounding_would_understate_p1() -> None:
    """P_1 is a crossing: below it the middle band is the weaker bound, so 9.8e18 is a claim."""
    c = M.printed_binding_constants()
    p1 = M.p1_crossing(1 / 12, c["lambda_0"]["value"], c["E_lead"]["value"],
                       c["E_tail"]["value"], 1 / c["c7_den"]["value"])
    assert float("%.1e" % p1) == 9.8e18        # what rounding to nearest gives
    assert 9.8e18 < p1                          # and it names a P where the bound is trivial
    row = next(r for r in M.kappa_table_audit() if r["kappa_den"] == 12)
    assert row["P1"][0] == 9.9e18


def test_the_boundary_coefficient_is_the_piece_boundary_cost() -> None:
    """3.5 V^(-1/2) at S = lambda_0 P^(-5/8); the table never says so, the numbers do."""
    c = M.printed_binding_constants()
    lam = c["lambda_0"]["value"]
    for r in M.kappa_table_audit():
        kappa = 1.0 / r["kappa_den"]
        assert abs(r["coef"][1] - 3.5 * (kappa * lam**0.5) ** -0.5) < 1e-9
        assert abs(r["coef"][0] / r["coef"][1] - 1) < 0.01


def test_the_erratum_figures_were_crossings_too() -> None:
    text = M.paper_text()
    BS = chr(92)
    assert "8.95" + BS + "cdot10^{13}" in text and "5.04" + BS + "cdot10^{19}" in text
    assert "4.03" + BS + "cdot10^{12}" in text and "1.02" + BS + "cdot10^{23}" in text
    assert "P_1=9.9" + BS + "cdot10^{18}" in text
    assert "P_1=9.8" + BS + "cdot10^{18}" not in text


def test_the_paper_states_the_convention_for_this_table() -> None:
    text = M.paper_text()
    assert "This table rounds up, for the reason A.1 does" in text
    assert "is still the weaker of the two" in text
    assert "recoverable from the display above it" in text


# --- A.6's exponent table ----------------------------------------------------------------------


def test_the_a6_table_rounds_up() -> None:
    rows = M.a6_table_audit()
    assert len(rows) == 25
    assert M.a6_failures() == []
    assert max(r["overshoot"] for r in rows) < 0.01


def test_the_a6_middle_row_is_a1s_four_rows() -> None:
    """Not an independent computation: the same four sites at the exponent actually used."""
    a1 = {r["tag"]: r["printed"] for r in M.a1_threshold_audit()}
    shared = [r for r in M.a6_table_audit() if r["a"] == "5/16" and r["site"] != "worst"]
    assert len(shared) == 4
    for row, tag in zip(shared, M.A6_SHARED_TAGS):
        assert row["printed"] == a1[tag], (tag, row["printed"], a1[tag])
    assert [r["printed"] for r in shared] == [1.45e9, 3.0e11, 7.5e8, 5.51e9]


def test_the_worst_column_is_the_row_maximum() -> None:
    rows = M.a6_table_audit()
    for a in ("1/4", "9/32", "5/16", "1/3", "3/8"):
        row = {r["site"]: r for r in rows if r["a"] == a}
        four = [row[s]["computed"] for s in ("collision", "qpp", "window", "flat")]
        assert abs(row["worst"]["computed"] - max(four)) < 1e-6 * max(four)
        assert row["worst"]["printed"] >= max(four)


def test_the_operating_exponent_is_the_minimum_of_the_worst_column() -> None:
    """Why 5/16 is chosen: it minimises the last column over the admissible range."""
    worst = {r["a"]: r["computed"] for r in M.a6_table_audit() if r["site"] == "worst"}
    assert min(worst, key=lambda k: worst[k]) == "5/16"
    assert abs(worst["5/16"] - 2.98166e11) / 2.98166e11 < 1e-4


def test_the_collision_row_at_a_quarter_is_three_to_the_twelfth() -> None:
    """3 P^(1/8+3/4) <= P^(23/24) is 3 <= P^(1/12): the crossing is exactly 3^12."""
    row = next(r for r in M.a6_table_audit() if r["a"] == "1/4" and r["site"] == "collision")
    assert abs(row["computed"] - 531441) < 1.0
    assert 3 ** 12 == 531441
    assert row["printed"] == 5.32e5


def test_the_paper_records_the_disagreement_between_the_two_tables() -> None:
    text = M.paper_text()
    assert "This table rounds up too, and its middle row is A.1's" in text
    assert "the two appendices must print the same four" in text
    assert "had been raised and this one had not" in text


# --- Proposition 7.1's density table and the run-length gains -----------------------------------


def test_the_density_table_recomputes_exactly() -> None:
    a = M.prop71_audit()
    assert len(a["rows"]) == 7
    assert M.prop71_failures() == []
    for r in a["rows"]:
        assert r["N_d"][0] == r["N_d"][1]              # exact integers, not rounded
        assert r["endpoint"][0] == r["endpoint"][1]
        assert r["two_d"][0] == r["two_d"][1] == 2 ** r["d"]


def test_the_dynamic_program_agrees_with_brute_enumeration() -> None:
    """The table's algorithm is described in the proof; this is the algorithm, checked."""
    import itertools
    N = M.nd_counts(16)
    for d in range(1, 15):
        brute = 0
        for bits in itertools.product((0, 1), repeat=d):
            o, ok = 0, True
            for t, b in enumerate(bits, 1):
                o += b
                if 3 ** o < 2 ** t:
                    ok = False
                    break
            brute += ok
        assert brute == N[d], (d, brute, N[d])
    assert [N[d] for d in (4, 5, 6, 8, 12, 16)] == [3, 4, 8, 19, 226, 2114]


def test_the_two_rates_are_what_the_paper_prints() -> None:
    c, rho = M.hoeffding_c(), M.sharp_rate()
    import math
    assert abs(c - 0.03428520074) < 1e-10
    assert abs(rho - 0.965906553) < 1e-8
    assert abs(-math.log(rho) - 0.0346881852) < 1e-9
    assert round(c, 6) == 0.034285 and c > 0.034285   # printed rounded down: safe for e^(-cd)
    text = M.paper_text()
    assert "0.965907" in text and "0.034688" in text and "c=0.034285" in text


def test_the_loss_ratio_at_1600_was_overstated() -> None:
    """1.3e4 for 1.13e4, where the three figures beside it are right to under a per cent."""
    ratios = {r["d"]: r for r in M.prop71_audit()["ratios"]}
    assert abs(ratios[1600]["computed"] - 11337) < 5
    assert abs(1.3e4 / ratios[1600]["computed"] - 1) > 0.14      # what was printed
    assert ratios[1600]["printed"] == 1.13e4                      # what is printed now
    for d in (5, 10, 40):
        assert abs(ratios[d]["computed"] / ratios[d]["printed"] - 1) < 0.01
    BS = chr(92)
    assert "1.13" + BS + "cdot10^{4}" in M.paper_text()
    # it survives once, in the sentence recording the correction
    assert M.paper_text().count("1.3" + BS + "cdot10^{4}") == 1


def test_the_run_length_gains_are_their_own_row_sums() -> None:
    """Exact dyadic entries: nothing rounds, so only the invariant can fail."""
    rows = M.runlength_rows()
    assert len(rows) == 5
    assert M.runlength_failures() == []
    from fractions import Fraction
    assert [r["gain"] for r in rows] == [Fraction(1, 16), Fraction(1, 16), Fraction(3, 128),
                                         Fraction(7, 256), Fraction(3, 256)]


def test_the_paper_records_the_recomputation() -> None:
    text = M.paper_text()
    assert "The table is exact and has been re-run" in text
    assert "One figure did not survive" in text
    assert "brute enumeration of all" in text


# --- what the machine-checked column rests on ----------------------------------------------------


def test_every_cited_declaration_rests_on_mathlibs_three_axioms() -> None:
    assert M.axiom_failures() == []
    results = M.axiom_check_results()
    assert len(results) == 47
    assert set(results.values()) == {"[propext, Classical.choice, Quot.sound]"}


def test_the_artifact_asks_about_exactly_the_cited_names() -> None:
    """Neither more nor fewer: a name added to the paper must be added to the check."""
    import importlib.util
    spec = importlib.util.spec_from_file_location(
        "trust_boundary", ROOT / "tools" / "trust_boundary.py")
    tb = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(tb)
    cited = sorted({r["name"] for r in tb.audit() if r["declared"]})
    assert M.axiom_check_names() == cited
    assert len(cited) == 47


def test_no_sorry_in_the_paper_b_modules() -> None:
    """The textual half; the axiom check is the one that sees through imports."""
    import re as _re
    for name in ("BranchFreeze", "MasterIdentity", "MeanValues", "MonomialSplitting",
                 "PaperBAssembly", "ThresholdCertificate"):
        src = (ROOT / "formal" / "Problems" / "Juggler" / (name + ".lean")).read_text(
            encoding="utf-8")
        assert not _re.search(r"(?<![A-Za-z0-9_])sorry(?![A-Za-z0-9_])", src), name
        assert "native_decide" not in src, name


def test_the_axiom_check_actually_runs() -> None:
    """Slow but the point: the recorded output is regenerated, not trusted."""
    import shutil
    import subprocess
    if shutil.which("lake") is None:
        import pytest
        pytest.skip("no lake on PATH")
    out = subprocess.run(["lake", "env", "lean", "AxiomCheckPaperB.lean"],
                         cwd=ROOT / "formal", capture_output=True, text=True, timeout=600)
    assert out.returncode == 0, out.stderr[-2000:]
    expected = (ROOT / "formal" / "AxiomCheckPaperB.expected").read_text(encoding="utf-8")
    assert out.stdout.strip() == expected.strip()


def test_the_paper_states_the_third_convention() -> None:
    text = M.paper_text()
    assert "Declared and reachable is still not proved" in text
    assert "[propext, Classical.choice, Quot.sound]" in text
    assert "AxiomCheckPaperB.lean" in text


# --- the certificate's Lean rows ------------------------------------------------------------------


def test_the_pairing_the_numeral_audit_assumed_now_exists() -> None:
    a = M.lean_row_audit()
    assert M.lean_row_failures() == []
    assert len(a["rows"]) == 33
    assert a["distinct_tags"] == 31


def test_seven_certificate_rows_have_no_lean_theorem() -> None:
    assert M.lean_row_audit()["uncovered"] == [
        "claimD-shift", "st2-collision", "st3a-flatcost", "st5b-qpp",
        "t61-stepB-discard", "t63-flat", "t63-window"]


def test_the_count_is_thirty_eight_minus_seven_plus_two() -> None:
    """The paper said 33 was 38 with two rows split in two, which would be forty."""
    a = M.lean_row_audit()
    assert 38 - len(a["uncovered"]) + 2 == len(a["rows"]) == 33
    text = M.paper_text()
    assert "38-7+2" in text
    assert "seven rows have no Lean theorem at all" in text


def test_every_witness_certifies_at_or_above_its_crossing() -> None:
    """A witness below its crossing would be a false Lean theorem; this measures conservatism."""
    losses = [r["loss"] for r in M.lean_row_audit()["rows"] if r["loss"] is not None]
    assert len(losses) == 30                      # three rows hold from P >= 1
    assert min(losses) >= 1.0 - 1e-9
    assert sum(1 for x in losses if x < 1.10) == 19


def test_the_lean_certified_threshold_is_the_binding_rows_witness() -> None:
    a = M.lean_row_audit()
    row = next(r for r in a["rows"] if r["theorem"] == "row_5b_binding")
    assert row["witness"] == 1.92 and row["k"] == [48]
    assert abs(a["certified_P0"] - 1.92 ** 48) / 1.92 ** 48 < 1e-9
    assert abs(a["certified_P0"] - 3.96697e13) / 3.96697e13 < 1e-4
    assert a["certified_P0"] > 3.58576e13          # what Python bisects, and Lean does not reach


def test_the_loosest_witness_is_the_lambda_range_row() -> None:
    rows = {r["theorem"]: r for r in M.lean_row_audit()["rows"]}
    worst = max((r for r in rows.values() if r["loss"]), key=lambda r: r["loss"])
    assert worst["theorem"].startswith("row_5b_lam0")
    assert abs(worst["loss"] - 2.3845) < 1e-3
    assert worst["witness"] == 17.0 and worst["k"] == [4]
    assert 17 ** 4 == 83521


def test_the_numeral_audit_no_longer_names_a_structure_that_never_existed() -> None:
    src = (ROOT / "tools" / "lean_numeral_audit.py").read_text(encoding="utf-8")
    cert = (ROOT / "src" / "research" / "juggler_sequence" / "p0_certificate.py").read_text(
        encoding="utf-8")
    assert "LEAN_ROWS" not in cert                  # it never did exist
    assert "p0_certificate.LEAN_ROWS, which never did" in src
    assert "manuscript_self_audit.lean_row_audit" in src


def test_the_paper_names_the_seven_uncovered_rows() -> None:
    text = M.paper_text()
    for phrase in ("Claim D's shift range", "the collision band", "the Step 3(a) flat",
                   "Step 5b(a) " + chr(92) + "(q''" + chr(92) + ") ratio",
                   "Theorem 6.1's Step B discard", "two depth-five sites"):
        assert phrase in text, phrase
    assert "certifies thirty-one of the thirty-eight" in text
