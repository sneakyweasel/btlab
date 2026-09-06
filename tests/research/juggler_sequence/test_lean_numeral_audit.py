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
    """Printed numbers citing no function; the count is recorded rather than hidden.

    Three when this guard was written; the twelve-exponent sweep has since been given a
    stated ladder in decoration_budget, so two remain, both in the other session's module.
    """
    un = A.unanchored_measurements()
    assert len(un) == 2, [r["printed"] for r in un]
    why = " ".join(r["why"] for r in un)
    assert "20,000-sample" in why and "ten-sample" in why
    assert "no sweep exists" not in why
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


# --- the twelve exponents, now a stated ladder ---


def test_the_level1_sweep_ladder_is_the_printed_one() -> None:
    import inspect
    from research.juggler_sequence import decoration_budget as DB
    sig = inspect.signature(DB.level1_exponent_sweep)
    assert sig.parameters["ps"].default == (10**4, 3 * 10**4, 10**5, 10**6)
    assert sig.parameters["ks"].default == (1, 2, 4)
    assert DB.LEVEL1_SWEEP_PS == sig.parameters["ps"].default
    assert DB.LEVEL1_SWEEP_KS == sig.parameters["ks"].default
    assert len(DB.LEVEL1_SWEEP_PS) * len(DB.LEVEL1_SWEEP_KS) == 12
    text = A.paper_text()
    assert r"\(P\in\{10^4,3\cdot10^4,10^5,10^6\}\)" in text
    assert "`decoration_budget.level1_exponent_sweep`, which is that ladder" in text


def test_the_sweep_runs_and_the_smallest_P_is_the_outlier() -> None:
    """Cheap subset: the two smallest P, where the one calibration outlier lives."""
    from research.juggler_sequence import decoration_budget as DB
    s = DB.level1_exponent_sweep(ps=(10**4, 3 * 10**4))
    assert s["n"] == 6 and s["ks"] == [1, 2, 4]
    assert s["square_root_exponent"] == 0.5 and s["no_cancellation_exponent"] == 1.0
    assert DB.level1_sweep_outside_calibration(s) == ["10000,1"]
    assert abs(s["exponents"]["10000,1"] - 0.3866) < 5e-3


def test_the_paper_now_states_which_figures_belong_to_which_scope() -> None:
    """[0.94, 1.12] is the P = 10^6 range; over P >= 10^5 it is [0.87, 1.15]."""
    text = A.paper_text()
    assert r"sits in \([0.94,1.12]\) at \(P=10^6\)" in text
    assert r"the honest interval is" in text and r"\([0.87,1.15]\)" in text
    assert r"reaches \(0.874\) at \(k=4\) and \(1.150\) at" in text
    # the mean and the outlier are printed at the precision the sweep gives
    assert r"twelve" in text and r"exponents with mean \(0.487\)" in text
    assert r"\(P=10^4\), \(k=1\), at \(0.3866\)" in text
    assert r"\([0.4268,0.5684]\)" in text


def test_the_unanchored_count_fell_by_one() -> None:
    un = A.unanchored_measurements()
    assert len(un) == 2, [r["printed"] for r in un]
    assert all("twelve" not in r["why"] for r in un)


# --- the separation is not a feature of one P ---


def test_the_control_crossover_is_where_the_separation_opens() -> None:
    """L* = sqrt(P)/3, and the fitted window clears it at P = (512/3)^2 = 2.91e4."""
    from research.juggler_sequence import decoration_budget as DB
    assert abs(DB.level1_control_crossover(10**6)["P_where_window_clears"]
               - (512 / 3) ** 2) < 1.0
    assert not DB.level1_control_crossover(10**4)["window_clears"]
    assert DB.level1_control_crossover(3 * 10**4)["window_clears"]
    for P in (10**4, 10**6):
        c = DB.level1_control_crossover(P)
        assert abs(c["lambda"] - 3 * P**-0.5) < 1e-12
        assert abs(c["crossover_L"] - P**0.5 / 3) < 1e-9
        assert abs(c["L_min"] - P / 512) < 1e-9


def test_the_kernel_is_flat_and_the_control_climbs() -> None:
    """Cheap subset: the two smallest P, straddling the crossover."""
    from research.juggler_sequence import decoration_budget as DB
    t = DB.level1_control_trend(ps=(10**4, 3 * 10**4))
    assert [r["window_clears"] for r in t["rows"]] == [False, True]
    assert t["control_increases"]
    lo, hi = t["rows"]
    assert abs(lo["kernel"] - 0.3866) < 5e-3 and abs(lo["control"] - 0.4902) < 5e-3
    assert abs(hi["kernel"] - 0.5081) < 5e-3 and abs(hi["control"] - 0.5733) < 5e-3
    # at the P whose window does not clear, there is no separation to speak of
    assert lo["gap"] < 0.11
    assert DB.LEVEL1_TREND_PS[0] == 10**4 and len(DB.LEVEL1_TREND_PS) == 6


def test_the_paper_records_the_trend_and_its_mechanism() -> None:
    text = A.paper_text()
    assert "it opens where the" in text and "second-derivative test says it must" in text
    assert r"\(\lambda=3n^{-1/2}\sim3P^{-1/2}\)" in text
    assert r"\(L\gg1/\lambda=\sqrt P/3\)" in text
    assert r"\(P>(512/3)^2=2.91\cdot10^{4}\)" in text
    assert "`decoration_budget.level1_control_trend`" in text
    for figure in ("0.4902", "0.9852", "0.4928", "0.170"):
        assert figure in text, figure
    # the six rows of the table
    for P in (r"3\cdot10^{4}", r"3\cdot10^{5}", r"3\cdot10^{6}"):
        assert P in text, P


def test_the_mechanism_is_arithmetic_not_assertion() -> None:
    """L_min >= L* is sqrt(P) >= 2 bins / 3 with bins = 256."""
    bins = 256
    assert abs((2 * bins / 3) ** 2 - (512 / 3) ** 2) < 1e-9
    for P, clears in ((10**4, False), (29127, False), (3 * 10**4, True)):
        assert ((P / 2) / bins >= P**0.5 / 3) is clears, P


# --- and the kernel, which has no crossover at all ---


def test_the_kernel_condition_has_no_crossover_in_P() -> None:
    """2c' = (891k/512) n^(1/32) > 1 from n ~ 2e-8; there is no threshold to look for."""
    from research.juggler_sequence import decoration_budget as DB
    for P in (10**4, 3 * 10**6):
        c = DB.level1_kernel_condition(P)
        assert c["condition_met"]
        assert abs(c["two_c_prime"] - (891 / 512) * P ** (1 / 32)) < 1e-9
    assert abs(DB.level1_kernel_condition(10**4)["two_c_prime"] - 2.321) < 5e-3
    assert abs(DB.level1_kernel_condition(3 * 10**6)["two_c_prime"] - 2.773) < 5e-3
    start = DB.level1_kernel_condition(10**4)["P_where_condition_starts"]
    assert start < 1e-7                                  # below any P one would run
    assert DB.level1_kernel_condition(10**4)["P_where_two_c_prime_reaches_ten"] > 1e23
    # k scales it linearly, so k = 4 is already comfortable
    assert DB.level1_kernel_condition(10**4, k=4)["two_c_prime"] > 9


def test_the_low_reading_is_spread_and_comes_with_a_high_one() -> None:
    """0.3866 at P = 10^4, k = 1 is a draw: k = 8 at the same P reads 0.584."""
    from research.juggler_sequence import decoration_budget as DB
    r = DB.level1_kernel_k_spread(10**4)
    assert r["ks"] == [1, 2, 3, 4, 5, 6, 7, 8]
    assert abs(r["mean"] - 0.4771) < 5e-3
    assert r["outside_low"] == [1] and r["outside_high"] == [8]
    assert len(r["outside_interval"]) == 2               # what 90% predicts for eight draws
    assert r["terms"] == 5000                            # exactly the calibration's N


def test_the_spread_falls_with_P_and_that_is_the_instrument() -> None:
    from research.juggler_sequence import decoration_budget as DB
    a = DB.level1_kernel_k_spread(10**4, ks=(1, 2, 3, 4))
    b = DB.level1_kernel_k_spread(10**5, ks=(1, 2, 3, 4))
    assert b["spread"] < a["spread"]
    assert b["terms"] == 10 * a["terms"]


def test_the_paper_says_one_exponent_does_both_jobs() -> None:
    text = A.paper_text()
    assert "The kernel has no such threshold" in text
    assert r"\(2c'=\tfrac{891k}{512}n^{1/32}\)" in text
    assert r"\approx2\cdot10^{-8}\)" in text
    assert "One exponent does both" in text
    assert "it does the second from the start and" in text
    assert "`decoration_budget.level1_kernel_k_spread`" in text
    for figure in ("0.4771", "0.584", "2.32", "2.77"):
        assert figure in text, figure


# --- at most one, not none ---


def test_the_drift_window_holds_at_most_one_and_the_density_is_measured() -> None:
    """1/c' < 2 gives at most one odd integer, with density 1/(2c') -- never certainly none."""
    from research.juggler_sequence import decoration_budget as DB
    for P, want in ((10**4, 0.4309), (10**6, 0.3732)):
        r = DB.level1_drift_window_occupancy(P)
        assert r["holds_at_most_one"] and r["window_length"] < 2.0
        assert abs(r["predicted_occupancy"] - want) < 5e-4
        assert abs(r["counted_occupancy"] - r["predicted_occupancy"]) < 1e-3
        assert r["predicted_occupancy"] > 0.0
        assert r["ever_holds_none_for_certain"] is False
    # the density is 1/(2c') and falls only like n^(-1/32)
    a = DB.level1_drift_window_occupancy(10**4)["predicted_occupancy"]
    b = DB.level1_drift_window_occupancy(10**8)["predicted_occupancy"]
    assert 1.0 < a / b < 1.4


def test_two_c_prime_at_P0_is_four_point_six_not_three_point_four() -> None:
    """A figure I quoted from interpolation; the exponent is n^(1/32) and it is 4.615."""
    from research.juggler_sequence import decoration_budget as DB
    from research.juggler_sequence import p0_certificate as PC
    P0 = PC.certificate()["P0"]
    c = DB.level1_kernel_condition(P0)
    assert abs(c["two_c_prime"] - 4.615) < 5e-3
    assert abs(1.0 / c["two_c_prime"] - 0.2167) < 5e-4      # the occupancy at P_0
    assert c["two_c_prime"] < 5.0                            # a factor under five, not ten


def test_the_paper_records_the_erratum_and_answers_the_size_question() -> None:
    text = A.paper_text()
    assert "at most one, not none" in text
    assert "so it contains no integer at all" not in text.split("> *Erratum")[0]
    assert "it holds *at most one*" in text
    assert "window with one term is not a sum" in text
    assert "nothing printed depends on how much larger than" in text
    assert "it exceeds it by a factor under five" in text
    assert "`decoration_budget.level1_drift_window_occupancy`" in text
    for figure in ("0.43", "0.37", "0.22", "4.62", "2.32"):
        assert figure in text, figure


# --- and what "fatal" costs ---


def test_expanding_a_one_term_window_returns_the_whole_mass() -> None:
    """Two orders worse than trivial, not merely no better."""
    from research.juggler_sequence import decoration_budget as DB
    from research.juggler_sequence import p0_certificate as PC
    r = DB.lemma37_one_term_window_cost(int(PC.certificate()["P0"]))
    assert abs(r["b_mass"] - 76.4) < 0.2
    assert abs(r["v_mass"] - 41.3) < 0.2
    assert abs(r["total_mass"] - 117.7) < 0.4
    assert r["trivial_bound_on_one_term"] == 1.0
    assert r["total_mass"] > 100                        # two orders
    for P, want in ((10**6, 60.1), (10**24, 197.4)):
        assert abs(DB.lemma37_one_term_window_cost(P)["total_mass"] - want) < 0.5, P


def test_the_flat_term_alone_reaches_the_trivial_bound_at_the_boundary() -> None:
    """8(1+c)/U is exactly 1 at U = 8(1+c): the second edge, before any mode."""
    from research.juggler_sequence import decoration_budget as DB
    r = DB.lemma37_one_term_window_cost(10**6)
    assert abs(r["flat_per_point"] - 1.0) < 1e-12
    assert r["flat_alone_reaches_trivial"]
    # and buying that term back costs b-mass, which carries log U
    slack = DB.lemma37_one_term_window_cost(10**6, t_slack=100.0)
    assert slack["flat_per_point"] < 0.02
    assert slack["b_mass"] > r["b_mass"]


def test_both_failures_are_driven_by_c() -> None:
    """The window is short because c is large; the mass is large because c is large."""
    from research.juggler_sequence import decoration_budget as DB
    small, big = DB.lemma37_one_term_window_cost(10**6), DB.lemma37_one_term_window_cost(10**24)
    assert big["B"] > small["B"] and big["total_mass"] > small["total_mass"]
    w_small = DB.level1_drift_window_occupancy(10**6)["window_length"]
    w_big = DB.level1_drift_window_occupancy(10**8)["window_length"]
    assert w_big < w_small                              # window shrinks as the mass grows


def test_the_paper_prices_it_and_says_the_paper_does_not_need_it() -> None:
    text = A.paper_text()
    assert "can be priced, which says why care does not help" in text
    assert "returns the whole mass" in text
    assert "There are" in text and "two edges and not one" in text
    assert "The paper needs only" in text and "no better than trivial" in text
    assert "`decoration_budget.lemma37_one_term_window_cost`" in text
    for figure in ("40.5", "76.4", "117.7", "197.4"):
        assert figure in text, figure
    # re-lettered for Section 7: the lemma's B and T are this section's c and U
    assert r"e(-c\{t\})" in text and r"\(U\ge8(1{+}c)\)" in text


# --- and the mass at every site that uses the lemma ---


def test_every_lemma37_site_is_logarithmic() -> None:
    """coefficient = 2 max(beta, tau) + 4 iota, finite at all ten sites."""
    from fractions import Fraction as Fr
    from research.juggler_sequence import decoration_budget as DB
    r = DB.lemma37_site_masses()
    assert len(r["rows"]) == 10 and r["all_logarithmic"]
    assert abs(r["max_coefficient"] - float(Fr(9, 4))) < 1e-9
    assert abs(r["min_coefficient"] - float(Fr(5, 8))) < 1e-9
    for row in r["rows"]:
        assert 0.5 < row["coefficient"] <= 2.25, row["site"]
        assert row["mass"] > 0


def test_the_two_fattest_sites_are_the_two_carrying_R0() -> None:
    from fractions import Fraction as Fr
    from research.juggler_sequence import decoration_budget as DB
    r = DB.lemma37_site_masses()
    assert set(r["fattest_sites"]) == {"Thm 4.1 St.3(s1)", "Thm 4.1 St.6(D2)"}
    for row in r["rows"]:
        if row["site"] in r["fattest_sites"]:
            assert abs(row["J_exponent"] - 5 / 16) < 1e-12     # Stage 2's truncation
    # v-mass 4*(5/16) = 5/4 outweighs the b-mass 2*(1/2) = 1
    assert Fr(4) * Fr(5, 16) == Fr(5, 4) and Fr(5, 4) > 1


def test_the_paper_s_largest_log_power_sits_on_its_thinnest_site() -> None:
    """Theorem 6.3 carries log^(15/4) and has the smallest mass coefficient, 5/8."""
    from research.juggler_sequence import decoration_budget as DB
    from research.juggler_sequence import p0_certificate as PC
    r = DB.lemma37_site_masses()
    assert r["thinnest_site"] == "Thm 6.3 depth five"
    thin = [x for x in r["rows"] if x["site"] == "Thm 6.3 depth five"][0]
    assert abs(thin["T_exponent"] - 5 / 16) < 1e-12            # R_0, not P^(1/2)
    assert thin["J_exponent"] is None
    powers = {x["log_power"] for x in PC.log_absorption_thresholds()}
    assert 3.75 in powers                                       # log^(15/4) is Thm 6.3's
    assert max(powers) == 3.75


def test_the_paper_carries_the_site_table() -> None:
    text = A.paper_text()
    assert "The mass this lemma costs, at every site that uses it" in text
    assert "`decoration_budget.lemma37_site_masses`" in text
    assert "the coefficient never exceeds" in text
    assert "worth reading twice" in text
    for frag in (r"\text{Thm 6.3 depth five}", r"\text{Lemma 5.2(iii)}", "47/24", "11/12"):
        assert frag in text, frag
