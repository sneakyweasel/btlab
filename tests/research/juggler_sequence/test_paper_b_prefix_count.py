"""The exact non-contracting count of Proposition 7.1, and Proposition 7.4's arc count.

Proposition 7.1 bounded the number of length-d words with no contracting prefix by Hoeffding
applied to the endpoint.  Two things were given away: the prefix constraint itself, and the
local-limit factor.  The count is a dynamic program over ``(t, o_t)``, so the exact number is
available; these tests check it against the paper's own figures and against the closed form it
replaces.
"""

from __future__ import annotations

import io
import math
import re
from fractions import Fraction
from pathlib import Path

import pytest

from research.juggler_sequence import paper_b_prefix_count as B

ROOT = Path(__file__).resolve().parents[3]
PAPER = ROOT / "docs" / "theory" / "juggler_parity_discrepancy_note.md"


def surviving_words(d: int) -> list[str]:
    out: list[str] = []

    def rec(w: str, o: int, t: int) -> None:
        if t == d:
            out.append(w)
            return
        for ch, s in (("O", 1), ("E", 0)):
            if B.survives(t + 1, o + s):
                rec(w + ch, o + s, t + 1)

    rec("", 0, 0)
    return out


# --- the count itself ---


def test_count_agrees_with_direct_enumeration() -> None:
    for d in range(1, 15):
        assert B.non_contracting(d) == len(surviving_words(d)), d


def test_depth_five_reproduces_corollary_6_4() -> None:
    """The four survivors give certificate density 7/8, which Corollary 6.4 reaches by
    counting contractors rather than words.  Two of the four are the open OOOO* split."""
    words = surviving_words(5)
    assert words == ["OOOOO", "OOOOE", "OOOEO", "OOEOO"]
    assert 1 - len(words) / 2 ** 5 == 7 / 8
    assert sum(1 for w in words if w.startswith("OOOO")) == 2


def test_depth_six_buys_nothing_without_depth_five() -> None:
    """All eight children of the depth-five survivors survive, so the density is 7/8 again."""
    assert B.non_contracting(6) == 8
    assert 1 - 8 / 2 ** 6 == 7 / 8


def test_every_e_rooted_word_contracts_immediately() -> None:
    """The step the proposition opens with: 3^0 < 2."""
    for d in range(1, 12):
        assert all(w.startswith("O") for w in surviving_words(d))


# --- the closed form it replaces is still a valid bound, and how lossy ---


def test_hoeffding_is_an_upper_bound_at_every_depth() -> None:
    for d in range(1, 41):
        assert B.non_contracting(d) <= B.hoeffding_bound(d), d


def test_two_losses_compound_and_neither_touches_the_rate() -> None:
    rows = {r["d"]: r for r in B.table(40)}
    # loss 1: dropping the prefix constraint
    assert abs(rows[5]["endpoint_only"] / rows[5]["N_d"] - 1.50) < 0.01
    assert abs(rows[24]["endpoint_only"] / rows[24]["N_d"] - 4.44) < 0.01
    # both together
    for d, want in ((5, 6.7), (10, 11.4), (40, 43.6)):
        got = rows[d]["density_hoeffding"] / rows[d]["density_exact"]
        assert abs(got - want) < 0.1, (d, got)
    # the exponential rate is essentially unchanged
    assert abs(2 * B.chernoff_rate() - 1.9318) < 5e-4
    assert abs(2 * math.exp(-B.HOEFFDING_C) - 1.9326) < 5e-4
    assert 2 * B.chernoff_rate() < 2 * math.exp(-B.HOEFFDING_C)
    # and N_d is far below its own asymptote in the operative range
    assert abs(rows[40]["N_d"] ** (1 / 40) - 1.7586) < 1e-3


def test_the_discarded_factor_is_polynomial_of_order_three_halves() -> None:
    """``N_d/2^d ~ C rho^d d^(-3/2)`` with ``C`` about 11.

    That exponent is the content of the improvement: ``d^(-1/2)`` for staying nonnegative
    under the zero-drift tilt, and a further ``d^(-1)`` because the tilted endpoint sits at
    height ``~sqrt(d)`` rather than at the origin.  The test is that the sequence converges;
    a wrong exponent would make it drift by a power of ``d``.
    """
    c = B.meander_constant((400, 800, 1600))
    assert all(8 < x < 13 for x in c), c
    assert c == sorted(c), c                       # increasing towards its limit
    assert (c[2] - c[1]) < (c[1] - c[0])           # and the increments are shrinking


def test_observed_rate_matches_the_theorem_ledger() -> None:
    """The ledger records this count independently at d = 200; the two agree.

    Row ``J-rate-free-density-one`` states "never-negative word count C_200/2^200 = 3.06e-6
    (empirical rate 0.0635/letter, Hoeffding majorizes at 0.0343)".  Both numbers are the
    polynomial factor at work, not a different exponential rate.
    """
    assert abs(B.non_contracting(200) / 2 ** 200 - 3.06e-6) < 0.01e-6
    assert abs(B.observed_rate(200) - 0.0635) < 5e-5
    for d, want in ((24, 0.1696), (1600, 0.0401)):
        assert abs(B.observed_rate(d) - want) < 5e-4, d
    # monotone decrease towards the asymptote, never below it
    rates = [B.observed_rate(d) for d in (24, 50, 100, 200, 400, 800, 1600)]
    assert rates == sorted(rates, reverse=True)
    assert rates[-1] > -math.log(B.chernoff_rate())


def test_error_term_improvement_is_the_same_factor() -> None:
    """Proposition 7.1's error term carries N_d, not 2^d."""
    for d, factor in ((5, 8.0), (16, 31.0)):
        assert abs(2 ** d / B.non_contracting(d) - factor) < 0.05, d


# --- Proposition 7.4: two arcs on the circle, not three ---


@pytest.mark.parametrize("seed", [0, 1, 2])
def test_off_diagonal_integral_obeys_the_two_arc_bound(seed: int) -> None:
    """``A{x+l} - B{y+l}`` has three pieces on [0,1) but two arcs on the circle.

    The first and last pieces carry the same linear branch -- their constants differ by
    exactly the slope -- so the bound is ``2/(pi|A-B|)``, not ``3/(pi|A-B|)``.
    """
    import numpy as np

    rng = np.random.default_rng(seed)
    n = 200_000
    lam = (np.arange(n) + 0.5) / n
    worst = 0.0
    for _ in range(40):
        a, b = rng.uniform(-500, 500, 2)
        if abs(a - b) < 1:
            continue
        x, y = rng.random(2)
        phase = a * ((x + lam) % 1.0) - b * ((y + lam) % 1.0)
        worst = max(worst, abs(np.exp(2j * np.pi * phase).mean()) * abs(a - b))
    assert worst <= 2 / math.pi + 1e-3, worst


def test_paper_quotes_the_table_this_module_computes() -> None:
    text = io.open(PAPER, encoding="utf-8").read()
    body = text[text.index("**Proposition 7.1"):text.index("Sections 3–5 prove")]
    rows = {r["d"]: r for r in B.table(24)}
    for d in (4, 5, 6, 8, 12, 16, 24):
        row = re.search(r"^\| \\\(%d\\\) \| \\\((\d+)\\\) \| \\\((\d+)\\\)" % d, body, re.MULTILINE)
        assert row, d
        assert int(row.group(1)) == rows[d]["N_d"], d
        assert int(row.group(2)) == rows[d]["endpoint_only"], d


def test_paper_no_longer_states_the_old_constants() -> None:
    text = io.open(PAPER, encoding="utf-8").read()
    assert r"e^{-cd}\,N+2^dE_d(N)" not in text
    assert r"\frac6\pi" not in text
    assert r"most three arcs" not in text
    assert r"Neither loss touches the" not in text


# --- the change has to reach every document that restates the proposition ---


DEPENDENTS = {
    "docs/theory/theorem_ledger.json": "the canonical row",
    "docs/theory/theorem_ledger.md": "rendered from the JSON",
    "docs/theory/juggler_cycle_itinerary_structure_note.md": "imports it as Proposition 6.1",
    "docs/problems/juggler_k3_rate_free.md": "derives the rate-free reduction from it",
    "docs/research/juggler_two_step_parity_lemma.md": "the source note",
}


@pytest.mark.parametrize("rel,role", sorted(DEPENDENTS.items()))
def test_dependents_state_the_exact_count(rel: str, role: str) -> None:
    """Five documents restate Proposition 7.1; the improvement has to reach all of them.

    The old closed form is still true -- Hoeffding remains valid and is kept as the bound on
    ``N_d`` -- so this is staleness, not error.  It is exactly the drift that a grep found once
    and would find again, which is why it is a test.
    """
    text = io.open(ROOT / rel, encoding="utf-8").read()
    assert "N_d" in text, (rel, role)
    for stale in ("2^d E_d(N)", "2^dE_d(N)", r"2^d E_d(N)", r"2^dE_d(N)"):
        assert stale not in text, (rel, stale)


def test_rendered_ledger_is_not_stale() -> None:
    """theorem_ledger.md is generated; the JSON edit has to be re-rendered."""
    import subprocess
    import sys

    r = subprocess.run([sys.executable, str(ROOT / "tools" / "render_theorem_ledger.py"),
                        "--check"], capture_output=True, text=True, cwd=ROOT)
    assert r.returncode == 0, r.stdout + r.stderr


def test_both_ledger_rows_cite_this_regression() -> None:
    import json

    rows = json.load(io.open(ROOT / "docs" / "theory" / "theorem_ledger.json", encoding="utf-8"))
    by_id = {r["id"]: r for r in rows}
    for rid in ("J-equidistribution-implies-density-one", "J-rate-free-density-one"):
        assert any("paper_b_prefix_count" in t for t in by_id[rid]["tests"]), rid


# --- Propositions 7.6 and 7.7: the weakest sufficient hypotheses ---


def test_bias_threshold_is_the_contraction_line_from_the_other_side() -> None:
    """beta_* = 1 - log2/log3: the bias at which a node-wise O-share stops forcing the odd
    count below the contraction line.  The two constants in Proposition 7.7 are one constant."""
    assert abs(B.BIAS_THRESHOLD - 0.369070) < 1e-6
    assert abs(B.BIAS_THRESHOLD + B.BETA - 1.0) < 1e-15


def test_chernoff_rate_is_positive_exactly_above_the_threshold() -> None:
    assert B.biased_chernoff_rate(B.BIAS_THRESHOLD) == 0.0
    assert B.biased_chernoff_rate(0.36) == 0.0
    for bias in (0.37, 0.40, 0.45, 0.50):
        assert B.biased_chernoff_rate(bias) > 0, bias
    rates = [B.biased_chernoff_rate(b) for b in (0.37, 0.40, 0.45, 0.50)]
    assert rates == sorted(rates), rates


def test_biased_dp_reduces_to_the_unbiased_count_at_one_half() -> None:
    """The check that the two accountings are one computation."""
    for d in (5, 10, 20, 30):
        assert abs(B.never_contracting_measure(d, 0.5) - B.non_contracting(d) / 2 ** d) < 1e-12


def test_just_above_the_threshold_the_rate_is_useless_at_any_feasible_depth() -> None:
    """At bias 0.37 the asymptotic rate is 1.85e-6 per letter while the extremal measure
    decays at 0.0841, 0.0274 and 0.0154 at d = 24, 100, 200 -- the finite-depth prefactor
    again, as in the unbiased count's d^(-3/2)."""
    assert abs(B.biased_chernoff_rate(0.37) - 1.85487e-06) < 1e-11
    for d, want in ((24, 0.0841), (100, 0.0274), (200, 0.0154)):
        assert abs(B.observed_biased_rate(d, 0.37) - want) < 5e-5, d
    rates = [B.observed_biased_rate(d, 0.37) for d in (24, 50, 100, 200, 400)]
    assert rates == sorted(rates, reverse=True)
    assert rates[-1] > B.biased_chernoff_rate(0.37)


def test_the_paper_states_both_weakenings_and_the_threshold() -> None:
    text = io.open(PAPER, encoding="utf-8").read()
    assert "**Proposition 7.6 (rate-free reduction).**" in text
    assert "**Proposition 7.7 (biased-split reduction).**" in text
    assert "0.36907" in text
    for figure in ("0.0841", "0.0274", "0.0154", r"1.85\cdot10^{-6}"):
        assert figure in text, figure


def test_section_7_binds_beta_only_as_the_bias() -> None:
    """Proposition 7.1's proof used beta for log2/log3 before 7.7 arrived; importing 7.7
    verbatim would have bound beta twice in one section, which is the collision the section
    was cleaned of.  log2/log3 is now written out and gamma does not appear."""
    text = io.open(PAPER, encoding="utf-8").read()
    sec = text[text.index("## 7. The Terras"):text.index("## 8. Relation")]
    assert r"\gamma" not in sec
    assert r"\beta=\log2/\log3" not in sec
    assert r"d\log2/\log3" in sec


def test_at_the_critical_bias_the_drift_is_exactly_zero() -> None:
    """1 - beta_* = log2/log3, so o_t - t log2/log3 has mean step zero, not merely small."""
    g = B.BETA
    assert B.BIAS_THRESHOLD == 1.0 - g
    assert g * (1 - g) + (1 - g) * (-g) == 0.0


def test_critical_bias_decays_like_d_to_the_minus_half() -> None:
    """Chernoff returns rate 0 at beta_*, but a zero-drift walk still fails to stay
    nonnegative.  The measure times sqrt(d) settles, and each doubling multiplies by 2^(-1/2)."""
    ds = (50, 100, 200, 400, 800, 1600, 3200)
    ms = [B.never_contracting_measure(d, B.BIAS_THRESHOLD) for d in ds]
    scaled = [m * math.sqrt(d) for m, d in zip(ms, ds)]
    assert all(0.66 < s < 0.67 for s in scaled), scaled
    assert abs(scaled[-1] - scaled[-2]) < 1e-4, scaled[-2:]
    for a, b in zip(ms, ms[1:]):
        assert abs(b / a - 2 ** -0.5) < 0.01, (a, b)
    assert B.biased_chernoff_rate(B.BIAS_THRESHOLD) == 0.0    # and Chernoff says nothing


def test_below_the_threshold_the_mass_does_not_vanish() -> None:
    """The hypothesis cannot be weakened: at bias 0.30 the drift is positive and the extremal
    measure keeps the same mass at d = 200 and d = 3200."""
    a = B.never_contracting_measure(200, 0.30)
    b = B.never_contracting_measure(3200, 0.30)
    assert a > 0.2 and abs(a - b) < 1e-3, (a, b)


def test_paper_states_the_non_strict_threshold_and_the_constants() -> None:
    text = io.open(PAPER, encoding="utf-8").read()
    sec = text[text.index("## 7. The Terras"):text.index("## 8. Relation")]
    assert r"\beta\ \ge\ \beta_*" in sec          # not the strict inequality
    assert r"2^{-1/2}" in sec and "0.6675" in sec
    assert "The threshold cannot be lowered" in sec
    assert "0.228" in sec


# --- 7.1 and 7.6 ask only for what their proofs consume ---


def test_proposition_7_1_hypothesis_is_one_sided() -> None:
    """The two-sided form was never used: the proof bounds each surviving class from above."""
    text = io.open(PAPER, encoding="utf-8").read()
    body = text[text.index("**Proposition 7.1"):text.index("The name of the proposition")]
    assert r"\#\{n\le N:\mathrm{word}_d(n)=w\}\ \le\ 2^{-d}N+E_d(N)" in body
    assert r"\bigl|\#\{n\le N:\mathrm{word}_d(n)=w\}-2^{-d}N\bigr|\le E_d(N)" not in body
    assert "each of *those* words" in body


def test_proposition_7_6_hypothesis_is_one_sided() -> None:
    text = io.open(PAPER, encoding="utf-8").read()
    body = text[text.index("**Proposition 7.6"):text.index("**Proposition 7.7")]
    assert r"\le\ 2^{-d}" in body
    assert "an upper bound only" in body
    assert r"\#w(N)=2^{-d}N+o(N)" not in body


@pytest.mark.parametrize("d,o_rooted,surviving", [
    (5, 16, 4), (8, 128, 19), (16, 32768, 2114), (24, 8388608, 286581),
])
def test_the_remark_quantifies_what_is_not_used(d: int, o_rooted: int, surviving: int) -> None:
    """The proof needs N_d classes, not the 2^(d-1) an equidistribution statement covers."""
    assert 2 ** (d - 1) == o_rooted
    assert B.non_contracting(d) == surviving
    text = io.open(PAPER, encoding="utf-8").read()
    remark = text[text.index("The name of the proposition"):text.index("The exact count is worth")]
    assert str(surviving) in remark, surviving
    assert str(o_rooted) in remark, o_rooted


def test_the_remark_names_the_four_depth_five_words() -> None:
    text = io.open(PAPER, encoding="utf-8").read()
    remark = text[text.index("The name of the proposition"):text.index("The exact count is worth")]
    for w in surviving_words(5):
        assert w in remark, w


def test_only_two_standing_conditions_are_hypotheses() -> None:
    """(C3) and (C4) cap k, h_1, h_2 each at P^(1/24); (C1) and (C2) follow.

    (C1) is exactly the product of the three caps, tight at k = h_1 = h_2 = P^(1/24).
    (C2) needs only P >= 3^(12/5) = 14.  So an invocation verifies two inequalities, not four,
    and the lemma statements say so.
    """
    from fractions import Fraction as F

    cap = F(1, 24)
    assert cap * 3 == F(1, 8)                      # (C1), with equality
    assert cap * 2 == F(1, 12) and F(1, 12) < F(1, 2)
    assert abs(3 ** (12 / 5) - 14.0) < 0.1         # where (C2) starts to hold

    text = io.open(PAPER, encoding="utf-8").read()
    assert "Assume (C3) and (C4), write" in text          # Lemma 5.2
    assert r"Assume (C3) and (C4), \(j=0\)" in text       # Lemma 5.2b
    assert "(C1)\u2013(C4)" not in text and "(C1)--(C4)" not in text
    assert "checking two inequalities, not four" in text


def test_c2_is_recorded_as_never_invoked() -> None:
    """Its only other occurrence was its own definition; the paper now says so rather than
    leaving a reader to check twenty proofs for a use that is not there."""
    text = io.open(PAPER, encoding="utf-8").read()
    assert "invoked nowhere below" in text
    # the real invariant is not a count but that no proof cites it, unlike (C1), (C3), (C4)
    assert "by (C2)" not in text
    for cited in ("by (C1)", "by (C3)", "by (C4)"):
        assert cited in text, cited


def test_decoration_budget_is_a_ceiling_not_a_count() -> None:
    """Claim E forms five terms; Step 4's leftovers add two; the class allows nine.

    The number is never used quantitatively -- it appears only in the class definition and in
    the sentence that records the true maximum -- so the ceiling is documentation, not an
    estimate anything depends on.
    """
    text = io.open(PAPER, encoding="utf-8").read()
    assert "at most nine terms" in text                 # the class definition
    assert "seven is the largest decoration this paper forms" in text
    assert "not a count that is" in text
    # the number is documentation: it occurs as the ceiling and as the note, nowhere else
    # (the third "nine" in the paper is "nine orders of magnitude", a different subject)
    assert text.count("budget of nine") == 1
    assert text.count("at most nine terms") == 1


def test_decoration_parameters_are_all_consumed() -> None:
    """The audit's negative results, pinned so a later edit cannot quietly loosen them.

    (D1)'s three parameters are each set by Claim E: q' = q_d sigma, h' = |d-e_1|/2, and
    d' = min(d,e_1).  The bound h' <= 2P^(1/24) is tight, since d and e_1 range over
    {0, d_1, d_2, d_1+d_2} and the largest gap is d_1+d_2 = 2(h_1+h_2).  (D3) carries a third
    derivative it does not use in Stage 6, and the paper says why: closure under one more
    difference.
    """
    text = io.open(PAPER, encoding="utf-8").read()
    assert r"h'=|d-e_1|/2\le2P^{1/24}" in text
    assert r"d'=\min(d,e_1)\in\mathcal D" in text
    assert "Only the second-derivative budget is used" in text
    assert "closed under one" in text


# --- Proposition 7.1b: the depth ceiling ------------------------------------


def test_ceiling_is_one_minus_the_surviving_share() -> None:
    for d in range(1, 13):
        assert B.ceiling(d) == Fraction(2 ** d - B.non_contracting(d), 2 ** d)


@pytest.mark.parametrize("d,value", [(4, "13/16"), (5, "7/8"), (6, "7/8"), (7, "115/128")])
def test_the_ceilings_the_paper_quotes(d: int, value: str) -> None:
    assert str(B.ceiling(d)) == value


def test_corollaries_49_and_64_sit_exactly_at_the_ceiling() -> None:
    """If either were below it, the paper would be leaving a certified class on the table."""
    assert B.ceiling(4) == Fraction(13, 16)
    assert B.ceiling(5) == Fraction(7, 8)


def test_depth_five_lower_bounds_come_from_63_and_the_OOOO_sum() -> None:
    """Proposition 7.1b(ii): 1/32 + 1/32 for OOEOO, OOOEO, and 1/16 for the OOOO pair."""
    assert Fraction(1, 32) + Fraction(1, 32) + Fraction(1, 16) == 1 - B.ceiling(5)


def test_the_weyl_criterion_matches_the_exact_count() -> None:
    """stalls(d) is a statement about frac((d-1)log2/log3); it must agree with the DP."""
    assert all(B.stalls(d) == (not B.ceiling_improves(d)) for d in range(2, 241))


def test_stalling_depths_have_density_beta_star() -> None:
    assert B.stalling_depths(30)[:11] == [3, 6, 9, 11, 14, 17, 19, 22, 25, 28, 30]
    # far out, use the criterion itself -- the exact DP is quadratic in big integers
    n = sum(1 for d in range(2, 200002) if B.stalls(d))
    assert abs(n / 200000 - B.BIAS_THRESHOLD) < 1e-4, n / 200000


def test_stalling_is_not_eventually_periodic_over_the_computed_range() -> None:
    """A rational theta would make it periodic; log2/log3 is not, and the run pattern shows it."""
    s = [d for d in range(2, 4001) if B.stalls(d)]
    gaps = sorted(set(b - a for a, b in zip(s, s[1:])))
    assert gaps == [2, 3], gaps          # a Sturmian two-gap sequence, never one gap


def test_depth_seven_is_worth_three_over_one_twenty_eight() -> None:
    assert B.ceiling(7) - B.ceiling(6) == Fraction(3, 128)


def test_depth_seven_needs_three_different_depth_five_survivors() -> None:
    """The claim that the OOOO* split alone does not unlock depth seven."""
    def surv(d: int) -> list[str]:
        out = []
        for bits in range(2 ** d):
            w = "".join("O" if bits >> (d - 1 - i) & 1 else "E" for i in range(d))
            o = 0
            if all(B.survives(t, (o := o + (c == "O"))) for t, c in enumerate(w, 1)):
                out.append(w)
        return out

    died = [w + "E" for w in surv(6) if w + "E" not in surv(7)]
    assert died == ["OOEOOEE", "OOOEOEE", "OOOOEEE"], died
    assert sorted({w[:5] for w in died}) == ["OOEOO", "OOOEO", "OOOOE"]


# --- Proposition 7.1b(iv): the lean survivors carry every gain ---------------


def test_every_gain_is_exactly_the_lean_survivors() -> None:
    """(iv): the removed words are the length-(d-1) survivors of least odd count."""
    for d in range(2, 15):
        die = B.dying_words(d)
        assert B.ceiling(d) - B.ceiling(d - 1) == Fraction(len(die), 2 ** d), d
        if die:
            assert len(die) == B.lean_count(d - 1), d
            least = min(w.count("O") for w in B.surviving_words(d - 1))
            assert {w.count("O") for w in die} == {least}, d


def test_dying_words_are_empty_exactly_at_a_stalling_depth() -> None:
    for d in range(2, 15):
        assert (B.dying_words(d) == []) == B.stalls(d), d


def test_the_lean_counts_the_paper_prints() -> None:
    assert [B.lean_count(t) for t in range(1, 11)] == [1, 1, 1, 2, 3, 3, 7, 12, 12, 30]


def test_longest_odd_run_places_the_known_kernels() -> None:
    """OOOO* is the level-3 kernel of Conjecture 7.3; Theorem 6.1 reaches run three."""
    assert B.longest_odd_run("OOOO") == 4
    assert B.longest_odd_run("OOOEE") == 3
    assert B.longest_odd_run("OOEOE") == 2
    assert B.longest_odd_run("OOEOOE") == 2


@pytest.mark.parametrize("d,expected", [
    (4, {2: "1/16"}),
    (5, {2: "1/32", 3: "1/32"}),
    (7, {2: "1/128", 3: "1/128", 4: "1/128"}),
    (8, {2: "1/256", 3: "3/256", 4: "1/128", 5: "1/256"}),
    (10, {2: "1/1024", 3: "1/256", 4: "1/256", 5: "1/512", 6: "1/1024"}),
])
def test_the_run_decomposition_table(d: int, expected: dict[int, str]) -> None:
    from collections import Counter
    c = Counter(B.longest_odd_run(w) for w in B.dying_words(d))
    assert {r: str(Fraction(n, 2 ** d)) for r, n in c.items()} == expected, d


def test_two_thirds_of_depth_seven_needs_no_new_kernel_level() -> None:
    """The claim that 7/8 -> 57/64 is available with Conjecture 7.3 still open."""
    cheap = [w for w in B.dying_words(7) if B.longest_odd_run(w) <= 3]
    assert len(cheap) == 2 and sorted(cheap) == ["OOEOOE", "OOOEOE"]
    assert Fraction(7, 8) + Fraction(len(cheap), 128) == Fraction(57, 64)
    assert B.ceiling(7) - (Fraction(7, 8) + Fraction(len(cheap), 128)) == Fraction(1, 128)


def test_paper_states_part_iv_and_the_run_table() -> None:
    text = io.open(PAPER, encoding="utf-8").read()
    assert "(iv) *(what carries a gain)*" in text
    assert r"\frac{L_{d-1}}{2^{d}}" in text
    assert "the level-3 kernel of Conjecture 7.3" in text
    assert r"carry the certified density to \(57/64\)" in text


# --- the theta-coefficient criterion behind the run statistic ----------------


def test_iterate_exponents_match_the_scales_the_paper_names() -> None:
    assert B.iterate_exponents("OO")[-1] == Fraction(9, 4)          # the level-2 wave
    assert B.iterate_exponents("OOOE")[-1] == Fraction(27, 16)      # OOOE* fifth-letter phase
    assert B.phase_exponents("OOEOO") == [Fraction(3, 2), Fraction(9, 4),
                                          Fraction(9, 8), Fraction(27, 16)]


def test_the_coefficient_rule_reproduces_the_papers_own_constants() -> None:
    """gamma_s = e_{t-1} - e_s against four constants displayed in Theorem 6.3 and Section 3.4."""
    # OOEO*, letter 5: C = (9k/16) n^{3/16}, remainder P^{-9/16}, B = (3k/4)v^{1/4} ~ k n^{9/16}
    assert B.theta_coefficients("OOEO", 5) == [Fraction(3, 16), Fraction(-9, 16), Fraction(9, 16)]
    # OOOE*, letter 5: the same C, the same discarded remainder
    assert B.theta_coefficients("OOOE", 5)[:2] == [Fraction(3, 16), Fraction(-9, 16)]
    # OOO*, letter 4: W ~ k n^{9/8}, the coefficient with no drift-1 interval
    assert B.theta_coefficients("OOO", 4) == [Fraction(15, 8), Fraction(9, 8)]


@pytest.mark.parametrize("word,letter,alpha,blocked", [
    ("OOEO", 5, "27/16", []),
    ("OOEOO", 5, "27/16", []),
    ("OOO", 4, "27/8", ["15/8", "9/8"]),
    ("OOOO", 5, "81/16", ["57/16", "45/16", "27/16"]),
    ("OOEOOEE", 6, "81/32", ["33/32", "45/32"]),
    ("OOOEOEE", 6, "81/32", ["33/32"]),
    ("OOOOEEE", 5, "81/16", ["57/16", "45/16", "27/16"]),
])
def test_the_drift_threshold_table(word: str, letter: int, alpha: str,
                                   blocked: list[str]) -> None:
    assert str(B.iterate_exponents(word)[letter - 2]) == alpha, word
    assert [str(g) for g in B.drift_blocked(word, letter)] == blocked, word


def test_OOOOEEE_is_the_open_split_coefficient_for_coefficient() -> None:
    """Conjecture 7.3 is necessary for that third of depth seven, not merely sufficient."""
    assert B.theta_coefficients("OOOOEEE", 5) == B.theta_coefficients("OOOO", 5)


def test_the_two_pursuable_thirds_sit_inside_theorem_61s_profile() -> None:
    """Fewer or smaller blocked coefficients than the split Theorem 6.1 already closes."""
    benchmark = B.drift_blocked("OOO", 4)                 # Thm 6.1: two, largest 15/8
    for word in ("OOEOOEE", "OOOEOEE"):
        got = B.drift_blocked(word, 6)
        assert len(got) <= len(benchmark), word
        assert max(got) < max(benchmark), word
    assert len(B.drift_blocked("OOOOEEE", 5)) > len(benchmark)


def test_theorem_53s_species_is_the_three_halves_defect() -> None:
    """Every blocked coefficient of the proved and the open split rides a 3/2-power defect."""
    for word, letter in (("OOO", 4), ("OOOO", 5), ("OOOOEEE", 5)):
        assert {sp for _, _, sp in B.blocked_profile(word, letter)} == {"3/2"}, word
    # theta_w = {v^{1/2}} of Theorem 6.3 is the square-root species, at s = 3 of OOEO*
    assert B.defect_species("OOEOO", 3) == "sqrt"
    assert B.defect_species("OOEOO", 1) == "3/2"


def test_the_ranking_flips_against_the_run_statistic() -> None:
    """Run put OOEOOEE first; species and count both put OOOEOEE first."""
    assert B.longest_odd_run("OOEOOEE") < B.longest_odd_run("OOOEOEE")   # what run said
    cheap, dear = B.blocked_profile("OOOEOEE", 6), B.blocked_profile("OOEOOEE", 6)
    assert len(cheap) == 1 and cheap[0][1:] == (Fraction(33, 32), "3/2")
    assert len(dear) == 2
    assert ("sqrt" in {sp for _, _, sp in dear}) and ("sqrt" not in {sp for _, _, sp in cheap})
    # and the single in-species one sits below both the pair Theorem 5.3 closes
    assert cheap[0][1] < min(B.drift_blocked("OOO", 4))


def test_the_paper_states_the_flip_and_the_single_monomial_caveat() -> None:
    text = io.open(PAPER, encoding="utf-8").read()
    assert "it is the harder of" in text
    assert "None of this makes any of the three a corollary." in text
    assert "showing they" in text and "do not vanish" in text
    assert "no theorem and no conjecture" in text


def test_the_extra_cost_is_recorded_rather_than_hidden() -> None:
    """Six waves against four is the honest price, and the paper says so."""
    assert B.wave_count("OOEOOEE") == 6 and B.wave_count("OOOEE") == 4
    text = io.open(PAPER, encoding="utf-8").read()
    assert "None of this makes any of the three a corollary." in text
    assert "six waves where the" in text
    assert "the *difference* of the" in text


# --- the coefficient rule with its constants, and the deepest blocked defect ---


def test_the_rule_returns_the_papers_named_constants_exactly() -> None:
    """Constant and exponent together, against three monomials the paper writes out."""
    assert B.defect_coefficient("OOO", 4, 2) == (Fraction(3, 4), Fraction(9, 8))
    assert B.defect_coefficient("OOEO", 5, 1) == (Fraction(9, 16), Fraction(3, 16))
    assert B.defect_coefficient("OOEO", 5, 3) == (Fraction(3, 4), Fraction(9, 16))


def test_the_rule_predicts_conjecture_73s_two_stated_scales() -> None:
    """Conjecture 7.3 quotes a weight derivative kP^{11/16} and a traded family kn^{45/16}."""
    const, exponent = B.defect_coefficient("OOOO", 5, 3)
    assert (const, exponent) == (Fraction(3, 4), Fraction(27, 16))
    assert exponent - 1 == Fraction(11, 16)                 # varrho' ~ k P^{11/16}
    assert B.defect_coefficient("OOOO", 5, 2) == (Fraction(9, 8), Fraction(45, 16))


def test_deepest_blocked_reproduces_the_papers_own_kernel_naming() -> None:
    """No kernel for OOEO*; the level-2 kernel for OOO*; the level-3 kernel for OOOO*."""
    assert B.deepest_blocked("OOEO", 5) is None
    assert B.deepest_blocked("OOO", 4) == (2, Fraction(3, 4), Fraction(9, 8), "3/2")
    assert B.deepest_blocked("OOOO", 5) == (3, Fraction(3, 4), Fraction(27, 16), "3/2")


def test_the_stop_threshold_is_the_one_conjecture_73_names() -> None:
    """9/4 is where every method of the paper stops; kn^{45/16} is what crosses it."""
    assert B.STOP_THRESHOLD == Fraction(9, 4)
    assert Fraction(45, 16) > B.STOP_THRESHOLD
    assert [str(c) for c in B.beyond_methods("OOOO", 5)] == ["57/16", "45/16"]
    for word, letter in (("OOEO", 5), ("OOO", 4), ("OOOEOEE", 6), ("OOEOOEE", 6)):
        assert B.beyond_methods(word, letter) == [], word


def test_the_depth_seven_verdicts() -> None:
    """OOOEOEE below Theorem 5.3's level; OOEOOEE at level 3 on a square root; OOOOEEE open."""
    assert B.deepest_blocked("OOOEOEE", 6) == (1, Fraction(27, 32), Fraction(33, 32), "3/2")
    assert B.deepest_blocked("OOEOOEE", 6) == (3, Fraction(9, 8), Fraction(45, 32), "sqrt")
    assert B.deepest_blocked("OOOOEEE", 5) == B.deepest_blocked("OOOO", 5)
    # the pursuable pair share the identical level-1 monomial, so that work is not doubled
    assert B.defect_coefficient("OOOEOEE", 6, 1) == B.defect_coefficient("OOEOOEE", 6, 1)


def test_paper_carries_the_deepest_blocked_table() -> None:
    text = io.open(PAPER, encoding="utf-8").read()
    for frag in (r"\tfrac{27k}{32}n^{33/32}", r"\tfrac{3k}4n^{27/16}", r"\tfrac{9k}8n^{45/32}",
                 r"\varrho'\asymp kP^{11/16}", "where every method of this paper stops",
                 "one level *below*"):
        assert frag in text, frag


# --- the form of the kernel weight, and the level-1 case ---


def test_theorem_53s_weight_really_is_a_monomial() -> None:
    """Its statement fixes c(n) = (3k/4)n^{9/8}; that is legitimate only if -3/8 < 0."""
    assert B.coefficient_sensitivity("OOO", 4) == [(1, Fraction(-3, 8))]
    assert B.coefficient_is_monomial("OOO", 4)


def test_the_level_three_weight_is_not_a_monomial() -> None:
    """A structural gap between the levels beyond the derivative count."""
    assert B.coefficient_sensitivity("OOOO", 5) == [(1, Fraction(3, 16)), (2, Fraction(-9, 16))]
    assert not B.coefficient_is_monomial("OOOO", 5)
    assert not B.coefficient_is_monomial("OOOOEEE", 5)          # the same split


def test_OOEOOEE_is_a_tidier_level_three_than_conjecture_73() -> None:
    """Same level, clean weight -- but the wrong species, which is what blocks it."""
    assert B.coefficient_sensitivity("OOEOOEE", 6) == [(1, Fraction(-3, 32)),
                                                       (2, Fraction(-27, 32))]
    assert B.coefficient_is_monomial("OOEOOEE", 6)
    assert B.deepest_blocked("OOEOOEE", 6)[3] == "sqrt"
    assert B.deepest_blocked("OOOO", 5)[3] == "3/2"


def test_OOOEOEE_has_no_inner_floor_to_keep_exact() -> None:
    """Level 1: the kernel's argument is n^{3/2}, still a smooth function of n."""
    assert B.coefficient_sensitivity("OOOEOEE", 6) == []
    assert B.deepest_blocked("OOOEOEE", 6)[0] == 1
    assert B.coefficient_is_monomial("OOOEOEE", 6)


def test_paper_states_the_level_one_reading_and_its_limit() -> None:
    text = io.open(PAPER, encoding="utf-8").read()
    assert r"\tfrac{27k}{32}n^{33/32}\{n^{3/2}\}" in text
    assert "not a smooth function" in text
    assert "Theorem 4.7 does not cover this sum" in text
    assert "still a kernel and this paper does not contain" in text
    # and the corrected justification for ignoring the shallower defects
    assert "not resolved elsewhere and not expanded either" in text


# --- Step 1's accounting is exponent-blind ---


def test_the_chain_returns_theorem_53s_own_parameters() -> None:
    """delta = 1/24 must give H_1 = P^{1/48}, H_2 = P^{1/24} and P^{1-1/96}."""
    r = B.differencing_chain(Fraction(1, 24))
    assert r["H1"] == Fraction(1, 48)
    assert r["H2"] == Fraction(1, 24)
    assert r["exponent"] == 1 - Fraction(1, 96)
    assert r["saving"] == Fraction(1, 96)


def test_each_differencing_halves_the_saving() -> None:
    """The paper's 1/96 = (1/4)(1/24): two differencings, two halvings."""
    d = Fraction(1, 24)
    assert B.differencing_chain(d, 1)["saving"] == d / 2
    assert B.differencing_chain(d, 2)["saving"] == d / 4
    assert B.differencing_chain(d, 3)["saving"] == d / 8


def test_the_second_range_is_the_square_of_the_first() -> None:
    for d in (Fraction(1, 24), Fraction(1, 12), Fraction(5, 48)):
        r = B.differencing_chain(d)
        assert r["H2"] == 2 * r["H1"], d          # exponents: H_2 = H_1^2


def test_any_power_saving_survives_the_chain() -> None:
    """No positive saving is lost entirely, and a trivial input gives a trivial output."""
    assert B.differencing_chain(Fraction(0))["exponent"] == 1
    for d in (Fraction(1, 1000), Fraction(1, 24), Fraction(1, 2)):
        assert B.differencing_chain(d)["exponent"] < 1, d


def test_paper_states_the_chain_and_its_consequence() -> None:
    text = io.open(PAPER, encoding="utf-8").read()
    assert "What the two differencings cost." in text
    assert r"H_2=H_1^2" in text
    assert "never sees the weight's exponent" in text
    assert "where it costs nothing" in text


# --- the branch-run criterion, the third threshold ---


def test_branch_runs_reproduce_lemma_51s_own_length() -> None:
    """Level 2 takes its branches from X = n^{3/2}: runs of length P^{1/2}/h."""
    assert B.branch_run_exponent(Fraction(3, 2)) == Fraction(1, 2)
    assert B.has_branch_runs(Fraction(3, 2))


def test_the_level_three_base_has_no_runs() -> None:
    """v sits at 9/4 and jumps by n^{5/4} per step, so the floor is never constant."""
    assert Fraction(9, 4) - 1 == Fraction(5, 4)              # the paper's stated jump
    assert B.branch_run_exponent(Fraction(9, 4)) == Fraction(-1, 4)
    assert not B.has_branch_runs(Fraction(9, 4))


def test_the_threshold_is_two_and_separates_the_known_cases() -> None:
    """e < 2 is what divides Theorem 5.3 from Conjecture 7.3."""
    assert B.has_branch_runs(B.iterate_exponents("O")[0])            # e_1 = 3/2, level 2
    assert not B.has_branch_runs(B.iterate_exponents("OO")[1])       # e_2 = 9/4, level 3
    assert B.branch_run_exponent(2) == 0


def test_level_one_branches_on_nothing() -> None:
    """The base is n, Delta_1 n = d_1 is constant, and the runs fill the block."""
    assert B.branch_run_exponent(Fraction(1)) == 1
    assert B.has_branch_runs(Fraction(1))


def test_paper_states_the_branch_criterion() -> None:
    text = io.open(PAPER, encoding="utf-8").read()
    assert "Where the branch decomposition comes from." in text
    assert r"\asymp P^{2-e}/h" in text
    assert "a third threshold" in text
    assert "level-1 form and it is degenerate" in text


# --- the three thresholds together ---


def test_branch_base_is_the_object_the_kernel_would_branch_on() -> None:
    assert B.branch_base("OOO", 4) == Fraction(3, 2)          # X = n^{3/2}
    assert B.branch_base("OOOO", 5) == Fraction(9, 4)         # v
    assert B.branch_base("OOOEOEE", 6) == Fraction(1)         # n itself
    assert B.branch_base("OOEO", 5) is None                   # unblocked


def test_OOEOOEE_inherits_conjecture_73s_branching_failure() -> None:
    """Same base object v, same n^{5/4} jump -- not merely an analogous difficulty."""
    assert B.branch_base("OOEOOEE", 6) == B.branch_base("OOOO", 5) == Fraction(9, 4)
    assert not B.obstruction_profile("OOEOOEE", 6)["branch_runs"]
    assert not B.obstruction_profile("OOOO", 5)["branch_runs"]
    # but unlike Conjecture 7.3 it carries nothing above the stop threshold
    assert B.obstruction_profile("OOEOOEE", 6)["beyond"] == []
    assert B.obstruction_profile("OOOO", 5)["beyond"] != []


def test_OOOEOEE_is_the_only_target_that_branches() -> None:
    assert B.obstruction_profile("OOOEOEE", 6)["branch_runs"]
    for word, letter in (("OOEOOEE", 6), ("OOOOEEE", 5)):
        assert not B.obstruction_profile(word, letter)["branch_runs"], word


def test_the_branch_and_stop_conditions_are_independent() -> None:
    """All four combinations occur, so neither threshold implies the other."""
    from itertools import product
    seen = set()
    for d in range(3, 9):
        for bits in product("EO", repeat=d):
            w = "".join(bits)
            if not w.startswith("O"):
                continue
            for t in range(3, d + 1):
                p = B.obstruction_profile(w, t)
                if p["branch_runs"] is None:
                    continue
                seen.add((p["branch_runs"], bool(p["beyond"])))
    assert seen == {(True, False), (True, True), (False, False), (False, True)}


def test_paper_states_the_independence_and_the_revised_gain() -> None:
    text = io.open(PAPER, encoding="utf-8").read()
    assert "genuinely independent" in text
    assert "inherits, verbatim, the branching failure" in text
    assert r"7/8\to113/128" in text
    assert "cuts" in text and "back to the first of the two" in text


# --- the coefficient rule against real orbits, at the depth it is used ---


def _iterates(n: int, d: int):
    """Actual Juggler iterates and the word n realises, at working precision."""
    from mpmath import mpf, floor, power
    it, w = [n], ""
    for _ in range(d):
        c = it[-1]
        w += "O" if c % 2 else "E"
        it.append(int(floor(power(mpf(c), mpf(3) / 2 if c % 2 else mpf(1) / 2))))
    return w, it


def _measured_coefficient(n: int, d: int, s: int):
    """d(J^d)/d(theta_s) along the real orbit: prod p_q (J^{q-1})^{p_q - 1}."""
    from mpmath import mpf, power
    w, it = _iterates(n, d)
    p = [mpf(3) / 2 if ch == "O" else mpf(1) / 2 for ch in w]
    out, v = mpf(1), mpf(it[s])
    for q in range(s + 1, d + 1):
        out *= p[q - 1] * power(v, p[q - 1] - 1)
        v = power(v, p[q - 1])
    return w, out


WITNESSES = [("OOEOOE", 1000057), ("OOOEEO", 1000091),
             ("OOOEOO", 1000069), ("OOOOOO", 1000053)]


@pytest.mark.parametrize("word,n", WITNESSES)
@pytest.mark.parametrize("s", [1, 2, 3, 4])
def test_coefficient_rule_holds_on_real_orbits_at_depth_six(word: str, n: int, s: int) -> None:
    """Constant and exponent together, at letter 7 -- where the paper prints nothing.

    Everything the frontier discussion says about depth seven rests on this formula, and until
    now it was checked only against constants the paper displays, all at depth at most five.
    """
    from mpmath import mp, mpf, power
    mp.dps = 100
    got_word, measured = _measured_coefficient(n, 6, s)
    assert got_word == word, (n, got_word)
    const, exponent = B.defect_coefficient(word, 7, s)
    predicted = (2 * mpf(const.numerator) / const.denominator
                 * power(mpf(n), mpf(exponent.numerator) / exponent.denominator))
    assert abs(measured / predicted - 1) < 1e-6, (word, s, float(measured / predicted))


def test_the_square_root_defect_that_blocks_OOEOOEE_is_measured() -> None:
    """theta_3 of OOEOOE at letter 6 is the (9k/8) n^{45/32} coefficient of the ranking."""
    from mpmath import mp
    mp.dps = 100
    const, exponent = B.defect_coefficient("OOEOOE", 6, 3)
    assert (const, exponent) == (Fraction(9, 8), Fraction(45, 32))
    assert B.defect_species("OOEOOE", 3) == "sqrt"
    word, measured = _measured_coefficient(1000057, 5, 3)
    assert word == "OOEOO"
    assert measured > 0


# --- linearisation: the composed map must be sub-quadratic ---


def test_every_kernel_the_paper_forms_is_one_step_from_defect_to_wave() -> None:
    """E = 3/2 for Theorem 5.3 and for Conjecture 7.3 -- the Lemma 5.1(i) shape."""
    for word, letter in (("OOO", 4), ("OOOO", 5), ("OOOOEEE", 5)):
        s = B.deepest_blocked(word, letter)[0]
        assert B.composed_map(word, letter, s) == Fraction(3, 2), word
        assert B.linearisation_safe(word, letter), word


def test_OOOEOEE_is_sub_quadratic_and_OOEOOEE_is_not() -> None:
    assert B.composed_map("OOOEOEE", 6, 1) == Fraction(27, 16)
    assert B.composed_map("OOEOOEE", 6, 3) == Fraction(9, 4)
    assert B.linearisation_safe("OOOEOEE", 6)
    assert not B.linearisation_safe("OOEOOEE", 6)
    assert B.second_order_exponent("OOEOOEE", 6, 3) == Fraction(9, 32)
    assert B.second_order_exponent("OOOEOEE", 6, 1) == Fraction(-15, 32)


def test_E_is_the_ratio_of_scale_exponents() -> None:
    for word, letter in (("OOO", 4), ("OOOO", 5), ("OOEOOEE", 6), ("OOOEOEE", 6)):
        e = B.iterate_exponents(word)
        for s in range(1, letter - 1):
            assert B.composed_map(word, letter, s) == e[letter - 2] / e[s - 1], (word, s)


def test_a_positive_second_order_at_an_unexpanded_defect_is_harmless() -> None:
    """OOO* and OOOO* both have one at s = 1, and both are proved or conjectured anyway."""
    assert B.second_order_exponent("OOO", 4, 1) > 0
    assert B.second_order_exponent("OOOO", 5, 1) > 0
    assert B.deepest_blocked("OOO", 4)[0] == 2 and B.deepest_blocked("OOOO", 5)[0] == 3
    assert B.linearisation_safe("OOO", 4) and B.linearisation_safe("OOOO", 5)


def test_the_squared_term_is_measured_on_an_orbit() -> None:
    """n = 1000057 realises OOEOO; its squared theta_3 term is ~50, not a correction."""
    from mpmath import mp, mpf, power
    mp.dps = 120
    word, it = _iterates(1000057, 5)
    assert word == "OOEOO"
    p = [mpf(3) / 2 if c == "O" else mpf(1) / 2 for c in word]
    E = p[3] * p[4]                                   # J^3 -> J^5, letter 6's wave
    assert abs(float(E) - 2.25) < 1e-12
    x = mpf(it[3])
    theta = power(mpf(it[2]), p[2]) - x
    resid = power(x + theta, E) - power(x, E) - E * power(x, E - 1) * theta
    pred = E * (E - 1) / 2 * power(x, E - 2) * theta ** 2
    assert abs(float(resid / pred) - 1) < 1e-6
    assert 40 < float(pred) < 60, float(pred)          # ~50, i.e. not negligible


def test_paper_states_the_linearisation_criterion() -> None:
    text = io.open(PAPER, encoding="utf-8").read()
    assert "not a linear object at all" in text
    assert r"E=\tfrac94" in text and r"E=\tfrac{27}{16}" in text
    assert "49.9" in text
    assert "keeps *exact* are\nharmless" in text or "keeps *exact*" in text
