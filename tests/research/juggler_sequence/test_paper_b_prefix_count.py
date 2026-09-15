# Historical Paper B audit: the 2026-09-04 snapshot is not the conditional publication.
"""The exact non-contracting count of Proposition 7.1, and Proposition 7.4's arc count.

Proposition 7.1 bounded the number of length-d words with no contracting prefix by Hoeffding
applied to the endpoint.  Two things were given away: the prefix constraint itself, and the
local-limit factor.  The count is a dynamic program over ``(t, o_t)``, so the exact number is
available; these tests check it against the paper's own figures and against the closed form it
replaces.
"""

from __future__ import annotations

import io
import itertools
import math
import re
from fractions import Fraction
from pathlib import Path

import pytest

BETA_ = math.log(2.0) / math.log(3.0)

from research.juggler_sequence import paper_b_prefix_count as B

ROOT = Path(__file__).resolve().parents[3]
PAPER = ROOT / "docs" / "theory" / "juggler_parity_discrepancy_note_2026_09_04.md"


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


def _all_words(lo: int, hi: int) -> list[str]:
    return ["".join(c) for d in range(lo, hi + 1)
            for c in itertools.product("OE", repeat=d)]


def test_the_composed_map_is_the_exponent_ratio() -> None:
    """``E = prod_{q=s+1}^{t-1} p_q`` is ``e_{t-1} / e_s``, identically.

    The chain rule for the coefficient of ``theta_s`` in letter ``t``'s phase is
    ``(k/2) E`` at exponent ``e_{t-1} - e_s``, so the whole rule rests on the
    product of intermediate step exponents being the ratio of iterate exponents.
    That is what makes it a rule rather than a table: it is checked here on every
    word of length 3..10 and every pair ``s < t``, not at the five points the
    paper prints.
    """
    checked = 0
    for w in _all_words(3, 10):
        e = B.iterate_exponents(w)
        for t_ in range(2, len(w) + 1):
            for s in range(1, t_):
                assert B.composed_map(w, t_, s) == e[t_ - 2] / e[s - 1], (w, t_, s)
                checked += 1
    assert checked == 75_768, checked


def test_the_second_order_exponent_is_e_s_times_E_minus_two() -> None:
    """``e_{t-1} - 2 e_s = e_s (E - 2)``, so it is negative exactly when ``E < 2``.

    This is the ``E < 2`` linearisation criterion as an identity.  ``e_s > 0``
    always, so the sign of the squared-defect exponent is the sign of ``E - 2``
    and nothing else -- the criterion is not a threshold chosen to fit the words,
    it is where the second-order term stops growing.
    """
    disagreements = []
    for w in _all_words(3, 10):
        e = B.iterate_exponents(w)
        for t_ in range(2, len(w) + 1):
            for s in range(1, t_):
                soe = B.second_order_exponent(w, t_, s)
                E = B.composed_map(w, t_, s)
                assert soe == e[s - 1] * (E - 2), (w, t_, s, soe, E)
                if (soe < 0) != (E < 2):
                    disagreements.append((w, t_, s))
    assert not disagreements, disagreements[:5]


def _walk(w: str) -> list[float]:
    """``u_t = o_t log2(3) - t``, the exponent walk of the Paper C collision work."""
    u, o = [0.0], 0
    for i, c in enumerate(w, start=1):
        if c == "O":
            o += 1
        u.append(o * math.log2(3.0) - i)
    return u


def test_the_composed_map_is_two_to_the_walk_climb() -> None:
    """``E = 2^(u_(t-1) - u_s)``, so ``E < 2`` is "the walk climbs less than one unit".

    Paper B's screen and the Paper C collision work were built separately, and this
    is the coordinate they share: the exponent walk whose minimum the ladder
    factorisation splits at is the same object that decides whether a defect may be
    linearised. Over ℚ the identity is exact, ``e_t = 3^(o_t)/2^t``; the walk is its
    base-2 logarithm.
    """
    for w in _all_words(3, 10):
        u = _walk(w)
        e = B.iterate_exponents(w)
        for t_ in range(1, len(w) + 1):
            assert abs(float(e[t_ - 1]) - 2.0 ** u[t_]) < 1e-9 * max(1.0, 2.0 ** u[t_])
        for t_ in range(2, len(w) + 1):
            for s in range(1, t_):
                E = B.composed_map(w, t_, s)
                assert abs(float(E) - 2.0 ** (u[t_ - 1] - u[s])) < 1e-9 * max(1.0, float(E))
                assert (E < 2) == ((u[t_ - 1] - u[s]) < 1.0 - 1e-12)


def test_the_criterion_sees_only_the_letter_counts() -> None:
    """``E`` is a function of ``(#O, #E)`` in the block, not of their order.

    Immediate once ``E = 3^a/2^(a+b)`` and not visible in the product form. The
    closed criterion is the exact integer inequality ``3^a < 2^(a+b+1)``.
    """
    seen: dict[tuple[int, int], Fraction] = {}
    for w in _all_words(3, 10):
        for t_ in range(2, len(w) + 1):
            for s in range(1, t_):
                mid = w[s:t_ - 1]
                key = (mid.count("O"), mid.count("E"))
                E = B.composed_map(w, t_, s)
                if key in seen:
                    assert seen[key] == E, (key, seen[key], E)
                seen[key] = E
    assert len(seen) == 45, len(seen)
    for (a, b), E in seen.items():
        assert (E < 2) == (3 ** a < 2 ** (a + b + 1)), (a, b, E)


def test_the_screen_does_not_test_the_maximal_defect() -> None:
    """The negative finding, pinned so it cannot drift.

    ``E = e_(t-1)/e_s`` is maximised over ``s`` exactly at the walk minimum -- which
    is the letter J-dominant-defect-at-walk-minimum calls dominant. Paper B's screen
    tests the deepest *blocked* defect instead, and the two usually differ: a defect
    the kernel keeps exact is never expanded, so its amplification is irrelevant to
    linearisation. Not a defect in the screen; a structural fact about what it looks at.
    """
    same = diff = 0
    for w in _all_words(3, 11):
        u = _walk(w)
        for t_ in range(3, len(w) + 1):
            deep = B.deepest_blocked(w, t_)
            if deep is None:
                continue
            s_walk = min(range(1, t_), key=lambda s: (u[s], s))
            if deep[0] == s_walk:
                same += 1
            else:
                diff += 1
            # the algebra: E really is maximised at the walk minimum
            best = max(range(1, t_), key=lambda s: B.composed_map(w, t_, s))
            assert B.composed_map(w, t_, best) == B.composed_map(w, t_, s_walk)
    assert (same, diff) == (1026, 3178), (same, diff)


def test_all_three_screen_conditions_are_walk_functionals() -> None:
    """Every condition in the screen is a function of the exponent walk alone.

        no branch runs  <=>  u_(s-1) >= 1              (absolute height)
        E >= 2          <=>  u_(t-1) - u_s >= 1        (a climb)
        coefficient>9/4 <=>  2^u_(t-1) - 2^u_s > 9/4   (a difference of heights)

    Two of the three are unit conditions on the same walk, one absolute and one
    relative. So the screen and the Paper C collision machinery are functionals of
    one object, not two related ones.
    """
    checked = 0
    for w in _all_words(3, 11):
        u = _walk(w)
        e = B.iterate_exponents(w)
        for t_ in range(3, len(w) + 1):
            deep = B.deepest_blocked(w, t_)
            if deep is None:
                continue
            s = deep[0]
            checked += 1
            no_runs = not B.has_branch_runs(B.branch_base(w, t_))
            assert no_runs == (u[s - 1] >= 1.0 - 1e-12), (w, t_, s)
            beyond = bool(B.beyond_methods(w, t_))
            pred = any(float(e[t_ - 2]) - float(e[j - 1]) > 2.25 + 1e-12
                       for j in range(1, t_))
            assert beyond == pred, (w, t_)
    assert checked == 4204, checked


def test_the_two_tilts_are_one_measure_in_different_coordinates() -> None:
    """Paper B's zero-drift tilt is the C -> infinity member of Paper C's theta_C.

    Paper C picks theta_C so the unconditioned tilted mean endpoint sits at the
    barrier -L; at L = 0 that is zero drift, which is the tilt meander_constant
    says Paper B works under, and which is the minimiser of the MGF chernoff_rate
    computes.

    The tilted odd-probabilities agree outright: p_C -> BETA, and Paper B's tilted
    P(O) is BETA. The tilt *parameters* do not, because the two papers tilt by
    different statistics -- Paper C by the odd count o, Paper B by the walk value
    in nats. On words of fixed length t, e^{theta sum X} = e^{theta(o log3 - t log2)}
    is const(t) * e^{(theta log 3) o}, so the two coordinates differ by exactly
    log 3, and theta_C = theta* log 3 to machine precision.
    """
    from research.juggler_sequence.tao_reduction import p_of_C, theta_of_C

    a, b = math.log(1.5), math.log(2.0)
    theta_star = math.log(b / a) / (a + b)          # the MGF minimiser, in closed form

    # the tilt really is zero-drift, and its O-probability is BETA
    m = 0.5 * (math.exp(theta_star * a) + math.exp(-theta_star * b))
    p_star = 0.5 * math.exp(theta_star * a) / m
    assert abs(p_star - BETA_) < 1e-12
    log2_3 = math.log2(3.0)
    drift = p_star * (log2_3 - 1.0) + (1 - p_star) * (-1.0)
    assert abs(drift) < 1e-9, drift

    # Paper C's tilted probability converges to the same number
    for C in (1000, 10000, 100000):
        assert abs(p_of_C(C) - BETA_) < 20.0 / C, C
    # the gap goes like BETA/C, so 6.3e-6 at C = 1e5
    assert abs(p_of_C(100000) - BETA_) < 1e-5

    # and the parameters differ by exactly log 3
    theta_C_limit = math.log(BETA_ / (1 - BETA_))
    assert abs(theta_C_limit - math.log(b / a)) < 1e-12
    assert abs(theta_C_limit - theta_star * math.log(3.0)) < 1e-12
    assert abs(theta_of_C(100000) - theta_C_limit) < 1e-4


def test_paper_c_exponent_is_paper_b_rate_at_level_zero() -> None:
    """e(C) and Paper B's rate are one rate function at two levels.

    The bad-word condition at depth d = CL is u_d > -L, so the odd fraction must
    exceed p(C) = (1 - 1/C)/log2(3), and e(C) = C * KL(p(C) || 1/2)/log 2. Paper B
    sits at L = 0, which is C -> infinity, where p(C) -> 1/log2(3) = BETA. So
    e(C)/C converges to Paper B's own rate in bits, and the two papers' exponents
    are the same function of the same walk evaluated at the level each needs.
    """
    from research.juggler_sequence.tao_reduction import chernoff_exponent, kl_bernoulli

    target = kl_bernoulli(BETA_) / math.log(2.0)
    for C in (100, 1000, 10000, 100000):
        gap = target - chernoff_exponent(C) / C
        assert gap > 0, C
        assert gap < 5.0 / C, (C, gap)          # converges like 1/C
    assert abs(target - chernoff_exponent(100000) / 100000) < 1e-5


def test_the_hoeffding_loss_is_polynomial_not_exponential() -> None:
    """Hoeffding's exponent is nearly sharp; essentially all the loss is the polynomial.

    chernoff_rate() returns the minimised MGF rho, so the sharp rate is -log(rho),
    and that equals the Bernoulli KL at BETA exactly. HOEFFDING_C is 0.034285
    against 0.034688, slack 1.0118 per letter -- "right to one part in eighty" as
    the module says. Over 24 letters that is 1.01x of a total loss of 25.7x. The
    other 25.5x is the d^(-3/2) factor meander_constant names.
    """
    from research.juggler_sequence.tao_reduction import kl_bernoulli

    rho = B.chernoff_rate()
    kl = kl_bernoulli(BETA_)
    assert abs(-math.log(rho) - kl) < 1e-9
    assert 1.011 < kl / B.HOEFFDING_C < 1.012

    for d in (6, 12, 24):
        total = B.hoeffding_bound(d) / B.non_contracting(d)
        exponential = math.exp((kl - B.HOEFFDING_C) * d)
        assert exponential < 1.02, (d, exponential)
        assert total / exponential > 6.0, (d, total, exponential)


def test_paper_b_count_is_paper_c_count_at_level_zero() -> None:
    """N_d is the L = 0 member of the bad-word count: two papers, one function.

    Paper B's Proposition 7.1 counts words with no contracting prefix, i.e. whose
    walk stays at or above 0. Paper C's bad-word count counts words whose walk never
    reaches -L. They are the same dynamic program over (steps, odd letters) at two
    levels, written independently in two modules, and at L = 0 they agree exactly.

    Exactly, not nearly: the two differ in whether the bound is strict, and that
    never bites because u_t = 0 would need 3^(o_t) = 2^t, forcing o_t = t = 0. The
    Lean is `three_pow_eq_two_pow` and `iter_eq_one_iff`.
    """
    from research.juggler_sequence.collision_large_sieve import bad_word_count

    for d in range(1, 17):
        nd = B.non_contracting(d)
        assert nd == bad_word_count(0.0, d), (d, nd, bad_word_count(0.0, d))
        assert nd == bad_word_count(1e-9, d), d

    # every non-contracting word starts with O, so the count's O-rooting is free
    assert all(w[0] == "O" for w in B.surviving_words(8))

    # and the family is monotone in the level
    for d in (8, 12):
        row = [bad_word_count(L, d) for L in (0.0, 0.5, 1.0, 2.0, 4.0)]
        assert row == sorted(row), row


def test_the_hoeffding_step_loses_a_factor_that_grows_with_depth() -> None:
    """Paper B's own docstring names two losses; this measures them apart.

    The combinatorial step of Proposition 7.1 bounds N_d by Hoeffding on the
    endpoint. Two things are given away: the endpoint ignores the requirement at
    every t <= d, and Hoeffding's implied constant is poor in the certified range.
    The total loss grows with depth -- 6.5x at d = 6 and 25.7x at d = 24 -- and
    splits roughly evenly between the two causes.
    """
    rows = []
    for d in (6, 12, 24):
        nd = B.non_contracting(d)
        ep = B.endpoint_only(d)
        hb = B.hoeffding_bound(d)
        rows.append((d, hb / nd, ep / nd, hb / ep))
    total = {d: tot for d, tot, _, _ in rows}
    assert 6.0 < total[6] < 7.0, total
    assert 11.5 < total[12] < 12.5, total
    assert 25.0 < total[24] < 26.5, total
    # the loss is growing, not a fixed constant
    assert total[6] < total[12] < total[24]
    # and neither cause dominates
    for d, tot, path, hoeff in rows:
        assert path > 1.5 and hoeff > 2.0, (d, path, hoeff)


def _beta_semiconvergent_denominators(limit: int) -> set[int]:
    """Ostrowski skeleton of BETA = log3(2): denominators q_(k-1) + j q_k."""
    x, a = BETA_, []
    for _ in range(14):
        i = math.floor(x)
        a.append(i)
        x -= i
        if x < 1e-15:
            break
        x = 1 / x
    q = [0, 1]
    for ai in a[1:]:
        q.append(ai * q[-1] + q[-2])
    q = q[1:]
    out = set()
    for k in range(1, len(q) - 1):
        for j in range(0, a[k + 1] + 1):
            d = q[k - 1] + j * q[k]
            if 2 <= d <= limit:
                out.add(d)
    return out


def test_g_of_one_is_a_ladder_height_transform_over_an_irrational_ratio() -> None:
    """G(1) closes in the ladder height, and there it stops for a structural reason.

    Duality: reversing (S_1,...,S_n) turns {S_k >= 0 for all k <= n} into
    {S_n = max_j S_j}, so sum_n z^n E[e^{-theta S_n}; stay >= 0] is the renewal
    series of the weak ascending ladder and equals 1/(1 - E[z^{T+} e^{-theta H+}]).
    The tilted walk is mean-zero hence recurrent, so T+ < infinity a.s. and at z = 1

        G(1) = 1 / (1 - E[e^{-theta H+}]),

    with H+ in [0, A): the step that first reaches >= 0 is +A and the walk sat in
    [-A, 0) before it. From the series value G(1) = 7.069 this pins
    E[e^{-theta H+}] = 0.85854.

    That is as far as it closes. H+ is the overshoot of a renewal process whose two
    step sizes have IRRATIONAL ratio A/B = log(3/2)/log 2 = log2(3) - 1, so its law
    is an equidistribution object with no elementary form -- and the continued
    fraction governing it is the same one, to its tail, as BETA's:

        A/B      [0; 1, 1, 2, 2, 3, 1, 5, 2, 23, ...]
        log2(3)  [1; 1, 1, 2, 2, 3, 1, 5, 2, 23, ...]
        BETA     [0; 1, 1, 1, 2, 2, 3, 1, 5, 2, 23, ...]

    So the obstruction to a closed G(1) is the same Diophantine structure that makes
    c_d oscillate and the least-peak staircase step at semiconvergents. It is not a
    gap in effort.
    """
    a, b = math.log(3.0) - math.log(2.0), math.log(2.0)

    # the ladder height lives in [0, A) by the geometry of the last step
    assert 0 < a < b

    # the step ratio is log2(3) - 1 and irrational
    assert abs(a / b - (math.log2(3.0) - 1.0)) < 1e-15

    def cf(x: float, n: int = 12) -> list[int]:
        out = []
        for _ in range(n):
            i = math.floor(x)
            out.append(i)
            x -= i
            if x < 1e-14:
                break
            x = 1 / x
        return out

    tail = [1, 2, 2, 3, 1, 5, 2, 23]
    assert cf(a / b)[2:10] == tail, cf(a / b)
    assert cf(math.log2(3.0))[2:10] == tail, cf(math.log2(3.0))
    assert cf(BETA_)[3:11] == tail, cf(BETA_)

    # and the identity pins the transform from the series value
    g1 = 7.069
    assert abs((1 - 1 / g1) - 0.85854) < 1e-5


def test_the_meander_constant_has_a_closed_form_factor() -> None:
    """The constant is kappa * G(1), with kappa closed and G(1) a series in N_d.

    Wiener-Hopf / Spitzer: with P_theta(w) = 2^-d e^{theta S(w)}/M(theta)^d,

        sum_d z^d E[e^{-theta S_d}; survive]  =  exp( sum_n (z^n/n) a_n ),
        a_n = E[e^{-theta S_n}; S_n >= 0] ~ kappa / sqrt(n).

    The exponent carries a -2 sqrt(pi) kappa sqrt(1-z) singularity, so the
    coefficients go like kappa G(1) d^{-3/2} and the meander constant is

        kappa * G(1),   G(1) = sum_d N_d / (2 rho)^d.

    The walk is NOT on a lattice -- S_n = o log 3 - n log 2 with log3/log2
    irrational -- so no lattice correction enters, and kappa is the non-lattice
    local-limit constant 1/(sqrt(2 pi) theta sigma).

    Two closed forms fall out. The variance is exactly the product of the two step
    sizes, sigma^2 = log(3/2) log 2, and theta* = log(log2/log(3/2))/log 3.
    """
    a, b = math.log(3.0) - math.log(2.0), math.log(2.0)
    theta, _rho, _p, sigma = _tilt_constants()

    # sigma^2 is exactly the product of the step sizes
    assert abs(sigma ** 2 - a * b) < 1e-15, (sigma ** 2, a * b)
    # and theta has the stated closed form
    assert abs(theta - math.log(b / a) / (a + b)) < 1e-15

    kappa = 1.0 / (math.sqrt(2 * math.pi) * theta * sigma)
    assert abs(kappa - 1.541814521) < 1e-8, kappa


def test_the_derived_constant_matches_the_measured_one() -> None:
    """kappa * G(1) is about 10.90, and c_d oscillates around it rather than rising to it.

    G(1) = sum_d N_d/(2 rho)^d is computed with an exact integer mask (o log2(3) >= d
    tested as o * floor(log2(3) * 10^30) >= d * 10^30, exact for any depth here) and
    a d^{-3/2} tail. It settles at 7.07, giving kappa G(1) = 10.90 stable across
    d = 1600 to 12000.

    c_d = (N_d/2^d)/(rho^d d^{-3/2}) does NOT climb monotonically to that: it reads
    10.757, 11.046, 11.034, 11.063, 10.566 at d = 1600, 3200, 6400, 9600, 12000. It
    oscillates, which is why a single sample is not the limit -- an earlier reading
    of this called 11.03 "the true limit" on the strength of d = 3200 alone.
    """
    _theta, rho, _p, _sigma = _tilt_constants()
    from decimal import Decimal, getcontext

    getcontext().prec = 50
    K = 10 ** 30
    l23 = int((Decimal(3).ln() / Decimal(2).ln()) * K)
    scale = 1.0 / (2 * rho)

    st, G, last = {0: 1.0}, 1.0, 0.0
    D = 1600
    for d in range(1, D + 1):
        nx: dict[int, float] = {}
        dk = d * K
        for o, w in st.items():
            for do in (0, 1):
                o2 = o + do
                if o2 * l23 >= dk:
                    nx[o2] = nx.get(o2, 0.0) + w * scale
        st = nx
        last = sum(st.values())
        G += last

    theta, _r, _pp, sigma = _tilt_constants()
    kappa = 1.0 / (math.sqrt(2 * math.pi) * theta * sigma)
    g_full = G + 2.0 * last * D                    # d^{-3/2} tail
    assert 7.0 < g_full < 7.15, g_full
    assert 10.8 < kappa * g_full < 11.0, kappa * g_full

    # the exact-mask DP reproduces Paper B's own count, compared in logs since
    # (2 rho)^1600 overflows a float
    expected = math.log(B.non_contracting(D)) - D * math.log(2 * rho)
    assert abs(math.log(last) - expected) < 1e-9, (math.log(last), expected)


def _tilt_constants() -> tuple[float, float, float, float]:
    """(theta*, rho, p*, sigma) for the zero-drift tilt, in nats."""
    a, b = math.log(3.0) - math.log(2.0), math.log(2.0)
    theta = math.log(b / a) / (a + b)
    rho = 0.5 * (math.exp(theta * a) + math.exp(-theta * b))
    p = 0.5 * math.exp(theta * a) / rho
    sigma = math.sqrt(p * a * a + (1 - p) * b * b - (p * a - (1 - p) * b) ** 2)
    return theta, rho, p, sigma


def _tilted_survival_and_cost(d: int) -> tuple[float, float]:
    """P_theta(survive) and E_theta[e^{-theta S_d} | survive]."""
    theta, _rho, p, _sigma = _tilt_constants()
    a, b = math.log(3.0) - math.log(2.0), math.log(2.0)
    st = {0: 1.0}
    for step in range(1, d + 1):
        nx: dict[int, float] = {}
        for o, w in st.items():
            for do, pr in ((1, p), (0, 1 - p)):
                o2 = o + do
                if o2 * a - (step - o2) * b < -1e-15:
                    continue
                nx[o2] = nx.get(o2, 0.0) + w * pr
        st = nx
    surv = sum(st.values())
    cost = sum(w * math.exp(-theta * (o * a - (d - o) * b)) for o, w in st.items())
    return surv, cost / surv


def test_paper_bs_meander_constant_splits_and_only_one_half_is_slow() -> None:
    """The constant is a product, and its non-convergence lives in one factor.

    Exactly, from the change of measure: with P_theta(w) = 2^-d e^{theta S(w)} /
    M(theta)^d,

        N_d / 2^d = rho^d * E_theta[1_survive e^{-theta S_d}]

    which is checked here to nine figures. At the zero-drift tilt that splits into
    the survival probability, ~ c1/sqrt(d), and the endpoint cost, ~ c2/d because
    S_d ~ sigma sqrt(d) and the meander density vanishes linearly at the origin.
    Together, d^{-3/2}.

    Measured, the two behave nothing alike. P(surv) sqrt(d) is flat from d = 400 at
    0.66746 -- the ladder constant, settled. E[cost|surv] d is still climbing at
    d = 1600 and only settles near 16.53 by d = 3200-6400. Their product is 11.03,
    so that is the true limit of meander_constant; the depths it prints (9.84,
    10.45, 10.76 at 400, 800, 1600) are still 2.5% short at the deepest.

    The Brownian prediction for the second factor is 1/(theta sigma)^2 = 14.936,
    against 16.53 measured: a factor 1.107 the continuum picture does not supply,
    which is the lattice ladder-height correction.
    """
    theta, rho, _p, sigma = _tilt_constants()

    # the identity, exactly
    for d in (100, 400):
        lhs = B.non_contracting(d) / 2 ** d
        surv, cond = _tilted_survival_and_cost(d)
        assert abs(lhs - rho ** d * cond * surv) / lhs < 1e-9, d

    # the survival factor has converged
    svals = [_tilted_survival_and_cost(d)[0] * math.sqrt(d) for d in (400, 800, 1600)]
    assert all(abs(v - 0.6675) < 5e-4 for v in svals), svals
    # it is not yet settled at 200, which is why the claim starts at 400
    assert abs(_tilted_survival_and_cost(200)[0] * math.sqrt(200) - 0.6675) > 5e-4

    # the endpoint factor has not, at the depths meander_constant prints
    c800 = _tilted_survival_and_cost(800)[1] * 800
    c1600 = _tilted_survival_and_cost(1600)[1] * 1600
    assert 15.5 < c800 < 15.8 and 16.0 < c1600 < 16.3, (c800, c1600)
    assert c1600 - c800 > 0.3, (c800, c1600)       # still climbing

    # and the continuum prediction is short by the lattice factor
    predicted = 1.0 / (theta * sigma) ** 2
    assert abs(predicted - 14.936) < 1e-3, predicted
    assert 1.09 < 16.53 / predicted < 1.12


def _endpoint_profile(d: int) -> tuple[int, list[tuple[float, float]]]:
    """(N_d, [(endpoint level, share of N_d)]) with an exact integer mask."""
    from decimal import Decimal, getcontext

    getcontext().prec = 50
    log2_3 = math.log2(3.0)
    k = 10 ** 30
    l23k = int((Decimal(3).ln() / Decimal(2).ln()) * k)
    st = {0: 1}
    for step in range(1, d + 1):
        nx: dict[int, int] = {}
        tk = step * k
        for o, c in st.items():
            for do in (0, 1):
                o2 = o + do
                if o2 * l23k >= tk:
                    nx[o2] = nx.get(o2, 0) + c
        st = nx
    tot = sum(st.values())
    return tot, sorted((o * log2_3 - d, c / tot) for o, c in st.items())


def _beta_cf_and_denominators(n: int = 30):
    from decimal import Decimal, getcontext

    getcontext().prec = 120
    beta = Decimal(2).ln() / Decimal(3).ln()
    a, x = [], beta
    for _ in range(n):
        i = int(x)
        a.append(i)
        x -= i
        if x == 0:
            break
        x = 1 / x
    q = [0, 1]
    for ai in a[1:]:
        q.append(ai * q[-1] + q[-2])
    return a, q[1:]


def test_the_55_family_is_the_last_hard_one_in_reach() -> None:
    """a_16 onward, and what it says about the cost after 16785921.

    BETA's partial quotients are stable to 80 terms between 200- and 400-digit
    arithmetic, so the tail used here is not a precision artefact. From a_16:

        1, 4, 3, 1, 1, 15, 1, 9, 2, 5, 7, 1, 1, 4, 8, 1, 11, 1, 20, 2, 1, 10, ...

    The above-side families -- the ones the cycle work must walk -- then run

        q_14 = 301994          55 members     478245 .. 16785921
        q_16 = 17087915         4 members   33873836 .. 85137581
        q_18 = 272500658        1 member   357638239
        q_20 = 630138897       15 members 987777136 .. 9809721694

    So 16785921 is the END of the difficulty, not the start of worse: the family
    drops from 55 members to 4, then to 1. The next comparable cluster is 15
    members built on q_20, whose first member is near 10^9 and whose certified
    floor would be far out of reach.

    The practical reading is that the 55-member family now being walked is the
    binding obstruction and the last one at an accessible scale.
    """
    a, q = _beta_cf_and_denominators(30)
    assert a[15] == 55
    assert a[16:22] == [1, 4, 3, 1, 1, 15], a[16:22]
    assert q[15] == 16785921 and q[16] == 17087915

    # the family immediately after the 55 is much smaller
    assert a[17] == 4
    nxt = [q[15] + j * q[16] for j in range(1, a[17] + 1)]
    assert nxt == [33873836, 50961751, 68049666, 85137581], nxt

    # and nothing between 16785921 and 10^8 is bigger than 4 members
    sizes = {k: a[k + 1] for k in (16, 17, 18) if q[k] < 10 ** 9}
    assert max(sizes.values()) <= 4, sizes


def test_the_cycle_period_bounds_are_one_semiconvergent_family() -> None:
    """The lab's successive period lower bounds are j = 0, 1, 2 of one family.

    cycle_gap_baker's RECORD_LENGTHS are exactly the above-side semiconvergent
    denominators of BETA (J-the-cycle-staircase-split-is-a-sign-condition), which
    reproduces all eight of them and correctly skips the 23-member below-side family
    1539 ... 24727 that the module also skips.

    Continuing the rule past 50508 gives 176251, 478245, 780239, 1082233, ... -- and
    the ledger's three successive period bounds are the first three of those:
    J-cyclemin-walk-charge-instance at 176251, then 478245, then 780239, the last
    recorded there as 780239 = 176251 + 2 x 301994 and called Diophantine rather
    than computational.

    The family is q_13 + j q_14 = 176251 + j x 301994. It has 56 members because
    a_15 = 55, ending at q_15 = 16785921. Three are cleared, so 53 remain: that is
    the price of the current one-leftover-at-a-time route through this family,
    read off the continued fraction rather than discovered by search.
    """
    a, q = _beta_cf_and_denominators()
    assert q[13] == 176251 and q[14] == 301994, (q[13], q[14])
    assert a[15] == 55, a[15]
    assert q[15] == 16785921, q[15]

    family = [q[13] + j * q[14] for j in range(0, a[15] + 1)]
    assert len(family) == 56, len(family)
    assert family[:3] == [176251, 478245, 780239], family[:3]
    assert family[-1] == q[15]

    cleared = [176251, 478245, 780239]
    assert [(c - q[13]) // q[14] for c in cleared] == [0, 1, 2]
    assert len(family) - len(cleared) == 53


def test_near_closure_costs_nothing_in_word_count() -> None:
    """A cycle must nearly close, and that is free at the word-counting level.

    The endpoint u_d = o log2(3) - d takes values spaced log2(3) = 1.585 apart, so
    "u_d small and positive" is not a continuum event: at most one o qualifies at a
    given d, and generically none. The continuum meander density vanishes linearly
    at the origin, which would suggest the smallest positive level carries almost no
    mass. It does not.

    The profile over the lattice depends on the INDEX, not on the level's value. At
    d = 1054 the lowest level is 6.3e-5 and carries 7.65% of all non-contracting
    words; at d = 700 the lowest is 0.553 -- four orders of magnitude larger -- and
    carries 9.88%. The bottom level sits at roughly 40% of the next one up either
    way, which is the descending-ladder renewal function being positive at the
    origin rather than vanishing there.

    Consequence, and it is a closed door: near-closure provides NO word-counting
    suppression. Cycle candidates are not rare among non-contracting words, so a
    counting argument cannot bound them, and the Baker / Rhin lower bound on
    |L log 2 - o log 3| is doing all the work on the cycle side. That is presumably
    why the cycle module reaches for transcendence rather than for counting.
    """
    for d, expect_low in ((700, 0.0988), (1054, 0.0765)):
        tot, levels = _endpoint_profile(d)
        assert tot > 0
        u0, s0 = levels[0]
        _u1, s1 = levels[1]
        assert abs(s0 - expect_low) < 2e-3, (d, u0, s0)
        # the bottom level is depressed relative to the next, but only by ~2.5x,
        # nothing like the factor u0 a linear density would demand
        assert 0.3 < s0 / s1 < 0.55, (d, s0, s1)

    # the share of the lowest level is insensitive to how small that level is
    _t7, l7 = _endpoint_profile(700)
    _t10, l10 = _endpoint_profile(1054)
    assert l7[0][0] > 100 * l10[0][0]          # levels differ by >2 orders
    assert abs(l7[0][1] - l10[0][1]) < 0.03    # shares do not


def test_the_two_families_are_opposite_signs_of_one_approximation() -> None:
    """The complementarity is forced by sign, not by anything about log2(3).

    A cycle needs 3^o > 2^d: the CycleMin finance bound
    n ln n <= (6/5) L 3^o/(3^o - 2^L) is only meaningful when 3^o - 2^L > 0, i.e.
    the walk gap o log2(3) - d is POSITIVE. The staircase's binding level sits just
    below 1 - c = 2 - log2(3), where both E and OE are illegal and the walk must
    take OO; that is (o+1) log2(3) - (d+2) slightly NEGATIVE.

    So the two read the same approximation error with opposite signs. Measured: all
    eleven staircase jumps below 1200 have gap < 0, all six cycle record lengths
    have gap > 0. And a denominator has one sign, so the two sets are disjoint by
    construction -- for any irrational, checked on sqrt(2), the golden ratio, e and
    pi as well as log2(3).

    That is what makes the closed door permanent rather than a fact about the
    depths tried: no d can serve both constraints, at any depth, for any slope.
    """
    log2_3 = math.log2(3.0)

    def gap(d: int) -> float:
        o = round(d / log2_3)
        return min(((abs(c * log2_3 - d), c * log2_3 - d) for c in (o - 1, o, o + 1)))[1]

    jumps = [2, 5, 8, 27, 46, 65, 149, 233, 317, 401, 485]
    records = [3, 11, 19, 84, 569, 1054]
    assert all(gap(d) < 0 for d in jumps), [(d, gap(d)) for d in jumps]
    assert all(gap(d) > 0 for d in records), [(d, gap(d)) for d in records]

    # and the split into signs is disjoint for any irrational, not just this one
    def cf(x: float, n: int = 13) -> list[int]:
        out = []
        for _ in range(n):
            i = math.floor(x)
            out.append(i)
            x -= i
            if x < 1e-15:
                break
            x = 1 / x
        return out

    for alpha in (log2_3, math.sqrt(2.0), (1 + math.sqrt(5.0)) / 2, math.e, math.pi):
        a = cf(alpha)
        q = [0, 1]
        for ai in a[1:]:
            q.append(ai * q[-1] + q[-2])
        q = q[1:]
        below, above = set(), set()
        for k in range(1, len(q) - 1):
            for j in range(0, a[k + 1] + 1):
                d = q[k - 1] + j * q[k]
                if not (2 <= d <= 3000):
                    continue
                (below if d * alpha - round(d * alpha) < 0 else above).add(d)
        assert below and above, alpha
        assert below.isdisjoint(above), (alpha, sorted(below & above)[:5])


def test_the_cycle_record_lengths_are_the_staircase_non_jumps() -> None:
    """The no-cycle side and this bridge share one walk and split its Ostrowski skeleton.

    The CycleMin finance walk is u_k = log2(3/2)(#odds) - (#evens), which is this
    walk: o log2(3) - t = o log2(3/2) - #evens identically. Its constraint u_k >= 0
    is Paper B's non-contracting condition, and a cycle must also nearly close --
    |o log2(3) - d| tiny, i.e. o/d an exceptionally good approximation to BETA,
    which is what cycle_gap_baker bounds below via Rhin / Simons-de Weger.

    So both sides are reading BETA's continued fraction, and they take opposite
    halves of it. The cycle module's near-convergent RECORD_LENGTHS below 1200 are
    3, 11, 19, 84, 569, 1054 -- exactly the semiconvergent denominators at which the
    least-peak staircase does NOT step, which are the convergents approaching BETA
    from the other side.

    That is a closed door rather than a lever: the lengths where a cycle is
    Diophantine-plausible are exactly the lengths where the non-contracting
    constraint costs nothing extra, so the two cannot be played against each other
    at a common d.
    """
    from research.juggler_sequence.cycle_gap_baker import RECORD_LENGTHS
    from research.juggler_sequence.cycle_walk_charge import MU, STEP

    log2_3 = math.log2(3.0)
    # the cycle walk is this walk
    assert abs(MU - (log2_3 - 1.0)) < 1e-15
    assert abs(STEP - log2_3) < 1e-15
    for w in _all_words(3, 10):
        o = w.count("O")
        assert abs((o * log2_3 - len(w)) - (MU * o - (len(w) - o))) < 1e-12, w

    limit = 1200
    peaks = _least_peak(limit)
    jumps = {k + 1 for k in range(1, len(peaks)) if peaks[k] > peaks[k - 1] + 1e-12}
    jumps.add(2)
    semis = _beta_semiconvergent_denominators(limit)

    non_jumps = sorted(semis - jumps)
    records = sorted(r for r in RECORD_LENGTHS if 2 <= r <= limit)
    assert non_jumps == records == [3, 11, 19, 84, 569, 1054], (non_jumps, records)


def test_the_least_peak_staircase_is_betas_ostrowski_skeleton() -> None:
    """Where the least peak rises is a Diophantine fact about BETA, not a numeric one.

    The walk is u_t = o log2(3) - t, so it hugs a level exactly when o/t approximates
    1/log2(3) = BETA = log3(2). The least peak P(k) is set by how closely a reachable
    level creeps below 1 - c, an inhomogeneous one-sided approximation to BETA, so the
    staircase should step only at BETA's best approximation denominators.

    It does. Up to length 1200 the jumps are 2, 5, 8, 27, 46, 65, 149, 233, 317, 401,
    485 -- every one a semiconvergent denominator of BETA, with no exception. The
    structure is visible in the differences: 2, 5, 8 steps by 3; 8, 27, 46, 65 by 19;
    65, 149, 233, 317, 401, 485 by 84, and 3, 19, 84 are themselves convergent
    denominators.

    The converse fails, and informatively: 3, 19, 84 and 1054 are semiconvergents that
    are not jumps. Those are the convergents approaching BETA from the other side, and
    the staircase is one-sided by construction.

    This is the same constant the Juggler Ostrowski Lean layer certifies -- its theta
    denominators close at q = 301994, which is a convergent denominator of BETA.
    """
    limit = 1200
    peaks = _least_peak(limit)
    jumps = {k + 1 for k in range(1, len(peaks)) if peaks[k] > peaks[k - 1] + 1e-12}
    jumps.add(2)
    assert sorted(jumps) == [2, 5, 8, 27, 46, 65, 149, 233, 317, 401, 485], sorted(jumps)

    semis = _beta_semiconvergent_denominators(limit)
    assert jumps <= semis, sorted(jumps - semis)
    # one-sided: the other side's convergents are semiconvergents but not jumps
    assert {3, 19, 84} <= semis - jumps, sorted(semis - jumps)

    # and 301994, which the Lean layer certifies, is a convergent denominator
    x, a = BETA_, []
    for _ in range(16):
        i = math.floor(x)
        a.append(i)
        x -= i
        x = 1 / x
    q = [0, 1]
    for ai in a[1:]:
        q.append(ai * q[-1] + q[-2])
    assert 301994 in q, q[:16]


def _least_peak(kmax: int) -> list[float]:
    """Least achievable walk peak over non-contracting words, by length.

    State is (steps, odd letters), which fixes the level, so this is a DP rather
    than a search over 2^k words.
    """
    log2_3 = math.log2(3.0)
    f = {0: 0.0}
    out = []
    for step in range(1, kmax + 1):
        g: dict[int, float] = {}
        for a, peak in f.items():
            for da in (0, 1):
                a2 = a + da
                u = a2 * log2_3 - step
                if u < -1e-12:
                    continue
                p = max(peak, u)
                if a2 not in g or p < g[a2] - 1e-12:
                    g[a2] = p
        f = g
        out.append(min(f.values()))
    return out


def test_the_noncontracting_peak_is_bounded_and_its_supremum_is_log2_three() -> None:
    """The height route to a large-depth emptiness theorem is closed.

    The least peak a non-contracting walk can have is non-decreasing in length and
    always strictly below log2(3) = 1.58496, approaching it: the gap is 7.5e-2 at
    length 13 and 1.3e-3 at 3000. So the walk of the cheapest contractor does NOT
    get arbitrarily high, and no argument of the form "at depth d the walk must
    exceed T" can be made for T >= log2(3).

    The supremum has a reason. From a level u < 1 - c (c = log2(3) - 1) both E and
    OE are illegal, so the walk must take two O steps and reach u + 2c; levels
    a*log2(3) - t come arbitrarily close below 1 - c, forcing a peak arbitrarily
    close to (1 - c) + 2c = log2(3), and never equal to it because log2(3) is
    irrational. The measured gap to log2(3) matches the gap of the closest
    reachable level below 1 - c to three figures.

    The lower end is proved rather than measured: 2 log2(3) - 2 = 1.1699 at length
    two, which is `noncontracting_two_forces` in Lean, and it is above the
    branch-run threshold of 1. So the threshold is always cleared and the peak is
    always bounded -- the first is why the hypothesis can fire at every depth, the
    second is why that cannot be turned into a theorem by height alone.
    """
    log2_3 = math.log2(3.0)
    peaks = _least_peak(1200)

    assert all(peaks[i] <= peaks[i + 1] + 1e-12 for i in range(len(peaks) - 1))
    assert all(p < log2_3 - 1e-15 for p in peaks)
    assert peaks[1] == pytest.approx(2 * log2_3 - 2, abs=1e-9)
    assert peaks[1] > 1.0

    assert peaks[12] == pytest.approx(1.509775, abs=1e-5)
    assert peaks[99] == pytest.approx(1.568425, abs=1e-5)
    assert peaks[999] == pytest.approx(1.583488, abs=1e-5)
    # approaching log2(3), and still short of it
    assert 0 < log2_3 - peaks[999] < 2e-3


def test_non_contraction_forces_the_branch_threshold() -> None:
    """Staying non-contracting and tripping the branch-run hypothesis are the same
    constraint at two thresholds, 0 and 1, and at step two the first forces the second.

    A prefix that has not contracted by step two must be OO -- E first gives
    u_1 = -1, and OE gives u_2 = log2(3) - 2 < 0 -- so u_2 = 2 log2(3) - 2 = 1.1699,
    above the branch-run threshold of 1 because 3 > 2^(3/2). Every contractor begins
    OO for that reason. The Lean is `noncontracting_two_forces`.

    The forcing does not extend along the word: the walk is not monotone, so a later
    blocked defect can sit back below 1 (OOOEOOEE does, at s = 5 with u_4 = 0.755).
    What is measured here is that from depth ten the hypothesis nevertheless fires on
    every contractor.
    """
    contractors = [w + "E" for d in range(4, 14) for w in B.dying_words(d)]
    assert len(contractors) == 140
    assert {w[:2] for w in contractors} == {"OO"}

    peaks_by_depth = {}
    fires_by_depth = {}
    for d in range(4, 14):
        words = [w + "E" for w in B.dying_words(d)]
        if not words:
            continue
        peaks_by_depth[d] = min(max(_walk(w)) for w in words)
        fires_by_depth[d] = sum(
            1 for w in words
            if any(B.deepest_blocked(w, t_) is not None
                   and not B.has_branch_runs(B.branch_base(w, t_))
                   for t_ in range(3, len(w) + 1)))
    # the minimum peak a contractor can have rises with depth, and never dips to 1
    assert all(p > 1.0 for p in peaks_by_depth.values()), peaks_by_depth
    assert round(peaks_by_depth[4], 3) == 1.170
    assert round(peaks_by_depth[13], 3) == 1.510
    # and from depth ten the branch-run hypothesis fires on every one
    assert fires_by_depth[10] == 12 and fires_by_depth[12] == 30
    assert fires_by_depth[13] == 85


def _screen_verdict(word: str, use_theorem: bool) -> bool:
    """`unobstructed`, with the E < 2 criterion optionally switched off."""
    for t_ in range(3, len(word) + 1):
        if B.deepest_blocked(word, t_) is None:
            continue
        if not B.has_branch_runs(B.branch_base(word, t_)):
            return False
        if B.beyond_methods(word, t_):
            return False
        if use_theorem and not B.linearisation_safe(word, t_):
            return False
    return True


def test_the_screens_only_theorem_is_decisive_on_no_contractor() -> None:
    """The screen is hypothesis-driven end to end on the words it is applied to.

    Of its three conditions only E < 2 is proved. It fires on 60 of the 140
    contractors at depths 4..13 and changes the verdict on none of them: the same
    five words survive whether or not it is switched on. The two hypotheses --
    Conjecture 7.3's 9/4 and the branch-run sufficiency claim -- reject 135 of 140
    unaided.

    The criterion is not vacuous in general; it is decisive on 556 of the 4088 words
    of length 3..11. It is redundant specifically on contractors, which are the only
    words the screen sees. So the 227/256 certified density and the emptiness of the
    screen at depths 10, 12 and 13 rest on two unproved thresholds, with no proved
    ingredient contributing to any verdict.
    """
    words = [w + "E" for d in range(4, 14) for w in B.dying_words(d)]
    assert len(words) == 140, len(words)

    full = [w for w in words if _screen_verdict(w, True)]
    without = [w for w in words if _screen_verdict(w, False)]
    assert full == without, set(full) ^ set(without)
    assert len(full) == 5, full

    fires = [w for w in words
             if any(B.deepest_blocked(w, t_) is not None
                    and not B.linearisation_safe(w, t_)
                    for t_ in range(3, len(w) + 1))]
    assert len(fires) == 60, len(fires)

    # and the criterion is not vacuous away from the contractors
    decisive = [w for w in _all_words(3, 11)
                if _screen_verdict(w, True) != _screen_verdict(w, False)]
    assert len(decisive) == 556, len(decisive)


def test_the_screens_other_two_thresholds_are_not_identities() -> None:
    """The split the prospecting note demands, asserted rather than described.

    ``E < 2`` is a theorem about where the second-order term sits.  The other two
    conditions in ``unobstructed`` are not: ``9/4`` is the coefficient past which
    *Conjecture 7.3* says every method stops, and branch runs are a sufficiency
    claim relative to Paper B's toolkit.  Both are hypotheses, and a row that
    called them lemmas would be a definition wearing a theorem's label.  What can
    be checked is that they are genuinely independent of the criterion -- if they
    were implied by it, the distinction would be empty.
    """
    combos = set()
    for w in _all_words(3, 9):
        for t_ in range(3, len(w) + 1):
            if B.deepest_blocked(w, t_) is None:
                continue
            base = B.branch_base(w, t_)
            combos.add((B.linearisation_safe(w, t_),
                        bool(B.has_branch_runs(base)),
                        bool(B.beyond_methods(w, t_))))
    # E < 2 holding tells you nothing about either threshold.
    assert len({c[1] for c in combos if c[0]}) == 2, combos
    assert len({c[2] for c in combos if c[0]}) == 2, combos


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


# --- the screen over every contractor at every paying depth ---


def test_only_one_contractor_survives_at_depth_seven_and_eight() -> None:
    assert [w for w, _ in B.screen_depth(7)] == ["OOOEOEE"]
    assert [w for w, _ in B.screen_depth(8)] == ["OOOEOEOE"]


@pytest.mark.parametrize("d,total", [(10, 12), (12, 30), (13, 85)])
def test_nothing_survives_beyond_depth_eight(d: int, total: int) -> None:
    assert len(B.dying_words(d)) == total, d
    assert B.screen_depth(d) == [], d


def test_the_two_survivors_need_identical_machinery() -> None:
    """Same first six letters, so the same two kernels -- one proved, one not."""
    assert "OOOEOEE"[:6] == "OOOEOEOE"[:6] == "OOOEOE"
    for word in ("OOOEOEE", "OOOEOEOE"):
        assert B.unobstructed(word) == [(4, 2), (6, 1)], word
        # letter 4 is Theorem 5.3's own monomial
        assert B.deepest_blocked(word, 4) == B.deepest_blocked("OOO", 4)
        assert B.deepest_blocked(word, 4)[1:3] == (Fraction(3, 4), Fraction(9, 8))
        # letter 6 is the level-1 kernel, the single new ingredient
        assert B.deepest_blocked(word, 6)[1:3] == (Fraction(27, 32), Fraction(33, 32))


def test_the_level_one_kernel_is_worth_three_over_two_five_six() -> None:
    total = sum(Fraction(len(B.screen_depth(d)), 2 ** d) for d in (7, 8, 10, 12, 13))
    assert total == Fraction(3, 256)
    assert Fraction(7, 8) + total == Fraction(227, 256)


def test_the_screen_rejects_for_the_stated_reasons() -> None:
    """OOEOOEE fails on E >= 2 and branch runs; OOOOEEE on the 9/4 stop."""
    assert B.unobstructed("OOEOOEE") is None
    assert not B.linearisation_safe("OOEOOEE", 6)
    assert B.unobstructed("OOOOEEE") is None
    assert B.beyond_methods("OOOOEEE", 5) != []


def test_paper_carries_the_screen_table() -> None:
    text = io.open(PAPER, encoding="utf-8").read()
    assert "What one theorem would buy." in text
    assert r"\(227/256\)" in text
    assert r"\(127\) contractors" in text
    assert "negative evidence" in text


# --- what the level-1 kernel is: the same waves, at a wider frequency range ---


def test_the_sawtooth_fourier_modes_are_the_monomial_waves() -> None:
    """e(r{x}) = e(rx) for integer r, since r*floor(x) is an integer."""
    from mpmath import mp, mpf, pi, floor, power, exp
    mp.dps = 40
    for x in (mpf("3.7"), mpf("1234.56789"), power(mpf(1000003), mpf(3) / 2)):
        for r in (1, 2, -5, 37):
            lhs = exp(2j * pi * r * (x - floor(x)))
            rhs = exp(2j * pi * r * x)
            assert abs(lhs - rhs) < mpf(10) ** -25, (x, r)


def test_the_gap_is_a_frequency_range_of_P_95_over_96() -> None:
    """Theorems 4.4/4.7 reach P^{1/24}; the kernel's mass sits at P^{33/32}."""
    _, exponent = B.defect_coefficient("OOOEOEE", 6, 1)
    assert exponent == Fraction(33, 32)
    assert exponent - Fraction(1, 24) == Fraction(95, 96)


def test_the_drift_threshold_is_a_sub_lattice_window() -> None:
    """Coefficient exponent c gives a window of length P^{1-c}; above 1 it holds no integer."""
    _, exponent = B.defect_coefficient("OOOEOEE", 6, 1)
    assert 1 - exponent == Fraction(-1, 32)
    assert exponent > B.DRIFT_THRESHOLD
    # and the unblocked coefficients of the same word do give windows of positive length
    for s in (2, 4):
        _, e2 = B.defect_coefficient("OOOEOEE", 6, s)
        assert e2 < B.DRIFT_THRESHOLD and 1 - e2 > 0, s


def test_paper_states_what_the_level_one_kernel_is() -> None:
    text = io.open(PAPER, encoding="utf-8").read()
    assert "It is not a new species." in text
    assert r"e(r\{x\})=e(rx)" in text
    assert r"a gap of \(P^{95/96}\)" in text
    assert "finer than the lattice it is supposed to sit on" in text


# --- what one Fourier mode is worth ---


def test_the_generator_reproduces_the_classical_pairs() -> None:
    pairs = B.van_der_corput_pairs()
    assert (Fraction(0), Fraction(1)) in pairs                 # trivial
    assert (Fraction(1, 2), Fraction(1, 2)) in pairs           # B of trivial
    assert (Fraction(1, 6), Fraction(2, 3)) in pairs           # AB of trivial
    assert all(k >= 0 and l >= 0 for k, l in pairs)


def test_the_best_pair_at_the_kernel_frequency() -> None:
    """Phase size P^{81/32} is e(r n^{3/2}) at r ~ k P^{33/32}."""
    pair, value, saving = B.best_monomial_bound(Fraction(81, 32))
    assert pair == (Fraction(1, 11), Fraction(3, 4))
    assert value == Fraction(313, 352)
    assert saving == Fraction(39, 352)
    assert value < 1                                            # nontrivial


def test_a_quarter_of_the_mode_saving_clears_one_over_ninetysix() -> None:
    """The chain quarters a saving, so it needs 1/24 to reach P^{1-1/96}."""
    _, _, saving = B.best_monomial_bound(Fraction(81, 32))
    assert saving / 4 > Fraction(1, 96)
    assert saving > Fraction(1, 24)
    assert abs(float(saving / 4 / Fraction(1, 96)) - 2.66) < 0.01
    # and the chain's own arithmetic agrees
    assert B.differencing_chain(saving)["saving"] == saving / 4


def test_the_phase_size_is_the_wave_exponent() -> None:
    """P^{81/32} is e_5 of both winners -- the size is not an extra assumption."""
    for word in ("OOOEOEE", "OOOEOEOE"):
        assert B.iterate_exponents(word)[4] == Fraction(81, 32), word
        _, coeff_exp = B.defect_coefficient(word, 6, 1)
        assert coeff_exp + Fraction(3, 2) == Fraction(81, 32), word


def test_paper_states_the_mode_bound_and_its_caveat() -> None:
    text = io.open(PAPER, encoding="utf-8").read()
    assert "What one mode is worth." in text
    assert r"P^{313/352}" in text and r"\tfrac{39}{352}" in text
    assert "van der Corput pairs, not the" in text
    assert "says nothing whatever" in text


# --- the criterion retrodicts the paper's own frontier ---


ELEMENTARY_D4 = ["OEEE", "OEEO", "OEOE", "OEOO", "OOEE", "OOEO"]
KERNEL_D4 = ["OOOE", "OOOO"]


def test_depth_four_separates_exactly_as_the_paper_does() -> None:
    """Six words unblocked at every letter; those are the six proved by windows."""
    from itertools import product
    unblocked, blocked = [], []
    for bits in product("EO", repeat=3):
        w = "O" + "".join(bits)
        hit = any(B.deepest_blocked(w, t) for t in (3, 4))
        (blocked if hit else unblocked).append(w)
    assert sorted(unblocked) == ELEMENTARY_D4
    assert sorted(blocked) == KERNEL_D4


def test_the_two_blocked_depth_four_words_are_the_OOO_split() -> None:
    for w in KERNEL_D4:
        d = B.deepest_blocked(w, 4)
        assert d[0] == 2 and d[1:3] == (Fraction(3, 4), Fraction(9, 8))
        assert d == B.deepest_blocked("OOO", 4)


@pytest.mark.parametrize("word,letters", [
    ("OOEOE", []), ("OOEOO", []),
    ("OOOEE", [(4, 2)]), ("OOOEO", [(4, 2)]),
    ("OOOOE", [(4, 2), (5, 3)]), ("OOOOO", [(4, 2), (5, 3)]),
])
def test_depth_five_grades_three_ways(word: str, letters: list) -> None:
    """Windows only / level-2 kernel / open, matching Theorem 6.3 and Conjecture 7.3."""
    got = [(t, B.deepest_blocked(word, t)[0]) for t in range(3, 6)
           if B.deepest_blocked(word, t)]
    assert got == letters, word


def test_the_unblocked_depth_five_pair_has_the_better_exponent() -> None:
    """47/48 beats 1 - 1/96, which is what a kernel-free argument should give."""
    assert Fraction(47, 48) < 1 - Fraction(1, 96)
    for w in ("OOEOE", "OOEOO"):
        assert all(B.deepest_blocked(w, t) is None for t in range(3, 6)), w


def test_paper_states_the_retrodiction() -> None:
    text = io.open(PAPER, encoding="utf-8").read()
    assert "not calibrated on depth seven" in text
    assert "for the drift reason and for no other" in text
    assert "sixteen words, three outcomes, no" in text


# --- the starts the paper excludes ---


def _blocked_stats(root: str, d: int):
    from itertools import product
    total = blocked = sqrt_kind = 0
    for bits in product("EO", repeat=d - 1):
        w = root + "".join(bits)
        total += 1
        hits = [B.deepest_blocked(w, t) for t in range(3, d + 1) if B.deepest_blocked(w, t)]
        if hits:
            blocked += 1
            if any(h[3] == "sqrt" for h in hits):
                sqrt_kind += 1
    return total, blocked, sqrt_kind


def test_every_E_rooted_word_is_unblocked_at_depth_four() -> None:
    """Theorem 6.1 calls them easier; at the depth it means, the criterion agrees."""
    assert _blocked_stats("E", 4) == (8, 0, 0)
    assert _blocked_stats("O", 4)[:2] == (8, 2)


@pytest.mark.parametrize("d,e_blocked,o_blocked", [(5, 2, 4), (6, 4, 12), (7, 10, 24)])
def test_the_frequency_advantage_persists(d: int, e_blocked: int, o_blocked: int) -> None:
    assert _blocked_stats("E", d)[1] == e_blocked, d
    assert _blocked_stats("O", d)[1] == o_blocked, d


@pytest.mark.parametrize("d", [5, 6, 7])
def test_every_blocked_E_rooted_word_is_blocked_on_a_square_root(d: int) -> None:
    """Its first letter makes theta_1 = {n^{1/2}}, the species with no kernel here."""
    total, blocked, sqrt_kind = _blocked_stats("E", d)
    assert blocked == sqrt_kind > 0, (d, blocked, sqrt_kind)
    # and O-rooted words are not like that
    assert _blocked_stats("O", d)[2] < _blocked_stats("O", d)[1]


def test_the_first_blocked_E_rooted_word_also_fails_linearisation() -> None:
    d5 = B.deepest_blocked("EOOOE", 5)
    assert d5 == (1, Fraction(27, 16), Fraction(19, 16), "sqrt")
    assert B.composed_map("EOOOE", 5, 1) == Fraction(27, 8)
    assert not B.linearisation_safe("EOOOE", 5)


def test_paper_states_the_E_rooted_reading() -> None:
    text = io.open(PAPER, encoding="utf-8").read()
    assert "the starts this paper excludes" in text
    assert "easier to enter and harder to finish" in text
    assert r"\tfrac{27k}{16}n^{19/16}" in text


# --- the square-root species never occurs in proved territory ---


def _proved_words() -> list[str]:
    """Everything Paper B proves: all words of depth <= 4, plus Theorem 6.3's four."""
    from itertools import product
    out = ["".join(b) for d in (2, 3, 4) for b in product("EO", repeat=d)]
    return out + ["OOOEE", "OOOEO", "OOEOE", "OOEOO"]


def test_no_proved_word_has_a_square_root_blocked_defect() -> None:
    words = _proved_words()
    assert len(words) == 32
    for w in words:
        for t in range(3, len(w) + 1):
            d = B.deepest_blocked(w, t)
            assert not (d and d[3] == "sqrt"), (w, t, d)


def test_the_species_first_appears_one_depth_past_the_frontier() -> None:
    from itertools import product

    def first(root: str) -> tuple[int, list[str]]:
        for d in range(3, 8):
            hits = []
            for b in product("EO", repeat=d - 1):
                w = root + "".join(b)
                if any((x := B.deepest_blocked(w, t)) and x[3] == "sqrt"
                       for t in range(3, d + 1)):
                    hits.append(w)
            if hits:
                return d, sorted(hits)
        raise AssertionError(root)

    assert first("E") == (5, ["EOOOE", "EOOOO"])
    assert first("O") == (6, ["OOEOOE", "OOEOOO"])


def test_the_first_O_rooted_instance_is_OOEOOEEs_prefix() -> None:
    """What blocks OOEOOEE is the species' first appearance among O-rooted words."""
    assert "OOEOOEE"[:6] == "OOEOOE"
    d = B.deepest_blocked("OOEOOE", 6)
    assert d == (3, Fraction(9, 8), Fraction(45, 32), "sqrt")
    assert B.composed_map("OOEOOE", 6, 3) == Fraction(9, 4)
    assert not B.linearisation_safe("OOEOOE", 6)
    assert B.deepest_blocked("OOEOOEE", 6) == d


def test_paper_states_the_species_is_untouched() -> None:
    text = io.open(PAPER, encoding="utf-8").read()
    assert "untouched, not overlooked" in text
    assert "Thirty-two words, none." in text
    assert "the treatment stops before the species occurs" in text


# --- the level is unprecedented too, so both targets need something new ---


def test_every_blocked_defect_in_proved_territory_is_level_two() -> None:
    levels = set()
    for w in _proved_words():
        for t in range(3, len(w) + 1):
            d = B.deepest_blocked(w, t)
            if d:
                levels.add(d[0])
    assert levels == {2}


def test_the_first_level_one_3_2_blockage_is_at_depth_six() -> None:
    from itertools import product

    def scan(d: int) -> list[str]:
        out = []
        for b in product("EO", repeat=d):
            w = "".join(b)
            if any((x := B.deepest_blocked(w, t)) and x[0] == 1 and x[3] == "3/2"
                   for t in range(3, d + 1)):
                out.append(w)
        return sorted(out)

    assert scan(4) == [] and scan(5) == []
    assert scan(6) == ["OOOEOE", "OOOEOO", "OOOOEE", "OOOOEO"]
    for w in scan(6):
        assert B.deepest_blocked(w, 6)[1:3] == (Fraction(27, 32), Fraction(33, 32)), w
        assert B.composed_map(w, 6, 1) == Fraction(27, 16), w


def test_both_depth_seven_targets_need_something_unprecedented() -> None:
    """OOOEOEE a new level, OOEOOEE a new species; neither occurs in proved territory."""
    assert B.deepest_blocked("OOOEOEE", 6)[0] == 1          # level never proved
    assert B.deepest_blocked("OOEOOEE", 6)[3] == "sqrt"     # species never proved
    # but only one of them sits below the paper's own barrier
    assert B.linearisation_safe("OOOEOEE", 6)
    assert not B.linearisation_safe("OOEOOEE", 6)


def test_paper_tempers_the_one_theorem_reading() -> None:
    text = io.open(PAPER, encoding="utf-8").read()
    assert r"level \(1\) never occurs either" in text
    assert "should not be read as one routine theorem" in text
    assert "Both are new" in text


# --- the level-2 characterisation is the kernel's reach, not the depth's doing ---


def _blocked_profile_of(word: str):
    out = set()
    for t in range(3, len(word) + 1):
        d = B.deepest_blocked(word, t)
        if d:
            out.add((d[0], d[3]))
    return tuple(sorted(out))


def test_depths_four_and_five_sort_into_exactly_four_classes() -> None:
    from itertools import product
    proved = set(_proved_words())
    counts = {}
    for d in (4, 5):
        for b in product("EO", repeat=d):
            w = "".join(b)
            key = _blocked_profile_of(w)
            tot, pr = counts.get(key, (0, 0))
            counts[key] = (tot + 1, pr + (w in proved))
    assert counts[()] == (40, 16)
    assert counts[((2, "3/2"),)] == (4, 4)
    assert counts[((1, "sqrt"),)] == (2, 0)
    assert counts[((2, "3/2"), (3, "3/2"))] == (2, 0)
    assert len(counts) == 4


def test_among_blocked_words_proved_means_level_two_only() -> None:
    """Four words with that profile, all proved; four with any other, none proved."""
    from itertools import product
    proved = set(_proved_words())
    for d in (4, 5):
        for b in product("EO", repeat=d):
            w = "".join(b)
            prof = _blocked_profile_of(w)
            if not prof:
                continue
            assert (w in proved) == (prof == ((2, "3/2"),)), (w, prof)


def test_the_unproved_unblocked_depth_five_words_are_worth_nothing() -> None:
    """Corollary 6.4 attains the depth-five ceiling, so no further class can add density."""
    assert B.ceiling(5) == Fraction(7, 8)
    assert B.ceiling(5) - B.ceiling(4) == Fraction(1, 16)
    # depth six buys nothing either, so the 24 cannot be leveraged one step on
    assert B.ceiling(6) == B.ceiling(5)


def test_paper_states_the_four_class_sort() -> None:
    text = io.open(PAPER, encoding="utf-8").read()
    assert "Is the level-2 reading forced by the depth?" in text
    assert "it is the reach of the\nlevel-2 kernel" in text
    assert "declining costs nothing" in text


# --- counting blocked words without enumerating them ---


def _blocked_bruteforce(d: int) -> int:
    from itertools import product
    total = 0
    for bits in product("EO", repeat=d):
        e, o = [], 0
        for i, c in enumerate(bits, 1):
            o += c == "O"
            e.append(Fraction(3 ** o, 2 ** i))
        lo = None
        for t in range(3, d + 1):
            lo = e[t - 3] if lo is None else min(lo, e[t - 3])
            if e[t - 2] - lo > 1:
                total += 1
                break
    return total


@pytest.mark.parametrize("d", [3, 4, 5, 6, 7, 8, 9, 10, 11, 12])
def test_the_dp_agrees_with_enumeration(d: int) -> None:
    assert B.blocked_count(d)[0] == _blocked_bruteforce(d), d


def test_the_blocked_sequence() -> None:
    assert [B.blocked_count(d)[0] for d in range(3, 15)] == \
        [0, 2, 6, 16, 34, 82, 164, 368, 746, 1494, 3158, 6320]


def test_the_dp_reaches_depths_enumeration_cannot() -> None:
    for d, want, frac in ((20, 434976, 0.41483), (28, 116414536, 0.43368)):
        got, states = B.blocked_count(d)
        assert got == want, d
        assert abs(got / 2 ** d - frac) < 1e-5, d
        assert states < 1000, (d, states)          # against 2^d words


def test_blocking_couples_two_positions_and_contraction_does_not() -> None:
    """The contraction test reads (t, o_t) alone; the blocking test needs a running minimum."""
    # OOOE and OEOO share (t, o_t) = (4, 3), so contraction cannot tell them apart
    assert "OOOE".count("O") == "OEOO".count("O") == 3
    assert B.survives(4, 3)
    # but one is blocked and the other is not, because the paths differ
    assert B.deepest_blocked("OOOE", 4) is not None
    assert all(B.deepest_blocked("OEOO", t) is None for t in (3, 4))


def test_paper_states_why_the_two_counts_differ() -> None:
    text = io.open(PAPER, encoding="utf-8").read()
    assert "Why the two counts behave differently." in text
    assert "couples two positions of the path" in text
    assert r"0,2,6,16,34,82,164,368,\dots" in text


# --- Section 1's claims, and two of them are the frontier apparatus ---


def test_the_power_envelope_exponent_is_the_scale_exponent() -> None:
    """3^{#O(w)}/2^{|w|} is e_{|w|}."""
    for w in ("OOEOO", "OOOEOEE", "OOEOOEE", "OOOO", "OEE"):
        assert Fraction(3 ** w.count("O"), 2 ** len(w)) == B.iterate_exponents(w)[-1], w


def test_the_envelope_holds_on_real_orbits() -> None:
    """Flooring never raises an iterate above n^{e}."""
    from mpmath import mp, mpf, floor, power
    mp.dps = 60
    for n in range(1001, 1100, 2):
        it, w = n, ""
        for _ in range(6):
            w += "O" if it % 2 else "E"
            it = int(floor(power(mpf(it), mpf(3) / 2 if it % 2 else mpf(1) / 2)))
            e = Fraction(3 ** w.count("O"), 2 ** len(w))
            cap = power(mpf(n), mpf(e.numerator) / e.denominator)
            assert mpf(it) <= cap * (1 + mpf(10) ** -40), (n, w)


def test_the_leftover_eighth_is_the_three_named_pieces() -> None:
    """OOEOO, OOOEO and OOOO* are exactly the four depth-five survivors."""
    survivors = set(surviving_words(5))
    assert survivors == {"OOEOO", "OOOEO", "OOOOE", "OOOOO"}
    assert Fraction(len(survivors), 2 ** 5) == Fraction(1, 8)


def test_the_model_problems_hypothesis_is_the_drift_threshold() -> None:
    """A ~ n^c gives A' ~ n^{c-1}, so 1 << A' is exactly c > 1."""
    for c, blocked in ((Fraction(3, 16), False), (Fraction(9, 16), False),
                       (Fraction(33, 32), True), (Fraction(45, 32), True)):
        assert (c - 1 > 0) == blocked == (c > B.DRIFT_THRESHOLD), c
    # the instance the paper quotes is Conjecture 7.3's own weight
    assert B.defect_coefficient("OOOO", 5, 3) == (Fraction(3, 4), Fraction(27, 16))
    assert Fraction(27, 16) - 1 == Fraction(11, 16)


def test_paper_connects_both() -> None:
    text = io.open(PAPER, encoding="utf-8").read()
    assert "is the scale exponent of" in text
    assert "this section's drift threshold, written in the" in text
    assert "the blocked case with the words" in text


# --- the sign-critical composites as functions of the weight exponent ---


def test_the_closed_forms_return_every_printed_constant() -> None:
    """At alpha = 9/8 the forms are the paper's own rationals, corrected one included."""
    a = Fraction(3, 4)                                   # c(nu) = (3k/4) nu^{9/8}
    assert a * B.composite("5a", Fraction(9, 8)) == Fraction(729, 512)
    assert a * B.composite("E", Fraction(9, 8)) == Fraction(-243, 512)
    # the anchor 2c'G' + cG'' -- the corrected constant of the erratum
    assert a * Fraction(3, 4) * B.composite("anchor", Fraction(9, 8)) == Fraction(-27, 128)
    assert 9 * a * Fraction(3, 4) * B.composite("anchor", Fraction(9, 8)) == Fraction(-243, 128)
    # the three-term (cG_F)'' -- what the manuscript printed
    assert a * Fraction(3, 4) * B.composite("cG", Fraction(9, 8)) == Fraction(-135, 1024)
    assert 9 * a * Fraction(3, 4) * B.composite("cG", Fraction(9, 8)) == Fraction(-1215, 1024)
    # the printed two-way splits
    assert [a * x for x in B.composite_terms("5a", Fraction(9, 8))] \
        == [Fraction(945, 512), -Fraction(27, 64)]
    assert [a * x for x in B.composite_terms("E", Fraction(9, 8))] \
        == [Fraction(81, 512), -Fraction(81, 128)]


def test_the_anchor_is_the_three_term_form_less_c2_G() -> None:
    """(c(G-J))'' = (cG)'' - c''J_F, and c''G_F is the 81/1024 that separates them."""
    for num in range(17, 60):
        alpha = Fraction(num, 16)
        assert B.composite("cG", alpha) - B.composite("anchor", alpha) == alpha * (alpha - 1)
        assert B.composite("cG", alpha) == (alpha - Fraction(3, 4)) * (alpha - Fraction(7, 4))
    a = Fraction(3, 4)
    c2G = a * Fraction(3, 4) * Fraction(9, 8) * (Fraction(9, 8) - 1)
    assert c2G == Fraction(81, 1024)
    assert Fraction(-135, 1024) - c2G == Fraction(-216, 1024) == Fraction(-27, 128)


def test_the_zeros_separate_the_two_objects() -> None:
    """The anchor is linear with the single zero 7/8; (cG)'' is the quadratic with 3/4 and 7/4."""
    assert B.composite_roots("anchor") == [0.875]
    assert B.composite("anchor", Fraction(7, 8)) == 0
    assert B.composite_roots("cG") == [0.75, 1.75]
    for name in ("5a", "E"):
        for r in B.composite_roots(name):
            near = Fraction(r).limit_denominator(10 ** 7)
            assert B.composite(name, near) != 0
            assert abs(float(B.composite(name, near))) < 1e-5
    assert abs(B.composite_roots("5a")[1] - (10 ** 0.5 - 1) / 4) < 1e-12
    assert abs(B.composite_roots("E")[1] - (2 + 13 ** 0.5) / 4) < 1e-12
    # every blocked exponent exceeds 1, so no zero is reachable
    assert min(B.composite_screen(9)) is not None
    assert all(g > 1 for d in range(4, 10) for w in B.surviving_words(d) if len(w) == d
               for t in range(2, d + 1) for _s, g, _sp in B.blocked_profile(w, t))


def test_the_level_one_exponent_stays_the_same_order() -> None:
    """33/32 does not vanish on any composite: better on Step E, half again worse on the anchor."""
    a = Fraction(27, 32)                                 # c(nu) = (27k/32) nu^{33/32}
    assert a * B.composite("5a", Fraction(33, 32)) == Fraction(84321, 65536)
    assert a * B.composite("E", Fraction(33, 32)) == Fraction(-43983, 65536)
    assert 9 * a * Fraction(3, 4) * B.composite("anchor", Fraction(33, 32)) == Fraction(-10935, 8192)
    proved = [B.cancellation_factor(n, Fraction(9, 8)) for n in B.COMPOSITES]
    level1 = [B.cancellation_factor(n, Fraction(33, 32)) for n in B.COMPOSITES]
    assert [round(float(x), 2) for x in proved] == [1.59, 1.67, 8.00]
    assert [round(float(x), 2) for x in level1] == [1.74, 1.12, 12.20]
    assert level1[1] < proved[1]                          # Step E: 1.12 against 1.67
    assert max(level1) < 1.6 * max(proved)                # same order, not the same number


def test_no_frontier_exponent_is_composite_degenerate() -> None:
    """222 blocked exponents to depth 13, none a zero, all inside the errors the proofs carry."""
    worst = B.composite_screen(13)
    assert worst["5a"][0] == Fraction(4131, 4096)
    assert worst["E"][0] == Fraction(45, 32)             # OOEOOEE's blocked exponent
    assert worst["anchor"][0] == Fraction(4131, 4096)
    assert round(float(worst["5a"][1]), 2) == 1.78
    assert float(worst["E"][1]) == 129.0
    assert round(float(worst["anchor"][1]), 2) == 14.10
    p0 = 8.9e13
    assert float(worst["5a"][1]) < p0 ** 0.25
    assert float(worst["E"][1]) < p0 ** 0.25 < 3072
    assert float(worst["anchor"][1]) < p0 ** (15 / 16)


def test_the_hard_word_is_the_one_with_the_worst_composite() -> None:
    """45/32 is OOEOOEE's, and its Step E factor is 77 times the proved exponent's."""
    assert (3, Fraction(45, 32), "sqrt") in B.blocked_profile("OOEOOEE", 6)
    ratio = B.cancellation_factor("E", Fraction(45, 32)) / B.cancellation_factor("E", Fraction(9, 8))
    assert 76 < float(ratio) < 78
    worst = {a: max(B.cancellation_factor(n, a) for n in B.COMPOSITES)
             for a in (Fraction(9, 8), Fraction(33, 32), Fraction(27, 16), Fraction(45, 32))}
    order = sorted(worst, key=lambda a: worst[a])
    assert order == [Fraction(27, 16), Fraction(9, 8), Fraction(33, 32), Fraction(45, 32)]
    # the first three are within a factor of four; the fourth is an order of magnitude out
    assert float(worst[order[2]] / worst[order[0]]) < 4
    assert float(worst[order[3]] / worst[order[2]]) > 10


def test_paper_records_the_composite_screen() -> None:
    text = io.open(PAPER, encoding="utf-8").read()
    assert "recomputing the composites" in text
    assert "cancellation\nfactor" in text
    assert "84321" in text and "43983" in text and "10935" in text
    assert "1.4014" in text and "0.5406" in text
    assert "the only one of them that\nnever binds" in text
    assert "not a composite the paper has ever formed" in text
    # Step E's zero-offset is now derived, and its first half has no alpha-form
    assert "is absent from the three for a" in text
    assert "not a function of the weight" in text


# --- what truncation the carry term can afford ---


def test_the_vaaler_budget_reaches_the_requirement() -> None:
    """J = P^{5/22} and a saving of 5/22, against the 1/48 the differenced sum needs."""
    r = B.vaaler_truncation_budget()
    assert r["J_exponent"] == Fraction(5, 22)
    assert r["saving"] == Fraction(5, 22)
    assert r["required"] == Fraction(1, 48)
    assert r["room"] == Fraction(120, 11)
    assert r["reaches_the_requirement"]
    # the classical pair alone already clears it eight times over
    assert r["classical_pair_saving"] == Fraction(1, 6)
    assert r["classical_pair_saving"] / r["required"] == 8


def test_the_budget_formula_is_the_balance() -> None:
    """delta = (1 - k/2 - l)/(k+1) is P/J against J^k P^{k/2+l}, and the trivial pair gives none."""
    for kap, ell in B.van_der_corput_pairs(6):
        num = 1 - kap / 2 - ell
        if num <= 0:
            continue
        d = num / (kap + 1)
        # at J = P^d the two sides of the balance agree
        assert 1 - d == d * kap + kap / 2 + ell
    assert 1 - Fraction(0) / 2 - Fraction(1) == 0          # trivial pair: no saving, as it must


def test_both_unpriced_terms_are_one_family() -> None:
    """(Delta_h c) theta_1 shifts j by at most k h P^{1/32}, which J dominates."""
    r = B.vaaler_truncation_budget()
    assert r["shift_from_delta_h_c"] == Fraction(11, 96) == Fraction(1, 24) * 2 + Fraction(1, 32)
    assert r["J_dominates_the_shift"]
    assert r["J_exponent"] - r["shift_from_delta_h_c"] == Fraction(119, 1056)


def test_the_shifted_window_works_on_beta_where_it_failed_on_c() -> None:
    """beta drifts at exponent -1/2, far below the threshold that 33/32 sat above."""
    r = B.vaaler_truncation_budget()
    assert r["window_reach"] == Fraction(71, 264) < Fraction(1, 2)
    assert r["window_holds_integers"]
    assert r["window_margin"] == Fraction(61, 264)
    # the contrast: c has coefficient exponent 33/32, above the drift threshold; beta has -1/2
    assert Fraction(33, 32) > B.DRIFT_THRESHOLD > Fraction(-1, 2)


def test_paper_records_the_truncation_and_stops_where_it_stops() -> None:
    text = io.open(PAPER, encoding="utf-8").read()
    assert "What the truncation costs" in text
    assert "J=P^{5/22}" in text
    assert "10.9" in text and "times over" in text
    assert "it was being asked of the wrong quantity" in text
    assert "the two-monomial estimate itself" in text


# --- the carry needs no window ---


def test_the_carry_is_exact_in_integers() -> None:
    """kappa = floor(X(n+h)) - floor(X(n)) - floor(Delta_h X), with no floating point."""
    r = B.carry_sawtooth_identity()
    assert r["checked"] == 10000
    assert r["exact_integer_arithmetic"]
    assert not r["windows_needed"]
    # a live branch, not a degenerate one
    assert 0.4 < r["kappa_one_fraction"] < 0.6, r["kappa_one_fraction"]
    for n, h in ((10**6 + 1, 1), (10**6 + 3, 5), (2 * 10**6 - 1, 8)):
        assert B.carry_exact(n, h) in (0, 1)


def test_the_carry_matches_the_fractional_part_reading() -> None:
    """The integer route agrees with {X(n)} + {Delta_h X} >= 1 at high precision."""
    from mpmath import mp

    mp.dps = 50
    half = mp.mpf(3) / 2
    bad = 0
    for n in range(10**6 + 1, 10**6 + 400, 2):
        for h in (1, 3, 7):
            X0, X1 = mp.power(mp.mpf(n), half), mp.power(mp.mpf(n + h), half)
            th = X0 - mp.floor(X0)
            D = X1 - X0
            fd = D - mp.floor(D)
            bad += (1 if th + fd >= 1 else 0) != B.carry_exact(n, h)
    assert bad == 0, bad


def test_a_per_window_assembly_would_return_nothing() -> None:
    """Windows of length P^{1/2}/(Jh), count J h P^{1/2}: the product is P."""
    w = B.window_assembly_is_trivial()
    assert w["window_length"] == Fraction(61, 264)
    assert w["window_count"] == Fraction(203, 264)
    assert w["product"] == 1
    assert w["trivial_assembly_saving"] == 0
    # f' is frozen across a window, so no exponent pair beats the trivial bound there
    assert w["f_prime_drift_across_a_window"] == Fraction(-1, 24) < 0
    assert w["frozen_across_a_window"]


def test_the_sawtooth_arguments_are_smooth() -> None:
    """Three smooth arguments over the whole range, so the Vaaler expansion needs no window."""
    r = B.carry_sawtooth_identity()
    assert r["arguments_are_smooth"] == ("n^{3/2}", "(n+h)^{3/2}", "(n+h)^{3/2} - n^{3/2}")
    # the third family's amplitude is dominated by c(n+h), so it constrains nothing
    third = Fraction(5, 22) + Fraction(1, 24) - Fraction(1, 2)      # j h P^{-1/2} at the caps
    assert third == Fraction(-61, 264) < Fraction(1, 32)
    assert B.vaaler_truncation_budget()["J_exponent"] == Fraction(5, 22)


def test_paper_records_that_the_window_is_avoidable() -> None:
    text = io.open(PAPER, encoding="utf-8").read()
    assert "And it is not needed" in text
    assert "a per-window assembly returns nothing at all" in text
    assert "two lines of algebra" in text
    assert "50.3" in text
    assert "the two-monomial estimate itself" in text


# --- the leftover two-monomial question is not this one ---


def test_this_requirement_is_inside_the_hull() -> None:
    """delta >= 1/48 is 25p + 48q <= 47, against a hull minimum of 34.5."""
    r = B.two_monomial_requirement()
    assert r["here_line"] == 47
    assert r["here_hull_min"] == Fraction(69, 2)
    assert r["here_is_inside_the_hull"]
    assert abs(float(r["here_margin"]) - 0.266) < 0.001
    # the rearrangement itself: delta = (1 - p/2 - q)/(p+1) >= 1/48
    for p, q in ((Fraction(1, 6), Fraction(2, 3)), (Fraction(13, 84), Fraction(55, 84))):
        delta = (1 - p / 2 - q) / (p + 1)
        assert (delta >= Fraction(1, 48)) == (25 * p + 48 * q <= 47)


def test_the_notes_requirement_is_below_its_hull() -> None:
    """(5/4)p + q < 2/3 against a hull minimum of 0.8606: a subconvexity ask."""
    r = B.two_monomial_requirement()
    assert r["note_line"] == Fraction(2, 3)
    assert r["note_hull_min"] == Fraction(1673, 1944)
    assert not r["note_is_inside_the_hull"]
    assert r["note_literature_min"] == Fraction(95, 112)
    assert Fraction(95, 112) > Fraction(2, 3)          # even with Huxley and Bourgain
    for d in r["named"].values():
        assert not d["clears_note"] or d["phi"] < Fraction(2, 3)
    assert not r["named"]["Bourgain"]["clears_note"]
    assert r["named"]["Bourgain"]["clears_here"]


def test_only_the_trivial_neighbourhood_fails_here() -> None:
    """Three of fifty-six fail, and they are the trivial pair and what crawls back to it."""
    r = B.two_monomial_requirement()
    assert len(r["failing_pairs"]) == 3
    assert (Fraction(0), Fraction(1)) in r["failing_pairs"]
    assert r["failures_are_the_trivial_neighbourhood"]
    assert all(q >= Fraction(251, 255) for _p, q in r["failing_pairs"])
    assert r["named"]["trivial"]["psi"] == 48 and not r["named"]["trivial"]["clears_here"]
    for nm in ("van der Corput", "Weyl", "Bourgain"):
        assert r["named"][nm]["clears_here"], nm


def test_domination_is_not_what_separates_them() -> None:
    """Both problems are led by one monomial; that resemblance is not the difference."""
    d = B.two_monomial_domination()
    assert d["here_worst_corner"] == Fraction(41, 96) > 0
    assert d["here_top_of_range"] == Fraction(691, 1056)
    assert d["note_ratio"] == Fraction(71, 60) > 0
    assert d["here_dominated"] and d["note_dominated"]
    # the worst corner is j = 1 with k at its cap
    assert Fraction(3, 2) - Fraction(1, 24) - Fraction(33, 32) == Fraction(41, 96)


def test_paper_separates_the_two_questions() -> None:
    text = io.open(PAPER, encoding="utf-8").read()
    assert "it is a smaller thing than the leftover it resembles" in text
    assert "25p+48q" in text
    assert "subconvexity result" in text
    assert "What separates them is" in text
    assert "only where the target sits relative to the hull" in text
    assert "the missing ingredient is not a new exponent pair" in text


# --- the drift threshold is graded, not binary ---


def test_differencing_lowers_the_exponent_by_one() -> None:
    """Delta_h c ~ alpha k h n^{alpha - 1}, so the drift depth is ceil(alpha) - 1."""
    for alpha, want in ((Fraction(33, 32), 1), (Fraction(9, 8), 1), (Fraction(45, 32), 1),
                        (Fraction(27, 16), 1), (Fraction(15, 8), 1), (Fraction(9, 4), 2),
                        (Fraction(525297, 4096), 128)):
        assert B.drift_depth(alpha) == want, (alpha, B.drift_depth(alpha))
    # an integer exponent is a boundary case: alpha = 2 needs one, not two
    assert B.drift_depth(Fraction(2)) == 1
    # and below the threshold nothing is needed
    assert B.drift_depth(Fraction(1, 32)) == 0


def test_the_cost_is_the_max_of_the_two_counts() -> None:
    """Each differencing peels a level off one branch and an exponent off the other."""
    assert B.differencing_cost(2, Fraction(9, 8)) == 2        # level binds
    assert B.differencing_cost(1, Fraction(33, 32)) == 1      # they tie
    assert B.differencing_cost(3, Fraction(45, 32)) == 3      # level binds
    assert B.differencing_cost(1, Fraction(9, 4)) == 2        # drift binds
    for lev in (1, 2, 3):
        for alpha in (Fraction(33, 32), Fraction(9, 4), Fraction(17, 2)):
            assert B.differencing_cost(lev, alpha) == max(lev, B.drift_depth(alpha))


def test_the_grading_reproduces_the_papers_own_constant() -> None:
    """1/96 is Lemma 5.2(ii)'s 1/24 halved twice, and twice is what the grading says."""
    d = B.differencing_cost(2, Fraction(9, 8))
    assert d == 2
    assert Fraction(1, 24) / 2 ** d == Fraction(1, 96)
    assert B.drift_grading(9)["reproduces_one_over_96"]
    # the level-1 kernel spends one halving, not two
    assert B.differencing_cost(1, Fraction(33, 32)) == 1
    assert Fraction(1, 24) / 2 ** 1 == Fraction(1, 48)        # the requirement met earlier


def test_the_grading_separates_the_frontier() -> None:
    """26663 sites, d from 1 to 128, and neither count dominates the other."""
    r = B.drift_grading(13)
    assert r["sites"] == 26663
    assert r["distinct_exponents"] == 222
    assert r["max_depth"] == 128
    assert r["distribution"][1] == 1919
    cum = sum(v for k, v in r["distribution"].items() if k <= 3)
    assert 0.30 < cum / r["sites"] < 0.32
    b = r["binds"]
    assert b["level"] + b["drift"] + b["equal"] == r["sites"]
    for key in ("level", "drift"):
        assert 0.35 < b[key] / r["sites"] < 0.50, key


def test_only_the_level_one_target_ties() -> None:
    """The level binds for three of the four named targets; OOOEOEE is where they meet."""
    named = B.drift_grading(9)["named"]
    assert named["OOOEOEE letter 6"]["level"] == named["OOOEOEE letter 6"]["drift_depth"] == 1
    for nm in ("Theorem 5.3", "OOEOOEE letter 6", "Conjecture 7.3"):
        assert named[nm]["level"] > named[nm]["drift_depth"], nm
    assert named["Theorem 5.3"]["factor"] == Fraction(1, 4)
    assert named["OOOEOEE letter 6"]["factor"] == Fraction(1, 2)
    assert named["Conjecture 7.3"]["factor"] == Fraction(1, 8)


def test_paper_records_the_grading() -> None:
    text = io.open(PAPER, encoding="utf-8").read()
    assert "The drift threshold is graded" in text
    assert "26" + chr(92) + ",663" in text
    bs = chr(92)
    assert "d=" + bs + "max" + bs + "bigl(" + bs + "ell," in text
    assert bs + "lceil" + bs + "alpha" + bs + "rceil-1" in text
    assert "read off the grading" in text
    assert "target where the two counts coincide" in text


# --- the grading's domain: branch runs, and what level three forces ---


def test_every_contractor_begins_OO() -> None:
    """Survival at t = 2 needs 3^{o_2} >= 4, and 3 < 4, so o_2 = 2."""
    assert B.every_contractor_begins_oo(11)
    assert 3 ** 1 < 2 ** 2                       # o_2 = 1 does not survive
    assert 3 ** 2 >= 2 ** 2
    for d in (2, 5, 9):
        for w in B.surviving_words(d):
            if len(w) == d:
                assert w.startswith("OO"), w
                assert B.iterate_exponents(w)[1] == Fraction(9, 4)


def test_level_three_has_no_runs_anywhere() -> None:
    """Not a fact about OOOO*: a theorem about the level, forced by the OO prefix."""
    r = B.branch_runs_by_level(13)
    assert r["level_three_is_runless"]
    assert r["levels"][3]["runs"] == 0
    assert r["levels"][3]["no_runs"] == 3910
    assert r["levels"][3]["bases"] == [Fraction(9, 4)]
    assert not B.has_branch_runs(Fraction(9, 4))


def test_runs_reappear_above_level_three() -> None:
    """The 9/4 reading would predict none; an early even letter brings the base back under 2."""
    r = B.branch_runs_by_level(13)
    assert r["levels_with_runs"] == [1, 2, 4, 5, 7, 8, 10]
    assert r["levels_without"] == [3, 6, 9, 11]
    # level four: 9/8 for OOE*, 27/8 for OOO*
    assert r["levels"][4]["bases"] == [Fraction(9, 8), Fraction(27, 8)]
    assert B.has_branch_runs(Fraction(9, 8)) and not B.has_branch_runs(Fraction(27, 8))
    assert r["levels"][4]["runs"] == 746
    assert r["sites"] == 26663
    assert abs(r["fraction_with_runs"] - 0.512) < 0.002


def test_the_domain_makes_the_primary_split() -> None:
    """Branch runs separate the two tractable targets from the two hard ones."""
    have = {"Theorem 5.3": ("OOOE", 4), "OOOEOEE": ("OOOEOEE", 6)}
    lack = {"OOEOOEE": ("OOEOOEE", 6), "Conjecture 7.3": ("OOOOE", 5)}
    for nm, (w, t) in have.items():
        assert B.has_branch_runs(B.branch_base(w, t)), nm
    for nm, (w, t) in lack.items():
        assert not B.has_branch_runs(B.branch_base(w, t)), nm
    # and inside the second pair the grading is blind: both cost 2^-3
    for w, t in lack.values():
        s, _c, alpha, _sp = B.deepest_blocked(w, t)
        assert B.differencing_cost(s, alpha) == 3
    # what separates them is species and the composite factor, both isolating OOEOOEE
    assert B.deepest_blocked("OOEOOEE", 6)[3] == "sqrt"
    assert B.deepest_blocked("OOOOE", 5)[3] == "3/2"
    assert B.cancellation_factor("E", Fraction(45, 32)) > 100
    assert B.cancellation_factor("E", Fraction(27, 16)) < 5


def test_paper_records_the_domain_and_the_level_three_theorem() -> None:
    text = io.open(PAPER, encoding="utf-8").read()
    assert "The grading has a domain" in text
    assert "it is the grading's precondition" in text
    assert "every contractor begins" in text
    assert "a theorem about level three" in text
    assert "Levels beyond it are not uniformly barred" in text


# --- which defects the 9/4 stop should screen ---


def test_one_contractor_is_barred_by_the_stop_alone() -> None:
    """OOOEOOEE at depth eight, and it misses by 3/64."""
    r = B.stop_reading_gap()
    assert [w for w, _e in r["stop_alone"]] == ["OOOEOOEE"]
    assert r["stop_alone"][0][1] == Fraction(3, 64)
    assert Fraction(147, 64) - Fraction(9, 4) == Fraction(3, 64)
    # and the offending defect is theta_1, the shallowest, not the one the kernel rides
    prof = B.blocked_profile("OOOEOOEE", 7)
    over = [(s, g) for s, g, _sp in prof if g > B.STOP_THRESHOLD]
    assert over == [(1, Fraction(147, 64))]
    assert B.deepest_blocked("OOOEOOEE", 7)[0] == 5
    assert B.deepest_blocked("OOOEOOEE", 7)[2] == Fraction(81, 64) < B.STOP_THRESHOLD


def test_it_asks_for_exactly_the_two_kernels_already_named() -> None:
    """Letter 4 at level 2 on 9/8, letter 6 at level 1 on 33/32 -- and nothing else new."""
    for t, level, alpha in ((4, 2, Fraction(9, 8)), (6, 1, Fraction(33, 32)),
                            (7, 5, Fraction(81, 64))):
        deep = B.deepest_blocked("OOOEOOEE", t)
        assert deep[0] == level and deep[2] == alpha, (t, deep)
    # letter 7 is fine on both of the other axes
    assert B.has_branch_runs(B.branch_base("OOOEOOEE", 7))
    assert B.linearisation_safe("OOOEOOEE", 7)
    # the same two kernels the printed screen's survivors ask for
    assert B.unobstructed("OOOEOEE") == [(4, 2), (6, 1)]


def test_the_two_readings_differ_by_one_over_256() -> None:
    """227/256 as printed, 57/64 if the stop is tested on the deepest defect only."""
    r = B.stop_reading_gap()
    assert r["printed_ceiling"] == Fraction(227, 256)
    assert r["deepest_only_ceiling"] == Fraction(57, 64) == Fraction(228, 256)
    assert r["gap"] == Fraction(1, 256)
    assert B.unobstructed("OOOEOOEE") is None
    assert B.unobstructed_deepest_only("OOOEOOEE") is not None
    # every other word is unmoved by the reading
    for d, row in zip((7, 8, 10, 12, 13), r["rows"]):
        extra = set(row["deepest_only"]) - set(row["printed"])
        assert extra == ({"OOOEOOEE"} if d == 8 else set()), (d, extra)


def test_the_paper_applies_the_stop_to_shallow_defects_too() -> None:
    """The OOOO* row lists 57/16 and 45/16 while its deepest sits at 27/16."""
    deep = B.deepest_blocked("OOOOE", 5)
    assert deep[2] == Fraction(27, 16) < B.STOP_THRESHOLD
    over = B.beyond_methods("OOOOE", 5)
    assert sorted(over) == [Fraction(45, 16), Fraction(57, 16)]
    # so the printed screen bars it on defects the kernel does not ride
    assert B.unobstructed("OOOOEEE") is None


def test_paper_records_the_question_without_settling_it() -> None:
    text = io.open(PAPER, encoding="utf-8").read()
    assert "An open question about which defects" in text
    assert "Both readings cannot" in text
    assert "This paper does not settle it" in text
    assert "The screen is left as printed" in text
    assert "147" in text and "3/64" in text


def _theta(q: float) -> float:
    """Optimised Chernoff base for ``Pr(B_n >= q n)`` at ``p = 1/2``: ``exp(-KL(q||1/2))``."""
    return q ** (-q) * (1 - q) ** (q - 1) / 2


def test_theorem_six_ones_threshold_is_slack_and_the_slack_is_not_needed() -> None:
    """Theorem 6.1 picks q = (p+1/2)/2 and thereby throws away 75% of its own exponent.

    The proof needs a q with 1/2 < q < p satisfying ``p d - 1 >= q (d-1)`` -- the -1 is the
    leading O, which is spent before the binomial starts.  q = p is genuinely blocked: the
    condition reduces to p >= 1.  But the published repair, halving the distance to 1/2, is
    far more than the -1 costs.  The exact break-even is

        q_d = p - (1-p)/(d-1),

    at which the threshold step holds with EQUALITY, so q_d is the largest admissible choice
    at depth d rather than one of many.  Its only constraint is q_d > 1/2, which holds from
    d >= 4; the theorem therefore needs no "sufficiently large d" clause at all.

    Not a new theorem: the conclusion (density one) follows from any theta < 1 and is
    untouched.  What moves is the rate, and it moves by a factor that grows without bound.
    """
    p = BETA_
    for d in (4, 10, 100, 10 ** 6):
        q_d = p - (1 - p) / (d - 1)
        assert math.isclose(q_d * (d - 1), p * d - 1, rel_tol=1e-15), d

    # q = p itself is blocked, and blocked only by the -1
    assert p * 10 - 1 < p * (10 - 1)
    assert p < 1.0

    # q_d > 1/2 exactly from d = 4
    assert p - (1 - p) / (3 - 1) <= 0.5
    assert p - (1 - p) / (4 - 1) > 0.5
    assert math.isclose(1 + (1 - p) / (p - 0.5), 3.818842, rel_tol=1e-6)


def test_the_published_threshold_captures_a_quarter_of_the_available_exponent() -> None:
    """theta(p) is the module's sharp rate exactly, so the sharp rate was always in reach.

    ``chernoff_rate`` minimises ``E[e^(theta X)]`` for the step X in {log(3/2), -log 2}; the
    walk stays nonnegative exactly when ``o log 3 >= d log 2``, i.e. when at least ``p d`` of
    the letters are odd.  So the Cramer rate of the walk and the binomial large-deviation rate
    at threshold p are the same number, and Theorem 6.1's own inequality reaches it.

    Paper B instead reports -log theta((p+1/2)/2) = 0.008596 per letter against the available
    0.034688: 24.8%.
    """
    p = BETA_
    rho = B.chernoff_rate()
    assert math.isclose(_theta(p), rho, rel_tol=1e-14), (_theta(p), rho)

    sharp = -math.log(rho)
    published = -math.log(_theta((p + 0.5) / 2))
    assert math.isclose(sharp, 0.034688185, rel_tol=1e-8), sharp
    assert math.isclose(published, 0.0085959587, rel_tol=1e-8), published
    assert math.isclose(published / sharp, 0.2478, rel_tol=1e-3), published / sharp


def test_the_sharpened_bound_has_the_closed_form_p_times_rho_to_the_d() -> None:
    r"""At the break-even q_d the bound is not just sharp in rate -- its constant is p.

    Writing KL(q) = -log theta(q), so KL'(q) = log(q/(1-q)):

        (1/2) theta(q_d)^(d-1) / rho^d
            -> (1/2) exp(KL(p)) exp((1-p) KL'(p))
             = p^p (1-p)^(1-p) . (p/(1-p))^(1-p)
             = p^p p^(1-p) = p.

    Every factor of (1-p) cancels.  The sharpened Theorem 6.1 therefore reads

        dens(N \ C_d) <= p rho^d (1 + O(1/d)),    rho = 0.9659065532,

    with both constants explicit and no unspecified "some fixed t > 0".
    """
    p = BETA_
    rho = B.chernoff_rate()

    KL_p = -math.log(_theta(p))
    KL_prime_p = math.log(p / (1 - p))
    assert math.isclose(0.5 * math.exp(KL_p) * math.exp((1 - p) * KL_prime_p), p, rel_tol=1e-14)

    prev = None
    for d in (10 ** 3, 10 ** 4, 10 ** 5):
        v = math.exp(math.log(0.5) + (d - 1) * math.log(_theta(p - (1 - p) / (d - 1)))
                     - d * math.log(rho))
        assert v < p and math.isclose(v, p, rel_tol=4.0 / d), (d, v)
        if prev is not None:                       # the 1/d error term really is 1/d
            assert math.isclose((p - prev) / (p - v), 10.0, rel_tol=0.05), (prev, v)
        prev = v


def test_what_remains_after_sharpening_is_exactly_the_meander_polynomial() -> None:
    """The sharpened bound overshoots the truth by d^(3/2) and by the meander constant.

    N_d/2^d ~ C rho^d d^(-3/2) with C = kappa G(1) = 10.90 (J-paper-b-meander-constant...),
    and the sharpened bound is p rho^d, so the ratio is (C/p) d^(-3/2) inverted:

        (p rho^d) / (N_d/2^d) ~ (p/C) d^(3/2),   truth/(p rho^d) . d^(3/2) ~ psi/p.

    C is NOT a constant -- see
    test_the_meander_prefactor_is_not_a_constant_but_a_function_of_the_offset -- so the
    three numbers below are samples of psi/p over about 16.4..17.4, not approaches to a
    limit, and their wobble is the oscillation rather than measurement noise. The mean
    still recovers the recorded 10.90/p, which is what makes this an independent route to
    that value: nothing here uses the ladder-height transform, only the exact DP count and
    the sharpened Chernoff bound.  The published
    midpoint version by contrast overshoots by an exponentially growing factor -- 1.2e6 at
    d = 320 and 6.9e17 at d = 1280 -- so the gap it leaves is not a polynomial at all.
    """
    p = BETA_
    rho = B.chernoff_rate()

    ratios = []
    for d in (640, 1280, 2560):
        truth = B.non_contracting(d) / 2 ** d
        ratios.append(truth / (p * rho ** d) * d ** 1.5)
    assert all(15.0 < r < 18.5 for r in ratios), ratios
    assert math.isclose(sum(ratios) / len(ratios), 10.90 / p, rel_tol=0.08), ratios

    # and the published choice leaves an exponential gap, not a polynomial one
    mid = _theta((BETA_ + 0.5) / 2)
    gaps = [0.5 * mid ** (d - 1) / (B.non_contracting(d) / 2 ** d) for d in (320, 1280)]
    assert gaps[0] > 1e6 and gaps[1] > 1e17, gaps
    slope = math.log(gaps[1] / gaps[0]) / math.log(1280 / 320)
    assert slope > 15.0, slope                     # a polynomial gap would have slope O(1)


def test_the_depth_dependent_theta_is_still_uniformly_below_one() -> None:
    """Sharpening makes theta depend on d, so the proof needs a uniform bound.

    q_d = p - (1-p)/(d-1) increases in d and theta decreases on (1/2, 1), so theta_d
    decreases and theta_d <= theta_4 < 1 for every d >= 4.  theta_4 is 0.99987, barely
    below one -- the bound carries almost no content at depth 4 and earns it back only
    as d grows, which is the honest reading and is why the paper states the uniform
    bound rather than leaning on any single depth.
    """
    p = BETA_
    q = [p - (1 - p) / (d - 1) for d in range(4, 200)]
    assert all(a < b for a, b in zip(q, q[1:])), "q_d must increase"
    th = [_theta(x) for x in q]
    assert all(a > b for a, b in zip(th, th[1:])), "theta_d must decrease"
    assert th[0] < 1.0 and math.isclose(th[0], 0.99987, rel_tol=1e-4), th[0]
    assert all(x <= th[0] for x in th)

    # and the bound really does go to zero despite theta_d -> theta(p) from above
    assert 0.5 * th[0] ** 3 < 0.5
    rho = B.chernoff_rate()
    assert all(_theta(p - (1 - p) / (d - 1)) > rho for d in (10, 100, 1000))


def test_sharpening_theorem_six_one_does_not_reopen_the_near_closure_door() -> None:
    """A 4x better exponent does not make cycle candidates rare. Checked, not assumed.

    J-theorem-six-one-threshold-is-slack improved Theorem 6.1's bound on the DENSITY of
    non-contracting words by orders of magnitude.  The obvious hope is that this helps
    the cycle side, where J-near-closure-costs-nothing-in-word-count found that near-
    closing words are a flat ~8% of all non-contracting words at every depth.  It does
    not, and the reason is that the density was never the obstruction.

    The truth, untouched by any sharpening of an upper bound, is

        N_d ~ C (2 rho)^d d^(-3/2),   2 rho = 1.9318 > 1,

    so the ABSOLUTE number of non-contracting words grows exponentially, and ~8% of
    that is still exponential.  A counting argument cannot bound a set that grows.
    Baker / Rhin keeps doing all the work on the cycle side.
    """
    rho = B.chernoff_rate()
    assert 2 * rho > 1.0
    assert math.isclose(2 * rho, 1.931813106, rel_tol=1e-9), 2 * rho

    # N_d / ((2 rho)^d d^-1.5) -- computed in logs; the exact counts exceed float range
    seen = []
    for d in (200, 400, 800, 1600):
        log_N = math.log(B.non_contracting(d))
        seen.append(math.exp(log_N - d * math.log(2 * rho) + 1.5 * math.log(d)))
    assert all(a < b for a, b in zip(seen, seen[1:])), seen      # rising toward the constant
    assert math.isclose(seen[0], 8.919, rel_tol=2e-3), seen
    assert math.isclose(seen[-1], 10.757, rel_tol=2e-3), seen
    # meander_constant's c_d oscillates in 10.566..11.063, so this is a range not a limit
    assert 8.5 < seen[-1] < 11.1

    # the bound moved a great deal; what it bounds did not
    p = BETA_
    mid = 0.5 * _theta((p + 0.5) / 2) ** 799
    sharp = p * rho ** 800
    truth = math.exp(math.log(B.non_contracting(800)) - 800 * math.log(2.0))
    assert mid > sharp > truth, (mid, sharp, truth)
    assert mid / sharp > 1e8, mid / sharp          # sharpening gained 9 orders here
    assert sharp / truth < 1e4                     # and lands within 4 of the truth

    # yet the absolute count at that same depth is astronomically large
    assert math.log10(B.non_contracting(800)) > 225.0


def test_the_meander_prefactor_is_not_a_constant_but_a_function_of_the_offset() -> None:
    """N_d/2^d ~ C rho^d d^(-3/2) is FALSE: C is almost periodic, not constant.

    In the o coordinate the event is o_t >= t*BETA for all t <= d -- a simple walk on the
    integers against a line of IRRATIONAL slope.  The step distribution is non-lattice
    (log(3/2)/log2 is irrational), but at each fixed d the endpoint
    S_d = o log3 - d log2 lies on a lattice of spacing log3 whose offset -d log2 mod log3
    equidistributes.  The barrier sits at 0, so what the asymptotic sees is the gap from
    the barrier to the lowest available state, 1 - frac(d*BETA), and the prefactor is a
    function of that, not a number.

    Measured on the exact profile: binning c_d = (N_d/2^d)/(rho^d d^(-3/2)) by
    frac(d*BETA) collapses it -- within-bin scatter 0.065 against an across-bin range
    0.628, a 9.7x signal -- and the SHAPE is identical across disjoint depth windows
    (per-bin differences have sd 0.002) while only the LEVEL drifts, by +0.287, +0.124,
    +0.054 as the window doubles.  That drift is the 1+o(1); the shape is psi.

    The sign is the mechanism's, not a fit: larger frac(d*BETA) means a smaller gap above
    the barrier, hence more survivors, hence larger c.  psi rises from 10.37 at offset
    0.05 to 11.00 at 0.95.

    Consequences.  The previously recorded constant 10.90 is one sample of psi, and the
    recorded band 10.566..11.063 is psi's range -- explained rather than noted.  The
    d^(-3/2) exponent is unaffected.
    """
    import statistics

    rho = B.chernoff_rate()
    depth = 4000
    prof = B.surviving_log_mass(depth)
    c = {d: math.exp(prof[d] - d * math.log(rho) + 1.5 * math.log(d))
         for d in range(500, depth)}
    frac = {d: (d * BETA_) % 1.0 for d in c}

    def binned(lo: int, hi: int) -> list[float]:
        out = []
        for k in range(10):
            vals = [c[d] for d in c if lo <= d < hi and k / 10 <= frac[d] < (k + 1) / 10]
            out.append(statistics.fmean(vals))
        return out

    windows = [binned(1000, 2000), binned(2000, 3000), binned(3000, 4000)]

    # it does not converge: consecutive depths keep a fixed spread
    for centre in (1000, 2000, 3900):
        run = [c[d] for d in range(centre, centre + 20)]
        assert max(run) / min(run) > 1.05, (centre, max(run) / min(run))

    # it collapses onto a function of the offset
    last = windows[-1]
    scatter = statistics.fmean([
        statistics.pstdev([c[d] for d in c
                           if 3000 <= d < 4000 and k / 10 <= frac[d] < (k + 1) / 10])
        for k in range(10)])
    assert (max(last) - min(last)) / scatter > 8.0, (max(last) - min(last), scatter)

    # the shape is stable; only the level drifts, and the drift is shrinking
    shifts = []
    for a, b in zip(windows, windows[1:]):
        diff = [y - x for x, y in zip(a, b)]
        assert statistics.pstdev(diff) < 0.01, diff      # same shape
        shifts.append(statistics.fmean(diff))
    assert all(s > 0 for s in shifts) and shifts[0] > 2 * shifts[-1], shifts

    # psi is increasing in the offset, as the shrinking barrier gap predicts
    assert last[0] < last[-1]
    assert abs(last[0] - 10.37) < 0.05 and abs(last[-1] - 11.00) < 0.05, last


def test_the_mean_zero_tilt_is_bernoulli_beta_and_rho_is_its_closed_form() -> None:
    """The reduction behind psi, and an identity that was recorded as a coincidence.

    Steps Y = X - BETA with X ~ Bernoulli(1/2), so
    Lam(l) = -l*BETA + log((e^l + 1)/2).  Lam'(l) = -BETA + e^l/(e^l+1) vanishes exactly
    at l* = log(BETA/(1-BETA)), where the tilted coin is Bernoulli(BETA) -- so BETA is the
    threshold for a structural reason, not by fitting.

    Then rho = exp(Lam(l*)) = exp(-l* BETA)/(2(1-BETA)) = BETA^(-BETA) (1-BETA)^(BETA-1)/2,
    which IS theta(BETA).  J-theorem-six-one-threshold-is-slack recorded theta(p) = rho as
    agreeing to 1.1e-16; it is an algebraic identity, proved in
    Problems.Juggler.PaperBTilt.rho_closed_form.
    """
    lam = math.log(BETA_ / (1 - BETA_))
    assert math.isclose(lam, 0.536207535136, rel_tol=1e-11), lam

    # the mean-zero condition, and the tilted law
    assert abs(-BETA_ + math.exp(lam) / (math.exp(lam) + 1)) < 1e-15
    assert math.isclose(math.exp(lam) / (math.exp(lam) + 1), BETA_, rel_tol=1e-15)

    rho = B.chernoff_rate()
    assert math.isclose(math.exp(-lam * BETA_) / (2 * (1 - BETA_)), rho, rel_tol=1e-15)
    assert math.isclose(BETA_ ** (-BETA_) * (1 - BETA_) ** (BETA_ - 1) / 2, rho, rel_tol=1e-15)
    assert math.isclose(_theta(BETA_), rho, rel_tol=1e-15)


def test_the_change_of_measure_is_exact_and_the_gap_is_the_phase() -> None:
    """N_d/2^d = rho^d E~[e^(-l* S_d); S_t >= 0], and min S_d = 1 - frac(d*BETA).

    The second half is what puts frac(d*BETA) into the asymptotic: on the event the
    endpoint is S_d = m_d + (1 - frac(d*BETA)) with m_d = o_d - ceil(d*BETA) a NONNEGATIVE
    INTEGER, so the walk cannot end closer to the barrier than that gap.  Hence the exact
    factorisation N_d/2^d = rho^d e^(-l*(1-frac(d*BETA))) G(d) with G integer-indexed.
    """
    lam = math.log(BETA_ / (1 - BETA_))
    rho = B.chernoff_rate()

    for d in (50, 200, 500):
        mass = {0: 1.0}
        for t in range(1, d + 1):
            nxt: dict[int, float] = {}
            for o, m in mass.items():
                nxt[o + 1] = nxt.get(o + 1, 0.0) + BETA_ * m
                nxt[o] = nxt.get(o, 0.0) + (1 - BETA_) * m
            mass = {o: m for o, m in nxt.items() if o >= t * BETA_}
        tilted = sum(m * math.exp(-lam * (o - d * BETA_)) for o, m in mass.items())
        assert math.isclose(B.non_contracting(d) / 2 ** d, rho ** d * tilted, rel_tol=1e-12), d

        # the gap, and that it is attained
        gap = math.ceil(d * BETA_) - d * BETA_
        assert math.isclose(gap, 1 - (d * BETA_) % 1.0, rel_tol=1e-12)
        assert math.isclose(min(o - d * BETA_ for o in mass), gap, rel_tol=1e-12)


def test_the_six_percent_wobble_is_two_competing_sixty_percent_effects() -> None:
    """psi = e^(-l*(1-phi)) * h(phi), and the two factors nearly cancel.

    The explicit phase factor rises by e^(0.9 l*) = 1.620 across the circle.  psi rises by
    only 1.061.  So h -- the integer-indexed part, whose existence is the open local limit
    theorem -- must FALL by 1.527, and it does.  The small observed oscillation is the
    residue of two large opposed ones: a wider barrier gap costs e^(-l*(1-phi)) in the tilt
    and buys survival room in h.

    That is why stripping the elementary factor does not make the problem easier: it
    exchanges a 6% oscillation for a 53% one.
    """
    import statistics

    lam = math.log(BETA_ / (1 - BETA_))
    rho = B.chernoff_rate()
    depth = 4000
    prof = B.surviving_log_mass(depth)
    ds = range(3000, depth)
    c = {d: math.exp(prof[d] - d * math.log(rho) + 1.5 * math.log(d)) for d in ds}
    phi = {d: (d * BETA_) % 1.0 for d in ds}
    h = {d: c[d] * math.exp(lam * (1 - phi[d])) for d in ds}

    def binned(v: dict[int, float]) -> list[float]:
        return [statistics.fmean([v[d] for d in ds if k / 10 <= phi[d] < (k + 1) / 10])
                for k in range(10)]

    P, H = binned(c), binned(h)
    assert math.isclose(max(P) / min(P), 1.0606, rel_tol=5e-3), max(P) / min(P)
    assert math.isclose(math.exp(lam * 0.9), 1.6203, rel_tol=1e-3)
    assert math.isclose(max(H) / min(H), 1.527, rel_tol=5e-3), max(H) / min(H)
    assert P[0] < P[-1] and H[0] > H[-1]            # they move in opposite directions
