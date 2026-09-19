"""Phase-0 checks for the 1/3 vs 1/2 rest-average gap."""

from __future__ import annotations

import pytest

from pathlib import Path

from research.juggler_sequence.fate_contagion import lambda_root
from research.juggler_sequence.oe_rest_average import (
    ETA_H_BOUND,
    alpha_star,
    circle_norm,
    convergent_denominators,
    icbrt_exact,
    IDEAL,
    MASTER_C,
    PAIRING,
    POOR_SHARE,
    alpha_of,
    arc_count,
    averaging_payoff,
    averaging_theorem,
    classify,
    lock_census,
    master_inequality,
    poor_block_scaling,
    dyadic_logmass,
    exact_even_share,
    is_low_even,
    model_matches_fiber,
    poor_mask,
    summary,
)


def test_pairing_and_ideal_roots() -> None:
    assert abs(lambda_root(PAIRING) - 0.4480) < 5e-3
    assert abs(lambda_root(IDEAL) - 0.4927) < 5e-3
    assert lambda_root(PAIRING) < lambda_root(IDEAL)


def test_model_tracks_known_witness() -> None:
    rec = model_matches_fiber(1003635)
    assert rec["exact"] < 0.34
    assert rec["low_even"] is True
    assert is_low_even(rec["exact"], cutoff=0.35)


def test_poor_set_has_positive_logmass_fraction() -> None:
    mask = poor_mask(8_000)
    mid = dyadic_logmass(mask, 2_048, 4_095)
    hi = dyadic_logmass(mask, 4_096, 8_000)
    assert mid["fraction"] > 0.03
    assert hi["fraction"] > 0.03
    assert mid["n_set"] > 20


def test_alpha_defined_on_ordinary_m() -> None:
    a = alpha_of(10_000)
    assert 0.0 <= a < 1.0
    sh = exact_even_share(10_000)
    assert 0.2 <= sh <= 0.8


def test_classify_sharp_and_drowned() -> None:
    sharp = classify(
        [0.08, 0.09],
        {"weighted_even_share": 0.34, "rest_over_range": 0.4},
        {"weighted_even_share": 0.50},
    )
    drowned = classify(
        [0.08, 0.09],
        {"weighted_even_share": 0.49, "rest_over_range": 0.4},
        {"weighted_even_share": 0.50},
    )
    assert sharp.endswith("SHARP")
    assert drowned.endswith("DROWNED")


def test_small_summary_runs() -> None:
    rec = summary(limit=12_000)
    assert rec["n_poor"] > 0
    assert rec["classification"] in {
        "OE_REST_AVERAGE_SHARP",
        "OE_REST_AVERAGE_DROWNED",
        "OE_REST_AVERAGE_MIXED",
        "OE_REST_AVERAGE_PROVED",
    }
    assert rec["closure_classification"] in {
        "OE_REST_AVERAGE_SHARP",
        "OE_REST_AVERAGE_DROWNED",
        "OE_REST_AVERAGE_MIXED",
    }
    assert rec["lambda_roots"]["ideal"] > rec["lambda_roots"]["pairing"]
    assert rec["poor_logmass_fraction_min"] is not None
    assert rec["poor_logmass_fraction_min"] > 0.02


def test_dossier_headings() -> None:
    root = Path(__file__).resolve().parents[3]
    dossier = (root / "docs" / "problems" / "juggler_oe_rest_average.md").read_text(encoding="utf-8")
    for heading in (
        "## Problem",
        "## Exact statement",
        "## Current literature",
        "## Branch budget",
        "## Balanced-ternary formulation",
        "## Why BT may be relevant",
        "## Candidate operations / invariants",
        "## Experiments",
        "## Conjectures",
        "## Counterexamples",
        "## Formalization",
        "## Results",
        "## Open questions",
        "## Decision",
        "## Publication assessment",
    ):
        assert heading in dossier
    decision = dossier.split("## Decision", 1)[1].split("## ", 1)[0]
    assert any(word in decision for word in ("PROMOTE", "PARK", "CLOSE"))

def test_reopening_pays_only_at_essentially_the_mean() -> None:
    """The park stands, but the prize it was weighed against was the wrong one.

    The two-production inequality is the whole unconditional chain, and its
    root moves steeply in the OE coefficient: `2/9` gives `0.326121`, the mean
    share `1/3` gives `0.492658`. The coefficient matching `lambda**` on two
    productions alone is `0.3332760`, a share of `0.4999140` -- essentially the
    mean. So an averaged argument delivering the mean would reach the headline
    exponent with two productions, making the block-average family and the
    six-word ladder unnecessary for it, and taking Proposition 4.4's two
    exponential-sum bounds -- Paper C's largest unformalized gap -- off the
    critical path.

    The prize is therefore not a better exponent but the same exponent with the
    analytic core removed. That is a different prize from the one the PARK was
    weighed against, which is why the branch's "best next question: none on
    this line" is now recorded as arguable rather than settled.

    What still vindicates the park: the target is narrow. Break-even against
    the three-production base `0.448017`, which the block average ALREADY
    gives, is share `0.4555`. An averaged argument landing below that is a
    regression, not progress. Recovering "better than the worst case" is worth
    nothing here; only "essentially the mean" pays.
    """
    p = averaging_payoff()
    curve = {round(r["coefficient"], 6): r["root"] for r in p["two_production_curve"]}
    assert curve[round(2 / 9, 6)] == pytest.approx(0.326121, abs=1e-6)
    assert curve[0.3] == pytest.approx(0.442499, abs=1e-6)
    assert curve[round(1 / 3, 6)] == pytest.approx(0.492658, abs=1e-6)

    # the two anchors that decide whether reopening is worth anything
    assert p["matching_share"] == pytest.approx(0.499914, abs=1e-5)
    assert p["break_even_share"] == pytest.approx(0.455508, abs=1e-5)

    # and the shape of the answer: an intermediate coefficient can LOSE
    assert curve[0.3] < p["three_production_base"], (
        "share 0.45 is below what the block average already gives"
    )
    assert p["break_even_share"] < p["matching_share"] < 0.5


# --- the poor-fiber tail ---------------------------------------------------


def test_icbrt_exact_where_the_float_seed_is_not() -> None:
    """The seed `round(x ** (1/3))` is off by ~1e-16 x^(1/3), so it is useless
    exactly where `alpha_star` needs it: `m^2 S^3` with `S = 10^25`.

    `fate_contagion.icbrt` keeps that seed and stays correct for its own uses;
    it is a pinned Paper C input and is not edited from this branch.
    """
    for x in (0, 1, 7, 8, 26, 27, 10**30, 10**87 + 12345, (10**6) ** 2 * (10**25) ** 3):
        r = icbrt_exact(x)
        assert r**3 <= x < (r + 1) ** 3


def test_alpha_star_is_the_papers_alpha_not_the_fiber_step() -> None:
    """`alpha_star(m) = {(3/2) m^(2/3)}` exactly; perfect cubes are the check."""
    # m = t^3 gives (3/2) t^2, which is 0 mod 1 for even t and 1/2 for odd t
    assert alpha_star(100**3) == 0
    assert alpha_star(101**3) == pytest.approx(0.5)
    assert alpha_star(27) == pytest.approx(0.5)
    # and it is NOT alpha_of, which is the fiber's own first step
    m = 10**7 + 1
    assert abs(float(alpha_star(m)) - alpha_of(m)) < 1.1 * m ** (-1.0 / 3.0)


def test_convergents_have_the_defining_property() -> None:
    a = alpha_star(10**7 + 1)
    qs = convergent_denominators(a, 500)
    assert qs[0] == 1 and qs == sorted(qs)
    # ||q alpha|| < 1/q' for the next denominator: the fact Lemma 2 rests on
    for q, q_next in zip(qs, qs[1:]):
        assert float(circle_norm(q * a)) < 1.0 / q_next


def test_block_lock_master_inequality() -> None:
    """Lemma 1 is the whole proof of the poor-fiber tail. One negative slack
    refutes docs/theory/juggler_oe_poor_fiber_tail_note.md.

    Checked at every convergent denominator q <= H_m. The constant MASTER_C is
    1 + 4 sup(eta_m H_m), so the measured eta_m H_m is checked against the
    bound it is built on at the same time.
    """
    for lo, hi in ((10**6, 10**6 + 400), (10**7, 10**7 + 120), (10**8, 10**8 + 30)):
        rec = lock_census(lo, hi)
        assert rec["master_holds"], rec["tightest"]
        assert rec["min_slack"] > 0.0
        assert rec["eta_H_max"] <= ETA_H_BOUND
    assert MASTER_C >= 1.0 + 4.0 * ETA_H_BOUND


def test_every_poor_fiber_locks_at_a_small_denominator() -> None:
    """The mechanism, and the reason the tail is thin: a fiber with share at or
    below 0.40 has alpha_m within O(1/H_m) of a rational of small denominator.

    q = 1 is the extreme family of Corollary 4.6 (whole fibers with no even
    image); q = 3 is the attaining witness family of the pairing third.
    """
    rec = lock_census(10**6, 10**6 + 1500)
    assert rec["n_poor"] > 0
    assert set(rec["poor_lock_q_values"]) <= {1, 3, 5}
    assert rec["poor_max_resonance"] < 4.0


def test_arc_count_bounds_the_resonant_m() -> None:
    """Lemma 3, which is Lemma 4.3 with its two goodness arcs generalized."""
    for q_max in (1, 3, 8):
        for c in (1.0, 5.0, 20.0):
            rec = arc_count(10**4, q_max, c * 10**4 ** (-1.0 / 3.0))
            assert rec["holds"], rec
            assert rec["ratio"] <= 1.0


def test_poor_density_decays_at_the_cube_root() -> None:
    """The theorem is an upper bound; if the true exponent were smaller the
    corollary would be false, so the density times u^(1/3) must not drift up."""
    rec = poor_block_scaling(anchors=(10**5, 10**6), window=800)
    vals = [r["density_times_cube_root"] for r in rec["rows"]]
    assert all(0.5 < v < 5.0 for v in vals), vals
    assert vals[-1] <= vals[0] * 1.5


def test_two_productions_now_pass_lambda_star_star() -> None:
    """What the theorem buys: the same exponent with the analytic core removed.

    The gain in the number is 8.6e-5. The gain that matters is that (5.1) uses
    only Lemma 3.1, Lemma 3.2 and the tail theorem, so Proposition 4.4's two
    exponential-sum bounds -- Paper C's largest unformalized gap -- the
    six-word ladder, Appendix D, and Lemmas 4.1/4.1'/4.2 all leave the critical
    path. The supremum 0.4926580 is approached, not attained: eta_0 is fixed
    before x, which is the shape the published statement already has.
    """
    t = averaging_theorem()
    assert t["break_even_eta_0"] == pytest.approx(8.60e-5, rel=2e-2)
    assert t["beats_published"]
    assert t["two_production_root"] > t["lambda_star_star_published"]
    assert t["two_production_root"] < t["ideal_root"] <= 0.4926580
    # and the honest cost of the crude constants
    assert t["u_0"] > 1e30


def test_note_records_what_leaves_the_critical_path() -> None:
    root = Path(__file__).resolve().parents[3]
    note = (root / "docs" / "theory" / "juggler_oe_poor_fiber_tail_note.md").read_text(
        encoding="utf-8"
    )
    assert "EXACT — HUMAN PROOF" in note
    # the note is hard-wrapped prose, so match on collapsed whitespace
    flat = " ".join(note.lower().split())
    for claim in (
        "proposition 4.4 leaves the critical path",
        "not a halt theorem",
        "no cycle is excluded",
    ):
        assert claim in flat, claim
    dossier = (root / "docs" / "problems" / "juggler_oe_rest_average.md").read_text(
        encoding="utf-8"
    )
    assert "**PROMOTE.**" in dossier.split("## Decision", 1)[1]
