"""Guards for the run-type packing fragility audit."""

from __future__ import annotations

import math

import pytest

from research.juggler_sequence.cycle_budget_opt import budget_sum_terms
from research.juggler_sequence.cycle_finance import EPS_CONST, PUBLISHED_FLOOR
from research.juggler_sequence.cycle_packing_fragility import (
    PACKING_DEATHS,
    ee_model_holds,
    ee_to_resurrect,
    fragility_row,
    fragility_scan,
    packed_rhs_with_ee,
    three_term_rhs,
)
from research.juggler_sequence.paper_a_audit import o_min, parity_holds, theta

N = PUBLISHED_FLOOR + 1


def test_packing_deaths_match_the_published_progression() -> None:
    """Theorem 4.8 names 42 lengths 56347 + 1054k."""
    assert len(PACKING_DEATHS) == 42
    assert PACKING_DEATHS[0] == 56347
    assert PACKING_DEATHS[-1] == 56347 + 1054 * 41
    assert sorted(set(PACKING_DEATHS)) == list(PACKING_DEATHS)


def test_three_term_rhs_is_corollary_4_5s_charge() -> None:
    """The audit's three-term charge is exactly what `parity_holds` tests.

    This is the load-bearing identification of the whole branch: Corollary
    4.5's "length-only parity charge" is the three-class bound, not a
    two-class parity split.
    """
    for length in (19, 84, 1054, 25781, 56347):
        odd = o_min(length)
        th = theta(length, odd)
        rhs = three_term_rhs(N, length, odd)
        assert parity_holds(length, odd, th, N) == (th <= rhs)


def test_packed_rhs_at_zero_ee_reproduces_the_shipped_bound() -> None:
    """`ee = 0` must agree with `cycle_budget_opt`, or the audit prices the wrong thing."""
    for length in (56347, 75319, 99561):
        odd = o_min(length)
        mine = packed_rhs_with_ee(N, length, odd, 0)
        theirs = EPS_CONST * budget_sum_terms(N, length, odd)
        assert mine == pytest.approx(theirs, rel=1e-12)


@pytest.mark.parametrize(
    "word",
    ["OOEEOOE", "OOEOOE", "OOOOEE", "OOEOEOOEE", "OOEOOEOOE", "OE", "OOE"],
)
def test_ee_counting_model_holds_on_explicit_words(word: str) -> None:
    assert ee_model_holds(word)


def test_ooeeooe_is_the_documented_counterexample() -> None:
    """The word Paper A's ledger cites: EE makes #cheap exceed o - e."""
    word = "OOEEOOE"
    length, odd = len(word), word.count("O")
    even = length - odd
    runs = sum(1 for i in range(length) if word[i] == "E" and word[i - 1] == "O")
    assert (odd, even) == (4, 3)
    assert odd - runs == 2 > odd - even == 1


def test_every_death_survives_the_hypothesis_free_charge() -> None:
    """Each of the 42 is killed by the packing alone, never by the three-term bound."""
    data = fragility_scan()
    assert data["all_survive_three_term"]
    assert data["all_die_under_packing"]


def test_refinement_budget_is_the_single_constant() -> None:
    """The packing buys a uniform factor, and it is e/(o-e) to four places."""
    data = fragility_scan()
    assert data["refinement_budget_min"] == pytest.approx(1.4048, abs=5e-5)
    assert data["refinement_budget_max"] == pytest.approx(1.4048, abs=5e-5)
    # e/(o-e) is the leading order only: it reads off the n-scale terms and
    # ignores the t- and n^2-scale ones, which pull the true value down by
    # about a third of a percent.
    row = fragility_row(56347)
    assert row["refinement_budget"] == pytest.approx(
        row["e"] / (row["o"] - row["e"]), rel=5e-3
    )


def test_the_42_split_eighteen_fragile_and_twenty_four_robust() -> None:
    """The headline count. A change here changes what Theorem 4.8 may claim."""
    data = fragility_scan()
    assert data["deaths_examined"] == 42
    assert data["deaths_fragile_to_ee"] == 18
    assert data["deaths_robust_to_ee"] == 24
    assert data["robust_lengths"][0] == 75319
    # The split is a threshold in L, not a scatter.
    fragile = [r["L"] for r in data["rows"] if r["ee_to_resurrect"] is not None]
    assert fragile == list(PACKING_DEATHS[:18])


def test_fragile_deaths_need_less_ee_than_a_random_word_carries() -> None:
    """Why the 18 matter: the EE they need is well inside an ordinary EE density."""
    data = fragility_scan()
    assert data["deaths_inside_random_ee"] == data["deaths_fragile_to_ee"] == 18
    assert data["ee_to_resurrect_min"] == 50
    assert data["ee_to_resurrect_max"] == 3925


def test_resurrection_scan_does_not_stop_at_the_first_inadmissible_count() -> None:
    """The majorant rises to the cap crossing and falls after it.

    Stopping the scan early reports the inadmissibility point as a
    resurrection and calls every death fragile. This guards the bug.
    """
    length = 99561
    odd = o_min(length)
    even = length - odd
    assert packed_rhs_with_ee(N, length, odd, 2 * even - odd) is not None
    # Past the crossing the cheap count falls with the valleys.
    crossing = even - odd // 2
    below = packed_rhs_with_ee(N, length, odd, crossing)
    above = packed_rhs_with_ee(N, length, odd, crossing + 2000)
    assert below is not None and above is not None and above < below
    assert ee_to_resurrect(length) is None


def test_no_death_is_resurrected_by_the_three_term_bound_itself() -> None:
    """Sanity: the packed majorant never exceeds the hypothesis-free one at ee = 0."""
    for length in PACKING_DEATHS:
        odd = o_min(length)
        assert packed_rhs_with_ee(N, length, odd, 0) < three_term_rhs(N, length, odd)


def test_scan_makes_no_halt_or_refutation_claim() -> None:
    data = fragility_scan()
    assert data["halt_theorem"] is False
    assert data["no_cycle_all_lengths"] is False
    assert data["refutes_theorem_4_8"] is False
    assert math.isfinite(data["refinement_budget_max"])
