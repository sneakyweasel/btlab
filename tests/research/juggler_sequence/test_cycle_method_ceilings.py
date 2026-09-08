"""Guards for the two measured method ceilings."""

from __future__ import annotations

import math

import pytest

from research.juggler_sequence.cycle_method_ceilings import (
    RUN_CONST,
    admissible_shape_count,
    ceilings_report,
    distinctness_gain,
    even_count_of,
    law_kill_fraction,
    length_only_optimum,
    reach_scaling,
    trailing_evens_transport,
    shape_count_under,
    shape_growth,
    surplus,
)


def test_convergent_invariant_is_flat() -> None:
    """n_max log n / (q q_next) is a constant, so n_max ~ c q q_next.

    This is what makes the floor route diverge: q_next is unbounded.
    """
    data = ceilings_report()
    assert data["invariant_min"] > 0.4
    assert data["invariant_max"] < 0.55
    # Flat to within a factor 1.3 over five orders of magnitude in q.
    assert data["invariant_max"] / data["invariant_min"] < 1.3
    qs = [row["q"] for row in data["convergent_rows"]]
    assert qs == sorted(qs) and qs[-1] / qs[0] > 1000


def test_shape_count_at_the_theorem_3_31_frontier() -> None:
    """Theorem 3.31 settled e <= 7; this is the count it faced at o_min."""
    odd, count = admissible_shape_count(7)
    assert (odd, count) == (12, 2651)


def test_shape_count_grows_about_six_fold_per_even_letter() -> None:
    rows = shape_growth()
    growths = [r["growth"] for r in rows if r["growth"]]
    assert 5.0 < sorted(growths)[len(growths) // 2] < 7.0
    # Exponential, not polynomial: e = 20 is already past 10^13.
    by_e = {r["e"]: r["shapes"] for r in rows}
    assert by_e[20] > 10**13
    assert by_e[16] == 10_636_522_143


def test_the_frontier_is_nowhere_near_a_surviving_length() -> None:
    """Enumeration reached e = 7; the first survivor needs e in the thousands."""
    assert even_count_of(25781) == 9515
    assert even_count_of(25781) > 1000 * 7


def test_run_const_is_the_shared_constant() -> None:
    """The run cap and the least odd count use the same constant."""
    assert RUN_CONST == pytest.approx(1.7095112913514547, rel=1e-12)
    for even in (7, 20, 100):
        odd, _ = admissible_shape_count(even)
        assert odd == int(even * RUN_CONST) + 1


def test_report_makes_no_halt_claim() -> None:
    data = ceilings_report()
    assert data["halt_theorem"] is False
    assert data["no_cycle_all_lengths"] is False
    assert data["floor_route_reach_diverges"] is True


# --- The sharper ceiling: the law is vacuous where cycles could live ---


def test_law_is_the_anchor_tightened_by_the_surplus() -> None:
    """It can only remove shapes, never add them."""
    for even in (10, 16, 31):
        assert shape_count_under(even, run_suffix_law=True) <= shape_count_under(
            even, run_suffix_law=False
        )


def test_law_kills_nothing_once_the_surplus_is_small() -> None:
    """At e = 31 the surplus is already 2.1e-3 and the two counts agree exactly.

    Theorem 3.26's law adds no constraint there. Not "infeasible to
    enumerate" -- empty. The cheap witness; `e = 389` is the slow one.
    """
    row = law_kill_fraction(31)
    assert row["surplus"] < 3e-3
    assert row["anchor_shapes"] == row["law_shapes"]
    assert row["killed_fraction"] == 0.0
    assert row["anchor_shapes"] > 10**20


@pytest.mark.slow
def test_law_is_vacuous_at_a_survivor_scale_surplus() -> None:
    """e = 389 has surplus 4.4e-5, at or below every surviving length's.

    Exact integers of ~300 digits, so this is minutes; the conclusion is
    the same one `e = 31` shows cheaply.
    """
    row = law_kill_fraction(389)
    assert row["surplus"] < 5e-5
    assert row["anchor_shapes"] == row["law_shapes"]
    assert row["anchor_shapes"] > 10**200


def test_law_does_bite_when_the_surplus_is_ordinary() -> None:
    """The guard must be able to fail: at e = 10 the surplus is O(1) and the
    law removes about 41% of shapes."""
    row = law_kill_fraction(10)
    assert row["surplus"] > 0.3
    assert 0.35 < row["killed_fraction"] < 0.45


def test_the_survivors_sit_in_the_vacuous_regime() -> None:
    """Every surviving length has a surplus at or below the tested point."""
    data = ceilings_report()
    assert data["surplus_at_first_survivor"] < 5e-5
    assert any(row["killed_fraction"] == 0.0 for row in data["law_rows"])
    assert any(row["killed_fraction"] > 0.3 for row in data["law_rows"])


def test_surplus_is_the_fractional_part_identity() -> None:
    """Lambda = log(3/2) * (1 - frac(e * RUN_CONST))."""
    for even in (7, 31, 210, 389):
        expected = math.log(1.5) * (1.0 - (even * RUN_CONST) % 1.0)
        assert surplus(even) == pytest.approx(expected, rel=1e-9)


# --- The counting route, now that distinctness is formally available ---


def test_distinctness_is_real_but_worth_nothing_at_the_relevant_floor() -> None:
    """Orbit distinctness is Lean (cyclePrimitive_orbit_injOn), so the e valleys
    are distinct odds n, n+2, ... rather than all at n. The refinement is real
    and bounded by O(e/n) -- and n >> e wherever a length actually matters."""
    for row in ceilings_report()["distinctness_rows"]:
        assert row["gain"] > 0.0, row["L"]
        assert row["gain"] < 1e-3, row["L"]
        assert row["gain"] == pytest.approx(row["e_over_n"], rel=0.2)


def test_distinctness_gain_shrinks_as_the_floor_rises() -> None:
    """n_max ~ q q_next outgrows e ~ 0.37 L, so the counting route closes."""
    rows = ceilings_report()["distinctness_rows"]
    gains = [row["gain"] for row in rows]
    assert gains == sorted(gains, reverse=True)


def test_distinctness_would_matter_if_the_floor_were_small() -> None:
    """The guard must be able to bite: at n just above the published floor the
    same refinement is worth percent, not 1e-4."""
    row = distinctness_gain(176251, n=10**6 + 1)
    assert row["gain"] > 0.05


def test_finance_is_optimal_among_length_only_charges_up_to_the_unroll() -> None:
    """A length-only charge must cover e valleys at n, n+2, ..., so it is at
    least ~e/(n log n). Finance lands on that optimum times the 6/5 unroll,
    so the family has about 20% left in it and no more."""
    rows = length_only_optimum()
    big = [row for row in rows if row["q"] >= 1000]
    for row in big:
        assert 1.15 < row["ratio"] < 1.5, row["q"]
    # The largest convergents, where the asymptotics have settled, sit on 6/5.
    assert min(row["ratio"] for row in big) == pytest.approx(1.21, abs=0.02)


def test_the_optimum_is_the_even_share_over_log_three() -> None:
    """e/L -> 1 - log2/log3 = 0.369, so the optimum is a constant."""
    for row in length_only_optimum():
        assert row["even_share"] == pytest.approx(0.369, abs=0.002)
        assert row["optimum"] == pytest.approx(0.3359, abs=0.002)


def test_walk_charge_reach_is_sqrt_floor_times_log() -> None:
    """period ~ 2 sqrt(N0) log N0, derived from the boundary layer rather than
    fitted. Constant to 7% across the three published instances."""
    data = reach_scaling()
    assert data["walk_ratio_spread"] < 1.10
    for row in data["walk_rows"]:
        assert 1.9 < row["ratio"] < 2.2, row["floor"]


def test_the_fitted_powers_drift_where_the_derived_forms_do_not() -> None:
    """N0^0.69 is a fit over a narrow range; it is not the scaling law."""
    data = reach_scaling()
    powers = [row["period"] / row["fitted_power"] for row in data["walk_rows"]]
    ratios = [row["ratio"] for row in data["walk_rows"]]
    # The derived form is tighter than the fitted power across the same points.
    assert (max(ratios) / min(ratios)) < (max(powers) / min(powers))


def test_finance_reach_is_sqrt_of_floor_times_log() -> None:
    for row in reach_scaling()["finance_rows"]:
        assert 1.1 < row["ratio"] < 1.3, row["floor"]


def test_trailing_evens_constraint_is_r_independent() -> None:
    """The window's 2^r and the r square roots cancel exactly.

    So cycle_trailing_evens_lt is the r = 1 case transported, and the r = 1
    case is what finance is derived from. The family looks floor-sensitive
    but is not an independent constraint.
    """
    n = 10**6 + 1
    rows = [trailing_evens_transport(n, r) for r in range(1, 13)]
    base = rows[0]["transported"]
    for row in rows:
        assert row["transported"] == pytest.approx(base, rel=1e-15), row["r"]
        assert row["transported"] == pytest.approx(row["log1p"], rel=1e-15)
    # The uncancelled width does grow, which is why it looks like a lever.
    assert rows[-1]["log_width_at_cut"] / rows[0]["log_width_at_cut"] == pytest.approx(
        2**11, rel=1e-9
    )
