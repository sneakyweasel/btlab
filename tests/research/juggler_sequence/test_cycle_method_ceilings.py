"""Guards for the two measured method ceilings."""

from __future__ import annotations

import pytest

from research.juggler_sequence.cycle_method_ceilings import (
    RUN_CONST,
    admissible_shape_count,
    ceilings_report,
    even_count_of,
    shape_growth,
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
