"""Guards for the Wu-Wang instance of the floor-free gap transfer."""

from __future__ import annotations

import math

from research.juggler_sequence.cycle_wuwang_reduction import (
    BLS_P,
    DIRICHLET_P,
    N0,
    RHIN_C,
    RHIN_P,
    WUWANG_P,
    closure_threshold,
    exponent_table,
    forced_period,
    period_exponent,
    quotient_cap_consistency,
    report,
    survivor_band,
    transfer_exponent,
    wuwang_checks,
)


def test_the_exponent_is_the_measure_plus_one() -> None:
    """n log n <= (2/C) L^(p+1) is the whole content of the swap."""
    assert transfer_exponent(RHIN_P) == 14.3
    assert transfer_exponent(WUWANG_P) == 5.1163051
    assert math.isclose(period_exponent(WUWANG_P), 1 / 5.1163051)


def test_wuwang_beats_rhin_by_a_factor_of_2_8() -> None:
    ratio = transfer_exponent(RHIN_P) / transfer_exponent(WUWANG_P)
    assert 2.79 < ratio < 2.80
    # The 2018 sharpening is in the noise; it is not a separate branch.
    assert abs(transfer_exponent(BLS_P) - transfer_exponent(WUWANG_P)) < 1e-3


def test_all_swap_checks_pass() -> None:
    for row in wuwang_checks():
        assert row["ok"], row["check"]


def test_dirichlet_floor_is_two() -> None:
    """No irrationality measure takes the closure target below L^2."""
    assert transfer_exponent(DIRICHLET_P) == 2.0
    assert transfer_exponent(WUWANG_P) > transfer_exponent(DIRICHLET_P)


def test_still_toothless_at_the_certified_floor() -> None:
    """Anti-overclaim: this is a reduction, not a kill.

    At N_0 = 3.5e8 the finance table forces period 780239. The transfer
    forces 4 with Rhin and 74 with Wu-Wang -- and only 58676 even with a
    perfect measure, so no improvement of the Diophantine input makes the
    floor-free route compete with the table at this floor.
    """
    rhin_forced = (N0 * math.log(N0) / 915) ** (1 / 14.3)
    ww_forced = forced_period(N0, WUWANG_P, 1.0)
    perfect = forced_period(N0, DIRICHLET_P, 1.0)
    assert 3 <= rhin_forced < 4
    assert 70 < ww_forced < 80
    assert ww_forced > rhin_forced
    assert perfect < 780239


def test_the_printed_rhin_constant_is_unchanged() -> None:
    """Rhin stays the effective companion; Wu-Wang is the asymptotic one."""
    assert math.isclose(2 * math.exp(6.1256), 1 / RHIN_C * 2, rel_tol=1e-9)
    rows = {row["source"].split()[0]: row for row in exponent_table()}
    assert rows["rhin-1987"]["constant_effective"] is True
    assert rows["wu-wang-2014"]["constant_effective"] is False


def test_survivors_stay_inside_the_allowance() -> None:
    """Nothing is killed: every finance survivor satisfies the new bound."""
    band = survivor_band()
    assert len(band) == 5
    for row in band:
        assert row["inside_wuwang_allowance"], row["L"]


def test_the_survivor_exponent_is_L_squared_over_log() -> None:
    """Section 6.2's `n ~ L^1.7` is `n ~ L^2 / log n`, not an exponent below two.

    `n_max log n_max / L^2` is order one across the whole certified range,
    while `log L / log n_max` drifts around 0.59 only because the log eats
    part of the square.
    """
    band = survivor_band()
    ratios = [row["n_max_logn_over_L2"] for row in band]
    assert all(0.1 < r < 2.0 for r in ratios), ratios
    exps = [row["paper_a_exponent"] for row in band]
    assert all(0.57 < e < 0.62 for e in exps)


def test_observed_quotients_are_far_inside_the_wuwang_cap() -> None:
    """Which is why the cap cannot close Paper D's family leftover."""
    caps = quotient_cap_consistency()
    assert caps
    for row in caps:
        assert row["inside"], row["q"]
    assert max(row["ratio"] for row in caps) < 1e-3


def test_closure_threshold_is_stated_and_not_claimed() -> None:
    t = closure_threshold()
    assert t["unconditional_exponent"] == 5.1163051
    assert t["previous_exponent_rhin"] == 14.3
    assert t["hard_floor_exponent"] == 2.0
    assert t["proved_here"] is False
    assert t["no_cycle_of_any_length"] is False


def test_report_is_self_consistent() -> None:
    data = report()
    assert data["all_checks_ok"]
    assert data["every_survivor_inside_allowance"]
    assert data["every_quotient_inside_cap"]
    assert data["kills_nothing_new"] is True
    assert data["is_halt_theorem"] is False
    assert data["raises_descent_floor"] is False
