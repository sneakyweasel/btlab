"""Effective tower height: the fair-coin DP, its cross-check, and the tower tolerance."""

from __future__ import annotations

import math

from research.juggler_sequence import effective_tower_height as E
from research.juggler_sequence.tao_reduction import (
    N0_CERTIFIED,
    fair_tilted_live_suffix_odd_mass,
    p_of_C,
    scale_L,
    theta_of_C,
)

L12 = scale_L(12 * math.log(10.0), N0_CERTIFIED)
L50 = scale_L(50 * math.log(10.0), N0_CERTIFIED)


def test_reset_at_every_even_step_with_height_only_is_the_laboratory_mu_4() -> None:
    """With no depth cap and a reset at every E, the height-≥4 share is pressure_direct's μ_4."""
    for L, C in ((L12, 20), (L50, 20), (L50, 43)):
        d, theta = math.ceil(C * L), theta_of_C(C)
        mine = E.tilted_live_profile(L, d, theta, math.inf, depth_cap=None)["profile"]
        lab = [fair_tilted_live_suffix_odd_mass(L, t, theta, 4) for t in range(1, d + 1)]
        assert max(abs(a - b) for a, b in zip(mine, lab)) < 1e-12


def test_the_live_band_at_1e12_forbids_every_good_base() -> None:
    """L = 0.526: an even step at u ≤ 0 lands below -L, so no live start ever resets."""
    for C in (20, 43):
        r = E.tilted_live_profile(L12, math.ceil(C * L12), theta_of_C(C), 0.0)
        assert r["live"] and abs(r["mean_uncontrolled_second_half"] - 1.0) < 1e-12


def test_the_reset_rules_are_ordered_and_the_honest_one_has_no_fair_coin_room() -> None:
    """u ≤ 0 ⊇ u < 1 ⊇ any E in uncontrolled mass; the honest share exceeds the budget 2p_C - 1."""
    for C in (20, 43):
        d, theta, p = math.ceil(C * L50), theta_of_C(C), p_of_C(C)
        shares = {name: E.tilted_live_profile(L50, d, theta, thr, strict=s)["mean_uncontrolled_second_half"]
                  for name, (thr, s) in E.RESET_RULES.items()}
        assert shares["never"] >= shares["u_le_0"] >= shares["u_lt_1"] >= shares["any_E"]
        assert shares["u_le_0"] > 0.8 > 2 * p - 1 > shares["any_E"]


def test_the_consistent_tolerance_is_the_critical_share_for_every_controllable_rule() -> None:
    """β* = p_C + O(1/d) for u ≤ 0, u < 1 and never; only the any-E rule has room, near 0.78."""
    for C in (20, 43):
        p = p_of_C(C)
        for name in ("u_le_0", "u_lt_1", "never"):
            thr, s = E.RESET_RULES[name]
            t = E.tower_tolerance(L50, C, thr, strict=s)
            assert not t["vacuous"] and abs(t["beta_star"] - p) < 0.006
        t = E.tower_tolerance(L50, C, math.inf)
        assert 0.75 < t["beta_star"] < 0.82


def test_the_tilted_pool_climbs_once_its_odd_share_passes_0_533() -> None:
    """e^θ β / (e^θ β + 1 - β) > log2/log3 iff β > 0.533 at θ_20: that is why β* is pinned."""
    theta = theta_of_C(20)
    crit = math.log(2) / math.log(3)
    tilted = lambda b: math.exp(theta) * b / (math.exp(theta) * b + 1 - b)  # noqa: E731
    assert tilted(0.53) < crit < tilted(0.54)
    assert tilted(p_of_C(20)) > crit           # the pool at β = p_C already climbs
