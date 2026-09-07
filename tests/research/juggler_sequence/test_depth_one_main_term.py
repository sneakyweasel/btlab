"""The depth-one main term, its constant, and its cancellation on odd starts."""

from __future__ import annotations

import math

from research.juggler_sequence import depth_one_main_term as D


def test_the_complete_cubic_sums_mod_27_are_nine_for_both_dual_coefficients() -> None:
    """Coefficient -16 is the untwisted dual, -2 the half-integer-shifted one; both give 9."""
    for c in (-16, -2):
        s = D.complete_cubic_sum(c)
        assert abs(s.real - 9.0) < 1e-9 and abs(s.imag) < 1e-9


def test_the_stationary_phase_constant_is_four_root_eight_over_27_times_three_quarters_cubed_half() -> None:
    """(4√8/27)(3/4)^{3/2} = 0.27217, and the measured sum matches it to 1% at X = 1e5."""
    pred = D.predicted_constant()
    assert abs(pred - (4 * math.sqrt(8) / 27) * (3 / 4) ** 1.5) < 1e-12
    s = D.depth_one_sums(10**5)
    assert abs(s["abs_S_all_over_X34"] / pred - 1) < 0.02


def test_the_bias_lives_on_even_M_and_the_odd_sum_is_far_below_root_X() -> None:
    """Even M carry ≈ 0.425 X^{3/4} of imbalance; odd M carry O(1)-ish, and |S_odd| ≪ √X."""
    s = D.depth_one_sums(10**5)
    assert 0.40 < s["even_M_imbalance_over_X34"] < 0.45
    assert abs(s["imbalance_odd_M"]) < 0.02 * abs(s["imbalance_even_M"])
    assert s["abs_S_odd_over_sqrtX"] < 0.1


def test_the_tower_levels_show_only_root_order_imbalance() -> None:
    """Levels 1-4 over odd starts ≤ 1e5: |imbalance| / √cylinder stays O(1)."""
    t = D.tower_level_imbalances(10**5)
    assert all(abs(v["over_sqrt"]) < 3.0 for v in t.values())
    assert t["level_1"]["cylinder"] == 50000
