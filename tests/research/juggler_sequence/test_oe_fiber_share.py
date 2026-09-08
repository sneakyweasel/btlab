"""The OE-fiber share is a quadratic sweep; on cubes it is exact."""

from __future__ import annotations

from fractions import Fraction as F
from math import isqrt

from research.juggler_sequence import oe_fiber_share as O


def test_the_fiber_is_the_paper_c_fiber() -> None:
    """Phi(m) = odd n with m^4 <= n^3 < (m+1)^4, and H_m is within one of (2/3) m^{1/3}."""
    for m in (99969, 100000, 10 ** 6, 123457):
        ns = O.oe_fiber(m)
        assert all(n % 2 == 1 and m ** 4 <= n ** 3 < (m + 1) ** 4 for n in ns)
        assert abs(len(ns) - (2 / 3) * m ** (1 / 3)) <= 2
        # nothing just outside belongs
        assert (ns[0] - 2) ** 3 < m ** 4 and (ns[-1] + 2) ** 3 >= (m + 1) ** 4


def test_the_two_named_fibers() -> None:
    """99969 is empty, 10^6 = 100^3 is full."""
    assert O.share(99969) == (31, 0)
    H, G = O.share(10 ** 6)
    assert H == 67 and G == H


def test_the_cube_identity_and_its_range_on_small_cubes() -> None:
    """isqrt((k^4+t)^3) = k^6 + 3k^2 t/2 on the whole fiber of k^3, k = 2..60."""
    for k in range(2, 61):
        c = O.cube_fiber(k)
        assert c["identity_holds"], k
        assert c["range_slack"] >= 0, k          # 3 t_max <= 4 k
        assert c["as_predicted"], k
        if k % 2 == 0:
            assert c["full"] and not c["alternating"] or c["H"] == 1, k
        else:
            assert c["alternating"] and abs(2 * c["G"] - c["H"]) <= 1, k


def test_the_range_bound_is_attained() -> None:
    """3 t_max = 4 k happens, so the Lean hypothesis 3t <= 4k is the sharp one."""
    assert min(O.cube_fiber(k)["range_slack"] for k in range(2, 121)) == 0


def test_the_identity_outlives_the_fiber_and_then_breaks() -> None:
    """The identity holds while t^2 < 8k^2/3, i.e. t < 1.63k, which is past the fiber's
    4k/3; at t = 2k it fails. So 3t <= 4k in Lean is the fiber's bound, not the identity's."""
    holds_past_fiber = broken = 0
    for k in range(20, 60, 2):
        for t, expect in ((3 * k // 2, True), (2 * k, False)):
            t |= 1
            ok = 2 * isqrt((k ** 4 + t) ** 3) == 2 * k ** 6 + 3 * k * k * t
            if expect:
                holds_past_fiber += ok
            else:
                broken += not ok
    assert holds_past_fiber == 20 and broken == 20


def test_the_empty_region_integral_is_twenty_five_over_one_hundred_eight() -> None:
    assert O.empty_beta_integral() == F(25, 108)
    # piecewise measure is continuous at the joins and vanishes outside the window
    for b in (F(1, 6), F(0), F(-1, 3), F(-2, 3), F(-5, 6)):
        lhs = O.empty_theta_measure(b - F(1, 10 ** 6))
        rhs = O.empty_theta_measure(b + F(1, 10 ** 6))
        assert abs(lhs - rhs) < F(1, 10 ** 4), b
    assert O.empty_theta_measure(F(1, 5)) == 0 and O.empty_theta_measure(F(-9, 10)) == 0
    assert O.empty_theta_measure(F(0)) == F(1, 6)


def test_the_phase_average_is_one_half_at_every_drift() -> None:
    for b in (-0.9, -0.4, 0.0, 0.3, 1.7):
        assert abs(O.phase_average(b, 200) - 0.5) < 5e-3, b


def test_the_model_predicts_the_share_inside_the_window() -> None:
    """Mean error of order 1/H on the fibers near 10^5 with |beta| <= 1."""
    errs = []
    for m in range(100123, 103000):
        ph = O.phases(m)
        if abs(ph["beta"]) <= 1.0:
            H, G = O.share(m)
            errs.append(abs(G / H - O.model_share(ph["beta"], ph["theta"], 800)))
    assert len(errs) >= 30
    assert sum(errs) / len(errs) < 0.08          # 1/H = 0.032 here, with rounding noise


def test_extremes_only_occur_inside_the_predicted_drift_window() -> None:
    for m in range(100123, 104000):
        H, G = O.share(m)
        if G in (0, H):
            b = O.phases(m)["beta"]
            assert float(O.BETA_LO) - 0.15 <= b <= float(O.BETA_HI) + 0.15, (m, b)


def test_the_sharp_window_is_much_narrower_than_paper_c_discards() -> None:
    lo, hi = O.sharp_alpha_window(10 ** 6)
    assert (lo, hi) == (-1.25, 0.25)
    assert 2 * O.PAPER_C_WINDOW / (hi - lo) > 25


def test_the_density_is_at_the_predicted_scale_and_the_mean_is_a_half() -> None:
    d = O.density_scan(10 ** 4 + 123, 800)
    assert abs(d["mean_share"] - 0.5) < 0.01
    assert 0.5 * d["predicted_pct"] < d["empty_pct"] < 2.5 * d["predicted_pct"]
    assert 0.5 * d["predicted_pct"] < d["full_pct"] < 2.5 * d["predicted_pct"]


def test_the_lean_layer_carries_the_cube_theorems() -> None:
    from research.juggler_sequence.lean_paths import LAYERS

    src = LAYERS["CubeFiber"].read_text(encoding="utf-8")
    for name in ("cube_fiber_range", "cube_fiber_sqrt_even", "cube_fiber_even_image",
                 "even_cube_fiber_full", "cube_fiber_sqrt_odd", "cube_fiber_alternating",
                 "odd_cube_fiber_alternating"):
        assert f"theorem {name}" in src, name
    for banned in ("sorry", "admit"):
        assert banned not in src
