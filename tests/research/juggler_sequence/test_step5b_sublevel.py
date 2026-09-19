"""Fast checks for Step 5b sublevel geometry vs Lemma 3.9."""

from __future__ import annotations

from research.juggler_sequence.step5b_sublevel import (
    ANTI,
    P_LIST,
    _delta,
    C7,
    C7_ROW,
    FAMILY_NAMES,
    family_params,
    measure_model,
    paper_shifts,
    vandermonde_matrix,
)


def test_anti_overclaim() -> None:
    assert ANTI["sums_evaluated"] is False
    assert ANTI["paper_b_modified"] is False
    assert ANTI["k3_reopened"] is False
    assert ANTI["harvest_reopened"] is False
    assert ANTI["alpha_33_32"] is False
    assert ANTI["kernel_retagged"] is False


def test_c7_positive_on_printed_triple() -> None:
    assert C7 > 0.0
    assert C7_ROW["c7_positive_octant"] > 0.0
    assert abs(C7_ROW["det"]) > 1e-12
    m = vandermonde_matrix()
    assert len(m) == 3
    assert abs(m[1][0] + 0.75) < 1e-15
    assert abs(m[1][1] + 0.625) < 1e-15
    assert abs(m[1][2] + 0.5) < 1e-15


def test_w0_opposite_sign_one_omega_interval() -> None:
    params = family_params(10**6, "centre_cancel_w0", k=1)
    assert params is not None
    row = measure_model(params, which="phi", n_grid=20_000)
    assert row["omega_intervals"] == 1
    assert row["count_ok"]
    assert row["single_signed_complement"]


def test_same_sign_empty_omega() -> None:
    params = family_params(10**6, "centre_same_w0", k=1)
    assert params is not None
    row = measure_model(params, which="phi", n_grid=20_000)
    assert row["omega_intervals"] == 0
    assert row["omega_length"] == 0.0
    assert row["count_ok"]
    assert row["single_signed_complement"]


def test_p1e6_interval_count_at_most_cap() -> None:
    sh = paper_shifts(10**6)
    assert sh["h1"] >= 1
    seen = 0
    for name in FAMILY_NAMES:
        params = family_params(10**6, name, k=1)
        if params is None:
            continue
        row = measure_model(params, which="phi", n_grid=20_000)
        assert row["omega_intervals"] <= row["interval_cap"]
        assert row["count_ok"]
        seen += 1
    assert seen == len(FAMILY_NAMES)

def test_delta_has_no_cancellation_at_any_scale_this_module_reaches() -> None:
    """`_delta` is rationalised, and the direct form it replaced fails in range.

    All three returns are differences of powers of two nearby large numbers,
    with an answer of size `O(h sqrt(nu))` against operands of size `nu^1.5`.
    Written directly, BOTH derivatives are already seven digits down at
    `nu = 1e10`, which `P_LIST` reaches today -- `dp` at `3.4e-07` and `dpp` at
    `3.2e-07`, the same schedule -- and the value itself returns exactly `0.0`
    from about `1e20`. `first_v_half_p0` in the same module loops
    to `1e28`, so the scales sit side by side even though that path does not
    call this function.

    Rationalising removes the cancellation rather than bounding it, so this
    test asserts accuracy at every scale instead of guarding a threshold.
    """
    from mpmath import mp, mpf

    mp.dps = 50

    def reference(nu: float, h: float) -> tuple[float, float, float]:
        n = mpf(nu)
        x = n + 2 * h
        return (x ** mpf("1.5") - n ** mpf("1.5"),
                mpf("1.5") * (x ** mpf("0.5") - n ** mpf("0.5")),
                mpf("0.75") * (x ** mpf("-0.5") - n ** mpf("-0.5")))

    def direct(nu: float, h: float) -> tuple[float, float, float]:
        x = nu + 2.0 * h
        return (x**1.5 - nu**1.5, 1.5 * (x**0.5 - nu**0.5),
                0.75 * (x ** (-0.5) - nu ** (-0.5)))

    for exponent in (6, 10, 14, 20, 28):
        nu = 10.0**exponent
        got, want = _delta(nu, 1.0), reference(nu, 1.0)
        for value, truth in zip(got, want):
            assert abs((value - truth) / truth) < 1e-13, exponent

    # the top of the current P_LIST is already past BOTH of the direct form's
    # derivatives, so this was live breakage and not only a latent trap. Assert
    # both: checking dpp alone is the same mis-scoping that called this latent.
    assert float(P_LIST[-1]) == 1e10
    nu = 1e10
    for index in (1, 2):
        rel = abs((direct(nu, 1.0)[index] - reference(nu, 1.0)[index])
                  / reference(nu, 1.0)[index])
        assert rel > 1e-8, index

    # and from 1e20 the direct form silently returns zero rather than erroring
    assert direct(1e20, 1.0)[0] == 0.0
    assert _delta(1e20, 1.0)[0] > 2.9e10
