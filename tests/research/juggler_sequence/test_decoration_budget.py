"""Fast checks for the Paper B decoration-and-mode budget census."""

from __future__ import annotations

from fractions import Fraction

from research.juggler_sequence.decoration_budget import (
    OFFSET_RATIO_DECORATED,
    P0_T_LINE,
    P_LIST,
    algebraic_theta_identities,
    branch_offset,
    combinatorial_inventory,
    decorated_margin_scan,
    orbit_j_census,
    paper_scales,
    run_census,
)


def test_algebraic_7_4_and_2_5() -> None:
    alg = algebraic_theta_identities()
    assert alg["bare_ratio_is_4.375"]
    assert abs(alg["bare_ratio"] - 4.375) < 1e-12
    assert alg["decorated_ratio_is_7_4"]
    assert OFFSET_RATIO_DECORATED == Fraction(7, 4)
    assert alg["window_is_2.5_times_kernel"]
    assert alg["composite_positive"]
    assert alg["decorated_composite"] == [405, 512]


def test_three_p_t_ratio_is_3_p_to_minus_1_48() -> None:
    for p in P_LIST:
        s = paper_scales(float(p))
        predicted = 3.0 * float(p) ** (-1.0 / 48.0)
        assert abs(s["ratio_t_over_cap"] - predicted) < 1e-12
        assert predicted > 1.0
        assert predicted < 3.0
    # Dies: 3 P^{-1/48} < 1 iff P >= 3^{48}.
    assert P0_T_LINE == 3**48
    assert 3.0 * float(P0_T_LINE) ** (-1.0 / 48.0) <= 1.0 + 1e-12


def test_combinatorial_table_p0_not_structural() -> None:
    p0_sources = {
        "product_t",
        "product_qd",
        "term_count_rho",
        "thm61_j_passenger_qd",
    }
    for p in P_LIST:
        inv = combinatorial_inventory(float(p))
        by_src = {row["source"]: row for row in inv["rows"]}
        assert inv["kinds"]["structural"] == 0
        for src in p0_sources:
            assert by_src[src]["overflow_kind"] == "p0"
            assert by_src[src]["value"] > by_src[src]["cap"]
        # Single-layer J2 and Lemma 5.2(i) stay inside at these P.
        assert by_src["step3b_q_Y"]["overflow_kind"] == "none"
        assert by_src["step3a_W_uh"]["overflow_kind"] == "none"
        assert by_src["step3a_h"]["overflow_kind"] == "none"
        assert by_src["thm61_i"]["overflow_kind"] == "none"
        assert by_src["thm61_i_passenger_D3"]["overflow_kind"] == "none"
        assert by_src["step3e_j"]["j"] == 3.0
        # Ratios for the t-line shrink with P.
        assert abs(by_src["product_t"]["ratio"] - inv["scales"]["ratio_t_over_cap"]) < 1e-12


def test_t_ratio_shrinks() -> None:
    ratios = [
        combinatorial_inventory(float(p))["scales"]["ratio_t_over_cap"]
        for p in P_LIST
    ]
    assert ratios[0] > ratios[1] > ratios[2]
    assert ratios[2] < 2.0


def test_j_window_at_1e6() -> None:
    # Exact j = ΔΔ m at the paper's (H1, H2). Fast consecutive window.
    row = orbit_j_census(10**6, window=5_000, samples=2_000, boundary=200)
    assert row["h1"] == 2
    assert row["h2"] == 2
    # This census always reported live_j = [-1,0,1,2]; the assertion was written to the
    # manuscript's printed |j| <= 3 and so never flagged that 3 is unattainable.  The bound
    # is 2 (Lemma 5.1(iii) erratum, Lean `offset_abs_le_two`), and it is sharp.
    assert row["max_abs_j"] == 2
    assert row["j_overflow"] is False
    assert row["live_j"] == [-1, 0, 1, 2]
    assert abs(branch_offset(10**6 + 1, 4, 4)) <= 2


def test_decorated_composite_7_4() -> None:
    m = decorated_margin_scan(1e6, k=1, j=1)
    assert abs(m["kernel_ratio"] - 4.375) < 1e-9
    assert abs(m["decorated_ratio"] - 1.75) < 1e-9
    assert m["decorated_single_signed"]
    assert abs(m["B_decorated_ratio"] - 1.0) < 1e-6
    assert 0.8 < m["B_kernel_ratio"] < 1.3
    assert 2.0 < m["theta_factor_fd"] < 3.2


def test_run_census_parks() -> None:
    payload = run_census(
        (10**6, 10**8),
        orbit_window=2_000,
        orbit_samples=1_000,
        orbit_boundary=200,
    )
    assert payload["verdict"]["decision"] == "PARK"
    assert payload["verdict"]["j_overflow"] is False
    assert payload["verdict"]["theta_ok"] is True
    assert payload["verdict"]["kinds"]["structural"] == 0
    assert payload["verdict"]["kinds"]["p0"] > 0
    assert payload["anti_overclaim"]["paper_b_modified"] is False
