"""Effective threshold certificate for Paper B: P_0 = 8.9e13, binding at Step 5b's W <= c_7 S/2."""

from __future__ import annotations

import math

from research.juggler_sequence import p0_certificate as C


def _pred_for(tag: str):
    """The printed inequalities, transcribed independently of the module's own list."""
    S5b = lambda P: 0.35 * P**-0.625  # noqa: E731
    S5a = lambda P: 0.60 * P**-0.625  # noqa: E731
    k, c7, rho0 = C.KAPPA, C.C7, C.C7 / 8.0
    V, E = C._V, C.interpolant_error
    return {
        "s3s1-window": lambda P: P**0.5 >= 12,
        "s3s1-Bsmall": lambda P: 2.25 * P ** (-1 / 16) < 0.5,
        "s3s2-window": lambda P: P**0.5 >= 8 * (1 + 2.25 * P**0.25),
        "s3s2-flat": lambda P: 8 * (1 + 2.25 * P**0.25) * P**0.5 <= 19 * P**0.75,
        "s3s2-wincount": lambda P: 0.6 * P**0.25 + 1 <= 0.65 * P**0.25,
        "s3s2-bdry": lambda P: (0.6 * P**0.25 + 1) * (0.35 * P ** (3 / 16)) ** -0.5 * P**0.375
        <= 1.1 * P ** (17 / 32) and 1.1 * P ** (17 / 32) <= P**0.625,
        "stage2-modecurv": lambda P: 0.39 * P**0.125 >= 4,
        "stage5-band": lambda P: 4.5 - 1.5 / P**0.5 >= 4.4,
        "claimC-1": lambda P: P ** (7 / 72) >= 3,
        "claimC-2": lambda P: 41 * P ** (5 / 36) <= P**0.5,
        "claimG-pref": lambda P: 96 * P ** (-5 / 24) <= 1,
        "claimG-P36": lambda P: P ** (-1 / 36) <= 1,
        "st3a-window": lambda P: 0.5 * P ** (23 / 48) >= 15 * P ** (10 / 48),
        "st3b-window": lambda P: 0.5 * P ** (22 / 48) >= 15 * P ** (9 / 48),
        "st3a-flat": lambda P: 16 * P ** (1 / 48 + 0.5) + 30 * P**0.75 <= 46 * P**0.75,
        "st6D1-window": lambda P: P**0.5 >= 8 * (1 + 7 * P**0.25),
        "st6D1-good": lambda P: 72 * P**-0.5 <= 0.25,
        "5b-j0-window": lambda P: P**0.5 >= 56,
        "5b-Npieces": lambda P: 3 * P ** (1 / 24 + 0.5) + 2 + 22 * P ** (1 / 16 + 0.25)
        + 5 * P ** (1 / 3) <= 3.5 * P ** (13 / 24),
        "5b-lam0-range": lambda P: 2.44 * (1 + P**-0.25) * (1 + 1 / (3 * P**0.5)) ** 2 <= 2.6
        and 0.38 * (1 - P**-0.25) * (1 - 1 / (3 * P**0.5)) ** 2 >= 0.35,
        "39-c2": lambda P: (0.053 / 0.35) * P**-0.25 <= rho0,
        "39-c3": lambda P: (0.047 / 0.35) * P**-0.25 <= rho0,
        "39-c4": lambda P: (0.044 / 0.35) * P**-0.25 <= rho0,
        "39-beta": lambda P: (1.187 * 0.68 / 0.35) * P**-0.5 <= rho0,
        "39-wave": lambda P: (200 / 0.35) * P ** (-5 / 6) <= rho0,
        "5a-competitors": lambda P: max(1.3 * P**-0.125, 13 * P ** (-9 / 16),
                                        9 * P ** (-13 / 12), 3 * P**-0.125) <= 0.25,
        "5a-W<=c7S": lambda P: V(S5a(P), P, k) + E(P) <= c7 * S5a(P) / 2,
        "5b-W<=c7S": lambda P: V(S5b(P), P, k) + E(P) <= c7 * S5b(P) / 2,
        "5b-E<=c7S": lambda P: E(P) <= c7 * S5b(P) / 2,
        "thm63-rem": lambda P: P ** (43 / 96) <= P ** (1 - 1 / 96),
    }[tag]


def test_every_printed_threshold_is_solvable() -> None:
    rows = C.thresholds()
    assert len(rows) == 30
    assert all(r["log10_P_min"] is not None for r in rows), [
        r["tag"] for r in rows if r["log10_P_min"] is None
    ]


def test_p0_is_89e13_and_binds_at_the_lemma_3_9_hypothesis() -> None:
    cert = C.certificate()
    assert cert["binding"]["tag"] == "5b-W<=c7S"
    assert 8.8e13 < cert["P0"] < 9.0e13
    assert round(cert["P0"] / 1e13, 1) == 8.9  # the paper prints 8.9e13


def test_each_threshold_is_sharp_at_its_own_crossing() -> None:
    """Just below the reported value the inequality fails; just above it holds."""
    for r in C.thresholds():
        lg = r["log10_P_min"]
        if lg <= 0.0:  # holds for every P >= 1; nothing to straddle
            continue
        pred = _pred_for(r["tag"])
        assert pred(10.0 ** (lg + 0.01)), r["tag"]
        assert not pred(10.0 ** (lg - 0.01)), r["tag"]


def test_the_balance_comparisons_carry_the_threshold_alone() -> None:
    cert = C.certificate()
    # everything except the three Lemma 3.9 balance comparisons is satisfied far earlier
    assert 2.5e10 < cert["P0_excluding_lemma_3_9_balance"] < 3.5e10
    assert cert["binding_excluding_balance"]["tag"] == "s3s1-Bsmall"
    assert cert["P0"] / cert["P0_excluding_lemma_3_9_balance"] > 10**3


def test_superseded_normalisation_is_recovered() -> None:
    """kappa = 1/3 (the previous operating point) still gives 5.8e16."""
    cert = C.certificate()
    assert 5.5e16 < cert["P0_at_superseded_kappa"] < 6.1e16


# ----------------------------------------------------------------------------------------------
# The two constants: c_7 (Appendix A.5) and the interpolant error E
# ----------------------------------------------------------------------------------------------


def test_step5b_triple_gives_exactly_1_over_232() -> None:
    from fractions import Fraction as Fr

    assert C.c7_of_triple(C.STEP5B_TRIPLE) == Fr(1, 232)
    assert [sum(r) for r in C.minv_abs(C.STEP5B_TRIPLE)] == [110, 232, 123]


def test_c7_scales_as_the_square_of_the_exponent_gap() -> None:
    from fractions import Fraction as Fr

    ratios = []
    for d in (Fr(1, 8), Fr(1, 4), Fr(1, 2)):
        t = (Fr(-5, 8) - d + 2, Fr(-5, 8) + 2, Fr(-5, 8) + d + 2)
        ratios.append((d * d) / C.c7_of_triple(t))
    assert all(Fr(33, 10) <= r <= Fr(39, 10) for r in ratios), ratios
    assert ratios[0] == Fr(29, 8)  # exact at the Step 5b centre and gap


def test_the_uniform_choice_saturates_the_middle_row_so_c7_is_not_free() -> None:
    assert sum(C.MINV_ABS[1]) == 232
    assert C.vector_feasible(C.C7, C.C7, C.C7)
    assert not C.vector_feasible(C.C7 * 1.01, C.C7, C.C7)
    assert abs(C.max_c2(0.0, 0.0) - 1 / 24) < 1e-12
    assert C.max_c2() / C.C7 < 10  # the whole available gain is under a factor ten


def test_raising_c2_still_moves_cost_from_P0_to_P1() -> None:
    lever = C.c7_lever()
    cur, raised = lever["current"], lever["c2_raised"]
    assert raised["P0"] < cur["P0"]          # P_0 improves
    assert raised["P1"] > cur["P1"] * 1e3    # P_1 degrades by more than three orders
    assert cur["P1"] > cur["P0"]             # P_1 is the larger threshold either way


def test_interpolant_error_is_106_not_219() -> None:
    """52.89 k(h1+h2) P^-9/8 with k(h1+h2) <= 2 P^(1/12): 52.3125 from (i) plus 0.567 from (ii)."""
    # (i) is exactly (9/32)*186 = 52.3125 -- so it prints as 52.32, not 52.3
    assert abs((9 / 32) * 186 - 52.3125) < 1e-9
    # (ii) is (135/1024)*4.3 = 0.567, printed 0.57; 0.6 would push the sum past 52.9
    assert abs((135 / 1024) * 4.3 - 0.5669) < 1e-3
    assert (9 / 32) * 186 + 0.6 > 52.9
    assert (9 / 32) * 186 + 0.57 <= 52.9
    # 2 * 52.8795 = 105.759, printed 105.8 <= 106
    assert abs(2 * ((9 / 32) * 186 + (135 / 1024) * 4.3) - 105.759) < 1e-2
    assert 2 * ((9 / 32) * 186 + (135 / 1024) * 4.3) <= 105.8 <= 106
    # the factor ~2.07 is on the P^(-25/24) coefficient, not on the total: the second term
    # 0.11 P^(-5/6) is untouched and is co-dominant near P_0, so the total gains only ~1.6 there.
    assert 2.0 < 219 / 105.8 < 2.1
    for P in (1e14, 1e16, 1e20):
        assert C.interpolant_error(P) < C.interpolant_error_superseded(P)
    assert 1.5 < C.interpolant_error_superseded(8.93e13) / C.interpolant_error(8.93e13) < 1.7


def test_the_middle_band_cap_is_the_band_condition_itself() -> None:
    """mu <= 60 lambda_0 with mu = 0.84 max(u h1, u' h2)P^-3/4, lambda_0 <= 2.6 k h1 h2 P^-5/8."""
    assert abs(60 * 2.6 / 0.84 - 185.7) < 0.1


# ----------------------------------------------------------------------------------------------
# P_1: the point at which the middle band beats the trivial bound
# ----------------------------------------------------------------------------------------------


def test_P1_is_computed_from_three_different_exponents() -> None:
    """r=3 is P^(41/48), the other two P^(89/96); collecting them over-counts r=3 by P^(7/96)."""
    # far above P_0, where V dominates W, the r=3 slope is 41/48 and the boundary slope 89/96
    r3, _r4, bd = C.middle_band_cost(C.KAPPA, 1e40)
    r3b, _r4b, bdb = C.middle_band_cost(C.KAPPA, 1e41)
    assert math.isclose(math.log10(r3b / r3), 41 / 48, rel_tol=0.02)
    assert math.isclose(math.log10(bdb / bd), 89 / 96, rel_tol=0.02)
    # near P_0 the r=3 term is still E-dominated, so its slope sits between 19/24 and 41/48
    lo, hi = C.middle_band_cost(C.KAPPA, 1e14)[0], C.middle_band_cost(C.KAPPA, 1e15)[0]
    assert 19 / 24 < math.log10(hi / lo) < 41 / 48
    assert 4.5e19 < 10 ** C.log10_P1(C.KAPPA) < 5.5e19


def test_kappa_now_moves_P0_and_P1_together() -> None:
    """Under the raised threshold W = V + E the two thresholds stop fighting."""
    at13 = C.kappa_tradeoff(1 / 3)
    at12 = C.kappa_tradeoff(1 / 12)
    assert at12["P_min"] < at13["P_min"] / 100   # P_0 improves by more than two orders
    assert at12["P1"] < at13["P1"] / 10          # and P_1 improves too
    # 1/12 is the turning point: further down, P_1 rises again
    assert C.kappa_tradeoff(1 / 20)["P1"] > at12["P1"]
    assert C.kappa_tradeoff(1 / 20)["P_min"] < at12["P_min"]


def test_P1_exceeds_P0_but_both_are_finite() -> None:
    cert = C.certificate()
    assert cert["P0"] < cert["P1_nontrivial"]
    assert cert["P1_nontrivial"] < 1e21


# ----------------------------------------------------------------------------------------------
# epsilon and rendering
# ----------------------------------------------------------------------------------------------


def test_log_absorption_is_astronomically_larger_and_excluded() -> None:
    cert = C.certificate()
    for row in cert["log_absorption_not_required"]:
        assert row["P_min"] is None or row["P_min"] > 1e100
    assert cert["P0"] < 1e14


def test_weyl_steps_halve_the_log_power_twice() -> None:
    assert 3.0 / 2 / 2 == 0.75
    powers = [r["log_power"] for r in C.log_absorption_thresholds()]
    assert 0.75 in powers and 3.75 in powers


def test_certificate_table_renders_every_row() -> None:
    cert = C.certificate()
    md = C.markdown_table(cert["thresholds"])
    # header + rule + one line per row, joined: rows + 2 lines, hence rows + 1 newlines
    assert md.count("\n") == len(cert["thresholds"]) + 1
    assert "always" in md  # the three unconditional rows
    assert math.isclose(cert["log10_P0"], math.log10(cert["P0"]))


# ----------------------------------------------------------------------------------------------
# Cross-check against the Lean certificate (formal/Problems/Juggler/ThresholdCertificate.lean)
# ----------------------------------------------------------------------------------------------

# (probe tag, Lean theorem, substitution exponent n with P = t^n, rational threshold t0).
# Every exponent in the paper lies in (1/96)Z, so each row is polynomial in t and needs no rpow.
LEAN_ROWS = [
    ("s3s1-window",    "row_s3s1_window",     2, 12),
    ("s3s1-Bsmall",    "row_s3s1_Bsmall",    16, 4.6),
    ("s3s2-window",    "row_s3s2_window",     4, 19),
    ("s3s2-flat",      "row_s3s2_flat",       4, 8),
    ("s3s2-wincount",  "row_s3s2_wincount",   4, 20),
    ("s3s2-bdry",      "row_s3s2_bdry_a",    32, 1.46),
    ("s3s2-bdry",      "row_s3s2_bdry_b",    32, 1.46),
    ("stage2-modecurv","row_stage2_modecurv", 8, 10.26),
    ("stage5-band",    "row_stage5_band",     2, 15),
    ("claimC-1",       "row_claimC_1",       72, 1.17),
    ("claimC-2",       "row_claimC_2",       36, 1.34),
    ("claimG-pref",    "row_claimG_pref",    24, 2.5),
    ("claimG-P36",     "row_claimG_P36",     36, 1),
    ("st3a-window",    "row_st3a_window",    48, 1.3),
    ("st3b-window",    "row_st3b_window",    48, 1.3),
    ("st3a-flat",      "row_st3a_flat",      48, 1),
    ("st6D1-window",   "row_st6D1_window",    4, 57),
    ("st6D1-good",     "row_st6D1_good",      2, 288),
    ("5b-j0-window",   "row_5b_j0_window",    2, 56),
    ("5b-Npieces",     "row_5b_Npieces",     48, 1.46),
    ("5b-lam0-range",  "row_5b_lam0_upper",   4, 17),
    ("5b-lam0-range",  "row_5b_lam0_lower",   4, 17),
    ("39-c2",          "row_39_c2",           4, 282),
    ("39-c3",          "row_39_c3",           4, 250),
    ("39-c4",          "row_39_c4",           4, 234),
    ("39-beta",        "row_39_beta",         2, 4288),
    ("39-wave",        "row_39_wave",         6, 16.1),
    ("5a-competitors", "row_5a_competitors",  48, 1.52),
    ("5a-W<=c7S",      "row_5a_binding",     48, 1.89),
    ("5b-W<=c7S",      "row_5b_binding",     48, 1.96),
    ("5b-E<=c7S",      "row_5b_E_only",      48, 1.85),
    ("thm63-rem",      "row_thm63_rem",      96, 1),
]

_LEAN_FILE = "formal/Problems/Juggler/ThresholdCertificate.lean"


def _lean_source() -> str:
    import pathlib

    root = pathlib.Path(__file__).resolve().parents[3]
    return (root / _LEAN_FILE).read_text(encoding="utf-8")


def test_every_probe_row_has_a_lean_theorem() -> None:
    covered = {tag for tag, _thm, _n, _t0 in LEAN_ROWS}
    probe = {r["tag"] for r in C.thresholds()}
    assert covered == probe, (probe - covered, covered - probe)


def test_lean_theorems_exist_by_name() -> None:
    src = _lean_source()
    for _tag, thm, _n, _t0 in LEAN_ROWS:
        assert "theorem %s " % thm in src, thm


def test_lean_thresholds_cover_the_probe_thresholds() -> None:
    """Each Lean row's rational t0^n must be at or above the probe's bisected P."""
    probe = {r["tag"]: r["P_min"] for r in C.thresholds()}
    for tag, thm, n, t0 in LEAN_ROWS:
        assert t0**n >= probe[tag] * (1 - 1e-9), (thm, t0**n, probe[tag])


def test_the_lean_certified_P0_is_the_binding_row() -> None:
    """max over the Lean rows is row_5b_binding at 1.96^48 = 1.07e14."""
    worst = max(LEAN_ROWS, key=lambda r: r[3] ** r[2])
    assert worst[1] == "row_5b_binding"
    assert 1.0e14 < worst[3] ** worst[2] < 1.1e14
    # conservative by under 20% against the probe's 8.95e13
    assert 1.0 < (worst[3] ** worst[2]) / C.certificate()["P0"] < 1.25
