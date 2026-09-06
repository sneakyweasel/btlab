"""Effective threshold certificate for Paper B: P_0 = 3.6e13, binding at Step 5b's W <= c_7 S/2."""

from __future__ import annotations

import io
import math
import random
from fractions import Fraction as Fr
from pathlib import Path

import pytest

from research.juggler_sequence import decoration_budget as D
from research.juggler_sequence import p0_certificate as C

ROOT = Path(__file__).resolve().parents[3]
PAPER = ROOT / "docs" / "theory" / "juggler_parity_discrepancy_note.md"


def _pred_for(tag: str):
    """The printed inequalities, transcribed independently of the module's own list."""
    S5b = lambda P: 0.56 * P**-0.625  # noqa: E731  the corrected lambda_0 floor
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
        "st6D1-window": lambda P: P**0.5 >= 8 * (1 + 5 * P**0.25),
        "st6D1-good": lambda P: 72 * P**-0.5 <= 0.25,
        "st6D1-modeindex": lambda P: 5 * P**0.25 <= P ** (5 / 16),
        "5b-j0-window": lambda P: P**0.5 >= 56,
        "5b-Npieces": lambda P: 3 * P ** (1 / 24 + 0.5) + 2 + 22 * P ** (1 / 16 + 0.25)
        + 5 * P ** (1 / 3) <= 3.5 * P ** (13 / 24),
        "5b-lam0-range": lambda P: 3.90 * (1 + P**-0.25) * (1 + 1 / (3 * P**0.5)) ** 2 <= 4.2
        and 0.62 * (1 - P**-0.25) * (1 - 1 / (3 * P**0.5)) ** 2 >= 0.56,
        "39-c2": lambda P: (0.053 / 0.56) * P**-0.25 <= rho0,
        "39-c3": lambda P: (0.047 / 0.56) * P**-0.25 <= rho0,
        "39-c4": lambda P: (0.044 / 0.56) * P**-0.25 <= rho0,
        "39-beta": lambda P: (1.898 * 0.68 / 0.56) * P**-0.5 <= rho0,
        "39-wave": lambda P: (300 / 0.56) * P ** (-5 / 6) <= rho0,
        "5a-competitors": lambda P: max(1.3 * P**-0.125, 13 * P ** (-9 / 16),
                                        9 * P ** (-13 / 12), 3 * P**-0.125) <= 0.25,
        "5a-W<=c7S": lambda P: V(S5a(P), P, k) + E(P) <= c7 * S5a(P) / 2,
        "5b-W<=c7S": lambda P: V(S5b(P), P, k) + E(P) <= c7 * S5b(P) / 2,
        "5b-E<=c7S": lambda P: E(P) <= c7 * S5b(P) / 2,
        "claimD-shift": lambda P: 1.45 * P ** (7 / 72) <= P ** (1 / 8),
        "st3a-flatcost": lambda P: 23 * P ** (19 / 24) <= P ** (23 / 24),
        "t61-stepB-discard": lambda P: 1.5 * math.pi * P ** (1 / 96 - 1 / 8) <= 1,
        "st2-collision": lambda P: 3 * P ** (5 / 16 / 2 + 3 / 4) <= P ** (23 / 24),
        "st5b-qpp": lambda P: (1.85 * P ** (7 / 24) + P ** (5 / 16)) * 6 * P ** (-5 / 4)
        / (0.35 * P**-0.75) <= 0.25,
        "t63-window": lambda P: P ** (5 / 16) >= 8 * (1 + C.depth5_C_max(P)),
        "t63-flat": lambda P: 8 * (1 + C.depth5_C_max(P)) / P ** (5 / 16) <= P ** (-1 / 96),
        "thm63-rem": lambda P: P ** (43 / 96) <= P ** (1 - 1 / 96),
    }[tag]


def test_every_printed_threshold_is_solvable() -> None:
    rows = C.thresholds()
    assert len(rows) == 38
    assert all(r["log10_P_min"] is not None for r in rows), [
        r["tag"] for r in rows if r["log10_P_min"] is None
    ]


def test_p0_is_36e13_and_binds_at_the_lemma_3_9_hypothesis() -> None:
    cert = C.certificate()
    assert cert["binding"]["tag"] == "5b-W<=c7S"
    assert 3.5e13 < cert["P0"] < 3.7e13
    assert round(cert["P0"] / 1e13, 1) == 3.6  # the paper prints 3.6e13
    # under the pre-correction anchor of the erratum at Lemma 5.2b it was 8.9e13
    pre = C.thresholds(anchor=C.ANCHOR_CONSTANTS_PRECORRECTION)
    old = max(r["P_min"] for r in pre if r["P_min"])
    assert 8.8e13 < old < 9.0e13


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
    # They do -- but only because Lemma 5.1(iii)'s offset bound is 2 and not the printed 3.
    # At |j| <= 3 the widened mode index stands at 7^16 and takes this row; at |j| <= 2 it is
    # 5^16, an order under the q'' ratio, and the balance comparisons carry P_0 alone again.
    assert cert["binding_excluding_balance"]["tag"] == "st5b-qpp"
    assert abs(cert["P0_excluding_lemma_3_9_balance"] / 2.9817e11 - 1) < 1e-3
    assert cert["P0"] / cert["P0_excluding_lemma_3_9_balance"] > 100
    assert 7.0**16 > cert["P0_excluding_lemma_3_9_balance"] > 5.0**16

    # and the soft regime-naming inequality still sets the floor for the rest
    rest = [r for r in cert["thresholds"]
            if r["tag"] not in {"5a-W<=c7S", "5b-W<=c7S", "5b-E<=c7S", "st5b-qpp",
                                "st6D1-modeindex"}]
    assert max(rest, key=lambda r: r["log10_P_min"])["tag"] == "s3s1-Bsmall"


def test_superseded_normalisation_is_recovered() -> None:
    """kappa = 1/3 (the previous operating point) gives 1.2e16 under the corrected anchor."""
    cert = C.certificate()
    assert 1.1e16 < cert["P0_at_superseded_kappa"] < 1.3e16


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
    assert raised["P1"] > cur["P1"] * 1e3    # P_1 still degrades by three orders
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
    assert 1.27 < 219 / 170.6 < 1.29
    for P in (1e14, 1e16, 1e20):
        assert C.interpolant_error(P) < C.interpolant_error_superseded(P)
    P0 = C.certificate()["P0"]
    assert 1.15 < C.interpolant_error_superseded(P0) / C.interpolant_error(P0) < 1.25


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
    lo, hi = C.middle_band_cost(C.KAPPA, 1e15)[0], C.middle_band_cost(C.KAPPA, 1e16)[0]
    assert 19 / 24 < math.log10(hi / lo) < 41 / 48
    assert 9.5e18 < 10 ** C.log10_P1(C.KAPPA) < 1.05e19


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
    ("st6D1-window",   "row_st6D1_window",    4, 41),
    ("st6D1-good",     "row_st6D1_good",      2, 288),
    ("st6D1-modeindex","row_st6D1_modeindex",16, 5),
    ("5b-j0-window",   "row_5b_j0_window",    2, 56),
    ("5b-Npieces",     "row_5b_Npieces",     48, 1.46),
    ("5b-lam0-range",  "row_5b_lam0_upper",   4, 17),
    ("5b-lam0-range",  "row_5b_lam0_lower",   4, 17),
    ("39-c2",          "row_39_c2",           4, 176),
    ("39-c3",          "row_39_c3",           4, 156),
    ("39-c4",          "row_39_c4",           4, 146),
    ("39-beta",        "row_39_beta",         2, 4288),
    ("39-wave",        "row_39_wave",         6, 15.9),
    ("5a-competitors", "row_5a_competitors",  48, 1.52),
    ("5a-W<=c7S",      "row_5a_binding",     48, 1.91),
    ("5b-W<=c7S",      "row_5b_binding",     48, 1.92),
    ("5b-E<=c7S",      "row_5b_E_only",      48, 1.84),
    ("thm63-rem",      "row_thm63_rem",      96, 1),
    ("claimD-shift",    "claimD_shift_range", 72, 1.205),
    ("st3a-flatcost",   "st3a_flat_cost",     24, 2.19),
    ("t61-stepB-discard", "stepB_discard",    96, 1.16),
    ("st2-collision",   "row_st2_collision",  96, 1.25),
    ("st5b-qpp",        "row_st5b_qpp",       96, 1.32),
    ("t63-window",      "row_t63_window",     96, 1.24),
    ("t63-flat",        "row_t63_flat",       96, 1.27),
]

_LEAN_FILES = (
    "formal/Problems/Juggler/ThresholdCertificate.lean",
    "formal/Problems/Juggler/DepthFourFive.lean",
)


def _lean_source() -> str:
    import pathlib

    root = pathlib.Path(__file__).resolve().parents[3]
    return chr(10).join((root / f).read_text(encoding="utf-8") for f in _LEAN_FILES)


def test_every_probe_row_has_a_lean_theorem() -> None:
    covered = {tag for tag, _thm, _n, _t0 in LEAN_ROWS}
    probe = {r["tag"] for r in C.thresholds()}
    assert covered == probe, (probe - covered, covered - probe)


def test_lean_theorems_exist_by_name() -> None:
    src = _lean_source()
    for _tag, thm, _n, _t0 in LEAN_ROWS:
        assert "theorem %s " % thm in src, thm


def test_lean_thresholds_cover_the_probe_thresholds() -> None:
    """Each Lean row's rational t0^n must be at or above the probe's bisected P.

    Regenerated against the corrected table of the erratum at Lemma 5.2b: nine rows carry
    the anchor, and every one of them still admits a rational witness.
    """
    probe = {r["tag"]: r["P_min"] for r in C.thresholds()}
    for tag, thm, n, t0 in LEAN_ROWS:
        assert t0**n >= probe[tag] * (1 - 1e-9), (thm, t0**n, probe[tag])


def test_the_lean_certified_P0_is_the_binding_row() -> None:
    """max over the Lean rows is row_5b_binding at 1.92^48 = 4.0e13."""
    worst = max(LEAN_ROWS, key=lambda r: r[3] ** r[2])
    assert worst[1] == "row_5b_binding"
    assert 3.9e13 < worst[3] ** worst[2] < 4.1e13
    assert 1.0 < (worst[3] ** worst[2]) / C.certificate()["P0"] < 1.15
    # under the pre-correction anchor the same row read 1.96^48 = 1.07e14
    pre = C.thresholds(anchor=C.ANCHOR_CONSTANTS_PRECORRECTION)
    old_P0 = max(r["P_min"] for r in pre if r["P_min"])
    assert 1.0 < 1.96**48 / old_P0 < 1.25


# --- Stage 2's truncation R_0, which decides four rows ---


def test_R0_is_five_sixteenths() -> None:
    assert C.R0_EXPONENT == 5 / 16
    assert C.R0_EXPONENT_SUPERSEDED == 1 / 4


def test_the_superseded_R0_puts_two_sites_far_above_P0() -> None:
    """The finding: at R_0 = P^(1/4) the depth-five theorem needs 1.8e24."""
    P0 = C.certificate()["P0"]
    old = C.r0_tradeoff(C.R0_EXPONENT_SUPERSEDED)
    assert 2.5e19 < old["window"] < 2.6e19
    assert 1.8e24 < old["flat"] < 1.9e24
    assert old["worst"] > P0 * 1e9          # ten orders above P_0
    assert old["flat"] > old["window"]      # the flat cost is what binds


def test_the_adopted_R0_puts_every_site_under_P0() -> None:
    P0 = C.certificate()["P0"]
    new = C.r0_tradeoff(C.R0_EXPONENT)
    for site in ("collision", "qpp", "window", "flat"):
        assert new[site] < P0, (site, new[site])
    assert new["worst"] < P0 / 100          # and with two orders to spare


def test_five_sixteenths_is_the_optimum_of_the_trade() -> None:
    """Raising R_0 buys two sites and pays for two; 5/16 minimises the worst."""
    grid = [C.r0_tradeoff(a) for a in (1 / 4, 9 / 32, 5 / 16, 1 / 3, 3 / 8)]
    best = min(grid, key=lambda r: r["worst"])
    assert best["a"] == 5 / 16
    # the two neighbours are worse, in opposite directions
    by_a = {round(r["a"], 6): r for r in grid}
    assert by_a[round(9 / 32, 6)]["worst"] > best["worst"]   # window/flat too tight
    assert by_a[round(1 / 3, 6)]["worst"] > best["worst"]    # collision/q'' too loose


def test_P0_is_unchanged_by_the_substitution() -> None:
    cert = C.certificate()
    assert 3.5e13 < cert["P0"] < 3.7e13
    assert cert["binding"]["tag"] == "5b-W<=c7S"


def test_sharp_C_bound_is_inside_the_printed_one() -> None:
    for e in (10.0, 14.0, 19.0, 24.0):
        P = 10**e
        assert C.depth5_C_max(P) <= 2 * P ** (19 / 96)


def test_step_B_discard_costs_under_one_unit_at_P0() -> None:
    """The draft printed 7 P^(7/8); the true cost is (3 pi k/4) P^(-1/8) < 1."""
    import math

    P0 = C.certificate()["P0"]
    assert 1.5 * math.pi * P0 ** (1 / 96 - 1 / 8) < 1
    assert 1.5 * math.pi * P0 ** (1 / 96 - 1 / 8) < 7 * P0**0.875


# --- the stratification figures the manuscript prints ---


def _paper() -> str:
    import io
    from pathlib import Path
    root = Path(__file__).resolve().parents[3]
    return io.open(root / "docs" / "theory" / "juggler_parity_discrepancy_note.md",
                   encoding="utf-8").read()


def test_stratification_counts_four_exceptions_not_three() -> None:
    """Section 4 printed three exceptions and the four-exception figure.

    Excluding only the three Lemma 3.9 balance comparisons, the largest remaining site is the
    Step 5b(a) q'' curvature ratio at 2.98e11 -- far above the 2.9e10 the sentence claimed.
    2.8e10 is what holds once that fourth site is set aside too.
    """
    from research.juggler_sequence import p0_certificate as C

    th = C.certificate()["thresholds"]
    balance = [t for t in th if "c7S" in t["tag"]]
    assert len(balance) == 3, [t["tag"] for t in balance]

    rest = [t for t in th if "c7S" not in t["tag"]]
    worst = max(rest, key=lambda t: t["P_min"])
    assert worst["tag"] == "st5b-qpp"
    assert abs(worst["P_min"] / 2.9817e11 - 1) < 1e-3

    rest4 = [t for t in rest if t["tag"] != "st5b-qpp"]
    worst4 = max(rest4, key=lambda t: t["P_min"])
    assert worst4["tag"] == "st6D1-modeindex"          # 5^16, the row A.1 was missing
    assert abs(worst4["P_min"] / 5.0**16 - 1) < 1e-9

    rest5 = [t for t in rest4 if t["tag"] != "st6D1-modeindex"]
    worst5 = max(rest5, key=lambda t: t["P_min"])
    assert worst5["tag"] == "s3s1-Bsmall"
    assert abs(worst5["P_min"] / 2.8275e10 - 1) < 1e-3

    text = _paper()
    assert "except four holds" in text
    assert r"\(2.8\cdot10^{10}\)" in text
    assert r"\(2.9\cdot10^{10}\)" not in text
    assert "except the three\nLemma 3.9 balance comparisons" not in text


def test_appendix_a_and_section_4_agree_on_the_four() -> None:
    """Appendix A always had it right; the two passages must not drift apart again."""
    text = _paper()
    assert "Of the remaining five" in text
    for figure in (r"3.0\cdot10^{11}", "two orders"):
        assert text.count(figure) >= 2, figure     # stated in both places now


# --- c_7 in closed form, and a second implementation to check the first ---


def _c7_by_adjugate(triple):
    """Independent route: build M explicitly and invert by the adjugate.

    p0_certificate builds |M^{-1}| from Lagrange rows in the falling-factorial basis.  This does
    the plain 3x3 inverse instead, so agreement is a real cross-check rather than a restatement.
    """
    from fractions import Fraction as Fr
    x = [Fr(t) - 2 for t in triple]
    a, b, c = Fr(1), Fr(1), Fr(1)
    d, e, f = x
    g, h, i = [xi * (xi - 1) for xi in x]
    det = a * (e * i - f * h) - b * (d * i - f * g) + c * (d * h - e * g)
    adj = [[(e * i - f * h), -(b * i - c * h), (b * f - c * e)],
           [-(d * i - f * g), (a * i - c * g), -(a * f - c * d)],
           [(d * h - e * g), -(a * h - b * g), (a * e - b * d)]]
    rows = [[adj[r][s] / det for s in range(3)] for r in range(3)]
    return Fr(1) / max(sum(abs(v) for v in row) for row in rows)


@pytest.mark.parametrize("triple", [
    (Fr(5, 4), Fr(11, 8), Fr(3, 2)),
    (Fr(9, 8), Fr(5, 4), Fr(11, 8)),
    (Fr(3, 8), Fr(15, 8), Fr(27, 8)),
    (Fr(3, 8), Fr(9, 4), Fr(27, 8)),
])
def test_two_independent_inverses_agree(triple) -> None:
    assert C.c7_of_triple(triple) == _c7_by_adjugate(triple), triple


def test_the_closed_form_matches_the_matrix_wherever_it_applies() -> None:
    """delta^2/c_7 = x0^2 - 2 x0 + (2 - delta^2) on |x0| > delta, x0 < 1/2."""
    checked = 0
    for dk in range(1, 9):
        delta = Fr(dk, 8)
        for x0k in range(-40, 5):
            x0 = Fr(x0k, 8)
            if not C.c7_equally_spaced_applies(x0, delta):
                continue
            triple = (x0 - delta + 2, x0 + 2, x0 + delta + 2)
            if any(v in (0, 1, 2, 3) for v in triple) or not all(-4 <= v <= 4 for v in triple):
                continue
            assert C.c7_equally_spaced(x0, delta) == C.c7_of_triple(triple), (x0, delta)
            checked += 1
    assert checked > 100, checked


def test_the_additive_constant_is_two_minus_delta_squared() -> None:
    """The paper printed the band [1.75, 2]; it is exactly 2 - delta^2."""
    for delta, want in ((Fr(1, 2), Fr(7, 4)), (Fr(1, 4), Fr(31, 16)), (Fr(1, 8), Fr(127, 64))):
        assert 2 - delta * delta == want, delta
    assert Fr(7, 4) == min(2 - Fr(k, 8) ** 2 for k in range(1, 5))     # attained at delta = 1/2
    assert all(2 - Fr(k, 8) ** 2 < 2 for k in range(1, 9))             # never reaches 2


def test_closed_form_returns_the_two_constants_the_paper_names() -> None:
    assert C.c7_equally_spaced(Fr(-5, 8), Fr(1, 8)) == Fr(1, 232)     # Step 5b, proof-critical
    assert C.c7_equally_spaced(Fr(-3, 4), Fr(1, 8)) == Fr(1, 259)     # the inventory minimum


def test_paper_states_the_closed_form() -> None:
    text = io.open(PAPER, encoding="utf-8").read()
    assert r"c_7=\frac{\delta^2}{(x_0-1)^2+1-\delta^2}" in text
    assert r"exactly \(2-\delta^2\)" in text
    assert r"without reaching it" in text


# --- the c_7 lever has a ceiling, and R_0 has already been tuned to it ---


def test_the_floor_is_the_qpp_site() -> None:
    """Remove every c_7-dependent threshold and the largest left is Step 5b(a)'s q'' ratio."""
    r = C.c7_saturation()
    assert r["floor_tag"] == "st5b-qpp"
    assert abs(r["floor"] / 2.9817e11 - 1) < 1e-3, r["floor"]
    assert r["runner_up"][1] == "st6D1-modeindex"       # 5^16, and 7^16 would have taken it
    assert 1.9 < r["floor"] / r["runner_up"][0] < 2.0
    # the erratum at Lemma 5.2b did not move it: this row divides by Theorem 4.1's Stage-4
    # curvature 0.35 uh P^(-3/4), a different constant that happens to share the value
    pre = {x["tag"]: x["P_min"] for x in C.thresholds(anchor=C.ANCHOR_CONSTANTS_PRECORRECTION)}
    assert abs(pre["st5b-qpp"] / r["floor"] - 1) < 1e-9
    assert abs(pre["st6D1-modeindex"] / r["runner_up"][0] - 1) < 1e-9


def test_the_lever_saturates_near_one_over_sixty() -> None:
    """1/61 -- but only at |j| <= 2; at the printed |j| <= 3 the floor is 7^16 and it is 1/228."""
    r = C.c7_saturation()
    assert 60 < r["crossover_denom"] < 62, r["crossover_denom"]
    gate = lambda c: [x for x in C.thresholds(c7=c) if x["tag"] == "5b-W<=c7S"][0]["P_min"]
    lo, hi = C.C7, 1 / 40.0
    for _ in range(200):
        mid = (lo + hi) / 2
        lo, hi = (mid, hi) if gate(mid) > 7.0**16 else (lo, mid)
    assert 225 < 1 / hi < 230, 1 / hi
    # the erratum at Lemma 5.2b did not move the floor either
    pinned = [max(x["P_min"] for x in C.thresholds(c7=c) if x["P_min"])
              for c in (1 / 50.0, 1 / 30.0, 1 / 20.0)]
    assert all(abs(p / r["floor"] - 1) < 1e-6 for p in pinned), pinned


def test_the_whole_lever_is_worth_a_factor_of_one_hundred_and_twenty() -> None:
    """The printed 120 is right -- and needed two constants, only one of which was checked."""
    r = C.c7_saturation()
    assert abs(r["max_factor"] / 120.3 - 1) < 0.02, r["max_factor"]
    # A.5's vector trade realises 8.9 of it
    assert abs(r["P0"] / C.c7_lever()["c2_raised"]["P0"] / 8.9 - 1) < 0.05
    # it was 300 before the erratum, and fell only because P_0 did: the floor is unmoved
    pre = C.thresholds(anchor=C.ANCHOR_CONSTANTS_PRECORRECTION)
    old_P0 = max(x["P_min"] for x in pre if x["P_min"])
    assert abs((old_P0 / r["floor"]) / 300.0 - 1) < 0.02
    # at the printed offset bound the whole paragraph would read differently
    assert 7.0**16 / r["P0"] > 0.9 and 7.0**16 < r["P0"]


def test_five_sixteenths_is_best_of_the_tabulated_four_but_not_the_minimax() -> None:
    """A.6 tabulates four exponents and 5/16 wins among them; the continuum does better."""
    worsts = {a: C.r0_tradeoff(a)["worst"] for a in (0.25, 9 / 32, 5 / 16, 1 / 3)}
    assert min(worsts, key=lambda a: worsts[a]) == 5 / 16
    assert abs(worsts[5 / 16] / C.c7_saturation()["floor"] - 1) < 1e-3
    # but the flat/qpp crossing is lower and better
    lo, hi = 0.290, 0.310
    for _ in range(200):
        mid = (lo + hi) / 2
        r = C.r0_tradeoff(mid)
        lo, hi = (mid, hi) if r["flat"] > r["qpp"] else (lo, mid)
    assert abs(hi - 0.29919) < 1e-4, hi
    crossing = max(C.r0_tradeoff(hi)[k] for k in ("collision", "qpp", "window", "flat"))
    assert abs(crossing / 1.403e11 - 1) < 0.01, crossing
    assert 2.0 < worsts[5 / 16] / crossing < 2.3


def test_paper_states_the_saturation() -> None:
    text = io.open(PAPER, encoding="utf-8").read()
    assert "and it saturates, at a value" in text
    assert r"c_7=1/61" in text
    assert r"a factor of \(120\)" in text
    assert "Two constants had to be right for that paragraph" in text
    assert "feasible rather than optimal" in text


# --- the q'' site: the certificate is sharper than the printed constant ---


def test_the_printed_and_two_term_forms_differ_by_the_merge() -> None:
    """48.9 P^{-3/16} folds 1.85 P^{7/24} into P^{5/16}, losing P^{1/48}."""
    printed = 10 ** C.least_P(lambda P: 48.9 * P ** (-3 / 16) <= 0.25)
    two = 10 ** C.least_P(lambda P: (1.85 * P ** (7 / 24) + C.R0(P)) * 6 * P ** -1.25
                          / (0.35 * P ** -0.75) <= 0.25)
    assert abs(printed / 1.662e12 - 1) < 0.01, printed
    assert abs(two / 2.9817e11 - 1) < 0.01, two
    assert 5.4 < printed / two < 5.8, printed / two


def test_the_certificate_uses_the_two_term_form() -> None:
    """The floor of A.5 is 2.98e11, which is the sharper reading, not the printed one."""
    row = [r for r in C.thresholds() if r["tag"] == "st5b-qpp"][0]
    assert abs(row["P_min"] / 2.9817e11 - 1) < 1e-3, row["P_min"]
    assert abs(C.c7_saturation()["floor"] / row["P_min"] - 1) < 1e-9


def test_the_printed_constant_is_right_at_P0() -> None:
    """0.088 in the manuscript is 30.5 P^{-3/16} at P_0, and the merge costs 1.45 there."""
    P = C.certificate()["P0"]
    assert abs(48.9 * P ** (-3 / 16) - 0.14) < 0.005
    assert abs(17.1 / 0.35 - 48.9) < 0.05   # Theorem 4.1's Stage-4 curvature, not lambda_0
    merged, exact = 2.85 * P ** 0.3125, 1.85 * P ** (7 / 24) + P ** 0.3125
    assert abs(merged / exact - 1.45) < 0.01


@pytest.mark.parametrize("kw,want", [("A", 2.66), ("J", 5.04), ("F", -5.04), ("M", -5.04)])
def test_no_constant_at_the_qpp_site_is_slack(kw: str, want: float) -> None:
    """All four are forced by displayed derivations; the elasticities say which would matter."""
    import math

    def thr(A=1.85, J=6.0, F=0.35, M=0.25):
        return C.least_P(lambda P: (A * P ** (7 / 24) + C.R0(P)) * J * P ** -1.25
                         / (F * P ** -0.75) <= M)

    base = thr()
    got = (thr(**{kw: {"A": 1.85, "J": 6.0, "F": 0.35, "M": 0.25}[kw] * 1.1}) - base) \
        / math.log10(1.1)
    assert abs(got - want) < 0.05, (kw, got)


def test_paper_carries_the_two_term_form() -> None:
    text = io.open(PAPER, encoding="utf-8").read()
    assert "not the sharpest form available" in text
    assert r"2.98\cdot10^{11}" in text and r"1.66\cdot10^{12}" in text
    assert "the floor of Appendix A.5" in text


# --- Lemma 5.2(i): which of the five terms can ever be the largest ---


def _lemma_52i_terms(a: Fr, b: Fr, r0: Fr = Fr(5, 16)) -> dict:
    """Exponents of the five terms at u = P^a, h = P^b."""
    return {
        "T1": (a + b) / 2 + Fr(5, 8),
        "T2": (b - a) / 2 + Fr(7, 8),
        "T3": Fr(7, 8),
        "T4": Fr(1, 24) - (a + b) / 2 + Fr(7, 8),
        "T5": r0 / 2 + Fr(3, 4),
    }


def _admissible_vertices() -> list:
    """h <= P^{1/8}, uh <= P^{1/2}, u, h >= 1: the region's corners."""
    return [(Fr(0), Fr(0)), (Fr(0), Fr(1, 8)), (Fr(1, 2), Fr(0)), (Fr(3, 8), Fr(1, 8))]


def test_the_first_and_third_terms_are_never_the_largest() -> None:
    """Both peak at P^{7/8}, strictly under the fifth's P^{29/32}."""
    fifth = Fr(5, 16) / 2 + Fr(3, 4)
    assert fifth == Fr(29, 32)
    for key in ("T1", "T3"):
        peak = max(_lemma_52i_terms(a, b)[key] for a, b in _admissible_vertices())
        assert peak == Fr(7, 8), (key, peak)
        assert peak < fifth, key


def test_the_other_three_each_dominate_somewhere() -> None:
    assert _lemma_52i_terms(Fr(0), Fr(1, 8))["T2"] == Fr(15, 16)      # u = 1, h = P^{1/8}
    assert _lemma_52i_terms(Fr(0), Fr(0))["T4"] == Fr(11, 12)         # u = h = 1
    for key, at in (("T2", (Fr(0), Fr(1, 8))), ("T4", (Fr(0), Fr(0)))):
        t = _lemma_52i_terms(*at)
        assert t[key] == max(t.values()), key
    mid = _lemma_52i_terms(Fr(1, 4), Fr(1, 16))
    assert mid["T5"] == max(mid.values())


def test_at_the_earlier_truncation_the_fifth_is_absorbed_instead() -> None:
    """R_0 = P^{1/4} makes the fifth P^{7/8}, equal to the third -- the paper's own remark."""
    assert Fr(1, 4) / 2 + Fr(3, 4) == Fr(7, 8)
    assert _lemma_52i_terms(Fr(0), Fr(0), Fr(1, 4))["T5"] == Fr(7, 8)


def test_paper_states_the_three_term_reading() -> None:
    text = io.open(PAPER, encoding="utf-8").read()
    assert "The absorption runs both ways" in text
    assert "it is a three-term bound" in text
    assert r"P^{15/16}" in text and r"P^{11/12}" in text


# --- Lemma 5.2(ii): how much of the t-saving Step 4 actually spends ---


def _weight_sum(t: int, Q: int = 400) -> float:
    """sum over q1+q2+q3 = t of 1/(max(1,|q1|) max(1,|q2|) max(1,|q3|))."""
    total = 0.0
    for q1 in range(-Q, Q + 1):
        a = 1.0 / max(1, abs(q1))
        for q2 in range(-Q, Q + 1):
            q3 = t - q1 - q2
            if abs(q3) <= Q:
                total += a / max(1, abs(q2)) / max(1, abs(q3))
    return total


def test_the_inner_weight_sum_is_log_squared_over_t() -> None:
    """The shape the displayed bound assumes."""
    for t in (2, 5, 20, 50):
        w = _weight_sum(t)
        scaled = w * t / math.log(2 + t) ** 2
        assert 10 < scaled < 40, (t, scaled)


def test_without_a_t_saving_the_wave_piece_sum_diverges() -> None:
    """sum log^2(2+t)/t has no limit; the |t|^{-1/6} is load-bearing."""
    partial = [sum(math.log(2 + t) ** 2 / t for t in range(1, n)) for n in (10**4, 10**6)]
    assert partial[1] > partial[0] * 1.5           # still growing fast


def test_any_positive_saving_suffices() -> None:
    """1/6 is not consumed: delta > 0 is enough for convergence."""
    for delta in (1 / 6, 0.05, 0.01):
        tail = sum(math.log(2 + t) ** 2 / t ** (1 + delta) for t in range(10**6, 2 * 10**6))
        head = sum(math.log(2 + t) ** 2 / t ** (1 + delta) for t in range(1, 10**6))
        assert tail < head * 0.5, delta          # the tail is a shrinking fraction


def test_the_P_exponent_is_consumed_in_full() -> None:
    """1/96 = (1/4)(1/24) traces straight to P^{23/24}, unlike the t-exponent."""
    assert Fr(1, 4) * (1 - Fr(23, 24)) == Fr(1, 96)


def test_paper_states_what_the_t_saving_buys() -> None:
    text = io.open(PAPER, encoding="utf-8").read()
    assert r"The exponent \(\tfrac16\) is not consumed" in text
    assert r"some* power saving in \(t\)" in text
    assert "spent on convergence and nothing else" in text


# --- how far an improvement to Theorem 5.3 would carry ---


def test_the_shift_ranges_give_exactly_one_sixteenth() -> None:
    """H_1 = P^{1/48}, H_2 = P^{1/24}, so h1 h2 contributes 1/16."""
    assert Fr(1, 48) + Fr(1, 24) == Fr(1, 16)


def test_the_kernel_exponent_has_headroom_of_six() -> None:
    """Step C needs delta + 1/16 <= 1/8, so delta < 1/16 against the 1/96 in force."""
    limit = Fr(1, 8) - (Fr(1, 48) + Fr(1, 24))
    assert limit == Fr(1, 16)
    assert limit / Fr(1, 96) == 6
    for d in (Fr(1, 96), Fr(1, 32), Fr(1, 20), Fr(1, 16)):
        assert d + Fr(1, 16) <= Fr(1, 8), d
    assert Fr(1, 12) + Fr(1, 16) > Fr(1, 8)          # past the limit


def test_the_truncation_balances_the_kernel_bound() -> None:
    """J_3 = P^{1/96} makes the majorant 4P/J_3 = 4P^{1-1/96}, matching K_c."""
    delta = Fr(1, 96)
    assert 1 - delta == Fr(95, 96)
    assert (1 - delta) == 1 - delta                  # majorant exponent == kernel exponent


def test_paper_records_where_the_value_is_spent() -> None:
    text = io.open(PAPER, encoding="utf-8").read()
    assert "is where Theorem 5.3's" in text
    assert "headroom along this route is zero" in text
    assert "Nothing after this theorem consumes the value" in text


# --- what actually pins the kernel exponent: (C4), not (C1) ---


def test_the_shift_ranges_are_determined_by_lemma_52ii() -> None:
    """H_2 = P^{delta_0}, H_1 = P^{delta_0/2}, kernel saving delta_0/4."""
    from research.juggler_sequence import paper_b_prefix_count as PB
    r = PB.differencing_chain(Fr(1, 24))
    assert (r["H1"], r["H2"], r["saving"]) == (Fr(1, 48), Fr(1, 24), Fr(1, 96))


def test_C4_is_tight_and_C1_is_not() -> None:
    """H_2 sits exactly at (C4)'s cap; the Step C load has 5/96 of (C1) to spare."""
    from research.juggler_sequence import paper_b_prefix_count as PB
    r = PB.differencing_chain(Fr(1, 24))
    assert r["H2"] == Fr(1, 24)                       # (C4) cap, zero slack
    assert Fr(1, 24) - r["H1"] == Fr(1, 48)           # H_1 has room
    load = r["saving"] + r["H1"] + r["H2"]
    assert load == Fr(7, 96)
    assert Fr(1, 8) - load == Fr(5, 96)               # (C1) never binds


def test_delta_zero_has_no_headroom() -> None:
    """Any delta_0 > 1/24 puts H_2 outside (C4), long before (C1) would complain."""
    from research.juggler_sequence import paper_b_prefix_count as PB
    for d0 in (Fr(1, 22), Fr(1, 20), Fr(1, 14)):
        r = PB.differencing_chain(d0)
        assert r["H2"] > Fr(1, 24), d0                       # (C4) already violated
        assert r["saving"] + r["H1"] + r["H2"] <= Fr(1, 8), d0   # (C1) still fine


def test_C1_is_the_product_of_the_three_caps() -> None:
    assert 3 * Fr(1, 24) == Fr(1, 8)


def test_paper_locates_the_binding_condition_at_C4() -> None:
    text = io.open(PAPER, encoding="utf-8").read()
    assert "What pins it is (C4)." in text
    assert "The\nheadroom along this route is zero." in text or "headroom along this route is zero" in text
    assert "Tight over the\ndomain, slack at every invocation." in text \
        or "slack at every invocation" in text
    assert "to\nthe decoration budget" in text or "the decoration budget" in text


# --- the chain closes at (D1), and every link but (C1) is tight ---


def test_D1s_cap_produces_lemma_52i_fourth_term() -> None:
    """5.1 h' with h' <= 2P^{1/24} gives the printed 11 P^{1/24}; the cap is used."""
    assert 5.1 * 2 <= 11                      # printed constant, rounded up from 10.2
    assert _lemma_52i_terms(Fr(0), Fr(0))["T4"] == Fr(11, 12)


def test_the_fourth_term_exceeds_the_fifth_by_the_kernel_exponent() -> None:
    """11/12 - 29/32 = 1/96, at u = h = 1."""
    t = _lemma_52i_terms(Fr(0), Fr(0))
    assert t["T4"] - t["T5"] == Fr(1, 96)
    assert t["T4"] == max(t.values())         # and it is the one that leads there


def test_that_identity_is_R0_equals_five_sixteenths() -> None:
    """Solving 1/24 + 1/8 - R/2 = 1/96 returns the truncation A.6 picks by minimax."""
    assert 2 * (Fr(1, 24) + Fr(1, 8) - Fr(1, 96)) == Fr(5, 16)


def test_every_link_but_C1_is_tight() -> None:
    from research.juggler_sequence import paper_b_prefix_count as PB
    r = PB.differencing_chain(Fr(1, 24))
    assert Fr(1, 24) - r["H2"] == 0                              # (C4) exact
    load = r["saving"] + r["H1"] + r["H2"]
    assert Fr(1, 8) - load == Fr(5, 96)                          # (C1) alone has slack
    t = _lemma_52i_terms(Fr(0), Fr(0))
    assert t["T4"] > t["T5"]                                     # (D1)'s term leads


def test_paper_records_the_closed_chain() -> None:
    text = io.open(PAPER, encoding="utf-8").read()
    assert "The chain closes at (D1), tightly." in text
    assert "not merely at a corner of the" in text
    assert "without claiming a mechanism for it" in text


def test_A6s_actual_claim_is_feasibility_and_holds_over_a_band() -> None:
    """All four sites below P_0 -- true across roughly a in [0.283, 0.34]."""
    def worst(a):
        return max(C.r0_tradeoff(a)[k] for k in ("collision", "qpp", "window", "flat"))
    for a in (0.2825, 0.2850, 0.2996, 0.3125, 0.33):
        assert worst(a) < 8.946e13, a
    for a in (0.2750, 0.2800, 0.3500):
        assert worst(a) > 8.946e13, a


def test_paper_no_longer_calls_five_sixteenths_the_minimax() -> None:
    text = io.open(PAPER, encoding="utf-8").read()
    assert "**That crossing is infeasible.**" in text
    assert "0.29919" in text
    assert "feasible rather than optimal" in text
    assert "coincidence of a feasible choice" in text


# --- the crossing is transcendental, and the loss around it is lopsided ---


def _crossing(scale_flat: float = 1.0, scale_qpp: float = 1.0) -> float:
    lo, hi = 0.270, 0.330
    for _ in range(200):
        mid = (lo + hi) / 2
        r = C.r0_tradeoff(mid)
        lo, hi = (mid, hi) if r["flat"] * scale_flat > r["qpp"] * scale_qpp else (lo, mid)
    return hi


def _worst(a: float) -> float:
    return max(C.r0_tradeoff(a)[k] for k in ("collision", "qpp", "window", "flat"))


def test_three_tenths_is_the_nearest_simple_value() -> None:
    star = _crossing()
    assert abs(star - 0.2991907844) < 1e-8
    assert abs(0.3 - star) < 1e-3
    assert _worst(0.3) / _worst(star) < 1.05           # within 4% of optimal
    assert 2.0 < _worst(0.3125) / _worst(star) < 2.3   # 5/16 costs 2.13


def test_the_loss_is_steeply_asymmetric_about_the_crossing() -> None:
    """Below the crossing the flat cost explodes; above it the q'' ratio rises gently."""
    star = _worst(_crossing())
    assert _worst(2 / 7) / star > 50                   # 0.2857, far below
    assert _worst(0.3125) / star < 3                   # 5/16, above
    assert _worst(2 / 7) > _worst(0.3125) * 20


def test_five_sixteenths_has_five_times_the_margin_of_three_tenths() -> None:
    base = _crossing()
    assert 0.3 > _crossing(scale_flat=1.25) and 0.3 > _crossing(scale_qpp=0.8)
    assert 0.3 < _crossing(scale_flat=2.0)             # 3/10 falls below at a doubling
    assert 0.3125 > _crossing(scale_flat=5.0)          # 5/16 survives it
    assert (0.3125 - base) / (0.3 - base) > 10


def test_paper_states_the_robustness_reading() -> None:
    text = io.open(PAPER, encoding="utf-8").read()
    assert "solves a transcendental equation" in text
    assert "the loss is steeply asymmetric" in text
    assert "the robust choice rather than the optimal one against all five sites," in text
    assert "The fifth site does not overturn that reading, and came close to." in text


# --- the chain quarters the saving and the log power by one mechanism ---


def test_the_chain_carries_the_log_exponent() -> None:
    """Mode masses O(log^3 P) leave as log^{3/4} P, alongside 1/24 -> 1/96."""
    from research.juggler_sequence import paper_b_prefix_count as PB
    r = PB.differencing_chain(Fr(1, 24))
    assert r["saving"] == Fr(1, 96)
    assert r["log_exponent"] == Fr(3, 4)


def test_both_are_the_same_quartering() -> None:
    from research.juggler_sequence import paper_b_prefix_count as PB
    r = PB.differencing_chain(Fr(1, 24))
    assert r["saving"] / Fr(1, 24) == r["log_exponent"] / Fr(3) == Fr(1, 4)


@pytest.mark.parametrize("rounds,factor", [(1, Fr(1, 2)), (2, Fr(1, 4)), (3, Fr(1, 8))])
def test_each_round_halves_both(rounds: int, factor: Fr) -> None:
    from research.juggler_sequence import paper_b_prefix_count as PB
    r = PB.differencing_chain(Fr(1, 24), rounds)
    assert r["saving"] == Fr(1, 24) * factor
    assert r["log_exponent"] == Fr(3) * factor


def test_the_abstract_and_A3_agree_on_the_log_form() -> None:
    text = io.open(PAPER, encoding="utf-8").read()
    assert r"K_c\ll P^{1-1/96}\log^{3/4}P" in text            # abstract
    assert r"K_c(P)\ll P^{1-1/96}(\log P)^{3/4}" in text      # A.3
    assert "one\nquartering, not two coincidences" in text or "not two coincidences" in text


# --- what Proposition 7.4 delivers, quantified ---


def test_the_no_log_loss_condition_holds_by_a_wide_margin() -> None:
    """A'_min ~ P^{11/16} against log P at P_0."""
    P0 = C.certificate()["P0"]
    amin = P0 ** (11 / 16)
    assert abs(amin / 2.08e9 - 1) < 0.05
    assert 30 < math.log(P0) < 34
    assert amin / math.log(P0) > 1e7


@pytest.mark.parametrize("delta,exponent", [(Fr(1, 96), Fr(-47, 48)), (Fr(1, 24), Fr(-11, 12))])
def test_the_exceptional_shift_measure(delta: Fr, exponent: Fr) -> None:
    """|S| <= P^{1-delta} outside a set of measure P^{2 delta - 1}."""
    assert 2 * delta - 1 == exponent
    P0 = C.certificate()["P0"]
    assert P0 ** float(exponent) < 1e-12


def test_the_measure_at_the_level_two_saving_is_five_times_ten_to_the_minus_fourteen() -> None:
    P0 = C.certificate()["P0"]
    assert abs(P0 ** float(Fr(-47, 48)) / 5.34e-14 - 1) < 0.05


def test_a_generic_shift_would_overshoot_by_forty_eight() -> None:
    """Square-root cancellation is delta = 1/2 against the kernel's own 1/96."""
    assert Fr(1, 2) / Fr(1, 96) == 48


def test_paper_states_the_measurement_and_disclaims_it() -> None:
    text = io.open(PAPER, encoding="utf-8").read()
    assert "the quantifier alone" in text
    assert "None of which is evidence." in text
    assert "a fact about the proposition and not about the" in text


# --- Lemma 5.2b: the zero-offset anchor is c(G_F - J_F), not c G_F ---


def test_the_three_terms_sum_to_the_printed_constant() -> None:
    """81 - 972 + 756 = -135: correct arithmetic about (cG_F)''."""
    assert sum(C.ANCHOR_TERMS) == Fr(-135, 1024)
    assert C.bare_anchor_curvature() == Fr(-135, 1024)
    assert C.ANCHOR_TERMS == (Fr(81, 1024), Fr(-972, 1024), Fr(756, 1024))


def test_the_anchor_drops_the_c2_G_term() -> None:
    """The phase is c(G_F - J_F) with J_F frozen, so c'' multiplies a quantity below 1."""
    assert C.anchor_curvature() == Fr(-216, 1024) == Fr(-27, 128)
    assert C.bare_anchor_curvature() - C.anchor_curvature() == C.ANCHOR_TERMS[0]
    assert C.anchor_curvature() / C.bare_anchor_curvature() == Fr(8, 5)
    # Step 5a makes the same subtraction correctly on the offset branch
    assert Fr(945, 512) - Fr(81, 512) == Fr(864, 512)
    # and after beta1 beta2 -> 9 h1 h2 nu
    assert 9 * C.anchor_curvature() == Fr(-243, 128)
    assert 9 * C.bare_anchor_curvature() == Fr(-1215, 1024)
    # the corrected interpolant coefficient
    assert Fr(-243, 128) * Fr(64, 33) == Fr(-81, 22)
    assert Fr(-81, 22) * Fr(11, 8) * Fr(3, 8) == Fr(-243, 128)


def test_the_moving_gap_foil_is_not_243_over_128() -> None:
    """F_sm = (27/4) h1h2 nu^{1/4} gives 2673/1024; 243/128 is the corrected anchor's magnitude."""
    assert C.moving_gap_curvature() == Fr(2673, 1024)
    assert C.moving_gap_curvature() != Fr(243, 128)
    assert 9 * abs(C.anchor_curvature()) == Fr(243, 128)


def test_the_anchor_curvature_is_measured_not_asserted() -> None:
    """(c(G_F-J_F))'' at P = 1e8 on real j=0 branches, against 216/1024."""
    from mpmath import mp
    from research.juggler_sequence.paper_b_audit import level1_data

    mp.dps = 50
    P = 10 ** 8
    rng = random.Random(3)
    H1, H2, K = int(P ** (1 / 48)), int(P ** (1 / 24)), int(P ** (1 / 24))
    bare, anchor = [], []
    for _ in range(400):
        if len(anchor) >= 5:
            break
        n = rng.randrange(P + 1, 2 * P) | 1
        h1, h2, k = rng.randint(1, max(1, H1)), rng.randint(1, max(1, H2)), rng.randint(1, max(1, K))
        b1, _, _ = level1_data(n, 2 * h1)
        b2, _, _ = level1_data(n, 2 * h2)
        b12, _, _ = level1_data(n, 2 * h1 + 2 * h2)
        if b12 - b1 - b2 != 0:
            continue
        nm, half = mp.mpf(n), mp.mpf(3) / 2

        def GF(nu: object, _b1: int = b1, _b2: int = b2, _b12: int = b12) -> object:
            Xn = mp.power(nu, half)
            return (mp.power(Xn + _b12, half) - mp.power(Xn + _b1, half)
                    - mp.power(Xn + _b2, half) + mp.power(Xn, half))

        cc = lambda nu, _k=k: mp.mpf(3 * _k) / 4 * mp.power(nu, mp.mpf(9) / 8)  # noqa: E731
        JF = mp.floor(GF(nm))
        unit = k * abs(b1 * b2) * mp.power(nm, -mp.mpf(13) / 8)
        bare.append(float(abs(mp.diff(lambda nu: cc(nu) * GF(nu), nm, 2)) / unit))
        anchor.append(float(abs(mp.diff(lambda nu: cc(nu) * (GF(nu) - JF), nm, 2)) / unit))

    assert len(anchor) == 5
    assert all(abs(x - 135 / 1024) < 1e-5 for x in bare), bare
    assert all(abs(x - 216 / 1024) < 1e-4 for x in anchor), anchor


def test_the_correction_lowers_P0_and_leaves_it_valid() -> None:
    """The printed rows reproduce 8.9e13; the corrected ones close at 3.6e13."""
    printed = C.corrected_certificate(C.bare_anchor_curvature(), (0.35, 2.6))
    assert abs(printed["P0"] / 8.9e13 - 1) < 0.02
    assert abs(printed["E_const"] - 105.6) < 0.2
    fixed = C.corrected_certificate()
    assert abs(fixed["P0"] / 3.6e13 - 1) < 0.02
    assert fixed["u_cap"] == 300.0
    assert abs(fixed["E_const"] - 170.6) < 0.2
    # lower, so the printed P_0 stays valid: every row is monotone in P
    assert fixed["P0"] < printed["P0"]
    assert fixed["P0"] < 8.9e13
    assert 2.4 < printed["P0"] / fixed["P0"] < 2.6


def test_the_lambda_0_range_moves_by_the_same_factor() -> None:
    """[0.38, 2.44] -> [0.62, 3.90], the exact bracket before the paper's opening."""
    lo, hi = C.anchor_range(C.bare_anchor_curvature())
    assert round(lo, 2) == 0.38 and round(hi, 2) == 2.44
    lo2, hi2 = C.anchor_range(C.anchor_curvature())
    assert round(lo2, 2) == 0.62 and round(hi2, 2) == 3.90
    assert abs((lo2 / lo) - 1.6) < 1e-9 and abs((hi2 / hi) - 1.6) < 1e-9


def test_ledger_and_paper_carry_the_erratum() -> None:
    paper = io.open(PAPER, encoding="utf-8").read()
    ledger = io.open(ROOT / "docs" / "theory" / "paper_b_audit_ledger.md", encoding="utf-8").read()
    assert "Erratum (constants only" in paper
    assert "216}{1024}" in paper and "27}{128}" in paper
    assert "2673}{1024}" in paper
    assert r"3.6\cdot10^{13}" in paper
    assert "the two errors concealed" in paper
    assert "ERRATUM (confirmed; constants only)" in ledger
    assert "2673/1024" in ledger or "2673}{1024}" in ledger


# --- Theorem 6.1 Step E: the zero-offset composite, derived ---


def test_the_smooth_half_is_675_over_2048() -> None:
    """DD((k/2) m^{9/4}) = b1b2 f''(X) with f'' = (45k/32) Z^{1/4}, curvature (45/32)(3/8)(-5/8)."""
    assert C.smooth_double_difference_curvature() == Fr(-675, 2048)
    assert Fr(1, 2) * Fr(9, 4) * Fr(5, 4) == Fr(45, 32)          # f''
    assert Fr(3, 2) * Fr(1, 4) == Fr(3, 8)                       # X^{1/4} = nu^{3/8}
    assert Fr(3, 8) * (Fr(3, 8) - 2) == Fr(-39, 64)              # not the curvature exponent pair
    assert Fr(3, 8) * (Fr(3, 8) - 1) == Fr(-15, 64)              # (3/8)(-5/8)


def test_step_e_zero_offset_is_three_to_the_seventh() -> None:
    """2187/2048, not the printed 1095/1024; and b' = -729/352, not -365/176."""
    assert C.step_e_zero_offset() == Fr(2187, 2048) == Fr(3 ** 7, 2 ** 11)
    assert C.step_e_interpolant_b() == Fr(-729, 352) == Fr(-3 ** 6, 352)
    assert C.step_e_interpolant_b() * Fr(11, 8) * Fr(3, 8) == -C.step_e_zero_offset()
    # one slip, 729 -> 730, carried into b' by the propagation the ledger had noticed
    assert Fr(1095, 1024) == Fr(2190, 2048)
    assert Fr(-365, 176) == Fr(-730, 352)
    assert Fr(2190, 2048) - Fr(2187, 2048) == Fr(3, 2048)


def test_step_e_is_nine_sixteenths_of_the_kernel_anchor() -> None:
    """A ratio in lowest terms, where the printed pair gave 1095/1215 = 73/81."""
    kernel = -9 * C.anchor_curvature()                            # 243/128
    assert kernel == Fr(243, 128)
    assert C.step_e_zero_offset() / kernel == Fr(9, 16)
    assert C.step_e_interpolant_b() / Fr(-81, 22) == Fr(9, 16)
    assert Fr(1095, 1215) == Fr(73, 81)                           # the printed ratio, not in E


def test_the_printed_value_needed_the_corrected_anchor() -> None:
    """2190/2048 is near what the corrected anchor gives; the printed anchor is off by 5/3."""
    with_printed = -9 * (C.smooth_double_difference_curvature() - C.bare_anchor_curvature())
    assert with_printed == Fr(3645, 2048)
    assert with_printed / C.step_e_zero_offset() == Fr(5, 3)
    assert abs(float(C.step_e_zero_offset() / Fr(1095, 1024)) - 1) < 0.002


def test_the_printed_bracket_still_holds() -> None:
    """lambda_0' in [0.60, 1.25] survives, so no threshold and no appendix row moves."""
    lead = float(C.step_e_zero_offset())
    lo, hi = lead * 2 ** -0.625, lead
    assert 0.60 <= lo and hi <= 1.25
    assert round(lo, 4) == 0.6924 and round(hi, 4) == 1.0679
    # and it clears the A.5 row that reads S >= 0.60 P^(-5/8)
    assert lo > 0.60


def test_step_e_zero_offset_is_measured() -> None:
    """Both halves at P = 1e8 on real j=0 branches, against -675/2048 and -216/1024."""
    from mpmath import mp
    from research.juggler_sequence.paper_b_audit import level1_data

    mp.dps = 50
    P = 10 ** 8
    rng = random.Random(3)
    H1, H2, K = int(P ** (1 / 48)), int(P ** (1 / 24)), int(P ** (1 / 24))
    half, nine4, nine8 = mp.mpf(3) / 2, mp.mpf(9) / 4, mp.mpf(9) / 8
    totals = []
    for _ in range(600):
        if len(totals) >= 4:
            break
        n = rng.randrange(P + 1, 2 * P) | 1
        h1, h2, k = rng.randint(1, max(1, H1)), rng.randint(1, max(1, H2)), rng.randint(1, max(1, K))
        b1, _, _ = level1_data(n, 2 * h1)
        b2, _, _ = level1_data(n, 2 * h2)
        b12, _, _ = level1_data(n, 2 * h1 + 2 * h2)
        if b12 - b1 - b2 != 0:
            continue
        nm = mp.mpf(n)

        def shape(nu: object, p: object, _a: int = b1, _b: int = b2, _ab: int = b12) -> object:
            Xn = mp.power(nu, half)
            return (mp.power(Xn + _ab, p) - mp.power(Xn + _a, p)
                    - mp.power(Xn + _b, p) + mp.power(Xn, p))

        unit = k * abs(b1 * b2) * mp.power(nm, -mp.mpf(13) / 8)
        Q = lambda nu, _k=k: mp.mpf(_k) / 2 * shape(nu, nine4)          # noqa: E731
        GF = lambda nu: shape(nu, half)                                  # noqa: E731
        cc = lambda nu, _k=k: mp.mpf(3 * _k) / 4 * mp.power(nu, nine8)   # noqa: E731
        JF = mp.floor(GF(nm))
        dQ = float(mp.diff(Q, nm, 2) / unit)
        dA = float(mp.diff(lambda nu: cc(nu) * (GF(nu) - JF), nm, 2) / unit)
        assert abs(dQ - (-675 / 2048)) < 1e-6, dQ
        assert abs(dA - (-216 / 1024)) < 1e-4, dA
        totals.append(9 * (dQ - dA))

    assert len(totals) == 4
    assert all(abs(t + 2187 / 2048) < 1e-3 for t in totals), totals
    # and every sample is nearer 2187/2048 than the printed 2190/2048
    assert all(abs(t + 2187 / 2048) < abs(t + 1095 / 1024) for t in totals), totals


def test_paper_carries_the_step_e_derivation() -> None:
    paper = io.open(PAPER, encoding="utf-8").read()
    assert "2187}{2048}" in paper and "729}{352}" in paper
    assert "675}{2048}" in paper and "432}{2048}" in paper
    assert "1095}{1024}" in paper and "365}{176}" in paper   # only inside the erratum
    assert "This step\n> computed the anchor correctly" in paper
    assert paper.count("1095}{1024}") == 1 and paper.count("365}{176}") == 1


# --- Lemma 5.1(iii)'s offset bound, and the row that turns on it ---


def test_the_offset_is_two_not_three() -> None:
    """j = floor({D1X+t} + {D2X+t} - t + DDX) lands in {-1,0,1,2}; the census agrees."""
    for P in (10**5, 10**6):
        c = D.branch_offset_census(P, hmax=30)
        assert c["attained"] == (-1, 2), (P, c["attained"])
        assert c["within_true_bound"] and c["within_printed_bound"]
        assert set(c["counts"]) == {-1, 0, 1, 2}


def test_the_printed_three_is_the_bound_at_twice_the_hypothesis() -> None:
    """max j = r + 1 at h1 h2 <= r P^(1/2)/3: the printed 3 belongs to r = 2."""
    lad = D.branch_offset_ladder(10**6, multiples=(1, 2, 3, 6), hmax=100)
    assert lad["max_is_multiple_plus_one"]
    assert lad["min_is_always_minus_one"]
    by = {r["multiple"]: r["max"] for r in lad["rows"]}
    assert by[1] == 2 and by[2] == 3


def test_the_offset_is_exact_integer_arithmetic() -> None:
    """beta_i = m(n+d_i) - m(n) with m = floor(n^(3/2)) = isqrt(n^3); no floats anywhere."""
    from math import isqrt
    for n, h1, h2 in ((10**6 + 1, 9, 36), (10**8 + 5, 39, 39), (10**10 + 23, 26, 26)):
        d1, d2 = 2 * h1, 2 * h2
        b1 = D.m_floor(n + d1) - D.m_floor(n)
        b2 = D.m_floor(n + d2) - D.m_floor(n)
        b12 = D.m_floor(n + d1 + d2) - D.m_floor(n)
        assert b12 - b1 - b2 == D.offset_at(n, h1, h2)
        assert D.m_floor(n) == isqrt(n**3)
        assert abs(D.offset_at(n, h1, h2)) <= 2


def test_two_is_attained_but_not_in_the_range_lemma_52_uses() -> None:
    """h1, h2 <= P^(1/24) makes eps tiny and j = 2 needs {u}+{v} >= 2 - eps."""
    hit = D.branch_offset_census(10**6, hmax=30)
    assert hit["counts"][2] > 0
    for P in (10**10, 10**12):
        r = D.branch_offset_in_applied_range(P)
        assert r["attained"] == (-1, 1), (P, r["attained"])
        assert r["eps_max"] < 1e-3


def test_the_collected_widened_constant_is_five() -> None:
    """2|j'| <= 4, so |q'|(2|j'|P^(-1/4) + 20hh'P^(-3/4)) <= 4P^(1/4)/h' + 20P^(-1/8)."""
    w = D.widened_theta_constant(2)
    assert w["lead"] == 4 and w["collected"] == 5
    assert w["mode_index_row"] == 5**16 == 152587890625
    assert D.widened_theta_constant(3)["collected"] == 7          # the printed reading
    assert D.widened_theta_constant(3)["mode_index_row"] == 7**16
    assert C.WIDENED_B_CONST == 5.0 and C.WIDENED_B_CONST_SUPERSEDED == 7.0


# --- the row that was in a proof and never in the table ---


def test_the_widened_mode_index_is_a_row_and_it_is_exact() -> None:
    """Lemma 5.2(iii) needs 5 P^(1/4) <= R_0, and states its own threshold: 5^16."""
    row = [r for r in C.thresholds() if r["tag"] == "st6D1-modeindex"][0]
    assert row["P_min"] == pytest.approx(float(5**16), rel=1e-12)
    assert row["site"] == "Thm 5.3 St.6(D1)"
    assert row["P_min"] < C.certificate()["P0"]
    # alone among the rows the substitution P = t^16 gives an exact crossing, 5 t^4 <= t^5
    assert 5 * 5.0**4 == 5.0**5


def test_at_the_superseded_truncation_the_row_has_no_solution() -> None:
    """5 P^(1/4) <= P^(1/4) is false at every P: R_0 = P^(1/4) does not merely delay."""
    old = C.r0_tradeoff(C.R0_EXPONENT_SUPERSEDED)
    assert old["modeindex"] is None
    assert old["worst_all"] == float("inf")
    assert all(old[k] is not None for k in ("collision", "qpp", "window", "flat"))
    assert 1.8e24 < old["worst"] < 1.9e24


def test_the_row_pins_R0_from_below_and_the_recorded_minimax_is_infeasible() -> None:
    """A.6's a* = 0.29919 needs 1.6e14 on the fifth site even at the corrected constant."""
    P0 = C.certificate()["P0"]
    assert 1.6e14 < 5.0 ** (1 / (0.29919 - 0.25)) < 1.7e14
    assert C.r0_tradeoff(0.29919)["worst"] < P0             # the four are fine there
    assert C.r0_tradeoff(0.29919)["worst_all"] > 4.5 * P0   # the fifth is not
    assert 5.0**20 > P0                                     # nor is 3/10
    assert abs(C.r0_lower_pin() - 0.301567) < 1e-5
    assert 0.010 < C.R0_EXPONENT - C.r0_lower_pin() < 0.011


def test_the_five_site_minimax_barely_moves_five_sixteenths() -> None:
    """At |j| <= 2 the optimum is 0.3111 and 5/16 costs 1.09; at |j| <= 3 it was 57."""
    m = C.r0_minimax()
    assert abs(m["a"] - 0.311119) < 1e-5
    assert abs(m["worst"] / 2.731e11 - 1) < 0.01
    assert 1.05 < m["at_five_sixteenths"] / m["worst"] < 1.15
    old = C.r0_minimax(C.WIDENED_B_CONST_SUPERSEDED)
    assert abs(old["a"] - 0.321848) < 1e-5
    assert 55 < old["at_five_sixteenths"] / old["worst"] < 60


def test_five_sixteenths_is_robust_at_two_and_was_not_at_three() -> None:
    """It needs the collected constant <= P_0^(1/16) = 7.0333: 41% of room at 5, 0.5% at 7."""
    P0 = C.certificate()["P0"]
    assert abs(P0 ** (1 / 16) - 7.0333) < 1e-3
    assert P0 ** (1 / 16) / C.WIDENED_B_CONST > 1.40
    assert P0 ** (1 / 16) / C.WIDENED_B_CONST_SUPERSEDED < 1.005
    assert 7.04**16 > P0 > 7.0**16


def test_the_widened_constant_is_not_sharp_and_what_that_would_buy() -> None:
    """4 P^(1/4) + 20 P^(-1/8) <= 4.001 P^(1/4) from 2.95e11, below P_0."""
    assert abs(C.widened_b_constant_threshold(0.001) / 2.95e11 - 1) < 0.02
    assert C.widened_b_constant_threshold(0.001) < C.certificate()["P0"]
    sharp = C.WIDENED_B_CONST_SHARP**16
    assert abs(sharp / 4.312e9 - 1) < 0.01
    assert 34 < 5.0**16 / sharp < 36
    # only at the sharp constant does A.6's four-site crossing come back inside the band
    assert C.r0_lower_pin(C.WIDENED_B_CONST_SHARP) < 0.29919 < C.r0_lower_pin()
    assert abs(C.r0_lower_pin(C.WIDENED_B_CONST_SHARP) - 0.294425) < 1e-5


def test_it_is_no_longer_the_floor_but_at_the_printed_bound_it_would_be() -> None:
    """The whole of A.5's lever turns on one integer in Lemma 5.1(iii)."""
    r = C.c7_saturation()
    assert r["floor_tag"] == "st5b-qpp"
    assert abs(r["max_factor"] / 120.3 - 1) < 0.02
    # at |j| <= 3 the row is 7^16, which is above the q'' floor and below P_0
    assert r["runner_up"][0] < r["floor"] < 7.0**16 < r["P0"]
    assert abs(r["P0"] / 7.0**16 - 1.079) < 0.002


def test_the_row_is_kappa_free_so_it_would_have_stopped_the_kappa_table() -> None:
    """A.2's last two entries are the gate at 5^16 and would have been the row at 7^16."""
    for k, gate in ((1 / 16, 2.041e13), (1 / 20, 1.462e13)):
        assert abs(C.kappa_tradeoff(k)["P_min"] / gate - 1) < 0.01
        allrows = max(x["P_min"] for x in C.thresholds(kappa=k) if x["P_min"])
        assert abs(allrows / gate - 1) < 0.01           # the gate still wins at 5^16
        assert gate < 7.0**16                           # and would not have at 7^16
    assert C.kappa_tradeoff(1 / 12)["P_min"] > 7.0**16


def test_paper_and_lean_carry_the_new_row() -> None:
    text = io.open(PAPER, encoding="utf-8").read()
    assert r"widened \|B_0\| <= R_0: 5 P^(1/4) <= P^(5/16)" in text
    assert "thirty-eight" in text and "thirty-seven" not in text
    assert "(33 theorems" in text
    # all five sites now print the same three-figure value; 5^16 = 1.52588e11
    assert r"5^{16}=1.53\cdot10^{11}" in text
    assert r"5^{16}=1.5\cdot10^{11}" not in text
    root = Path(__file__).resolve().parents[3] / "formal" / "Problems" / "Juggler"
    lean = io.open(root / "ThresholdCertificate.lean", encoding="utf-8").read()
    assert "theorem row_st6D1_modeindex" in lean and "5 * t ^ 4" in lean
    branch = io.open(root / "BranchFreeze.lean", encoding="utf-8").read()
    assert "theorem offset_abs_le_two" in branch
    assert "theorem carry_eq_floor_shifted" in branch
    assert "theorem offset_abs_le_three" in branch      # kept beside it


def test_paper_records_both_errata_at_their_sites() -> None:
    text = io.open(PAPER, encoding="utf-8").read()
    # Lemma 5.1(iii): the offset
    assert "as though the two could be chosen" in text
    assert r"j\in\{-1,0,1,2\}" in text
    assert "twice the one stated beside it" in text
    # Lemma 5.2(iii): the drift count
    assert "the count is right; one route to it is not" in text
    assert "reached without knowing either sign" in text
    # and the downstream constants moved together
    for figure in (r"\frac{11.5}{uhh'}", r"uhh'\ge46", r"8.5\,(uh)^{-1/2}", r"\le48P^{3/4}"):
        assert figure in text, figure


# --- the same scan, on the rest of Lemma 5.1(iii), and on what Lean was checking ---


def test_the_beta_product_does_not_over_quantify() -> None:
    """Both factors are extremal at the same n = 2P, so 4.25^2 loses only rounding."""
    r = D.beta_inventory_attained(10**6)["product"]
    assert abs(r["attained"] / 18.0 - 1) < 1e-3
    assert abs(r["closed_form"] - 18.0) < 1e-12          # (3 sqrt 2)^2
    assert r["lean_hypothesis"] == 4.25**2
    assert 1.0 < r["printed"] / r["attained"] < 1.06     # under 6%, all of it rounding


def test_the_three_bounds_built_on_it_do() -> None:
    """Each pairs the product with a power of nu taken at the other end of the block."""
    r = D.beta_inventory_attained(10**6)
    lo, hi = r["second_difference_term"]["attained"]
    assert abs(lo - 27 / 4) < 1e-3 and abs(hi - (27 / 4) * 2**0.25) < 3e-3
    assert r["second_difference_term"]["printed"] == [1.4, 15.0]
    assert (15.0 - 1.4) / (hi - lo) > 10                 # printed interval ten times as wide
    assert abs(r["Gprime_beta"]["attained"] - 81 / 16) < 1e-3
    assert abs(r["Gsecond_beta"]["attained"] - 567 / 64) < 1e-3
    assert 3.9 < 20.0 / r["Gprime_beta"]["attained"] < 4.0
    assert 2.8 < 25.0 / r["Gsecond_beta"]["attained"] < 2.9


def test_none_of_the_three_propagates_anywhere_that_binds() -> None:
    """Which is why they are measured and left alone."""
    P0 = C.certificate()["P0"]
    # the 25 enters only through 25/0.35 <= 71.5, i.e. the st6D1-good row
    for c, want in ((25.0, 8.2e4), (567 / 64, 1.0e4)):
        row = (4 * c / 0.35) ** 2
        assert abs(row / want - 1) < 0.05, (c, row)
        assert row < P0 / 1e8
    # the 20 enters only through the lower-order 20 h P^(-1/4) of the widened coefficient
    for c, want in ((20.0, 2.95e11), (81 / 16, 7.59e9)):
        assert abs(C.widened_b_constant_threshold(0.001 * 20.0 / c) * 0 + (c / 0.001) ** (8 / 3)
                   / want - 1) < 0.05, c
    assert (81 / 16 / 0.001) ** (8 / 3) < P0            # and both are far below P_0


def test_the_lean_interpolant_chain_is_on_the_corrected_anchor() -> None:
    """It proved 186 / 0.57 / 106 while the manuscript displayed 300 / 0.91 / 170.6."""
    root = Path(__file__).resolve().parents[3] / "formal" / "Problems" / "Juggler"
    src = io.open(root / "PaperBAssembly.lean", encoding="utf-8").read()
    for frag in ("300 * k * h\u2082 * p18", "84.38 * (k * (h\u2081 + h\u2082)) * p98",
                 "(27 / 128 : \u211d) * 4.3 \u2264 0.91", "W\u2081 + W\u2082 \u2264 170.6 * p2524"):
        assert frag in src, frag
    for frag in ("interpolant_step_i_precorrection", "interpolant_step_ii_precorrection",
                 "interpolant_assembly_precorrection"):
        assert frag in src, frag
    # the corrected chain closes: (9/32)*300 + (27/128)*4.3, doubled
    assert abs(((9 / 32) * 300 + (27 / 128) * 4.3) * 2 - 170.564) < 1e-3
    assert (84.38 + 0.91) * 2 <= 170.6
    # and it is the constant the certificate is solved against
    assert abs(C.interpolant_error(1e13) / (170.6 * 1e13 ** (-25 / 24) + 0.11 * 1e13 ** (-5 / 6))
               - 1) < 1e-12
    assert C.ANCHOR_CONSTANTS[2] == 170.6 and C.ANCHOR_CONSTANTS_PRECORRECTION[2] == 105.8


def test_paper_says_what_the_machine_check_now_covers() -> None:
    text = io.open(PAPER, encoding="utf-8").read()
    assert "what the machine check was checking" in text
    assert "corrected figures above and not the ones the erratum replaced" in text
    assert "How much of the" in text and "inventory above is attained" in text
    assert r"\tfrac{81}{16}=5.0625" in text and r"\tfrac{567}{64}=8.8594" in text
    assert "neither propagates anywhere that binds" in text
