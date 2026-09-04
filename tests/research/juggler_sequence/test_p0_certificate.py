"""Effective threshold certificate for Paper B: P_0 = 3.8e16, binding at Step 5b's V <= c_7 S/2."""

from __future__ import annotations

import math

from research.juggler_sequence import p0_certificate as C


def test_every_printed_threshold_is_solvable() -> None:
    rows = C.thresholds()
    assert len(rows) == 31
    assert all(r["log10_P_min"] is not None for r in rows), [
        r["tag"] for r in rows if r["log10_P_min"] is None
    ]


def test_p0_is_38e16_and_binds_at_the_lemma_3_9_hypothesis() -> None:
    cert = C.certificate()
    assert cert["binding"]["tag"] == "5b-V<=c7S"
    assert 3.7e16 < cert["P0"] < 3.9e16
    # the paper prints 3.8e16
    assert round(cert["P0"] / 1e16, 1) == 3.8


def test_each_threshold_is_sharp_at_its_own_crossing() -> None:
    """Just below the reported value the inequality fails; just above it holds."""
    for r in C.thresholds():
        lg = r["log10_P_min"]
        if lg <= 0.0:  # holds for every P >= 1; nothing to straddle
            continue
        pred = dict(
            (t, p) for t, _s, _c, p in _rows()
        )[r["tag"]]
        assert pred(10.0 ** (lg + 0.01)), r["tag"]
        assert not pred(10.0 ** (lg - 0.01)), r["tag"]


def _rows():
    """The predicate list, re-derived so the test does not trust the cached thresholds."""
    import inspect

    src = inspect.getsource(C.thresholds)
    assert "5b-V<=c7S" in src
    # rebuild by calling thresholds() with instrumentation is overkill; use the module's own list
    out = []
    for r in C.thresholds():
        out.append((r["tag"], r["site"], r["claim"], _pred_for(r["tag"])))
    return out


def _pred_for(tag: str):
    S5b = lambda P: 0.35 * P**-0.625  # noqa: E731
    S5a = lambda P: 0.60 * P**-0.625  # noqa: E731
    k, c7, rho0 = C.KAPPA, C.C7, C.C7 / 8.0
    V = C._V
    table = {
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
        "5a-V>=10err": lambda P: V(S5a(P), P, k) >= 10 * C.interpolant_error(P),
        "5a-V<=c7S": lambda P: V(S5a(P), P, k) <= c7 * S5a(P) / 2,
        "5b-V>=10err": lambda P: V(S5b(P), P, k) >= 10 * C.interpolant_error(P),
        "5b-V<=c7S": lambda P: V(S5b(P), P, k) <= c7 * S5b(P) / 2,
        "thm63-rem": lambda P: P ** (43 / 96) <= P ** (1 - 1 / 96),
    }
    return table[tag]


def test_the_balance_comparisons_carry_the_threshold_alone() -> None:
    cert = C.certificate()
    # everything except the four Lemma 3.9 balance comparisons is satisfied six orders earlier
    assert 2.5e10 < cert["P0_excluding_lemma_3_9_balance"] < 3.5e10
    assert cert["binding_excluding_balance"]["tag"] == "s3s1-Bsmall"
    assert cert["P0"] / cert["P0_excluding_lemma_3_9_balance"] > 10**6


def test_kappa_trades_threshold_against_an_absorbed_coefficient() -> None:
    """Lowering kappa lowers P_0 fast and raises the P^{89/96} coefficient slowly."""
    at3 = C.kappa_tradeoff(3.0)
    at13 = C.kappa_tradeoff(1 / 3)
    assert at3["P_min"] / at13["P_min"] > 10**6
    assert at13["coeff_total"] / at3["coeff_total"] < 2.0
    # kappa = 3 is near the coefficient optimum, which is why the draft chose it
    assert C.kappa_tradeoff(3.69)["coeff_total"] < at3["coeff_total"] < at13["coeff_total"]
    # and 0.312 is the floor: below it the two comparisons collide
    assert C.kappa_tradeoff(0.312)["P_min"] < C.kappa_tradeoff(0.25)["P_min"]


def test_superseded_normalisation_reproduces_the_earlier_1e24() -> None:
    cert = C.certificate()
    assert 5.0e23 < cert["P0_at_superseded_kappa3_c7_288"] < 6.5e23


def test_log_absorption_is_astronomically_larger_and_excluded() -> None:
    """The eps-absorption thresholds are not part of P_0; Sections 4-6 carry P^eps."""
    cert = C.certificate()
    for row in cert["log_absorption_not_required"]:
        assert row["P_min"] is None or row["P_min"] > 1e100
    assert cert["P0"] < 1e17


def test_c7_is_the_exact_linf_inverse_norm_proved_in_lean() -> None:
    """c_7 = 1/||M^{-1}||_inf with rows 110, 232, 123 (formal/.../MonomialSplitting.lean)."""
    rows = [(10, 68, 32), (-24, -144, -64), (15, 76, 32)]
    assert max(sum(abs(x) for x in r) for r in rows) == 232
    assert abs(C.C7 - 1 / 232) < 1e-15


def test_weyl_steps_halve_the_log_power_twice() -> None:
    """Mode mass log^3 becomes log^{3/4} in K_c after two differencings."""
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
