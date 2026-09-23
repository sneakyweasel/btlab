"""Historical Paper B audit: standing.

Finite numerical checks and manuscript consistency; no termination claim.
"""
from __future__ import annotations

import random
from typing import Any

import mpmath as mp

from .identities import (
    level1_data,
)
from .numeric_objects import (
    X_of,
    Y_of,
    c_of,
    m_of,
)

# ----------------------------------------------------------------------------------------------
# Layer 2: standing estimates and inventories
# ----------------------------------------------------------------------------------------------


def standing_estimates(P: int, seed: int = 11, samples: int = 200) -> dict[str, Any]:
    rng = random.Random(seed)
    H1 = max(1, int(P ** (1 / 48)))
    H2 = max(1, int(P ** (1 / 24)))
    K = max(1, int(P ** (1 / 24)))
    Pm = mp.mpf(P)
    obs: dict[str, list[float]] = {
        "X1_over_P12": [],
        "X2_over_Pm12": [],
        "DX_over_hP12": [],
        "Dic_over_khP18": [],
        "DDc_over_kh1h2Pm78": [],
        "W_over_h1P54": [],
        "Wcell_speed_over_h1P14": [],
        "E6_ratio": [],
        "G1_over_bound": [],
        "frozen_j0_ratio": [],
    }
    for _ in range(samples):
        n = rng.randrange(P + 1, 2 * P) | 1
        h1, h2, k = rng.randint(1, H1), rng.randint(1, H2), rng.randint(1, K)
        d1, d2 = 2 * h1, 2 * h2
        nm = mp.mpf(n)
        obs["X1_over_P12"].append(float(mp.mpf(3) / 2 * mp.sqrt(nm) / mp.sqrt(Pm)))
        obs["X2_over_Pm12"].append(float(mp.mpf(3) / 4 / mp.sqrt(nm) * mp.sqrt(Pm)))
        for h in (h1, h2):
            dX = X_of(n + 2 * h) - X_of(n)
            obs["DX_over_hP12"].append(float(dX / (h * mp.sqrt(Pm))))
            dc = c_of(n + 2 * h, k) - c_of(n, k)
            obs["Dic_over_khP18"].append(float(dc / (k * h * mp.power(Pm, mp.mpf(1) / 8))))
        DDc = c_of(n + d1 + d2, k) - c_of(n + d1, k) - c_of(n + d2, k) + c_of(n, k)
        obs["DDc_over_kh1h2Pm78"].append(float(DDc / (k * h1 * h2 * mp.power(Pm, -mp.mpf(7) / 8))))
        W = Y_of(n + d1) - Y_of(n)
        obs["W_over_h1P54"].append(float(W / (h1 * mp.power(Pm, mp.mpf(5) / 4))))
        # speed of the W sawtooth on a cell: |W1'(m) X'| with W1(m) = (m+beta1)^{3/2} - m^{3/2}
        m = m_of(n)
        beta1, _, _ = level1_data(n, d1)
        W1p = mp.mpf(3) / 2 * (mp.sqrt(m + beta1) - mp.sqrt(m))
        Xp = mp.mpf(3) / 2 * mp.sqrt(nm)
        obs["Wcell_speed_over_h1P14"].append(float(W1p * Xp / (h1 * mp.power(Pm, mp.mpf(1) / 4))))
        # (E6) on an offset branch: numerical second derivative of c(nu) * F_kappa(X(nu)) in nu
        beta2, _, _ = level1_data(n, d2)
        beta12, _, _ = level1_data(n, d1 + d2)
        j = beta12 - beta1 - beta2

        def cF(nu: mp.mpf) -> mp.mpf:
            Xn = mp.power(nu, mp.mpf(3) / 2)
            Fm = (
                mp.power(Xn + beta12, mp.mpf(3) / 2)
                - mp.power(Xn + beta1, mp.mpf(3) / 2)
                - mp.power(Xn + beta2, mp.mpf(3) / 2)
                + mp.power(Xn, mp.mpf(3) / 2)
            )
            return mp.mpf(3 * k) / 4 * mp.power(nu, mp.mpf(9) / 8) * Fm

        d2cF = mp.diff(cF, nm, 2)
        if j != 0:
            lead = mp.mpf(945) / 512 * k * abs(j) * mp.power(nm, -mp.mpf(1) / 8)
            obs["E6_ratio"].append(float(abs(d2cF) / lead))
        else:
            lead0 = mp.mpf(135) / 1024 * k * abs(beta1 * beta2) * mp.power(nm, -mp.mpf(13) / 8)
            if lead0 != 0:
                obs["frozen_j0_ratio"].append(float(abs(d2cF) / lead0))
        # |G'| bound of Lemma 5.1(iii)
        def G(nu: mp.mpf) -> mp.mpf:
            Xn = mp.power(nu, mp.mpf(3) / 2)
            return (
                mp.power(Xn + beta12, mp.mpf(3) / 2)
                - mp.power(Xn + beta1, mp.mpf(3) / 2)
                - mp.power(Xn + beta2, mp.mpf(3) / 2)
                + mp.power(Xn, mp.mpf(3) / 2)
            )

        G1 = abs(mp.diff(G, nm, 1))
        bound = 2 * abs(j) * mp.power(Pm, -mp.mpf(1) / 4) + 20 * h1 * h2 * mp.power(Pm, -mp.mpf(3) / 4)
        obs["G1_over_bound"].append(float(G1 / bound))
    rng_summary = {key: (min(v), max(v)) if v else None for key, v in obs.items()}
    printed = {
        "X1_over_P12": (1.5, 2.13),
        "X2_over_Pm12": (0.53, 0.75),
        "DX_over_hP12": (3.0, 4.3),
        "Dic_over_khP18": (1.68, 1.85),
        "DDc_over_kh1h2Pm78": (0.22, 0.43),
        "W_over_h1P54": (4.4, 11.0),
        "Wcell_speed_over_h1P14": (2.2, 10.4),
    }
    verdict = {}
    for key, (lo, hi) in printed.items():
        r = rng_summary[key]
        verdict[key] = bool(r is not None and lo <= r[0] and r[1] <= hi)
    verdict["E6_ratio_within_1pm_P^-1/4"] = bool(rng_summary["E6_ratio"] is None or all(abs(x - 1) <= 1.5 * P ** (-0.25) + 0.02 for x in obs["E6_ratio"]))
    verdict["frozen_j0_ratio_near_one"] = bool(
        rng_summary["frozen_j0_ratio"] is None
        or all(abs(x - 1) <= 0.08 for x in obs["frozen_j0_ratio"])
    )
    verdict["G1_le_bound"] = bool(rng_summary["G1_over_bound"] is not None and rng_summary["G1_over_bound"][1] <= 1.0)
    return {"P": P, "observed_ranges": rng_summary, "printed_ranges": printed, "verdict": verdict, "all_ok": all(verdict.values())}


def cell_inventory(P: int, h: int) -> dict[str, Any]:
    """Level sets of floor(delta_h) over odd n in (P, 2P]: count and length range (E1 inventory)."""

    counts: list[int] = []
    prev = None
    run = 0
    for n in range(P + 1, 2 * P + 1, 2):
        d = int(mp.floor(X_of(n + 2 * h) - X_of(n)))
        if d == prev:
            run += 1
        else:
            if prev is not None:
                counts.append(run)
            prev, run = d, 1
    counts.append(run)
    inner = counts[1:-1]  # full cells only
    Ph = P**0.5 / h
    return {
        "P": P,
        "h": h,
        "cells": len(counts),
        "printed_max_cells": 1.5 * h * P**0.5 + 1,
        "min_full_cell_over_P12_h": (2 * min(inner) / Ph) if inner else None,  # cells counted in odd n: length in integers is 2x
        "max_full_cell_over_P12_h": (2 * max(inner) / Ph) if inner else None,
        "ok": len(counts) <= 1.5 * h * P**0.5 + 1 and (not inner or (2 * min(inner) / Ph >= 2 / 3 - 0.02 and 2 * max(inner) / Ph <= 0.95 + 0.02)),
    }


def cell_scaling_check(h: int = 1, lo: int = 10**5, hi: int = 3 * 10**5) -> dict[str, Any]:
    """Is the cell inventory scale-invariant, or does the low-`P` evaluation only look safe?

    `cell_inventory` enumerates every odd `n` in `(P, 2P]`, so it cannot be run anywhere near
    `P_0 = 3.6e13`; the standing estimates could be lifted into their claimed regime and this
    cannot.  What can be tested is the property the extrapolation rests on: the quantities are
    normalised by `P^{1/2}/h`, so they should not move with `P`.  Measured over a 30x range
    they do not — the cell count stays at `0.828` of its printed bound, the long-cell ratio at
    `0.942` against the printed `0.95`, and the short-cell ratio rises towards `2/3` from
    below with a deficit of order `P^{-1/2}` (`2.6e-3` at `1e5`, `3.7e-4` at `3e6`), which is
    why the printed `2/3` carries a `0.02` tolerance.
    """

    a, b = cell_inventory(lo, h), cell_inventory(hi, h)
    drift_min = abs(a["min_full_cell_over_P12_h"] - b["min_full_cell_over_P12_h"])
    drift_max = abs(a["max_full_cell_over_P12_h"] - b["max_full_cell_over_P12_h"])
    frac_a = a["cells"] / a["printed_max_cells"]
    frac_b = b["cells"] / b["printed_max_cells"]
    return {
        "h": h, "P_lo": lo, "P_hi": hi,
        "min_ratio": [a["min_full_cell_over_P12_h"], b["min_full_cell_over_P12_h"]],
        "max_ratio": [a["max_full_cell_over_P12_h"], b["max_full_cell_over_P12_h"]],
        "cell_count_fraction": [frac_a, frac_b],
        "drift_min": drift_min, "drift_max": drift_max,
        "short_cell_deficit_from_two_thirds": [2 / 3 - a["min_full_cell_over_P12_h"],
                                               2 / 3 - b["min_full_cell_over_P12_h"]],
        # scale invariance is the claim; 0.01 is well inside the 0.02 the printed bounds carry
        "ok": drift_min < 0.01 and drift_max < 0.01 and abs(frac_a - frac_b) < 0.01,
    }


def frozen_run_inventory(P: int, h1: int, h2: int) -> dict[str, Any]:
    """Runs of floor(G) with G = F_kappa(X(n)) on odd n in (P, 2P] for fixed level-1 gaps, against 22(|j|+1)P^{3/4}."""

    mp.mp.dps = 40
    n0 = (P + 1) | 1
    beta1, _, _ = level1_data(n0, 2 * h1)
    beta2, _, _ = level1_data(n0, 2 * h2)
    beta12, _, _ = level1_data(n0, 2 * h1 + 2 * h2)
    j = beta12 - beta1 - beta2
    runs, prev = 0, None
    for n in range(P + 1, 2 * P + 1, 2):
        Xn = X_of(n)
        G = mp.power(Xn + beta12, mp.mpf(3) / 2) - mp.power(Xn + beta1, mp.mpf(3) / 2) - mp.power(Xn + beta2, mp.mpf(3) / 2) + mp.power(Xn, mp.mpf(3) / 2)
        fl = int(mp.floor(G))
        if fl != prev:
            runs += 1
            prev = fl
    mp.mp.dps = 60
    return {"P": P, "h1": h1, "h2": h2, "j": j, "runs": runs, "printed_bound": 22 * (abs(j) + 1) * P**0.75, "ok": runs <= 22 * (abs(j) + 1) * P**0.75}


def frozen_anchor_curvature_samples(P: int = 10**8, seed: int = 3, trials: int = 40) -> dict[str, Any]:
    """Lemma 5.2b on j=0 branches: the bare composite beside the anchor the phase carries.

    ``frozen_ratio`` measures ``|(c G_F)''|`` against ``135/1024``, which is what the manuscript
    printed.  ``anchor_ratio`` measures ``|(c(G_F - J_F))''|`` -- the object the lemma defines,
    with ``J_F`` frozen -- against ``216/1024 = 27/128``.  Both come out at 1.  They are different
    functions, differing by ``c'' J_F``, and the erratum at Lemma 5.2b is that the printed
    constant belongs to the first while the proof uses the second.

    The moving-gap model is recorded to show it matches neither.  Measured, it is ``2673/1024``,
    not the ``243/128`` earlier printings gave it -- and ``243/128`` is exactly ``9 * 216/1024``,
    the corrected anchor after ``β1 β2 -> 9 h1 h2 ν``, so the two errors concealed each other.
    """

    rng = random.Random(seed)
    H1 = max(1, int(P ** (1 / 48)))
    H2 = max(1, int(P ** (1 / 24)))
    K = max(1, int(P ** (1 / 24)))
    frozen_ratios: list[float] = []
    anchor_ratios: list[float] = []
    eight_fifths: list[float] = []
    moving_ratios: list[float] = []
    for _ in range(trials * 4):
        if len(frozen_ratios) >= trials:
            break
        n = rng.randrange(P + 1, 2 * P) | 1
        h1, h2, k = rng.randint(1, H1), rng.randint(1, H2), rng.randint(1, K)
        beta1, _, _ = level1_data(n, 2 * h1)
        beta2, _, _ = level1_data(n, 2 * h2)
        beta12, _, _ = level1_data(n, 2 * h1 + 2 * h2)
        j = beta12 - beta1 - beta2
        if j != 0:
            continue
        nm = mp.mpf(n)

        def GF(nu: mp.mpf) -> mp.mpf:
            Xn = mp.power(nu, mp.mpf(3) / 2)
            return (
                mp.power(Xn + beta12, mp.mpf(3) / 2)
                - mp.power(Xn + beta1, mp.mpf(3) / 2)
                - mp.power(Xn + beta2, mp.mpf(3) / 2)
                + mp.power(Xn, mp.mpf(3) / 2)
            )

        def c(nu: mp.mpf) -> mp.mpf:
            return mp.mpf(3 * k) / 4 * mp.power(nu, mp.mpf(9) / 8)

        JF = mp.floor(GF(nm))                       # frozen on the piece
        d2 = mp.diff(lambda nu: c(nu) * GF(nu), nm, 2)
        d2a = mp.diff(lambda nu: c(nu) * (GF(nu) - JF), nm, 2)
        unit = k * abs(beta1 * beta2) * mp.power(nm, -mp.mpf(13) / 8)
        lead = mp.mpf(135) / 1024 * unit
        anchor = mp.mpf(216) / 1024 * unit
        moving = mp.mpf(2673) / 1024 * k * h1 * h2 * mp.power(nm, -mp.mpf(5) / 8)
        if lead == 0:
            continue
        frozen_ratios.append(float(abs(d2) / lead))
        anchor_ratios.append(float(abs(d2a) / anchor))
        eight_fifths.append(float(abs(d2a) / abs(d2)))
        moving_ratios.append(float(abs(d2) / moving))
    return {
        "P": P,
        "samples": len(frozen_ratios),
        "frozen_ratio_range": (min(frozen_ratios), max(frozen_ratios)) if frozen_ratios else None,
        "anchor_ratio_range": (min(anchor_ratios), max(anchor_ratios)) if anchor_ratios else None,
        "moving_gap_ratio_range": (min(moving_ratios), max(moving_ratios)) if moving_ratios else None,
        "frozen_near_one": bool(frozen_ratios) and all(abs(x - 1) <= 0.08 for x in frozen_ratios),
        "anchor_near_one": bool(anchor_ratios) and all(abs(x - 1) <= 0.08 for x in anchor_ratios),
        "anchor_over_bare_range": (min(eight_fifths), max(eight_fifths)) if eight_fifths else None,
        "anchor_is_eight_fifths_of_bare": bool(eight_fifths)
        and all(abs(r - 8 / 5) <= 0.02 for r in eight_fifths),
        "moving_gap_is_wrong_model": bool(moving_ratios) and all(abs(x - 1) > 0.2 for x in moving_ratios),
    }


def frozen_theta_coeff_samples(P: int = 10**6, seed: int = 9, trials: int = 12) -> dict[str, Any]:
    """Step 5b j=0: frozen B = c F'(X) against (9/32) k β1 β2 ν^{-9/8}; |B| ≤ 6."""

    rng = random.Random(seed)
    H1 = max(1, int(P ** (1 / 48)))
    H2 = max(1, int(P ** (1 / 24)))
    K = max(1, int(P ** (1 / 24)))
    k_c1 = max(1, int(P ** 0.125))
    ratios: list[float] = []
    abs_B: list[float] = []
    attempts = 0
    forced: list[tuple[int, int, int]] = [(1, 1, 1)]
    if k_c1 * 1 * 1 <= P ** 0.125 * (1.0 + 1e-12):
        forced.append((1, 1, k_c1))
    while len(ratios) < trials and attempts < 4000:
        attempts += 1
        n = rng.randrange(P + 80, 2 * P - 80) | 1
        if forced:
            h1, h2, k = forced.pop(0)
        else:
            h1, h2, k = rng.randint(1, H1), rng.randint(1, H2), rng.randint(1, K)
        if k * h1 * h2 > P ** 0.125 * (1.0 + 1e-12):
            continue
        beta1, _, _ = level1_data(n, 2 * h1)
        beta2, _, _ = level1_data(n, 2 * h2)
        beta12, _, _ = level1_data(n, 2 * h1 + 2 * h2)
        if beta12 - beta1 - beta2 != 0:
            continue
        nm = mp.mpf(n)
        m = mp.mpf(m_of(n))
        # exact frozen F' at the integer m, j = 0
        fp = mp.mpf(3) / 2 * (
            mp.sqrt(m + beta12) - mp.sqrt(m + beta1) - mp.sqrt(m + beta2) + mp.sqrt(m)
        )
        B = c_of(n, k) * fp
        lead = -mp.mpf(9) / 32 * k * beta1 * beta2 * mp.power(nm, -mp.mpf(9) / 8)
        if lead == 0:
            continue
        ratios.append(float(B / lead))
        abs_B.append(float(abs(B)))
    return {
        "P": P,
        "samples": len(ratios),
        "ratio_range": (min(ratios), max(ratios)) if ratios else None,
        "abs_B_range": (min(abs_B), max(abs_B)) if abs_B else None,
        "ratio_near_one": bool(ratios) and all(abs(x - 1) <= 0.08 for x in ratios),
        "abs_B_at_most_six": bool(abs_B) and max(abs_B) <= 6.0,
    }


def _frozen_total_d2(n: int, h1: int, h2: int, k: int) -> tuple[mp.mpf, int, mp.mpf]:
    """Second nu-derivative of DeltaDelta(k/2 m^{9/4}) - c(G_F - J_F), betas frozen."""

    d1, d2 = 2 * h1, 2 * h2
    beta1, _, _ = level1_data(n, d1)
    beta2, _, _ = level1_data(n, d2)
    beta12, _, _ = level1_data(n, d1 + d2)
    j = beta12 - beta1 - beta2
    x0 = X_of(n)
    G0 = (
        mp.power(x0 + beta12, mp.mpf(3) / 2)
        - mp.power(x0 + beta1, mp.mpf(3) / 2)
        - mp.power(x0 + beta2, mp.mpf(3) / 2)
        + mp.power(x0, mp.mpf(3) / 2)
    )
    jf = int(mp.floor(G0))

    def tot(nu: mp.mpf) -> mp.mpf:
        xt = mp.power(nu, mp.mpf(3) / 2)
        m94 = mp.mpf(k) / 2 * (
            mp.power(xt + beta12, mp.mpf(9) / 4)
            - mp.power(xt + beta1, mp.mpf(9) / 4)
            - mp.power(xt + beta2, mp.mpf(9) / 4)
            + mp.power(xt, mp.mpf(9) / 4)
        )
        ker = mp.mpf(3 * k) / 4 * mp.power(nu, mp.mpf(9) / 8) * (
            mp.power(xt + beta12, mp.mpf(3) / 2)
            - mp.power(xt + beta1, mp.mpf(3) / 2)
            - mp.power(xt + beta2, mp.mpf(3) / 2)
            + mp.power(xt, mp.mpf(3) / 2)
            - jf
        )
        return m94 - ker

    return mp.diff(tot, mp.mpf(n), 2), j, G0 - jf


def frozen_total_phase_samples(P: int = 10**6, seed: int = 7, trials: int = 8) -> dict[str, Any]:
    """Theorem 6.1 Step E: frozen total-phase curvature against 81/512 (offset) and 1095/1024 (j=0)."""

    rng = random.Random(seed)
    off_ratios: list[float] = []
    b_ratios: list[float] = []
    z_ratios: list[float] = []
    moving_z: list[float] = []
    attempts = 0
    while (len(off_ratios) < trials or len(z_ratios) < trials) and attempts < 4000:
        attempts += 1
        n = rng.randrange(P + 80, 2 * P - 80) | 1
        h1, h2, k = 1, 1, 1
        d2, j, _frac = _frozen_total_d2(n, h1, h2, k)
        nm = mp.mpf(n)
        if j == 0 and len(z_ratios) < trials:
            lead = mp.mpf(1095) / 1024 * k * h1 * h2 * mp.power(nm, -mp.mpf(5) / 8)
            moving = mp.mpf(16929) / 2048 * k * h1 * h2 * mp.power(nm, -mp.mpf(5) / 8)
            if lead != 0:
                z_ratios.append(float(abs(d2) / lead))
                moving_z.append(float(abs(d2) / moving))
        elif j != 0 and len(off_ratios) < trials:
            lead = mp.mpf(81) / 512 * k * j * mp.power(nm, -mp.mpf(1) / 8)
            if lead != 0:
                off_ratios.append(float(d2 / lead))
            # B by a tiny theta shift
            beta1, _, _ = level1_data(n, 2)
            beta2, _, _ = level1_data(n, 2)
            beta12, _, _ = level1_data(n, 4)
            x0 = X_of(n)
            G0 = (
                mp.power(x0 + beta12, mp.mpf(3) / 2)
                - mp.power(x0 + beta1, mp.mpf(3) / 2)
                - mp.power(x0 + beta2, mp.mpf(3) / 2)
                + mp.power(x0, mp.mpf(3) / 2)
            )
            jf = int(mp.floor(G0))

            def phase(eps: mp.mpf) -> mp.mpf:
                xt = x0 - eps
                m94 = mp.mpf(k) / 2 * (
                    mp.power(xt + beta12, mp.mpf(9) / 4)
                    - mp.power(xt + beta1, mp.mpf(9) / 4)
                    - mp.power(xt + beta2, mp.mpf(9) / 4)
                    + mp.power(xt, mp.mpf(9) / 4)
                )
                ker = c_of(n, k) * (
                    mp.power(xt + beta12, mp.mpf(3) / 2)
                    - mp.power(xt + beta1, mp.mpf(3) / 2)
                    - mp.power(xt + beta2, mp.mpf(3) / 2)
                    + mp.power(xt, mp.mpf(3) / 2)
                    - jf
                )
                return m94 - ker

            eps = mp.mpf("1e-8")
            B = -(phase(eps) - phase(mp.mpf(0))) / eps
            Blead = mp.mpf(27) / 32 * k * j * mp.power(nm, mp.mpf(3) / 8)
            if Blead != 0:
                b_ratios.append(float(B / Blead))
    return {
        "P": P,
        "offset_samples": len(off_ratios),
        "zero_samples": len(z_ratios),
        "offset_ratio_range": (min(off_ratios), max(off_ratios)) if off_ratios else None,
        "B_ratio_range": (min(b_ratios), max(b_ratios)) if b_ratios else None,
        "zero_ratio_range": (min(z_ratios), max(z_ratios)) if z_ratios else None,
        "offset_near_one": bool(off_ratios) and all(abs(x - 1) <= 0.04 for x in off_ratios),
        "B_near_27_over_32": bool(b_ratios) and all(abs(x - 1) <= 0.06 for x in b_ratios),
        "zero_near_one": bool(z_ratios) and all(abs(x - 1) <= 0.04 for x in z_ratios),
        "moving_8_27_is_wrong_model": bool(moving_z) and all(abs(x - 1) > 0.5 for x in moving_z),
    }
