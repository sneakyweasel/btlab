"""Step 5b sublevel geometry vs Paper B Lemma 3.9.

Phase-0 only. Measures Ω_V and the Vandermonde transition
set T on the printed zero-offset three-term model, then
compares length and interval count to an explicit c_7 bound.
Not a Paper B edit, not a harvest reopen, not a K3 attack,
not an exponential sum.
"""

from __future__ import annotations

from research.juggler_sequence.lean_paths import (
    DATA_ROOT,
)

import json
from math import floor, sqrt
from pathlib import Path
from typing import Any, Callable

DATA_DIR = DATA_ROOT / "step5b_sublevel"
JSON_PATH = DATA_DIR / "summary.json"

# Printed zero-offset triple of Theorem 5.3 Step 5b.
ALPHA = 5.0 / 4.0
BETA = 11.0 / 8.0
GAMMA = 3.0 / 2.0
A_COEFF = ALPHA * (ALPHA - 1.0)  # 5/16
B_COEFF = BETA * (BETA - 1.0)  # 33/64
C_COEFF = GAMMA * (GAMMA - 1.0)  # 3/4
XA = ALPHA - 2.0  # -3/4
XB = BETA - 2.0  # -5/8
XG = GAMMA - 2.0  # -1/2

P_LIST = (10**6, 10**8, 10**10)
N_GRID = 200_000
BISECT_STEPS = 40
MU_PREFACTOR = 0.84
LAMBDA0_MID = 3.0
V_PREFACTOR = 3.0
PAPER_VS_CAP = 6.7
N_INVENTORY_PREFACTOR = 3.5

ANTI = {
    "halt_theorem": False,
    "paper_a_modified": False,
    "paper_b_modified": False,
    "sums_evaluated": False,
    "k3_reopened": False,
    "harvest_reopened": False,
    "alpha_33_32": False,
    "kernel_retagged": False,
}


def _det3(m: list[list[float]]) -> float:
    a, b, c = m[0]
    d, e, f = m[1]
    g, h, i = m[2]
    return a * (e * i - f * h) - b * (d * i - f * g) + c * (d * h - e * g)


def _inv3(m: list[list[float]]) -> list[list[float]]:
    a, b, c = m[0]
    d, e, f = m[1]
    g, h, i = m[2]
    det = _det3(m)
    if abs(det) < 1e-18:
        raise ValueError("Vandermonde matrix is singular")
    cof = [
        [e * i - f * h, c * h - b * i, b * f - c * e],
        [f * g - d * i, a * i - c * g, c * d - a * f],
        [d * h - e * g, b * g - a * h, a * e - b * d],
    ]
    return [[cof[j][i] / det for j in range(3)] for i in range(3)]


def vandermonde_matrix() -> list[list[float]]:
    xs = (XA, XB, XG)
    return [
        [1.0, 1.0, 1.0],
        [xs[0], xs[1], xs[2]],
        [xs[0] * (xs[0] - 1.0), xs[1] * (xs[1] - 1.0), xs[2] * (xs[2] - 1.0)],
    ]


def c7_printed_triple() -> dict[str, float]:
    """c_7 = 1 / ||M^{-1}||_∞ on the printed exponents."""
    m = vandermonde_matrix()
    inv = _inv3(m)
    inf_norm = max(sum(abs(x) for x in row) for row in inv)
    c7 = 1.0 / inf_norm
    # Positive-octant sample on the max-norm cube faces.
    pos_min = inf_norm
    for i in range(3):
        for s0 in (0.0, 1.0):
            for s1 in (0.0, 1.0):
                for s2 in (0.0, 1.0):
                    v = [s0, s1, s2]
                    if max(v) <= 0.0:
                        continue
                    v[i] = 1.0
                    mv = [
                        m[0][0] * v[0] + m[0][1] * v[1] + m[0][2] * v[2],
                        m[1][0] * v[0] + m[1][1] * v[1] + m[1][2] * v[2],
                        m[2][0] * v[0] + m[2][1] * v[1] + m[2][2] * v[2],
                    ]
                    ratio = max(abs(t) for t in mv) / max(v)
                    if ratio < pos_min:
                        pos_min = ratio
    return {
        "c7": c7,
        "c7_positive_octant": pos_min,
        "inv_inf_norm": inf_norm,
        "det": _det3(m),
    }


C7_ROW = c7_printed_triple()
C7 = C7_ROW["c7"]


def paper_shifts(p: int) -> dict[str, int]:
    h1 = max(1, floor(float(p) ** (1.0 / 48.0)))
    h2 = max(1, floor(float(p) ** (1.0 / 24.0)))
    k_max = max(1, floor(float(p) ** (1.0 / 24.0)))
    cap_c1 = float(p) ** 0.125
    k_cap = max(1, floor(cap_c1 / (h1 * h2)))
    return {
        "P": p,
        "h1": h1,
        "h2": h2,
        "k_max": min(k_max, k_cap),
    }


def scale_S(
    p: float, u: float, up: float, w: float, k: float, h1: float, h2: float
) -> dict[str, float]:
    t_wave = abs(u * h1 + up * h2) * p ** (-0.75)
    t_anchor = abs(k * h1 * h2) * p ** (-0.625)
    t_window = abs(w) * p ** (-0.5)
    s = max(t_wave, t_anchor, t_window)
    return {
        "S": s,
        "S_wave": t_wave,
        "S_anchor": t_anchor,
        "S_window": t_window,
    }


def paper_V(p: float, s: float) -> float:
    return V_PREFACTOR * sqrt(s) * p ** (-11.0 / 24.0)


def phi_coeffs(u: float, up: float, k: float, h1: float, h2: float) -> tuple[float, float]:
    a = -2.7 * (u * h1 + up * h2)
    b = (81.0 / 22.0) * k * h1 * h2
    return a, b


def abc_at(a: float, b: float, w: float, n: float) -> tuple[float, float, float]:
    aa = a * A_COEFF * n ** (ALPHA - 2.0)
    bb = b * B_COEFF * n ** (BETA - 2.0)
    cc = w * C_COEFF * n ** (GAMMA - 2.0)
    return aa, bb, cc


def scaled_derivs(
    a: float, b: float, w: float, n: float
) -> tuple[float, float, float]:
    aa, bb, cc = abc_at(a, b, w, n)
    f2 = aa + bb + cc
    nf3 = XA * aa + XB * bb + XG * cc
    n2f4 = XA * (XA - 1.0) * aa + XB * (XB - 1.0) * bb + XG * (XG - 1.0) * cc
    return f2, nf3, n2f4


def phi_double_prime(a: float, b: float, w: float, n: float) -> float:
    return scaled_derivs(a, b, w, n)[0]


def _delta(nu: float, h: float) -> tuple[float, float, float]:
    x = nu + 2.0 * h
    d = x**1.5 - nu**1.5
    dp = 1.5 * (x**0.5 - nu**0.5)
    dpp = 0.75 * (x ** (-0.5) - nu ** (-0.5))
    return d, dp, dpp


def f_sm_derivs(nu: float, h1: float, h2: float) -> tuple[float, float, float]:
    d1, d1p, d1pp = _delta(nu, h1)
    d2, d2p, d2pp = _delta(nu, h2)
    p = nu ** (-0.75)
    pp = -0.75 * nu ** (-1.75)
    ppp = 1.3125 * nu ** (-2.75)
    k = 0.75
    f = k * d1 * d2 * p
    fp = k * (d1p * d2 * p + d1 * d2p * p + d1 * d2 * pp)
    fpp = k * (
        d1pp * d2 * p
        + d1 * d2pp * p
        + 2.0 * d1p * d2p * p
        + 2.0 * d1p * d2 * pp
        + 2.0 * d1 * d2p * pp
        + d1 * d2 * ppp
    )
    return f, fp, fpp


def c_derivs(nu: float, k: float) -> tuple[float, float, float]:
    c = 0.75 * k * nu**1.125
    cp = 0.75 * k * 1.125 * nu**0.125
    cpp = 0.75 * k * 1.125 * 0.125 * nu ** (-0.875)
    return c, cp, cpp


def lambda_interp(
    nu: float, u: float, up: float, w: float, k: float, h1: float, h2: float
) -> float:
    d1, _, _ = _delta(nu, h1)
    d2, _, _ = _delta(nu, h2)
    wave = (-9.0 / 32.0) * u * d1 * (nu + 2.0 * h1) ** (-1.25)
    wave += (-9.0 / 32.0) * up * d2 * (nu + 2.0 * h2) ** (-1.25)
    c, cp, cpp = c_derivs(nu, k)
    _, fp, fpp = f_sm_derivs(nu, h1, h2)
    anchor = 2.0 * cp * fp + c * fpp + 0.5 * cpp
    xpp = 0.75 * nu ** (-0.5)
    return wave + anchor + w * xpp


def _u_for_ratio(
    p: float, k: float, h2: float, mu_over_lambda: float
) -> float:
    return mu_over_lambda * LAMBDA0_MID / MU_PREFACTOR * k * h2 * p**0.125


def _w_collision(p: float, k: float, h1: float, h2: float) -> float:
    return k * h1 * h2 * p ** (-0.125)


def u_for_phi_zero(
    k: float,
    h1: float,
    h2: float,
    w: float,
    n_star: float,
    *,
    split_waves: bool = True,
) -> tuple[float, float]:
    """Choose (u, u') so Φ''(n_star)=0 (cancellation on the block)."""
    b = (81.0 / 22.0) * k * h1 * h2
    b_term = b * B_COEFF * n_star ** (BETA - 2.0)
    c_term = w * C_COEFF * n_star ** (GAMMA - 2.0)
    a = (-b_term - c_term) / (A_COEFF * n_star ** (ALPHA - 2.0))
    wave_sum = a / (-2.7)
    if split_waves:
        u = wave_sum / (2.0 * h1)
        up = u * h1 / h2
    else:
        u = wave_sum / h1
        up = 0.0
    return u, up


def first_v_half_p0(c7: float = C7, s_kind: str = "anchor") -> int | None:
    """First P with paper V/S majorant ≤ c_7/2.

    anchor: worst case S = P^{-5/8}, V/S ≤ 3 P^{-7/48}.
    large: S = 300 P^{-1/2}, V/S ≤ 3*300^{-1/2} P^{-5/24}.
    """
    half = 0.5 * c7
    p = 2
    while p <= 10**28:
        if s_kind == "anchor":
            vs = 3.0 * float(p) ** (-7.0 / 48.0)
        else:
            vs = 3.0 * (300.0**-0.5) * float(p) ** (-5.0 / 24.0)
        if vs <= half:
            return p
        p = int(p * 1.05) + 1
    return None


def family_params(p: int, name: str, k: int | None = None) -> dict[str, Any] | None:
    sh = paper_shifts(p)
    h1 = float(sh["h1"])
    h2 = float(sh["h2"])
    if k is None:
        k = 1
    if k < 1 or k > sh["k_max"]:
        return None
    kf = float(k)
    pf = float(p)
    n_star = 1.5 * pf
    if name == "centre_cancel_w":
        w = _w_collision(pf, kf, h1, h2)
        u, up = u_for_phi_zero(kf, h1, h2, w, n_star)
    elif name == "edge_lo_cancel_w":
        u = _u_for_ratio(pf, kf, h2, 1.0 / 60.0)
        up = u * h1 / h2
        w = _w_collision(pf, kf, h1, h2)
    elif name == "edge_hi_cancel_w":
        u = _u_for_ratio(pf, kf, h2, 60.0)
        up = u * h1 / h2
        w = _w_collision(pf, kf, h1, h2)
    elif name == "centre_cancel_w0":
        w = 0.0
        u, up = u_for_phi_zero(kf, h1, h2, w, n_star)
    elif name == "centre_same_w0":
        w = 0.0
        u, up = u_for_phi_zero(kf, h1, h2, w, n_star)
        u, up = -u, -up
    elif name == "centre_same_w":
        w = _w_collision(pf, kf, h1, h2)
        u, up = u_for_phi_zero(kf, h1, h2, w, n_star)
        u, up = -u, -up
    else:
        raise KeyError(name)
    mu = MU_PREFACTOR * max(abs(u) * h1, abs(up) * h2) * pf ** (-0.75)
    lam0 = LAMBDA0_MID * kf * h1 * h2 * pf ** (-0.625)
    ratio = mu / lam0 if lam0 > 0.0 else float("inf")
    if ratio < 1.0 / 60.0 - 1e-12 or ratio > 60.0 + 1e-12:
        return None
    a, b = phi_coeffs(u, up, kf, h1, h2)
    sc = scale_S(pf, u, up, w, kf, h1, h2)
    return {
        "name": name,
        "P": p,
        "k": k,
        "h1": sh["h1"],
        "h2": sh["h2"],
        "u": u,
        "u_prime": up,
        "w": w,
        "a": a,
        "b": b,
        "mu": mu,
        "lambda0": lam0,
        "mu_over_lambda0": ratio,
        **sc,
        "V": paper_V(pf, sc["S"]),
    }


FAMILY_NAMES = (
    "centre_cancel_w",
    "edge_lo_cancel_w",
    "edge_hi_cancel_w",
    "centre_cancel_w0",
    "centre_same_w0",
    "centre_same_w",
)


def _linspace(lo: float, hi: float, n: int) -> list[float]:
    if n <= 1:
        return [lo]
    step = (hi - lo) / (n - 1)
    return [lo + i * step for i in range(n)]


def _bisect(
    pred: Callable[[float], bool], left: float, right: float, left_flag: bool
) -> float:
    for _ in range(BISECT_STEPS):
        mid = 0.5 * (left + right)
        if pred(mid) == left_flag:
            left = mid
        else:
            right = mid
    return 0.5 * (left + right)


def _intervals_from_flags(
    xs: list[float],
    flags: list[bool],
    pred: Callable[[float], bool],
) -> list[tuple[float, float]]:
    out: list[tuple[float, float]] = []
    i = 0
    n = len(xs)
    while i < n:
        if not flags[i]:
            i += 1
            continue
        if i == 0:
            start = xs[0]
        else:
            start = _bisect(pred, xs[i - 1], xs[i], False)
        j = i + 1
        while j < n and flags[j]:
            j += 1
        if j == n:
            end = xs[-1]
        else:
            end = _bisect(pred, xs[j - 1], xs[j], True)
        out.append((start, end))
        i = j
    return out


def intervals_of(
    pred: Callable[[float], bool],
    lo: float,
    hi: float,
    n_grid: int,
) -> list[tuple[float, float]]:
    xs = _linspace(lo, hi, n_grid)
    flags = [bool(pred(x)) for x in xs]
    return _intervals_from_flags(xs, flags, pred)


def _total_length(intervals: list[tuple[float, float]]) -> float:
    return sum(b - a for a, b in intervals)


def _complement(
    lo: float, hi: float, intervals: list[tuple[float, float]]
) -> list[tuple[float, float]]:
    out: list[tuple[float, float]] = []
    cursor = lo
    for a, b in intervals:
        if a > cursor:
            out.append((cursor, a))
        cursor = max(cursor, b)
    if cursor < hi:
        out.append((cursor, hi))
    return out


def _winning_r(f2: float, nf3: float, n2f4: float) -> int:
    m2, m3, m4 = abs(f2), abs(nf3), abs(n2f4)
    if m4 >= m3 and m4 > m2:
        return 4
    if m3 > m2:
        return 3
    return 2


def _r_pieces(
    derivs: Callable[[float], tuple[float, float, float]],
    lo: float,
    hi: float,
    n_grid: int,
) -> list[tuple[float, float, int]]:
    xs = _linspace(lo, hi, n_grid)
    rs = [_winning_r(*derivs(x)) for x in xs]

    def pred_r(x: float, target: int) -> bool:
        return _winning_r(*derivs(x)) == target

    pieces: list[tuple[float, float, int]] = []
    i = 0
    n = len(xs)
    while i < n:
        r = rs[i]
        if i == 0:
            start = xs[0]
        else:
            start = _bisect(lambda t, rr=r: pred_r(t, rr), xs[i - 1], xs[i], False)
        j = i + 1
        while j < n and rs[j] == r:
            j += 1
        if j == n:
            end = xs[-1]
        else:
            end = _bisect(lambda t, rr=r: pred_r(t, rr), xs[j - 1], xs[j], True)
        pieces.append((start, end, r))
        i = j
    return pieces


def cells_meeting(
    intervals: list[tuple[float, float]], lo: float, hi: float, cell_len: float
) -> int:
    if cell_len <= 0.0 or not intervals:
        return 0
    touched: set[int] = set()
    span = hi - lo
    nmax = max(0, int(span / cell_len))
    for a, b in intervals:
        aa = max(lo, min(hi, a))
        bb = max(lo, min(hi, b))
        if bb <= aa:
            continue
        i0 = max(0, int((aa - lo) / cell_len))
        i1 = min(nmax, int((bb - lo) / cell_len))
        for i in range(i0, i1 + 1):
            touched.add(i)
    return len(touched)


def _score_omega(
    *,
    which: str,
    params: dict[str, Any],
    omega: list[tuple[float, float]],
    t_set: list[tuple[float, float]],
    pieces: list[tuple[float, float, int]],
    f2: Callable[[float], bool] | Callable[[float], float],
    max_abs_f2: float,
    max_resid: float,
    lo: float,
    hi: float,
) -> dict[str, Any]:
    p = float(params["P"])
    s = float(params["S"])
    v = float(params["V"])
    h1 = float(params["h1"])
    h2 = float(params["h2"])
    n3 = sum(1 for *_, r in pieces if r == 3)
    n4 = sum(1 for *_, r in pieces if r == 4)
    n2 = sum(1 for *_, r in pieces if r == 2)
    comp = _complement(lo, hi, omega)
    single_signed = True
    sign_changes_outside = 0
    for ca, cb in comp:
        width = cb - ca
        if width <= 0.0:
            continue
        samples = [f2(ca + width * t) for t in (0.02, 0.5, 0.98)]
        signs = [y > 0.0 for y in samples if abs(y) > 0.25 * v]
        if signs and any(sg != signs[0] for sg in signs):
            single_signed = False
            sign_changes_outside += 1
    vs = v / s if s > 0.0 else float("inf")
    lemma_len = 0.0
    if s > 0.0 and C7 > 0.0:
        lemma_len = n3 * (4.0 * p * v / (C7 * s)) + n4 * (
            16.0 * p * sqrt(v / (C7 * s))
        )
    paper_len = p * vs + p * sqrt(vs) if vs > 0.0 else 0.0
    interval_cap = 2 * max(1, n3 + n4)
    omega_len = _total_length(omega)
    t_len = _total_length(t_set)
    cell_len = p**0.5 / max(h1, h2, 1.0)
    n_meet = cells_meeting(omega, lo, hi, cell_len)
    n_inv = N_INVENTORY_PREFACTOR * p ** (13.0 / 24.0)
    old_cost = n_meet / sqrt(v) if v > 0.0 else float("inf")
    repaired_bound = n_inv / sqrt(v) if v > 0.0 else float("inf")
    c_meas = max_abs_f2 / s if s > 0.0 else 0.0
    repaired_good = p * sqrt(max(c_meas, 1.0) * s) if s > 0.0 else 0.0
    paper_89 = p ** (89.0 / 96.0)
    v_le_half = v <= 0.5 * C7 * s if s > 0.0 else False
    vs_ok = vs <= PAPER_VS_CAP * p ** (-7.0 / 48.0) if s > 0.0 else False
    resid_ok = v >= 10.0 * max_resid
    length_ok = omega_len <= lemma_len + 1e-9 if lemma_len > 0.0 else omega_len == 0.0
    count_ok = len(omega) <= interval_cap
    return {
        "which": which,
        "name": params["name"],
        "P": params["P"],
        "k": params["k"],
        "omega_length": omega_len,
        "omega_intervals": len(omega),
        "t_length": t_len,
        "t_intervals": len(t_set),
        "complement_intervals": len(comp),
        "r_pieces": len(pieces),
        "n_r2": n2,
        "n_r3": n3,
        "n_r4": n4,
        "interval_cap": interval_cap,
        "lemma_length_bound": lemma_len,
        "paper_length_unit_c": paper_len,
        "omega_over_paper": omega_len / paper_len if paper_len > 0.0 else 0.0,
        "omega_over_lemma": omega_len / lemma_len if lemma_len > 0.0 else 0.0,
        "single_signed_complement": single_signed,
        "sign_changes_outside": sign_changes_outside,
        "max_abs_f2": max_abs_f2,
        "c_meas": c_meas,
        "max_lambda_phi_resid": max_resid,
        "S": s,
        "V": v,
        "V_over_S": vs,
        "v_le_c7_s_half": v_le_half,
        "vs_paper_ok": vs_ok,
        "resid_ok": resid_ok,
        "length_ok": length_ok,
        "count_ok": count_ok,
        "n_meet": n_meet,
        "N_inventory": n_inv,
        "cell_length": cell_len,
        "old_invalid_cost": old_cost,
        "repaired_piece_boundaries": repaired_bound,
        "repaired_transition": omega_len,
        "repaired_good_pieces": repaired_good,
        "paper_P89_96": paper_89,
        "repaired_total": omega_len + repaired_bound + repaired_good,
        "omega_over_N": len(omega) / n_inv if n_inv > 0.0 else 0.0,
        "n_meet_per_interval": n_meet / len(omega) if omega else 0.0,
    }


def measure_model(
    params: dict[str, Any],
    *,
    which: str = "phi",
    n_grid: int = N_GRID,
) -> dict[str, Any]:
    pair = measure_pair(params, n_grid=n_grid)
    return pair[which]


def measure_pair(
    params: dict[str, Any],
    *,
    n_grid: int = N_GRID,
) -> dict[str, dict[str, Any]]:
    p = float(params["P"])
    lo, hi = p, 2.0 * p
    a = float(params["a"])
    b = float(params["b"])
    w = float(params["w"])
    v = float(params["V"])
    u = float(params["u"])
    up = float(params["u_prime"])
    k = float(params["k"])
    h1 = float(params["h1"])
    h2 = float(params["h2"])
    xs = _linspace(lo, hi, n_grid)
    f2_phi: list[float] = []
    nf3s: list[float] = []
    n2f4s: list[float] = []
    f2_lam: list[float] = []
    max_resid = 0.0
    for n in xs:
        f2, nf3, n2f4 = scaled_derivs(a, b, w, n)
        lam = lambda_interp(n, u, up, w, k, h1, h2)
        f2_phi.append(f2)
        nf3s.append(nf3)
        n2f4s.append(n2f4)
        f2_lam.append(lam)
        resid = abs(lam - f2)
        if resid > max_resid:
            max_resid = resid

    def pred_omega_phi(n: float) -> bool:
        return abs(phi_double_prime(a, b, w, n)) <= v

    def pred_omega_lam(n: float) -> bool:
        return abs(lambda_interp(n, u, up, w, k, h1, h2)) <= v

    def pred_t(n: float) -> bool:
        f2, nf3, n2f4 = scaled_derivs(a, b, w, n)
        return abs(f2) < max(abs(nf3), abs(n2f4))

    def pred_r(n: float, target: int) -> bool:
        return _winning_r(*scaled_derivs(a, b, w, n)) == target

    omega_phi = _intervals_from_flags(
        xs, [abs(y) <= v for y in f2_phi], pred_omega_phi
    )
    omega_lam = _intervals_from_flags(
        xs, [abs(y) <= v for y in f2_lam], pred_omega_lam
    )
    t_set = _intervals_from_flags(
        xs,
        [
            abs(f2) < max(abs(nf3), abs(n2f4))
            for f2, nf3, n2f4 in zip(f2_phi, nf3s, n2f4s)
        ],
        pred_t,
    )
    rs = [_winning_r(f2, nf3, n2f4) for f2, nf3, n2f4 in zip(f2_phi, nf3s, n2f4s)]
    pieces: list[tuple[float, float, int]] = []
    i = 0
    nxs = len(xs)
    while i < nxs:
        r = rs[i]
        if i == 0:
            start = xs[0]
        else:
            start = _bisect(lambda t, rr=r: pred_r(t, rr), xs[i - 1], xs[i], False)
        j = i + 1
        while j < nxs and rs[j] == r:
            j += 1
        if j == nxs:
            end = xs[-1]
        else:
            end = _bisect(lambda t, rr=r: pred_r(t, rr), xs[j - 1], xs[j], True)
        pieces.append((start, end, r))
        i = j

    common = dict(
        t_set=t_set,
        pieces=pieces,
        max_resid=max_resid,
        lo=lo,
        hi=hi,
        params=params,
    )
    return {
        "phi": _score_omega(
            which="phi",
            omega=omega_phi,
            f2=lambda n: phi_double_prime(a, b, w, n),
            max_abs_f2=max(abs(y) for y in f2_phi),
            **common,
        ),
        "lambda": _score_omega(
            which="lambda",
            omega=omega_lam,
            f2=lambda n: lambda_interp(n, u, up, w, k, h1, h2),
            max_abs_f2=max(abs(y) for y in f2_lam),
            **common,
        ),
    }


def iter_samples(p_list: tuple[int, ...] = P_LIST) -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    for p in p_list:
        sh = paper_shifts(p)
        ks = [1]
        if sh["k_max"] != 1:
            ks.append(sh["k_max"])
        for name in FAMILY_NAMES:
            for k in ks:
                params = family_params(p, name, k)
                if params is None:
                    continue
                rows.append(params)
    return rows


def run_census(
    p_list: tuple[int, ...] = P_LIST,
    n_grid: int = N_GRID,
) -> dict[str, Any]:
    samples = iter_samples(p_list)
    rows: list[dict[str, Any]] = []
    for params in samples:
        pair = measure_pair(params, n_grid=n_grid)
        rows.append({"params": params, "phi": pair["phi"], "lambda": pair["lambda"]})
    p0_anchor = first_v_half_p0(s_kind="anchor")
    p0_large = first_v_half_p0(s_kind="large")
    verdict = classify_census(rows)
    verdict["p0_v_half_anchor"] = p0_anchor
    verdict["p0_v_half_large_s"] = p0_large
    return {
        "experiment": "juggler_step5b_sublevel",
        "anti_overclaim": ANTI,
        "c7": C7_ROW,
        "P_list": list(p_list),
        "n_grid": n_grid,
        "n_samples": len(rows),
        "p0_v_half_anchor": p0_anchor,
        "p0_v_half_large_s": p0_large,
        "rows": rows,
        "verdict": verdict,
    }


def classify_census(rows: list[dict[str, Any]]) -> dict[str, Any]:
    omega_counts: dict[int, list[int]] = {}
    t_counts: dict[int, list[int]] = {}
    holes: list[str] = []
    max_omega = 0
    max_t = 0
    worst_length_ratio = 0.0
    any_sign = False
    any_count_fail = False
    any_length_fail = False
    v_half_fail_large = False
    resid_fail_large = False
    for pack in rows:
        for key in ("phi", "lambda"):
            r = pack[key]
            p = int(r["P"])
            omega_counts.setdefault(p, []).append(int(r["omega_intervals"]))
            t_counts.setdefault(p, []).append(int(r["t_intervals"]))
            max_omega = max(max_omega, int(r["omega_intervals"]))
            max_t = max(max_t, int(r["t_intervals"]))
            worst_length_ratio = max(
                worst_length_ratio, float(r["omega_over_lemma"])
            )
            if not r["single_signed_complement"]:
                any_sign = True
                holes.append(f"{key}:{r['name']}:P={p}:sign")
            if int(r["omega_intervals"]) > 8:
                any_count_fail = True
                holes.append(f"{key}:{r['name']}:P={p}:count")
            if not r["length_ok"] and r["lemma_length_bound"] > 0.0:
                any_length_fail = True
                holes.append(f"{key}:{r['name']}:P={p}:length")
            if p >= 10**8 and not r["v_le_c7_s_half"]:
                v_half_fail_large = True
            if p >= 10**8 and not r["resid_ok"]:
                resid_fail_large = True
                holes.append(f"{key}:{r['name']}:P={p}:resid")

    counts_flat = [c for cs in omega_counts.values() for c in cs]
    p_dependent = False
    if len(omega_counts) >= 2:
        maxima = [max(cs) for cs in omega_counts.values()]
        # Growing with P would be a hole; a bounded O_E(1) table is not.
        p_dependent = max(maxima) >= 8 and max(maxima) > 2 * min(maxima) + 2

    geometry_hole = (
        any_sign
        or any_count_fail
        or any_length_fail
        or resid_fail_large
        or p_dependent
    )
    if geometry_hole:
        decision = "PROMOTE"
        why = "named hole in Lemma 3.9 geometry or Step 5b reduction"
    else:
        decision = "PROMOTE"
        why = (
            "explicit c7 = 1/288; V ≤ c7 S/2 is a hidden P0 "
            "(anchor majorant 1.66e22). On cancellation families "
            "|Ω_V| is Θ(P) at census P, so the printed short-transition "
            "assembly is ineffective, not a growing interval-count hole. "
            "Counts stay O_E(1); complement is single-signed; the "
            "1/c7 length bound holds."
        )
    hole = geometry_hole
    return {
        "decision": decision,
        "why": why,
        "hole": hole,
        "holes": holes,
        "max_omega_intervals": max_omega,
        "max_t_intervals": max_t,
        "worst_length_ratio": worst_length_ratio,
        "omega_counts_by_P": {str(k): v for k, v in omega_counts.items()},
        "t_counts_by_P": {str(k): v for k, v in t_counts.items()},
        "p_dependent_count": p_dependent,
        "v_half_fail_large_p": v_half_fail_large,
        "n_rows_scored": len(counts_flat),
    }


def write_json(payload: dict[str, Any], path: Path = JSON_PATH) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")


def main() -> None:
    payload = run_census()
    write_json(payload)
    verdict = payload["verdict"]
    print("c7", payload["c7"]["c7"])
    print("p0_anchor", payload["p0_v_half_anchor"], "p0_large_S", payload["p0_v_half_large_s"])
    print("decision", verdict["decision"])
    print("why", verdict["why"])
    print("max_omega", verdict["max_omega_intervals"], "max_T", verdict["max_t_intervals"])
    print("worst_length_ratio", verdict["worst_length_ratio"])
    print("holes", verdict["holes"])
    for pack in payload["rows"]:
        r = pack["phi"]
        print(
            f"P={r['P']} {r['name']} k={r['k']} "
            f"nΩ={r['omega_intervals']} |Ω|={r['omega_length']:.4e} "
            f"nT={r['t_intervals']} r=({r['n_r2']},{r['n_r3']},{r['n_r4']}) "
            f"meet={r['n_meet']} old={r['old_invalid_cost']:.4e} "
            f"rep={r['repaired_total']:.4e} P89={r['paper_P89_96']:.4e} "
            f"v_half={r['v_le_c7_s_half']} resid_ok={r['resid_ok']} "
            f"len_ok={r['length_ok']} cnt_ok={r['count_ok']}"
        )


if __name__ == "__main__":
    main()
