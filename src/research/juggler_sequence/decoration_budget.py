"""Decoration-and-mode budget census for Paper B Lemma 5.2 / Theorems 5.3, 6.1.

Phase-0 only. Not a Paper B edit, not a harvest reopen, not a K3
attack, not a halt theorem. Enumerates the printed Step-3 / Step-A
pieces at the paper's (H1, H2, k) and checks them against the
printed budgets. Orbit geometry is sampled, not exhaustive at 10^10.
"""

from __future__ import annotations

from research.juggler_sequence.lean_paths import (
    DATA_ROOT,
)

import json
from fractions import Fraction
import math
from math import ceil, isqrt
from pathlib import Path
from typing import Any

DATA_DIR = DATA_ROOT / "decoration_budget"
JSON_PATH = DATA_DIR / "summary.json"

P_LIST = (10**6, 10**8, 10**10)
P0_T_LINE = 3**48  # |t| <= 3 J2 <= P^{1/16} needs P >= 3^{48}

# Algebra of Theorem 6.1 Step E / Theorem 5.3 Step 5a.
KERNEL_SMOOTH = Fraction(945, 512)
KERNEL_WINDOW = Fraction(27, 64)  # = 216/512
KERNEL_COMPOSITE = KERNEL_SMOOTH - KERNEL_WINDOW  # 729/512
DECORATED_WINDOW = Fraction(135, 128)  # = 540/512; 2.5 * 27/64
DECORATED_COMPOSITE = KERNEL_SMOOTH - DECORATED_WINDOW  # 405/512
THETA_FACTOR = Fraction(5, 2)  # passengers multiply the window-centre term
OFFSET_RATIO_DECORATED = KERNEL_SMOOTH / DECORATED_WINDOW  # 945/540 = 7/4

ANTI = {
    "halt_theorem": False,
    "paper_a_modified": False,
    "paper_b_modified": False,
    "harvest_reopened": False,
    "k3_reopened": False,
    "kernel_retagged": False,
}


def paper_scales(p: float) -> dict[str, float]:
    """Real scales as printed: H1 = P^{1/48}, H2 = J2 = P^{1/24}."""
    return {
        "P": p,
        "H1": p ** (1.0 / 48.0),
        "H2": p ** (1.0 / 24.0),
        "J2": p ** (1.0 / 24.0),
        "J3": p ** (1.0 / 96.0),
        "J_W": p ** 0.25,
        "k_kernel": p ** (1.0 / 24.0),
        "k_depth4": 2.0 * p ** (1.0 / 96.0),
        "cap_q": p ** (1.0 / 16.0),
        "cap_uh": p ** 0.5,
        "cap_h": p ** 0.125,
        "cap_ijk": 2.0 * p ** (1.0 / 96.0),
        "cap_d3_pp": 3.0 * (p ** (1.0 / 24.0)) * (p ** (1.0 / 48.0)) * (p ** (1.0 / 24.0)) * p ** (-5.0 / 8.0),
        "ratio_t_over_cap": 3.0 * p ** (-1.0 / 48.0),
    }


def paper_ints(p: int) -> dict[str, int]:
    """Integer shifts used on the orbit: ceil of the printed scales."""
    return {
        "P": p,
        "h1": max(1, ceil(p ** (1.0 / 48.0))),
        "h2": max(1, ceil(p ** (1.0 / 24.0))),
        "k_kernel": max(1, ceil(p ** (1.0 / 24.0))),
        "k_depth4": max(1, ceil(2.0 * p ** (1.0 / 96.0))),
    }


def _overflow_kind(value: float, cap: float, dies: bool) -> str:
    """dies=True means value/cap → 0 as P → ∞ (P0, not Theorem-T)."""
    if value <= cap + 1e-12:
        return "none"
    return "p0" if dies else "structural"


def _row(
    source: str,
    klass: str,
    value: float,
    cap: float,
    dies: bool,
    *,
    q: float | None = None,
    u: float | None = None,
    j: float | None = None,
    h: float | None = None,
    h_prime: float | None = None,
    note: str = "",
) -> dict[str, Any]:
    kind = _overflow_kind(value, cap, dies)
    return {
        "source": source,
        "q": q,
        "u": u,
        "j": j,
        "h": h,
        "h_prime": h_prime,
        "class": klass,
        "value": value,
        "cap": cap,
        "ratio": (value / cap) if cap else None,
        "overflow_kind": kind,
        "note": note,
    }


def combinatorial_inventory(p: float) -> dict[str, Any]:
    """Layer A: printed expansions at the paper endpoint, no orbit scan."""
    s = paper_scales(p)
    h1, h2 = s["H1"], s["H2"]
    j2, j3 = s["J2"], s["J3"]
    k = s["k_kernel"]
    cap_q, cap_uh, cap_h = s["cap_q"], s["cap_uh"], s["cap_h"]

    # (3a) Vaaler of {W}: |u| <= B + T, B <= 1.85 k h2 P^{1/8}, T = P^{1/2}/(2 h1).
    b_max = 1.85 * k * h2 * (p ** 0.125)
    t_vaaler = (p ** 0.5) / (2.0 * h1)
    u_max = b_max + t_vaaler
    uh1 = u_max * h1
    # Paper writes uh1 <= 1.85 P^{1/4} + P^{1/2}/2 using (C1). Direct endpoint:
    uh1_c1 = 1.85 * (p ** 0.25) + 0.5 * (p ** 0.5)

    # Products: one mode per layer, three layers. A corner can take two layers.
    t_max = 3.0 * j2
    qd_max = 2.0 * j2
    qd_passenger = 3.0 * j2 + j3

    # Term count of ρ: four Y-corners + u W + u' W' + D2 + D3 + slow {DD Y}.
    term_count = 9
    # i-passenger curvature vs (D3) cap (analytic, paper 2.3 i h1 h2 P^{-5/2}).
    i_max = s["cap_ijk"]
    i_curv = 2.3 * i_max * h1 * h2 * (p ** -2.5)
    d3_cap = 3.0 * k * h1 * h2 * (p ** (-5.0 / 8.0))

    rows = [
        _row(
            "step3a_W_uh",
            "Lemma 5.2(i)",
            uh1,
            cap_uh,
            True,
            u=u_max,
            h=h1,
            note="uh1 at paper (k,H1,H2); dies because leading extra is P^{11/48}",
        ),
        _row(
            "step3a_W_uh_C1",
            "Lemma 5.2(i)",
            uh1_c1,
            cap_uh,
            True,
            u=uh1_c1 / h1,
            h=h1,
            note="paper's (C1) majorant 1.85 P^{1/4} + P^{1/2}/2",
        ),
        _row(
            "step3a_h",
            "Lemma 5.2(i)",
            h1,
            cap_h,
            True,
            h=h1,
            note="H1 = P^{1/48} vs h <= P^{1/8}",
        ),
        _row(
            "step3b_q_Y",
            "D1",
            j2,
            cap_q,
            True,
            q=j2,
            h=h1,
            note="J2-mode on Y(n), Y(n+d1)",
        ),
        _row(
            "step3c_q_Y",
            "D1",
            j2,
            cap_q,
            True,
            q=j2,
            h=h2,
            note="mirror: J2-mode on Y(n+d2)",
        ),
        _row(
            "step3d_q_Y",
            "D1",
            j2,
            cap_q,
            True,
            q=j2,
            note="M4 carries: J2 on Y(n+d), d in {0,d2,d1+d2}",
        ),
        _row(
            "step3e_j",
            "D2",
            3.0,
            3.0,
            False,
            j=3.0,
            note="printed |j| <= 3; eight kappa-branches",
        ),
        _row(
            "product_t",
            "Lemma 5.2(ii)",
            t_max,
            cap_q,
            True,
            q=t_max,
            note="|t| <= 3 J2 vs P^{1/16}; ratio 3 P^{-1/48}",
        ),
        _row(
            "product_qd",
            "Lemma 5.2(ii)",
            qd_max,
            cap_q,
            True,
            q=qd_max,
            note="one corner can take two layers: |qd| <= 2 J2",
        ),
        _row(
            "term_count_rho",
            "decoration",
            float(term_count),
            8.0,
            True,
            note="4 Y-corners + 2 differenced-waves + D2 + D3 + slow; fixed 9",
        ),
        _row(
            "thm61_i",
            "Theorem 6.1",
            i_max,
            s["cap_ijk"],
            False,
            note="Vaaler J3 = P^{1/96}; range by construction",
        ),
        _row(
            "thm61_j_mode",
            "Theorem 6.1",
            i_max,
            s["cap_ijk"],
            False,
            j=i_max,
            note="|j| <= 2 P^{1/96} by construction",
        ),
        _row(
            "thm61_k",
            "Theorem 6.1",
            i_max,
            s["cap_ijk"],
            False,
            note="|k| <= 2 P^{1/96}; sits inside kernel k <= P^{1/24}",
        ),
        _row(
            "thm61_j_passenger_qd",
            "D1",
            qd_passenger,
            cap_q,
            True,
            q=qd_passenger,
            note="|qd| <= 3 P^{1/24} + P^{1/96} after the Y-passenger",
        ),
        _row(
            "thm61_i_passenger_D3",
            "D3",
            i_curv,
            d3_cap,
            True,
            note="2.3 i H1 H2 P^{-5/2} vs 3 k H1 H2 P^{-5/8}",
        ),
    ]
    return {
        "P": p,
        "scales": s,
        "rows": rows,
        "kinds": _kind_counts(rows),
    }


def _kind_counts(rows: list[dict[str, Any]]) -> dict[str, int]:
    out = {"none": 0, "p0": 0, "structural": 0}
    for row in rows:
        out[row["overflow_kind"]] = out.get(row["overflow_kind"], 0) + 1
    return out


def algebraic_theta_identities() -> dict[str, Any]:
    """Exact fractions of the printed 4.375 → 7:4 shrink."""
    bare_ratio = KERNEL_SMOOTH / KERNEL_WINDOW
    return {
        "kernel_smooth": [KERNEL_SMOOTH.numerator, KERNEL_SMOOTH.denominator],
        "kernel_window": [KERNEL_WINDOW.numerator, KERNEL_WINDOW.denominator],
        "kernel_composite": [KERNEL_COMPOSITE.numerator, KERNEL_COMPOSITE.denominator],
        "decorated_window": [DECORATED_WINDOW.numerator, DECORATED_WINDOW.denominator],
        "decorated_composite": [DECORATED_COMPOSITE.numerator, DECORATED_COMPOSITE.denominator],
        "theta_factor": [THETA_FACTOR.numerator, THETA_FACTOR.denominator],
        "bare_ratio": float(bare_ratio),
        "bare_ratio_is_4.375": bare_ratio == Fraction(35, 8),
        "decorated_ratio": float(OFFSET_RATIO_DECORATED),
        "decorated_ratio_is_7_4": OFFSET_RATIO_DECORATED == Fraction(7, 4),
        "composite_positive": DECORATED_COMPOSITE > 0,
        "window_is_2.5_times_kernel": DECORATED_WINDOW == THETA_FACTOR * KERNEL_WINDOW,
    }


def decorated_margin_scan(p: float, k: int = 1, j: int = 1) -> dict[str, Any]:
    """Numerical interpolant check of the 2.5 factor and 7:4 composite.

    Kernel model: φ_k(θ) = (3k/4) n^{9/8} F(X-θ) on an offset branch.
    Depth-4 model (Step E): φ_4(θ) = (9k/8) j (X-θ)^{5/4}.
    Finite differences in θ give the θ-coefficients; second n-derivatives
    of the smooth parts give the two curvatures.
    """
    n = 1.5 * p
    x = n ** 1.5
    ints = paper_ints(int(p)) if p >= 3 else {"h1": 1, "h2": 1}
    h1, h2 = ints["h1"], ints["h2"]
    d1, d2 = 2 * h1, 2 * h2
    n0 = int(n) | 1
    m0 = isqrt(n0**3)
    beta1 = isqrt((n0 + d1) ** 3) - m0
    beta2 = isqrt((n0 + d2) ** 3) - m0

    def f_branch(m: float) -> float:
        return (
            (m + beta1 + beta2 + j) ** 1.5
            - (m + beta1) ** 1.5
            - (m + beta2) ** 1.5
            + m**1.5
        )

    c = (3.0 * k / 4.0) * (n ** 1.125)
    # d/dm F via rationalized first differences: the raw four-sqrt
    # combination cancels 15 digits at P = 10^10.
    s_off = (x + beta1 + beta2 + j) ** 0.5 + (x + beta1) ** 0.5
    s_base = (x + beta2) ** 0.5 + x ** 0.5
    f_prime = 1.5 * ((beta2 + j) / s_off - beta2 / s_base)
    b_k = -c * f_prime
    b_k_pred = (9.0 / 16.0) * k * j * (n ** 0.375)
    b_4 = -(9.0 * k / 8.0) * j * 1.25 * (x ** 0.25)
    b_4_pred = (45.0 / 32.0) * k * j * (n ** 0.375)

    # Smooth-part second derivatives at the monomial models.
    cf_pp_k = (945.0 / 512.0) * k * j * (n ** -0.125)
    u_term_k = -(27.0 / 64.0) * k * j * (n ** -0.125)
    cf_pp_4 = (945.0 / 512.0) * k * j * (n ** -0.125)
    u_term_4 = -(135.0 / 128.0) * k * j * (n ** -0.125)

    return {
        "P": p,
        "n": n,
        "h1": h1,
        "h2": h2,
        "beta1": beta1,
        "beta2": beta2,
        "B_kernel_fd": b_k,
        "B_kernel_pred": b_k_pred,
        "B_kernel_ratio": abs(b_k / b_k_pred) if b_k_pred else None,
        "B_decorated_fd": b_4,
        "B_decorated_pred": b_4_pred,
        "B_decorated_ratio": abs(b_4 / b_4_pred) if b_4_pred else None,
        "theta_factor_fd": abs(b_4 / b_k) if b_k else None,
        "theta_factor_pred": 2.5,
        "kernel_composite_over_kj": (cf_pp_k + u_term_k) / (k * j * n ** -0.125),
        "kernel_ratio": abs(cf_pp_k / u_term_k),
        "decorated_composite_over_kj": (cf_pp_4 + u_term_4) / (k * j * n ** -0.125),
        "decorated_ratio": abs(cf_pp_4 / u_term_4),
        "decorated_single_signed": (cf_pp_4 + u_term_4) * (k * j) > 0,
    }


def branch_offset(n: int, d1: int, d2: int) -> int:
    """j = β12 - β1 - β2 = ΔΔ m, exact integers (Lemma 5.1(iii))."""
    m = isqrt(n**3)
    m1 = isqrt((n + d1) ** 3)
    m2 = isqrt((n + d2) ** 3)
    m12 = isqrt((n + d1 + d2) ** 3)
    return m12 - m1 - m2 + m


def _carries(n: int, d1: int, d2: int) -> tuple[int, int, int]:
    """Level-1 carries κ = [{X} + {ΔX} >= 1] at the three shifts."""
    s = 10**12

    def frac_x(t: int) -> int:
        return isqrt(t**3 * s * s) % s

    def frac_dx(t: int, d: int) -> int:
        return (isqrt((t + d) ** 3 * s * s) - isqrt(t**3 * s * s)) % s

    def kap(t: int, d: int) -> int:
        return 1 if frac_x(t) + frac_dx(t, d) >= s else 0

    return kap(n, d1), kap(n, d2), kap(n, d1 + d2)


def orbit_j_census(
    p: int,
    *,
    window: int = 100_000,
    samples: int = 100_000,
    boundary: int = 2_000,
) -> dict[str, Any]:
    """Layer B: exact j on a window / stride / cell-boundary sample."""
    ints = paper_ints(p)
    h1, h2 = ints["h1"], ints["h2"]
    d1, d2 = 2 * h1, 2 * h2
    start = p + 1 if (p % 2 == 0) else p
    if start % 2 == 0:
        start += 1

    max_abs = 0
    min_j = 0
    max_j = 0
    witness = None
    n_seen = 0
    live_j: set[int] = set()
    live_kappa: set[tuple[int, int, int]] = set()

    def ingest(n: int) -> None:
        nonlocal max_abs, min_j, max_j, witness, n_seen
        j = branch_offset(n, d1, d2)
        n_seen += 1
        live_j.add(j)
        if n_seen <= 400:
            live_kappa.add(_carries(n, d1, d2))
        if j < min_j:
            min_j = j
        if j > max_j:
            max_j = j
        aj = abs(j)
        if aj > max_abs:
            max_abs = aj
            witness = n

    # Consecutive window from the left endpoint.
    n = start
    for _ in range(window):
        ingest(n)
        n += 2

    # Stride sample through (P, 2P].
    span = p
    stride = max(2, 2 * (span // max(samples, 1)))
    if stride % 2 == 1:
        stride += 1
    n = start
    limit = 2 * p
    taken = 0
    while n < limit and taken < samples:
        ingest(n)
        n += stride
        taken += 1

    # Cell-boundary: a short run near 3P/2, where gaps are typical.
    n = (3 * p // 2) | 1
    for _ in range(boundary):
        if n >= 2 * p:
            break
        ingest(n)
        n += 2

    return {
        "P": p,
        "h1": h1,
        "h2": h2,
        "d1": d1,
        "d2": d2,
        "n_seen": n_seen,
        "min_j": min_j,
        "max_j": max_j,
        "max_abs_j": max_abs,
        "witness": witness,
        "live_j": sorted(live_j),
        "n_live_kappa": len(live_kappa),
        "kappa_cap": 8,
        "j_overflow": max_abs > 3,
    }


def i_passenger_curvature_fd(p: float) -> dict[str, Any]:
    """Analytic X'''' = (9/16) n^{-5/2} versus the printed (D3) cap.

    A fourth-difference stencil of n^{3/2} is below float64 at these P.
    """
    n = 1.5 * p
    x4 = (9.0 / 16.0) * (n ** -2.5)
    s = paper_scales(p)
    i_max = s["cap_ijk"]
    h1, h2, k = s["H1"], s["H2"], s["k_kernel"]
    # Paper: |ΔΔ(i X / 2)''| <= 2.3 i h1 h2 P^{-5/2}.
    i_curv = 2.3 * i_max * h1 * h2 * abs(x4)
    d3_cap = 3.0 * k * h1 * h2 * (p ** (-5.0 / 8.0))
    return {
        "X4": x4,
        "i_curvature": i_curv,
        "d3_cap": d3_cap,
        "ratio": i_curv / d3_cap if d3_cap else None,
        "overflow_kind": _overflow_kind(i_curv, d3_cap, True),
    }


def classify_census(payload: dict[str, Any]) -> dict[str, Any]:
    """Apply the Phase-0 decision rule once."""
    kinds = {"none": 0, "p0": 0, "structural": 0}
    for block in payload["inventories"]:
        for key, val in block["kinds"].items():
            kinds[key] = kinds.get(key, 0) + val
    j_overflow = any(row["j_overflow"] for row in payload["orbits"])
    theta_ok = (
        payload["algebra"]["decorated_ratio_is_7_4"]
        and payload["algebra"]["composite_positive"]
        and payload["algebra"]["window_is_2.5_times_kernel"]
        and all(m["decorated_single_signed"] for m in payload["margins"])
    )
    if j_overflow or kinds["structural"] or not theta_ok:
        decision = "CLOSE"
        why = "Theorem-T-type witness or 7:4 composite failed"
    elif kinds["p0"]:
        decision = "PARK"
        why = (
            "finite-P overflows die as P→∞ (ratio 3 P^{-1/48}→0); "
            f"named P0 for |t|<=3 J2<=P^{{1/16}} is P>={P0_T_LINE}"
        )
    else:
        decision = "PROMOTE"
        why = "every printed budget holds at the three P"
    return {
        "decision": decision,
        "why": why,
        "kinds": kinds,
        "j_overflow": j_overflow,
        "theta_ok": theta_ok,
        "p0_t_line": P0_T_LINE,
    }


def run_census(
    p_list: tuple[int, ...] = P_LIST,
    *,
    orbit_window: int = 20_000,
    orbit_samples: int = 20_000,
    orbit_boundary: int = 1_000,
) -> dict[str, Any]:
    inventories = [combinatorial_inventory(float(p)) for p in p_list]
    orbits = [
        orbit_j_census(
            p,
            window=orbit_window,
            samples=orbit_samples,
            boundary=orbit_boundary,
        )
        for p in p_list
    ]
    margins = [decorated_margin_scan(float(p)) for p in p_list]
    curvatures = [i_passenger_curvature_fd(float(p)) for p in p_list]
    payload = {
        "experiment": "juggler_decoration_budget",
        "anti_overclaim": ANTI,
        "P_list": list(p_list),
        "algebra": algebraic_theta_identities(),
        "inventories": inventories,
        "orbits": orbits,
        "margins": margins,
        "i_passenger_curvatures": curvatures,
    }
    payload["verdict"] = classify_census(payload)
    return payload


def write_json(payload: dict[str, Any], path: Path = JSON_PATH) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")



# --- Lemma 5.1(iii): the branch offset j, and how large it really gets ---
#
# beta_i = m(n + d_i) - m(n) with m = floor(n^{3/2}), so beta_i = floor(Delta_i X + theta)
# exactly, theta = X - m.  Hence
#
#     j = beta_12 - beta_1 - beta_2
#       = floor(A + B + eps + theta) - floor(A + theta) - floor(B + theta)
#       = floor( {A + theta} + {B + theta} - theta + eps ),   eps = DeltaDelta X,
#
# one floor of an argument in (-1, 3) whenever 0 < eps < 1, so j is in {-1, 0, 1, 2}.
# The manuscript prints |j| <= 3, which is what one gets by adding the corner floor
# range [-1, 2] to a carry vector in {0,1}^3 as though the two were independent.  They
# are not: all three carries are floor(. + theta) at the same theta.
#
# Everything below is exact integer arithmetic -- floor(n^{3/2}) = isqrt(n^3).

OFFSET_RANGE = (-1, 2)          # attained, both ends
OFFSET_RANGE_PRINTED = (-3, 3)  # the free-carry reading


def m_floor(n: int) -> int:
    """``floor(n^(3/2))``, exactly."""
    return isqrt(n * n * n)


def offset_at(n: int, h1: int, h2: int) -> int:
    """``branch_offset`` addressed by half-shifts: ``d_i = 2 h_i``, as the lemma states them."""
    return branch_offset(n, 2 * h1, 2 * h2)


def hypothesis_limit(p: int) -> int:
    """The lemma's ``h1 h2 <= P^(1/2)/3``, as an integer bound on the product."""
    return isqrt(p) // 3


def branch_offset_census(p: int, hmax: int = 40, stride: int | None = None) -> dict[str, Any]:
    """Attained values of ``j`` over ``n in (P, 2P]`` under the lemma's own hypothesis."""
    lim = hypothesis_limit(p)
    step = stride or max(1, p // 400) | 1
    counts: dict[int, int] = {}
    extreme: tuple[int, int, int, int] | None = None
    for n in range(p + 1, 2 * p + 1, step):
        for h1 in range(1, hmax + 1):
            for h2 in range(1, hmax + 1):
                if h1 * h2 > lim:
                    continue
                j = offset_at(n, h1, h2)
                counts[j] = counts.get(j, 0) + 1
                if extreme is None or abs(j) > abs(extreme[0]):
                    extreme = (j, n, h1, h2)
    return {"P": p, "product_limit": lim, "samples": sum(counts.values()),
            "counts": dict(sorted(counts.items())),
            "attained": (min(counts), max(counts)) if counts else None,
            "extreme": extreme, "within_printed_bound": all(abs(j) <= 3 for j in counts),
            "within_true_bound": all(abs(j) <= 2 for j in counts)}


def branch_offset_ladder(p: int, multiples: tuple[int, ...] = (1, 2, 3, 6),
                         hmax: int = 120, stride: int | None = None) -> dict[str, Any]:
    """``j``'s attained range as the product is allowed past the hypothesis.

    The printed ``|j| <= 3`` is the bound at *twice* the stated hypothesis: the range grows
    by one for each unit of ``eps = 3 h1 h2 / sqrt(xi)``, so ``m`` times the limit gives
    ``j <= m + 1``.  Evidence that the printed 3 is an off-by-one between a lemma's
    hypothesis and its conclusion rather than a different argument.
    """
    lim = hypothesis_limit(p)
    step = stride or max(1, p // 250) | 1
    rows = []
    for mult in multiples:
        seen: set[int] = set()
        for n in range(p + 1, 2 * p + 1, step):
            for h1 in range(1, hmax + 1):
                for h2 in range(1, hmax + 1):
                    if h1 * h2 > mult * lim:
                        continue
                    seen.add(offset_at(n, h1, h2))
        rows.append({"multiple": mult, "product_limit": mult * lim,
                     "attained": sorted(seen), "max": max(seen), "min": min(seen)})
    return {"P": p, "rows": rows,
            "max_is_multiple_plus_one": all(r["max"] == r["multiple"] + 1 for r in rows),
            "min_is_always_minus_one": all(r["min"] == -1 for r in rows)}


def branch_offset_in_applied_range(p: int) -> dict[str, Any]:
    """Lemma 5.2 runs at ``h1, h2 <= P^(1/24)``, where ``eps`` is tiny and ``j = 2`` is not seen.

    An observation, not a theorem: ``j = 2`` needs ``{A+theta} + {B+theta} >= 2 - eps + theta``,
    a set of measure ``~eps^2/2``, and ``eps <= 3 P^(1/12 - 1/2)`` here.  The bound stated in
    the lemma must still be the one for the lemma's own hypothesis.
    """
    hmax = max(2, round(p ** (1 / 24)))
    counts: dict[int, int] = {}
    for n in range(p + 1, min(2 * p, p + 400001) + 1, 4001):
        for h1 in range(1, hmax + 1):
            for h2 in range(1, hmax + 1):
                j = offset_at(n, h1, h2)
                counts[j] = counts.get(j, 0) + 1
    return {"P": p, "h_max": hmax, "eps_max": 3.0 * hmax * hmax / p**0.5,
            "counts": dict(sorted(counts.items())), "attained": (min(counts), max(counts))}


# The widened (D1) theta-coefficient of Lemma 5.2(iii) is |q'|(2|j'| P^(-1/4) + 20 h h' P^(-3/4)).
# At |j'| <= 2 the first summand is 4 P^(1/4)/h' and the collected constant is 5, not 7.
WIDENED_THETA_CONST = 5
WIDENED_THETA_CONST_PRINTED = 7


def widened_theta_constant(j_max: int = 2) -> dict[str, Any]:
    """The collected constant and the certificate row it sets, as a function of ``max |j|``."""
    lead = 2 * j_max
    return {"j_max": j_max, "lead": lead, "collected": lead + 1,
            "valid_from": 20 ** (8 / 3),          # 20 P^(-1/8) <= P^(1/4)
            "mode_index_row": (lead + 1) ** 16}   # (lead+1) P^(1/4) <= P^(5/16)



def beta_inventory_attained(p: int, hmax: int = 7, stride: int | None = None) -> dict[str, Any]:
    """What Lemma 5.1(iii)'s ``beta``-inventory actually attains, against what it prints.

    The offset erratum came from bounding two quantities separately that one variable
    determines.  This is the same scan over the rest of the lemma.  The ``beta``-product is
    clean -- both factors are extremal at the same ``n = 2P``, so ``beta1 beta2/(h1 h2 P)``
    attains ``18 = (3 sqrt 2)^2`` and the Lean pair ``beta_i <= 4.25 h_i P^(1/2) + 1`` loses
    only the rounding.  The three bounds built on it are not, because each pairs the product
    with a power of ``nu`` taken at the other end of the block:

    ```text
      (3/4) b1 b2 (m+xi2)^(-1/2) / (h1 h2 P^(1/4))   printed [1.4, 15]  attained [27/4, (27/4)2^(1/4)]
      beta-part of |G'|  / (h1 h2 P^(-3/4))          printed 20         attained 81/16
      beta-part of |G''| / (h1 h2 P^(-7/4))          printed 25         attained 567/64
    ```

    Nothing here is sharpened: see the note at the lemma for why none of the three propagates
    anywhere that binds.
    """
    step = stride or max(1, p // 300) | 1
    prod = 0.0
    term_lo, term_hi = float("inf"), 0.0
    gp = gs = 0.0
    for n in range(p + 1, 2 * p + 1, step):
        m = m_floor(n)
        for h1 in range(1, hmax + 1):
            for h2 in range(1, hmax + 1):
                b = (m_floor(n + 2 * h1) - m) * (m_floor(n + 2 * h2) - m)
                hh = h1 * h2
                prod = max(prod, b / (hh * p))
                v = 0.75 * b / m**0.5 / (hh * p**0.25)
                term_lo = min(term_lo, v)
                term_hi = max(term_hi, v)
                gp = max(gp, (9 / 16) * b * n**-1.75 / (hh * p**-0.75))
                gs = max(gs, (63 / 64) * b * n**-2.75 / (hh * p**-1.75))
    return {
        "P": p, "h_max": hmax,
        "product": {"attained": prod, "closed_form": 18.0, "lean_hypothesis": 4.25**2,
                    "printed": 19.0},
        "second_difference_term": {"attained": [term_lo, term_hi],
                                   "closed_form": [27 / 4, (27 / 4) * 2**0.25],
                                   "printed": [1.4, 15.0]},
        "Gprime_beta": {"attained": gp, "closed_form": 81 / 16, "printed": 20.0},
        "Gsecond_beta": {"attained": gs, "closed_form": 567 / 64, "printed": 25.0},
    }



def offset_term_attained(p: int, hmax: int = 7, stride: int | None = None) -> dict[str, Any]:
    """The offset term of Lemma 5.1(iii) against its printed range ``[1.5, 2.6]``.

    ``(3/2)|j|(m + beta_1 + beta_2 + xi_1)^(1/2)`` as a multiple of ``|j| P^(3/4)``.  The
    manuscript reported this from a 300-point sample as ``[1.510, 2.514]``; it has closed
    forms.  Over ``n`` in ``(P, 2P]`` the bracket runs from ``m ~ P^(3/2)`` to
    ``m ~ (2P)^(3/2)``, so the ratio runs over ``[3/2, (3/2) 2^(3/4)]``, the lower end
    attained and the upper ``2.5227`` against a printed ``2.6``: three percent of headroom,
    and the *lower* bound is the one that is sharp.

    ``xi_1`` lies between ``0`` and ``j``, which is ``O(1)`` beside ``m ~ P^(3/2)`` and moves
    the ratio by ``O(P^(-3/2))``; it is dropped, as the manuscript's own display does.
    """
    step = stride or max(1, p // 400) | 1
    lo, hi = float("inf"), 0.0
    for n in range(p + 1, 2 * p + 1, step):
        m = m_floor(n)
        for h1 in range(1, hmax + 1):
            for h2 in range(1, hmax + 1):
                b1 = m_floor(n + 2 * h1) - m
                b2 = m_floor(n + 2 * h2) - m
                v = 1.5 * (m + b1 + b2) ** 0.5 / p**0.75
                lo = min(lo, v)
                hi = max(hi, v)
    return {"P": p, "h_max": hmax, "attained": [lo, hi],
            "closed_form": [1.5, 1.5 * 2**0.75], "printed": [1.5, 2.6],
            "headroom_at_top": 2.6 / hi}



# --- the level-1 kernel's cancellation exponent, swept ---
#
# Section 5 reports "over P in [10^4, 10^6] and k in {1,2,4}, twelve exponents with mean 0.49".
# The measurement is `paper_b_audit.level1_kernel_block_scaling`, which takes one (P, k); no
# sweep existed, and the four P values were nowhere stated, so the claim could not be re-run
# from the text.  This is the ladder, stated.  Calling across modules rather than adding to
# `paper_b_audit`, which the other session owns.

LEVEL1_SWEEP_PS = (10**4, 3 * 10**4, 10**5, 10**6)
LEVEL1_SWEEP_KS = (1, 2, 4)


def level1_exponent_sweep(ps: tuple[int, ...] = LEVEL1_SWEEP_PS,
                          ks: tuple[int, ...] = LEVEL1_SWEEP_KS) -> dict[str, Any]:
    """Block-scaling exponent of ``K_1`` over the stated ladder, with the flatness ranges.

    Twelve points at the default ladder, mean ``0.4870``.  Square-root cancellation is ``1/2``
    and no cancellation is ``1``; the instrument's own 90% interval on data that is exactly
    ``1/2`` is ``[0.4268, 0.5684]`` (``paper_b_audit.block_exponent_calibration``), and exactly
    one of the twelve falls outside it -- ``P = 10^4``, ``k = 1``, at ``0.3866``.

    ``ratio_range_by_P`` is ``rms/sqrt(L)`` over the five fitted block lengths.  It is what the
    manuscript's ``[0.94, 1.12]`` reports, and that interval is the ``P = 10^6`` range: taking
    ``P >= 10^5`` as the sentence says widens it to ``[0.874, 1.150]``.
    """
    from research.juggler_sequence import paper_b_audit as _pba

    exponents: dict[tuple[int, int], float] = {}
    ratios: dict[int, list[float]] = {}
    for p in ps:
        for k in ks:
            r = _pba.level1_kernel_block_scaling(P=p, k=k)
            exponents[(p, k)] = r["level1_exponent"]
            ratios.setdefault(p, []).extend(
                b["rms_K1_over_sqrtL"] for b in r["blocks"][:5])
    xs = list(exponents.values())
    mean = sum(xs) / len(xs)
    return {
        "ps": list(ps), "ks": list(ks), "n": len(xs),
        "exponents": {"%d,%d" % pk: v for pk, v in exponents.items()},
        "mean": mean, "min": min(xs), "max": max(xs),
        "ratio_range_by_P": {p: [min(v), max(v)] for p, v in ratios.items()},
        "square_root_exponent": 0.5, "no_cancellation_exponent": 1.0,
    }


def level1_sweep_outside_calibration(sweep: dict[str, Any] | None = None,
                                     interval: tuple[float, float] = (0.4268, 0.5684),
                                     ) -> list[str]:
    """Which swept points fall outside the instrument's own 90% interval."""
    s = sweep or level1_exponent_sweep()
    lo, hi = interval
    return [pk for pk, v in s["exponents"].items() if not (lo <= v <= hi)]



# --- and whether the kernel/control separation is a feature of one P ---

LEVEL1_TREND_PS = (10**4, 3 * 10**4, 10**5, 3 * 10**5, 10**6, 3 * 10**6)


def level1_control_crossover(p: int, bins: int = 256, fit_min_count: int = 16) -> dict[str, Any]:
    """Where van der Corput's second-derivative test turns linear for the control.

    The control is ``e({n^(3/2)}) = e(n^(3/2))``, the Weyl sum itself.  Over odd ``n`` with
    step 2 the curvature in the term index is ``lambda = 3 n^(-1/2) ~ 3 P^(-1/2)``, so a block
    sum of length ``L`` is ``<< L lambda^(1/2) + lambda^(-1/2)``.  The first term is *linear*
    in ``L`` and dominates once ``L >> 1/lambda = sqrt(P)/3``, so the fitted exponent goes to
    ``1``, not to ``1/2``.

    The five fitted block lengths run over ``[N/bins, N/fit_min_count]`` with ``N = P/2``, i.e.
    ``[P/512, P/32]`` at the defaults, so the whole window clears the crossover once
    ``sqrt(P) >= 2 bins / 3``, i.e. ``P > (2 bins/3)^2 = 2.91e4``.  That is where the
    separation opens.
    """
    lam = 3.0 * p**-0.5
    n_terms = p / 2
    return {"P": p, "lambda": lam, "crossover_L": 1.0 / lam,
            "L_min": n_terms / bins, "L_max": n_terms / fit_min_count,
            "L_min_over_crossover": (n_terms / bins) * lam,
            "window_clears": (n_terms / bins) * lam >= 1.0,
            "P_where_window_clears": (2.0 * bins / 3.0) ** 2}


def level1_control_trend(ps: tuple[int, ...] = LEVEL1_TREND_PS, k: int = 1) -> dict[str, Any]:
    """Kernel and control exponents against ``P``, and the gap between them.

    The passage in Section 5 measured both at one ``P`` and read the contrast off it.  Across
    the ladder the kernel stays at ``1/2`` -- mean ``0.4928`` over the six, no trend -- while
    the control climbs monotonically ``0.4902 -> 0.9852``, and the gap widens monotonically
    from ``P = 3e4`` on.  At ``P = 10^4`` there is no separation at all: the control reads
    ``0.4902`` against the kernel's ``0.3866``, and that is the one ``P`` whose fitted window
    does not clear the crossover.

    So the separation is not a small-``P`` artefact; it is the opposite, and it appears exactly
    where ``level1_control_crossover`` says it should.
    """
    from research.juggler_sequence import paper_b_audit as _pba

    rows = []
    for p in ps:
        r = _pba.level1_kernel_block_scaling(P=p, k=k)
        cross = level1_control_crossover(p)
        rows.append({"P": p, "kernel": r["level1_exponent"], "control": r["wave_exponent"],
                     "gap": r["wave_exponent"] - r["level1_exponent"],
                     "L_min_over_crossover": cross["L_min_over_crossover"],
                     "window_clears": cross["window_clears"]})
    ks = [x["kernel"] for x in rows]
    ws = [x["control"] for x in rows]
    cleared = [x for x in rows if x["window_clears"]]
    return {
        "ps": list(ps), "k": k, "rows": rows,
        "kernel_mean": sum(ks) / len(ks),
        "kernel_spread": max(ks) - min(ks),
        "control_increases": all(ws[i] < ws[i + 1] for i in range(len(ws) - 1)),
        "control_range": [min(ws), max(ws)],
        "gap_increases_once_cleared": all(
            cleared[i]["gap"] < cleared[i + 1]["gap"] for i in range(len(cleared) - 1)),
    }



def level1_kernel_condition(p: int, k: int = 1) -> dict[str, Any]:
    """The kernel's own decorrelation condition, and why it has no crossover in ``P``.

    The control's exponent turns at a definite ``P`` because van der Corput's second-derivative
    test turns linear at ``L = 1/lambda``.  The kernel's condition is not of that kind.  Its
    coefficient is ``c(n) = (27k/32) n^(33/32)``, so ``c'(n) = (891k/1024) n^(1/32)`` and, over
    odd ``n`` with step 2, the coefficient advances by ``2c' = (891k/512) n^(1/32)`` per
    summand.  "More than a whole period per step" is ``2c' > 1``, which holds from
    ``n = (512/(891k))^32 ~ 2e-8`` upward -- below every ``P`` anyone would run.

    So there is no threshold to cross, and none should be looked for: ``2c'`` runs from
    ``2.32`` at ``10^4`` to ``2.77`` at ``3e6`` and reaches ``10`` only near ``2e24``.  The
    exponent is ``1/2`` throughout because the condition is met throughout.
    """
    two_c_prime = (891.0 * k / 512.0) * p ** (1 / 32)
    return {"P": p, "k": k, "two_c_prime": two_c_prime, "condition_met": two_c_prime > 1.0,
            "P_where_condition_starts": (512.0 / (891.0 * k)) ** 32,
            "P_where_two_c_prime_reaches_ten": (10.0 * 512.0 / (891.0 * k)) ** 32}


def level1_kernel_k_spread(p: int, ks: tuple[int, ...] = (1, 2, 3, 4, 5, 6, 7, 8),
                           interval: tuple[float, float] = (0.4268, 0.5684)) -> dict[str, Any]:
    """The kernel exponent across ``k`` at one ``P``: is a low reading systematic or a draw?

    The single reading ``0.3866`` at ``P = 10^4``, ``k = 1`` sits outside the instrument's own
    90% interval, and it is tempting to read a regime boundary into it.  There is none
    (``level1_kernel_condition``).  Across eight ``k`` at that ``P`` the mean is ``0.4771`` and
    the two excursions are one low *and one high* -- ``k = 8`` reads ``0.584`` -- which is what
    a 90% interval predicts for eight draws.  What does change with ``P`` is the spread:
    ``0.062``, ``0.035``, ``0.024`` at ``10^4``, ``3e4``, ``10^5``.  That is the estimator, not
    the object: the calibration was run at ``N = 5000`` terms, which is exactly ``P = 10^4``'s.
    """
    from research.juggler_sequence import paper_b_audit as _pba

    lo, hi = interval
    xs = [_pba.level1_kernel_block_scaling(P=p, k=k)["level1_exponent"] for k in ks]
    mean = sum(xs) / len(xs)
    outside = [k for k, v in zip(ks, xs) if not (lo <= v <= hi)]
    return {
        "P": p, "ks": list(ks), "exponents": xs, "mean": mean,
        "spread": (sum((x - mean) ** 2 for x in xs) / len(xs)) ** 0.5,
        "outside_interval": outside,
        "outside_low": [k for k, v in zip(ks, xs) if v < lo],
        "outside_high": [k for k, v in zip(ks, xs) if v > hi],
        "terms": p // 2,
    }



def level1_drift_window_occupancy(p: int, k: int = 1, span: float = 20000.0) -> dict[str, Any]:
    """How many drift-1 windows actually hold a summand, against "none at all".

    The window on which ``c`` moves by less than 1 has length ``1/c'``, and the manuscript
    read that as "shorter than the spacing of the summation variable, so it contains no
    integer at all".  Shorter than the spacing gives *at most one*, not none: over odd ``n``
    the spacing is 2, so a window of length ``1/c' < 2`` holds one odd integer with density
    ``(1/c')/2 = 1/(2c')`` and none otherwise.  That density is ``0.43`` at ``P = 10^4`` and
    ``0.22`` at ``P_0``; it is never zero, and it falls only like ``n^(-1/32)``.

    The conclusion the sentence supports is untouched.  What Lemma 3.7 needs is a window with
    *several* summands to expand over; at most one is already fatal, and "finer than the
    lattice" is the right description of that.  Only "no integer at all" is too strong.

    Tiles the block with consecutive windows and counts, so the density is measured and not
    assumed.
    """
    c_prime = (891.0 * k / 1024.0) * p ** (1.0 / 32.0)
    length = 1.0 / c_prime
    n_win = int(span / length)
    hits = 0
    x = float(p)
    for _ in range(n_win):
        lo, hi = x, x + length
        m = 2 * int((lo - 1) // 2) + 1
        while m < lo:
            m += 2
        hits += 1 if m < hi else 0
        x = hi
    return {"P": p, "k": k, "c_prime": c_prime, "two_c_prime": 2.0 * c_prime,
            "window_length": length, "lattice_spacing": 2,
            "predicted_occupancy": length / 2.0, "counted_occupancy": hits / n_win,
            "windows": n_win, "holds_at_most_one": length < 2.0,
            "ever_holds_none_for_certain": False}



def lemma37_one_term_window_cost(p: int, k: int = 1, j_exponent: float = 5 / 16,
                                 t_slack: float = 1.0) -> dict[str, Any]:
    """What Lemma 3.7 returns on a window holding a single term, against the trivial bound.

    "At most one summand per window is already fatal" is usually left there.  It can be priced,
    and the price says why no amount of care recovers the level-1 kernel.

    Lemma 3.7 expands ``e(-B{t})`` into ``|u| <= T`` and ``0 < |q| <= J`` modes with
    ``sum |b_u| <= 8 + 2 log(2 + |B| + T)`` and ``|v_q| <= min(2, 2 pi |B|)/|q|``, under
    ``T >= 8(1 + |B|)``, with a pointwise error ``min(2, 2 pi |B|) Delta_J(t) + 8(1+|B|)/T``.
    On a window of ``W`` terms the trivial bound is ``W``.  The expansion beats it only if the
    individual mode sums beat it, and at ``W = 1`` every mode sum is a single unimodular term,
    of modulus exactly ``1``.  So the expansion returns the *whole coefficient mass* against a
    trivial bound of ``1``.

    Two edges, not one.  At the hypothesis boundary ``T = 8(1 + |B|)`` the flat error term
    ``8(1+|B|)/T`` is exactly ``1`` on its own -- the trivial bound, before a single mode is
    counted.  Taking ``T`` larger makes that term small and the ``b``-mass larger, since the
    mass carries ``log T``.

    And the two failures have one cause.  The window is short because ``c`` is large
    (``1/c' ~ P^(-1/32)/k``), and the mass is large because ``c`` is large
    (``2 log|B| ~ (33/16) log P``).  Pushing ``T`` up to satisfy the hypothesis only makes the
    second worse.  That is the content of "no amount of care with Lemma 3.7 recovers it".
    """
    B = (27.0 * k / 32.0) * p ** (33.0 / 32.0)
    T = t_slack * 8.0 * (1.0 + B)
    J = p ** j_exponent
    b_mass = 8.0 + 2.0 * math.log(2.0 + B + T)
    # sum_{0 < |q| <= J} |v_q| <= 2 * sum_{q=1}^{J} 2/q = 4 H_J
    v_mass = 4.0 * (math.log(J) + 0.5772156649)
    flat_per_point = 8.0 * (1.0 + B) / T
    return {"P": p, "k": k, "B": B, "T": T, "J": J,
            "b_mass": b_mass, "v_mass": v_mass, "total_mass": b_mass + v_mass,
            "flat_per_point": flat_per_point,
            "trivial_bound_on_one_term": 1.0,
            "expansion_worse_by": b_mass + v_mass,
            "flat_alone_reaches_trivial": flat_per_point >= 1.0}



# Every place Lemma 3.7 is invoked, with the parameters it is invoked at:
# (site, |B| exponent, |B| constant, T exponent, T constant, J exponent or None).
LEMMA37_SITES = (
    ("Thm 4.1 St.3(s1)", -1 / 16, 2.25, 1 / 2, 1.0, 5 / 16),
    ("Thm 4.1 St.3(s2)", 1 / 4, 2.25, 1 / 2, 1.0, None),
    ("Thm 4.1 St.6(D1)", 0.0, 1.0, 1 / 2, 1.0, None),
    ("Thm 4.1 St.6(D2)", 1 / 8, 1.85, 1 / 2, 1.0, 5 / 16),
    ("Thm 5.3 St.3(a)", 1 / 8, 15 / 8, 23 / 48, 0.5, 1 / 4),
    ("Thm 5.3 St.3(b)", 1 / 8, 1.85, 11 / 24, 0.5, None),
    ("Thm 5.3 St.5b j=0", 0.0, 6.0, 1 / 2, 1.0, None),
    ("Thm 6.1 Step E", 0.0, 6.0, 1 / 2, 1.0, None),
    ("Thm 6.3 depth five", 19 / 96, 2.0, 5 / 16, 1.0, None),
    ("Lemma 5.2(iii)", 1 / 4, 5.0, 1 / 2, 1.0, None),
)


def lemma37_site_masses(p: float | None = None) -> dict[str, Any]:
    """Is Lemma 3.7's coefficient mass really ``O(log P)`` at every site it is used?

    The lemma carries ``sum|b_u| + sum|v_q| <= 8 + 2 log(2 + |B| + T) + 4 H_J``, which the
    paper absorbs into ``P^epsilon`` everywhere and prints nowhere.  Since ``|B|``, ``T`` and
    ``J`` are powers of ``P`` at every site, it is ``O(log P)`` at every site, with coefficient
    ``2 max(beta, tau) + 4 iota``.  The largest is ``9/4``, at the two sites carrying Stage 2's
    truncation ``J = R_0 = P^(5/16)``, where the ``v``-mass ``5/4`` outweighs the ``b``-mass.

    Theorem 6.3 carries the paper's largest log power, ``log^(15/4) P``, and has the *thinnest*
    site of the ten at ``5/8``, because its window parameter is ``R_0`` rather than ``P^(1/2)``.
    That log power is the count of applications at depth five, not the mass of any one of them.
    """
    if p is None:
        from research.juggler_sequence import p0_certificate as _pc
        p = _pc.certificate()["P0"]
    rows = []
    for name, be, bc, te, tc, je in LEMMA37_SITES:
        B, T = bc * p**be, tc * p**te
        b_mass = 8.0 + 2.0 * math.log(2.0 + B + T)
        v_mass = 0.0 if je is None else 4.0 * (math.log(p**je) + 0.5772156649)
        rows.append({"site": name, "B_exponent": be, "T_exponent": te, "J_exponent": je,
                     "coefficient": 2.0 * max(be, te) + (0.0 if je is None else 4.0 * je),
                     "mass": b_mass + v_mass})
    coeffs = [r["coefficient"] for r in rows]
    return {"P": p, "rows": rows, "max_coefficient": max(coeffs),
            "min_coefficient": min(coeffs),
            "all_logarithmic": all(c < 10.0 for c in coeffs),
            "thinnest_site": min(rows, key=lambda r: r["coefficient"])["site"],
            "fattest_sites": [r["site"] for r in rows if r["coefficient"] == max(coeffs)]}



# The log powers Sections 4-6 carry, and where each comes from.
LOG_POWER_CHAIN = (
    ("T_2 mode masses", 3.0, "at most three expansion layers plus the shift devices"),
    ("Weyl step 1 (T_1)", 1.5, "the A-process squares, so the square root halves the power"),
    ("Weyl step 2 (K_c)", 0.75, "and again"),
    ("Theorem 6.3", 3.75, "three further truncations, two of them its own"),
)

# The three truncations behind Theorem 6.3's further log^3.
THEOREM63_TRUNCATIONS = (
    ("Vaaler, fifth wave", "J_5 = 2 P^(1/96)", True),
    ("Lemma 3.7 window", "T = R_0 = P^(5/16) against |C| <= 1.30 P^(19/96)", True),
    ("first-letter index", "|i| <= 2 P^(1/96), inherited from Theorem 6.1", False),
)


def log_power_ledger(delta: float = 1 / 96) -> dict[str, Any]:
    """Where each log power comes from, and when it would be absorbed into ``P^delta``.

    ``|T_2| << P^(23/24) log^3 P`` from at most three expansion layers; the two Weyl steps of
    Theorem 5.3 each halve the exponent, giving ``log^(3/2)`` and then ``K_c``'s ``log^(3/4)``;
    Theorem 6.3 adds three more, for ``3/4 + 3 = 15/4``.

    Only two of those three are Theorem 6.3's own -- the Vaaler expansion at ``J_5`` and the
    Lemma 3.7 window at ``R_0``.  The third is the first-letter index it inherits from Theorem
    6.1 when it merges the two into ``|I_tot| <= 2 P^(5/16)``, and that one is not inside the
    ``log^(3/4)``, since that power is ``K_c``'s and Theorem 6.1 is where ``K_c`` is applied
    rather than proved.  So the count of three is right and only "its own" is loose.

    Absorption is nowhere near either way: a larger ``A`` is the weaker claim, so the generous
    count is the safe one.
    """
    ln10 = math.log(10.0)

    def least_log10(a: float) -> float:
        lo, hi = 2.0, 5000.0
        for _ in range(300):
            mid = (lo + hi) / 2
            if a * math.log(mid * ln10) - delta * mid * ln10 <= 0:
                hi = mid
            else:
                lo = mid
        return hi

    return {
        "chain": [{"stage": n, "log_power": a, "why": w} for n, a, w in LOG_POWER_CHAIN],
        "theorem63_truncations": [{"name": n, "parameter": p, "own": o}
                                  for n, p, o in THEOREM63_TRUNCATIONS],
        "own_count": sum(1 for _, _, o in THEOREM63_TRUNCATIONS if o),
        "inherited_count": sum(1 for _, _, o in THEOREM63_TRUNCATIONS if not o),
        "absorption_log10": {a: least_log10(a) for a in (0.75, 1.0, 2.75, 3.75)},
        "final_power": 3.75,
        "halving_is_exact": 3.0 / 2 / 2 == 0.75,
        "sum_is_exact": 0.75 + 3 == 3.75,
    }


def main() -> None:
    payload = run_census(
        orbit_window=100_000,
        orbit_samples=100_000,
        orbit_boundary=2_000,
    )
    write_json(payload)
    verdict = payload["verdict"]
    print("decision", verdict["decision"])
    print("why", verdict["why"])
    print("kinds", verdict["kinds"])
    for orb in payload["orbits"]:
        print(
            f"orbit P={orb['P']} max|j|={orb['max_abs_j']} "
            f"live_j={orb['live_j']} n={orb['n_seen']}"
        )
    for inv in payload["inventories"]:
        p0s = [r["source"] for r in inv["rows"] if r["overflow_kind"] == "p0"]
        print(f"inventory P={inv['P']} p0={p0s}")


if __name__ == "__main__":
    main()
