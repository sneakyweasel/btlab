"""The OE-fiber share is a quadratic phase sweep, and on cubes it is exact.

The ``OE`` fiber of ``m`` is the set of odd ``n`` with ``m^4 <= n^3 < (m+1)^4``; the
members whose odd-step image ``floor(n^{3/2})`` is even reach ``m`` in two steps.  Paper C
writes ``H_m`` for the fiber size and ``G_m`` for the even-image count, and its whole
production argument rests on lower bounds for ``G_m``.  Some fibers are empty: ``99969``
has ``G = 0``, and ``10^6`` has ``G = H``.  This module says why, exactly.

**The law.**  Along the fiber the phase ``x = n^{3/2}/2`` advances by
``(3/2) sqrt(n)`` per odd step, and that increment itself grows: the phase is quadratic
in the position, ``{theta + alpha j + gamma j^2}``, with ``alpha = {(3/2) m^{2/3}}`` the
reduced step, ``theta = {x_1}`` the landing phase, and total curvature ``gamma H^2 -> 1/3``.
Write ``beta = alpha H`` for the linear drift in fiber units (signed, ``alpha`` taken in
``(-1/2, 1/2]``).  Then

    G_m / H_m = S(beta_m, theta_m) + O(1/H_m),
    S(beta, theta) = |{ s in [0,1] : {theta + beta s + s^2/3} < 1/2 }|.

Three consequences of the formula alone:

* ``int_0^1 S(beta, theta) d theta = 1/2`` for every ``beta`` (Fubini and translation
  invariance).  Aggregate counts never see the extremes.
* ``S in {0, 1}`` is possible iff ``beta in [-5/6, 1/6]``: the phase range over the fiber
  is ``beta + 1/3`` for ``beta >= 0`` and ``max(0, beta+1/3) + 3 beta^2/4`` for
  ``-2/3 <= beta < 0``, and an extreme needs range ``<= 1/2``.
* The ``beta``-integral of the ``theta``-measure of ``{S = 0}`` is exactly ``25/108``, so
  under equidistribution of ``(beta_m, theta_m)`` the density of empty fibers is
  ``(25/108) / H_m``, the same for full ones.  Measured: ``1.0%`` against ``0.74%``
  predicted at ``m ~ 10^5``, ``0.45%`` against ``0.35%`` at ``10^6``.

**The exact case.**  For ``m = k^3`` the reduced step is ``{3k^2/2}``, exactly ``0`` for
even ``k`` and ``1/2`` for odd ``k``, and the law becomes an integer identity: on the
fiber ``n = k^4 + t``,

    isqrt((k^4 + t)^3) = k^6 + 3 k^2 t / 2     whenever 3 t <= 4 k,

which holds on the whole fiber.  Even ``k``: every image even, the fiber is **full**.
Odd ``k``: the image has the parity of ``1 + t/2``, the fiber **alternates** exactly.
This is Lean-verified (``CubeFiber.lean``: ``cube_fiber_range``, ``even_cube_fiber_full``,
``odd_cube_fiber_alternating``), by ``nlinarith`` on the two square-root inequalities.

**Impact on Paper C.**  Lemma 4.2 discards ``||alpha_m|| < 22 m^{-1/3}``; the extremes
live in the signed window ``alpha_m in [-1.25, 0.25] m^{-1/3}``, about 29 times
narrower.  And the parked lift of the remainder-set production from ``1/3`` to ``1/2`` is
exactly the statement that the landing phase ``theta_m`` equidistributes along the
remainder set conditionally on ``beta_m``: a depth-two fairness statement on a
backward-closed set, which no fiber-local lemma can supply and which the empty fibers do
not obstruct.
"""

from __future__ import annotations

import json
from decimal import Decimal, getcontext
from fractions import Fraction as F
from math import isqrt
from typing import Any

from research.juggler_sequence.lean_paths import DATA_ROOT

getcontext().prec = 80

ARTIFACT = DATA_ROOT / "oe_fiber_share" / "summary.json"
#: Paper C, Lemma 4.2: m is bad when ||alpha_m|| < PAPER_C_WINDOW * m^{-1/3}
PAPER_C_WINDOW = 22
#: the extreme window in drift units: S can be 0 or 1 iff beta in [BETA_LO, BETA_HI]
BETA_LO, BETA_HI = F(-5, 6), F(1, 6)
#: H_m ~ (2/3) m^{1/3}, so one drift unit is (3/2) m^{-1/3} in alpha
ALPHA_PER_BETA = F(3, 2)


# ------------------------------------------------------------------ the fiber

def icbrt(x: int) -> int:
    """Exact floor cube root."""
    r = max(int(round(x ** (1 / 3))) - 2, 1) if x < 10 ** 290 else int(10 ** (len(str(x)) / 3))
    while (r + 1) ** 3 <= x:
        r += 1
    while r ** 3 > x:
        r -= 1
    return r


def oe_fiber(m: int) -> list[int]:
    """Odd ``n`` with ``m^4 <= n^3 < (m+1)^4``, i.e. ``floor(n^{3/4}) = m``."""
    lo = icbrt(m ** 4)
    while lo ** 3 < m ** 4:
        lo += 1
    hi = icbrt((m + 1) ** 4 - 1)
    return list(range(lo | 1, hi + 1, 2))


def image_parities(m: int) -> list[int]:
    return [isqrt(n ** 3) & 1 for n in oe_fiber(m)]


def share(m: int) -> tuple[int, int]:
    """``(H_m, G_m)``: fiber size and even-image count."""
    p = image_parities(m)
    return len(p), len(p) - sum(p)


# ------------------------------------------------------------------ the phases

def phases(m: int) -> dict[str, float | int]:
    """``alpha`` signed in ``(-1/2, 1/2]``, ``beta = alpha H``, ``theta = {n_1^{3/2}/2}``."""
    ns = oe_fiber(m)
    H = len(ns)
    a = Decimal(m) ** (Decimal(2) / Decimal(3)) * Decimal(3) / Decimal(2)
    al = a - int(a)
    if al > Decimal("0.5"):
        al -= 1
    x1 = (Decimal(ns[0]) ** Decimal("1.5")) / 2
    return {"H": H, "alpha": float(al), "beta": float(al) * H, "theta": float(x1 - int(x1))}


def model_share(beta: float, theta: float, N: int = 2000) -> float:
    """``S(beta, theta)``: the measure of ``s`` with ``{theta + beta s + s^2/3} < 1/2``."""
    return sum(((theta + beta * (s / N) + (s / N) ** 2 / 3) % 1.0) < 0.5 for s in range(N)) / N


def phase_average(beta: float, N: int = 400) -> float:
    """``int_0^1 S(beta, theta) d theta``, which is ``1/2`` exactly."""
    return sum(model_share(beta, k / N, 600) for k in range(N)) / N


def empty_theta_measure(beta: F) -> F:
    """Exact ``theta``-measure of ``{S(beta, .) = 0}``: ``1/2`` minus the phase range."""
    if beta >= 0:
        rng = beta + F(1, 3)
    elif beta >= F(-2, 3):
        rng = max(F(0), beta + F(1, 3)) + F(3, 4) * beta * beta
    else:
        rng = -beta - F(1, 3)
    return max(F(0), F(1, 2) - rng)


def _integrate(coeffs: list[F], lo: F, hi: F) -> F:
    """Exact integral of ``sum c_i x^i`` over ``[lo, hi]``."""
    anti = lambda x: sum(c * x ** (i + 1) / (i + 1) for i, c in enumerate(coeffs))
    return anti(hi) - anti(lo)


def empty_beta_integral() -> F:
    """``int empty_theta_measure(beta) d beta`` over the extreme window, exactly."""
    pieces = (
        ([F(1, 6), F(-1)], F(0), F(1, 6)),                     # 1/6 - beta
        ([F(1, 6), F(-1), F(-3, 4)], F(-1, 3), F(0)),          # 1/6 - beta - 3 beta^2 / 4
        ([F(1, 2), F(0), F(-3, 4)], F(-2, 3), F(-1, 3)),       # 1/2 - 3 beta^2 / 4
        ([F(5, 6), F(1)], F(-5, 6), F(-2, 3)),                 # 5/6 + beta
    )
    return sum(_integrate(c, lo, hi) for c, lo, hi in pieces)


def sharp_alpha_window(m: int) -> tuple[float, float]:
    """The signed ``alpha_m`` window in which a fiber can be extreme, in units of m^{-1/3}."""
    return float(BETA_LO * ALPHA_PER_BETA), float(BETA_HI * ALPHA_PER_BETA)


# ------------------------------------------------------------------ the cubes

def cube_identity(k: int, t: int) -> bool:
    """``isqrt((k^4+t)^3) == k^6 + 3k^2 t / 2`` for the fiber's parity of ``t``."""
    if (k ** 4 + t) % 2 == 0:
        raise ValueError("fiber elements are odd")
    return 2 * isqrt((k ** 4 + t) ** 3) == 2 * k ** 6 + 3 * k * k * t


def cube_fiber(k: int) -> dict[str, Any]:
    """The fiber of ``k^3``: full for even ``k``, exactly alternating for odd ``k``."""
    ns = oe_fiber(k ** 3)
    par = [isqrt(n ** 3) & 1 for n in ns]
    H, G = len(par), len(par) - sum(par)
    t_max = ns[-1] - k ** 4
    return {
        "k": k, "m": k ** 3, "H": H, "G": G,
        "full": G == H,
        "alternating": all(par[i] != par[i + 1] for i in range(H - 1)),
        "range_slack": 4 * k - 3 * t_max,          # >= 0 iff the identity covers the fiber
        "identity_holds": all(cube_identity(k, n - k ** 4) for n in ns),
        "as_predicted": (G == H) if k % 2 == 0 else abs(2 * G - H) <= 1,
    }


# ------------------------------------------------------------------ the census

def density_scan(lo: int, count: int) -> dict[str, Any]:
    E = Fu = 0
    Hs = 0
    Gs = 0
    for m in range(lo, lo + count):
        H, G = share(m)
        Hs += H
        Gs += G
        E += G == 0
        Fu += G == H
    Hbar = Hs / count
    return {
        "lo": lo, "count": count, "mean_H": Hbar, "mean_share": Gs / Hs,
        "empty_pct": 100 * E / count, "full_pct": 100 * Fu / count,
        "predicted_pct": 100 * float(empty_beta_integral()) / Hbar,
    }


def window_fit(lo: int, count: int, bmax: float = 1.2) -> dict[str, Any]:
    """Actual share against ``S(beta, theta)`` on the fibers inside the drift window."""
    errs = []
    extreme_betas = []
    for m in range(lo, lo + count):
        ph = phases(m)
        if abs(ph["beta"]) <= bmax:
            H, G = share(m)
            errs.append(abs(G / H - model_share(ph["beta"], ph["theta"], 1500)))
        if abs(ph["beta"]) <= 3:
            H, G = share(m)
            if G in (0, H):
                extreme_betas.append(ph["beta"])
    return {
        "n_window": len(errs),
        "mean_abs_error": sum(errs) / len(errs) if errs else None,
        "max_abs_error": max(errs) if errs else None,
        "one_over_H": 1 / phases(lo)["H"],
        "n_extreme": len(extreme_betas),
        "extreme_beta_min": min(extreme_betas) if extreme_betas else None,
        "extreme_beta_max": max(extreme_betas) if extreme_betas else None,
    }


def summary() -> dict[str, Any]:
    cubes = [cube_fiber(k) for k in range(2, 121)]
    scans = [density_scan(10 ** 4 + 123, 2000), density_scan(10 ** 5 + 123, 2000),
             density_scan(10 ** 6 + 7777, 1200)]
    fit = window_fit(10 ** 6 + 7777, 12000)
    lo_a, hi_a = sharp_alpha_window(10 ** 6)
    return {
        "statement": (
            "G_m/H_m = S(beta_m, theta_m) + O(1/H_m) with S the measure of s in [0,1] such "
            "that {theta + beta s + s^2/3} < 1/2; the theta-average of S is 1/2 for every "
            "beta; an extreme is possible iff beta in [-5/6, 1/6]; the beta-integral of the "
            "empty region is 25/108. For m = k^3 the fiber is full (k even) or exactly "
            "alternating (k odd), by the integer identity isqrt((k^4+t)^3) = k^6 + 3k^2t/2."
        ),
        "cubes": {
            "checked_k": [2, 120],
            "all_as_predicted": all(c["as_predicted"] for c in cubes),
            "identity_holds_on_every_fiber": all(c["identity_holds"] for c in cubes),
            "min_range_slack": min(c["range_slack"] for c in cubes),
            "examples": [c for c in cubes if c["k"] in (2, 3, 4, 5, 10, 11, 100)],
        },
        "empty_beta_integral": str(empty_beta_integral()),
        "extreme_window_beta": [str(BETA_LO), str(BETA_HI)],
        "extreme_window_alpha_units_of_m_to_minus_third": [lo_a, hi_a],
        "paper_c_window_units_of_m_to_minus_third": [-PAPER_C_WINDOW, PAPER_C_WINDOW],
        "paper_c_window_over_sharp": 2 * PAPER_C_WINDOW / (hi_a - lo_a),
        "phase_average": {str(b): phase_average(b) for b in (-0.8, -0.4, 0.0, 0.1, 0.5, 2.0)},
        "density": scans,
        "window_fit": fit,
        "lean": [
            "cube_fiber_range", "cube_fiber_sqrt_even", "cube_fiber_even_image",
            "even_cube_fiber_full", "cube_fiber_sqrt_odd", "cube_fiber_alternating",
            "odd_cube_fiber_alternating",
        ],
        "paper_c": {
            "lemma_4_2_window_can_shrink_by": 2 * PAPER_C_WINDOW / (hi_a - lo_a),
            "rest_lift_is": (
                "equidistribution of the landing phase theta_m along the remainder set, "
                "conditionally on beta_m: a depth-two fairness statement on a backward-closed set"
            ),
        },
    }


def main() -> None:
    s = summary()
    ARTIFACT.parent.mkdir(parents=True, exist_ok=True)
    ARTIFACT.write_text(json.dumps(s, indent=2) + "\n", encoding="utf-8")
    c = s["cubes"]
    print(f"cubes k in {c['checked_k']}: all as predicted {c['all_as_predicted']}, "
          f"identity on every fiber {c['identity_holds_on_every_fiber']}, "
          f"min range slack {c['min_range_slack']}")
    print(f"empty-region beta-integral = {s['empty_beta_integral']}; extreme window beta in "
          f"{s['extreme_window_beta']}, alpha in {s['extreme_window_alpha_units_of_m_to_minus_third']} "
          f"m^-1/3 (Paper C: +-{PAPER_C_WINDOW}, ratio {s['paper_c_window_over_sharp']:.1f})")
    print("phase averages:", {k: round(v, 4) for k, v in s["phase_average"].items()})
    print(f"{'m':>10} {'H':>6} {'mean share':>10} {'pred %':>7} {'empty %':>8} {'full %':>7}")
    for d in s["density"]:
        print(f"{d['lo']:>10} {d['mean_H']:>6.1f} {d['mean_share']:>10.4f} "
              f"{d['predicted_pct']:>7.2f} {d['empty_pct']:>8.2f} {d['full_pct']:>7.2f}")
    f = s["window_fit"]
    print(f"window fit at 1e6: {f['n_window']} fibers, mean |err| {f['mean_abs_error']:.4f}, "
          f"max {f['max_abs_error']:.3f}, 1/H {f['one_over_H']:.3f}; "
          f"{f['n_extreme']} extremes with beta in [{f['extreme_beta_min']:.3f}, {f['extreme_beta_max']:.3f}]")
    print(f"wrote {ARTIFACT}")


if __name__ == "__main__":
    main()
