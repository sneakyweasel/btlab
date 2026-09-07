"""The failure margin: how much tilted momentum the conjecture's failure would require.

Two unconditional inequalities and one theorem of the laboratory bound the tilted odd share from
below when the conjecture is false.

* Theorem 9.2 (Paper C): ``#{τ > d} ≤ e^{-θ p_C d} Σ_{τ>d} e^{θ o_d}``.
* Proposition 9.3 (telescoping, no hypothesis):
  ``Σ_{τ>d} e^{θ o_d} ≤ N e^{θ} a_{θ,q}^{d-1} exp(c_θ Σ_{t<d} (s_θ(t) - q)^+)`` with
  ``a_{θ,q} = 1 + (e^θ - 1) q`` and ``c_θ = (e^θ - 1)/a_{θ,q}``.
* ``J-tao-rate-implies-conjecture``: if ``#{n odd in (y,2y] : τ(n) > d(y)} ≤ y (log y)^{-e}`` for all
  large ``y`` with ``e > 1 - λ** = REQUIRED_RATE``, the conjecture holds.  Contrapositive: if the
  conjecture is false then for every ``ε > 0`` the live count exceeds ``y (log y)^{-(REQUIRED_RATE+ε)}``
  for infinitely many ``y``.

With ``θ = log(p_C(1-q)/(q(1-p_C)))`` one has ``θ p_C - log a_{θ,q} = D(p_C ‖ q)``, so combining the
three, along those ``y``:

    (1/d) Σ_{t<d} (s_θ(t) - q)^+  ≥  m(C, q) - o(1),
    m(C, q) = [D(p_C ‖ q) - REQUIRED_RATE · ln 2 / C] / c_θ .

``m(C, q)`` is the *failure margin*: the average excess of the tilted odd share over ``q`` that the
conjecture's failure forces, at depth ``d = C L``.  It is ``0`` exactly at the laboratory's least
``C`` for each ``q`` (where ``C D(p_C‖q)/ln 2 = REQUIRED_RATE``), grows with ``C``, and tends to
``D(log2/log3 ‖ q)/c_{θ_∞,q}`` — ``6.62%`` at ``q = 1/2`` — as ``C → ∞``.  Below the least ``C`` the
margin is zero: at such depths no momentum at all is required for failure, so a census there
cannot bear on the no-momentum hypothesis.  The pressure census runs to depth ``40``, which at
``10^{12}``, ``10^{50}``, ``10^{100}`` is ``C = 76, 15.6, 11.3`` — below the least ``C = 19`` at the two
larger scales — and resolves the share to ``±0.06``, an order of magnitude coarser than the margin
at any accessible ``C``.

Nothing here is an estimate of the Juggler map; it is the exact price, in tilted share per step,
of the conjecture being false.
"""

from __future__ import annotations

import json
import math
from pathlib import Path
from typing import Any

from .tao_reduction import N0_CERTIFIED, REQUIRED_RATE, kl_bernoulli, least_C_pressure, p_of_C, scale_L

REPO_ROOT = Path(__file__).resolve().parents[3]
ARTIFACT = REPO_ROOT / "data" / "research" / "juggler" / "failure_margin" / "summary.json"
LOG2_3_INV = math.log(2.0) / math.log(3.0)          # the critical odd share 0.6309
CENSUS_DEPTH = 40                                     # tao_census / pressure_census d_max


def theta_of(p: float, q: float) -> float:
    """The tilt that re-centres a ``q``-coin at odd share ``p``: ``log(p(1-q)/(q(1-p)))``."""

    return math.log(p * (1.0 - q) / (q * (1.0 - p)))


def c_theta(theta: float, q: float) -> float:
    """``(e^θ - 1)/a_{θ,q}`` of Proposition 9.3."""

    return (math.exp(theta) - 1.0) / (1.0 + (math.exp(theta) - 1.0) * q)


def failure_margin(C: float, q: float = 0.5, required: float = REQUIRED_RATE) -> dict[str, Any]:
    """``m(C, q)`` and its ingredients; the margin is clipped at ``0`` below the least ``C``."""

    p = p_of_C(C)
    if p <= q:
        return {"C": C, "q": q, "p_C": p, "theta": None, "kl": 0.0, "margin": 0.0, "positive": False}
    theta = theta_of(p, q)
    kl = kl_bernoulli(p, q)
    raw = (kl - required * math.log(2.0) / C) / c_theta(theta, q)
    return {"C": C, "q": q, "p_C": p, "theta": theta, "kl": kl, "c_theta": c_theta(theta, q),
            "margin": max(raw, 0.0), "positive": raw > 0.0}


def asymptotic_margin(q: float = 0.5) -> float:
    """``lim_{C→∞} m(C, q) = D(log2/log3 ‖ q)/c_{θ_∞,q}``."""

    p = LOG2_3_INV
    return kl_bernoulli(p, q) / c_theta(theta_of(p, q), q)


def census_depth_as_C(log10_y: int, N0: int = N0_CERTIFIED, depth: int = CENSUS_DEPTH) -> float:
    """The census depth expressed as a multiple of ``L``: ``C = depth / L``."""

    return depth / scale_L(log10_y * math.log(10.0), N0)


def summary() -> dict[str, Any]:
    Cs = (20, 25, 30, 43, 50, 100, 230, 1000)
    qs = (0.5, 0.55, 0.6)
    table = {f"q{q}": {f"C{C}": failure_margin(C, q) for C in Cs} for q in qs}
    census = {f"1e{e}": {"C_at_depth_40": census_depth_as_C(e),
                         "margin_at_that_depth_q0.5": failure_margin(census_depth_as_C(e), 0.5)["margin"]}
              for e in (12, 50, 100)}
    return {
        "required_rate": REQUIRED_RATE,
        "table": table,
        "asymptotic_margin": {f"q{q}": asymptotic_margin(q) for q in qs},
        "census": census,
        "census_resolution": 0.06,
        "least_C": {f"q{q}": least_C_pressure(q) for q in qs},
        "margin_is_zero_below_least_C": all(
            not failure_margin(least_C_pressure(q) - 1, q)["positive"]
            and failure_margin(least_C_pressure(q), q)["positive"] for q in qs),
        "census_is_below_least_C_at": [k for k, v in census.items()
                                       if v["C_at_depth_40"] < least_C_pressure(0.5)],
        "margin_at_C20_q0.5": failure_margin(20, 0.5)["margin"],
        "margin_at_C50_q0.5": failure_margin(50, 0.5)["margin"],
        "classification": "FAILURE_MARGIN_IS_SUB_PERCENT_AT_C20_AND_BELOW_CENSUS_RESOLUTION",
    }


def main() -> None:
    s = summary()
    ARTIFACT.parent.mkdir(parents=True, exist_ok=True)
    ARTIFACT.write_text(json.dumps(s, indent=1, ensure_ascii=False), encoding="utf-8")
    print(f"required rate 1 - lambda** = {s['required_rate']:.4f}")
    for q, row in s["table"].items():
        cells = "  ".join(f"C{v['C']}={100*v['margin']:.2f}%" for v in row.values())
        print(f"  {q}: {cells}   ->  {100*s['asymptotic_margin'][q]:.2f}% as C->inf")
    for k, v in s["census"].items():
        print(f"  census depth 40 at {k}: C = {v['C_at_depth_40']:.1f}, margin {100*v['margin_at_that_depth_q0.5']:.2f}%")
    print(s["classification"])
    print(ARTIFACT)


if __name__ == "__main__":
    main()
