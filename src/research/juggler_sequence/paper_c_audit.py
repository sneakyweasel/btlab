"""Audit probe for Paper C (``docs/theory/juggler_fate_almost_all_note.md``).

Papers A and B have audit modules; Paper C had none, so its printed constants were checked
only where some other test happened to touch them.  This closes that asymmetry.  Four layers,
none of which is a proof:

1. **Contagion exponents.**  The three-state residual and the run-ladder transfer matrix of the
   exponent calculus, recomputed and compared with every exponent Paper C prints:
   ``lambda* = 0.3774``, pairing-only ``0.4480``, OEOEE ``0.4801``,
   V_3 ``0.4891``, V_4 ``0.4916``, V_5 ``0.4924``, ``lambda** = 0.4926`` (plus V_6),
   ``lambda*** = 0.5392``, the conditional depth-two ideal-share model ``0.4927``,
   and the conditional ``lambda(r)`` transfer-matrix ladder of Section 5.7.
2. **Tao thresholds and depths.**  ``e(20) = 0.574``, ``e(18) = 0.480``, the least depth in each
   regime, and the one-sided ``C(q)`` values.  Every regime is carried explicitly, because the
   same symbol ``C(q)`` denotes different numbers under ``lambda**`` and ``lambda***``
   (``C(0.55)`` is ``41`` under ``lambda**``, ``44`` under pairing, ``39`` under ``lambda***``)
   and Paper C quotes the third.
3. **The Section 8.4 constants table.**  ``L(y)``, ``d(y)``, the exact fair-coin bad probability,
   the target ``(log y)^-0.6`` and the least depth for rate ``0.6``, at the three printed scales.
4. **Statement boundaries.**  Exact integer arithmetic records that ``1015`` follows ``OEOEE``
   to ``6`` although ``floor(1015^(9/32)) = 7``; it separately verifies the nested fiber used by
   the finite ``V_k`` argument.  Numerical inequalities also guard the additive-error exponent
   in Theorem 9.1 and the optimizing tilt required for the KL rate in Proposition 9.3.
The floor-derived stratification scales ``N0^{4/3}``, ``N0^{3/2}`` and ``N0^2`` were audited
here under a heading calling them "Section 6".  Paper C prints none of them; Paper A does, and
cites Paper C only for the odd-generation result underneath.  They now live in
``paper_a_audit.stratification_checks``, read from Paper A's own text.

A check is a dict with ``printed``, ``computed`` and ``ok``.  Nothing here proves a theorem, and
nothing here is a halt statement.  Run ``python -m research.juggler_sequence.paper_c_audit``.
"""

from __future__ import annotations

from research.juggler_sequence.lean_paths import (
    DATA_ROOT,
    DOCS_THEORY,
    REPO_ROOT,
)

import json
import math
from pathlib import Path
from typing import Any, Callable

import numpy as np

from research.juggler_sequence.cycle_finance import git_commit
from research.juggler_sequence.fate_contagion import RECURSIONS, lambda_root
from research.juggler_sequence.tao_reduction import (
    LOG2_3,
    N0_CERTIFIED,
    REQUIRED_RATE,
    REQUIRED_RATE_STAR3,
    azuma_exponent,
    bad_word_probability,
    chernoff_biased_exponent,
    chernoff_exponent,
    kl_bernoulli,
    least_C,
    least_C_biased,
    least_C_pressure,
    required_depth,
    scale_L,
)

DATA_DIR = DATA_ROOT / "paper_c_audit"
PAPER = DOCS_THEORY / "juggler_fate_almost_all_note.md"

#: absolute tolerance for a printed four-decimal exponent
EXP_TOL = 5e-5


def _bisect(f: Callable[[float], float], lo: float = 1e-9, hi: float = 1.0, iters: int = 200) -> float:
    """Root of a strictly decreasing ``f`` on ``[lo, hi]``; the lower end is kept off zero
    because the three-state residual has a ``1/(1-x)`` factor singular at ``lambda = 0``."""

    flo, fhi = f(lo), f(hi)
    if flo < 0:
        return lo
    if fhi > 0:
        return hi
    for _ in range(iters):
        mid = 0.5 * (lo + hi)
        if f(mid) > 0:
            lo = mid
        else:
            hi = mid
    return 0.5 * (lo + hi)


def residual(lam: float, eta0: float, eta1: float, eta2: float) -> float:
    """Section 5.7's three-state residual; its root is the contagion exponent."""

    x = 2.0**-lam

    def y(e: float) -> float:
        return (e / 3.0) * 1.5**lam

    return x * x * y(eta2) / (1 - x) + x * y(eta1) + y(eta0) - 1.0


def exponent(eta0: float, eta1: float, eta2: float) -> float:
    if residual(1 - 1e-12, eta0, eta1, eta2) > 0:
        return 1.0
    return _bisect(lambda lam: residual(lam, eta0, eta1, eta2))


def run_exponent(r: int, eta1: float = 1.0, eta2: float = 1.0, nu: float = 1.0) -> float:
    """Exponent when backward ``O``-runs are controlled only up to length ``r``."""

    def rho(lam: float) -> float:
        x, g = 2.0**-lam, 1.5**lam / 3.0
        states = ["E1", "E2"] + [f"O{i}" for i in range(1, r + 1)]
        k = {s: i for i, s in enumerate(states)}
        M = np.zeros((len(states), len(states)))
        for s in states:
            M[k[s], k["E2" if s.startswith("E") else "E1"]] += x
            if s == "E1":
                M[k[s], k["O1"]] += eta1 * g
            elif s == "E2":
                M[k[s], k["O1"]] += eta2 * g
            else:
                i = int(s[1:])
                if i + 1 <= r:
                    M[k[s], k[f"O{i + 1}"]] += nu * g
        return float(max(abs(np.linalg.eigvals(M))))

    if rho(1 - 1e-9) > 1:
        return 1.0
    return _bisect(lambda lam: rho(lam) - 1.0)


def _check(name: str, printed: float, computed: float, tol: float) -> dict[str, Any]:
    return {
        "name": name,
        "printed": printed,
        "computed": computed,
        "abs_error": abs(printed - computed),
        "ok": abs(printed - computed) <= tol,
    }


def _assertion(name: str, holds: bool, **evidence: Any) -> dict[str, Any]:
    """A non-rounded audit check, with the exact evidence retained in the JSON payload."""

    return {
        "name": name,
        "printed": True,
        "computed": bool(holds),
        "abs_error": 0 if holds else 1,
        "ok": bool(holds),
        "evidence": evidence,
    }


def floor_rational_power(n: int, numerator: int, denominator: int) -> int:
    """Exact ``floor(n ** (numerator / denominator))`` by integer comparisons."""

    if n < 0 or numerator <= 0 or denominator <= 0:
        raise ValueError("require n >= 0 and positive exponents")
    target = n**numerator
    lo, hi = 0, 1
    while hi**denominator <= target:
        lo, hi = hi, 2 * hi
    while lo + 1 < hi:
        mid = (lo + hi) // 2
        if mid**denominator <= target:
            lo = mid
        else:
            hi = mid
    return lo


def juggler_step(n: int) -> int:
    """The exact Juggler map, using integer square roots in both branches."""

    return math.isqrt(n**3) if n % 2 else math.isqrt(n)


def fiber_counterexample() -> dict[str, Any]:
    """The smallest recorded falsifier of the collapsed ``OEOEE`` monomial fiber claim."""

    start, depth = 1015, 5
    orbit = [start]
    word: list[str] = []
    n = start
    for _ in range(depth):
        word.append("O" if n % 2 else "E")
        n = juggler_step(n)
        orbit.append(n)
    source = orbit[-1]
    collapsed = floor_rational_power(start, 9, 32)
    nested = floor_rational_power(start, 3, 4)
    return {
        "start": start,
        "word": "".join(word),
        "orbit": orbit,
        "source": source,
        "collapsed_9_32_floor": collapsed,
        "in_claimed_source_interval": source**32 <= start**9 < (source + 1) ** 32,
        "nested_3_4_floor": nested,
        "nested_source_condition": source**8 <= nested**3 < (source + 1) ** 8,
    }


def rate_boundary_evidence() -> dict[str, float]:
    """Numerical witnesses for the two corrected quantifier boundaries in Sections 9--10."""

    C_az, q_az = 100.0, 0.5
    azuma = azuma_exponent(C_az, q_az)
    weak_A = C_az + 1.5  # satisfies the old A > C + 1, but not the claimed rate absorption

    C_ch, q_ch = 41.0, 0.55
    p = (1.0 - 1.0 / C_ch) / LOG2_3
    theta_opt = math.log(p * (1.0 - q_ch) / (q_ch * (1.0 - p)))

    def tilt_rate(theta: float) -> float:
        return theta * p - math.log(1.0 - q_ch + q_ch * math.exp(theta))

    return {
        "C_azuma": C_az,
        "q_azuma": q_az,
        "azuma_exponent": azuma,
        "old_A_witness": weak_A,
        "additive_error_exponent": weak_A - C_az,
        "C_chernoff": C_ch,
        "q_chernoff": q_ch,
        "p_C": p,
        "theta_optimizer": theta_opt,
        "optimized_tilt_rate": tilt_rate(theta_opt),
        "off_tilt_rate": tilt_rate(theta_opt / 2.0),
        "kl_rate": kl_bernoulli(p, q_ch),
        "chernoff_exponent": chernoff_biased_exponent(int(C_ch), q_ch),
    }


def boundary_checks() -> list[dict[str, Any]]:
    """Exact/computational guards for corrected claims, rather than manuscript token checks."""

    fiber = fiber_counterexample()
    rate = rate_boundary_evidence()
    return [
        _assertion(
            "1015 follows OEOEE to 6",
            fiber["word"] == "OEOEE" and fiber["orbit"] == [1015, 32336, 179, 2394, 48, 6],
            **fiber,
        ),
        _assertion(
            "collapsed 9/32 fiber differs from exact iterate",
            fiber["collapsed_9_32_floor"] == 7
            and fiber["source"] == 6
            and not fiber["in_claimed_source_interval"],
            **fiber,
        ),
        _assertion(
            "nested OEOEE source condition survives the falsifier",
            fiber["nested_3_4_floor"] == 179 and fiber["nested_source_condition"],
            **fiber,
        ),
        _assertion(
            "A greater than C plus one need not absorb the Azuma target",
            rate["old_A_witness"] > rate["C_azuma"] + 1.0
            and rate["additive_error_exponent"] < rate["azuma_exponent"],
            **rate,
        ),
        _assertion(
            "optimizing tilt is required for the KL rate",
            abs(rate["optimized_tilt_rate"] - rate["kl_rate"]) < 1e-12
            and rate["off_tilt_rate"] < rate["kl_rate"],
            **rate,
        ),
    ]


def contagion_checks() -> list[dict[str, Any]]:
    """Every contagion exponent Paper C prints, against the recursion roots and the ladder."""

    out = [
        _check("lambda_star (block_average_only)", 0.3774, lambda_root(RECURSIONS["block_average_only"]), EXP_TOL),
        _check("pairing-only (block_average_plus_third)", 0.4480, lambda_root(RECURSIONS["block_average_plus_third"]), EXP_TOL),
        _check("oeoee-only (block_third_plus_oeoee)", 0.4801, lambda_root(RECURSIONS["block_third_plus_oeoee"]), EXP_TOL),
        _check("v3-only (block_third_plus_oeoee_v3)", 0.4891, lambda_root(RECURSIONS["block_third_plus_oeoee_v3"]), EXP_TOL),
        _check("v4-only (block_third_plus_oeoee_v4)", 0.4916, lambda_root(RECURSIONS["block_third_plus_oeoee_v4"]), EXP_TOL),
        _check("v5-only (block_third_plus_oeoee_v5)", 0.4924, lambda_root(RECURSIONS["block_third_plus_oeoee_v5"]), EXP_TOL),
        _check("lambda** (block_third_plus_oeoee_v6)", 0.4926, lambda_root(RECURSIONS["block_third_plus_oeoee_v6"]), EXP_TOL),
        _check("lambda*** (block_third_plus_ooeee)", 0.5392, lambda_root(RECURSIONS["block_third_plus_ooeee"]), EXP_TOL),
        _check("conditional depth-two ideal-share model", 0.4927, lambda_root(RECURSIONS["depth_two_ideal"]), EXP_TOL),
        # the same pairing/ideal constants through the residual, which is how Section 5.7 derives them
        _check("lambda_star via residual", 0.3774, exponent(0.0, 0.0, 1.0), EXP_TOL),
        _check("pairing via residual", 0.4480, exponent(0.0, 2 / 3, 1.0), EXP_TOL),
        _check("ideal via residual", 0.4927, exponent(0.0, 1.0, 1.0), EXP_TOL),
    ]
    # Section 5.7: conditional transfer-matrix outputs, not attained production theorems.
    ladder = {1: (0.4480, 0.4927), 2: (0.6247, 0.7180), 3: (0.7095, 0.8414), 4: (0.7516, 0.9121)}
    for r, (present, ideal) in ladder.items():
        out.append(_check(f"lambda({r}) conditional pairing-share model", present,
                          run_exponent(r, eta1=2 / 3), EXP_TOL))
        out.append(_check(f"lambda({r}) conditional ideal-share model", ideal,
                          run_exponent(r, eta1=1.0), EXP_TOL))
    return out


def tao_checks() -> list[dict[str, Any]]:
    """Rate thresholds, the exponents ``e(C)``, and the one-sided ``C(q)`` in each regime."""

    pairing = lambda_root(RECURSIONS["block_average_plus_third"])
    oeoee = lambda_root(RECURSIONS["block_third_plus_oeoee"])
    v3 = lambda_root(RECURSIONS["block_third_plus_oeoee_v3"])
    v4 = lambda_root(RECURSIONS["block_third_plus_oeoee_v4"])
    v5 = lambda_root(RECURSIONS["block_third_plus_oeoee_v5"])
    lam2 = lambda_root(RECURSIONS["block_third_plus_oeoee_v6"])
    lam3 = lambda_root(RECURSIONS["block_third_plus_ooeee"])
    ideal = lambda_root(RECURSIONS["depth_two_ideal"])
    out = [
        _check("rate threshold 1 - pairing", 0.5520, 1.0 - pairing, 1e-3),
        _check("rate threshold 1 - oeoee", 0.5199, 1.0 - oeoee, 1e-3),
        _check("rate threshold 1 - v3", 0.5109, 1.0 - v3, 1e-3),
        _check("rate threshold 1 - v4", 0.5084, 1.0 - v4, 1e-3),
        _check("rate threshold 1 - v5", 0.5076, 1.0 - v5, 1e-3),
        _check("rate threshold 1 - lambda**", 0.5074, 1.0 - lam2, 1e-3),
        _check("rate threshold 1 - lambda***", 0.4608, 1.0 - lam3, 1e-3),
        _check("rate threshold 1 - lambda_ideal", 0.5073, 1.0 - ideal, 1e-3),
        _check("e(20)", 0.574, chernoff_exponent(20), 1e-3),
        _check("e(19)", 0.527, chernoff_exponent(19), 1e-3),
        _check("e(18)", 0.480, chernoff_exponent(18), 1e-3),
        _check("least depth, pairing regime", 20, least_C(1.0 - pairing), 0),
        _check("least depth, oeoee regime", 19, least_C(1.0 - oeoee), 0),
        _check("least depth, v3 regime", 19, least_C(1.0 - v3), 0),
        _check("least depth, v4 regime", 19, least_C(1.0 - v4), 0),
        _check("least depth, v5 regime", 19, least_C(1.0 - v5), 0),
        _check("least depth, lambda** regime", 19, least_C(REQUIRED_RATE), 0),
        _check("least depth, lambda*** regime", 18, least_C(REQUIRED_RATE_STAR3), 0),
        _check("least depth, ideal regime", 19, least_C(1.0 - ideal), 0),
        # One-sided Azuma C(q), with every row kept in its explicit contagion regime.
        _check("C(0.5), lambda*** regime", 18, least_C_biased(0.5, REQUIRED_RATE_STAR3), 0),
        _check("C(0.55), lambda*** regime", 39, least_C_biased(0.55, REQUIRED_RATE_STAR3), 0),
        _check("C(0.6), lambda*** regime", 206, least_C_biased(0.6, REQUIRED_RATE_STAR3), 0),
        _check("C(0.62), lambda*** regime", 1451, least_C_biased(0.62, REQUIRED_RATE_STAR3), 0),
        _check("C(0.5), lambda** regime", 19, least_C_biased(0.5, REQUIRED_RATE), 0),
        _check("C(0.55), lambda** regime", 41, least_C_biased(0.55, REQUIRED_RATE), 0),
        _check("C(0.6), lambda** regime", 223, least_C_biased(0.6, REQUIRED_RATE), 0),
        _check("C(0.62), lambda** regime", 1586, least_C_biased(0.62, REQUIRED_RATE), 0),
        _check("C(0.5), pairing regime", 20, least_C_biased(0.5, 1.0 - pairing), 0),
        _check("C(0.55), pairing regime", 44, least_C_biased(0.55, 1.0 - pairing), 0),
        _check("C(0.6), pairing regime", 240, least_C_biased(0.6, 1.0 - pairing), 0),
        _check("C(0.62), pairing regime", 1715, least_C_biased(0.62, 1.0 - pairing), 0),
        # Biased Chernoff/no-momentum C(q), valid at theta = theta_{C,q}.
        _check("pressure C(0.5), lambda*** regime", 18, least_C_pressure(0.5, REQUIRED_RATE_STAR3), 0),
        _check("pressure C(0.55), lambda*** regime", 38, least_C_pressure(0.55, REQUIRED_RATE_STAR3), 0),
        _check("pressure C(0.6), lambda*** regime", 198, least_C_pressure(0.6, REQUIRED_RATE_STAR3), 0),
        _check("pressure C(0.62), lambda*** regime", 1369, least_C_pressure(0.62, REQUIRED_RATE_STAR3), 0),
        _check("pressure C(0.5), lambda** regime", 19, least_C_pressure(0.5, REQUIRED_RATE), 0),
        _check("pressure C(0.55), lambda** regime", 41, least_C_pressure(0.55, REQUIRED_RATE), 0),
        _check("pressure C(0.6), lambda** regime", 214, least_C_pressure(0.6, REQUIRED_RATE), 0),
        _check("pressure C(0.62), lambda** regime", 1496, least_C_pressure(0.62, REQUIRED_RATE), 0),
        _check("pressure C(0.5), pairing regime", 20, least_C_pressure(0.5, 1.0 - pairing), 0),
        _check("pressure C(0.55), pairing regime", 43, least_C_pressure(0.55, 1.0 - pairing), 0),
        _check("pressure C(0.6), pairing regime", 230, least_C_pressure(0.6, 1.0 - pairing), 0),
        _check("pressure C(0.62), pairing regime", 1618, least_C_pressure(0.62, 1.0 - pairing), 0),
    ]
    return out


def constants_table_checks() -> list[dict[str, Any]]:
    """Section 8.4 at the certified floor, using its conservative display value ``C = 20``."""

    printed = {
        20: {"L": 1.25, "d": 25, "bad": 0.065, "target": 0.100, "least_depth": 19},
        100: {"L": 3.55, "d": 72, "bad": 0.017, "target": 0.038, "least_depth": 56},
        1000: {"L": 6.87, "d": 138, "bad": 0.0038, "target": 0.0096, "least_depth": 117},
    }
    out: list[dict[str, Any]] = []
    for log10_y, row in printed.items():
        log_y = log10_y * math.log(10.0)
        L = scale_L(log_y, N0_CERTIFIED)
        d = math.ceil(20 * L)
        out.append(_check(f"L(1e{log10_y})", row["L"], L, 5e-3))
        out.append(_check(f"d(1e{log10_y})", row["d"], d, 0))
        out.append(_check(f"bad probability at 1e{log10_y}", row["bad"], bad_word_probability(L, d), 5e-4))
        out.append(_check(f"(log y)^-0.6 at 1e{log10_y}", row["target"], log_y**-0.6, 5e-4))
        out.append(_check(f"least depth for rate 0.6 at 1e{log10_y}", row["least_depth"],
                          required_depth(log_y, N0_CERTIFIED, 0.6), 0))
    return out


def summary() -> dict[str, Any]:
    groups = {
        "contagion": contagion_checks(),
        "tao": tao_checks(),
        "constants_table": constants_table_checks(),
        "statement_boundaries": boundary_checks(),
    }
    failures = [c for g in groups.values() for c in g if not c["ok"]]
    return {
        "git_commit": git_commit(),
        "paper": str(PAPER.relative_to(REPO_ROOT)).replace("\\", "/"),
        "N0": N0_CERTIFIED,
        "checks": groups,
        "classification": {
            "total_checks": sum(len(g) for g in groups.values()),
            "failures": len(failures),
            "failing_names": [c["name"] for c in failures],
            "all_printed_constants_reproduce": not failures,
        },
    }


def main() -> None:
    result = summary()
    DATA_DIR.mkdir(parents=True, exist_ok=True)
    out = DATA_DIR / "summary.json"
    out.write_text(json.dumps(result, indent=2), encoding="utf-8")
    print(json.dumps(result["classification"], indent=2))
    print(out)


if __name__ == "__main__":
    main()
