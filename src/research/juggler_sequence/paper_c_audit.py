"""Audit probe for Paper C (``docs/theory/juggler_fate_almost_all_note.md``).

Papers A and B have audit modules; Paper C had none, so its printed constants were checked
only where some other test happened to touch them.  This closes that asymmetry.  Four layers,
none of which is a proof:

1. **Contagion exponents.**  The three-state residual and the run-ladder transfer matrix of the
   exponent calculus, recomputed and compared with every exponent Paper C prints:
   ``lambda* = 0.3774``, ``lambda** = 0.4480``, ``lambda*** = 0.5392``, the depth-two ideal
   ceiling ``0.4927``, and the ``lambda(r)`` ladder of Section 5.7.
2. **Tao thresholds and depths.**  ``e(20) = 0.574``, ``e(18) = 0.480``, the least depth in each
   regime, and the one-sided ``C(q)`` values.  Every regime is carried explicitly, because the
   same symbol ``C(q)`` denotes different numbers under ``lambda**`` and ``lambda***``
   (``C(0.55)`` is ``44`` in the first and ``39`` in the second) and Paper C quotes the second.
3. **The Section 8.4 constants table.**  ``L(y)``, ``d(y)``, the exact fair-coin bad probability,
   the target ``(log y)^-0.6`` and the least depth for rate ``0.6``, at the three printed scales.
4. **Floor-derived stratification scales.**  ``N0^{4/3}``, ``N0^{3/2}`` and ``N0^2``, the scales
   at which each type of failure can first appear.

A check is a dict with ``printed``, ``computed`` and ``ok``.  Nothing here proves a theorem, and
nothing here is a halt statement.  Run ``python -m research.juggler_sequence.paper_c_audit``.
"""

from __future__ import annotations

import json
import math
from pathlib import Path
from typing import Any, Callable

import numpy as np

from research.juggler_sequence.cycle_finance import git_commit
from research.juggler_sequence.fate_contagion import RECURSIONS, lambda_root
from research.juggler_sequence.tao_reduction import (
    N0_CERTIFIED,
    REQUIRED_RATE,
    REQUIRED_RATE_STAR3,
    bad_word_probability,
    chernoff_exponent,
    least_C,
    least_C_biased,
    required_depth,
    scale_L,
)

REPO_ROOT = Path(__file__).resolve().parents[3]
DATA_DIR = REPO_ROOT / "data" / "research" / "juggler" / "paper_c_audit"
PAPER = REPO_ROOT / "docs" / "theory" / "juggler_fate_almost_all_note.md"

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


def contagion_checks() -> list[dict[str, Any]]:
    """Every contagion exponent Paper C prints, against the recursion roots and the ladder."""

    out = [
        _check("lambda_star (block_average_only)", 0.3774, lambda_root(RECURSIONS["block_average_only"]), EXP_TOL),
        _check("lambda** (block_average_plus_third)", 0.4480, lambda_root(RECURSIONS["block_average_plus_third"]), EXP_TOL),
        _check("lambda*** (block_third_plus_ooeee)", 0.5392, lambda_root(RECURSIONS["block_third_plus_ooeee"]), EXP_TOL),
        _check("depth-two ideal ceiling", 0.4927, lambda_root(RECURSIONS["depth_two_ideal"]), EXP_TOL),
        # the same three constants through the residual, which is how Section 5.7 derives them
        _check("lambda_star via residual", 0.3774, exponent(0.0, 0.0, 1.0), EXP_TOL),
        _check("lambda** via residual", 0.4480, exponent(0.0, 2 / 3, 1.0), EXP_TOL),
        _check("ideal via residual", 0.4927, exponent(0.0, 1.0, 1.0), EXP_TOL),
    ]
    # Section 5.7 ladder: lambda(r) under the present sweep (eta1 = 2/3) and ideal fibers
    ladder = {1: (0.4480, 0.4927), 2: (0.6247, 0.7180), 3: (0.7095, 0.8414), 4: (0.7516, 0.9121)}
    for r, (present, ideal) in ladder.items():
        out.append(_check(f"lambda({r}) present sweep", present, run_exponent(r, eta1=2 / 3), EXP_TOL))
        out.append(_check(f"lambda({r}) ideal fibers", ideal, run_exponent(r, eta1=1.0), EXP_TOL))
    return out


def tao_checks() -> list[dict[str, Any]]:
    """Rate thresholds, the exponents ``e(C)``, and the one-sided ``C(q)`` in each regime."""

    lam2 = lambda_root(RECURSIONS["block_average_plus_third"])
    lam3 = lambda_root(RECURSIONS["block_third_plus_ooeee"])
    ideal = lambda_root(RECURSIONS["depth_two_ideal"])
    out = [
        _check("rate threshold 1 - lambda**", 0.5520, 1.0 - lam2, 1e-3),
        _check("rate threshold 1 - lambda***", 0.4608, 1.0 - lam3, 1e-3),
        _check("rate threshold 1 - lambda_ideal", 0.5073, 1.0 - ideal, 1e-3),
        _check("e(20)", 0.574, chernoff_exponent(20), 1e-3),
        _check("e(18)", 0.480, chernoff_exponent(18), 1e-3),
        _check("least depth, lambda** regime", 20, least_C(REQUIRED_RATE), 0),
        _check("least depth, lambda*** regime", 18, least_C(REQUIRED_RATE_STAR3), 0),
        _check("least depth, ideal regime", 19, least_C(1.0 - ideal), 0),
        # one-sided C(q): Paper C's Section 10 quotes the lambda*** regime
        _check("C(0.5), lambda*** regime", 18, least_C_biased(0.5, REQUIRED_RATE_STAR3), 0),
        _check("C(0.55), lambda*** regime", 39, least_C_biased(0.55, REQUIRED_RATE_STAR3), 0),
        # the lambda** regime values, quoted in AGENTS.md and the Tao note
        _check("C(0.5), lambda** regime", 20, least_C_biased(0.5, REQUIRED_RATE), 0),
        _check("C(0.55), lambda** regime", 44, least_C_biased(0.55, REQUIRED_RATE), 0),
    ]
    return out


def constants_table_checks() -> list[dict[str, Any]]:
    """Section 8.4, at the certified floor with the least unconditional depth ``C = 20``."""

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


def stratification_checks() -> list[dict[str, Any]]:
    """The scales at which each type of failure can first appear (Section 6)."""

    n0 = float(N0_CERTIFIED)
    return [
        _check("N0^{4/3}", 2.5e11, n0 ** (4 / 3), 0.05e11),
        _check("N0^{3/2}", 6.5e12, n0**1.5, 0.05e12),
        _check("N0^2", 1.2e17, n0**2, 0.05e17),
    ]


def summary() -> dict[str, Any]:
    groups = {
        "contagion": contagion_checks(),
        "tao": tao_checks(),
        "constants_table": constants_table_checks(),
        "stratification": stratification_checks(),
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
