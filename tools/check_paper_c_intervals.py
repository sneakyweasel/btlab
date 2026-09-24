"""Certify selected Paper C numerical constants with FLINT/Arb.

Independent of the older float/mpmath audit. This checks explicit expressions,
not production hypotheses, asymptotic error estimates, or termination.
Without --output the command only prints; artifact writes include provenance.
"""
from __future__ import annotations

import argparse
from fractions import Fraction as F
import json
from pathlib import Path
import sys

import flint
from flint import arb

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "src"))

from research.experiments.provenance import write_manifest
from research_engine.intervals import (
    RootBracket, UnresolvedInterval, ball, production_residual, production_root,
    rational, signed_evaluation,
)

PAPER = ROOT / "docs/theory/juggler_fate_almost_all_note.md"
OOEE_NOTE = ROOT / "docs/theory/juggler_ooee_contagion_note.md"
LEAN = ROOT / "formal/Problems/Juggler/FateContagionBound.lean"
SCOPE = ("COMPUTATIONALLY VERIFIED: finite Arb certificates for explicit Paper C "
         "production roots, recurrence slack, and integer rate crossings. "
         "No Lean proof, production estimate, asymptotic bound, or termination claim.")


def production_models() -> dict:
    """Exact coefficients from (1.1), Appendix C, and the OOEE companion §5."""
    pair = [(F(1), F(1, 2)), (F(1, 9), F(3, 8)), (F(2, 9), F(3, 4))]
    models = {"pairing": pair}
    ladder = list(pair)
    for k in range(2, 7):
        ladder = ladder + [(F(1, 3**(k + 1)), F(1, 2) * F(3, 4)**k)]
        models[f"V{k}"] = ladder
    models.update({
        "conditional_Appendix_C": pair + [(F(1, 9), F(9, 32))],
        "depth_two_ideal": [(F(1), F(1, 2)), (F(1, 3), F(3, 4))],
        "OOEE_fixed": [(F(1), F(1, 2)), (F(33, 100), F(3, 4)),
                       (F(11, 100), F(9, 16))],
        "OOEE_limiting_model": [(F(1), F(1, 2)), (F(1, 3), F(3, 4)),
                                (F(1, 9), F(9, 16))],
        "sweep": [(F(1), F(1, 2)), (F(2, 21), F(3, 4))],
        "worst_case_share": [(F(1), F(1, 2)), (F(2, 9), F(3, 4))],
    })
    return models


def rate(C: int, q: F, kind: str) -> arb:
    """Paper C Theorem 4's KL/pressure or Azuma rate, with zero below drift."""
    q = rational(q)
    if type(C) is not int or C < 5 or not 0 < q < 1:
        raise ValueError("Require integer C >= 5 and 0 < q < 1")
    if kind not in {"Chernoff", "Azuma"}:
        raise ValueError("Unknown rate kind")
    log2, log3 = arb(2).log(), arb(3).log()
    L3 = log3 / log2
    p, qb = (1 - ball(F(1, C))) / L3, ball(q)
    if p <= qb:
        return arb(0)
    if not p > qb:
        return arb("nan")  # force precision escalation rather than select a branch
    if kind == "Chernoff":
        kl = p * (p / qb).log() + (1 - p) * ((1 - p) / (1 - qb)).log()
        return C * kl / log2
    return 2 * (C * (1 - qb * L3) - 1)**2 / (C * L3**2 * log2)


def least_depth(q: F, kind: str, exponent: F | RootBracket, *, max_C=10000) -> dict:
    """Check every integer C from 5 through the first certified crossing.

    A root bracket is propagated in full when computing 1-lambda. All earlier
    candidates must be certified nonpositive; one unresolved sign aborts the run.
    Thus minimality does not depend on a sampled monotonicity assumption.
    """
    q = rational(q)
    if type(max_C) is not int or max_C < 5:
        raise ValueError("Require integer max_C >= 5")
    if not isinstance(exponent, RootBracket):
        exponent = rational(exponent)
    lo = exponent.lower if isinstance(exponent, RootBracket) else exponent
    hi = exponent.upper if isinstance(exponent, RootBracket) else exponent
    if not 0 < lo <= hi < 1 or not 0 < q < 1:
        raise ValueError("Require 0 < lambda < 1 and 0 < q < 1")
    drift, _ = signed_evaluation(lambda: arb(2).log() - ball(q) * arb(3).log())
    if drift <= 0:
        raise ValueError("q is outside the positive-drift range")

    def gap(C):
        lam = exponent.as_ball() if isinstance(exponent, RootBracket) else ball(exponent)
        return rate(C, q, kind) - (1 - lam)

    previous = None
    for C in range(5, max_C + 1):
        decision, evidence = signed_evaluation(lambda: gap(C))
        if decision > 0:
            return {"least_integer_C": C, "checked_from": 5,
                    "rejected_candidates": C - 5, "gap_at_C": evidence,
                    "gap_at_previous_C": previous}
        previous = evidence
    raise UnresolvedInterval(f"No crossing through C={max_C}")


#: Theorem 5.20's five actual productions. Kept out of production_models(), whose twelve
#: canonical models the Arb MCP serves; certified here alongside them.
FIVE_ACTUAL_PRODUCTIONS = [(F(1), F(1, 2)), (F(33, 100), F(3, 4)),
                           (F(11, 100), F(9, 16)), (F(1, 14), F(27, 32))]


def certificate() -> dict:
    models = {**production_models(), "five_actual_productions": FIVE_ACTUAL_PRODUCTIONS}
    roots = {name: production_root(terms) for name, terms in models.items()}
    regimes = {key: roots[key] for key in ("pairing", "V6", "conditional_Appendix_C")}
    regimes.update({"Lean_baseline_100_203": F(100, 203), "written_OOEE_5_8": F(5, 8),
                    "Theorem_5_20_37_50": F(37, 50)})
    depths = {name: {
        kind: {str(q): least_depth(q, kind, exponent)
               for q in (F(1, 2), F(11, 20), F(3, 5), F(31, 50))}
        for kind in ("Chernoff", "Azuma")}
        for name, exponent in regimes.items()}
    positive, slack = signed_evaluation(
        lambda: production_residual(models["OOEE_fixed"], F(5, 8)))
    if positive != 1:
        raise ArithmeticError("The OOEE recurrence does not have positive slack at 5/8")
    positive5, slack5 = signed_evaluation(
        lambda: production_residual(models["five_actual_productions"], F(37, 50)))
    if positive5 != 1:
        raise ArithmeticError("The five-production recurrence does not have positive slack at 37/50")
    return {
        "schema": "btlab.paper-c-intervals.v1", "scope": SCOPE,
        "arithmetic": {"backend": "python-flint/Arb", "version": flint.__version__,
                       "initial_bits": 128, "max_bits": 4096, "root_decimal_width": 24,
                       "inputs": "exact rationals; endpoints exported as rational strings"},
        "roots": {name: {**root.as_dict(),
                         "terms": [[str(c), str(b)] for c, b in models[name]]}
                  for name, root in roots.items()},
        "OOEE_slack_at_5_8": slack, "five_production_slack_at_37_50": slack5,
        "rate_crossings": depths,
        "not_certified": ["run-model transfer-matrix eigenvalues",
                          "infinite tails and asymptotic error constants",
                          "OOEE production theorem or its independent analytic review",
                          "Paper B's Theorem 6.3 or the depth-five production inequalities",
                          "open cylinder, pressure, and Tao-rate hypotheses"],
        "all_checks_passed": True,
    }


def main(argv=None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, help="Write JSON plus a .research.json sidecar")
    args = parser.parse_args(argv)
    result = certificate()
    payload = json.dumps(result, indent=2) + "\n"
    if args.output:
        dest = args.output.resolve()
        dest.parent.mkdir(parents=True, exist_ok=True)
        dest.write_text(payload, encoding="utf-8", newline="\n")
        write_manifest(dest.with_suffix(".research.json"), programme="juggler", scope=SCOPE,
                       outputs=[dest], parameters=result["arithmetic"], root=ROOT,
                       command=["python", "tools/check_paper_c_intervals.py", "--output", str(args.output)],
                       inputs=[PAPER, OOEE_NOTE, LEAN], sources=[Path(__file__)])
    print(payload, end="")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
