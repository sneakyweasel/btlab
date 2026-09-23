"""One bounded Arb request per process; private JSON protocol used by arb_mcp."""
from __future__ import annotations

import hashlib
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "tools"))
sys.path.insert(0, str(ROOT / "src"))

import flint
from flint import ctx

from research_engine.arb_expressions import compare, evaluate, exact, precision
from research_engine.intervals import UnresolvedInterval, ball, enclosure, production_root

MAX_REQUEST_BYTES = 32768
SCOPE = ("Finite numerical enclosure of the supplied expressions and input box. "
         "Not a Lean proof, analytic hypothesis, infinite-tail bound, or termination proof. "
         "Only a certified decision establishes the requested comparison; unresolved is not false.")


def dispatch(operation: str, arguments: dict) -> dict:
    if operation == "evaluate":
        return evaluate(**arguments)
    if operation == "compare":
        return compare(**arguments)
    if operation == "production_root":
        terms = arguments["terms"]
        if (type(terms) is not list or not 1 <= len(terms) <= 32
                or any(type(pair) is not list or len(pair) != 2 for pair in terms)):
            raise ValueError("Require 1..32 [coefficient, base] pairs of exact strings")
        pairs = [(exact(c), exact(b)) for c, b in terms]
        lower, upper = exact(arguments.get("lower", "0")), exact(arguments.get("upper", "1"))
        if not 0 <= lower < upper <= 16:
            raise ValueError("Root endpoints require 0 <= lower < upper <= 16")
        digits = arguments.get("digits", 24)
        if type(digits) is not int or not 1 <= digits <= 100:
            raise ValueError("Require integer digits in [1, 100]")
        bits, max_bits = arguments.get("bits", 128), arguments.get("max_bits", 4096)
        precision(bits, max_bits)
        root = production_root(pairs, lower=lower, upper=upper, digits=digits,
                               bits=bits, max_bits=max_bits)
        return {"status": "certified", "root": root.as_dict(), "unique": True,
                "equation": "sum(coefficient * base**lambda) = 1",
                "justification": "Positive coefficients and bases in (0,1) give continuity "
                                 "and strict decrease; endpoint signs bracket the unique root.",
                "width_at_most": f"1e-{digits}"}
    if operation == "paper_c_models":
        from check_paper_c_intervals import production_models

        return {"models": {name: [[str(c), str(b)] for c, b in terms]
                           for name, terms in production_models().items()},
                "usage": "Pass one model's terms to arb_production_root",
                "source": "tools/check_paper_c_intervals.py:production_models",
                "caution": "Model names do not establish production hypotheses or attained exponents"}
    if operation == "paper_c_rate":
        from check_paper_c_intervals import rate

        C, q = arguments["C"], exact(arguments["q"])
        exponent = exact(arguments.get("exponent", "5/8"))
        kind = arguments.get("kind", "Chernoff")
        bits, max_bits = arguments.get("bits", 128), arguments.get("max_bits", 4096)
        precision(bits, max_bits)
        if type(C) is not int or not 5 <= C <= 10000 or not 0 < q < 1 or not 0 < exponent < 1:
            raise ValueError("Require integer 5 <= C <= 10000, 0 < q < 1, 0 < exponent < 1")
        if kind not in ("Chernoff", "Azuma"):
            raise ValueError("Unknown Paper C rate kind")
        attempts = []
        while True:
            attempts.append(bits)
            with ctx.workprec(bits):
                value = rate(C, q, kind)
                gap = value - (1 - ball(exponent))
                holds = True if gap > 0 else False if gap <= 0 else None
                if holds is not None or bits == max_bits:
                    return {"status": "certified" if holds is not None else "unresolved",
                            "holds": holds, "relation": "rate > 1 - exponent",
                            "rate": enclosure(value) if value.is_finite() else None,
                            "difference": enclosure(gap) if gap.is_finite() else None,
                            "precision_bits": bits, "attempted_bits": attempts,
                            "source": "tools/check_paper_c_intervals.py:rate",
                            "caution": "A single C is tested; minimality and the paper's "
                                       "cylinder/pressure and contagion hypotheses are not certified."}
            bits = min(2 * bits, max_bits)
    raise ValueError("Unknown worker operation")


def run(request: dict) -> dict:
    if type(request) is not dict or set(request) != {"operation", "arguments"}:
        raise ValueError("Expected operation and arguments")
    if type(request["arguments"]) is not dict:
        raise ValueError("Expected an arguments object")
    paths = [Path(__file__), ROOT / "src/research_engine/arb_expressions.py",
             ROOT / "src/research_engine/intervals.py"]
    if request["operation"] in ("paper_c_models", "paper_c_rate"):
        paths.append(ROOT / "tools/check_paper_c_intervals.py")
    sources = {p.relative_to(ROOT).as_posix(): hashlib.sha256(p.read_bytes()).hexdigest()
               for p in paths}
    try:
        result = dispatch(request["operation"], request["arguments"])
    except UnresolvedInterval as exc:
        result = {"status": "unresolved", "reason": str(exc)}
    return {**result, "schema": "btlab.arb-mcp.v1", "request": request,
            "backend": {"python_flint": flint.__version__, "flint": flint.__FLINT_VERSION__},
            "source_sha256": sources, "scope": SCOPE}


def main() -> None:
    try:
        raw = sys.stdin.buffer.read(MAX_REQUEST_BYTES + 1)
        if len(raw) > MAX_REQUEST_BYTES:
            raise ValueError("Request exceeds 32768 bytes")
        result = run(json.loads(raw))
    except (ValueError, TypeError, ArithmeticError, KeyError, RecursionError) as exc:
        result = {"error": str(exc), "error_type": type(exc).__name__}
    print(json.dumps(result, ensure_ascii=True, allow_nan=False))


if __name__ == "__main__":
    main()
