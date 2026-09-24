"""Local, read-only FLINT/Arb MCP with isolated, time-limited computations."""
from __future__ import annotations

import asyncio
import json
from pathlib import Path
import subprocess
import sys
from typing import Any, Literal

import anyio
from mcp.server.fastmcp import FastMCP
from mcp.types import ToolAnnotations
from pydantic import StrictInt, StrictStr

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "tools"))
sys.path.insert(0, str(ROOT / "src"))

import flint
from research_engine.arb_expressions import FUNCTIONS, LIMITS, RELATIONS
from arb_worker import MAX_CF_TERMS, MAX_REQUEST_BYTES, SCOPE

TIMEOUT_SECONDS = 20
MAX_RESPONSE_BYTES = 131072
_slots = asyncio.Semaphore(2)
Variables = dict[str, StrictStr | list[StrictStr]]
READ_ONLY = ToolAnnotations(readOnlyHint=True, destructiveHint=False,
                            idempotentHint=True, openWorldHint=False)
mcp = FastMCP("arb-local", instructions=(
    "Certify finite real expressions with FLINT/Arb. Start with arb_capabilities. "
    "Inputs are exact decimal/rational strings; retain outward rational endpoints. "
    "A comparison's holds=null is unresolved, never false. Input interval boxes "
    "are enclosed uniformly, without claiming omitted tails or analytic hypotheses. "
    "Use arb_paper_c_models and arb_paper_c_rate for canonical paper formulas, and "
    "arb_continued_fraction for certified partial quotients, never a float expansion. "
    "No arbitrary Python, files, networking or artifact writes. " + SCOPE))


async def calculate(operation: str, arguments: dict) -> dict:
    payload = json.dumps({"operation": operation, "arguments": arguments}, allow_nan=False).encode()
    if len(payload) > MAX_REQUEST_BYTES:
        raise ValueError("Request exceeds 32768 bytes")
    try:
        await asyncio.wait_for(_slots.acquire(), timeout=TIMEOUT_SECONDS)
    except TimeoutError as exc:
        raise ValueError("Arb workers busy; retry this bounded request") from exc
    process = None
    try:
        launch = asyncio.create_task(asyncio.create_subprocess_exec(
            sys.executable, "-I", "-B", str(ROOT / "tools/arb_worker.py"),
            stdin=asyncio.subprocess.PIPE, stdout=asyncio.subprocess.PIPE,
            stderr=asyncio.subprocess.PIPE, cwd=str(ROOT),
            creationflags=subprocess.CREATE_NO_WINDOW if sys.platform == "win32" else 0))
        try:
            process = await asyncio.shield(launch)
        except asyncio.CancelledError:
            # Recover the handle even if cancellation arrives during process creation.
            with anyio.CancelScope(shield=True):
                process = await launch
            raise
        output, _error = await asyncio.wait_for(process.communicate(payload), TIMEOUT_SECONDS)
        if process.returncode:
            raise ValueError(f"Arb worker exited with code {process.returncode}; no certificate")
        if len(output) > MAX_RESPONSE_BYTES:
            raise ValueError("Result exceeds output budget; reduce precision or expression size")
        result = json.loads(output)
        if "error" in result:
            raise ValueError(result["error"])
        return result
    except TimeoutError as exc:
        raise ValueError("Arb calculation exceeded 20 seconds; no certificate") from exc
    finally:
        try:
            # MCP uses AnyIO level cancellation: cleanup must survive its repeated delivery.
            with anyio.CancelScope(shield=True):
                if process is not None and process.returncode is None:
                    try:
                        process.kill()
                    except ProcessLookupError:
                        pass
                    await process.communicate()
        finally:
            _slots.release()


@mcp.tool(annotations=READ_ONLY)
def arb_capabilities() -> dict[str, Any]:
    """Read syntax, budgets, examples, backend versions, checkout and proof boundaries."""
    return {"backend": "python-flint/Arb", "python_flint": flint.__version__,
            "flint": flint.__FLINT_VERSION__, "root": str(ROOT),
            "syntax": "Exact decimal literals, + - * / **, parentheses, variables, constant pi",
            "functions": FUNCTIONS, "relations": RELATIONS,
            "variables": 'Point: {"q":"3/5"}; closed interval: {"x":["1/3","1/2"]}',
            "limits": {**LIMITS, "production_terms": 32, "root_digits": 100,
                       "continued_fraction_terms": MAX_CF_TERMS,
                       "root_domain": "0 <= lower < upper <= 16", "exp_argument_abs": 700,
                       "workers": 2, "worker_seconds": TIMEOUT_SECONDS,
                       "queue_wait_seconds": TIMEOUT_SECONDS, "request_bytes": MAX_REQUEST_BYTES,
                       "response_bytes": MAX_RESPONSE_BYTES},
            "examples": [{"tool": "arb_compare", "arguments":
                          {"left": "sqrt(2)", "right": "7/5", "relation": ">"}},
                         {"tool": "arb_evaluate", "arguments":
                          {"expression": "log(x)/log(3)", "variables": {"x": ["2", "3"]}}},
                         {"tool": "arb_continued_fraction", "arguments":
                          {"expression": "log(3)/log(2)", "terms": 40}}],
            "scope": SCOPE, "guide": "arb://guide"}


@mcp.tool(annotations=READ_ONLY)
async def arb_evaluate(expression: StrictStr, variables: Variables | None = None,
                       bits: StrictInt = 128) -> dict[str, Any]:
    """Enclose a bounded real expression, uniformly over an optional exact input box.

    Decimal tokens are exact, including 0.1; no Python eval is used. Variables
    are strings or [lower,upper] strings. Read arb_capabilities for syntax/limits.
    Returns outward rational endpoints, or unresolved for a nonfinite/domain result.
    """
    return await calculate("evaluate", {"source": expression, "variables": variables, "bits": bits})


@mcp.tool(annotations=READ_ONLY)
async def arb_compare(left: StrictStr, right: StrictStr,
                      relation: Literal["<", "<=", ">", ">=", "==", "!="] = ">",
                      variables: Variables | None = None, bits: StrictInt = 128,
                      max_bits: StrictInt = 4096) -> dict[str, Any]:
    """Certify an inequality/equality, doubling precision up to max_bits.

    holds=true certifies the relation uniformly; false certifies its negation
    uniformly; null means unresolved. Overlapping intervals are never a false
    certificate. Increasing precision cannot remove input uncertainty or interval
    dependency (even x-x may enclose a range). No symbolic identity simplification.
    """
    return await calculate("compare", {"left": left, "right": right, "relation": relation,
                                      "variables": variables, "bits": bits, "max_bits": max_bits})


@mcp.tool(annotations=READ_ONLY)
async def arb_production_root(terms: list[list[StrictStr]], lower: StrictStr = "0",
                              upper: StrictStr = "1", digits: StrictInt = 24,
                              bits: StrictInt = 128, max_bits: StrictInt = 4096) -> dict[str, Any]:
    """Bracket the unique root of sum(c * base**lambda)=1 by exact rational bisection.

    terms are 1..32 [coefficient,base] string pairs with c>0 and 0<base<1.
    Require 0<=lower<upper<=16 and 1..100 decimal width digits. Endpoint signs
    certify existence; positivity implies strict decrease. Not a general root finder.
    Use arb_paper_c_models to retrieve canonical terms without transcribing them.
    """
    return await calculate("production_root", {"terms": terms, "lower": lower, "upper": upper,
                                               "digits": digits, "bits": bits, "max_bits": max_bits})


@mcp.tool(annotations=READ_ONLY)
async def arb_continued_fraction(expression: StrictStr, terms: StrictInt = 20,
                                 variables: Variables | None = None, bits: StrictInt = 128,
                                 max_bits: StrictInt = 4096) -> dict[str, Any]:
    """Certify the leading continued-fraction partial quotients of a real expression.

    A term is returned only when it is the same for every point of the enclosure,
    including an input box; precision doubles up to max_bits. status=unresolved
    returns the certified prefix and why expansion stopped; it never guesses a term.
    A bare exact rational such as "355/113" expands exactly by Euclid's algorithm.
    terms is 1..1000; last_convergent is p/q of the returned prefix.
    """
    return await calculate("continued_fraction", {"expression": expression, "terms": terms,
                                                  "variables": variables, "bits": bits,
                                                  "max_bits": max_bits})


@mcp.tool(annotations=READ_ONLY)
async def arb_paper_c_models() -> dict[str, Any]:
    """Read all twelve canonical Paper C production models as exact coefficient/base pairs."""
    return await calculate("paper_c_models", {})


@mcp.tool(annotations=READ_ONLY)
async def arb_paper_c_rate(C: StrictInt, q: StrictStr,
                          kind: Literal["Chernoff", "Azuma"] = "Chernoff",
                          exponent: StrictStr = "5/8", bits: StrictInt = 128,
                          max_bits: StrictInt = 4096) -> dict[str, Any]:
    """Certify the canonical Paper C rate > 1-exponent at one integer depth C.

    Exact q/exponent strings in (0,1); C in [5,10000]. Default exponent is the
    written OOEE 5/8; use 100/203 for the formal baseline. This does not establish
    least C, an admissible error exponent, production or cylinder/pressure hypotheses.
    """
    return await calculate("paper_c_rate", {"C": C, "q": q, "kind": kind, "exponent": exponent,
                                           "bits": bits, "max_bits": max_bits})


@mcp.resource("arb://guide")
def guide() -> str:
    """Arb language, agent workflow, examples and trust boundaries."""
    return (ROOT / "docs/architecture/arb_mcp.md").read_text(encoding="utf-8")


@mcp.resource("arb://capabilities")
def capabilities_resource() -> str:
    return json.dumps(arb_capabilities())


if __name__ == "__main__":
    mcp.run(transport="stdio")
