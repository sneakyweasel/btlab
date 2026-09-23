"""Bounded, exact-input expression language for real Arb enclosures.

Python's AST supplies syntax only: no compile/eval, attribute access or arbitrary
calls. Decimal tokens are read from source, never from AST binary floats.
Call in an isolated process when serving concurrent requests (FLINT ctx is global).
"""
from __future__ import annotations

import ast
from fractions import Fraction
import re

from flint import arb, ctx

from research_engine.intervals import UnresolvedInterval, ball, enclosure

LIMITS = {"expression_chars": 2048, "ast_nodes": 160, "ast_depth": 24,
          "variables": 24, "literal_chars": 128, "decimal_exponent": 256,
          "min_bits": 32, "max_bits": 4096, "power_exponent": 256,
          "magnitude_bits": 1024, "endpoint_exponent_min": -8192}
FUNCTIONS = ("sqrt", "log", "exp", "sin", "cos", "atan", "abs")
RELATIONS = ("<", "<=", ">", ">=", "==", "!=")
_DECIMAL = r"[+-]?(?:[0-9]+(?:\.[0-9]*)?|\.[0-9]+)(?:[eE]([+-]?[0-9]+))?"
_FRACTION = r"[+-]?[0-9]+/[0-9]+"


def exact(text: str) -> Fraction:
    """Parse bounded exact decimal/rational text without unbounded 10**exponent."""
    if type(text) is not str or not 1 <= len(text) <= LIMITS["literal_chars"]:
        raise ValueError("Exact numbers must be strings of 1..128 characters")
    match = re.fullmatch(_DECIMAL, text)
    if not match and not re.fullmatch(_FRACTION, text):
        raise ValueError("Use an exact decimal or p/q string, with no whitespace")
    if match and match[1] and abs(int(match[1])) > LIMITS["decimal_exponent"]:
        raise ValueError("Decimal exponent exceeds 256")
    try:
        value = Fraction(text)
    except (ValueError, ZeroDivisionError) as exc:
        raise ValueError("Invalid exact rational") from exc
    if abs(value) > 2**LIMITS["magnitude_bits"]:
        raise ValueError("Input magnitude exceeds 2**1024")
    return value


def precision(bits: int, max_bits: int | None = None) -> None:
    if max_bits is None:
        max_bits = bits
    if (type(bits) is not int or type(max_bits) is not int
            or not LIMITS["min_bits"] <= bits <= max_bits <= LIMITS["max_bits"]):
        raise ValueError("Require integer precision 32 <= bits <= max_bits <= 4096")


def bounded(value: arb) -> arb:
    """Reject nonfinite or enormous dyadics before exporting rational endpoints."""
    if not value.is_finite():
        raise UnresolvedInterval("Nonfinite enclosure; domain or denominator unresolved")
    if not abs(value) <= arb(2)**LIMITS["magnitude_bits"]:
        raise ValueError("Intermediate magnitude exceeds 2**1024")
    for part in (value.mid(), value.rad()):
        mantissa, exponent = part.man_exp()
        if mantissa and exponent < LIMITS["endpoint_exponent_min"]:
            raise ValueError("Intermediate dyadic exponent is below -8192")
    return value


class Expression:
    """Validated expression with exact point or closed-interval variable inputs."""

    def __init__(self, source: str, variables: dict | None = None):
        if type(source) is not str or not 1 <= len(source) <= LIMITS["expression_chars"]:
            raise ValueError("Expression must contain 1..2048 characters")
        self.source = source.strip()
        if variables is None:
            variables = {}
        if type(variables) is not dict or len(variables) > LIMITS["variables"]:
            raise ValueError("At most 24 named variables are allowed")
        self.variables = {}
        for name, value in variables.items():
            if (type(name) is not str or not re.fullmatch(r"[A-Za-z][A-Za-z0-9_]{0,31}", name)
                    or name in (*FUNCTIONS, "pi")):
                raise ValueError("Invalid or reserved variable name")
            if type(value) is str:
                lo = hi = exact(value)
            elif type(value) is list and len(value) == 2:
                lo, hi = map(exact, value)
            else:
                raise ValueError("Variables require exact strings or [lower, upper] strings")
            if lo > hi:
                raise ValueError("Variable interval requires lower <= upper")
            self.variables[name] = (lo, hi)
        try:
            self.tree = ast.parse(self.source, mode="eval")
        except (SyntaxError, RecursionError) as exc:
            raise ValueError("Invalid expression syntax") from exc
        if sum(1 for _ in ast.walk(self.tree)) > LIMITS["ast_nodes"]:
            raise ValueError("Expression exceeds 160 AST nodes")
        self._validate(self.tree.body, 1)

    def _validate(self, node, depth):
        if depth > LIMITS["ast_depth"]:
            raise ValueError("Expression exceeds depth 24")
        if isinstance(node, ast.Constant) and type(node.value) in (int, float):
            exact(ast.get_source_segment(self.source, node))
        elif isinstance(node, ast.Name) and node.id in (*self.variables, "pi"):
            pass
        elif isinstance(node, ast.UnaryOp) and isinstance(node.op, (ast.UAdd, ast.USub)):
            self._validate(node.operand, depth + 1)
        elif isinstance(node, ast.BinOp) and isinstance(node.op, (ast.Add, ast.Sub, ast.Mult,
                                                                ast.Div, ast.Pow)):
            self._validate(node.left, depth + 1)
            self._validate(node.right, depth + 1)
        elif (isinstance(node, ast.Call) and isinstance(node.func, ast.Name)
              and node.func.id in FUNCTIONS and len(node.args) == 1 and not node.keywords):
            self._validate(node.args[0], depth + 1)
        else:
            raise ValueError("Unsupported syntax or name; use arb_capabilities for the language")

    def evaluate(self) -> arb:
        variables = {name: ball(lo) if lo == hi else ball(lo).union(ball(hi))
                     for name, (lo, hi) in self.variables.items()}

        def visit(node):
            if isinstance(node, ast.Constant):
                result = ball(exact(ast.get_source_segment(self.source, node)))
            elif isinstance(node, ast.Name):
                result = arb.pi() if node.id == "pi" else variables[node.id]
            elif isinstance(node, ast.UnaryOp):
                value = visit(node.operand)
                result = -value if isinstance(node.op, ast.USub) else value
            elif isinstance(node, ast.Call):
                value = visit(node.args[0])
                if node.func.id == "exp" and not abs(value) <= 700:
                    raise ValueError("exp argument must lie within [-700, 700]")
                result = abs(value) if node.func.id == "abs" else getattr(value, node.func.id)()
            else:
                left, right = visit(node.left), visit(node.right)
                if isinstance(node.op, ast.Add):
                    result = left + right
                elif isinstance(node.op, ast.Sub):
                    result = left - right
                elif isinstance(node.op, ast.Mult):
                    result = left * right
                elif isinstance(node.op, ast.Div):
                    result = left / right
                else:
                    if not abs(right) <= LIMITS["power_exponent"]:
                        raise ValueError("Power exponent must lie within [-256, 256]")
                    # Integer powers also work on negative bases and intervals through zero.
                    integer = (right.is_exact() and right.fmpq().denominator == 1)
                    if not integer and not left > 0:
                        raise UnresolvedInterval("A noninteger power requires a positive base")
                    result = left ** (int(right.fmpq()) if integer else right)
            return bounded(result)

        return visit(self.tree.body)


def evaluate(source: str, variables: dict | None = None, *, bits: int = 128) -> dict:
    precision(bits)
    expression = Expression(source, variables)
    with ctx.workprec(bits):
        try:
            value = expression.evaluate()
            return {"status": "enclosed", "enclosure": enclosure(value), "precision_bits": bits}
        except UnresolvedInterval as exc:
            return {"status": "unresolved", "enclosure": None, "precision_bits": bits,
                    "reason": str(exc)}


def relation_value(gap: arb, relation: str) -> bool | None:
    """Tri-state decision about left-right, including closed inequality endpoints."""
    if relation not in RELATIONS:
        raise ValueError("Unknown comparison relation")
    yes, no = {"<": (gap < 0, gap >= 0), "<=": (gap <= 0, gap > 0),
               ">": (gap > 0, gap <= 0), ">=": (gap >= 0, gap < 0),
               "==": (gap == 0, gap < 0 or gap > 0),
               "!=": (gap < 0 or gap > 0, gap == 0)}[relation]
    return True if yes else False if no else None


def compare(left: str, right: str, relation: str = ">", variables: dict | None = None,
            *, bits: int = 128, max_bits: int = 4096) -> dict:
    precision(bits, max_bits)
    if relation not in RELATIONS:
        raise ValueError("Unknown comparison relation")
    lhs, rhs = Expression(left, variables), Expression(right, variables)
    attempts = []
    while True:
        attempts.append(bits)
        with ctx.workprec(bits):
            decision, evidence = None, None
            reason = "Enclosures overlap; precision or interval dependency prevents a decision"
            try:
                gap = bounded(lhs.evaluate() - rhs.evaluate())
                evidence = enclosure(gap)
                decision = relation_value(gap, relation)
            except UnresolvedInterval as exc:
                reason = str(exc)
            if decision is not None or bits == max_bits:
                result = {"status": "certified" if decision is not None else "unresolved",
                          "holds": decision, "difference": evidence, "precision_bits": bits,
                          "attempted_bits": attempts, "relation": relation,
                          "quantifier": "Decision and its negation are uniform over the input box"}
                if decision is None:
                    result["reason"] = reason
                return result
        bits = min(2 * bits, max_bits)
