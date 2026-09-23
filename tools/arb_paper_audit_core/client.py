"""MCP evidence capture and exact rational interval bookkeeping; no local Arb calls."""
from __future__ import annotations

import asyncio
from dataclasses import dataclass
from fractions import Fraction as F


@dataclass(frozen=True)
class Bounds:
    lo: F
    hi: F

    def __post_init__(self):
        if self.lo > self.hi:
            raise ValueError("Reversed bounds")

    @classmethod
    def read(cls, item):
        return cls(F(item["lower"]), F(item["upper"]))

    def as_dict(self):
        return {"lower": str(self.lo), "upper": str(self.hi)}

    def box(self, digits=48):
        """Round outwards to bounded exact decimal strings accepted by the MCP."""
        scale = 10**digits
        low, high = self.lo * scale, self.hi * scale
        integers = (low.numerator // low.denominator, -((-high.numerator) // high.denominator))
        def decimal(n):
            sign = "-" if n < 0 else ""
            n = abs(n)
            return f"{sign}{n // scale}.{n % scale:0{digits}d}"
        return [decimal(n) for n in integers]

    def __add__(self, other):
        if not isinstance(other, Bounds):
            other = Bounds(F(other), F(other))
        return Bounds(self.lo + other.lo, self.hi + other.hi)

    def __sub__(self, other):
        if not isinstance(other, Bounds):
            other = Bounds(F(other), F(other))
        return Bounds(self.lo - other.hi, self.hi - other.lo)

    def __mul__(self, other):
        if not isinstance(other, Bounds):
            other = Bounds(F(other), F(other))
        candidates = [x*y for x in (self.lo, self.hi) for y in (other.lo, other.hi)]
        return Bounds(min(candidates), max(candidates))


class Audit:
    def __init__(self, session, semaphore):
        self.session, self.semaphore = session, semaphore
        self.calls = {}

    async def call(self, key, tool, arguments):
        if key in self.calls:
            raise ValueError(f"Duplicate check ID: {key}")
        async with self.semaphore:
            response = await self.session.call_tool(tool, arguments)
        if response.isError or not response.structuredContent:
            raise ArithmeticError(f"{key}: {response.content}")
        result = response.structuredContent
        if result.get("status") == "unresolved":
            raise ArithmeticError(f"{key}: unresolved: {result}")
        self.calls[key] = {"tool": tool, "arguments": arguments, "result": result}
        return result

    async def evaluate(self, key, expression, variables=None, bits=256):
        result = await self.call(key, "arb_evaluate", {"expression": expression,
                                    "variables": variables, "bits": bits})
        if result["status"] != "enclosed":
            raise ArithmeticError(f"{key}: no finite enclosure")
        return Bounds.read(result["enclosure"])

    async def compare(self, key, left, right, relation=">", variables=None, expected=True):
        result = await self.call(key, "arb_compare", {"left": left, "right": right,
                     "relation": relation, "variables": variables, "bits": 256, "max_bits": 1024})
        if result["status"] != "certified" or result["holds"] is not expected:
            raise ArithmeticError(f"{key}: expected {expected}, obtained {result}")
        return result


async def constants(audit):
    names = {"ln2": "log(2)", "ln3": "log(3)", "beta": "log(2)/log(3)",
             "delta": "log(3)/log(2)"}
    values = await asyncio.gather(*(audit.evaluate(name, expr) for name, expr in names.items()))
    return dict(zip(names, values))
