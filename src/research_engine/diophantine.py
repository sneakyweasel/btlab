"""Continued fractions and rational approximations, independent of either research programme.

Exact rationals expand by Euclid's algorithm. A real number is supplied as a
callback that rebuilds its Arb enclosure at the current precision. A partial
quotient is reported only when the floor of the running enclosure is a single
integer, so every returned term holds for every point the enclosure contains,
including a whole input box. Precision doubles up to a budget; the result says
how many terms were certified and why expansion stopped. Floats are rejected:
a binary double yields sixteen correct terms of log2(3) and then continues
silently with wrong ones.
"""
from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
from typing import Callable, Iterable

from flint import arb, ctx

from research_engine.intervals import rational


def rational_partial_quotients(value: int | str | Fraction) -> list[int]:
    """The finite expansion [a0; a1, ..., an] of an exact rational.

    Euclid's algorithm on the exact numerator and denominator; the last term
    exceeds 1 whenever n >= 1, so the expansion is the canonical one.
    """
    x = rational(value)
    p, q = x.numerator, x.denominator
    terms = []
    while q:
        a = p // q
        terms.append(a)
        p, q = q, p - a * q
    return terms


def _quotients(quotients: Iterable[int]) -> list[int]:
    terms = list(quotients)
    if not terms or any(type(a) is not int for a in terms) or any(a < 1 for a in terms[1:]):
        raise ValueError("Require integer partial quotients with a_n >= 1 for n >= 1")
    return terms


def convergents(quotients: Iterable[int]) -> list[tuple[int, int]]:
    """Convergents p_n/q_n of [a0; a1, ...] as (p, q) pairs, in order."""
    p_prev, q_prev, p, q = 0, 1, 1, 0
    result = []
    for a in _quotients(quotients):
        p_prev, q_prev, p, q = p, q, a * p + p_prev, a * q + q_prev
        result.append((p, q))
    return result


def semiconvergents(quotients: Iterable[int], max_denominator: int | None = None
                    ) -> list[tuple[int, int]]:
    """p0/q0, then (k p_{n-1} + p_{n-2}) / (k q_{n-1} + q_{n-2}) for 1 <= k <= a_n, n >= 1.

    These are all intermediate fractions, in nondecreasing denominator order;
    k = a_n gives the convergent p_n/q_n. No best-approximation condition such
    as k >= a_n/2 is applied. With max_denominator, the list stops at the first
    fraction whose denominator exceeds it.
    """
    terms = _quotients(quotients)
    if max_denominator is not None and (type(max_denominator) is not int or max_denominator < 1):
        raise ValueError("max_denominator must be a positive integer")
    p2, q2, p1, q1 = 1, 0, terms[0], 1
    result = [(p1, q1)]
    for a in terms[1:]:
        for k in range(1, a + 1):
            p, q = k * p1 + p2, k * q1 + q2
            if max_denominator is not None and q > max_denominator:
                return result
            result.append((p, q))
        p2, q2, p1, q1 = p1, q1, p, q
    return result


@dataclass(frozen=True)
class Expansion:
    """Certified leading partial quotients of an enclosed real number."""

    quotients: tuple[int, ...]
    requested: int
    terminated: bool
    precision_bits: int
    attempted_bits: tuple[int, ...]
    reason: str | None

    @property
    def complete(self) -> bool:
        """The requested count was reached, or the expansion provably ended."""
        return self.terminated or len(self.quotients) == self.requested

    def as_dict(self) -> dict:
        return {"status": "certified" if self.complete else "unresolved",
                "quotients": [str(a) for a in self.quotients],
                "certified_terms": len(self.quotients), "requested_terms": self.requested,
                "terminated": self.terminated, "precision_bits": self.precision_bits,
                "attempted_bits": list(self.attempted_bits), "reason": self.reason}


def _expand(x: arb, terms: int) -> tuple[list[int], bool, str | None]:
    found: list[int] = []
    while len(found) < terms:
        if not x.is_finite():
            return found, False, f"Nonfinite enclosure at term {len(found)}"
        a = x.floor().unique_fmpz()
        if a is None:
            return found, False, f"Floor of the enclosure is not one integer at term {len(found)}"
        found.append(int(a))
        rest = x - a
        if rest.is_zero():
            return found, True, None
        if rest.contains(0):
            return found, False, (f"Remainder after term {len(found) - 1} encloses zero: "
                                  "the value may be rational here, or precision is exhausted")
        x = 1 / rest
    return found, False, None


def certified_partial_quotients(evaluate: Callable[[], arb], terms: int, *, bits: int = 128,
                                max_bits: int = 4096) -> Expansion:
    """Rebuild the enclosure at increasing precision until `terms` quotients are certain.

    Construct every rounded quantity inside `evaluate`. Only an exactly
    integral enclosure terminates. Any other rational, dyadic ones included,
    reaches an inexact reciprocal and stays unresolved -- use
    rational_partial_quotients for rationals.
    Results from different precisions must agree on their common prefix;
    disagreement means a broken enclosure and raises instead of choosing one.
    """
    if type(terms) is not int or terms < 1:
        raise ValueError("Require a positive integer number of terms")
    if type(bits) is not int or type(max_bits) is not int or not 2 <= bits <= max_bits:
        raise ValueError("Require integer precision 2 <= bits <= max_bits")
    attempts: list[int] = []
    best: tuple[list[int], bool, str | None] = ([], False, None)
    best_bits = bits
    while True:
        attempts.append(bits)
        with ctx.workprec(bits):
            found, terminated, reason = _expand(evaluate(), terms)
        shorter, longer = sorted((found, best[0]), key=len)
        if longer[:len(shorter)] != shorter:
            raise ArithmeticError("Certified prefixes disagree between precisions")
        if len(found) >= len(best[0]):
            best, best_bits = (found, terminated, reason), bits
        if terminated or len(found) == terms or bits == max_bits:
            break
        bits = min(2 * bits, max_bits)
    found, terminated, reason = best
    return Expansion(tuple(found), terms, terminated, best_bits, tuple(attempts), reason)
