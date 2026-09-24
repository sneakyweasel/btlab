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

from flint import arb, ctx, fmpq

from research_engine.intervals import enclosure, rational


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
    satisfied: bool = False

    @property
    def complete(self) -> bool:
        """The requested count or stopping condition was reached, or the expansion ended."""
        return self.terminated or self.satisfied or len(self.quotients) == self.requested

    def as_dict(self) -> dict:
        return {"status": "certified" if self.complete else "unresolved",
                "quotients": [str(a) for a in self.quotients],
                "certified_terms": len(self.quotients), "requested_terms": self.requested,
                "terminated": self.terminated, "precision_bits": self.precision_bits,
                "attempted_bits": list(self.attempted_bits), "reason": self.reason}


Until = Callable[[list[int]], bool]


def _expand(x: arb, terms: int, until: Until | None
            ) -> tuple[list[int], bool, str | None, bool]:
    found: list[int] = []
    while len(found) < terms:
        if not x.is_finite():
            return found, False, f"Nonfinite enclosure at term {len(found)}", False
        a = x.floor().unique_fmpz()
        if a is None:
            return (found, False, f"Floor of the enclosure is not one integer at term {len(found)}",
                    False)
        found.append(int(a))
        if until is not None and until(found):
            return found, False, None, True
        rest = x - a
        if rest.is_zero():
            return found, True, None, False
        if rest.contains(0):
            return found, False, (f"Remainder after term {len(found) - 1} encloses zero: "
                                  "the value may be rational here, or precision is exhausted"), False
        x = 1 / rest
    return found, False, None, False


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
    return _certified(evaluate, terms, None, bits, max_bits)


def _check_precision(bits: int, max_bits: int) -> None:
    if type(bits) is not int or type(max_bits) is not int or not 2 <= bits <= max_bits:
        raise ValueError("Require integer precision 2 <= bits <= max_bits")


def _certified(evaluate: Callable[[], arb], terms: int, until: Until | None, bits: int,
               max_bits: int) -> Expansion:
    if type(terms) is not int or terms < 1:
        raise ValueError("Require a positive integer number of terms")
    _check_precision(bits, max_bits)
    attempts: list[int] = []
    best: tuple[list[int], bool, str | None, bool] = ([], False, None, False)
    best_bits = bits
    while True:
        attempts.append(bits)
        with ctx.workprec(bits):
            found, terminated, reason, satisfied = _expand(evaluate(), terms, until)
        shorter, longer = sorted((found, best[0]), key=len)
        if longer[:len(shorter)] != shorter:
            raise ArithmeticError("Certified prefixes disagree between precisions")
        if len(found) >= len(best[0]):
            best, best_bits = (found, terminated, reason, satisfied), bits
        if terminated or satisfied or len(found) == terms or bits == max_bits:
            break
        bits = min(2 * bits, max_bits)
    found, terminated, reason, satisfied = best
    return Expansion(tuple(found), terms, terminated, best_bits, tuple(attempts), reason,
                     satisfied)


def _fibonacci_index_above(bound: int) -> int:
    """Least n with F(n) > bound; q_n >= F(n+1) bounds how many terms reach it."""
    a, b, n = 0, 1, 1
    while b <= bound:
        a, b, n = b, a + b, n + 1
    return n


def partial_quotients_past(evaluate: Callable[[], arb], max_denominator: int, *,
                           bits: int = 128, max_bits: int = 4096) -> Expansion:
    """Certified quotients up to the first convergent whose denominator exceeds the bound.

    `complete` means that convergent was reached, or the expansion ended first
    (an exact integer). Otherwise the prefix is certified but stops short of
    the bound, and callers must not treat it as covering every q <= bound.
    """
    if type(max_denominator) is not int or max_denominator < 1:
        raise ValueError("max_denominator must be a positive integer")
    return _certified(evaluate, _fibonacci_index_above(max_denominator) + 2,
                      lambda found: convergents(found)[-1][1] > max_denominator,
                      bits, max_bits)


def best_approximations(evaluate: Callable[[], arb], max_denominator: int,
                        tau: int | str | Fraction = 0, *, bits: int = 128,
                        max_bits: int = 4096) -> dict:
    """Certify min over 1 <= q <= Q of q**tau * ||q alpha||, with every convergent up to Q.

    For tau >= 0 the minimum is attained at a convergent denominator: if
    q_n <= q < q_{n+1} then ||q alpha|| >= ||q_n alpha|| (convergents are the best
    approximations of the second kind; Khinchin, Continued Fractions, Theorems
    16-17) and q**tau >= q_n**tau. When a_1 = 1 the convergents p_0/q_0 and
    p_1/q_1 share q = 1, and only the nearer one, p_1, gives ||alpha||.

    The result is a finite-range statement. It bounds from above every valid
    constant c in |q alpha - p| >= c q**(-tau), and certifies nothing for q > Q.
    Distances are recomputed from `evaluate` at doubling precision until each is
    certainly positive or exactly zero; otherwise the status is unresolved.
    """
    exponent = rational(tau)
    if exponent < 0:
        raise ValueError("tau must be nonnegative")
    _check_precision(bits, max_bits)
    expansion = partial_quotients_past(evaluate, max_denominator, bits=bits, max_bits=max_bits)
    base = {"max_denominator": str(max_denominator), "tau": str(exponent),
            "quotients": [str(a) for a in expansion.quotients],
            "expansion_bits": list(expansion.attempted_bits)}
    if not (expansion.satisfied or expansion.terminated):
        return {**base, "status": "unresolved",
                "reason": expansion.reason or "Continued fraction did not pass max_denominator"}
    fractions = convergents(expansion.quotients)
    rows = [(n, p, q) for n, (p, q) in enumerate(fractions) if q <= max_denominator]
    if len(fractions) > 1 and fractions[1][1] == 1:
        rows = rows[1:]
    attempts: list[int] = []
    while True:
        attempts.append(bits)
        with ctx.workprec(bits):
            alpha = evaluate()
            signed = [q * alpha - p for _, p, q in rows]
            if all(s.is_zero() or s > 0 or s < 0 for s in signed):
                weights = [arb(q) ** arb(fmpq(exponent.numerator, exponent.denominator))
                           for _, _, q in rows]
                entries = []
                for (n, p, q), s, w in zip(rows, signed, weights):
                    distance = abs(s)
                    entries.append({"n": n, "p": str(p), "q": str(q),
                                    "side": "exact" if s.is_zero() else "below" if s > 0 else "above",
                                    "distance": enclosure(distance),
                                    "weighted": enclosure(w * distance)})
                break
        if bits == max_bits:
            return {**base, "status": "unresolved", "precision_bits": bits,
                    "attempted_bits": attempts,
                    "reason": "A convergent distance still encloses zero at max_bits"}
        bits = min(2 * bits, max_bits)
    lower = min(Fraction(e["weighted"]["lower"]) for e in entries)
    upper = min(Fraction(e["weighted"]["upper"]) for e in entries)
    attained = [e["q"] for e in entries if Fraction(e["weighted"]["lower"]) <= upper]
    return {**base, "status": "certified", "convergents": entries,
            "minimum": {"lower": str(lower), "upper": str(upper)}, "attained_at": attained,
            "precision_bits": bits, "attempted_bits": attempts,
            "scope": "Minimum over 1 <= q <= max_denominator only; nothing is certified "
                     "for larger q."}
