"""Small Arb certification primitives, independent of either research programme.

Inputs are exact rationals. Unknown signs are errors, never negative answers.
Precision is scoped, but FLINT's context is global: use separate processes for
parallel calculations that change precision, not concurrent Python threads.
"""
from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
from typing import Callable

from flint import arb, ctx, fmpq


class UnresolvedInterval(ArithmeticError):
    """The precision budget did not establish a finite, definite comparison."""


def rational(value: int | str | Fraction) -> Fraction:
    """Parse an exact input; deliberately reject floats and booleans."""
    if isinstance(value, bool) or not isinstance(value, (int, str, Fraction)):
        raise TypeError("Use an integer, Fraction, or exact decimal/rational string")
    return Fraction(value)


def ball(value: int | str | Fraction) -> arb:
    """Enclose the intended rational at the current working precision."""
    value = rational(value)
    return arb(fmpq(value.numerator, value.denominator))


def bounds(value: arb) -> tuple[Fraction, Fraction]:
    """Outward-rounded endpoints, exported as exact rationals, never floats."""
    if not isinstance(value, arb) or not value.is_finite():
        raise UnresolvedInterval("Expected a finite Arb enclosure")
    return Fraction(str(value.lower().fmpq())), Fraction(str(value.upper().fmpq()))


def enclosure(value: arb) -> dict:
    """A portable enclosure; the decimal display retains its error radius."""
    lo, hi = bounds(value)
    return {"lower": str(lo), "upper": str(hi), "display": value.str(30)}


def sign(value: arb) -> int | None:
    """Return -1/0/+1 only when certain; overlap or nonfinite means unknown."""
    if not isinstance(value, arb) or not value.is_finite():
        return None
    if value > 0:
        return 1
    if value < 0:
        return -1
    if value == 0:
        return 0
    return None


def signed_evaluation(evaluate: Callable[[], arb], *, bits: int = 128,
                      max_bits: int = 4096) -> tuple[int, dict]:
    """Rebuild an expression at increasing precision until its sign is certain.

    Construct all inexact intermediates inside the callback. Reusing an already
    rounded input cannot recover its lost accuracy. Exact zero is distinguished
    from an interval containing zero. Failure raises instead of guessing.
    """
    if type(bits) is not int or type(max_bits) is not int or not 2 <= bits <= max_bits:
        raise ValueError("Require integer precision 2 <= bits <= max_bits")
    while True:
        with ctx.workprec(bits):
            value = evaluate()
            decision = sign(value)
            if decision is not None:
                return decision, {**enclosure(value), "precision_bits": bits}
        if bits == max_bits:
            raise UnresolvedInterval(f"No definite finite sign at {max_bits} bits")
        bits = min(2 * bits, max_bits)


def _terms(terms) -> tuple[tuple[Fraction, Fraction], ...]:
    result = tuple((rational(c), rational(b)) for c, b in terms)
    if not result or any(c <= 0 or not 0 < b < 1 for c, b in result):
        raise ValueError("Require nonempty productions with c > 0 and 0 < base < 1")
    return result


def production_residual(terms, exponent: int | str | Fraction) -> arb:
    """Enclose sum(c * base**exponent) - 1 at the current precision."""
    pairs = _terms(terms)
    lam = ball(exponent)
    return sum((ball(c) * ball(base) ** lam for c, base in pairs), arb(0)) - 1


@dataclass(frozen=True)
class RootBracket:
    """The unique root of a strictly decreasing positive-production sum."""

    lower: Fraction
    upper: Fraction
    lower_residual: dict
    upper_residual: dict

    def as_ball(self) -> arb:
        return ball(self.lower).union(ball(self.upper))

    def as_dict(self) -> dict:
        with ctx.workprec(128):
            display = self.as_ball().str(30)
        return {"lower": str(self.lower), "upper": str(self.upper), "display": display,
                "lower_residual": self.lower_residual,
                "upper_residual": self.upper_residual}


def production_root(terms, *, lower=0, upper=1, digits: int = 24,
                    bits: int = 128, max_bits: int = 4096) -> RootBracket:
    """Certify a unique root in a rational bracket of width <= 10**(-digits).

    Positive coefficients and bases in (0,1) establish strict monotonicity and
    continuity analytically. Endpoint signs establish existence. No derivative
    sampling, unconstrained root finder, or float midpoint enters the certificate.
    """
    pairs = _terms(terms)
    lo, hi = rational(lower), rational(upper)
    if lo >= hi or type(digits) is not int or not 1 <= digits <= 200:
        raise ValueError("Require lower < upper and integer digits in [1, 200]")

    def at(x):
        return signed_evaluation(lambda: production_residual(pairs, x),
                                 bits=bits, max_bits=max_bits)

    slo, elo = at(lo)
    shi, ehi = at(hi)
    if slo < 0 or shi > 0:
        raise ValueError("The endpoints do not bracket a root")
    if slo == 0:
        return RootBracket(lo, lo, elo, elo)
    if shi == 0:
        return RootBracket(hi, hi, ehi, ehi)
    while hi - lo > Fraction(1, 10**digits):
        mid = (lo + hi) / 2
        smid, emid = at(mid)
        if smid == 0:
            return RootBracket(mid, mid, emid, emid)
        if smid > 0:
            lo, elo = mid, emid
        else:
            hi, ehi = mid, emid
    return RootBracket(lo, hi, elo, ehi)
