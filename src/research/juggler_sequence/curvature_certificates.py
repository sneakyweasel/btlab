"""Certified one-signedness of the two new curvatures on the depth-five critical path.

Lemma E7 (``OOEOE``, ``j = 0``) and Lemma E5 (``OOOEE``, ``k = 0``, ``j = 0``) each
rest on a curvature whose leading constant only barely avoids zero:
``-(1701/4096) k d x^(-21/16)`` for E7 and ``(243/4096) l d x^(-21/16)`` for E5.
This module does two things.

1. It re-derives both constants exactly with SymPy, as limits of the exact second
   derivative.
2. It certifies with Arb (python-flint) that the full curvature, including every
   correction the lemmas charge, keeps its sign on a stated range.

Write ``u = 2d/x`` and ``g(a, u) = ((1+u)^a - 1)/u``. Then each curvature,
divided by its scale, is an exact combination ``sum_j c_j g(a_j, u)``. Taylor's
theorem with Lagrange remainder encloses ``g(a, u)`` for ``u`` in ``[0, u_0]`` as
``a + (a(a-1)/2) [0, u_0]``, because ``(1+xi)^(a-2) <= 1`` for ``a < 2``. The
corrections are bounded by explicit decreasing powers of ``x``, so an enclosure
at ``x = X`` holds for every ``x >= X``. The corrections are:

- E7: the frozen carry `B'' (S - Q)`, with `|S - Q| <= 1`; the `i`-term; the
  `l`-term;
- E5: the `O(1)` error in the frozen centre `N`, with `|N - B| <= 2`; the modes
  `|i/2 + r| <= C/2 + x^(1/8)`.

All inputs are exact rationals, and the certificate reports ``holds = None``
whenever an enclosure straddles zero. This certifies a finite real inequality; it
does not prove the lemmas' exponential-sum steps.
"""

from __future__ import annotations

import json
from fractions import Fraction
from pathlib import Path

from flint import arb, ctx

from research.experiments.outputs import artifact_path
from research.experiments.provenance import write_manifest
from research.juggler_sequence.lean_paths import DATA_ROOT

DATA_DIR = DATA_ROOT / "depth_five_production" / "curvature_certificates"
PREC = 256
U0 = Fraction(1, 10 ** 6)          # covers 2d/x for d <= x^(1/48), x >= 10^8
FREQUENCY_BOUNDS = (1, 10, 100)

#: Exact decompositions sum_j c_j g(a_j, u) of each curvature over its scale.
E7_TERMS = ((Fraction(297, 256), Fraction(-5, 16)),
            (Fraction(-243, 128), Fraction(1, 8)),
            (Fraction(-27, 128), Fraction(-7, 8)))
E5_TERMS = ((Fraction(297, 256), Fraction(-5, 16)),
            (Fraction(-27, 32), Fraction(-1, 2)))
E7_LEADING = Fraction(-1701, 4096)
E5_LEADING = Fraction(243, 4096)


def _arb(q: Fraction) -> arb:
    return arb(q.numerator) / q.denominator


def g_enclosure(a: Fraction, u0: Fraction = U0) -> arb:
    """Enclosure of ``((1+u)^a - 1)/u`` for every ``u`` in ``(0, u0]``, ``a < 2``."""
    assert a < 2
    spread = a * (a - 1) / 2 * u0
    lo, hi = (a + min(spread, 0), a + max(spread, 0))
    return arb.union(_arb(lo), _arb(hi))


def leading_constants() -> dict:
    """Exact leading constants from the decompositions (rational arithmetic)."""
    return {"E7": str(sum(c * a for c, a in E7_TERMS)),
            "E5": str(sum(c * a for c, a in E5_TERMS))}


def sympy_constants() -> dict:
    """Independent SymPy derivation: limits of the exact second derivatives."""
    import sympy as sp
    x, d, k, l, Q, t, e = sp.symbols("x d k l Q t epsilon", positive=True)
    R = sp.Rational
    S = lambda y: (y + 2 * d) ** R(9, 8) - y ** R(9, 8)
    B = R(3, 4) * k * x ** R(9, 16)
    F = k / 2 * ((x + 2 * d) ** R(27, 16) - x ** R(27, 16)) - B * (S(x) - Q)
    F2 = sp.diff(F, x, 2).subs(Q, S(x))
    e7 = sp.limit(sp.simplify(F2 / (k * d * x ** R(-21, 16))).subs(d, e * x), e, 0)
    N = R(9, 16) * l * x ** R(3, 16)
    psi = l / 2 * sp.diff(t ** R(27, 16), t, 2) - N * sp.diff(t ** R(3, 2), t, 2)
    expr = psi.subs(t, x + 2 * d) - psi.subs(t, x)
    e5 = sp.limit(sp.simplify(expr / (l * d * x ** R(-21, 16))).subs(d, e * x), e, 0)
    return {"E7": str(e7), "E5": str(e5)}


def _pow(X: int, q: Fraction) -> arb:
    return arb(X) ** _arb(q)


def e7_certificate(X: int, C: int) -> dict:
    """Enclose E7's curvature ratio for all ``x >= X``, ``1 <= d``, ``2d/x <= U0``,
    ``k >= 1`` and ``|i|, |l| <= C``."""
    with ctx.workprec(PREC):
        main = sum((_arb(c) * g_enclosure(a) for c, a in E7_TERMS), arb(0))
        err = (arb(189) / 1024 * _pow(X, Fraction(-1, 8))
               + arb(3) / 4 * C * abs(g_enclosure(Fraction(-1, 2))).upper() * _pow(X, Fraction(-3, 16))
               + arb(9) / 64 * C * abs(g_enclosure(Fraction(-7, 8))).upper() * _pow(X, Fraction(-9, 16)))
        total = main + arb(0, err.upper())
        holds = True if total.upper() < 0 else (False if total.lower() > 0 else None)
        return {"X": X, "C": C, "main": main.str(12), "error_radius": err.upper().str(12),
                "lower": total.lower().str(12), "upper": total.upper().str(12), "negative": holds}


def e5_certificate(X: int, C: int) -> dict:
    """Enclose E5's diagonal curvature ratio for all ``x >= X`` in a block
    ``[P, 3P]`` with cutoff ``T <= P^(1/8)``, ``1 <= d``, ``2d/x <= U0``,
    ``|l| >= 1`` and ``|i| <= C``."""
    with ctx.workprec(PREC):
        main = sum((_arb(c) * g_enclosure(a) for c, a in E5_TERMS), arb(0))
        gm = abs(g_enclosure(Fraction(-1, 2))).upper()
        err = (arb(3) * gm * _pow(X, Fraction(-3, 16))
               + arb(3) / 2 * gm * (arb(C) / 2 * _pow(X, Fraction(-3, 16)) + _pow(X, Fraction(-1, 16))))
        total = main + arb(0, err.upper())
        holds = True if total.lower() > 0 else (False if total.upper() < 0 else None)
        return {"X": X, "C": C, "main": main.str(12), "error_radius": err.upper().str(12),
                "lower": total.lower().str(12), "upper": total.upper().str(12), "positive": holds}


def threshold(cert, key: str, C: int, start: int = 8, stop: int = 60) -> int | None:
    """Least ``e`` in ``[start, stop]`` with the certificate at ``X = 10^e`` holding."""
    for e in range(start, stop + 1):
        if cert(10 ** e, C)[key] is True:
            return e
    return None


def table() -> dict:
    return {
        "u0": str(U0), "precision_bits": PREC,
        "leading_constants": leading_constants(), "sympy_constants": sympy_constants(),
        "e7": {str(C): {"threshold_log10_X": threshold(e7_certificate, "negative", C),
                        "at_1e12": e7_certificate(10 ** 12, C)} for C in FREQUENCY_BOUNDS},
        "e5": {str(C): {"threshold_log10_X": threshold(e5_certificate, "positive", C),
                        "at_1e30": e5_certificate(10 ** 30, C)} for C in FREQUENCY_BOUNDS},
    }


def run(output_root: Path | None = None) -> Path:
    out_dir = artifact_path(DATA_DIR, output_root)
    out_dir.mkdir(parents=True, exist_ok=True)
    out = out_dir / "certificates.json"
    out.write_text(json.dumps(table(), indent=1) + "\n", encoding="utf-8", newline="\n")
    return write_manifest(
        out_dir / "run.research.json", programme="juggler",
        research_id="juggler/depth_five_production",
        scope="E5 and E7 curvature ratios for x >= X, 2d/x <= 10^-6, frequencies <= C",
        parameters={"u0": str(U0), "precision_bits": PREC,
                    "frequency_bounds": list(FREQUENCY_BOUNDS)},
        outputs=[out], sources=[Path(__file__)],
    )


if __name__ == "__main__":
    print(run())
