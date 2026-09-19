"""Paper C's production equation: the Lean constants must give the roots the manuscript prints.

Theorem 1 fixes the exponent as the root of

    2^(-L) + (1/9)(3/8)^L + (2/9)(3/4)^L + sum_{k=2..6} 3^(-(k+1)) ((1/2)(3/4)^k)^L = 1,

and the manuscript prints that root and five truncations of it.  The same eight pairs are
`productionRate` and `productionCoeff` in `Problems/Juggler/FateContagionBound.lean`.  Nothing
connected the two: the Lean carried eight bare numerals and the manuscript carried six decimals,
and either could have drifted from the other silently.

These tests read the constants out of the Lean source, build the equation from them, and check
the roots against the decimals the manuscript prints.  A changed numeral in Lean, or a changed
decimal in the paper, fails here.

They also pin the two comparison values Section 5 names, because those are what make the
exponent legible: the sweep alone gives 0.138, and perfect fiber equidistribution at depth two
gives 0.4927, "the ceiling of the depth-two method".  The laboratory's own unconditional Lean
certificate sits at the worst-case share and reaches 0.326121, which is why 13/40 is its
ceiling.  The gap from 0.326 to 0.4926 is the distance from the guaranteed parity share 1/3 to
the average share 1/2; the gap from 0.4926 to 0.4927 is all that the block-average family and
the six-word ladder leave on the table, which is 0.000086.  Going past 0.4927 needs depth three,
not better depth-two constants.
"""
from __future__ import annotations

import io
import re
from fractions import Fraction
from pathlib import Path

import pytest
from mpmath import findroot, mp, mpf, power

ROOT = Path(__file__).resolve().parents[3]
LEAN = ROOT / "formal" / "Problems" / "Juggler" / "FateContagionBound.lean"
PAPER = ROOT / "docs" / "theory" / "juggler_fate_almost_all_note.md"

mp.dps = 30


def lean_table(name: str) -> list[Fraction]:
    """The eight branches of a `Fin 8 → ℝ` definition, in index order."""
    src = io.open(LEAN, encoding="utf-8").read()
    start = src.index(f"noncomputable def {name} : Fin 8 → ℝ")
    body = src[start : src.index("\n\n", start)]
    rows = dict(re.findall(r"\|\s*(\d)\s*=>\s*([0-9]+(?:\s*/\s*[0-9]+)?)", body))
    assert len(rows) == 8, (name, sorted(rows))
    return [Fraction(rows[str(i)].replace(" ", "")) for i in range(8)]


def root(pairs: list[tuple[Fraction, Fraction]], guess: str = "0.45") -> float:
    """The root of `sum c_i e_i^L = 1`."""
    def f(lam):
        return sum(mpf(c.numerator) / c.denominator *
                   power(mpf(e.numerator) / e.denominator, lam) for c, e in pairs) - 1
    return float(findroot(f, mpf(guess)))


def pairs() -> list[tuple[Fraction, Fraction]]:
    return list(zip(lean_table("productionCoeff"), lean_table("productionRate")))


def test_the_lean_constants_are_the_paper_s_eight_productions() -> None:
    """Three from (5.2), five from the ladder (5.10), with the closed forms of Theorem 1."""
    coeff, rate = lean_table("productionCoeff"), lean_table("productionRate")
    assert (coeff[0], rate[0]) == (Fraction(1), Fraction(1, 2))
    assert (coeff[1], rate[1]) == (Fraction(1, 9), Fraction(3, 8))
    assert (coeff[2], rate[2]) == (Fraction(2, 9), Fraction(3, 4))
    for k in range(2, 7):
        i = k + 1
        assert rate[i] == Fraction(1, 2) * Fraction(3, 4) ** k, (k, rate[i])
        assert coeff[i] == Fraction(3) ** (-(k + 1)), (k, coeff[i])


def test_the_ladder_coefficients_are_the_increments_of_5_9() -> None:
    """`c_k - (2/9) c_{k-1} = 3^{-(k+1)}` with `c_k = 3^{-k}`: inclusion-exclusion against the
    depth-two `OE` family, which has already counted the `V_k`-starts.  The Lean statement is
    `productionCoeff_ladder`."""
    coeff = lean_table("productionCoeff")
    for k in range(2, 7):
        increment = Fraction(3) ** (-k) - Fraction(2, 9) * Fraction(3) ** (-(k - 1))
        assert coeff[k + 1] == increment == Fraction(3) ** (-(k + 1)), k


@pytest.mark.parametrize("n_terms,printed,label", [
    (3, "0.4480", "pairing only"),
    (4, "0.4801", "OEOEE truncation"),
    (5, "0.4891", "V_3 truncation"),
    (6, "0.4916", "V_4 truncation"),
    (7, "0.4924", "V_5 truncation"),
    (8, "0.4926", "lambda**"),
])
def test_each_printed_root_comes_out_of_the_lean_constants(n_terms: int, printed: str,
                                                            label: str) -> None:
    """Every decimal Theorem 1 and Section 5 print, rebuilt from the Lean table."""
    assert f"{root(pairs()[:n_terms]):.4f}" == printed, label
    assert printed in io.open(PAPER, encoding="utf-8").read(), (printed, label)


def test_the_two_comparison_values_section_5_names() -> None:
    """The sweep alone, and perfect depth-two equidistribution: 0.138 and 0.4927."""
    half = (Fraction(1), Fraction(1, 2))
    assert f"{root([half, (Fraction(2, 21), Fraction(3, 4))], '0.14'):.3f}" == "0.138"
    assert f"{root([half, (Fraction(1, 3), Fraction(3, 4))], '0.49'):.4f}" == "0.4927"


def test_the_unconditional_certificate_sits_at_the_worst_case_share() -> None:
    """Two productions with the guaranteed share `2/9` give `0.326121`, so `13/40` is its ceiling.

    `2/9 = (2/3)(1/3)` is the fiber size times the *guaranteed* parity share of Lemma 4.2;
    `1/3 = (2/3)(1/2)` would be the *average* share of Corollary 4.6(1).  That single factor of
    `3/2` is the whole distance from the unconditional exponent to the depth-two ceiling.
    """
    half = (Fraction(1), Fraction(1, 2))
    worst = root([half, (Fraction(2, 9), Fraction(3, 4))], "0.33")
    assert f"{worst:.6f}" == "0.326121"
    assert Fraction(13, 40) < Fraction(326121, 1000000)


def test_the_full_ladder_does_not_pass_the_depth_two_ceiling() -> None:
    """`lambda** < lambda_ideal`, by `0.000086`: the ladder recovers the ideal share and stops.

    This is the reason improving the `2/9` cannot help much, and the reason going further needs
    depth three rather than better depth-two constants.
    """
    half = (Fraction(1), Fraction(1, 2))
    ideal = root([half, (Fraction(1, 3), Fraction(3, 4))], "0.49")
    assert 0 < ideal - root(pairs()) < 1e-4
