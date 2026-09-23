"""Shared integer and function jets used by the active applications."""

from __future__ import annotations


from bt.calculus.jets import (
    function_jet_of_integer,
    integer_jet,
    output_prefix_depends_on_input_prefix,
    reconstruct_along_jet,
    reconstruction_holds,
    residual_argument,
)
from bt.calculus.section import parse_poly


def test_integer_jet_matches_digits():
    for n in range(-50, 51):
        k = 4
        jet = integer_jet(n, k)
        acc = residual_argument(n, k)
        for b in reversed(jet):
            acc = b + 3 * acc
        assert acc == n


def test_function_jet_reconstruction():
    polys = [parse_poly(s) for s in ("x", "2x+1", "x^2", "x^2+x", "x^3")]
    for f in polys:
        for n in range(-20, 21):
            for k in (0, 1, 2, 3):
                assert reconstruction_holds(f, n, k)
                jet = function_jet_of_integer(f, n, k)
                assert reconstruct_along_jet(jet, residual_argument(n, k)) == f.eval(n)


def test_prefix_locality_polynomials():
    f = parse_poly("x^2")
    for n in range(-15, 16):
        for m in range(-15, 16):
            for k in (1, 2, 3):
                assert output_prefix_depends_on_input_prefix(f, n, m, k)
