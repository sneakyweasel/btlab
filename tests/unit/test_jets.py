"""Integer jets, function jets, locality, CLI."""

from __future__ import annotations

import io
from contextlib import redirect_stdout

from cli.main import main
from bt.calculus.jets import (
    function_jet_of_integer,
    integer_jet,
    output_prefix_depends_on_input_prefix,
    reconstruct_along_jet,
    reconstruction_holds,
    residual_argument,
)
from bt.calculus.jet_locality import profile_jet, profile_standard, same_index_locality
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


def test_same_index_locality_fails_for_square():
    f = parse_poly("x^2")
    found = False
    for n in range(-30, 31):
        if not same_index_locality(f, n, 2):
            found = True
            break
    assert found


def test_state_profiles_finite_at_fixed_k():
    rows = profile_standard(3)
    assert len(rows) == 8
    lin = profile_jet(parse_poly("x"), 4)
    assert lin.raw_states == 1
    sq = profile_jet(parse_poly("x^2"), 3)
    assert sq.raw_states >= 1
    assert sq.max_degree == 2
    assert sq.lc_abs >= 1


def test_calculus_jet_cli():
    def _run(*args: str) -> str:
        buf = io.StringIO()
        with redirect_stdout(buf):
            code = main(["--include-archive", "calculus", *args])
        assert code == 0
        return buf.getvalue()

    sd = _run("section-deriv", "x^2", "--section", "1")
    assert "D_a f" in sd
    nd = _run("normalized-deriv", "2")
    assert "hatD" in nd
    assert "D_coeff" in nd
    j = _run("jet", "5", "--depth", "3")
    assert "J_3" in j
    fj = _run("function-jet", "x^2", "5", "--depth", "2")
    assert "reconstruction = True" in fj
    st = _run("states", "x", "--depth", "3")
    assert "raw =" in st
    cj = _run("compare-jets", "x", "x^2", "--depth", "2", "--n", "4")
    assert "f output" in cj
