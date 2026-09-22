"""Polynomial function congruence modulo 3^k."""

from __future__ import annotations

import io
from contextlib import redirect_stdout
from itertools import product

from cli.main import main
from bt.calculus.myhill_nerode import equiv_by_outputs, merge_examples
from bt.calculus.quadratic import pack_word
from bt.calculus.residual import TRITS, residual_along
from bt.calculus.poly_congruence import (
    cubic_vanishes,
    distinguishing_residue,
    first_distinction_horizon,
    function_equiv,
    monomial_valuation,
    newton_coeffs,
    newton_from_monomials,
    newton_valuation,
    phi_equal,
    poly_congruence_report,
    residual_shift,
    tau_leading_bound,
    vanishing_poly,
    vanishes_as_function,
)
from bt.calculus.section import IntPoly, parse_poly


def test_newton_matches_stirling():
    for text in ("x^2", "x^3-x", "2x^4+x", "x^3+9x^2+3x"):
        f = parse_poly(text)
        assert newton_coeffs(f) == newton_from_monomials(f.coeffs)


def test_degree_le_2_is_coeffwise():
    f = parse_poly("9x^2+3x+18")
    assert vanishes_as_function(f, 1)
    assert not vanishes_as_function(f, 2)
    g = parse_poly("18x^2")
    assert vanishes_as_function(g, 2)
    assert not vanishes_as_function(g, 3)
    # Invisible quadratics do not exist.
    rec = vanishing_poly(2, 2)
    assert rec["invisible"] is None


def test_x3_minus_x_is_first_invisible():
    h = parse_poly("x^3-x")
    assert vanishes_as_function(h, 1)
    assert not vanishes_as_function(h, 2)
    assert newton_coeffs(h) == (0, 0, 6, 6)
    assert newton_valuation(h) == 1
    assert monomial_valuation(h) == 0
    rec = vanishing_poly(3, 1)
    assert rec["invisible_coeffs"] == [0, -1, 0, 1]
    rec2 = vanishing_poly(3, 2)
    assert rec2["invisible_coeffs"] == [0, -3, 0, 3]


def test_cubic_criterion():
    assert cubic_vanishes(1, 0, -1, 0, 1)
    assert not cubic_vanishes(1, 0, -1, 0, 2)
    assert cubic_vanishes(3, 0, -3, 0, 2)
    assert not cubic_vanishes(1, 0, 0, 0, 1)


def test_function_equiv_is_myhill_nerode():
    pairs = [
        (parse_poly("x^3"), parse_poly("x"), 1),
        (parse_poly("x^3"), parse_poly("x"), 2),
        (parse_poly("9x^3-9x^2+3x"), parse_poly("9x^3+9x^2+3x"), 2),
        (parse_poly("9x^3-9x^2+3x"), parse_poly("9x^3+9x^2+3x"), 3),
        (parse_poly("27x^4"), parse_poly("729x^4"), 3),
        (parse_poly("27x^4"), parse_poly("729x^4"), 4),
        (parse_poly("x^2"), parse_poly("3x^2"), 1),
    ]
    for f, g, k in pairs:
        assert function_equiv(f, g, k) == equiv_by_outputs(f, g, k)


def test_x3_first_merge_via_invariant():
    f = residual_along(parse_poly("x^3"), (-1,))
    g = residual_along(parse_poly("x^3"), (1,))
    assert f.render() == "3x - 9x^2 + 9x^3"
    assert g.render() == "3x + 9x^2 + 9x^3"
    assert function_equiv(f, g, 2)
    assert not function_equiv(f, g, 3)
    assert first_distinction_horizon(f, g) == 3
    h = f.sub(g)
    assert h.coeffs == (0, 0, -18)
    assert newton_valuation(h) == 2
    assert distinguishing_residue(f, g, 3) is not None


def test_x4_first_merge_via_invariant():
    f = residual_along(parse_poly("x^4"), (0,))
    g = residual_along(parse_poly("x^4"), (0, 0))
    assert f.coeffs == (0, 0, 0, 0, 27)
    assert g.coeffs == (0, 0, 0, 0, 729)
    assert function_equiv(f, g, 3)
    assert not function_equiv(f, g, 4)
    assert first_distinction_horizon(f, g) == 4
    assert newton_valuation(f.sub(g)) == 3


def test_tau_formula_and_bound():
    h = parse_poly("x^3-x")
    z = IntPoly((0,))
    assert first_distinction_horizon(h, z) == 2
    assert tau_leading_bound(h) == 2
    eighteen = parse_poly("-18x^2")
    assert first_distinction_horizon(eighteen, z) == 3
    assert tau_leading_bound(eighteen) == 3
    # Coefficient min-valuation is not τ − 1.
    assert monomial_valuation(h) == 0
    assert newton_valuation(h) == 1


def test_x3_x4_merge_dataset_tau():
    rows3 = merge_examples(parse_poly("x^3"), 2, limit=4)
    assert rows3
    f = parse_poly(rows3[0]["p"])
    g = parse_poly(rows3[0]["q"])
    assert first_distinction_horizon(f, g) == 3
    rows4 = merge_examples(parse_poly("x^4"), 3, limit=4)
    assert rows4
    p = parse_poly(rows4[0]["p"])
    q = parse_poly(rows4[0]["q"])
    tau = first_distinction_horizon(p, q)
    assert tau is not None and tau >= 4


def test_phi_complete_on_small_box():
    polys = [
        parse_poly("x^3"),
        parse_poly("x"),
        parse_poly("x^3-x"),
        parse_poly("3x^3-3x"),
        parse_poly("x^2+x+1"),
        parse_poly("27x^4"),
        parse_poly("729x^4"),
    ]
    for k in range(0, 4):
        for i, f in enumerate(polys):
            for g in polys[i + 1 :]:
                assert phi_equal(f, g, k) == function_equiv(f, g, k)


def test_poly_congruence_cli():
    def _run(*args: str) -> str:
        buf = io.StringIO()
        with redirect_stdout(buf):
            code = main(["--include-archive", "calculus", *args])
        assert code == 0
        return buf.getvalue()

    yes = _run("poly-congruence", "9x^3-9x^2+3x", "9x^3+9x^2+3x", "--k", "2")
    assert "YES" in yes
    assert "finite-difference profile" in yes
    no = _run("poly-congruence", "9x^3-9x^2+3x", "9x^3+9x^2+3x", "--k", "3")
    assert "NO" in no
    assert "probe" in no
    vp = _run("vanishing-poly", "3", "--k", "1")
    assert "[0, -1, 0, 1]" in vp or "x^3" in vp
    vp2 = _run("vanishing-poly", "2", "--k", "2")
    assert "none" in vp2


def test_report_fields():
    rec = poly_congruence_report(parse_poly("x^3"), parse_poly("x"), 1)
    assert rec["equivalent"] is True
    assert rec["phi_f"] == rec["phi_g"]
    rec2 = poly_congruence_report(parse_poly("x^3"), parse_poly("x"), 2)
    assert rec2["equivalent"] is False
    assert rec2["probe"] is not None


def test_residual_shift_matches_residual_along():
    for text in ("x^2", "x^3", "x^3-x", "x^4+2x", "x^5-x"):
        f = parse_poly(text)
        for m in range(3):
            for word in product(TRITS, repeat=m):
                p = pack_word(word)
                assert residual_shift(f, m, p) == residual_along(f, word)
