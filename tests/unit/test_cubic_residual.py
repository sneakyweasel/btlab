"""Newton-class image of the residual machine of ``x^3``."""

from __future__ import annotations

import io
from contextlib import redirect_stdout
from itertools import product

from cli.main import main
from bt.calculus.cubic import (
    F_k,
    M_k_x3,
    collision_classes,
    cubic_coeffs,
    cubic_residual_formula,
    image_profile,
    newton_from_monomial,
    newton_of_residual,
    newton_section_step,
    newton_section_step_closed,
    raw_count_x3,
    section_monomial_step,
    shallow_lower_bound,
    tau_sign_pair,
)
from bt.calculus.myhill_nerode import myhill_nerode_count
from bt.calculus.poly_congruence import newton_coeffs, phi_equal
from bt.calculus.quadratic import pack_word
from bt.calculus.residual import TRITS, residual_along
from bt.calculus.section import IntPoly, parse_poly


def test_closed_form_matches_residual_along():
    f = parse_poly("x^3")
    for m in range(5):
        for word in product(TRITS, repeat=m):
            assert cubic_residual_formula(word) == residual_along(f, word)


def test_reconstruction_from_shifted_cube():
    from bt.calculus.quadratic import iter_dz

    for m in range(4):
        for word in product(TRITS, repeat=m):
            p = pack_word(word)
            A, B, C, D = cubic_coeffs(m, p)
            # f_w(x) = D^m((p + 3^m x)^3)
            for x in range(-3, 4):
                shifted = (p + 3**m * x) ** 3
                assert A * x**3 + B * x**2 + C * x + D == iter_dz(shifted, m)


def test_newton_of_monomial_matches_table():
    for A, B, C, D in ((1, 0, 0, 0), (9, -9, 3, 0), (9, 9, 3, 0), (81, 27, 12, 1)):
        poly = IntPoly((D, C, B, A))
        assert newton_from_monomial(A, B, C, D) == newton_coeffs(poly)


def test_section_step_matches_section_deriv():
    f = parse_poly("x^3")
    for a in TRITS:
        g = f.section_deriv(a)
        assert section_monomial_step(1, 0, 0, 0, a) == (
            g.coefficient(3),
            g.coefficient(2),
            g.coefficient(1),
            g.coefficient(0),
        )


def test_newton_section_closed_form():
    for m in range(3):
        for word in product(TRITS, repeat=m):
            p = pack_word(word)
            N = newton_of_residual(m, p)
            for a in TRITS:
                Np = newton_section_step(N, a)
                assert Np == newton_section_step_closed(m, p, a)
                assert Np == newton_of_residual(m + 1, p + 3**m * a)
                assert Np[3] == 9 * N[3]
                assert Np[2] == 3 * N[2] + 3 * (a + 2) * N[3]


def test_raw_count_and_injectivity():
    f = parse_poly("x^3")
    seen = set()
    for m in range(5):
        for word in product(TRITS, repeat=m):
            key = residual_along(f, word).coeffs
            assert key not in seen
            seen.add(key)
        assert raw_count_x3(m + 1) == len(seen)


def test_first_merge_is_newton_mod_9():
    n_neg = newton_of_residual(1, -1)
    n_pos = newton_of_residual(1, 1)
    assert F_k(1, -1, 2) == F_k(1, 1, 2)
    assert F_k(1, -1, 3) != F_k(1, 1, 3)
    assert all((a - b) % 9 == 0 for a, b in zip(n_neg, n_pos))
    assert (n_neg[1] - n_pos[1]) % 27 != 0
    f = parse_poly("x^3")
    assert phi_equal(residual_along(f, (-1,)), residual_along(f, (1,)), 2)
    assert not phi_equal(residual_along(f, (-1,)), residual_along(f, (1,)), 3)


def test_image_is_F_k_and_matches_mn_small_k():
    f = parse_poly("x^3")
    expected = {1: 1, 2: 3, 3: 12, 4: 36, 5: 115}
    for k, Mk in expected.items():
        assert M_k_x3(k) == Mk
        assert M_k_x3(k) == len({F_k(m, pack_word(w), k)
                                 for m in range(k)
                                 for w in (product(TRITS, repeat=m) if m else [()])})
        assert M_k_x3(k) == myhill_nerode_count(f, k)
        assert M_k_x3(k) <= raw_count_x3(k)
        assert M_k_x3(k) >= shallow_lower_bound(k)


def test_computed_image_table():
    table = {
        1: (1, 1),
        2: (4, 3),
        3: (13, 12),
        4: (40, 36),
        5: (121, 115),
        6: (364, 349),
        7: (1093, 1074),
        8: (3280, 3231),
        9: (9841, 9780),
        10: (29524, 29394),
    }
    for k, (R, M) in table.items():
        rec = image_profile(k)
        assert rec["R"] == R
        assert rec["M"] == M
        assert rec["collisions"] == R - M


def test_naive_lift_recurrence_fails():
    Ms = [M_k_x3(k) for k in range(1, 6)]
    for i in range(len(Ms) - 1):
        assert Ms[i + 1] != 3 * Ms[i] + 1


def test_collision_not_just_prefix_congruence():
    # Same-depth collisions at k=4 include ±1 and ±2, not a single residue class.
    classes = collision_classes(4)
    packs = [[p for _w, _m, p in members] for members in classes]
    assert any(set(ps) == {-1, 1} for ps in packs)
    assert any(set(ps) == {-2, 2} for ps in packs)
    # Packed-prefix congruence alone does not label the classes.
    assert not all(len({p % 9 for _w, _m, p in members}) == 1 for members in classes)


def test_sign_pair_tau():
    assert tau_sign_pair(1, 1) == 3
    assert tau_sign_pair(2, 1) == 4
    assert tau_sign_pair(3, 2) == 5
    assert tau_sign_pair(1, 0) is None


def test_x4_same_newton_machinery():
    f = parse_poly("x^4")
    zero = residual_along(f, (0,))
    zeros = residual_along(f, (0, 0))
    assert zero.coefficient(4) == 27
    assert zeros.coefficient(4) == 729
    assert phi_equal(zero, zeros, 3)
    assert not phi_equal(zero, zeros, 4)
    n = newton_coeffs(zero.sub(zeros))
    assert min(v for v in (abs(c) for c in n) if v) % 27 == 0 or all(
        c % 27 == 0 for c in n
    )
    assert all(c % 27 == 0 for c in n)
    assert any(c % 81 != 0 for c in n)


def test_newton_class_cli():
    def _run(*args: str) -> str:
        buf = io.StringIO()
        with redirect_stdout(buf):
            code = main(["--include-archive", "calculus", *args])
        assert code == 0
        return buf.getvalue()

    out = _run("newton-class", "x^3", "--k", "2")
    assert "class_id" in out
    assert "newton" in out
    hits = _run("class-collisions", "x^3", "--k", "2")
    assert "collision_classes" in hits
    assert "[-1]" in hits or "-1" in hits
