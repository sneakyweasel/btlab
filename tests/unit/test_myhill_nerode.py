"""Exact finite-horizon Myhill–Nerode residual automata."""

from __future__ import annotations

import io
from contextlib import redirect_stdout
from itertools import product

from cli.main import main
from bt.calculus.automata import profile_states, trie_count
from bt.calculus.composition import (
    cascade_state_bound,
    negation_rho_delta,
    output_cascade_holds,
    profile_composition,
)
from bt.calculus.jet_locality import minimized_count
from bt.calculus.myhill_nerode import (
    distinguish_pair,
    equiv_by_outputs,
    equiv_recursive,
    merge_examples,
    myhill_nerode_count,
    raw_count,
    semantic_count,
)
from bt.calculus.quadratic import (
    canonical_distinguishing_word,
    coeff_triple,
    quadratic_residual_formula,
    residual_formula_table,
    section_coeff_step,
)
from bt.calculus.residual import residual_along
from bt.calculus.normalizer_compose import (
    hatD_is_normalize_then_drop,
    hatD_state_upper_bound,
    profile_compose_normalizer,
    profile_hatD,
)
from bt.calculus.section import parse_poly
from bt.normtheory.coeffword import CoeffWord
from bt.normtheory.hatd import hatD, milestone14_witness


def test_equiv_recursive_matches_outputs():
    f = parse_poly("x^2")
    g = parse_poly("3x^2")
    h = parse_poly("x^2")
    for k in range(0, 4):
        assert equiv_recursive(f, h, k)
        assert equiv_recursive(f, g, k) == equiv_by_outputs(f, g, k)
        assert not equiv_recursive(f, g, 1)


def test_raw_semantic_coincide():
    f = parse_poly("x^3")
    for k in range(0, 5):
        assert raw_count(f, k) == semantic_count(f, k)


def test_affine_mn_stabilizes():
    assert myhill_nerode_count(parse_poly("x"), 6) == 1
    assert myhill_nerode_count(parse_poly("x+1"), 6) == 2
    assert myhill_nerode_count(parse_poly("2x+1"), 6) == 3
    assert myhill_nerode_count(parse_poly("3x+1"), 6) == 3


def test_quadratic_closed_form():
    from bt.calculus.section import parse_poly

    f = parse_poly("x^2")
    for word in product((-1, 0, 1), repeat=3):
        got = residual_along(f, word)
        closed = quadratic_residual_formula(word)
        assert got.coeffs == closed.coeffs
        A, B, C = coeff_triple(got)
        a = word[-1]
        prefix = quadratic_residual_formula(word[:-1])
        pA, pB, pC = coeff_triple(prefix)
        assert section_coeff_step(pA, pB, pC, a) == (A, B, C)
    rows = residual_formula_table(f, 3)
    assert all(row["closed_x2"] for row in rows)
    rec = distinguish_pair(parse_poly("x^2"), parse_poly("3x^2"), 2)
    assert rec["equiv"] is False
    assert rec["canonical"] is not None
    assert canonical_distinguishing_word(parse_poly("x^2"), parse_poly("3x^2"), 1) == (1,)
    assert merge_examples(f, 4) == []


def test_x2_no_finite_horizon_collapse():
    f = parse_poly("x^2")
    for k in range(0, 6):
        r = raw_count(f, k)
        m = myhill_nerode_count(f, k)
        assert r == m
        if k == 0:
            assert r == 1
        else:
            assert r == (3**k - 1) // 2


def test_sample_is_not_myhill_nerode():
    f = parse_poly("x^2")
    sample = minimized_count(f, 3)
    mn = myhill_nerode_count(f, 3)
    assert sample == 7
    assert mn == 13
    assert sample != mn


def test_x3_does_collapse():
    f = parse_poly("x^3")
    assert raw_count(f, 4) == 40
    assert myhill_nerode_count(f, 4) == 36
    assert myhill_nerode_count(f, 4) < raw_count(f, 4)


def test_prefix_locality_not_small_automaton():
    f = parse_poly("x^2")
    rec = profile_states(f, 4)
    assert rec.trie == trie_count(4)
    assert rec.myhill_nerode == rec.raw
    assert rec.compression is not None
    assert rec.compression < 3**4


def test_cascade_outputs_and_bound():
    f = parse_poly("x^2")
    g = parse_poly("x+1")
    for w in product((-1, 0, 1), repeat=3):
        assert output_cascade_holds(f, g, w)
    rec = profile_composition(f, g, 4)
    assert rec.M_fog <= cascade_state_bound(f, g, 4)
    rec4 = profile_composition(parse_poly("x^2"), parse_poly("x^2"), 4)
    assert rec4.M_fog == myhill_nerode_count(parse_poly("x^4"), 4)
    assert rec4.M_fog < rec4.naive_product


def test_negation_symmetry():
    for s in ("x", "x^2", "x^3", "2x+1"):
        f = parse_poly(s)
        for a in (-1, 0, 1):
            assert negation_rho_delta(f, a)


def test_normalizer_obstruction_and_hatd():
    rec = profile_compose_normalizer(parse_poly("x^2"), 4, B=5)
    assert rec.max_coeff > 5
    assert rec.representable is False
    aff = profile_compose_normalizer(parse_poly("x"), 6, B=1)
    assert aff.representable is True
    w = milestone14_witness()
    assert hatD(w).value() == 1
    assert hatD_is_normalize_then_drop(CoeffWord((2,)))
    assert hatD_state_upper_bound(5) == 2 * (2 * 5 + 1)
    hd = profile_hatD(5)
    assert hd.carry_states == 11
    assert hd.witness_two is True


def test_calculus_mn_cli():
    def _run(*args: str) -> str:
        buf = io.StringIO()
        with redirect_stdout(buf):
            code = main(["--include-archive", "calculus", *args])
        assert code == 0
        return buf.getvalue()

    st = _run("states", "x", "--depth", "3")
    assert "raw =" in st
    assert "Myhill-Nerode =" in st
    assert "sample =" in st
    mn = _run("minimize", "x^2", "--depth", "3")
    assert "Myhill-Nerode = 13" in mn
    assert "sample = 7" in mn
    dist = _run("distinguish", "x^2", "--depth", "2")
    assert "word=" in dist
    co = _run("compose", "x^2", "x+1", "--depth", "3")
    assert "M_fog =" in co
    cn = _run("compose-normalizer", "x^2", "--depth", "3", "--bound", "2")
    assert "representable =" in cn
    ps = _run("profile-states", "x", "--max-depth", "3")
    assert "Myhill-Nerode" in ps
    pair = _run("distinguish-pair", "x^2", "3x^2", "--depth", "2")
    assert "shortest =" in pair
    assert "canonical =" in pair
    rf = _run("residual-formula", "x^2", "--depth", "3")
    assert "closed_x2" in rf
    assert "rho_triples =" in rf
    wit = _run("witness", "x^2", "--depth", "2")
    assert "canonical=" in wit
    mg = _run("merge-examples", "x^2", "--depth", "3")
    assert "no merge pair" in mg
    mg3 = _run("merge-examples", "x^3", "--depth", "2")
    assert "split_next=" in mg3
