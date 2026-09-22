"""Calculus link, Setun subset, discovery, graphs, CLI."""

from __future__ import annotations

import io
from contextlib import redirect_stdout

from cli.main import main
from bt.calculus.derivative import D
from bt.normtheory.calculus_link import (
    D_coeff,
    D_normalize_words_equal,
    I_coeff,
    I_section_on_coeff,
    S_coeff,
    commute_side_condition,
    integer_I_matches,
)
from bt.normtheory.coeffword import CoeffWord
from bt.normtheory.complexity import enumerate_words
from bt.normtheory.discovery import discover
from bt.normtheory.graph import distance_to_normal_form, geodesic_equals_excess, rewrite_graph
from bt.normtheory.setun_subset import (
    FACTS,
    SKETCHES,
    Add,
    Cmp3,
    Fma,
    Lit,
    Mul,
    Normalize,
    Shift,
    eval_ast,
    label,
)
from bt.normtheory.strategies import normal_form


def test_calculus_link_side_condition():
    fail = CoeffWord((2,))
    assert not commute_side_condition(fail)
    assert not D_normalize_words_equal(fail)
    assert D_coeff(fail).value() == 0
    assert D(normal_form(fail).value()) == 1
    ok = CoeffWord((1, 2, 0))
    assert commute_side_condition(ok)
    assert D_normalize_words_equal(ok)
    assert I_section_on_coeff(-1, ok)
    assert integer_I_matches(1, ok)
    assert S_coeff(CoeffWord((1,))).value() == 3
    assert I_coeff(0, CoeffWord((1,))).coeffs == (0, 1)


def test_setun_subset_eval():
    expr = Add(Lit(2), Mul(Lit(3), Lit(-1)))
    assert eval_ast(expr).value() == 2 + 3 * (-1)
    fma = Fma(Lit(2), Lit(5), Lit(-1))
    assert eval_ast(fma).value() == 9
    assert eval_ast(Shift(Lit(1))).value() == 3
    assert eval_ast(Normalize(Lit(2))).coeffs == (-1, 1)
    assert eval_ast(Cmp3(Lit(1), Lit(4))).coeffs == (-1,)
    assert SKETCHES
    assert FACTS
    assert label("signed trits") == "HISTORICAL FACT"
    assert label("18-trit hardware registers as a universal Setun word size") == "HISTORICAL SKETCH"


def test_discovery_never_proved():
    rows = discover(width=3, bound=2)
    assert rows
    assert all(r.status != "EXACT — HUMAN PROOF" for r in rows)
    names = {r.name for r in rows}
    assert "weighted_l1_alpha_3_2_decreases" in names
    assert "D_normalize_commutes" in names
    weighted = next(r for r in rows if r.name.startswith("weighted"))
    assert weighted.status == "REFUTED"
    dnf = next(r for r in rows if r.name.startswith("D_normalize"))
    assert dnf.status == "REFUTED"


def test_rewrite_graph_and_distance():
    word = CoeffWord((2,))
    g = rewrite_graph(word)
    assert g.distance == 1
    assert g.normal_form.coeffs == (-1, 1)
    assert distance_to_normal_form(CoeffWord((0,))) == 0
    five = CoeffWord((5,))
    assert geodesic_equals_excess(five) is False
    assert five.excess() == 4
    assert distance_to_normal_form(five) == 2


def test_normalize_cli():
    def _run(*args: str) -> str:
        buf = io.StringIO()
        with redirect_stdout(buf):
            code = main(["--include-archive", "normalize", *args])
        assert code == 0
        return buf.getvalue()

    ev = _run("eval", "2")
    assert "value = 2" in ev
    assert "normal form" in ev
    st = _run("step", "2", "0")
    assert "after" in st
    strat = _run("strategies", "2,2")
    assert "A:" in strat and "D:" in strat
    g = _run("graph", "2")
    assert "normal_form" in g
    disc = _run("discover", "--width", "2", "--bound", "2")
    assert "weighted_l1" in disc
    prof = _run("profile", "2,0", "--json")
    assert "rewrite_A" in prof
