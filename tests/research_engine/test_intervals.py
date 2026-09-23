"""Certification must distinguish exact truth, rounded overlap, and failure."""
from fractions import Fraction as F

from flint import arb, ctx
import pytest

from research_engine.intervals import (
    UnresolvedInterval, ball, bounds, enclosure, production_root,
    rational, sign, signed_evaluation,
)


@pytest.mark.parametrize("bad", [0.1, True, complex(1, 0), arb(1)])
def test_exact_inputs_reject_accidentally_rounded_values(bad):
    with pytest.raises(TypeError):
        ball(bad)


def test_decimal_and_rational_inputs_enclose_the_intended_value():
    with ctx.workprec(128):
        for text in ("0.1", "1/3", "-1.23456789"):
            lo, hi = bounds(ball(text))
            assert lo <= F(text) <= hi
        assert rational("0.1") == F(1, 10)
        assert not ball("0.1").contains(arb(0.1))


def test_serialized_endpoints_are_outward_and_radius_is_retained():
    with ctx.workprec(160):
        value = arb(2).sqrt()
        data = enclosure(value)
        lo, hi = F(data["lower"]), F(data["upper"])
        assert 0 < lo < hi and lo**2 < 2 < hi**2
        assert "+/-" in data["display"]
        assert arb(data["display"]).contains(value)


def test_unknown_is_never_reported_as_false_or_zero():
    assert sign(arb(0)) == 0
    assert sign(arb("-1 +/- 0.1")) == -1
    assert sign(arb("1 +/- 0.1")) == 1
    for value in (arb("0 +/- 1"), arb("nan"), arb("+inf")):
        assert sign(value) is None
        with pytest.raises(UnresolvedInterval):
            signed_evaluation(lambda: value, bits=16, max_bits=32)
    with pytest.raises(UnresolvedInterval):
        enclosure(arb("nan"))


def test_precision_retries_rebuild_and_restore_even_on_failure():
    before = ctx.prec
    decision, evidence = signed_evaluation(lambda: arb(2).sqrt() - ball(
        "1.41421356237309504880168872420969807856967187537694"),
        bits=32, max_bits=512)
    assert decision == 1 and evidence["precision_bits"] > 128
    assert ctx.prec == before
    with pytest.raises(UnresolvedInterval):
        signed_evaluation(lambda: arb(2).sqrt() - arb(2).sqrt(), bits=32, max_bits=64)
    assert ctx.prec == before
    with pytest.raises(ZeroDivisionError):
        signed_evaluation(lambda: 1 / 0)
    assert ctx.prec == before


def test_root_bracket_contains_an_independently_known_irrational_root():
    # 2*(1/4)^x + (1/2)^x = 1 has x=1 exactly.
    exact = production_root([(2, "1/4"), (1, "1/2")], upper=2)
    assert exact.lower == exact.upper == 1
    # 2*(1/3)^x=1, so x=log(2)/log(3); compare at much higher precision.
    root = production_root([(2, "1/3")], bits=32, digits=30)
    assert root.upper - root.lower <= F(1, 10**30)
    with ctx.workprec(256):
        independent = arb(2).log() / arb(3).log()
        assert ball(root.lower) < independent < ball(root.upper)
    assert F(root.lower_residual["lower"]) > 0
    assert F(root.upper_residual["upper"]) < 0


@pytest.mark.parametrize("terms", [[], [(0, "1/2")], [(-1, "1/2")],
                                  [(1, 0)], [(1, 1)], [(1, 2)]])
def test_root_requires_the_hypotheses_used_for_uniqueness(terms):
    with pytest.raises(ValueError):
        production_root(terms)


def test_root_requires_existence_and_propagates_unresolved_signs():
    with pytest.raises(ValueError, match="bracket"):
        production_root([(1, "1/2")], lower=1, upper=2)
    with pytest.raises(UnresolvedInterval):
        production_root([(2, "1/3")], bits=8, max_bits=8)
    for kwargs in ({"bits": 0}, {"digits": 0}, {"lower": 1, "upper": 0}):
        with pytest.raises(ValueError):
            production_root([(2, "1/3")], **kwargs)
