"""Independent containment checks and rejection cases for the bounded Arb language."""
from fractions import Fraction as F

from flint import ctx
import pytest

from research_engine.arb_expressions import Expression, compare, evaluate, exact


def endpoints(result):
    return F(result["enclosure"]["lower"]), F(result["enclosure"]["upper"])


@pytest.mark.parametrize(("source", "value"), [
    ("0.1", F(1, 10)), ("9007199254740993", F(9007199254740993)),
    ("1e-100", F(1, 10**100)), ("(2+3)*7/4-1", F(31, 4)),
    ("(-2)**3", F(-8)), ("sqrt(4)", F(2)), ("abs(-3)", F(3)),
    ("cos(0)+exp(0)+sin(0)+atan(0)", F(2)), ("2**-3", F(1, 8)),
])
def test_exact_values_are_enclosed(source, value):
    result = evaluate(source)
    lo, hi = endpoints(result)
    assert lo <= value <= hi
    assert hi - lo < F(1, 10**20)


def test_irrational_containment_and_precision_restoration():
    before = ctx.prec
    lo, hi = endpoints(evaluate("sqrt(2)", bits=256))
    assert 0 < lo and lo**2 < 2 < hi**2
    assert ctx.prec == before
    with pytest.raises(ValueError):
        evaluate("exp(701)")
    assert ctx.prec == before


def test_box_enclosure_covers_endpoints_and_interior():
    lo, hi = endpoints(evaluate("x*x", {"x": ["-2", "3"]}))
    assert lo <= 0 <= hi and lo <= 4 <= hi and lo <= 9 <= hi
    result = compare("x-x", "0", "==", {"x": ["1", "2"]}, max_bits=128)
    assert result["status"] == "unresolved" and result["holds"] is None
    assert compare("x", "0", ">", {"x": ["1", "2"]})["holds"] is True
    assert compare("x", "0", "<", {"x": ["1", "2"]})["holds"] is False


@pytest.mark.parametrize(("relation", "expected"), [
    ("<", False), ("<=", True), (">", False), (">=", True), ("==", True), ("!=", False),
])
def test_exact_zero_comparisons(relation, expected):
    assert compare("1/2", "0.5", relation)["holds"] is expected


def test_adaptive_precision_resolves_nearby_distinct_reals():
    result = compare("sqrt(2)+1e-70", "sqrt(2)", bits=32, max_bits=512)
    assert result["holds"] is True
    assert len(result["attempted_bits"]) > 1
    assert F(result["difference"]["lower"]) > 0


@pytest.mark.parametrize("source", ["1/0", "log(-1)", "sqrt(-1)", "(-2)**0.5"])
def test_domain_failures_never_certify(source):
    assert evaluate(source)["status"] == "unresolved"
    result = compare(source, "0", max_bits=256)
    assert result["status"] == "unresolved" and result["holds"] is None


@pytest.mark.parametrize("source", [
    "__import__('os')", "open('x')", "pi.__class__", "(1).__class__", "x[0]",
    "[x for x in (1,2)]", "(lambda:1)()", "sqrt(x=1)", "True", "1j", "0xff",
    "1_000", "2^3", "1//2", "nan", "inf", "1e99999999999999999999999999999",
    "2**257", "exp(701)", "exp(exp(10))", "9" * 129,
    "1+" * 100 + "1", "-" * 25 + "1", "1" * 2049,
])
def test_unsupported_or_excessive_expressions_are_rejected(source):
    with pytest.raises(ValueError):
        evaluate(source)


@pytest.mark.parametrize("variables", [
    {"x": 0.1}, {"x": True}, {"x": ["2", "1"]}, {"x": ["1"]},
    {"x": ["0", 1]}, {"pi": "3"}, {"_x": "1"}, {"x": "1/0"},
])
def test_invalid_variables(variables):
    with pytest.raises(ValueError):
        Expression("x", variables)


@pytest.mark.parametrize("value", [0.1, True, "1e10000", "NaN", "1 +/- 1", "1/0"])
def test_no_rounded_or_nonfinite_exact_inputs(value):
    with pytest.raises(ValueError):
        exact(value)


@pytest.mark.parametrize(("bits", "max_bits"), [(True, 128), (31, 128), (128, 64), (128, 4097)])
def test_precision_budget(bits, max_bits):
    with pytest.raises(ValueError):
        compare("1", "0", bits=bits, max_bits=max_bits)


def test_extreme_intermediates_cannot_create_giant_endpoint_strings():
    for source in ("(1e-256)**256", "(1e256)**256"):
        with pytest.raises(ValueError):
            evaluate(source)
