"""Continued fractions must be exact for rationals and never guess a real's next term."""
from fractions import Fraction as F

from flint import arb, ctx
import pytest

from research_engine.diophantine import (
    best_approximations, certified_partial_quotients, convergents, partial_quotients_past,
    rational_partial_quotients, semiconvergents,
)
from research_engine.intervals import ball, bounds

#: OEIS A028507, continued fraction for log_2(3), terms n = 0..44 of the published entry.
LOG2_3 = [1, 1, 1, 2, 2, 3, 1, 5, 2, 23, 2, 2, 1, 1, 55, 1, 4, 3, 1, 1, 15, 1, 9, 2, 5,
          7, 1, 1, 4, 8, 1, 11, 1, 20, 2, 1, 10, 1, 4, 1, 1, 1, 1, 1, 37]


def log2_3() -> arb:
    return arb(3).log() / arb(2).log()


@pytest.mark.parametrize(("value", "expected"), [
    ("355/113", [3, 7, 16]), ("0.1", [0, 10]), ("-7/3", [-3, 1, 2]), (5, [5]),
    ("1/2", [0, 2]), (F(485, 306), [1, 1, 1, 2, 2, 3, 1, 5]),
])
def test_rational_expansion_is_canonical_and_round_trips(value, expected):
    terms = rational_partial_quotients(value)
    assert terms == expected
    p, q = convergents(terms)[-1]
    assert F(p, q) == F(value)


def test_rational_expansion_rejects_floats():
    with pytest.raises(TypeError):
        rational_partial_quotients(0.1)


def test_convergents_of_log2_3_are_the_known_cycle_ratios():
    assert convergents(LOG2_3[:10]) == [
        (1, 1), (2, 1), (3, 2), (8, 5), (19, 12), (65, 41), (84, 53), (485, 306),
        (1054, 665), (24727, 15601)]


def test_semiconvergents_interleave_the_convergents_by_denominator():
    fractions = semiconvergents([1, 1, 1, 2, 2])
    assert fractions == [(1, 1), (2, 1), (3, 2), (5, 3), (8, 5), (11, 7), (19, 12)]
    assert set(convergents([1, 1, 1, 2, 2])) <= set(fractions)
    denominators = [q for _, q in fractions]
    assert denominators == sorted(denominators)
    assert semiconvergents(LOG2_3, max_denominator=12)[-1] == (19, 12)


@pytest.mark.parametrize("bad", [[], [1, 0], [1, -2], [1.0, 2]])
def test_invalid_quotients_are_rejected(bad):
    with pytest.raises(ValueError):
        convergents(bad)


def test_log2_3_expansion_matches_oeis_a028507():
    expansion = certified_partial_quotients(log2_3, len(LOG2_3))
    assert expansion.complete and not expansion.terminated
    assert list(expansion.quotients) == LOG2_3
    assert expansion.as_dict()["status"] == "certified"


def test_a_short_budget_stops_on_a_true_prefix_instead_of_guessing():
    expansion = certified_partial_quotients(log2_3, 60, bits=32, max_bits=64)
    assert not expansion.complete
    assert expansion.reason
    assert 0 < len(expansion.quotients) < 60
    assert list(expansion.quotients) == LOG2_3[:len(expansion.quotients)]
    assert expansion.attempted_bits == (32, 64)
    assert expansion.as_dict()["status"] == "unresolved"


def test_a_double_would_have_continued_with_a_wrong_term():
    import math

    x, terms = math.log2(3), []
    for _ in range(20):
        terms.append(math.floor(x))
        x = 1 / (x - math.floor(x))
    assert terms[:16] == LOG2_3[:16] and terms[16] != LOG2_3[16]
    assert certified_partial_quotients(log2_3, 20).quotients[16] == LOG2_3[16]


def test_exact_integer_terminates():
    expansion = certified_partial_quotients(lambda: arb(5), 10)
    assert expansion.terminated and expansion.complete
    assert expansion.quotients == (5,)


@pytest.mark.parametrize(("value", "prefix"), [("1/3", [0]), ("7/4", [1, 1])])
def test_rational_input_is_unresolved_not_invented(value, prefix):
    expansion = certified_partial_quotients(lambda: ball(value), 5, max_bits=512)
    assert not expansion.complete
    assert list(expansion.quotients) == prefix
    assert prefix == rational_partial_quotients(value)[:len(prefix)]


def test_an_input_box_certifies_only_the_shared_prefix():
    low, high = rational_partial_quotients("1.58"), rational_partial_quotients("1.59")
    expansion = certified_partial_quotients(lambda: ball("1.58").union(ball("1.59")), 10)
    shared = list(expansion.quotients)
    assert not expansion.complete
    assert shared == low[:len(shared)] == high[:len(shared)]
    assert len(shared) < min(len(low), len(high))


@pytest.mark.parametrize("arguments", [{"terms": 0}, {"terms": 3, "bits": 64, "max_bits": 32},
                                       {"terms": 2.0}])
def test_invalid_budgets_are_rejected(arguments):
    with pytest.raises(ValueError):
        certified_partial_quotients(log2_3, **arguments)


@pytest.mark.parametrize("bound", [1, 2, 20000, 10**6, 10**30])
def test_expansion_stops_at_the_first_denominator_past_the_bound(bound):
    expansion = partial_quotients_past(log2_3, bound)
    denominators = [q for _, q in convergents(expansion.quotients)]
    assert expansion.complete and expansion.satisfied
    assert denominators[-1] > bound >= denominators[-2]
    shared = min(len(expansion.quotients), len(LOG2_3))
    assert list(expansion.quotients)[:shared] == LOG2_3[:shared]


def test_expansion_past_a_bound_reports_a_short_budget():
    expansion = partial_quotients_past(log2_3, 10**40, bits=32, max_bits=64)
    assert not expansion.complete
    assert [q for _, q in convergents(expansion.quotients)][-1] <= 10**40
    assert partial_quotients_past(lambda: arb(5), 10**9).terminated


def brute_force_minimum(evaluate, max_denominator, tau):
    """min over every q <= Q of q**tau * ||q alpha||, without the convergent theorem."""
    with ctx.workprec(256):
        alpha, best = evaluate(), None
        for q in range(1, max_denominator + 1):
            y = q * alpha
            frac = y - y.floor().unique_fmpz()
            nearest = frac if frac < arb(1) / 2 else 1 - frac
            value = arb(q) ** tau * nearest
            if best is None or value < best[0]:
                best = (value, q)
    return best


@pytest.mark.parametrize(("evaluate", "tau"), [(log2_3, 0), (log2_3, 1), (log2_3, 2),
                                               (lambda: arb(2).sqrt(), 1)])
def test_best_approximation_minimum_agrees_with_brute_force(evaluate, tau):
    result = best_approximations(evaluate, 2000, tau)
    value, q = brute_force_minimum(evaluate, 2000, tau)
    assert result["status"] == "certified" and result["attained_at"] == [str(q)]
    lo, hi = bounds(value)
    assert F(result["minimum"]["lower"]) <= hi and lo <= F(result["minimum"]["upper"])


def test_best_approximations_of_log2_3_reach_the_near_cycle_ratio():
    result = best_approximations(log2_3, 10**6)
    rows = result["convergents"]
    assert [row["q"] for row in rows] == ["1", "2", "5", "12", "41", "53", "306", "665", "15601",
                                          "31867", "79335", "111202", "190537"]
    assert (rows[-1]["p"], rows[-1]["q"]) == ("301994", "190537")
    assert result["attained_at"] == ["190537"]
    assert [row["side"] for row in rows[:4]] == ["above", "below", "above", "below"]
    assert "larger q" in result["scope"]


def test_q_equal_one_uses_the_nearer_integer():
    # log2(3) = [1; 1, ...]: the integer 2 is nearer than 1, so ||alpha|| = 2 - alpha.
    rows = best_approximations(log2_3, 1)["convergents"]
    assert [(row["p"], row["q"]) for row in rows] == [("2", "1")]
    # sqrt(2) = [1; 2, ...]: the floor is nearer.
    rows = best_approximations(lambda: arb(2).sqrt(), 1)["convergents"]
    assert [(row["p"], row["q"]) for row in rows] == [("1", "1")]


def test_an_integer_has_exact_zero_distance():
    result = best_approximations(lambda: arb(5), 10)
    assert result["status"] == "certified"
    assert result["minimum"] == {"lower": "0", "upper": "0"}
    assert result["convergents"][0]["side"] == "exact"


def test_a_short_budget_is_unresolved_rather_than_a_minimum():
    result = best_approximations(log2_3, 10**15, bits=32, max_bits=32)
    assert result["status"] == "unresolved" and "minimum" not in result


@pytest.mark.parametrize(("max_denominator", "tau"), [(0, 0), (10, -1), (10, 0.5), (1.0, 0)])
def test_invalid_best_approximation_requests(max_denominator, tau):
    with pytest.raises((TypeError, ValueError)):
        best_approximations(log2_3, max_denominator, tau)
