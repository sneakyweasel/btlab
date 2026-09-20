"""The multiplicative Knight transports exactly, and its residual is the state dependence.

Knight's cancellation works because the Bohm-Sontacchi charge is word-determined. The Juggler's
cocycle is multiplicative, so cube-and-divide is the analogue of 3f - f^R and cancels the shared
middle exponent exactly -- but 1 + q depends on the state as well as the word, so the residual is the
sixth power of the ratio of the two middle slacks rather than 1.
"""

from __future__ import annotations

import json
from fractions import Fraction

import pytest

from research.juggler_sequence.multiplicative_knight import (
    CLASS_RESIDUAL,
    JSON_PATH,
    concatenation_law,
    floor_power,
    per_start_residual,
    residual,
    slack,
    word_index,
    word_of,
)


def test_slack_is_the_lean_definition() -> None:
    """`1 + q = n^(3^#O) / T_w(n)^(2^|w|)`."""
    q, end = slack(3, "O")
    assert end == floor_power(3) == 5
    assert q == Fraction(3**3, 5**2)
    q, end = slack(4, "E")
    assert end == 2 and q == Fraction(4, 2**2) == 1        # 4 is a square: no charge
    assert slack(3, "E") == (None, None)                    # word not realized


def test_concatenation_law_holds() -> None:
    data = concatenation_law(limit=200, depth=5)
    assert data["holds"]
    assert data["failures"] == []
    assert data["splits_checked"] > 100


def test_the_residual_is_exactly_the_middle_slack_ratio() -> None:
    data = residual(length=6, bound=120_000)
    assert data["holds"]
    assert data["failures"] == []
    assert data["pairs_tested"] > 0


def test_knights_case_never_occurs_on_the_juggler() -> None:
    """The residual is 1 for Collatz identically; here it is 1 in no realized pair."""
    data = residual(length=6, bound=120_000)
    assert data["pairs_with_equal_middle_slack"] == 0


def test_the_residual_over_every_realizing_start() -> None:
    """Many instances per word, not one: the identity is exact and the residual is never 1."""
    data = per_start_residual(limit=2500, bound=120_000)
    assert data["holds"]
    assert data["failures"] == 0
    assert data["instances_tested"] > 200
    assert data["instances_with_equal_middle_slack"] == 0


def test_the_middle_word_is_read_at_different_states() -> None:
    """The mechanism: O u E starts its middle at J(n), E u O at J(n'), and n != n'."""
    first = word_index(length=6, bound=120_000)
    checked = 0
    for w, n in sorted(first.items()):
        if w[0] != "O" or w[-1] != "E":
            continue
        mirror = "E" + w[1:-1] + "O"
        n2 = first.get(mirror)
        if n2 is None:
            continue
        assert n != n2
        qa, _ = slack(floor_power(n), w[1:-1])
        qb, _ = slack(floor_power(n2), w[1:-1])
        if qa is not None and qb is not None:
            assert qa != qb                    # the two readings differ, so nothing cancels
            checked += 1
    assert checked > 0


def test_word_of_agrees_with_the_map() -> None:
    n = 7
    letters = []
    for _ in range(5):
        letters.append("E" if n % 2 == 0 else "O")
        n = floor_power(n)
    assert word_of(7, 5) == "".join(letters)


@pytest.mark.skipif(not JSON_PATH.exists(), reason="probe artifact not built")
def test_committed_artifact_is_green() -> None:
    data = json.loads(JSON_PATH.read_text(encoding="utf-8"))
    assert data["decision"]["classification"] == CLASS_RESIDUAL
    assert data["decision"]["branch"] == "CLOSE"
    assert data["concatenation_law"]["holds"] and data["residual"]["holds"]
    assert data["residual"]["pairs_with_equal_middle_slack"] == 0
