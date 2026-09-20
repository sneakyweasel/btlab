"""Paper B's survivor recursion, and the Beatty pair its plateau lengths form.

These tests pin the recursion the Lean layer already carries, the two closed forms that
locate its plateaus, the one-term shift in the deficit identification, and the `d = 1`
exception -- the three places where an unstated offset would otherwise hide.
"""

from __future__ import annotations

import json
import math

import pytest

from research.juggler_sequence.oeis_neighbourhood import (
    A100982_STORED,
    CLASS_NEIGHBOURHOOD,
    JSON_PATH,
    MAX_DEPTH,
    a020914,
    a054414,
    beatty_partition,
    deficit_is_a100982,
    probe_payload,
    recursion_holds,
    render_markdown,
    survivor_recursion,
)


def test_recursion_matches_the_lean_theorem() -> None:
    """`N_(d+1) + M_(d+1) = 2 N_d` is `neverNegCount_succ_sub_onBarrier`, kernel-checked."""
    res = recursion_holds(max_depth=120)
    assert res["holds"]
    assert res["violations"] == []
    # the opening of A076227, which J-paper-b-survivors-are-oeis-a076227 identifies N_d with
    assert res["first_twenty_counts"][:10] == [1, 1, 2, 3, 4, 8, 13, 19, 38, 64]


def test_survivor_recursion_rejects_nonsense_depth() -> None:
    with pytest.raises(ValueError):
        survivor_recursion(0)


def test_plateau_lengths_are_the_beatty_complement() -> None:
    part = beatty_partition(max_depth=MAX_DEPTH)
    assert part["stalling_is_a020914"]
    assert part["doubling_is_a054414_minus_one"]
    assert part["partition_of_one_to_max"]
    # the laboratory's three verified plateau instances sit in the doubling set
    for length in (6, 9, 11):
        assert length in part["doubling_lengths"]


def test_one_is_the_exception_and_it_is_stated() -> None:
    """A054414 contains 1, but `E` contracts at once, so 1 is NOT a plateau length."""
    part = beatty_partition(max_depth=40)
    assert part["one_is_the_exception"]
    assert not part["doubling_is_a054414_exactly"]
    assert 1 in a054414(40)
    assert 1 not in part["doubling_lengths"]
    _counts, certs = survivor_recursion(4)
    assert certs[1] == 1


def test_closed_forms_are_what_they_claim() -> None:
    got = a020914(20)
    want = [v for v in (math.floor(n * math.log2(3)) + 1 for n in range(0, 40)) if v <= 20]
    assert got == want
    assert got[:6] == [1, 2, 4, 5, 7, 8]
    slope = 1 - math.log(2) / math.log(3)
    got54 = a054414(20)
    want54 = [v for v in (1 + math.floor(n / slope) for n in range(0, 40)) if v <= 20]
    assert got54 == want54
    assert got54[:6] == [1, 3, 6, 9, 11, 14]
    # the two closed forms are complementary apart from the shared value 1
    assert sorted(set(got) | set(got54)) == list(range(1, 21))
    assert set(got) & set(got54) == {1}


def test_deficit_identification_carries_its_shift() -> None:
    """The laboratory's deficit list has one extra leading term; A100982 is the rest."""
    dfc = deficit_is_a100982(max_depth=MAX_DEPTH)
    assert dfc["equal_after_dropping_one"]
    assert not dfc["equal_without_shift"]
    assert dfc["terms_compared"] == len(A100982_STORED)
    assert dfc["deficits_head"][0] == 1
    assert dfc["deficits_head"][1:5] == list(A100982_STORED[:4])


def test_a100982_constant_was_not_hand_transcribed() -> None:
    """A guard on the failure that produced it: the tail must not be round numbers.

    The hand transcription replaced by this constant was right for the twelve terms that had
    appeared in a terminal and invented for the twenty that had not. The invented tail grew
    too slowly; the real one grows like the survivor count.
    """
    assert len(A100982_STORED) == 32
    assert A100982_STORED[:4] == (1, 1, 2, 3)
    assert A100982_STORED[12] == 8045
    assert A100982_STORED[-1] == 794919136728
    ratios = [A100982_STORED[i + 1] / A100982_STORED[i] for i in range(6, 31)]
    assert all(r > 1.5 for r in ratios)


def test_payload_and_markdown() -> None:
    data = probe_payload(max_depth=60)
    assert data["decision"]["classification"] == CLASS_NEIGHBOURHOOD
    assert data["decision"]["call"] == "CLOSE"
    assert set(data["sequences"]) == {"A076227", "A020914", "A054414", "A100982"}
    assert "CC BY-SA" in data["provenance"]
    assert "N_0 = 350000000 is untouched" in data["anti_overclaim"]
    text = render_markdown(data)
    assert "Beatty" in text
    assert "A054414" in text


@pytest.mark.skipif(not JSON_PATH.exists(), reason="probe artifact not built")
def test_committed_artifact_agrees() -> None:
    data = json.loads(JSON_PATH.read_text(encoding="utf-8"))
    assert data["recursion"]["holds"]
    assert data["partition"]["stalling_is_a020914"]
    assert data["partition"]["doubling_is_a054414_minus_one"]
    assert data["deficit"]["equal_after_dropping_one"]
