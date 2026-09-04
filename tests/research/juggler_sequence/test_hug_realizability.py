"""Is the hug word realizable at the generic rate? (Section 6)

The reformulated obstruction asks which Sturmian words in {OE, OOE} at the critical density
occur as Juggler itineraries.  The extremal walk of Theorem 5.3 is one, so if it were rare the
walk charge would bound an adversary that cannot occur.  It is not rare.
"""

from __future__ import annotations

from research.juggler_sequence import hug_realizability as H
from research.juggler_sequence.paper_a_audit import o_min

HI = 400_000


def test_hug_word_is_two_blocks_only() -> None:
    """The extremal walk is a mixture of OE and OOE alone, once the truncated tail is dropped."""
    w = H.hug_word(40, o_min(40), 1000)
    b = H.sturmian_blocks(w)
    assert b["only_OE_OOE"], b["blocks"]
    assert 0.5 < b["OOE_share"] < 0.8


def test_truncated_tail_is_not_counted_as_a_block() -> None:
    """OO at the end of a prefix is a cut, not a third block type."""
    assert H.sturmian_blocks((1, 1, 0, 1, 1))["only_OE_OOE"]
    assert H.sturmian_blocks((1, 1, 0, 1, 0))["blocks"] == {"OOE": 1, "OE": 1}


def test_prefix_counts_are_nested() -> None:
    """Longer prefixes can only be realized by fewer starts."""
    w = H.hug_word(30, o_min(30), 1000)
    counts = H.prefix_counts(w, 14, HI)
    assert counts == sorted(counts, reverse=True)


def test_hug_prefixes_are_realized_at_the_generic_rate() -> None:
    """Ratio to 2^-(l-1) stays near 1 -- no deficit, hence no hug-specific obstruction."""
    r = H.realizability_profile(length=30, depth=14, hi=HI)
    for row in r["rows"]:
        if row["l"] < 6 or row["count"] == 0:
            continue
        assert 0.5 < row["ratio"] < 2.5, row


def test_normalisation_accounts_for_the_forced_first_letter() -> None:
    """Odd starts always begin with O, so the expectation is 2^-(l-1), not 2^-l."""
    r = H.realizability_profile(length=30, depth=3, hi=HI)
    first = r["rows"][0]
    assert first["count"] == r["odd_starts"]
    assert abs(first["ratio"] - 1.0) < 1e-9


def test_control_band_is_wide_and_the_hug_sits_inside_it() -> None:
    """The Juggler itinerary measure is far from uniform at this depth; the hug is ordinary."""
    c = H.control_profile(depth=12, hi=HI)
    assert c["max_ratio"] > 10 * c["median_ratio"]
    assert c["min_ratio"] < 0.5
    r = H.realizability_profile(length=30, depth=12, hi=HI)
    hug_ratio = r["rows"][-1]["ratio"]
    assert c["min_ratio"] < hug_ratio < c["max_ratio"]
