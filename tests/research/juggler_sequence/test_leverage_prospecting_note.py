"""Anti-overclaim guard for the leverage prospecting note.

The note ranks open objects of the programme by an estimated leverage ratio.  Its whole risk is
that a later edit turns an estimate into a claim: a ranking is a reading of the corpus, and the
only thing standing between it and an unearned label is the prose.  These tests pin the
disclaimers, the OBSERVATION label, and the two conclusions the note is answerable for -- that
every ranked candidate sits below the frontier, and that the objects it excluded stay excluded.
"""

from __future__ import annotations

import re
from pathlib import Path

NOTE = Path("docs/theory/juggler_leverage_prospecting_note.md")


def flowed() -> str:
    """The note's lowercased text with runs of whitespace collapsed.

    The note is hard-wrapped, so a phrase these tests pin can straddle a line break; matching
    against the raw text would make the guard depend on where the paragraph happens to wrap.
    """
    return re.sub(r"\s+", " ", NOTE.read_text(encoding="utf-8").lower())

#: the seven labels of docs/README.md; only OBSERVATION may carry the note's own estimates
INVENTED_TAGS = ("PROVED", "VERIFIED COMPUTATIONALLY", "LEAN_CERTIFIED", "MACHINE VERIFIED")


def test_note_is_labelled_observation_and_quotes_existing_rows():
    note = NOTE.read_text(encoding="utf-8")
    assert "**OBSERVATION**" in note
    for row in ("J-equidistribution-implies-density-one", "J-tao-rate-implies-conjecture"):
        assert row in note
    for source in (
        "juggler_oeoee_production.md",
        "juggler_fate_almost_all_note.md",
        "juggler_parity_discrepancy_note.md",
        "theorem_ledger.md",
    ):
        assert source in note
    for tag in INVENTED_TAGS:
        assert tag not in note


def test_note_anti_overclaim():
    note = NOTE.read_text(encoding="utf-8")
    lower = flowed()
    assert "not a halt theorem" in lower
    assert "not a second manuscript" in note
    assert "not a termination theorem" in lower
    assert "no cycle of any length" in lower
    assert "nothing unconditional is claimed" in lower
    assert "no fate is excluded" in lower
    assert "theorem no_cycle_itinerary_any_length" not in note


def test_note_keeps_its_own_negative_conclusion():
    """The ranking's honest finding: the survivors are below the frontier, and it opens nothing."""
    lower = flowed()
    assert "below the frontier" in lower
    assert "no branch is opened" in lower
    assert "no candidate is promoted here" in lower
    assert "proofability" in lower


def test_note_does_not_reopen_fenced_rows():
    """Excluded objects are named as excluded; the note must not argue for revisiting them."""
    note = NOTE.read_text(encoding="utf-8")
    lower = flowed()
    assert "J-clotho-threads-per-thread-contagion" in note
    assert "J-kernel-localize" in note
    assert "those fences stand" in lower
