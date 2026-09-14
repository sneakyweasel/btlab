"""A branch must not quietly hold results that main does not.

Three times in September 2026 the same finding was made twice, weeks apart,
because the first one sat on a branch nobody merged. This gate does not forbid
that -- branches are where work happens -- it forbids *nobody having looked*.
Every branch carrying a ledger row or an artifact main lacks must appear in
ACKNOWLEDGED with a reason. A new one fails the suite until someone reads it
and writes down what it is.

Acknowledging is cheap and is meant to be: one line saying superseded,
pending, or abandoned. The expensive thing is the rediscovery it prevents.
"""

from __future__ import annotations

import sys
from pathlib import Path

import pytest

REPO = Path(__file__).resolve().parents[2]
TOOLS = REPO / "tools"
if str(TOOLS) not in sys.path:
    sys.path.insert(0, str(TOOLS))

import branch_drift as BD  # noqa: E402

#: Branches whose drift has been read, with what was found. Keyed by the
#: trailing part of the ref, so a local checkout and its origin/ copy match the
#: same entry. Remove an entry when the branch is merged or deleted; do not add
#: one without looking at what the branch holds.
#:
#: Assessed 14 September 2026.
ACKNOWLEDGED: dict[str, str] = {
    "claude/information-field-dynamics-8eexis": (
        "Carries formal/Problems/Engine/InformationField.lean (938 lines, 90 "
        "declarations, no sorry, the three standard Mathlib axioms) and its "
        "prospecting-note test. Verified to build against Lean 4.33.1 / Mathlib "
        "v4.33.1 on 14 September: 1279 jobs, no errors, no warnings. Its two "
        "housekeeping commits are both superseded -- the 3.11 f-string repair by "
        "ab04ce80 and the itinerary restoration by c72419e7 -- so what remains is "
        "mathematics. EXTRACTION PENDING; the branch is 410 behind and will not "
        "merge."
    ),
    "claude/repo-progress-uq349e": (
        "Its collision / large-sieve body was extracted in 94006052. The three "
        "rows left behind are superseded and were dropped deliberately: "
        "J-tao-cylinder-hypothesis-quantifier-defect by J-unstopped-cylinder-bound "
        "on J-absorbed-cylinder, J-tower-threshold-two-readings by Paper C SS9.3(b) "
        "which prints both readings already, J-oeoee-envelope-audited by the "
        "Section 11 audit repairs of 14 September. Nothing further to take."
    ),
    "cursor/operator-fragment-nf-2862": (
        "BTC-op-fragment-complete (EXACT — HUMAN PROOF, 23 August) states that with "
        "N(D(x))→D(N(x)) every irreducible is Pref∘D^k∘N^ε and these inject into "
        "maps Z→Z. Superseded: main carries BTC-op-fragment-nd-nf and "
        "BTC-op-fragment-nd-semantic for the same enlarged TRS, both EXACT — LEAN "
        "VERIFIED, which is strictly stronger than the human proof. Nothing to take."
    ),
}


def _key(ref: str) -> str:
    return ref.split("origin/", 1)[-1]


@pytest.fixture(scope="module")
def drifts() -> list[BD.Drift]:
    refs = BD.branch_refs(REPO)
    if not refs:
        pytest.skip("no branch refs visible (shallow clone); drift cannot be measured")
    return BD.report(REPO)


def test_every_drifting_branch_has_been_read(drifts: list[BD.Drift]) -> None:
    """A branch holding a row or artifact main lacks must be acknowledged."""

    unread = [d for d in drifts if _key(d.ref) not in ACKNOWLEDGED]
    assert not unread, (
        "branch(es) carry laboratory results main does not have, and nobody has "
        "recorded what they are:\n\n"
        + BD.render(unread)
        + "\n\nRead them, then add an entry to ACKNOWLEDGED in this file saying "
        "superseded, pending extraction, or abandoned. Run "
        "`python tools/branch_drift.py` for the full report."
    )


def test_acknowledgements_are_not_stale(drifts: list[BD.Drift]) -> None:
    """Entries for branches that no longer drift should be removed."""

    live = {_key(d.ref) for d in drifts}
    stale = sorted(set(ACKNOWLEDGED) - live)
    assert not stale, (
        f"{stale} no longer carry anything main lacks -- merged, deleted, or "
        "extracted. Remove them from ACKNOWLEDGED so the list stays a list of "
        "real outstanding work."
    )


def test_files_are_counted_against_the_merge_base_not_main() -> None:
    """The calibration that cost the orphan gate its first two readings.

    Measuring 'present on the branch, absent from main' counts every file main
    has *deleted* since the fork. The August cursor/* branches each scored 17
    Lean files and 102 sources that way -- all of them casualties of the src/bt
    restructure, none of them the branch's work. Counting additions since the
    merge base gives zero, which is the truth.
    """

    ref = "origin/cursor/operator-fragment-nd-commute-d502"
    if ref not in BD.branch_refs(REPO):
        pytest.skip(f"{ref} not present")
    d = BD.drift_for(REPO, ref)
    assert d.ahead == 1, d.ahead
    assert not any(d.files.values()), d.files


def test_artifacts_are_counted_and_not_only_ledger_rows() -> None:
    """The other calibration: a branch can carry a module and no ledger row.

    information-field-dynamics adds a 938-line Lean module and not one ledger
    id, so a ledger-only gate reports it as clean. Whatever else changes, this
    branch must be visible while it exists.
    """

    ref = "origin/claude/information-field-dynamics-8eexis"
    if ref not in BD.branch_refs(REPO):
        pytest.skip(f"{ref} not present")
    d = BD.drift_for(REPO, ref)
    assert d.ledger_ids == [], d.ledger_ids
    assert d.files["lean"], "the Lean module must register as drift"
    assert d.carries_work
