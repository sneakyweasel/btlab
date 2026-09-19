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
    "claude/latest-progress-summary-s011un": (
        "PENDING EXTRACTION, and it supersedes a day of work on main. Read "
        "2026-09-19. Three rows main lacks -- J-oe-fiber-block-lock, "
        "J-oe-poor-fiber-tail and "
        "J-oe-averaged-two-productions-reach-the-depth-two-ceiling -- plus "
        "formal/Problems/Juggler/FateResonanceCount.lean, which its own commit "
        "says is NOT YET COMPILED and is deliberately not imported into the "
        "barrel. It answers the averaging question by one inequality, "
        "|G_m/H_m - 1/2| <= 4||q alpha_m|| + 5/(2q) + 3.77 q/H_m at every "
        "convergent denominator q, with no exponential sum anywhere. Crucially "
        "it observes that P has FINITE total logarithmic mass, so there is "
        "nothing to plant: the adversarial-concentration problem that main "
        "spent 19 September building a backward-closure argument for does not "
        "need solving, and the conclusion holds for every set of integers with "
        "no structure at all. Verified here independently: the 1/m-weighted "
        "poor density decays like m^(-1/3) and sum over P of 1/m converges to "
        "about 1.3. What main has that survives is "
        "J-oe-fiber-pairing-third-is-attained and the ladder's 8.6e-5, both of "
        "which that branch explicitly leaves standing. Merging is Philippe's "
        "call and takes the whole branch or none of it, since the rows and the "
        "Lean are one result."
    ),
}


def _key(ref: str) -> str:
    return ref.split("origin/", 1)[-1]


@pytest.fixture(scope="module")
def drifts() -> list[BD.Drift]:
    if not BD.refs_are_visible(REPO):
        pytest.skip("no remote refs at all (shallow or single-branch clone)")
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

    Measuring "present on the branch, absent from main" counts every file main
    has since *deleted*. The August cursor/* branches each scored 17 Lean files
    and 102 sources that way -- all casualties of the src/bt restructure, none
    of them the branch's work. Counting additions since the merge base gives
    zero, which is the truth.

    Those branches are merged and gone, so the property is exercised against a
    throwaway ref at an ancestor commit rather than against whichever branch
    happens to illustrate it. An ancestor is the sharpest case: its merge base
    is itself, so it added nothing, while it still carries files main no longer
    has. The naive metric is computed alongside to show the two disagree --
    without that, a metric that always returned zero would pass.
    """

    import subprocess

    ancestor = subprocess.run(
        ["git", "rev-list", "-1", "HEAD", "--", "src/automata/modular.py"],
        capture_output=True, cwd=REPO, text=True,
    ).stdout.strip()
    if not ancestor:
        pytest.skip("pre-restructure history not present in this clone")

    ref = "refs/drift-calibration"
    subprocess.run(["git", "update-ref", ref, ancestor], cwd=REPO, check=True)
    try:
        on_ref = set(subprocess.run(
            ["git", "ls-tree", "-r", "--name-only", ancestor], capture_output=True,
            cwd=REPO, text=True).stdout.split())
        on_main = set(subprocess.run(
            ["git", "ls-tree", "-r", "--name-only", "main"], capture_output=True,
            cwd=REPO, text=True).stdout.split())
        naive = {f for f in on_ref - on_main if f.startswith(("src/", "formal/"))}
        assert naive, "the control needs an ancestor that main has since pruned"

        drift = BD.drift_for(REPO, ref)
        assert drift.ahead == 0, "an ancestor is behind main, never ahead"
        assert not any(drift.files.values()), (
            f"the merge-base metric must ignore main's own deletions; naive would "
            f"have reported {len(naive)} files"
        )
    finally:
        subprocess.run(["git", "update-ref", "-d", ref], cwd=REPO, check=False)

def test_artifacts_are_counted_and_not_only_ledger_rows() -> None:
    """The other calibration: a branch can carry a module and no ledger row.

    information-field-dynamics was the live example -- a 938-line Lean module
    and not one ledger id, invisible to a rows-only gate. Extracting it in
    7b93d626 dissolved that example, which is the point of extracting it, so
    the property is asserted against the classifier rather than against
    whichever branch happens to illustrate it today.
    """

    rows_only = BD.Drift(ref="x", ahead=1, behind=0, last_commit="2026-09-07")
    assert not rows_only.carries_work, "a branch adding nothing must not register"

    module_only = BD.Drift(
        ref="x",
        ahead=1,
        behind=0,
        last_commit="2026-09-07",
        ledger_ids=[],
        files={"lean": ["formal/Problems/Engine/Whatever.lean"], "probe": [], "test": [], "dossier": []},
    )
    assert module_only.carries_work, "a Lean module with no ledger row must register"

    row_only = BD.Drift(
        ref="x", ahead=1, behind=0, last_commit="2026-09-07", ledger_ids=["J-something"]
    )
    assert row_only.carries_work, "a ledger row with no files must register"

    assert {"lean", "probe", "test", "dossier"} <= set(BD.ARTIFACTS), (
        "the artifact classes a branch can strand must all be scanned"
    )
