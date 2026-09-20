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
#: Assessed 14 September 2026; extended 19 September 2026.
ACKNOWLEDGED: dict[str, str] = {
    "claude/exponent-floor-3n1-2adic-mvwa96": (
        "Pending extraction. Six rows from the 19-20 September exponent-floor session. "
        "Four are CLOSE placements: J-lemma-eight-is-the-exponent-valuation and "
        "J-exponential-sends-density-to-log-density locate Hercher's Lemma 8 on the "
        "Juggler's exponent and price its confinement; "
        "J-lemma-eight-floor-is-tight-at-every-known-cycle and "
        "J-the-missing-juggler-floor-is-worth-a-quarter-at-length-22 price the same floor "
        "on the negative Collatz side; J-repunit-floor-power-is-closed-form adds two exact "
        "floor-power values off the perfect-power locus and kills the Mersenne primality "
        "reading. One is PROMOTE and is the one to read first: "
        "J-negative-floor-makes-the-mirror-unconditional supplies the 3x-1 verification "
        "floor this journal had named as its best next question, so the finance mirror's "
        "period bound is a statement rather than a table -- a fourth negative cycle has "
        "period at least 4404167. No row raises N_0, excludes a Juggler cycle or touches a "
        "manuscript. Nothing here is superseded and nothing is abandoned -- the branch is "
        "waiting to be read and merged. Extended 20 September: two further CLOSE rows, "
        "J-multiplicative-knight-residual-is-the-state-dependence (Knight's cancellation "
        "transports as cube-and-divide and its residual is exactly the state dependence "
        "of the slack) and J-even-run-dual-of-lemma-eight-is-capped-by-the-shape (the "
        "multiplicative order of 2, read off the even runs, is a second floor dual to "
        "Lemma 8, and the CycleMin shape caps it at R <= floor((log2 3 - 1) a), below "
        "Lemma 8 by 2^(0.41504 a), with zero dual-only kills in a census of 2.26 million "
        "shape words)."
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
