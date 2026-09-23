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
#: The commit each acknowledgement was read AT. An acknowledgement is about a
#: branch's CONTENTS, so it expires when the contents change; without this the
#: gate stays green while an acknowledged branch grows, which is how
#: latest-progress-summary reached +8 unread on 2026-09-20 after being
#: acknowledged at +5. Update the sha in the same commit as the reason.
#: Emptied 20 September 2026: all four acknowledged branches were merged into
#: main on that day, and `python tools/branch_drift.py` reports that no branch
#: carries a ledger row or artifact main lacks. The staleness gate asks for
#: entries to be removed once a branch stops drifting, so both lists are empty
#: rather than historical. The reasons they held are in the merge commits.
READ_AT: dict[str, str] = {}

ACKNOWLEDGED: dict[str, str] = {}


def _key(ref: str) -> str:
    return ref.split("origin/", 1)[-1]


@pytest.fixture(scope="module")
def drifts() -> list[BD.Drift]:
    if not BD.refs_are_visible(REPO):
        pytest.skip("no remote refs at all (shallow or single-branch clone)")
    return BD.report(REPO)


def test_the_symbolic_head_alias_is_never_scanned_as_a_branch() -> None:
    """refs/remotes/origin/HEAD shortens to "origin", which the old skip set missed.

    It spelled the exclusion "origin/HEAD", a string git never produces for that ref, so
    the alias was scanned as though it were a branch. Once the last feature branch was
    merged and deleted this left exactly one ref in the scan -- an alias of the base --
    and the gate compared main against itself.
    """
    refs = BD.branch_refs(REPO)
    assert "origin" not in refs, (
        "the remote's symbolic HEAD is being scanned as a branch; it resolves to whatever "
        "origin/HEAD points at, so the gate is comparing the base with an alias of itself")
    assert all(not r.endswith("/HEAD") for r in refs), refs


def test_a_scan_of_nothing_does_not_report_as_a_clean_scan() -> None:
    """Zero branches and zero drift are different facts and must not read alike.

    This is the gate's own failure mode, not a hypothetical: on 2026-09-20 every feature
    branch was merged and deleted, and `python tools/branch_drift.py` went on printing
    "No branch carries a ledger row or artifact that main lacks" over a scan of nothing.
    That sentence was quoted as evidence at the time.
    """
    scanned = BD.branch_refs(REPO)
    message = BD.render(BD.report(REPO), scanned)
    if scanned:
        assert "measured nothing" not in message
        assert "scanned" in message or "(+" in message
    else:
        assert "measured nothing" in message
        assert "No branch carries" not in message, (
            "an empty scan is being reported in the words of a clean one")


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



def test_files_are_counted_against_the_merge_base_not_main(tmp_path) -> None:
    """Main's deletions are not branch work; actual branch additions still count.

    The fixture owns its Git refs and history. It must never write a calibration
    ref in the shared checkout or depend on its pre-cleanup history.
    """
    import subprocess

    def git(*args):
        return subprocess.run(['git', '-c', f'safe.directory={tmp_path.as_posix()}',
                               '-c', 'user.name=Fixture', '-c', 'user.email=fixture@example.invalid',
                               '-c', 'commit.gpgsign=false', *args], cwd=tmp_path,
                              check=True, capture_output=True, text=True).stdout.strip()

    git('init', '-b', 'main')
    source = tmp_path / 'src/old.py'
    source.parent.mkdir()
    source.write_text('# deleted by main\n')
    git('add', 'src/old.py')
    git('commit', '-m', 'Ancestor')
    git('branch', 'ancestor')
    source.unlink()
    (tmp_path / 'src/current.py').write_text('# main\n')
    git('add', 'src')
    git('commit', '-m', 'Main cleanup')
    on_ref = set(git('ls-tree', '-r', '--name-only', 'ancestor').splitlines())
    on_main = set(git('ls-tree', '-r', '--name-only', 'main').splitlines())
    assert on_ref - on_main == {'src/old.py'}
    drift = BD.drift_for(tmp_path, 'ancestor')
    assert drift.ahead == 0
    assert not any(drift.files.values())

    git('checkout', '-b', 'research', 'ancestor')
    (tmp_path / 'src/new_result.py').write_text('# independent result\n')
    git('add', 'src/new_result.py')
    git('commit', '-m', 'Branch result')
    drift = BD.drift_for(tmp_path, 'research')
    assert drift.ahead == 1 and drift.carries_work
    assert drift.files['probe'] == ['src/new_result.py']


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

def test_acknowledgements_name_the_commit_they_read(drifts: list[BD.Drift]) -> None:
    """An acknowledgement expires when the branch moves past what was read.

    ACKNOWLEDGED describes a branch's CONTENTS, so a branch that grows after
    being acknowledged is unread again while the gate stays green. That is not
    hypothetical: `latest-progress-summary` was acknowledged at +5 and reached
    +8 with three more kernel-checked results before anyone looked, because
    nothing tied the entry to a commit.
    """
    heads = {_key(d.ref): BD.head_sha(REPO, d.ref) for d in drifts}

    missing = sorted(set(ACKNOWLEDGED) - set(READ_AT))
    assert not missing, (
        f"{missing} are acknowledged without naming the commit read. Add a "
        "short sha to READ_AT."
    )

    moved = [
        (key, READ_AT[key], heads[key])
        for key in sorted(set(ACKNOWLEDGED) & set(heads))
        if not heads[key].startswith(READ_AT[key])
    ]
    assert not moved, (
        "branch(es) have new commits since the acknowledgement was written, "
        "so what is recorded no longer describes them:\n"
        + "\n".join(
            f"    {k}: read at {r}, now at {h}" for k, r, h in moved
        )
        + "\n\nRead the new commits, update the reason, move the sha."
    )
