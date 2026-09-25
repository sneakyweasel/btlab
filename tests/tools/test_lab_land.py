"""Landing: one branch at a time, shared views regenerated, main moved only by fast-forward."""
from __future__ import annotations

import os
from pathlib import Path
import subprocess
import sys

import pytest

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "tools"))
import lab_land  # noqa: E402

VIEW = "docs/theory/theorem_ledger.md"
#: A stand-in generator: the view lists every claim file, as the real ledger lists every row.
GENERATOR = """
import os
from pathlib import Path
rows = sorted(p.read_text().strip() for p in Path('claims').glob('*.txt'))
Path('docs/theory').mkdir(parents=True, exist_ok=True)
Path('docs/theory/theorem_ledger.md').write_text('\\n'.join(rows) + '\\n', newline='\\n')
"""
CHECK = """
import os
from pathlib import Path
import sys
rows = sorted(p.read_text().strip() for p in Path('claims').glob('*.txt'))
sys.exit(Path('docs/theory/theorem_ledger.md').read_text() != '\\n'.join(rows) + '\\n')
"""


def git(repo: Path, *args: str) -> str:
    return subprocess.run(["git", *args], cwd=repo, check=True, capture_output=True,
                          text=True).stdout.strip()


def commit(repo: Path, files: dict[str, str], message: str) -> None:
    for name, text in files.items():
        (repo / name).parent.mkdir(parents=True, exist_ok=True)
        (repo / name).write_text(text)
    git(repo, "add", "--", *files)
    git(repo, "commit", "-q", "-m", message)


def regenerate(repo: Path) -> None:
    subprocess.run([sys.executable, "gen.py"], cwd=repo, check=True)


def make_repo(tmp_path: Path) -> Path:
    """A small lab: a claim, a generator for its view, and the committed view."""
    repo = tmp_path / "lab"
    repo.mkdir()
    git(repo, "init", "-q", "-b", "main")
    git(repo, "config", "user.name", "Test")
    git(repo, "config", "user.email", "test@example.invalid")
    git(repo, "config", "core.autocrlf", "false")
    (repo / ".gitignore").write_text(".build/\n")
    commit(repo, {"gen.py": GENERATOR, "check.py": CHECK, "claims/a.txt": "row a\n",
                  "notes.md": "base\n", ".gitignore": ".build/\n"}, "base")
    regenerate(repo)
    git(repo, "add", VIEW)
    git(repo, "commit", "-q", "-m", "view")
    return repo


@pytest.fixture
def repo(tmp_path):
    return make_repo(tmp_path)


def branch_with(repo: Path, name: str, files: dict[str, str], with_view: bool = True) -> None:
    git(repo, "switch", "-q", "-c", name)
    commit(repo, files, f"work on {name}")
    if with_view:
        regenerate(repo)
        git(repo, "commit", "-q", "-am", "view on branch")
    git(repo, "switch", "-q", "main")


def land(repo, branch, **kw):
    return lab_land.land(repo, branch, regenerate=(["gen.py"],), checks=(["check.py"],), **kw)


def test_a_clean_branch_lands_by_fast_forward(repo):
    branch_with(repo, "agent/one", {"claims/b.txt": "row b\n"})
    report = land(repo, "agent/one")
    assert report["status"] == "landed"
    assert git(repo, "rev-parse", "main") == report["new_head"]
    assert (repo / VIEW).read_text() == "row a\nrow b\n"
    assert not list((repo / ".build/land").iterdir()), "the landing worktree must be removed"


def test_two_agents_editing_the_shared_view_are_merged_by_regeneration(repo):
    branch_with(repo, "agent/one", {"claims/b.txt": "row b\n"})
    branch_with(repo, "agent/two", {"claims/c.txt": "row c\n"})
    assert land(repo, "agent/one")["status"] == "landed"
    report = land(repo, "agent/two")
    assert report["status"] == "landed" and report["resolved_shared_views"] == [VIEW]
    assert (repo / VIEW).read_text() == "row a\nrow b\nrow c\n"


def test_a_conflict_in_a_real_file_stops_with_main_unchanged(repo):
    branch_with(repo, "agent/one", {"notes.md": "one\n"}, with_view=False)
    branch_with(repo, "agent/two", {"notes.md": "two\n"}, with_view=False)
    land(repo, "agent/one")
    before = git(repo, "rev-parse", "main")
    with pytest.raises(lab_land.LandingError, match="conflict outside the shared views"):
        land(repo, "agent/two")
    assert git(repo, "rev-parse", "main") == before
    assert (repo / "notes.md").read_text() == "one\n"


def test_uncommitted_work_in_mains_checkout_is_never_overwritten(repo):
    branch_with(repo, "agent/one", {"notes.md": "landed\n"}, with_view=False)
    (repo / "notes.md").write_text("someone's unfinished edit\n")
    before = git(repo, "rev-parse", "main")
    with pytest.raises(lab_land.LandingError, match="waits on land/agent-one"):
        land(repo, "agent/one")
    assert git(repo, "rev-parse", "main") == before
    assert (repo / "notes.md").read_text() == "someone's unfinished edit\n"
    assert git(repo, "rev-parse", "land/agent-one")


def test_a_failing_check_or_a_dry_run_leaves_main_alone(repo):
    branch_with(repo, "agent/one", {"claims/b.txt": "row b\n"})
    before = git(repo, "rev-parse", "main")
    report = land(repo, "agent/one", dry_run=True)
    assert report["status"].startswith("ready") and git(repo, "rev-parse", "main") == before
    with pytest.raises(lab_land.LandingError, match="landing check failed"):
        lab_land.land(repo, "agent/one", regenerate=(), checks=([ "-c", "raise SystemExit(1)"],))
    assert git(repo, "rev-parse", "main") == before


def test_a_branch_already_in_main_has_nothing_to_land(repo):
    git(repo, "branch", "agent/old")
    assert land(repo, "agent/old")["status"] == "nothing to land"


def test_a_view_that_differs_only_in_line_endings_is_not_a_change(repo):
    """Regression: on Windows the regenerated views came out CRLF; git reports such a file
    as modified and then normalises it away on `add`, and landing failed on an empty commit."""
    commit(repo, {".gitattributes": "* text=auto eol=lf\n"}, "attributes")
    view = repo / VIEW
    view.write_bytes(view.read_bytes().replace(b"\n", b"\r\n"))
    assert git(repo, "status", "--porcelain"), "the precondition: git sees the file as modified"
    assert lab_land.commit_views(repo, "regenerate") == []
    assert git(repo, "log", "-1", "--format=%s") == "attributes"


def test_regeneration_may_only_touch_the_shared_views(repo):
    (repo / "notes.md").write_text("changed by a generator\n")
    with pytest.raises(lab_land.LandingError, match="outside the shared views"):
        lab_land.commit_views(repo, "regenerate")


def agent_worktree(repo: Path, name: str, files: dict[str, str] | None = None) -> Path:
    """An agent worktree as `lab.py worktree new` makes it, optionally with one commit."""
    work = repo / ".build/worktrees" / name
    git(repo, "worktree", "add", "-q", "-b", f"agent/{name}", str(work), "main")
    if files:
        commit(work, files, f"work on {name}")
    return work


def gone(repo: Path, work: Path, branch: str) -> bool:
    return not work.exists() and not git(repo, "branch", "--list", branch)


def test_a_branch_with_an_unlanded_commit_is_refused(repo):
    work = agent_worktree(repo, "one", {"claims/b.txt": "row b\n"})
    report = lab_land.remove_worktree(repo, "one")
    assert report["status"] == "refused" and not report["verdict"]["landed"]
    assert report["verdict"]["unlanded"][0].endswith("work on one")
    assert work.exists() and git(repo, "branch", "--list", "agent/one")


def test_a_dirty_worktree_is_refused_even_when_landed(repo):
    work = agent_worktree(repo, "one")
    (work / "scratch.txt").write_text("untracked\n")
    report = lab_land.remove_worktree(repo, "one")
    assert report["verdict"]["test"] == "ancestor"
    assert report["status"] == "refused" and "untracked" in report["reasons"][0]
    (work / "scratch.txt").unlink()
    (work / "notes.md").write_text("modified\n")
    assert lab_land.remove_worktree(repo, "one")["status"] == "refused"
    assert (work / "notes.md").read_text() == "modified\n"


def test_a_rebased_and_landed_branch_is_accepted_by_cherry(repo):
    work = agent_worktree(repo, "one", {"claims/b.txt": "row b\n"})
    commit(repo, {"notes.md": "main moved on\n"}, "unrelated work on main")
    assert land(repo, "agent/one")["status"] == "landed"
    assert subprocess.run(["git", "merge-base", "--is-ancestor", "agent/one", "main"],
                          cwd=repo).returncode, "the precondition: landing rewrote the commit"
    dry = lab_land.remove_worktree(repo, "one", dry_run=True)
    assert dry["status"].startswith("removable") and dry["verdict"]["test"] == "cherry"
    assert work.exists(), "a dry run changes nothing"
    assert lab_land.remove_worktree(repo, "one")["status"] == "removed"
    assert gone(repo, work, "agent/one")


def test_a_merged_branch_is_accepted_as_an_ancestor(repo):
    work = agent_worktree(repo, "one", {"claims/b.txt": "row b\n"})
    git(repo, "merge", "-q", "--no-ff", "-m", "merge", "agent/one")
    report = lab_land.remove_worktree(repo, "one")
    assert report["status"] == "removed" and report["verdict"]["test"] == "ancestor"
    assert gone(repo, work, "agent/one")


def test_worktree_listing_reports_each_agent_branch(repo):
    agent_worktree(repo, "done")
    work = agent_worktree(repo, "open", {"claims/b.txt": "row b\n"})
    (work / "scratch.txt").write_text("untracked\n")
    rows = {row["name"]: row for row in lab_land.agent_branches(repo)}
    assert rows["done"]["landed"] and rows["done"]["dirty"] is False
    assert not rows["open"]["landed"] and rows["open"]["dirty"] is True


def test_removing_an_unknown_branch_fails(repo):
    with pytest.raises(lab_land.LandingError, match="no branch agent/none"):
        lab_land.remove_worktree(repo, "none")


def test_a_worktree_with_paths_beyond_windows_max_path_is_removed(repo):
    """Regression: a prepared worktree holds Lake packages deeper than 260 characters, and
    Git for Windows without core.longpaths dropped the registration but left the tree."""
    work = agent_worktree(repo, "deep")
    # The extended-length prefix lets Python create what Git must then delete.
    prefix = "\\\\?\\" if sys.platform == "win32" else ""
    deep = work / ".build"
    deep.mkdir()
    for part in ("d" * 60, "e" * 60, "f" * 60, "g" * 60):
        deep /= part
        os.mkdir(prefix + str(deep))
    with open(prefix + str(deep / "package.olean"), "w") as handle:
        handle.write("ignored build output\n")
    assert len(str(deep)) > 260
    assert lab_land.remove_worktree(repo, "deep")["status"] == "removed"
    assert gone(repo, work, "agent/deep")
