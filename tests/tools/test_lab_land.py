"""Landing: one branch at a time, shared views regenerated, main moved only by fast-forward."""
from __future__ import annotations

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
from pathlib import Path
rows = sorted(p.read_text().strip() for p in Path('claims').glob('*.txt'))
Path('docs/theory').mkdir(parents=True, exist_ok=True)
Path('docs/theory/theorem_ledger.md').write_text('\\n'.join(rows) + '\\n')
"""
CHECK = """
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


@pytest.fixture
def repo(tmp_path):
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
