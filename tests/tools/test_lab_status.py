"""`lab.py status`: one read-only report of the lab's state."""
from __future__ import annotations

from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "tools"))
sys.path.insert(0, str(ROOT / "tests/tools"))
import lab_status  # noqa: E402
from research.knowledge import journal_errors  # noqa: E402
from test_lab_land import agent_worktree, commit, git, repo  # noqa: E402,F401


def test_warnings_are_grouped_by_message_with_their_paths():
    changed = "Changed source byte size; use --hashes to check declared text identity: tools/lab.py"
    issues = [{"severity": "warning", "path": "b.research.json", "error": changed},
              {"severity": "warning", "path": "a.research.json", "error": changed},
              {"severity": "warning", "path": "x.md", "error": "No explicit branch decision found"},
              {"severity": "error", "error": "Invalid/duplicate research id: "}]
    summary = lab_status.summarise_issues(issues)
    assert (summary["status"], summary["errors"], summary["warnings"]) == ("failed", 1, 3)
    assert summary["warning_groups"] == {changed: ["a.research.json", "b.research.json"],
                                         "No explicit branch decision found": ["x.md"]}
    assert list(summary["warning_groups"])[0] == changed, "the largest group comes first"
    assert summary["error_groups"] == {"Invalid/duplicate research id: ": [None]}


def test_the_journal_count_is_the_one_check_enforces(tmp_path):
    journal = tmp_path / "docs/research_journal.md"
    journal.parent.mkdir(parents=True)
    for entries, within in ((12, True), (13, False)):
        text = "# Journal\n\n" + "".join(f"## 2026-09-{i:02d} entry\n\ntext\n\n" for i in range(1, entries + 1))
        journal.write_text(text + "### not an entry\n", encoding="utf-8")
        report = lab_status.journal(tmp_path)
        assert (report["entries"], report["limit"], report["within_limit"]) == (entries, 12, within)
        assert bool(journal_errors(text)) is not within


def snapshot(root: Path) -> dict[str, tuple[int, int]]:
    return {str(p.relative_to(root)): (p.stat().st_mtime_ns, p.stat().st_size)
            for p in root.rglob("*") if p.is_file()}


def test_status_reports_main_and_agents_and_writes_nothing(repo):
    agent_worktree(repo, "done")
    agent_worktree(repo, "open", {"claims/b.txt": "row b\n"})
    before = snapshot(repo)
    report = lab_status.status(repo, with_check=False, with_papers=False)
    assert snapshot(repo) == before
    assert report["main"]["head"] == git(repo, "rev-parse", "main") and report["main"]["clean"]
    assert {row["name"]: row["landed"] for row in report["agents"]} == {"done": True, "open": False}
    assert report["journal"]["entries"] == 0
    (repo / "notes.md").write_text("dirty\n")
    assert lab_status.status(repo, with_check=False, with_papers=False)["main"]["clean"] is False
