"""The state of the lab in one read-only call.

    python tools/lab.py status

Reports main's head and whether its checkout is clean, every agent branch with its
worktree, dirty flag and landed verdict, the journal size against its limit, the
`lab.py check` summary with warnings grouped by message, and each paper's local
version against its latest recorded deposit. It writes no files and changes no Git
state: Git status runs without optional locks, so not even the index is refreshed.
"""
from __future__ import annotations

import argparse
from collections import Counter, defaultdict
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "tools"))
sys.path.insert(0, str(ROOT / "src"))
from lab_land import agent_branches, changes, checkout_of, git  # noqa: E402
from research.knowledge import JOURNAL, JOURNAL_LIMIT, journal_entries  # noqa: E402


def main_state(root: Path, onto: str = "main") -> dict:
    head, subject = git(root, "log", "-1", "--format=%H%x00%s", onto).split("\0", 1)
    holder = checkout_of(root, onto)
    return {"branch": onto, "head": head, "subject": subject,
            "checkout": str(holder) if holder else None,
            "clean": not changes(holder) if holder else None}


def journal(root: Path) -> dict:
    path = root / JOURNAL
    count = journal_entries(path.read_text(encoding="utf-8")) if path.exists() else 0
    return {"path": JOURNAL, "entries": count, "limit": JOURNAL_LIMIT, "within_limit": count <= JOURNAL_LIMIT}


def summarise_issues(issues: list[dict]) -> dict:
    """Counts by severity, and each distinct message with the paths that report it."""
    counts = Counter(i["severity"] for i in issues)
    grouped = {"error": defaultdict(list), "warning": defaultdict(list)}
    for issue in issues:
        grouped[issue["severity"]][issue["error"]].append(issue.get("path"))

    def ordered(groups):
        return {message: sorted(paths, key=str)
                for message, paths in sorted(groups.items(), key=lambda kv: (-len(kv[1]), kv[0]))}

    return {"status": "failed" if counts["error"] else "ok", "errors": counts["error"],
            "warnings": counts["warning"], "error_groups": ordered(grouped["error"]),
            "warning_groups": ordered(grouped["warning"])}


def check(root: Path) -> dict:
    from research_catalog import ResearchCatalogue
    return summarise_issues(ResearchCatalogue(root).issues())


def papers(root: Path) -> list[dict]:
    """Local version from the paper's build configuration; latest deposit from the
    metadata the builder carries forward from the recorded deposit."""
    from build_paper import Paper, letters
    rows = []
    for letter in letters(root):
        paper = Paper(letter, root)
        meta = json.loads((root / paper.METADATA).read_text(encoding="utf-8"))
        latest = meta.get("latest_deposit") or {}
        rows.append({"paper": letter.upper(), "local": paper.version, "deposited": latest.get("version"),
                     "deposit_doi": latest.get("doi"),
                     "ahead": latest.get("version") != paper.version})
    return rows


def status(root: Path = ROOT, onto: str = "main", *, with_check: bool = True,
           with_papers: bool = True) -> dict:
    report = {"main": main_state(root, onto), "agents": agent_branches(root, onto),
              "journal": journal(root)}
    if with_check:
        report["check"] = check(root)
    if with_papers:
        report["papers"] = papers(root)
    return report


def main(argv: list[str]) -> int:
    parser = argparse.ArgumentParser(prog="lab.py status", description=__doc__,
                                     formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--onto", default="main")
    parser.add_argument("--no-check", action="store_true", help="skip the lab.py check summary")
    args = parser.parse_args(argv)
    print(json.dumps(status(ROOT, args.onto, with_check=not args.no_check), ensure_ascii=False, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
