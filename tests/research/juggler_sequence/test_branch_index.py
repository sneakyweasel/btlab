"""The generated Juggler branch index is current and complete."""

from __future__ import annotations

from pathlib import Path

from research.juggler_sequence.branch_index import check_index
from research.juggler_sequence.lean_paths import CAPSULE_ROOT, INDEX_PATH, REPO_ROOT


def test_agent_guide_exists():
    assert (CAPSULE_ROOT / "AGENT.md").is_file()


def test_index_file_exists():
    assert INDEX_PATH.is_file()


def test_index_is_current_and_complete():
    problems = check_index()
    assert problems == [], problems[:20]


def test_every_branch_row_has_the_triad():
    from research.juggler_sequence.branch_index import build_index

    missing: list[str] = []
    for row in build_index()["branches"]:
        if row["kind"] != "branch":
            continue
        for key in ("probe", "test", "dossier", "decision"):
            if not row.get(key):
                missing.append(f"{row['id']}:{key}")
        for rel in (row["probe"], row["test"], row["dossier"]):
            path = REPO_ROOT / rel
            if not path.is_file():
                missing.append(f"missing {rel}")
    assert missing == [], missing[:20]
