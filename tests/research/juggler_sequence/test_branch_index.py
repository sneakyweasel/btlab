"""The generated Juggler branch index is current and complete."""

from __future__ import annotations

from research.juggler_sequence.branch_index import check_index
from research.juggler_sequence.lean_paths import (
    BRANCHES_ROOT,
    CAPSULE_ROOT,
    DATA_ROOT,
    DOCS_RESEARCH,
    DOCS_THEORY,
    FORMAL_DIR,
    INDEX_PATH,
    JUGGLER_DIR,
    REPO_ROOT,
    repo_root,
)


def test_repo_root_walker_finds_pyproject():
    assert repo_root() == REPO_ROOT
    assert (REPO_ROOT / "pyproject.toml").is_file()


def test_path_constants_point_at_the_live_trees():
    assert DATA_ROOT.is_dir()
    assert DOCS_RESEARCH.is_dir()
    assert DOCS_THEORY.is_dir()
    assert BRANCHES_ROOT.is_dir()
    assert FORMAL_DIR.is_dir()
    assert JUGGLER_DIR.is_dir()


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
