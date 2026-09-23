"""The generated Juggler branch index is current and complete."""

from __future__ import annotations

from research.juggler_sequence.branch_index import _decision, check_index
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
        if "aliases" not in row or "nk_clusters" not in row:
            missing.append(f"{row['id']}: missing lookup fields")
    assert missing == [], missing[:20]


def test_show_cycle_gap_baker():
    from research.juggler_sequence.branch_index import format_show, show_row

    row = show_row("cycle_gap_baker")
    assert row is not None
    assert row["decision"] == "CLOSE"
    assert row["probe"]
    assert row["test"]
    assert row["dossier"]
    assert "baker" in row["aliases"]
    text = format_show(row)
    assert "cycle_gap_baker" in text
    assert "baker" in text


def test_search_hardy_hits_floor_hardy():
    from research.juggler_sequence.branch_index import search_rows

    hits = search_rows("hardy")
    ids = {row["id"] for row in hits}
    assert "rate_free_floor_hardy" in ids


def test_multiple_obstructions_remain_searchable_for_one_branch():
    from research.juggler_sequence.branch_index import parse_nk_clusters, search_rows

    clusters = parse_nk_clusters("## First barrier\njuggler_example\n"
                                 "## Separate boundary\njuggler_example\n")
    assert clusters["example"] == ["First barrier", "Separate boundary"]
    row = {"id": "example", "nk_clusters": clusters["example"]}
    assert search_rows("separate boundary", {"branches": [row]}) == [row]


def test_modular_probe_keeps_its_lean_associations():
    from research.juggler_sequence.branch_index import show_row

    row = show_row("paper_b_audit")
    assert "formal/Problems/Juggler/MasterIdentity.lean" in row["lean"]


def test_render_new_branch_uses_template_and_path_constants():
    from research.juggler_sequence.branch_index import render_new_branch

    texts = render_new_branch("foo_bar")
    assert "DATA_ROOT" in texts["probe"]
    assert 'DATA_DIR = DATA_ROOT / "foo_bar"' in texts["probe"]
    assert "juggler_foo_bar.md" in texts["test"]
    assert "Already killed by?" in texts["dossier"]
    assert "foo_bar" in texts["dossier"]


def test_render_new_branch_rejects_bad_ids():
    from research.juggler_sequence.branch_index import render_new_branch

    for stem in ("Foo", "foo-bar", "1abc", ""):
        try:
            render_new_branch(stem)
        except ValueError:
            continue
        raise AssertionError(stem)


def test_write_new_branch_refuses_existing():
    from research.juggler_sequence.branch_index import write_new_branch

    try:
        write_new_branch("accelerated")
    except FileExistsError:
        return
    raise AssertionError("expected FileExistsError")


def test_search_is_case_insensitive():
    from research.juggler_sequence.branch_index import search_rows

    assert search_rows("BAKER")
    assert search_rows("baker")[0]["id"] == search_rows("BAKER")[0]["id"]


def test_decision_is_the_word_stated_first_not_the_first_in_the_tuple():
    """The bug this guards mislabelled 17 dossiers, 13 of them livelier than the text.

    `_decision` used to return the first match in _DECISIONS order ('PROMOTE', 'PARK',
    'CLOSE'), so a section opening **CLOSE** and mentioning a PARK floor further down
    indexed as PARK, and one mentioning PROMOTE anywhere indexed as PROMOTE. The first
    three cases below return the tuple-order answer under the old code and the stated
    verdict under the new one.
    """
    closed_then_parks = """## Decision

**CLOSE**. The falsifier fired. It rests on a PARK floor.
"""
    assert _decision(closed_then_parks) == "CLOSE"

    closed_then_promotes = """## Decision

**CLOSE** the attack. Do not PROMOTE it again.
"""
    assert _decision(closed_then_promotes) == "CLOSE"

    parked_then_promoted = """## Decision

**PARK** (branch) / **PROMOTE** (depth-one lemma).
"""
    assert _decision(parked_then_promoted) == "PARK"

    single = """## Decision

**PROMOTE**. Worth the branch.
"""
    assert _decision(single) == "PROMOTE"

    none_stated = """## Decision

No verdict yet.
"""
    assert _decision(none_stated) is None
    assert _decision("## Problem" + chr(10) + chr(10) + "No decision section at all." + chr(10)) is None

    # the section ends at the next heading: a later one cannot supply the verdict
    bounded = """## Decision

**CLOSE**.

## Next steps

PROMOTE something else entirely.
"""
    assert _decision(bounded) == "CLOSE"
