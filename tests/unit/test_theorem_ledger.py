"""Theorem ledger paths must exist; markdown must match the JSON."""

from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "tools"))

from render_theorem_ledger import HEADER, TAGS, check_tags  # noqa: E402

ROOT = Path(__file__).resolve().parents[2]
JSON_PATH = ROOT / "docs" / "theory" / "theorem_ledger.json"
LEAN_VERIFIED = "EXACT — LEAN VERIFIED"


def _entries() -> list[dict]:
    return json.loads(JSON_PATH.read_text(encoding="utf-8"))


def test_ledger_ids_are_unique():
    ids = [row["id"] for row in _entries()]
    assert ids
    assert len(ids) == len(set(ids))


def test_ledger_required_fields():
    required = ("id", "tag", "statement", "source", "lean", "tests")
    for row in _entries():
        for key in required:
            assert key in row, f"{row.get('id')}: missing {key}"
        source = ROOT / str(row["source"])
        assert source.is_file(), f"{row['id']}: missing source {row['source']}"


def test_ledger_test_paths_exist():
    for row in _entries():
        tests = row.get("tests") or []
        assert tests, f"{row['id']}: tests must be a non-empty list"
        for rel in tests:
            path = ROOT / rel
            assert path.is_file(), f"{row['id']}: missing test {rel}"


def test_ledger_lean_paths_exist_when_required():
    for row in _entries():
        lean = str(row.get("lean") or "").strip()
        if not lean:
            assert row["tag"] != LEAN_VERIFIED, f"{row['id']}: LEAN VERIFIED needs a lean path"
            continue
        path = ROOT / "formal" / lean
        if not path.exists():
            path = ROOT / lean
        assert path.exists(), f"{row['id']}: missing lean {lean}"
        if row["tag"] == LEAN_VERIFIED:
            assert path.is_file() or path.is_dir(), f"{row['id']}: lean path is not a file or dir"


def test_ledger_tags_are_in_the_fixed_vocabulary():
    assert check_tags(_entries()) == []


def test_documented_tags_match_the_whitelist():
    for tag in TAGS:
        assert f"`{tag}`" in HEADER, f"{tag} is missing from the rendered tag list"
    readme = (ROOT / "docs" / "README.md").read_text(encoding="utf-8")
    for tag in TAGS:
        assert tag in readme, f"{tag} is missing from docs/README.md"


def test_ledger_markdown_is_generated():
    script = ROOT / "tools" / "render_theorem_ledger.py"
    result = subprocess.run(
        [sys.executable, str(script), "--check"],
        cwd=ROOT,
        check=False,
        capture_output=True,
        text=True,
    )
    assert result.returncode == 0, result.stdout + result.stderr


def test_decl_when_present_names_a_declaration_in_the_rows_own_file():
    """The ``decl`` field is the join the ``lean`` file pointer cannot make.

    A row naming a declaration that is not in its file is worse than a row naming none:
    it reads as a resolved claim while pointing somewhere else.
    """
    import re

    for row in _entries():
        decl = row.get("decl")
        if not decl:
            continue
        lean = str(row.get("lean") or "").strip()
        assert lean.endswith(".lean"), f"{row['id']}: decl needs a file, not {lean!r}"
        text = (ROOT / "formal" / lean).read_text(encoding="utf-8")
        pattern = rf"^\s*(?:theorem|lemma|def|abbrev|instance|structure)\s+{re.escape(decl)}\b"
        assert re.search(pattern, text, re.MULTILINE), f"{row['id']}: {decl} not in {lean}"


def test_lean_trust_is_recorded_wherever_a_declaration_is_named():
    """``EXACT — LEAN VERIFIED`` does not distinguish kernel from ``native_decide``.

    Paper A's Section 1.2 states that boundary in prose; a row that names its declaration
    can carry it as data, so the tag stops having two meanings.
    """
    for row in _entries():
        if row.get("decl"):
            assert row.get("lean_trust") in {"kernel", "compiler", "open"}, row["id"]
