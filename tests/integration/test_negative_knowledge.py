"""The negative-knowledge index cites every recorded failure identifier."""

from __future__ import annotations

import json
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
INDEX = ROOT / "docs" / "negative_knowledge.md"
LEDGER = ROOT / "docs" / "theory" / "theorem_ledger.json"
CONJECTURES = ROOT / "conjectures" / "refuted"
PROBLEMS = ROOT / "docs" / "problems"


def _index_text() -> str:
    return INDEX.read_text(encoding="utf-8")


def _refuted_conjecture_ids() -> set[str]:
    ids: set[str] = set()
    for path in CONJECTURES.glob("*.json"):
        data = json.loads(path.read_text(encoding="utf-8"))
        ids.add(data["id"])
    return ids


def _refuted_ledger_ids() -> set[str]:
    rows = json.loads(LEDGER.read_text(encoding="utf-8"))
    return {row["id"] for row in rows if row.get("tag") == "REFUTED"}


def _close_dossier_stems() -> set[str]:
    stems: set[str] = set()
    for path in PROBLEMS.glob("*.md"):
        if path.name == "TEMPLATE.md":
            continue
        text = path.read_text(encoding="utf-8")
        parts = re.split(r"^## Decision$", text, flags=re.M)
        if len(parts) < 2:
            continue
        section = re.split(r"^## ", parts[1], flags=re.M)[0]
        if "CLOSE" in section:
            stems.add(path.stem)
    return stems


def test_index_exists():
    assert INDEX.is_file()


def test_every_refuted_conjecture_is_cited():
    text = _index_text()
    missing = sorted(i for i in _refuted_conjecture_ids() if i not in text)
    assert missing == [], f"conjectures/refuted ids missing from index: {missing}"


def test_every_refuted_ledger_row_is_cited():
    text = _index_text()
    missing = sorted(i for i in _refuted_ledger_ids() if i not in text)
    assert missing == [], f"REFUTED ledger ids missing from index: {missing}"


def test_every_close_dossier_is_cited():
    text = _index_text()
    missing = sorted(s for s in _close_dossier_stems() if s not in text)
    assert missing == [], f"CLOSE dossier stems missing from index: {missing}"
