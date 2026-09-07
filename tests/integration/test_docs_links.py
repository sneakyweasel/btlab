"""Check internal Markdown links in README and docs."""

from __future__ import annotations

import re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
LINK = re.compile(r"\[[^\]]+\]\(([^)]+)\)")


def _targets() -> list[Path]:
    files = [ROOT / "README.md", ROOT / "docs" / "README.md", ROOT / "AGENTS.md"]
    files.extend(sorted((ROOT / "docs").rglob("*.md")))
    files.append(ROOT / "formal" / "README.md")
    capsule = ROOT / "attacks" / "juggler"
    if capsule.is_dir():
        files.extend(sorted(capsule.rglob("*.md")))
    return files


def test_internal_markdown_links_resolve():
    missing: list[str] = []
    seen: set[Path] = set()
    for path in _targets():
        if path in seen or not path.exists():
            continue
        seen.add(path)
        text = path.read_text(encoding="utf-8")
        for raw in LINK.findall(text):
            target = raw.split()[0].strip("<>")
            if target.startswith(("http://", "https://", "mailto:", "#")):
                continue
            href, _, _anchor = target.partition("#")
            if not href:
                continue
            resolved = (path.parent / href).resolve()
            if not resolved.exists():
                missing.append(f"{path.relative_to(ROOT)} -> {raw}")
    assert missing == []
