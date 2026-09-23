"""Canonical obstruction records shared by laboratory discovery tools.

The Markdown index is navigation; the records own the detailed arguments.
Readers never write an index or follow links outside the selected checkout.
"""
from __future__ import annotations

from pathlib import Path
import re

INDEX = "docs/negative_knowledge.md"
DIRECTORY = "docs/negative_knowledge"


def negative_paths(root: Path) -> list[Path]:
    """Return the index and all local records, including newly added records."""
    root = root.resolve()
    candidates = [root / INDEX, *sorted((root / DIRECTORY).glob("*.md"))]
    return [p for p in candidates if p.is_file() and p.resolve().is_relative_to(root)]


def heading_anchor(heading: str) -> str:
    """GitHub-style anchors for the existing plain-text Markdown headings."""
    return re.sub(r"[^\w\- ]", "", heading.lower()).replace(" ", "-")


def negative_entries(root: Path, texts: dict[str, str] | None = None) -> list[dict]:
    """Read records with exact source locations; accept an inline index in fixtures.

    Passing already-read texts keeps catalogue records in the same snapshot.
    Nested headings remain inside their obstruction, so its scope is not lost.
    """
    if texts is None:
        texts = {p.relative_to(root.resolve()).as_posix(): p.read_text(encoding="utf-8")
                 for p in negative_paths(root)}
    records = sorted(p for p in texts if p.startswith(DIRECTORY + "/") and p.endswith(".md"))
    result = []
    for file in records or ([INDEX] if INDEX in texts else []):
        text = texts[file]
        pattern = r"^# (.+)$" if records else r"^## (.+)$"
        headings = list(re.finditer(pattern, text, re.M))
        for n, match in enumerate(headings):
            end = headings[n + 1].start() if n + 1 < len(headings) else len(text)
            result.append({"id": Path(file).stem if records else heading_anchor(match[1]),
                           "file": file, "line": text.count("\n", 0, match.start()) + 1,
                           "heading": match[1], "body": text[match.end():end].strip()})
    return result


def negative_text(root: Path) -> str:
    """Full evidence text for coverage checks and the branch cluster reader."""
    return "\n\n".join("## " + p["heading"] + "\n\n" + p["body"] for p in negative_entries(root))


def render_negative_index(root: Path, entries: list[dict] | None = None) -> str:
    """Render a compact directory while retaining the former section anchors."""
    entries = negative_entries(root) if entries is None else entries
    intro = """# Negative knowledge

Search these canonical obstruction records before proposing a direction. Each
record retains the precise scope, evidence and links to its dossiers or proof
maps; a closed method is not a proof that the research problem is impossible.
Older records can be superseded: follow their linked current proof sources.

Use `python tools/lab.py search \"your question\" --kind obstruction`, then
`python tools/lab.py context obstruction/<id> --section obstructions`.
Edit the relevant record under `docs/negative_knowledge/`; regenerate this index
with `python tools/research_memory.py`. Do not duplicate its argument in a journal.

<!-- Generated directory; the anchors preserve existing inbound links. -->

"""
    def anchors(part):
        headings = [part["heading"], *re.findall(r"^#{2,6} (.+)$", part["body"], re.M)]
        return "".join(f'<a id="{heading_anchor(h)}"></a>' for h in headings)
    return intro + "\n".join(
        f'- {anchors(p)}'
        f' [{p["heading"]}](negative_knowledge/{Path(p["file"]).name})'
        for p in entries) + "\n"


def negative_errors(root: Path, texts: dict[str, str]) -> list[dict]:
    """Reject missing/duplicate records and a stale generated directory."""
    records = {p: body for p, body in texts.items() if p.startswith(DIRECTORY + "/") and p.endswith(".md")}
    if not records and "<!-- Generated directory;" not in texts.get(INDEX, ""):
        return []
    errors = []
    anchors = set()
    for file, body in records.items():
        headings = re.findall(r"^# (.+)$", body, re.M)
        if len(headings) != 1:
            errors.append({"path": file, "error": "Obstruction record must have exactly one title"})
        for heading in headings:
            anchor = heading_anchor(heading)
            if anchor in anchors:
                errors.append({"path": file, "error": "Duplicate obstruction heading: " + heading})
            anchors.add(anchor)
    if texts.get(INDEX) != render_negative_index(root, negative_entries(root, texts)):
        errors.append({"path": INDEX, "error": "Stale obstruction index; run python tools/research_memory.py"})
    return errors


def journal_errors(text: str) -> list[dict]:
    """Keep chronology bounded; durable evidence belongs in canonical records."""
    if len(re.findall(r"^## ", text, re.M)) > 12:
        return [{"path": "docs/research_journal.md", "error":
                 "Journal exceeds twelve entries; consolidate older results into canonical records"}]
    return []
