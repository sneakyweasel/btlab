"""A theorem index over the Lean sources: what exists, what it rests on, who checks it.

The laboratory already has two halves of an index and no join between them.  The theorem
ledger carries 597 curated rows -- a natural-language statement, a tag, a test -- but its
``lean`` field names a *file*, never a declaration, so no row points at a theorem.  The Lean
sources carry ~3,900 declarations with no readable statement and no tag.

This builds the join, plus the edge the ledger has never had: the module graph, so a change
can be asked what it breaks before it is made.  That question -- "who depends on this?" -- is
the one two agents editing the same corpus keep getting wrong.

Trust is recorded per declaration rather than assumed:

  ``kernel``    checked by Lean's kernel
  ``compiler``  rests on ``native_decide``; the compiler is trusted, not the kernel
  ``open``      carries a ``sorry``

Usage::

    python tools/formalpedia.py build          # write the index
    python tools/formalpedia.py search <text>  # statements and names matching text
    python tools/formalpedia.py show <name>    # one declaration
    python tools/formalpedia.py impact <path>  # modules that would be rebuilt by a change
"""

from __future__ import annotations

import argparse
import io
import json
import re
import sys
from collections import defaultdict
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parents[1]
FORMAL = ROOT / "formal"
LEDGER = ROOT / "docs" / "theory" / "theorem_ledger.json"
INDEX = ROOT / "data" / "research" / "formalpedia" / "index.json"

DECL = re.compile(
    r"^(?P<kind>theorem|lemma|def|abbrev|instance|structure)\s+"
    r"(?P<name>[A-Za-z_][A-Za-z0-9_'!?.]*)",
    re.MULTILINE,
)
IMPORT = re.compile(r"^import\s+([A-Za-z_][A-Za-z0-9_.']*)", re.MULTILINE)

LIBRARIES = ("Core", "Representation", "Operators", "Problems", "BTCalculus")
"""The lean_lib roots from formal/lakefile.toml; an import outside them is Mathlib or std."""


def sources() -> list[Path]:
    """Every Lean file of the laboratory itself -- never the 12 GB of .lake build output."""
    out: list[Path] = []
    for lib in LIBRARIES:
        out.extend(sorted((FORMAL / lib).rglob("*.lean")))
        top = FORMAL / f"{lib}.lean"
        if top.is_file():
            out.append(top)
    return out


def module_of(path: Path) -> str:
    return ".".join(path.relative_to(FORMAL).with_suffix("").parts)


def _docstring(text: str, start: int) -> str:
    """The ``/-- ... -/`` block immediately above a declaration, if there is one.

    Immediately: nothing but whitespace may sit between the closing ``-/`` and the
    declaration, and the block must be the last one opened.  A regex reaching backwards for
    any earlier ``/--`` attaches one theorem's prose to every theorem below it.
    """
    head = text[:start].rstrip()
    if not head.endswith("-/"):
        return ""
    opened = head.rfind("/--")
    if opened == -1:
        return ""
    body = head[opened + 3: -2]
    if "-/" in body:
        return ""
    return " ".join(body.split())


def _trust(body: str) -> str:
    if re.search(r"\bsorry\b", body):
        return "open"
    if "native_decide" in body:
        return "compiler"
    return "kernel"


def declarations(path: Path) -> list[dict[str, Any]]:
    text = io.open(path, encoding="utf-8").read()
    hits = list(DECL.finditer(text))
    out: list[dict[str, Any]] = []
    for i, m in enumerate(hits):
        end = hits[i + 1].start() if i + 1 < len(hits) else len(text)
        out.append(
            {
                "name": m.group("name"),
                "kind": m.group("kind"),
                "module": module_of(path),
                "file": str(path.relative_to(ROOT)).replace("\\", "/"),
                "line": text[: m.start()].count("\n") + 1,
                "doc": _docstring(text, m.start()),
                "trust": _trust(text[m.start(): end]),
            }
        )
    return out


def imports(path: Path, known: set[str]) -> list[str]:
    """Internal imports only: an edge to a module this repository actually defines."""
    text = io.open(path, encoding="utf-8").read()
    return sorted({m.group(1) for m in IMPORT.finditer(text) if m.group(1) in known})


def ledger_by_file() -> dict[str, list[dict[str, str]]]:
    """Ledger rows keyed by the file their ``lean`` field names, normalised to repo paths."""
    if not LEDGER.is_file():
        return {}
    rows = json.load(io.open(LEDGER, encoding="utf-8"))
    out: dict[str, list[dict[str, str]]] = defaultdict(list)
    for row in rows:
        ref = row.get("lean")
        if not isinstance(ref, str) or not ref.endswith(".lean"):
            continue
        key = "formal/" + ref.lstrip("/")
        out[key].append(
            {"id": row["id"], "tag": row["tag"], "statement": row.get("statement", "")}
        )
    return dict(out)


def build() -> dict[str, Any]:
    paths = sources()
    known = {module_of(p) for p in paths}
    by_file = ledger_by_file()
    decls: list[dict[str, Any]] = []
    modules: dict[str, dict[str, Any]] = {}
    for path in paths:
        rel = str(path.relative_to(ROOT)).replace("\\", "/")
        found = declarations(path)
        for d in found:
            d["ledger"] = [r["id"] for r in by_file.get(rel, [])]
        decls.extend(found)
        modules[module_of(path)] = {
            "file": rel,
            "imports": imports(path, known),
            "declarations": len(found),
            "ledger": by_file.get(rel, []),
        }
    trust: dict[str, int] = defaultdict(int)
    for d in decls:
        trust[d["trust"]] += 1
    return {
        "modules": modules,
        "declarations": decls,
        "totals": {
            "modules": len(modules),
            "declarations": len(decls),
            "trust": dict(trust),
            "declarations_with_a_ledger_row": sum(1 for d in decls if d["ledger"]),
            "ledger_rows_naming_a_file": sum(len(v) for v in by_file.values()),
        },
    }


def dependents(index: dict[str, Any]) -> dict[str, list[str]]:
    """Reverse the import graph: module -> modules that import it, directly."""
    rev: dict[str, list[str]] = defaultdict(list)
    for name, data in index["modules"].items():
        for dep in data["imports"]:
            rev[dep].append(name)
    return {k: sorted(v) for k, v in rev.items()}


def transitive(rev: dict[str, list[str]], start: str) -> list[str]:
    seen: set[str] = set()
    stack = list(rev.get(start, []))
    while stack:
        cur = stack.pop()
        if cur in seen:
            continue
        seen.add(cur)
        stack.extend(rev.get(cur, []))
    return sorted(seen)


def load() -> dict[str, Any]:
    if not INDEX.is_file():
        sys.exit("no index; run: python tools/formalpedia.py build")
    return json.load(io.open(INDEX, encoding="utf-8"))


def _resolve(index: dict[str, Any], target: str) -> str | None:
    """Accept a module name, a repo path, or a path fragment."""
    if target in index["modules"]:
        return target
    needle = target.replace("\\", "/")
    for name, data in index["modules"].items():
        if data["file"] == needle or data["file"].endswith("/" + needle.lstrip("/")):
            return name
    return None


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(description="A theorem index over the Lean sources.")
    sub = ap.add_subparsers(dest="cmd", required=True)
    sub.add_parser("build", help="rebuild the index")
    p = sub.add_parser("search", help="declarations whose name or docstring matches")
    p.add_argument("text")
    p.add_argument("--limit", type=int, default=20)
    p = sub.add_parser("show", help="one declaration by exact name")
    p.add_argument("name")
    p = sub.add_parser("impact", help="modules rebuilt by a change to this module or file")
    p.add_argument("target")
    args = ap.parse_args(argv)

    if args.cmd == "build":
        index = build()
        INDEX.parent.mkdir(parents=True, exist_ok=True)
        INDEX.write_text(json.dumps(index, indent=2, sort_keys=True) + "\n", encoding="utf-8")
        t = index["totals"]
        print(f"{t['declarations']} declarations in {t['modules']} modules")
        print(f"  trust: {t['trust']}")
        print(f"  declarations under a ledger row: {t['declarations_with_a_ledger_row']}")
        return 0

    index = load()

    if args.cmd == "search":
        needle = args.text.lower()
        hits = [d for d in index["declarations"]
                if needle in d["name"].lower() or needle in d["doc"].lower()]
        for d in hits[: args.limit]:
            print(f"{d['name']}  [{d['trust']}]  {d['file']}:{d['line']}")
            if d["doc"]:
                print(f"    {d['doc'][:110]}")
        print(f"-- {len(hits)} matching")
        return 0

    if args.cmd == "show":
        for d in index["declarations"]:
            if d["name"] == args.name:
                print(json.dumps(d, indent=2))
                return 0
        print(f"no declaration named {args.name}", file=sys.stderr)
        return 1

    module = _resolve(index, args.target)
    if module is None:
        print(f"no module or file matching {args.target}", file=sys.stderr)
        return 1
    rev = dependents(index)
    direct, all_ = rev.get(module, []), transitive(rev, module)
    print(f"{module} ({index['modules'][module]['declarations']} declarations)")
    print(f"  imported directly by {len(direct)}, transitively by {len(all_)}")
    for name in all_:
        mark = "*" if name in direct else " "
        print(f"   {mark} {name}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
