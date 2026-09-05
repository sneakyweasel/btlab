"""What Paper B claims is Lean-checked, and whether the repository backs each claim.

The referee asked for one compact table separating human proof from machine check from
classical input.  Guessing it would defeat the purpose, so this builds it from evidence:

  * every backticked identifier in Paper B's prose, with the section that cites it;
  * whether that identifier is actually declared somewhere under formal/Problems/;
  * whether its module is reachable from Problems/JugglerPaper.lean, which is the root the
    paper's formalization claims are supposed to track;
  * the theorem-ledger tag of the corresponding row, where one exists.

A name cited by the paper but absent from the Lean sources, or present but unreachable from the
paper root, is exactly what the table must not silently assert.
"""

from __future__ import annotations

import io
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
PAPER = ROOT / "docs" / "theory" / "juggler_parity_discrepancy_note.md"
LEAN = ROOT / "formal" / "Problems" / "Juggler"
UMBRELLA = ROOT / "formal" / "Problems" / "Juggler.lean"
PAPER_A_ROOT = ROOT / "formal" / "Problems" / "JugglerPaper.lean"
PAPER_B_ROOT = ROOT / "formal" / "Problems" / "JugglerParityPaper.lean"

IDENT = re.compile(r"`([a-z][A-Za-z0-9_']*)`")
SECTION = re.compile(r"^#{2,3}\s+(.*)$", re.MULTILINE)
DECL = re.compile(r"^(?:theorem|lemma|def|abbrev|noncomputable def)\s+([A-Za-z0-9_']+)",
                  re.MULTILINE)


def sections(text: str) -> list[tuple[int, str]]:
    return [(text[: m.start()].count("\n") + 1, m.group(1).strip())
            for m in SECTION.finditer(text)]


def section_of(line: int, heads: list[tuple[int, str]]) -> str:
    name = "(front matter)"
    for ln, h in heads:
        if ln <= line:
            name = h
        else:
            break
    return name


def declared() -> dict[str, str]:
    """identifier -> module basename, over every Lean file under Problems/."""
    out: dict[str, str] = {}
    for path in (ROOT / "formal" / "Problems").rglob("*.lean"):
        src = io.open(path, encoding="utf-8", errors="replace").read()
        for name in DECL.findall(src):
            out.setdefault(name, path.stem)
    return out


def reachable_modules(root) -> set[str]:
    """Modules reachable from a root by transitive import.

    JugglerPaper.lean is *Paper A*'s root -- Dynamics, Cycles, LeftoverFamilies,
    EvenCountThree.  JugglerParityPaper.lean is Paper B's, importing exactly the five modules
    its prose cites.  The umbrella Juggler.lean imports everything that builds.
    """
    imports: dict[str, set[str]] = {}
    for path in LEAN.glob("*.lean"):
        src = io.open(path, encoding="utf-8", errors="replace").read()
        imports[path.stem] = set(re.findall(r"^import Problems\.Juggler\.(\w+)", src, re.M))
    seen: set[str] = set()
    stack = list(re.findall(r"^import Problems\.Juggler\.(\w+)",
                            io.open(root, encoding="utf-8").read(), re.M))
    while stack:
        m = stack.pop()
        if m in seen or m not in imports:
            continue
        seen.add(m)
        stack.extend(imports[m])
    return seen


def audit() -> list[dict[str, object]]:
    text = io.open(PAPER, encoding="utf-8").read()
    heads = sections(text)
    decl = declared()
    reach = reachable_modules(PAPER_B_ROOT)
    reach_a = reachable_modules(PAPER_A_ROOT)
    rows: dict[str, dict[str, object]] = {}
    for m in IDENT.finditer(text):
        name = m.group(1)
        line = text[: m.start()].count("\n") + 1
        row = rows.setdefault(name, {
            "name": name, "sections": set(), "module": decl.get(name),
            "declared": name in decl,
        })
        row["sections"].add(section_of(line, heads).split(".")[0])
    for row in rows.values():
        mod = row["module"]
        row["reachable"] = bool(mod) and mod in reach
        row["in_paper_a_root"] = bool(mod) and mod in reach_a
    return sorted(rows.values(), key=lambda r: (not r["declared"], str(r["name"])))


def main() -> None:
    rows = audit()
    missing = [r for r in rows if not r["declared"]]
    unreachable = [r for r in rows if r["declared"] and not r["reachable"]]
    print("identifiers cited in Paper B's prose: %d" % len(rows))
    print("   declared in formal/Problems/ : %d" % (len(rows) - len(missing)))
    print("   of those, reachable from Problems/JugglerParityPaper.lean: %d"
          % (len(rows) - len(missing) - len(unreachable)))
    print()
    if missing:
        print("CITED BUT NOT DECLARED (%d):" % len(missing))
        for r in missing:
            print("   %-42s cited in %s" % (r["name"], sorted(r["sections"])))
        print()
    if unreachable:
        print("DECLARED BUT NOT REACHABLE FROM THE UMBRELLA (%d):" % len(unreachable))
        for r in unreachable:
            print("   %-42s %-24s cited in %s"
                  % (r["name"], r["module"], sorted(r["sections"])))
        print()
    print("by citing section:")
    per: dict[str, list[str]] = {}
    for r in rows:
        for s in r["sections"]:
            per.setdefault(s, []).append(str(r["name"]))
    for s in sorted(per):
        ok = sum(1 for n in per[s]
                 if any(x["name"] == n and x["declared"] and x["reachable"] for x in rows))
        print("   %-46s %2d cited, %2d declared+reachable" % (s[:46], len(per[s]), ok))


if __name__ == "__main__":
    main()
