"""Which symbols carry more than one meaning, and where a reviewer would trip over it.

A symbol collision is only a defect when a reader can plausibly hold both meanings at once.
Two sections apart, with a fresh "write X for ..." at each site, is usually fine; the same
letter meaning two things inside one proof is not.  So this module does not just count symbols:
it locates *binding sites* -- the places where a symbol is introduced -- and reports collisions
ranked by how close together the bindings are.

Binding phrasings the manuscripts actually use, in order of reliability:

    write X for ... / writing X for ...      explicit, unambiguous
    let X = ... / put X = ... / set X = ...  explicit
    \\[ X = ... \\] or \\(X = ...\\)           a display or inline definition
    X denotes ... / X is the ...             prose

The output is advisory.  Deciding whether a collision is confusing is a judgement about the
argument, not something a regex settles, so ``main`` prints the evidence and the distance and
leaves the ranking to a reader.
"""

from __future__ import annotations

import io
import re
from collections import defaultdict
from pathlib import Path
from typing import Any, Iterable

ROOT = Path(__file__).resolve().parents[3]

PAPERS = {
    "A": ROOT / "docs" / "theory" / "juggler_finite_dynamics_note.md",
    "B": ROOT / "docs" / "theory" / "juggler_parity_discrepancy_note.md",
    "C": ROOT / "docs" / "theory" / "juggler_fate_almost_all_note.md",
}

# A symbol: one latin or greek letter, optionally primed, optionally subscripted.
SYM = r"[A-Za-z]|\\(?:alpha|beta|gamma|delta|theta|kappa|lambda|mu|rho|sigma|tau|phi|chi|psi|omega|Delta|Theta|Lambda|Sigma|Phi|Omega|varepsilon|varphi)"

BINDERS: tuple[tuple[str, str], ...] = (
    (r"[Ww]rit(?:e|ing)\s+\\\((%s)[^\\]*\\\)\s+for" % SYM, "write ... for"),
    (r"[Ll]et\s+\\\((%s)\s*=" % SYM, "let ... ="),
    (r"[Pp]ut\s+\\\((%s)\s*=" % SYM, "put ... ="),
    (r"[Ss]et\s+\\\((%s)\s*=" % SYM, "set ... ="),
    (r"[Dd]efine\s+\\\((%s)" % SYM, "define"),
    (r"\\\((%s)(?:_\{?\w+\}?)?\s*=\s*[^\\]" % SYM, "inline ="),
)

SECTION = re.compile(r"^#{2,3}\s+(.*)$", re.MULTILINE)


def sections(text: str) -> list[tuple[int, str]]:
    """(line number, heading) for every section heading."""
    out = []
    for m in SECTION.finditer(text):
        out.append((text[: m.start()].count("\n") + 1, m.group(1).strip()))
    return out


def section_of(line: int, heads: list[tuple[int, str]]) -> str:
    name = "(front matter)"
    for ln, h in heads:
        if ln <= line:
            name = h
        else:
            break
    return name


def bindings(text: str) -> dict[str, list[dict[str, Any]]]:
    """symbol -> the sites where the text appears to bind it."""
    heads = sections(text)
    lines = text.splitlines()
    found: dict[str, list[dict[str, Any]]] = defaultdict(list)
    for pattern, kind in BINDERS:
        for m in re.finditer(pattern, text):
            sym = m.group(1)
            line = text[: m.start()].count("\n") + 1
            ctx = lines[line - 1].strip()
            found[sym].append({
                "line": line, "kind": kind, "section": section_of(line, heads),
                "context": ctx[:150],
            })
    for sites in found.values():
        sites.sort(key=lambda s: s["line"])
    return found


def _norm(ctx: str) -> str:
    """Collapse a context line to something comparable, to spot repeat bindings."""
    return re.sub(r"\s+", " ", re.sub(r"[^A-Za-z0-9=+\-*/^_{}()\\ ]", "", ctx)).strip()


def collisions(text: str, min_sites: int = 2) -> list[dict[str, Any]]:
    """Symbols bound at sites whose contexts differ, ranked by how close they are."""
    out = []
    for sym, sites in bindings(text).items():
        if len(sites) < min_sites:
            continue
        distinct: list[dict[str, Any]] = []
        seen: set[str] = set()
        for s in sites:
            key = _norm(s["context"])[:60]
            if key not in seen:
                seen.add(key)
                distinct.append(s)
        if len(distinct) < 2:
            continue
        span = min(b["line"] - a["line"]
                   for a, b in zip(distinct, distinct[1:]))
        out.append({
            "symbol": sym,
            "n_sites": len(sites),
            "n_distinct": len(distinct),
            "closest_gap": span,
            "same_section": len({s["section"] for s in distinct}) < len(distinct),
            "sites": distinct,
        })
    out.sort(key=lambda r: (not r["same_section"], r["closest_gap"]))
    return out


def report(name: str, path: Path, top: int = 12) -> Iterable[str]:
    text = io.open(path, encoding="utf-8").read()
    rows = collisions(text)
    yield "Paper %s -- %d symbols bound at two or more distinguishable sites" % (name, len(rows))
    for r in rows[:top]:
        flag = "SAME SECTION" if r["same_section"] else "%d lines apart" % r["closest_gap"]
        yield "  %-14s %-16s %d sites" % (r["symbol"], flag, r["n_distinct"])
        for s in r["sites"][:4]:
            yield "      L%-6d %-26s %s" % (s["line"], s["section"][:26], s["context"][:88])


MATH = re.compile(r"\\\((.*?)\\\)|\\\[(.*?)\\\]", re.DOTALL)
LETTER = re.compile(r"(?<![A-Za-z\\])([A-Za-z])(?![A-Za-z])")


def letter_census(text: str) -> dict[str, int]:
    """How often each single latin letter appears as a standalone math symbol."""
    counts: dict[str, int] = defaultdict(int)
    for m in MATH.finditer(text):
        body = m.group(1) or m.group(2) or ""
        for sym in LETTER.findall(body):
            counts[sym] += 1
    return dict(counts)


def letter_sites(text: str, letter: str) -> list[tuple[int, str]]:
    """(line, math span) for every standalone use of ``letter`` as a math symbol."""
    pat = re.compile(r"(?<![A-Za-z\\])" + re.escape(letter) + r"(?![A-Za-z])")
    out = []
    for m in MATH.finditer(text):
        body = m.group(1) or m.group(2) or ""
        if pat.search(body):
            out.append((text[: m.start()].count("\n") + 1, " ".join(body.split())[:100]))
    return out


def free_letters(text: str, cap: int = 0) -> list[str]:
    """Letters used at most ``cap`` times -- candidates for a rename target."""
    counts = letter_census(text)
    return [c for c in "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ"
            if counts.get(c, 0) <= cap]


def census_report(name: str, path: Path) -> Iterable[str]:
    counts = letter_census(io.open(path, encoding="utf-8").read())
    yield "Paper %s letter census (standalone math symbols)" % name
    yield "  unused: %s" % ("".join(free_letters(io.open(path, encoding="utf-8").read())) or "none")
    rare = sorted((v, k) for k, v in counts.items() if v <= 12)
    yield "  rare:   %s" % ", ".join("%s:%d" % (k, v) for v, k in rare[:20])


def main() -> None:
    for name, path in PAPERS.items():
        for line in census_report(name, path):
            print(line)
        print()


if __name__ == "__main__":
    main()
