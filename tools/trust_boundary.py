# Historical Paper B audit: the 2026-09-04 snapshot is not the conditional publication.
"""What Paper B claims is Lean-checked, and whether the repository backs each claim.

The referee asked for one compact table separating human proof from machine check from
classical input.  Guessing it would defeat the purpose, so this builds it from evidence:

  * every backticked identifier in Paper B's prose, with the section that cites it;
  * whether that identifier is actually declared somewhere under formal/Problems/;
  * whether its module is reachable from Problems/JugglerParityPaper.lean, which is the root
    this paper's formalization claims are supposed to track (JugglerPaper.lean is Paper A's);
  * the theorem-ledger tag of the corresponding row, where one exists.

A name cited by the paper but absent from the Lean sources, or present but unreachable from the
paper root, is exactly what the table must not silently assert.
"""

from __future__ import annotations

import io
import re
from collections import defaultdict
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
PAPER = ROOT / "docs" / "theory" / "juggler_parity_discrepancy_note_2026_09_04.md"
PAPER_A = ROOT / "docs" / "theory" / "juggler_finite_dynamics_note.md"
LEAN = ROOT / "formal" / "Problems" / "Juggler"
UMBRELLA = ROOT / "formal" / "Problems" / "Juggler.lean"
PAPER_A_ROOT = ROOT / "formal" / "Problems" / "JugglerPaper.lean"
PAPER_B_ROOT = ROOT / "formal" / "Problems" / "JugglerParityPaper.lean"

# Lean 4.33.1: Init/Meta/Defs.lean, isIdFirst/isIdRest. These are
# regular identifiers, not arbitrary Unicode words: e.g. lambda is notation.
# Escaped identifiers and macro-generated declarations are outside this source
# index's supported syntax; the executable Lean audit remains authoritative.
_LETTERLIKE = (
    r"\u03b1-\u03ba\u03bc-\u03c9\u0391-\u039f\u03a1-\u03a2\u03a4-\u03a9"
    r"\u03ca-\u03fb\u1f00-\u1ffe\u2100-\u214f\U0001d49c-\U0001d59f"
    r"\u00c0-\u00d6\u00d8-\u00f6\u00f8-\u00ff\u0100-\u017f"
)
_ID_FIRST = rf"[A-Za-z_{_LETTERLIKE}]"
_ID_REST = rf"[A-Za-z0-9_'!?{_LETTERLIKE}\u2080-\u2089\u2090-\u209c\u1d62-\u1d6a\u2c7c]"
_ID_SEGMENT = rf"{_ID_FIRST}{_ID_REST}*"
QUALIFIED_IDENT = rf"{_ID_SEGMENT}(?:\.{_ID_SEGMENT})*"
IDENT = re.compile(rf"`({QUALIFIED_IDENT})`")
IDENTIFIER_TOKEN = re.compile(rf"(?<!{_ID_REST})(?<!\.){QUALIFIED_IDENT}(?!{_ID_REST}|\.)")
SECTION = re.compile(r"^#{2,3}\s+(.*)$", re.MULTILINE)
DECL = re.compile(
    r"^(?:@\[[^\]]*\]\s*)*(?P<modifiers>(?:(?:private|protected|noncomputable|unsafe|partial|public)\s+)*)"
    r"(?:theorem|lemma|def|abbrev|structure|inductive)\s+"
    rf"(?P<name>{QUALIFIED_IDENT})(?=$|[\s:({{\[]|\.\{{)")
SCOPE = re.compile(
    r"^(?P<modifiers>(?:(?:noncomputable|public|private)\s+)*)"
    rf"(?P<kind>namespace|section|end)(?:\s+(?P<name>{QUALIFIED_IDENT}))?\s*$")
MODIFIERS_ONLY = re.compile(r"^(?:(?:private|protected|noncomputable|unsafe|partial|public)\s*)+$")
ATTRIBUTES_ONLY = re.compile(r"^(?:@\[[^\]]*\]\s*)+$")
CHAR_LITERAL = re.compile(r"'(?:[^'\\\r\n]|\\[^\r\n])'")
RAW_STRING = re.compile(r'r(#+)"')


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


def source_commands(src: str) -> list[str]:
    """Mask nested Lean comments and strings, retaining line boundaries.

    This is a source index, not a Lean proof checker. The exact resolved names
    are independently checked by the executable Lean dependency audit.
    """
    chars = list(src)
    depth, quoted, i = 0, False, 0
    while i < len(src):
        pair = src[i:i + 2]
        if depth:
            if pair == "/-":
                chars[i:i + 2] = "  "
                depth += 1
                i += 2
                continue
            if pair == "-/":
                chars[i:i + 2] = "  "
                depth -= 1
                i += 2
                continue
            if src[i] != "\n":
                chars[i] = " "
        elif quoted:
            if src[i] == "\\" and i + 1 < len(src):
                chars[i] = " "
                if src[i + 1] != "\n":
                    chars[i + 1] = " "
                i += 2
                continue
            if src[i] == '"':
                quoted = False
            if src[i] != "\n":
                chars[i] = " "
        elif pair == "/-":
            chars[i:i + 2] = "  "
            depth = 1
            i += 2
            continue
        elif pair == "--":
            while i < len(src) and src[i] != "\n":
                chars[i] = " "
                i += 1
            continue
        elif src[i] == "'" and (i == 0 or not (re.fullmatch(_ID_REST, src[i - 1]) or src[i - 1] == ".")):
            # Apostrophes in declaration names are not character delimiters.
            literal = CHAR_LITERAL.match(src, i)
            if literal:
                chars[i:literal.end()] = " " * (literal.end() - i)
                i = literal.end()
                continue
        elif src[i] == "r" and (i == 0 or not re.fullmatch(_ID_REST, src[i - 1])):
            raw = RAW_STRING.match(src, i)
            if raw:
                closing = '"' + raw.group(1)
                end = src.find(closing, raw.end())
                stop = len(src) if end < 0 else end + len(closing)
                for j in range(i, stop):
                    if src[j] != "\n":
                        chars[j] = " "
                i = stop
                continue
        elif src[i] == '"':
            chars[i] = " "
            quoted = True
        i += 1
    return "".join(chars).splitlines()


def identifier_tokens(text: str) -> list[str]:
    """Complete regular Lean identifier spellings, without prefix truncation."""
    return [match.group(0) for match in IDENTIFIER_TOKEN.finditer(text)]


def scoped_source_commands(src: str) -> list[tuple[int, str, str, bool]]:
    """Non-scope commands as (line, masked text, namespace, private scope).

    This keeps the lexical context shared by declaration and reference indexes.
    It does not elaborate aliases, open namespaces, notation, or generated names.
    """
    namespace, private_scope = "", False
    stack: list[tuple[str, bool]] = []
    pending_modifiers = ""
    out = []
    for line, command in enumerate(source_commands(src), 1):
        command = command.strip()
        if not command or ATTRIBUTES_ONLY.fullmatch(command):
            continue
        if MODIFIERS_ONLY.fullmatch(command):
            pending_modifiers += command + " "
            continue
        command = pending_modifiers + command
        pending_modifiers = ""
        scope = SCOPE.fullmatch(command)
        if scope is None and re.match(
                r"^(?:(?:noncomputable|public|private)\s+)*(?:namespace|section|end)(?=\s|$)", command):
            raise ValueError(f"Unsupported Lean scope at line {line}: {command}")
        if scope:
            kind, name = scope["kind"], scope["name"]
            modifiers = scope["modifiers"].split()
            if kind == "end":
                if stack:
                    namespace, private_scope = stack.pop()
            else:
                stack.append((namespace, private_scope))
                if "private" in modifiers:
                    private_scope = True
                elif "public" in modifiers:
                    private_scope = False
                if kind == "namespace" and name:
                    namespace = (name.removeprefix("_root_.") if name.startswith("_root_.")
                                 else ".".join(filter(None, (namespace, name))))
            continue
        out.append((line, command, namespace, private_scope))
    return out


def source_declarations(src: str) -> list[tuple[str, int]]:
    """Public regular declaration identities, including dotted namespaces.

    Standalone modifiers apply across line breaks; section visibility and
    anonymous sections are restored independently of the namespace spelling.
    Unsupported identifier syntax is never indexed as a shorter valid name.
    """
    out = []
    for line, command, namespace, private_scope in scoped_source_commands(src):
        match = DECL.match(command)
        if match:
            modifiers = match["modifiers"].split()
            if "private" in modifiers or (private_scope and "public" not in modifiers):
                continue
            name = match["name"]
            full = (name.removeprefix("_root_.") if name.startswith("_root_.")
                    else ".".join(filter(None, (namespace, name))))
            out.append((full, line))
    return out


def declaration_index() -> dict[str, list[dict[str, object]]]:
    """All source locations by qualified name; no filesystem-first selection."""
    out: dict[str, list[dict[str, object]]] = defaultdict(list)
    formal = ROOT / "formal"
    for path in sorted((formal / "Problems").rglob("*.lean")):
        module = ".".join(path.relative_to(formal).with_suffix("").parts)
        for full, line in source_declarations(path.read_text(encoding="utf-8")):
            out[full].append({"qualified_name": full, "module_name": module,
                              "module": path.stem, "line": line})
    return dict(out)


def resolve_name(name: str, index: dict[str, list[dict[str, object]]]) -> list[dict[str, object]]:
    """Resolve exact absolute names or relative suffixes, retaining ambiguities."""
    if name.startswith(("_root_.", "Problems.")):
        return index.get(name.removeprefix("_root_."), [])
    if "." in name and name in index:
        return index[name]
    return [row for full, rows in index.items()
            if full == name or full.endswith("." + name) for row in rows]


def repository_namespace_suffixes(index: dict[str, list[dict[str, object]]]) -> set[str]:
    """Recognize a repository namespace even when the cited final name is misspelled."""
    namespaces: set[str] = set()
    for full in index:
        parts = full.split(".")
        for end in range(1, len(parts)):
            for start in range(end):
                namespaces.add(".".join(parts[start:end]))
    return namespaces

def declared() -> dict[str, str]:
    """Legacy short-name/module view; ambiguous short names are excluded."""
    index = declaration_index()
    aliases: dict[str, list[dict[str, object]]] = defaultdict(list)
    for full, rows in index.items():
        aliases[full].extend(rows)
        short = full.rsplit(".", 1)[-1]
        if short != full:
            aliases[short].extend(rows)
    return {name: str(rows[0]["module"]) for name, rows in aliases.items() if len(rows) == 1}


def reachable_module_names(root: Path, *, formal_root: Path | None = None) -> set[str]:
    """Repository import closure, including declarations in the root itself."""
    formal = ROOT / "formal" if formal_root is None else formal_root
    try:
        root_module = ".".join(root.relative_to(formal).with_suffix("").parts)
    except ValueError:
        root_module = ""
    seen: set[str] = {root_module} if root_module else set()
    stack = [root]
    while stack:
        path = stack.pop()
        for command in source_commands(path.read_text(encoding="utf-8")):
            imported = re.match(r"^\s*(?:public\s+)?import\s+(.+)$", command)
            if not imported:
                continue
            # Lean permits several modules on one import command.
            for module in imported.group(1).split():
                if not re.fullmatch(r"Problems\.[\w.]+", module) or module in seen:
                    continue
                seen.add(module)
                dependency = formal / (module.replace(".", "/") + ".lean")
                if dependency.is_file():
                    stack.append(dependency)
    return seen

def reachable_modules(root: Path) -> set[str]:
    """Legacy module-basename view for the historical table consumers."""
    return {module.rsplit(".", 1)[-1] for module in reachable_module_names(root)}


def audit(paper: Path = PAPER, root: Path | None = None) -> list[dict[str, object]]:
    """Rows for one paper.  Defaults to Paper B, so existing callers are unchanged.

    Pass ``paper=PAPER_A, root=PAPER_A_ROOT`` for Paper A.  ``reachable`` is measured
    against ``root``; ``in_paper_a_root`` is always measured against Paper A's barrel.
    """
    if root is None:
        root = PAPER_B_ROOT
    text = io.open(paper, encoding="utf-8").read()
    heads = sections(text)
    index = declaration_index()
    namespace_suffixes = repository_namespace_suffixes(index)
    reach = reachable_module_names(root)
    reach_a = reachable_module_names(PAPER_A_ROOT)
    rows: dict[str, dict[str, object]] = {}
    for m in IDENT.finditer(text):
        name = m.group(1)
        matches = resolve_name(name, index)
        if "." in name:
            # Module/file citations and external-library/probe names are not
            # claims that this repository declares a Lean constant.
            module_file = ROOT / "formal" / (name.replace(".", "/") + ".lean")
            if name.endswith(".lean") or module_file.is_file():
                continue
            prefix = name.removeprefix("_root_.").rsplit(".", 1)[0]
            if (not matches and not name.startswith(("_root_.", "Problems.", "Juggler."))
                    and prefix not in namespace_suffixes):
                continue
        elif not name[0].islower() and not matches:
            continue
        line = text[: m.start()].count("\n") + 1
        resolved = matches[0] if len(matches) == 1 else {}
        row = rows.setdefault(name, {
            "name": name, "sections": set(), "module": resolved.get("module"),
            "module_name": resolved.get("module_name"),
            "qualified_name": resolved.get("qualified_name"),
            "declared": len(matches) == 1,
            "ambiguous": len(matches) > 1,
            "candidates": sorted(str(row["qualified_name"]) for row in matches),
        })
        row["sections"].add(section_of(line, heads).split(".")[0])
    for row in rows.values():
        mod = row["module_name"]
        row["reachable"] = bool(mod) and mod in reach
        row["in_paper_a_root"] = bool(mod) and mod in reach_a
    return sorted(rows.values(), key=lambda r: (not r["declared"], str(r["name"])))



STANDARD_DEPENDENCIES = frozenset({"propext", "Classical.choice", "Quot.sound"})
_DEPENDENCY_RECORD = re.compile(
    rf"'(?P<name>{QUALIFIED_IDENT})' "
    r"(?:depends on axioms:\s*\[(?P<dependencies>[^\]]*)\]|does not depend on any axioms)"
)


def dependency_requests(source: str) -> list[str]:
    """Read exact regular names requested by the audit's #print axioms commands."""
    requests = []
    pattern = re.compile(rf"#print\s+axioms\s+({QUALIFIED_IDENT})\s*$")
    for command in source_commands(source):
        if not re.match(r"\s*#print\s+axioms\b", command):
            continue
        match = pattern.fullmatch(command.strip())
        if match is None:
            raise ValueError(f"Unsupported dependency request: {command.strip()}")
        requests.append(match.group(1))
    if len(requests) != len(set(requests)):
        raise ValueError("Repeated dependency request")
    return requests


def parse_dependency_records(raw: str) -> dict[str, frozenset[str]]:
    """Parse every Lean dependency record; fail on duplicates or unparsed output."""
    records: dict[str, frozenset[str]] = {}
    end = 0
    for match in _DEPENDENCY_RECORD.finditer(raw):
        if raw[end:match.start()].strip():
            raise ValueError(f"Unparsed dependency output: {raw[end:match.start()].strip()}")
        name = match["name"]
        if name in records:
            raise ValueError(f"Repeated dependency record: {name}")
        body = (match["dependencies"] or "").strip()
        dependencies = [part.strip() for part in body.split(",")] if body else []
        if any(re.fullmatch(QUALIFIED_IDENT, part) is None for part in dependencies):
            raise ValueError(f"Malformed dependency set for {name}: {body}")
        if len(dependencies) != len(set(dependencies)):
            raise ValueError(f"Repeated dependency in {name}")
        records[name] = frozenset(dependencies)
        end = match.end()
    if raw[end:].strip():
        raise ValueError(f"Unparsed dependency output: {raw[end:].strip()}")
    return records


def validate_dependency_records(raw: str, expected: set[str],
                                exceptions: dict[str, set[str]] | None = None
                                ) -> dict[str, frozenset[str]]:
    """Exact request coverage and exact named exceptions to the standard-only rule.

    Every nonstandard dependency must be explicitly listed for its consumer;
    even an authorized exception cannot conceal an additional dependency.
    """
    records = parse_dependency_records(raw)
    if set(records) != expected:
        raise ValueError(f"Dependency coverage mismatch: missing={sorted(expected - records.keys())}, "
                         f"extra={sorted(records.keys() - expected)}")
    exceptions = exceptions or {}
    if not exceptions.keys() <= expected:
        raise ValueError("Dependency exceptions contain an unrequested declaration")
    for name, dependencies in records.items():
        actual = dependencies - STANDARD_DEPENDENCIES
        allowed = frozenset(exceptions.get(name, set()))
        if actual != allowed:
            raise ValueError(f"Unexpected dependencies for {name}: "
                             f"expected extras={sorted(allowed)}, actual extras={sorted(actual)}")
    return records

def main() -> None:
    import argparse
    ap = argparse.ArgumentParser(description="Trust boundary for Paper A or Paper B.")
    ap.add_argument("--paper", choices=["a", "b"], default="b")
    args = ap.parse_args()
    if args.paper == "a":
        rows = audit(PAPER_A, PAPER_A_ROOT)
        label, rootname = "Paper A", "Problems/JugglerPaper.lean"
    else:
        rows = audit()
        label, rootname = "Paper B", "Problems/JugglerParityPaper.lean"
    ambiguous = [r for r in rows if r["ambiguous"]]
    missing = [r for r in rows if not r["declared"]]
    unreachable = [r for r in rows if r["declared"] and not r["reachable"]]
    print("identifiers cited in %s's prose: %d" % (label, len(rows)))
    print("   declared in formal/Problems/ : %d" % (len(rows) - len(missing)))
    print("   of those, reachable from %s: %d"
          % (rootname, len(rows) - len(missing) - len(unreachable)))
    print()
    if ambiguous:
        print("AMBIGUOUS CITATIONS (use a qualified declaration name):")
        for r in ambiguous:
            print("   %s: %s" % (r["name"], ", ".join(r["candidates"])))
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
    if ambiguous:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
