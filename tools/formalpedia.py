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
    python tools/formalpedia.py jev-propose    # ask Jev which theorem each unresolved row means
    python tools/formalpedia.py jev-calibrate  # score Jev on rows whose theorem is recorded
    python tools/formalpedia.py jev-coverage   # ask Jev whether recorded theorems cover their rows
"""

from __future__ import annotations

import argparse
import collections
import datetime
import hashlib
import io
import json
import random
import re
import sys
from collections import defaultdict
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path
from typing import Any, Callable

ROOT = Path(__file__).resolve().parents[1]
FORMAL = ROOT / "formal"
LEDGER = ROOT / "docs" / "theory" / "theorem_ledger.json"
INDEX = ROOT / "data" / "research" / "formalpedia" / "index.json"
DAG = ROOT / "data" / "research" / "formalpedia" / "dag.json"
PROPOSALS = ROOT / "data" / "research" / "formalpedia" / "decl_proposals.json"
REVIEW = ROOT / "docs" / "research" / "formalpedia_decl_review.md"
JEV = ROOT / "data" / "research" / "formalpedia" / "jev_verdicts.json"
COVERAGE = ROOT / "docs" / "research" / "formalpedia_coverage_review.md"

_ATTR = r"@\[[^\]]*\][ \t]*"
"""An attribute block in front of a declaration, on the declaration's own line.

Same line, deliberately.  An attribute written on the line *above* leaves the keyword at the
start of its own line, where the pattern already finds it; letting this group cross a newline
would move the match back onto the attribute and report every such declaration one line early.
"""

_MODIFIER = r"(?:private\s+|protected\s+|noncomputable\s+)*"

DECL = re.compile(
    rf"^[ \t]*(?:{_ATTR})*{_MODIFIER}"
    r"(?P<kind>theorem|lemma|def|abbrev|instance|structure)\s+"
    r"(?P<name>[A-Za-z_][A-Za-z0-9_'!?.]*)",
    re.MULTILINE,
)
"""Every declaration a file opens.  Run against :func:`blank_comments` output, never raw text.

Three forms were invisible here and each failed silently, which is the only way this index
fails.  ``@[simp] theorem foo`` -- 70 of them -- had no room for the attribute and were absent
from the index outright.  An indented declaration was unreachable because the pattern anchored
at ``^`` with nothing after it.  And the ``^`` anchor was simultaneously the only guard against
prose: ``formal/`` writes long docstrings, and a line wrapping so that ``theorem`` lands at
column 0 put six English words -- ``of``, ``at``, ``needs``, ``nothing`` -- into the index as
declarations.  Allowing indentation without blanking comments first adds a seventh.  So the two
changes are one change: the anchor stops carrying a job it was never doing on purpose, and
:func:`blank_comments` takes it over.
"""
IMPORT = re.compile(r"^import\s+([A-Za-z_][A-Za-z0-9_.']*)", re.MULTILINE)
IDENT = re.compile(r"[A-Za-z][A-Za-z0-9_']*_[A-Za-z0-9_']+")
"""A bare Lean identifier in prose.  Ledger rows name their theorems this way -- not in
backticks, which is why an early search for backticked names found none at all."""

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


def blank_comments(text: str) -> str:
    """Replace every comment byte with a space, keeping all offsets and newlines in place.

    Offsets are the point.  The declaration scan runs on this, while each declaration's
    docstring and trust are sliced out of the original text at the positions this reports,
    so a blanker that shortened anything would misreport every line after the first comment.

    Lean block comments nest -- ``/- outer /- inner -/ still outer -/`` -- so this scans
    rather than running the non-greedy ``/-.*?-/`` used elsewhere in this file, which closes
    such a comment at the inner ``-/`` and hands the tail back as if it were code.  String
    literals are honoured too, so a ``--`` inside one opens nothing.
    """
    out = list(text)
    i, n, depth = 0, len(text), 0
    while i < n:
        if depth == 0 and text[i] == '"':
            i += 1
            while i < n and text[i] != '"':
                i += 2 if text[i] == "\\" else 1
            i += 1
        elif text.startswith("/-", i):
            depth += 1
            out[i] = out[i + 1] = " "
            i += 2
        elif depth and text.startswith("-/", i):
            depth -= 1
            out[i] = out[i + 1] = " "
            i += 2
        elif depth:
            if text[i] != "\n":
                out[i] = " "
            i += 1
        elif text.startswith("--", i):
            end = text.find("\n", i)
            end = n if end == -1 else end
            out[i:end] = " " * (end - i)
            i = end
        else:
            i += 1
    return "".join(out)


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


_DOCSTRING = re.compile(r"/--.*?-/", re.S)


def _trust(body: str) -> str:
    """Trust from the proof, not from the prose around it.

    Docstrings are stripped first.  A body runs to the next declaration, so a docstring
    that *mentions* the compiled-runtime tactic -- one recording that a scan was replaced
    by a structural proof, say -- used to mark the declaration above it compiler-trusted.
    That mislabels in both directions, and this field must not do that.
    """
    body = _DOCSTRING.sub(" ", body)
    if re.search(r"\bsorry\b", body):
        return "open"
    if "native_decide" in body:
        return "compiler"
    return "kernel"


def declares(text: str, name: str, kind: str = "theorem") -> bool:
    """Does `text` declare exactly `name` -- not merely something starting with it?

    519 of the 4,528 declaration names in this corpus are a proper prefix of another, because
    helper lemmas are named by extending their main theorem: `power_bound_compensated_contracts`
    and `power_bound_compensated_contracts_follows`, `power_bound_word` and
    `power_bound_word_strict`.  A guard written as ``f"theorem {name}" in text`` therefore still
    passes after its theorem is deleted, as long as one of those neighbours survives -- which is
    precisely the event such a guard exists to catch.

    It reads the same forms :data:`DECL` does, and for the same reason: this answers "is the
    theorem still here", so every form it cannot read reports a live theorem deleted.  It took
    a bare ``kind`` with room for neither an attribute nor a modifier, so ``@[simp] theorem f``
    and ``private theorem f`` both answered False.  The tail rejects ``!`` and ``?`` as well as
    word characters, since Lean admits all three in a name and ``foo`` must not match ``foo!``.
    """
    return re.search(
        rf"(?:^|\n)[ \t]*(?:{_ATTR})*{_MODIFIER}{kind}\s+{re.escape(name)}(?![A-Za-z0-9_'!?])",
        text,
    ) is not None


def declarations(path: Path) -> list[dict[str, Any]]:
    """Every declaration in one file: what it is called, where it sits, what checks it.

    The scan runs on comment-blanked text and the docstring and trust of each hit are sliced
    from the original at the same offsets -- so prose cannot be read as a declaration, while
    the prose *belonging* to a declaration is still read.
    """
    text = io.open(path, encoding="utf-8").read()
    hits = list(DECL.finditer(blank_comments(text)))
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



def lean_key(ref: object) -> str:
    """Repo-relative key for a ledger row's `lean` field, however it is spelled.

    The ledger spells it both ways: 421 rows give a path relative to `formal/`
    ("Problems/Juggler/X.lean") and 43 give it from the repository root
    ("formal/Problems/Juggler/X.lean"). Prepending "formal/" unconditionally turned the
    second spelling into "formal/formal/...", which matches no file, so those 43 rows
    resolved to zero declarations while every gate stayed green -- the index simply
    reported a smaller surface than the repository has.
    """
    text = str(ref or "").lstrip("/")
    return text if text.startswith("formal/") else "formal/" + text


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
        key = lean_key(ref)
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


def reachable(index: dict[str, Any]) -> dict[str, set[str]]:
    """Every module each module can reach through imports."""
    mods = index["modules"]
    out: dict[str, set[str]] = {}

    def walk(m: str) -> set[str]:
        if m in out:
            return out[m]
        out[m] = set()
        acc: set[str] = set()
        for dep in mods.get(m, {}).get("imports", []):
            acc.add(dep)
            acc |= walk(dep)
        out[m] = acc
        return acc

    for m in mods:
        walk(m)
    return out


PAPER_ROOTS = {
    "Paper A": "Problems.JugglerPaper",
    "Paper B": "Problems.JugglerParityPaper",
    "Paper C": "Problems.JugglerFatePaper",
}
"""The module each manuscript's formalization claims to track.

Reachability from these roots is what a trust sentence in a paper is actually about.  A
directory grep answers a different question -- `formal/Problems/Juggler/` holds modules no
paper imports -- and would let a `native_decide` land inside a paper's surface while the
count outside it stayed reassuring.
"""


_IDENT = re.compile(r"[A-Za-z_][A-Za-z0-9_'.]*")
_HEAD = re.compile(rf"(?:^|\n)[ \t]*(?:{_ATTR})*{_MODIFIER}"
                   r"(?:theorem|lemma|def|abbrev|instance)\s+([A-Za-z_][A-Za-z0-9_'!?.]*)")
"""Where each proof body starts, for the citation scan.  Carries :data:`DECL`'s alternation
because a head this cannot see is not a boundary: the body above it runs on through the
declaration into its neighbour, and picks up whatever the neighbour cites."""


def trust_closure(index: dict[str, Any]) -> set[str]:
    """Declarations that rest on ``native_decide``, following citation rather than syntax.

    ``_trust`` reads one proof body, so it answers "does this proof run the compiler" -- not
    "does this theorem depend on the compiler".  Those differ, and the gap is not academic:
    ``shortcutC_terminal_cycle`` is the term ``<shortcutC_one, shortcutC_two>`` and both halves
    are ``native_decide``, yet the body carries no such token and the label read ``kernel``.
    Inside Paper A, ``window_digit_cap`` cites ``window_digit_scan`` the same way.

    Edges are name occurrences in a comment-stripped proof body, which is why comments are
    stripped first: a docstring naming a compiled lemma is prose, not a dependency.  Two
    limits are worth stating rather than hiding.  Forty declaration names are not unique
    across the corpus, so a citation of a duplicated name taints every declaration sharing it;
    that is the conservative direction.  And a name occurring in a proof is evidence of use,
    not proof of it -- the exact graph lives in the ``.olean`` files, and reading those is a
    bigger job than this answers.
    """
    decls = index["declarations"]
    names = {d["name"] for d in decls}
    bodies: dict[tuple[str, str], str] = {}
    for path in sorted({d["file"] for d in decls}):
        # Blanked once, for both jobs: it keeps prose from opening a body, and it is the
        # comment strip this line already did -- minus the non-greedy `/-.*?-/` that used to
        # do it, which closes a nested comment early and hands the tail back as if it were a
        # proof. Comments must go either way: a docstring naming a compiled lemma is prose,
        # not a dependency.
        text = blank_comments(Path(path).read_text(encoding="utf-8"))
        heads = list(_HEAD.finditer(text))
        for i, m in enumerate(heads):
            end = heads[i + 1].start() if i + 1 < len(heads) else len(text)
            bodies[(path, m.group(1))] = text[m.end():end]

    cites: dict[tuple[str, str], set[str]] = {}
    for key, body in bodies.items():
        used = {t for t in _IDENT.findall(body) if t in names}
        used.discard(key[1])
        if used:
            cites[key] = used

    tainted = {d["name"] for d in decls if d["trust"] == "compiler"}
    changed = True
    while changed:
        changed = False
        for (_path, name), used in cites.items():
            if name not in tainted and used & tainted:
                tainted.add(name)
                changed = True
    return tainted


def paper_surface(index: dict[str, Any]) -> dict[str, Any]:
    """Per paper: the modules it reaches, and the proofs in them the kernel does not check."""
    reach = reachable(index)
    tainted = trust_closure(index)
    out: dict[str, Any] = {}
    for label, root in PAPER_ROOTS.items():
        if root not in index["modules"]:
            out[label] = {"root": root, "present": False}
            continue
        mods = reach.get(root, set()) | {root}
        inside = [d for d in index["declarations"] if d["module"] in mods]
        out[label] = {
            "root": root,
            "present": True,
            "modules": len(mods),
            "declarations": len(inside),
            "compiler_trusted": sorted(d["name"] for d in inside if d["trust"] == "compiler"),
            "compiler_dependent": sorted(d["name"] for d in inside if d["name"] in tainted),
            "open": sorted(d["name"] for d in inside if d["trust"] == "open"),
        }
    return out


def dag(index: dict[str, Any], ledger: list[dict[str, Any]]) -> dict[str, Any]:
    """The claim graph: modules that carry a ledger row, reduced to its essential edges.

    Edges are kept at module granularity on purpose.  Only 27 of 263 verified rows name
    their declaration, so a row-to-row edge would assert a dependency nobody has checked --
    file A importing file B says some theorem there may rest on some theorem here, not which.
    Transitive reduction is what makes the result readable: 894 edges carry the same
    information as 119, and the 119 are the ones a person can follow.
    """
    file_to_mod = {m["file"]: name for name, m in index["modules"].items()}
    rows: dict[str, list[str]] = defaultdict(list)
    for row in ledger:
        ref = row.get("lean")
        if isinstance(ref, str) and ref.endswith(".lean"):
            mod = file_to_mod.get(lean_key(ref))
            if mod:
                rows[mod].append(row["id"])

    reach = reachable(index)
    carriers = set(rows)
    edges = {m: {d for d in reach.get(m, set()) if d in carriers} for m in carriers}
    reduced: dict[str, list[str]] = {}
    for m, ds in edges.items():
        implied: set[str] = set()
        for d in ds:
            implied |= edges.get(d, set()) & ds
        reduced[m] = sorted(ds - implied)

    reach = reachable(index)
    serves = {
        label: (reach.get(root, set()) | {root}) if root in index["modules"] else set()
        for label, root in PAPER_ROOTS.items()
    }

    nodes = {}
    for m in sorted(carriers):
        data = index["modules"][m]
        trust = collections.Counter(
            d["trust"] for d in index["declarations"] if d["module"] == m
        )
        nodes[m] = {
            "file": data["file"],
            "declarations": data["declarations"],
            "ledger": sorted(rows[m]),
            "trust": dict(trust),
            "depends_on": reduced[m],
            "papers": sorted(label for label, mods in serves.items() if m in mods),
        }
    return {
        "granularity": "module",
        "nodes": nodes,
        "totals": {
            "nodes": len(nodes),
            "edges": sum(len(v) for v in reduced.values()),
            "edges_before_reduction": sum(len(v) for v in edges.values()),
            "ledger_rows_placed": sum(len(v) for v in rows.values()),
        },
    }


STOP = frozenset(
    "the a an of is are for and or to in on with by that this it its at as be has have if then"
    " every any no not all each one two from into under over than so which there their can does"
    " do was were but we lean theorem lemma proof proved shows gives same such only also both"
    " paper section".split()
)


def words(text: str) -> set[str]:
    """Content words of a sentence or an identifier, camel and snake pieces split alike."""
    text = re.sub(r"\\\(.*?\\\)", " ", text)
    out: set[str] = set()
    for raw in re.findall(r"[A-Za-z][A-Za-z0-9]*", text):
        for piece in re.findall(r"[A-Z]+(?![a-z])|[A-Z]?[a-z]+|\d+", raw) or [raw]:
            if len(piece) > 2 and piece.lower() not in STOP:
                out.add(piece.lower())
    return out


def row_decls(row: dict[str, Any]) -> list[str]:
    """The declarations a ledger row names, as a list, whether it names one or many.

    Most rows resolve to a single theorem and carry ``decl`` as a string. Some do not:
    ``J-cyclemin-walk-ostrowski-arithmetic`` is Paper A's certified-arithmetic inventory and
    names eighteen declarations, seventeen kernel-checked and one (``window_digit_scan``)
    compiler-trusted. A single string cannot describe that row without misreporting one side
    of the kernel boundary, so ``decl`` accepts a list and every consumer reads it through
    here.
    """
    decl = row.get("decl")
    if not decl:
        return []
    return [decl] if isinstance(decl, str) else list(decl)


def similarity(statement_words: set[str], decl: dict[str, Any]) -> float:
    other = words(decl["doc"]) | words(decl["name"])
    both = statement_words | other
    return len(statement_words & other) / len(both) if both else 0.0


def calibrate(index: dict[str, Any], ledger: list[dict[str, Any]]) -> dict[str, int]:
    """Score the scorer against every row whose answer is already recorded.

    Computed, never written down.  A hardcoded precision goes stale silently: this figure
    was quoted as 96% for twenty-five ticks after the calibration set had grown past the
    easy rows it was measured on, and it is now 86%.
    """
    by_file: dict[str, list[dict[str, Any]]] = defaultdict(list)
    for d in index["declarations"]:
        if d["kind"] in ("theorem", "lemma"):
            by_file[d["file"]].append(d)
    resolved = [r for r in ledger if len(row_decls(r)) == 1]
    fires = correct = 0
    for row in resolved:
        cands = by_file.get(lean_key(row.get("lean")), [])
        if len(cands) < 2:
            continue
        sw = words(row["statement"])
        ranked = sorted(cands, key=lambda d: similarity(sw, d), reverse=True)
        a, b = similarity(sw, ranked[0]), similarity(sw, ranked[1])
        if a >= 0.10 and a >= 1.5 * max(b, 1e-9):
            fires += 1
            correct += ranked[0]["name"] == row_decls(row)[0]
    return {"resolved": len(resolved), "fires": fires, "correct": correct}


def _queue(
    index: dict[str, Any], ledger: list[dict[str, Any]]
) -> list[tuple[dict[str, Any], list[dict[str, Any]] | None, list[dict[str, Any]]]]:
    """The rows the queue is about, each with the theorems and definitions its file offers.

    A declaration already claimed by a resolved row cannot be the answer to another: one
    theorem backs one claim, which the ledger's own collision test enforces.  Offering a
    taken declaration wastes a reviewer's judgement on an answer that would be rejected, so
    those are removed here, once, for the scorer and for Jev alike.  A row whose ``lean``
    field is not a file gets ``None`` in place of its theorems.
    """
    taken = {(lean_key(r.get("lean")), name) for r in ledger for name in row_decls(r)}

    by_file: dict[str, list[dict[str, Any]]] = defaultdict(list)
    defs_by_file: dict[str, list[dict[str, Any]]] = defaultdict(list)
    for d in index["declarations"]:
        if d["kind"] in ("theorem", "lemma"):
            by_file[d["file"]].append(d)
        elif d["kind"] in ("def", "abbrev"):
            defs_by_file[d["file"]].append(d)

    out: list[tuple[dict[str, Any], list[dict[str, Any]] | None, list[dict[str, Any]]]] = []
    for row in ledger:
        if row["tag"] != "EXACT — LEAN VERIFIED" or row.get("decl"):
            continue
        ref = row.get("lean")
        if not (isinstance(ref, str) and ref.endswith(".lean")):
            out.append((row, None, []))
            continue
        key = lean_key(ref)
        cands = [d for d in by_file.get(key, []) if (key, d["name"]) not in taken]
        out.append((row, cands, defs_by_file.get(key, [])))
    return out


def propose(
    index: dict[str, Any], ledger: list[dict[str, Any]], jev: dict[str, Any] | None = None
) -> dict[str, Any]:
    """Rank the declarations a still-unresolved row might mean.  Proposals, never answers.

    Measured against every resolved row: it fires on 49 and gets 42 right, so **86%**, about
    one wrong in seven.  An earlier figure of 96% came from a calibration set of 70 rows that
    was dominated by the easiest cases -- rows naming their theorem outright -- and overstated
    what the scorer does on the rows that are actually left.  The misses are sibling
    confusions: ``lsdZ_mul`` for ``D_mul``, ``q_eq_of_cube_mod`` for both ``qCubic_def`` and
    ``q_visible_mod``, ``cycleMin_length_of_gap`` for ``cycleMin_gap_transfer``.  One in seven
    is a queue a person reads, never a ledger write, which is why nothing here is applied.

    ``jev`` is the verdict record ``jev_propose`` writes.  ``None`` reads the committed one,
    so the CLI and the staleness gate see the same file; ``{}`` is the scorer alone.  A
    cached verdict is merged onto its row only while the row's statement and its file's
    offer are what Jev was asked about; otherwise it is marked stale and routes nothing.  A
    pick at or above ``JEV_REVIEW`` lists the row in the review digest whatever the scorer
    thought.  The candidates themselves stay the scorer's, untouched: Jev's answer is a
    field beside them, never a substitute for them.
    """
    verdicts = load_jev() if jev is None else jev
    prior = (verdicts or {}).get("rows", {})

    # ``composite`` counts only rows that *name* two or more of their own declarations, so it
    # is a lower bound and not the count.  Rows composite by content name nothing: "cmp3
    # translation, negation, and antisymmetry" is three theorems and no identifiers.  Two
    # heuristics over the statement text were calibrated against eleven rows classified by
    # reading -- equation conjunctions, then prose lists as well -- and caught 0 and 3 of the
    # eleven.  The eleven are composite for unrelated reasons (a noun list, two equations, an
    # inventory of Lean names, a claim beside its instance) and share no surface form, so the
    # true count is not obtainable without reading. Do not infer one from this field.
    out: list[dict[str, Any]] = []
    for row, cands, defs in _queue(index, ledger):
        ref = row.get("lean")
        if cands is None:
            out.append({"id": row["id"], "lean": ref, "why": "lean field is not a file",
                        "confidence": "low", "candidates": []})
            continue
        sw = words(row["statement"])
        ranked_all = sorted(cands, key=lambda d: similarity(sw, d), reverse=True)
        ranked = ranked_all[:3]
        scores = [round(similarity(sw, d), 3) for d in ranked]
        top = scores[0] if scores else 0.0
        second = scores[1] if len(scores) > 1 else 0.0
        # Definitions are ranked separately, never merged into the theorem list: admitting
        # them to one ranking displaces the true answer on 3 of the rows already resolved.
        # A row like BTA-x3-Q-def describes a `def`, and until now had no candidate at all.
        dcands = sorted(defs, key=lambda d: similarity(sw, d), reverse=True)[:2]
        named = [t for t in dict.fromkeys(IDENT.findall(row["statement"]))
                 if any(d["name"] == t for d in cands)]
        scorer = "review" if (top >= 0.10 and top >= 1.5 * max(second, 1e-9)) else "low"
        entry: dict[str, Any] = {
            "id": row["id"],
            "lean": ref,
            "statement": row["statement"][:400],
            "in_file": len(cands),
            "names_own": named,
            "composite": len(named) >= 2,
            "confidence": scorer,
            "candidates": [{"decl": d["name"], "score": s, "trust": d["trust"], "line": d["line"]}
                           for d, s in zip(ranked, scores)],
            "definitions": [{"decl": d["name"], "score": round(similarity(sw, d), 3),
                             "line": d["line"]} for d in dcands],
        }
        verdict = prior.get(row["id"])
        if verdict is not None:
            offer = ranked_all[:JEV_SHORTLIST]
            field = _jev_field(verdict, offer, jev_key(row, offer))
            confident = field["verdict"] == "pick" and field["confidence"] >= JEV_REVIEW
            field["routed"] = confident and scorer == "low"
            if confident:
                entry["confidence"] = "review"
            entry["jev"] = field
        out.append(entry)
    return {
        "note": "Proposals for human review. Calibration: 86% precision (42 of 49 fires) "
                "against all resolved rows. Nothing here has been written into the ledger.",
        "unresolved": len(out),
        "worth_reviewing": sum(1 for o in out if o["confidence"] == "review"),
        "composite": sum(1 for o in out if o.get("composite")),
        "jev": _jev_summary(out),
        "rows": out,
    }


JEV_REVIEW = 0.7
"""Jev's confidence at or above which a pick lists its row in the review digest.

A threshold is a policy, so it lives here and not in what the model returns.  Set from the
21 September 2026 sample of thirty resolved rows: sixteen of the twenty-one answers at or
above 0.7 named the recorded declaration, three of the nine below did.  ``jev-calibrate``
re-measures it, and the digest quotes the stored measurement rather than this sentence.
"""

JEV_SHORTLIST = 60
"""How many of a file's theorems Jev is offered, in the scorer's order.

Two files carry more than a hundred; capping keeps a request well inside the model's
budget for the state plus one question, and ``shortlist`` on each verdict records how many
were offered, so a miss can be told from a truncation.
"""

JEV_PROMPT = 1
"""Bumped whenever the instructions or the offer format change, so verdicts cached under an
older wording are asked again rather than reused."""

JEV_NONE = "none_of_these"

JEV_INSTRUCTIONS = (
    "The `claim` is an English statement from a theorem ledger. Each option is a Lean 4 "
    "declaration from the file the ledger names, given as its docstring (if any) followed by "
    "its statement header. Select the declaration whose formal statement is the same result "
    "as the claim: same objects, same hypotheses, same conclusion. A sibling lemma about a "
    "related but different object, a special case, or a helper used in the proof is not the "
    "answer."
)

JEV_NONE_TEXT = ("No listed declaration states this claim; the claim is broader, narrower, "
                 "or about something else.")

Ask = Callable[[dict[str, Any], str, dict[str, str | None]], dict[str, Any]]
"""What ``jev_propose`` and ``jev_calibrate`` call: ``ask(state, instructions, criteria)``
returning ``choice``, ``confidence``, ``probabilities``, ``model`` and ``input_tokens``.
``jev_ask`` builds the real one over the TypeSafe SDK; the tests pass a function."""


def _clip(text: str, limit: int) -> str:
    text = " ".join((text or "").split())
    return text if len(text) <= limit else text[: limit - 3] + "..."


def jev_shortlist(
    row: dict[str, Any], cands: list[dict[str, Any]], limit: int = JEV_SHORTLIST
) -> list[dict[str, Any]]:
    """The theorems Jev is offered for a row: the scorer's order, capped."""
    sw = words(row["statement"])
    return sorted(cands, key=lambda d: similarity(sw, d), reverse=True)[:limit]


def jev_question(
    row: dict[str, Any], offer: list[dict[str, Any]]
) -> tuple[dict[str, Any], dict[str, str | None]]:
    """The state and the criteria for one row: the claim, and each theorem as its docstring
    followed by its statement header, plus the option that none of them is the claim.

    The header is shown even when a docstring exists, for the reason the digest gives: a
    docstring can be true and still narrower than the row, and only the binders say so.
    """
    criteria: dict[str, str | None] = {}
    for d in offer:
        text = _clip(signature(d), 420)
        if d.get("doc"):
            text = _clip(d["doc"], 260) + " || " + text
        criteria[d["name"]] = text or None
    criteria[JEV_NONE] = JEV_NONE_TEXT
    state = {"claim": row["statement"], "lean_file": row.get("lean") or "",
             "ledger_id": row["id"]}
    return state, criteria


def jev_key(row: dict[str, Any], offer: list[dict[str, Any]]) -> str:
    """What a cached verdict is good for: this statement, this file, this offer, this wording.

    Names rather than docstrings, so a docstring edit in the file does not re-ask sixty
    rows; ``--refresh`` exists for that.  A changed statement, a theorem added to or claimed
    out of the file, or a bumped ``JEV_PROMPT`` all change the key, and the row is asked
    again.
    """
    payload = [JEV_PROMPT, row["statement"], row.get("lean") or "", [d["name"] for d in offer]]
    blob = json.dumps(payload, ensure_ascii=False).encode("utf-8")
    return hashlib.sha256(blob).hexdigest()[:16]


def jev_ask(model: str = "jev-latest", timeout: float = 60.0) -> Ask:
    """The real asker: one Choice question per call over the TypeSafe SDK.

    The SDK reads ``TYPESAFE_API_KEY`` from the environment.  Imported here rather than at
    the top so that the index, the scorer and the tests need neither the package nor a key.
    """
    try:
        from typesafe_sdk import Choice, TypeSafeClient
    except ImportError as exc:  # pragma: no cover - depends on the environment
        raise SystemExit(
            "typesafe-sdk is not installed: pip install typesafe-sdk, then set TYPESAFE_API_KEY"
        ) from exc
    client = TypeSafeClient(timeout=timeout)

    def ask(state: dict[str, Any], instructions: str,
            criteria: dict[str, str | None]) -> dict[str, Any]:
        response = client.system_one(
            state=state,
            questions={"pick": Choice(instructions=instructions, criteria=criteria)},
            model=model,
        )
        answer = response.choices["pick"]
        return {
            "choice": answer.choice,
            "confidence": float(answer.confidence),
            "probabilities": {k: float(v) for k, v in answer.probabilities.items()},
            "model": response.model,
            "input_tokens": int(response.usage.input_tokens),
        }

    return ask


def load_jev() -> dict[str, Any] | None:
    """The committed verdict record, or ``None`` when Jev has never been asked."""
    if not JEV.is_file():
        return None
    return json.load(io.open(JEV, encoding="utf-8"))


def _run(items: list[Any], fn: Callable[[Any], Any], workers: int) -> list[Any]:
    if workers > 1 and len(items) > 1:
        with ThreadPoolExecutor(workers) as pool:
            return list(pool.map(fn, items))
    return [fn(item) for item in items]


_EMPTY_TOTALS = {"answered": 0, "asked_now": 0, "reused": 0, "input_tokens": 0}


def _jev_record(rows: dict[str, Any], calibration: dict[str, Any] | None,
                totals: dict[str, int], coverage: dict[str, Any] | None = None) -> dict[str, Any]:
    models = {v["model"] for v in rows.values() if v.get("model")}
    if calibration and calibration.get("model"):
        models.add(calibration["model"])
    for v in ((coverage or {}).get("rows") or {}).values():
        if v.get("model"):
            models.add(v["model"])
    return {
        "note": "Jev's answers, cached by ledger row. `rows`: for each unresolved row, which "
                "of the file's theorems states it, or none of them. `coverage`: for each "
                "resolved row, whether the declarations it names cover its claim. Advisory, "
                "like the scorer: propose() and the digests merge these, and nothing here is "
                "written into the ledger.",
        "asked": datetime.date.today().isoformat(),
        "models": sorted(models),
        "calibration": calibration,
        "totals": totals,
        "coverage": coverage,
        "rows": dict(sorted(rows.items())),
    }


def jev_propose(
    index: dict[str, Any], ledger: list[dict[str, Any]], ask: Ask,
    cached: dict[str, Any] | None = None, refresh: bool = False,
    limit: int | None = None, workers: int = 4,
) -> dict[str, Any]:
    """Ask Jev, once per unresolved row, which of its file's theorems states the row.

    Every row the scorer queues is asked, not only the ones the scorer is confident about:
    on the 21 September 2026 sample the scorer fired on ten of thirty rows and Jev put the
    recorded declaration first on nineteen, so the rows the scorer rates low are where Jev
    earns its keep.  Verdicts are cached under ``jev_key``: a row whose key still matches is
    reused unless ``refresh``, a row resolved since is dropped, and ``limit`` caps how many
    are asked in one run, the rest keeping whatever verdict they had.  Cost is input tokens
    only, reported in ``totals``.
    """
    prior = (cached or {}).get("rows", {})
    rows: dict[str, Any] = {}
    pending: list[tuple[dict[str, Any], list[dict[str, Any]], str, int, Any]] = []
    for row, cands, _defs in _queue(index, ledger):
        if not cands:
            continue
        offer = jev_shortlist(row, cands)
        key = jev_key(row, offer)
        old = prior.get(row["id"])
        if old is not None and old.get("key") == key and not refresh:
            rows[row["id"]] = old
            continue
        pending.append((row, offer, key, len(cands), old))
    todo = pending if limit is None else pending[:limit]
    for row, _offer, _key, _in_file, old in pending[len(todo):]:
        if old is not None:
            rows[row["id"]] = old
    today = datetime.date.today().isoformat()

    def one(
        item: tuple[dict[str, Any], list[dict[str, Any]], str, int, Any]
    ) -> tuple[str, dict[str, Any], int]:
        row, offer, key, in_file, _old = item
        state, criteria = jev_question(row, offer)
        v = ask(state, JEV_INSTRUCTIONS, criteria)
        ranked = sorted(v["probabilities"].items(), key=lambda kv: (-kv[1], kv[0]))[:5]
        verdict = {
            "key": key,
            "model": v["model"],
            "asked": today,
            "choice": v["choice"],
            "confidence": round(float(v["confidence"]), 3),
            "probabilities": {k: round(float(p), 3) for k, p in ranked},
            "shortlist": len(offer),
            "in_file": in_file,
        }
        return row["id"], verdict, int(v.get("input_tokens", 0))

    tokens = 0
    for rid, verdict, used in _run(todo, one, workers):
        rows[rid] = verdict
        tokens += used
    totals = {"answered": len(rows), "asked_now": len(todo),
              "reused": len(rows) - len(todo), "input_tokens": tokens}
    return _jev_record(rows, (cached or {}).get("calibration"), totals,
                       (cached or {}).get("coverage"))


def jev_calibrate(
    index: dict[str, Any], ledger: list[dict[str, Any]], ask: Ask,
    sample: int | None = None, seed: int = 0, workers: int = 4,
) -> dict[str, Any]:
    """Score Jev the way ``calibrate`` scores the scorer: on rows whose answer is recorded.

    Same population -- rows naming exactly one declaration, in a file offering at least two
    theorems -- and the recorded declaration is offered like any other, so the measurement is
    of the same question ``jev_propose`` asks.  Stored with its date, model, sample and seed
    in the verdict record; the digest quotes the stored figures and never a hardcoded one.
    """
    by_file: dict[str, list[dict[str, Any]]] = defaultdict(list)
    for d in index["declarations"]:
        if d["kind"] in ("theorem", "lemma"):
            by_file[d["file"]].append(d)
    resolved = [r for r in ledger if len(row_decls(r)) == 1]
    eligible: list[tuple[dict[str, Any], list[dict[str, Any]]]] = []
    for row in resolved:
        cands = by_file.get(lean_key(row.get("lean")), [])
        if len(cands) >= 2 and any(d["name"] == row_decls(row)[0] for d in cands):
            eligible.append((row, cands))
    chosen = eligible
    if sample is not None and sample < len(eligible):
        chosen = random.Random(seed).sample(eligible, sample)

    def one(item: tuple[dict[str, Any], list[dict[str, Any]]]) -> dict[str, Any]:
        row, cands = item
        truth = row_decls(row)[0]
        offer = jev_shortlist(row, cands)
        state, criteria = jev_question(row, offer)
        v = ask(state, JEV_INSTRUCTIONS, criteria)
        ranked = [k for k, _ in sorted(v["probabilities"].items(),
                                       key=lambda kv: (-kv[1], kv[0]))]
        sw = words(row["statement"])
        scorer = sorted(cands, key=lambda d: similarity(sw, d), reverse=True)[0]["name"]
        return {
            "id": row["id"], "truth": truth, "choice": v["choice"],
            "confidence": round(float(v["confidence"]), 3),
            "top3": truth in ranked[:3], "offered": any(d["name"] == truth for d in offer),
            "scorer": scorer, "model": v["model"],
            "input_tokens": int(v.get("input_tokens", 0)),
        }

    results = _run(chosen, one, workers)
    confident = [r for r in results if r["confidence"] >= JEV_REVIEW]
    misses = [{"id": r["id"], "truth": r["truth"], "choice": r["choice"],
               "confidence": r["confidence"], "scorer": r["scorer"]}
              for r in results if r["choice"] != r["truth"]]
    return {
        "asked": datetime.date.today().isoformat(),
        "model": sorted({r["model"] for r in results})[-1] if results else None,
        "resolved": len(resolved),
        "eligible": len(eligible),
        "sampled": len(results),
        "seed": seed,
        "top1": sum(r["choice"] == r["truth"] for r in results),
        "top3": sum(r["top3"] for r in results),
        "none": sum(r["choice"] == JEV_NONE for r in results),
        "truth_not_offered": sum(not r["offered"] for r in results),
        "confident": len(confident),
        "confident_correct": sum(r["choice"] == r["truth"] for r in confident),
        "scorer_top1": sum(r["scorer"] == r["truth"] for r in results),
        "input_tokens": sum(r["input_tokens"] for r in results),
        "misses": sorted(misses, key=lambda m: (-m["confidence"], m["id"])),
    }


def _jev_field(verdict: dict[str, Any], offer: list[dict[str, Any]], key: str) -> dict[str, Any]:
    """A cached verdict as the row will carry it, checked against the current offer.

    Four states.  ``pick``: a theorem this file offers now.  ``none``: Jev chose the option
    that no listed declaration states the claim.  ``stale``: the row or the offer changed
    since Jev was asked.  ``not_a_candidate``: a name the offer does not hold -- a theorem
    claimed since, a renamed one, or an invention -- which is ignored rather than proposed,
    because the digest must never show a candidate the file does not offer.
    """
    names = {d["name"] for d in offer}
    choice = verdict.get("choice")
    if verdict.get("key") != key:
        state, decl = "stale", None
    elif choice == JEV_NONE:
        state, decl = "none", None
    elif choice in names:
        state, decl = "pick", choice
    else:
        state, decl = "not_a_candidate", None
    return {
        "verdict": state,
        "decl": decl,
        "choice": choice,
        "confidence": float(verdict.get("confidence", 0.0)),
        "probabilities": verdict.get("probabilities", {}),
        "model": verdict.get("model"),
        "asked": verdict.get("asked"),
    }


def _jev_summary(rows: list[dict[str, Any]]) -> dict[str, Any] | None:
    carrying = [r for r in rows if r.get("jev")]
    if not carrying:
        return None
    fields = [r["jev"] for r in carrying]
    picks = [j for j in fields if j["verdict"] == "pick"]
    dates = [j["asked"] for j in fields if j.get("asked")]
    return {
        "models": sorted({j["model"] for j in fields if j.get("model")}),
        "asked": max(dates) if dates else None,
        "answered": len(fields),
        "picks": len(picks),
        "none": sum(j["verdict"] == "none" for j in fields),
        "stale": sum(j["verdict"] == "stale" for j in fields),
        "not_a_candidate": sum(j["verdict"] == "not_a_candidate" for j in fields),
        "confident": sum(j["confidence"] >= JEV_REVIEW for j in picks),
        "agree_with_scorer": sum(
            1 for r in carrying
            if r["jev"]["verdict"] == "pick" and r["candidates"]
            and r["jev"]["decl"] == r["candidates"][0]["decl"]
        ),
        "routed": sum(1 for j in fields if j.get("routed")),
    }


JEV_COVERAGE_PROMPT = 2
"""Bumped with the coverage questions or the state format, as ``JEV_PROMPT`` is for the offer.

Version 1 asked about the claim "as written" and about "some declaration": on 21 September
2026 it put 222 of 249 resolved rows below half, the digest's own repaired example among
them at 0.08, because a ledger row cites papers, tests and trust levels and says what it does
not claim, and because each of two declarations covering half a claim is, alone, narrower
than the claim.  Version 2 sets provenance aside and judges the declarations together: the
rows readable as covered moved to 0.72 and above, the five known part-for-whole joins stayed
at or below 0.08, and the repaired example rose to 0.27 with "narrower" halved.
"""

JEV_COVERAGE_FLAG = 0.5
"""A resolved row is listed for review when Jev puts coverage below this.  Half is where yes
and no are equally likely, the Noul's own neutral; the list is read and never applied."""

JEV_COVERAGE_LOW = 0.25
"""Below this the digest files a row under "not covered" rather than "doubtful".  On the
21 September 2026 sample every row whose claim demonstrably said more than its declaration
sat at or below 0.14, and the ones readable as covered at 0.72 or above; the band between is
where the reviewer's reading is genuinely needed."""

JEV_COVERAGE_QUESTIONS = {
    "covers": (
        "`claim` is an informal ledger entry. It may cite papers, sections, tests and trust "
        "levels, name the Lean declarations it rests on, and say what it does not claim; set "
        "all of that aside and take only the mathematical assertions it makes. Do the formal "
        "statements in `declarations`, taken together, establish those assertions: the same "
        "objects, no hypothesis the claim does not make, and every conclusion the claim makes? "
        "Yes means a reader could cite the declarations as the formal proof of the mathematics "
        "in the claim."
    ),
    "claim_broader": (
        "Setting aside provenance, references, trust remarks and disclaimers in `claim`, does "
        "its mathematics assert something that the declarations in `declarations`, taken "
        "together, do not state: an additional conclusion, a further case, a stronger "
        "quantifier, or a wider domain?"
    ),
    "decl_narrower": (
        "Are the declarations in `declarations`, taken together, restricted more than the "
        "mathematics of `claim`: a hypothesis the claim does not make, a smaller domain such "
        "as natural numbers where the claim speaks of integers, a special case, or one "
        "direction of an equivalence the claim states in both directions? Several "
        "declarations that together cover the claim are not narrower."
    ),
    "different_result": (
        "Is some declaration in `declarations` about a different result from the mathematics "
        "of `claim` altogether, rather than a part or the whole of it?"
    ),
}
"""The retag rule as four yes/no questions over one row.  ``covers`` is the rule itself and
the only one that lists a row; the other three are the failure modes the proposal digest
names, asked separately so the reviewer is told what to look for.  All four are answered in
one request and cannot see one another."""

JEV_COVERAGE_READINGS = {
    "claim_broader": "the claim asserts more than the declarations state",
    "decl_narrower": "a declaration is narrower than the claim",
    "different_result": "a declaration is a different result",
}

AskNouls = Callable[[dict[str, Any], dict[str, str]], dict[str, Any]]
"""``ask(state, questions)`` with one instruction per question id, returning ``nouls`` (id to
the probability of yes), ``model`` and ``input_tokens``.  ``jev_ask_nouls`` builds the real
one; the tests pass a function."""


def jev_ask_nouls(model: str = "jev-latest", timeout: float = 60.0) -> AskNouls:
    """The real asker for the coverage questions: several Nouls over one state per call."""
    try:
        from typesafe_sdk import Noul, TypeSafeClient
    except ImportError as exc:  # pragma: no cover - depends on the environment
        raise SystemExit(
            "typesafe-sdk is not installed: pip install typesafe-sdk, then set TYPESAFE_API_KEY"
        ) from exc
    client = TypeSafeClient(timeout=timeout)

    def ask(state: dict[str, Any], questions: dict[str, str]) -> dict[str, Any]:
        response = client.system_one(
            state=state,
            questions={qid: Noul(instructions=text) for qid, text in questions.items()},
            model=model,
        )
        return {
            "nouls": {qid: float(response.nouls[qid].noul) for qid in questions},
            "model": response.model,
            "input_tokens": int(response.usage.input_tokens),
        }

    return ask


def _no_ask(state: dict[str, Any], questions: dict[str, str]) -> dict[str, Any]:
    raise RuntimeError("no question may be asked in this run")


def _resolved(
    index: dict[str, Any], ledger: list[dict[str, Any]]
) -> list[tuple[dict[str, Any], list[dict[str, Any]], list[str]]]:
    """Rows that name their declarations, each with those declarations from the index.

    A name the index does not hold is reported rather than skipped silently: the ledger's
    own tests forbid it, so a hit here means the index is stale.  A ``REFUTED`` row is left
    out: its declaration is the refutation, and whether that covers the refuted claim is a
    different question from the retag rule.
    """
    byname = {(d["file"], d["name"]): d for d in index["declarations"]}
    out: list[tuple[dict[str, Any], list[dict[str, Any]], list[str]]] = []
    for row in ledger:
        names = row_decls(row)
        if not names or row["tag"] == "REFUTED":
            continue
        key = lean_key(row.get("lean"))
        found = [byname[(key, n)] for n in names if (key, n) in byname]
        missing = [n for n in names if (key, n) not in byname]
        out.append((row, found, missing))
    return out


def coverage_state(row: dict[str, Any], decls: list[dict[str, Any]]) -> dict[str, Any]:
    """The claim beside every declaration it names, each with docstring and header."""
    return {
        "claim": row["statement"],
        "lean_file": row.get("lean") or "",
        "ledger_id": row["id"],
        "declarations": [
            {"name": d["name"], "docstring": _clip(d.get("doc", ""), 600),
             "statement": _clip(signature(d, limit=12), 900)}
            for d in decls
        ],
    }


def coverage_key(row: dict[str, Any], decls: list[dict[str, Any]]) -> str:
    """Unlike the offer key, this covers the declarations' text: a strengthened header or a
    corrected docstring changes what covers the claim, and re-asking one row is cheap."""
    payload = [JEV_COVERAGE_PROMPT, row["statement"], row.get("lean") or "",
               [[d["name"], d.get("doc", ""), signature(d, limit=12)] for d in decls]]
    blob = json.dumps(payload, ensure_ascii=False).encode("utf-8")
    return hashlib.sha256(blob).hexdigest()[:16]


def jev_coverage(
    index: dict[str, Any], ledger: list[dict[str, Any]], ask: AskNouls,
    cached: dict[str, Any] | None = None, refresh: bool = False,
    limit: int | None = None, only: set[str] | None = None, workers: int = 4,
) -> dict[str, Any]:
    """Ask Jev, once per resolved row, whether the declarations it names cover its claim.

    The retag rule -- ``EXACT — LEAN VERIFIED`` only when the Lean theorem covers the English
    statement -- has had no mechanism behind it: the proposal digest names the two ways a join
    records a part as the whole and leaves both to the reader.  This asks the rule as four
    Nouls over the claim and every declaration the row names, and caches the answers under
    ``coverage_key`` in the verdict record, beside the offer verdicts.  ``only`` restricts a
    run to some row ids, which is how one retag is checked; ``limit`` and ``refresh`` are as in
    ``jev_propose``, and ``limit=0`` rewrites the artifacts from the cache without asking.
    Advisory: the ledger is never written.
    """
    record = dict(cached or {})
    prior = (record.get("coverage") or {}).get("rows", {})
    rows: dict[str, Any] = {}
    pending: list[tuple[dict[str, Any], list[dict[str, Any]], str, Any]] = []
    unfound: dict[str, list[str]] = {}
    for row, decls, missing in _resolved(index, ledger):
        old = prior.get(row["id"])
        if missing:
            unfound[row["id"]] = missing
            continue
        if only is not None and row["id"] not in only:
            if old is not None:
                rows[row["id"]] = old
            continue
        key = coverage_key(row, decls)
        if old is not None and old.get("key") == key and not refresh:
            rows[row["id"]] = old
            continue
        pending.append((row, decls, key, old))
    todo = pending if limit is None else pending[:limit]
    for row, _decls, _key, old in pending[len(todo):]:
        if old is not None:
            rows[row["id"]] = old
    today = datetime.date.today().isoformat()

    def one(
        item: tuple[dict[str, Any], list[dict[str, Any]], str, Any]
    ) -> tuple[str, dict[str, Any], int]:
        row, decls, key, _old = item
        v = ask(coverage_state(row, decls), JEV_COVERAGE_QUESTIONS)
        verdict: dict[str, Any] = {
            "key": key, "model": v["model"], "asked": today,
            "decls": [d["name"] for d in decls],
        }
        for qid in JEV_COVERAGE_QUESTIONS:
            verdict[qid] = round(float(v["nouls"][qid]), 3)
        return row["id"], verdict, int(v.get("input_tokens", 0))

    tokens = 0
    for rid, verdict, used in _run(todo, one, workers):
        rows[rid] = verdict
        tokens += used
    earlier = (record.get("coverage") or {}).get("asked")
    coverage = {
        "asked": today if todo else earlier,
        "totals": {"answered": len(rows), "asked_now": len(todo),
                   "reused": len(rows) - len(todo), "input_tokens": tokens,
                   "unfound": len(unfound)},
        "rows": dict(sorted(rows.items())),
    }
    return _jev_record(record.get("rows", {}), record.get("calibration"),
                       record.get("totals", dict(_EMPTY_TOTALS)), coverage)


def coverage_rows(index: dict[str, Any], ledger: list[dict[str, Any]],
                  record: dict[str, Any] | None) -> list[dict[str, Any]]:
    """Every resolved row with its cached coverage verdict checked against the declarations
    as they are now: ``verdict`` is ``fresh``, ``stale`` or ``unasked``; ``band`` is
    ``covered``, ``doubtful`` or ``not_covered`` by ``covers`` alone; ``flagged`` says whether
    the digest lists it; ``reading`` names the failure mode Jev rates highest when that is at
    or above half."""
    prior = ((record or {}).get("coverage") or {}).get("rows", {})
    out: list[dict[str, Any]] = []
    for row, decls, missing in _resolved(index, ledger):
        entry: dict[str, Any] = {
            "id": row["id"], "tag": row["tag"], "lean": row.get("lean"),
            "trust": row.get("lean_trust"), "statement": row["statement"], "decls": decls,
            "missing": missing, "verdict": "unasked", "band": None, "flagged": False,
            "reading": None,
        }
        v = prior.get(row["id"])
        if v is not None and not missing:
            entry["verdict"] = "fresh" if v.get("key") == coverage_key(row, decls) else "stale"
            for qid in JEV_COVERAGE_QUESTIONS:
                entry[qid] = float(v.get(qid, 0.0))
            entry["model"], entry["asked"] = v.get("model"), v.get("asked")
            if entry["verdict"] == "fresh":
                covers = entry["covers"]
                entry["band"] = ("not_covered" if covers < JEV_COVERAGE_LOW
                                 else "doubtful" if covers < JEV_COVERAGE_FLAG else "covered")
                entry["flagged"] = covers < JEV_COVERAGE_FLAG
                modes = {q: entry[q] for q in JEV_COVERAGE_READINGS}
                worst = max(modes, key=lambda q: (modes[q], q))
                entry["reading"] = worst if modes[worst] >= 0.5 else None
        out.append(entry)
    return out


def coverage_digest(
    index: dict[str, Any], ledger: list[dict[str, Any]], jev: dict[str, Any] | None = None
) -> str:
    """Resolved rows whose declarations may not state the whole claim, lowest coverage first.

    The proposal digest joins rows to declarations; this one asks whether a recorded join is
    complete, which is the retag rule.  Each entry is the row's statement beside every
    declaration it names, docstring and header, with Jev's four probabilities and the failure
    mode it rates highest, so the reviewer knows what to look for before reading.
    """
    verdicts = load_jev() if jev is None else jev
    rows = coverage_rows(index, ledger, verdicts)
    out = [
        "# Coverage review queue",
        "",
        "Resolved rows -- rows that name their declarations -- whose declarations may not state",
        "the whole claim.  The rule for `EXACT — LEAN VERIFIED` is that the Lean theorem covers",
        "the English statement, and nothing checked it: the proposal digest names the two ways a",
        "join records a part as the whole and leaves both to the reader.  Here Jev is asked four",
        "yes/no questions over each row and every declaration it names: whether the declarations",
        "cover the claim, whether the claim asserts more than they state, whether a declaration",
        "is narrower than the claim, and whether one is a different result.",
        "",
        f"A row is listed when coverage is below {JEV_COVERAGE_FLAG}, lowest first: below",
        f"{JEV_COVERAGE_LOW} it is filed as not covered, between the two as doubtful.  The other",
        "three answers are shown as the reading to check first.  Jev returns probabilities, not",
        "a reading: the list is where to look, and the ruling is the reviewer's.  Answer by",
        "extending `decl` to the declarations that together state the claim, narrowing the",
        "statement to what the declarations prove, or retagging to `EXACT — HUMAN PROOF`; then",
        "rerun `jev-coverage`, which re-asks a row whose statement or declarations changed.",
        "",
        "A short claim filed as not covered is the likeliest mis-join and is worth reading first.",
        "A long one usually summarizes a paper section and says more than one theorem proves,",
        "which is what the ledger's list-valued `decl` exists to record.  `REFUTED` rows are not",
        "asked: their declaration is the refutation.",
        "",
    ]
    asked = [r for r in rows if r["verdict"] != "unasked"]
    if not asked:
        out += ["Jev has not been asked yet: run `python tools/formalpedia.py jev-coverage`.", ""]
        return "\n".join(out) + "\n"
    stale = [r for r in asked if r["verdict"] == "stale"]
    flagged = sorted((r for r in asked if r["flagged"]), key=lambda r: (r["covers"], r["id"]))
    bands = collections.Counter(r["band"] for r in asked if r["band"])
    models = sorted({r["model"] for r in asked if r.get("model")})
    dates = [r["asked"] for r in asked if r.get("asked")]
    tail = (f", and {len(stale)} answered an earlier version of their row and need a rerun."
            if stale else ".")
    out += [
        f"Jev ({', '.join(models)}, last asked {max(dates) if dates else '?'}) has answered",
        f"{len(asked)} of the {len(rows)} resolved rows: {bands['covered']} covered,",
        f"{bands['doubtful']} doubtful, {bands['not_covered']} not covered; {len(flagged)} are",
        f"listed below{tail}",
        "",
    ]
    short = [r for r in flagged if r["band"] == "not_covered" and len(r["statement"]) < 150]
    if short:
        names = ", ".join(f"`{r['id']}` ({r['covers']})" for r in short)
        out += [f"Short claims filed as not covered, the likeliest mis-joins: {names}.", ""]
    marked = False
    for n, r in enumerate(flagged, 1):
        if r["band"] == "doubtful" and not marked:
            out += [f"**Doubtful from here: coverage between {JEV_COVERAGE_LOW} and "
                    f"{JEV_COVERAGE_FLAG}.**", ""]
            marked = True
        out += [f"## {n}. `{r['id']}` &mdash; covers {r['covers']}", ""]
        reading = JEV_COVERAGE_READINGS.get(r["reading"] or "")
        if reading:
            out.append(f"*Reads as: {reading} ({r[r['reading']]}).*")
        else:
            out.append("*No failure mode above the line; coverage itself is doubtful.*")
        out += [
            "",
            f"*Claim broader {r['claim_broader']}; declaration narrower {r['decl_narrower']}; "
            f"different result {r['different_result']}.  Tag {r['tag']}, trust "
            f"{r['trust'] or '?'}.*",
            "",
            f"**Row.** {r['statement'][:800]}"
            + ("  *(truncated; read the ledger row)*" if len(r["statement"]) > 800 else ""),
            "",
        ]
        label = "**Declaration.**" if len(r["decls"]) == 1 else "**Declarations.**"
        for i, d in enumerate(r["decls"]):
            head = label if i == 0 else "**And.**"
            out += [f"{head} `{d['name']}` &mdash; {d['trust']}-checked, `{r['lean']}:{d['line']}`",
                    ""]
            if d.get("doc"):
                out += [f"> {d['doc']}", ""]
            out += ["```lean", signature(d, limit=12) or "(could not read the declaration)",
                    "```", ""]
    return "\n".join(out) + "\n"


def signature(decl: dict[str, Any], limit: int = 8) -> str:
    """A declaration's statement, from its header down to the `:=` that starts the proof.

    Nine of the queue's confident candidates carry no docstring, and an entry that offers
    only a name is not answerable: deciding "is this row that theorem?" needs the theorem.
    The signature is what the docstring would have paraphrased.
    """
    try:
        lines = io.open(ROOT / decl["file"], encoding="utf-8").read().splitlines()
    except OSError:
        return ""
    out: list[str] = []
    for line in lines[decl["line"] - 1: decl["line"] - 1 + limit]:
        out.append(line.rstrip())
        if ":=" in line or line.rstrip().endswith("by"):
            break
    text = "\n".join(out)
    return text.split(":=")[0].rstrip() if ":=" in text else text


def _jev_lines(row: dict[str, Any], top: dict[str, Any],
               docs: dict[tuple[str, str], dict[str, Any]]) -> list[str]:
    """Jev's answer for one digest entry, beside the scorer's candidate.

    A disagreement prints Jev's declaration in full, docstring and header, because the
    reviewer's question is the same for both candidates and needs the same evidence.
    """
    jv = row.get("jev")
    if not jv:
        return []
    conf = jv["confidence"]
    out: list[str] = []
    if jv["verdict"] == "pick" and jv["decl"] == top["decl"]:
        out += [f"**Jev.** picks `{jv['decl']}` as well, at {conf}.", ""]
    elif jv["verdict"] == "pick":
        other = docs.get((lean_key(row["lean"]), jv["decl"]))
        trust = other["trust"] if other else "?"
        line = other["line"] if other else "?"
        out += [f"**Jev.** picks `{jv['decl']}` at {conf}, not the scorer's candidate.", "",
                f"**Jev's candidate.** `{jv['decl']}` &mdash; {trust}-checked, "
                f"`{row['lean']}:{line}`", ""]
        if other and other.get("doc"):
            out += [f"> {other['doc']}", ""]
        shown = (signature(other) if other else "") or "(could not read the declaration)"
        out += ["```lean", shown, "```", ""]
    elif jv["verdict"] == "none":
        out += [f"**Jev.** none of these, at {conf}.  Read the row for a claim broader than any "
                "one declaration here, or a declaration narrower than the row.", ""]
    elif jv["verdict"] == "stale":
        out += ["**Jev.** answered an earlier version of this row or of its file; rerun "
                "`jev-propose`.", ""]
    else:
        out += [f"**Jev.** named `{jv['choice']}`, which this file does not offer; ignored.", ""]
    if jv.get("routed"):
        out += ["*The scorer rated this row low; it is listed on Jev's confidence.*", ""]
    return out


def review_digest(
    index: dict[str, Any], ledger: list[dict[str, Any]], jev: dict[str, Any] | None = None
) -> str:
    """The confident half of the proposal queue, laid out to be answered in one sitting.

    The JSON queue has everything except the thing the decision needs: what the candidate
    theorem actually says.  Deciding "is this row that declaration?" means reading the row's
    statement beside the declaration's docstring, so this puts them adjacent and drops
    everything else.

    When Jev has been asked, each entry also carries its answer beside the scorer's, and a
    row Jev is confident about is listed even where the scorer rated it low.  ``jev`` is the
    verdict record, ``None`` for the committed one, as in ``propose``.
    """
    docs = {(d["file"], d["name"]): d for d in index["declarations"]}
    verdicts = load_jev() if jev is None else jev
    cal = calibrate(index, ledger)
    pct = round(100 * cal["correct"] / cal["fires"]) if cal["fires"] else 0
    out = [
        "# Declaration review queue",
        "",
        "Rows where one candidate leads its file clearly.  Each entry is the ledger row's own",
        "statement beside the candidate's docstring; the question is only whether they say the",
        f"same thing.  Measured against all {cal['resolved']} single-declaration rows the scorer gets",
        f"{cal['correct']} of the {cal['fires']} it fires on right, {pct}% precise, so roughly one in",
        f"{max(1, round(cal['fires'] / max(1, cal['fires'] - cal['correct'])))} below is wrong.",
        "",
        "Two failure modes are not scored at all, and both record a part as the whole.",
        "",
        "The row may be broader than the candidate: `BTC-select3` reads \"select3 represents",
        "every Trit->Z map; abs/min/max\" -- four theorems, of which `select3_represents` is",
        "one.  If a row says \"and\", \";\" or lists several claims, it belongs in neither column.",
        "",
        "Or the candidate may be narrower than the row, with nothing in the prose to say so.",
        "`BTN-sdrg-lambda1-interval` claims every integer with |s| <= m/2 is reachable, and",
        "`lambda1_interval_reachable` reads \"every nonnegative point\" -- true, and half of it;",
        "its `n : ℕ` is the tell, and a sibling proves the rest.  That is why the statement is",
        "printed below every candidate, docstring or not.",
        "",
    ]
    proposals = propose(index, ledger, jev=verdicts)
    s = proposals.get("jev")
    if s:
        out += [
            f"Jev ({', '.join(s['models'])}, last asked {s['asked']}) answered {s['answered']} of",
            f"the unresolved rows: {s['picks']} picks and {s['none']} \"none of these\".",
            f"{s['agree_with_scorer']} of the picks are the scorer's own first candidate, and",
            f"{s['confident']} are at or above {JEV_REVIEW} confidence.  A confident pick lists",
            "a row here whatever the scorer thought, and every entry shows Jev's answer beside",
            "the scorer's.  Jev returns a probability, not a reading: a second opinion for the",
            "reviewer, never a ledger write.",
            "",
        ]
    c = (verdicts or {}).get("calibration")
    if c:
        out += [
            f"Measured on {c['sampled']} resolved rows on {c['asked']} ({c['model']}): the",
            f"recorded declaration first {c['top1']} times, in its top three {c['top3']} times,",
            f"right {c['confident_correct']} of {c['confident']} times at or above {JEV_REVIEW}",
            f"confidence.  The scorer's first candidate was right {c['scorer_top1']} times on the",
            "same rows.",
            "",
        ]
    out += [
        "Answer by adding `decl` and `lean_trust` to the row in `docs/theory/theorem_ledger.json`.",
        "",
    ]
    shown = 0
    for row in proposals["rows"]:
        if row["confidence"] != "review" or not row["candidates"]:
            continue
        top = row["candidates"][0]
        decl = docs.get((lean_key(row["lean"]), top["decl"]))
        shown += 1
        out.append(f"## {shown}. `{row['id']}`")
        out.append("")
        out.append(f"**Row.** {row['statement'][:340]}")
        out.append("")
        out.append(f"**Candidate.** `{top['decl']}` &mdash; {top['trust']}-checked, "
                   f"`{row['lean']}:{top['line']}`")
        out.append("")
        doc = (decl or {}).get("doc")
        if doc:
            out.append(f"> {doc}")
            out.append("")
        # The statement is always shown, not only when prose is missing.  A docstring can be
        # true and still narrower than the row: `lambda1_interval_reachable` reads "every
        # nonnegative point", and only the `n : ℕ` in its signature says the row's
        # `|s| <= m/2` is half unproved by it.
        out.append("```lean")
        out.append((signature(decl) if decl else "") or "(could not read the declaration)")
        out.append("```")
        out.append("")
        out.extend(_jev_lines(row, top, docs))
        if row.get("names_own"):
            out.append(f"*Statement names: {', '.join('`' + n + '`' for n in row['names_own'])}*")
            out.append("")
        others = ", ".join(f"`{c['decl']}` ({c['score']})" for c in row["candidates"][1:])
        if others:
            out.append(f"*Runners-up: {others}*")
            out.append("")
        extended = [c["decl"] for c in row["candidates"][1:]
                    if top["decl"] != c["decl"] and top["decl"].startswith(c["decl"])]
        if extended:
            out.append(f"*Careful: `{top['decl']}` extends `{extended[0]}`, and in this corpus a "
                       "longer name is usually a special case of the shorter one. Twice the "
                       "shorter name was the answer and the scorer ranked it second, because "
                       "the specialisation happened to be the documented one.*")
            out.append("")
        if row.get("definitions"):
            defs = ", ".join(f"`{d['decl']}`" for d in row["definitions"])
            out.append(f"*If this row describes a definition rather than a theorem: {defs}*")
            out.append("")
    out.insert(7, f"{shown} rows below, of {proposals['unresolved']} unresolved.\n")
    return "\n".join(out) + "\n"


def render(payload: Any) -> str:
    """The exact bytes every generated artifact here is written as.

    The staleness gate in tests compares the committed file to a fresh
    build through this function, so the two sides cannot drift apart by
    someone changing an indent or a sort on one of them alone.
    """
    return json.dumps(payload, indent=2, sort_keys=True) + "\n"


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


def _write_jev_artifacts(index: dict[str, Any], ledger: list[dict[str, Any]],
                         record: dict[str, Any]) -> None:
    """The verdict record, then the two artifacts that merge it, in that order."""
    JEV.parent.mkdir(parents=True, exist_ok=True)
    JEV.write_text(render(record), encoding="utf-8")
    PROPOSALS.write_text(render(propose(index, ledger, jev=record)), encoding="utf-8")
    REVIEW.parent.mkdir(parents=True, exist_ok=True)
    REVIEW.write_text(review_digest(index, ledger, jev=record), encoding="utf-8")
    COVERAGE.write_text(coverage_digest(index, ledger, jev=record), encoding="utf-8")
    for path in (JEV, PROPOSALS, REVIEW, COVERAGE):
        print(f"wrote {path.relative_to(ROOT).as_posix()}")


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
    sub.add_parser("dag", help="rebuild the claim graph over ledger-carrying modules")
    sub.add_parser("propose", help="rank declarations for rows that name none")
    sub.add_parser("papers", help="each manuscript's reachable trust surface")
    sub.add_parser("review", help="write the confident proposals as a readable digest")
    p = sub.add_parser("jev-propose",
                       help="ask Jev which theorem each unresolved row means; verdicts are cached")
    p.add_argument("--model", default="jev-latest")
    p.add_argument("--refresh", action="store_true",
                   help="ask again where a cached verdict still matches")
    p.add_argument("--limit", type=int, default=None, help="ask about at most this many rows now")
    p.add_argument("--workers", type=int, default=4)
    p = sub.add_parser("jev-calibrate",
                       help="score Jev against rows whose declaration is recorded")
    p.add_argument("--model", default="jev-latest")
    p.add_argument("--sample", type=int, default=None,
                   help="rows to draw; every eligible row if omitted")
    p.add_argument("--seed", type=int, default=0)
    p.add_argument("--workers", type=int, default=4)
    p = sub.add_parser("jev-coverage",
                       help="ask Jev whether each resolved row's declarations cover its claim")
    p.add_argument("--model", default="jev-latest")
    p.add_argument("--refresh", action="store_true",
                   help="ask again where a cached verdict still matches")
    p.add_argument("--limit", type=int, default=None,
                   help="ask about at most this many rows now; 0 rewrites from the cache")
    p.add_argument("--rows", default=None,
                   help="comma-separated ledger ids to ask about, e.g. the row being retagged")
    p.add_argument("--workers", type=int, default=4)
    args = ap.parse_args(argv)

    if args.cmd == "jev-coverage":
        index = load()
        ledger = json.load(io.open(LEDGER, encoding="utf-8"))
        only = {s.strip() for s in args.rows.split(",") if s.strip()} if args.rows else None
        ask = _no_ask if args.limit == 0 else jev_ask_nouls(args.model)
        record = jev_coverage(index, ledger, ask, cached=load_jev(), refresh=args.refresh,
                              limit=args.limit, only=only, workers=args.workers)
        _write_jev_artifacts(index, ledger, record)
        t = record["coverage"]["totals"]
        print(f"{t['answered']} resolved rows carry a coverage verdict: asked {t['asked_now']} "
              f"now ({t['input_tokens']} input tokens), reused {t['reused']}"
              + (f"; {t['unfound']} rows name a declaration the index lacks" if t["unfound"]
                 else ""))
        rows = coverage_rows(index, ledger, record)
        bands = collections.Counter(r["band"] for r in rows if r["band"])
        print(f"  {bands['covered']} covered, {bands['doubtful']} doubtful, "
              f"{bands['not_covered']} not covered; {sum(r['flagged'] for r in rows)} listed "
              f"for review, {sum(r['verdict'] == 'stale' for r in rows)} stale")
        for r in rows:
            if only and r["id"] in only and r["verdict"] != "unasked":
                reading = JEV_COVERAGE_READINGS.get(r["reading"] or "", "no failure mode")
                print(f"  {r['id']}: {r['band']}; covers {r['covers']}, claim broader "
                      f"{r['claim_broader']}, declaration narrower {r['decl_narrower']}, "
                      f"different result {r['different_result']} -> {reading}")
        return 0

    if args.cmd == "jev-propose":
        index = load()
        ledger = json.load(io.open(LEDGER, encoding="utf-8"))
        record = jev_propose(index, ledger, jev_ask(args.model), cached=load_jev(),
                             refresh=args.refresh, limit=args.limit, workers=args.workers)
        _write_jev_artifacts(index, ledger, record)
        t = record["totals"]
        print(f"{t['answered']} rows carry a verdict: asked {t['asked_now']} now "
              f"({t['input_tokens']} input tokens), reused {t['reused']}")
        merged = propose(index, ledger, jev=record)
        s = merged["jev"] or {}
        print(f"  {s.get('picks', 0)} picks ({s.get('confident', 0)} at or above {JEV_REVIEW}), "
              f"{s.get('none', 0)} none of these, {s.get('agree_with_scorer', 0)} agreeing with "
              f"the scorer; {merged['worth_reviewing']} rows now worth reviewing")
        return 0

    if args.cmd == "jev-calibrate":
        index = load()
        ledger = json.load(io.open(LEDGER, encoding="utf-8"))
        cal = jev_calibrate(index, ledger, jev_ask(args.model), sample=args.sample,
                            seed=args.seed, workers=args.workers)
        cached = load_jev()
        record = _jev_record((cached or {}).get("rows", {}), cal,
                             (cached or {}).get("totals", dict(_EMPTY_TOTALS)),
                             (cached or {}).get("coverage"))
        _write_jev_artifacts(index, ledger, record)
        print(f"{cal['sampled']} of {cal['eligible']} eligible rows ({cal['model']}, seed "
              f"{cal['seed']}, {cal['input_tokens']} input tokens)")
        print(f"  recorded declaration first: {cal['top1']}; in the top three: {cal['top3']}; "
              f"none of these: {cal['none']}; not offered: {cal['truth_not_offered']}")
        print(f"  at or above {JEV_REVIEW}: {cal['confident_correct']} of {cal['confident']} "
              f"right; scorer first candidate right: {cal['scorer_top1']}")
        for m in cal["misses"]:
            print(f"    miss {m['id']}: recorded {m['truth']}, Jev {m['choice']} "
                  f"({m['confidence']}), scorer {m['scorer']}")
        return 0

    if args.cmd == "build":
        index = build()
        INDEX.parent.mkdir(parents=True, exist_ok=True)
        INDEX.write_text(render(index), encoding="utf-8")
        t = index["totals"]
        print(f"{t['declarations']} declarations in {t['modules']} modules")
        print(f"  trust: {t['trust']}")
        print(f"  declarations under a ledger row: {t['declarations_with_a_ledger_row']}")
        return 0

    if args.cmd == "review":
        index = load()
        ledger = json.load(io.open(LEDGER, encoding="utf-8"))
        REVIEW.parent.mkdir(parents=True, exist_ok=True)
        REVIEW.write_text(review_digest(index, ledger), encoding="utf-8")
        print(f"wrote {REVIEW.relative_to(ROOT)}")
        return 0

    if args.cmd == "papers":
        for label, s in paper_surface(load()).items():
            if not s["present"]:
                print(f"{label}: root {s['root']} is not in the index")
                continue
            print(f"{label} ({s['root']}): {s['modules']} modules, "
                  f"{s['declarations']} declarations")
            print(f"   proofs running native_decide: {s['compiler_trusted'] or 'none'}")
            resting = [n for n in s["compiler_dependent"] if n not in s["compiler_trusted"]]
            print(f"   resting on one through citation: {resting or 'none'}")
            if s["open"]:
                print(f"   carrying sorry: {s['open']}")
        return 0

    if args.cmd == "propose":
        index = load()
        ledger = json.load(io.open(LEDGER, encoding="utf-8"))
        out = propose(index, ledger)
        PROPOSALS.parent.mkdir(parents=True, exist_ok=True)
        PROPOSALS.write_text(render(out), encoding="utf-8")
        print(f"{out['unresolved']} unresolved rows; {out['worth_reviewing']} worth reviewing; "
              f"{out['composite']} name two or more of their own declarations")
        return 0

    if args.cmd == "dag":
        index = load()
        ledger = json.load(io.open(LEDGER, encoding="utf-8"))
        graph = dag(index, ledger)
        DAG.parent.mkdir(parents=True, exist_ok=True)
        DAG.write_text(render(graph), encoding="utf-8")
        g = graph["totals"]
        print(f"{g['nodes']} modules carry {g['ledger_rows_placed']} ledger rows")
        print(f"  {g['edges_before_reduction']} edges -> {g['edges']} after transitive reduction")
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
