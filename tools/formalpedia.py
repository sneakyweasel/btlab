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
import collections
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
DAG = ROOT / "data" / "research" / "formalpedia" / "dag.json"
PROPOSALS = ROOT / "data" / "research" / "formalpedia" / "decl_proposals.json"
REVIEW = ROOT / "docs" / "research" / "formalpedia_decl_review.md"

DECL = re.compile(
    r"^(?P<kind>theorem|lemma|def|abbrev|instance|structure)\s+"
    r"(?P<name>[A-Za-z_][A-Za-z0-9_'!?.]*)",
    re.MULTILINE,
)
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


def declares(text: str, name: str, kind: str = "theorem") -> bool:
    """Does `text` declare exactly `name` -- not merely something starting with it?

    519 of the 4,528 declaration names in this corpus are a proper prefix of another, because
    helper lemmas are named by extending their main theorem: `power_bound_compensated_contracts`
    and `power_bound_compensated_contracts_follows`, `power_bound_word` and
    `power_bound_word_strict`.  A guard written as ``f"theorem {name}" in text`` therefore still
    passes after its theorem is deleted, as long as one of those neighbours survives -- which is
    precisely the event such a guard exists to catch.
    """
    return re.search(rf"(?:^|\n)\s*{kind}\s+{re.escape(name)}(?![A-Za-z0-9_'])", text) is not None


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
}
"""The module each manuscript's formalization claims to track.

Reachability from these roots is what a trust sentence in a paper is actually about.  A
directory grep answers a different question -- `formal/Problems/Juggler/` holds modules no
paper imports -- and would let a `native_decide` land inside a paper's surface while the
count outside it stayed reassuring.
"""


def paper_surface(index: dict[str, Any]) -> dict[str, Any]:
    """Per paper: the modules it reaches, and the proofs in them the kernel does not check."""
    reach = reachable(index)
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
            mod = file_to_mod.get("formal/" + ref)
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
    resolved = [r for r in ledger if r.get("decl")]
    fires = correct = 0
    for row in resolved:
        cands = by_file.get("formal/" + str(row.get("lean")), [])
        if len(cands) < 2:
            continue
        sw = words(row["statement"])
        ranked = sorted(cands, key=lambda d: similarity(sw, d), reverse=True)
        a, b = similarity(sw, ranked[0]), similarity(sw, ranked[1])
        if a >= 0.10 and a >= 1.5 * max(b, 1e-9):
            fires += 1
            correct += ranked[0]["name"] == row["decl"]
    return {"resolved": len(resolved), "fires": fires, "correct": correct}


def propose(index: dict[str, Any], ledger: list[dict[str, Any]]) -> dict[str, Any]:
    """Rank the declarations a still-unresolved row might mean.  Proposals, never answers.

    Measured against every resolved row: it fires on 49 and gets 42 right, so **86%**, about
    one wrong in seven.  An earlier figure of 96% came from a calibration set of 70 rows that
    was dominated by the easiest cases -- rows naming their theorem outright -- and overstated
    what the scorer does on the rows that are actually left.  The misses are sibling
    confusions: ``lsdZ_mul`` for ``D_mul``, ``q_eq_of_cube_mod`` for both ``qCubic_def`` and
    ``q_visible_mod``, ``cycleMin_length_of_gap`` for ``cycleMin_gap_transfer``.  One in seven
    is a queue a person reads, never a ledger write, which is why nothing here is applied.
    """
    # A declaration already claimed by a resolved row cannot be the answer to another: one
    # theorem backs one claim, which the ledger's own collision test enforces.  Offering a
    # taken declaration wastes a reviewer's judgement on an answer that would be rejected.
    taken = {(r["lean"], r["decl"]) for r in ledger if r.get("decl")}

    by_file: dict[str, list[dict[str, Any]]] = defaultdict(list)
    defs_by_file: dict[str, list[dict[str, Any]]] = defaultdict(list)
    for d in index["declarations"]:
        if d["kind"] in ("theorem", "lemma"):
            by_file[d["file"]].append(d)
        elif d["kind"] in ("def", "abbrev"):
            defs_by_file[d["file"]].append(d)

    # ``composite`` counts only rows that *name* two or more of their own declarations, so it
    # is a lower bound and not the count.  Rows composite by content name nothing: "cmp3
    # translation, negation, and antisymmetry" is three theorems and no identifiers.  Two
    # heuristics over the statement text were calibrated against eleven rows classified by
    # reading -- equation conjunctions, then prose lists as well -- and caught 0 and 3 of the
    # eleven.  The eleven are composite for unrelated reasons (a noun list, two equations, an
    # inventory of Lean names, a claim beside its instance) and share no surface form, so the
    # true count is not obtainable without reading. Do not infer one from this field.
    out: list[dict[str, Any]] = []
    for row in ledger:
        if row["tag"] != "EXACT — LEAN VERIFIED" or row.get("decl"):
            continue
        ref = row.get("lean")
        if not (isinstance(ref, str) and ref.endswith(".lean")):
            out.append({"id": row["id"], "lean": ref, "why": "lean field is not a file",
                        "confidence": "low", "candidates": []})
            continue
        cands = [d for d in by_file.get("formal/" + ref, [])
                 if (ref, d["name"]) not in taken]
        sw = words(row["statement"])
        ranked = sorted(cands, key=lambda d: similarity(sw, d), reverse=True)[:3]
        scores = [round(similarity(sw, d), 3) for d in ranked]
        top = scores[0] if scores else 0.0
        second = scores[1] if len(scores) > 1 else 0.0
        # Definitions are ranked separately, never merged into the theorem list: admitting
        # them to one ranking displaces the true answer on 3 of the rows already resolved.
        # A row like BTA-x3-Q-def describes a `def`, and until now had no candidate at all.
        dcands = sorted(defs_by_file.get("formal/" + ref, []),
                        key=lambda d: similarity(sw, d), reverse=True)[:2]
        named = [t for t in dict.fromkeys(IDENT.findall(row["statement"]))
                 if any(d["name"] == t for d in cands)]
        out.append({
            "id": row["id"],
            "lean": ref,
            "statement": row["statement"][:400],
            "in_file": len(cands),
            "names_own": named,
            "composite": len(named) >= 2,
            "confidence": "review" if (top >= 0.10 and top >= 1.5 * max(second, 1e-9)) else "low",
            "candidates": [{"decl": d["name"], "score": s, "trust": d["trust"], "line": d["line"]}
                           for d, s in zip(ranked, scores)],
            "definitions": [{"decl": d["name"], "score": round(similarity(sw, d), 3),
                             "line": d["line"]} for d in dcands],
        })
    return {
        "note": "Proposals for human review. Calibration: 86% precision (42 of 49 fires) "
                "against all resolved rows. Nothing here has been written into the ledger.",
        "unresolved": len(out),
        "worth_reviewing": sum(1 for o in out if o["confidence"] == "review"),
        "composite": sum(1 for o in out if o.get("composite")),
        "rows": out,
    }


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


def review_digest(index: dict[str, Any], ledger: list[dict[str, Any]]) -> str:
    """The confident half of the proposal queue, laid out to be answered in one sitting.

    The JSON queue has everything except the thing the decision needs: what the candidate
    theorem actually says.  Deciding "is this row that declaration?" means reading the row's
    statement beside the declaration's docstring, so this puts them adjacent and drops
    everything else.
    """
    docs = {(d["file"], d["name"]): d for d in index["declarations"]}
    cal = calibrate(index, ledger)
    pct = round(100 * cal["correct"] / cal["fires"]) if cal["fires"] else 0
    out = [
        "# Declaration review queue",
        "",
        "Rows where one candidate leads its file clearly.  Each entry is the ledger row's own",
        "statement beside the candidate's docstring; the question is only whether they say the",
        f"same thing.  Measured against all {cal['resolved']} resolved rows the scorer gets",
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
        "Answer by adding `decl` and `lean_trust` to the row in `docs/theory/theorem_ledger.json`.",
        "",
    ]
    proposals = propose(index, ledger)
    shown = 0
    for row in proposals["rows"]:
        if row["confidence"] != "review" or not row["candidates"]:
            continue
        top = row["candidates"][0]
        decl = docs.get(("formal/" + row["lean"], top["decl"]))
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
        if row.get("names_own"):
            out.append(f"*Statement names: {', '.join('`' + n + '`' for n in row['names_own'])}*")
            out.append("")
        others = ", ".join(f"`{c['decl']}` ({c['score']})" for c in row["candidates"][1:])
        if others:
            out.append(f"*Runners-up: {others}*")
            out.append("")
        if row.get("definitions"):
            defs = ", ".join(f"`{d['decl']}`" for d in row["definitions"])
            out.append(f"*If this row describes a definition rather than a theorem: {defs}*")
            out.append("")
    out.insert(7, f"{shown} rows below, of {proposals['unresolved']} unresolved.\n")
    return "\n".join(out) + "\n"


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
    sub.add_parser("dag", help="rebuild the claim graph over ledger-carrying modules")
    sub.add_parser("propose", help="rank declarations for rows that name none")
    sub.add_parser("papers", help="each manuscript's reachable trust surface")
    sub.add_parser("review", help="write the confident proposals as a readable digest")
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
            print(f"   off the kernel: {s['compiler_trusted'] or 'none'}")
            if s["open"]:
                print(f"   carrying sorry: {s['open']}")
        return 0

    if args.cmd == "propose":
        index = load()
        ledger = json.load(io.open(LEDGER, encoding="utf-8"))
        out = propose(index, ledger)
        PROPOSALS.parent.mkdir(parents=True, exist_ok=True)
        PROPOSALS.write_text(json.dumps(out, indent=2, sort_keys=True) + "\n", encoding="utf-8")
        print(f"{out['unresolved']} unresolved rows; {out['worth_reviewing']} worth reviewing; "
              f"{out['composite']} name two or more of their own declarations")
        return 0

    if args.cmd == "dag":
        index = load()
        ledger = json.load(io.open(LEDGER, encoding="utf-8"))
        graph = dag(index, ledger)
        DAG.parent.mkdir(parents=True, exist_ok=True)
        DAG.write_text(json.dumps(graph, indent=2, sort_keys=True) + "\n", encoding="utf-8")
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
