"""Source import reachability, paper surfaces and claim DAGs."""
from __future__ import annotations

import collections
import re
from collections import defaultdict
from typing import Any
from . import identities as _fp_identities
from . import source as _fp_source
from . import workspace as _fp_workspace


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
    "Paper D": "Problems.Collatz.NegativeMCycles",
    "Paper E": "Problems.JugglerCollatzPaper",
}

"""The module each manuscript's formalization claims to track.

Reachability from these roots is what a trust sentence in a paper is actually about.  A
directory grep answers a different question -- `formal/Problems/Juggler/` holds modules no
paper imports -- and would let a `native_decide` land inside a paper's surface while the
count outside it stayed reassuring.
"""


_IDENT = re.compile(r"[A-Za-z_][A-Za-z0-9_'.]*")


_HEAD = re.compile(rf"(?:^|\n)[ \t]*(?:{_fp_source._ATTR})*{_fp_source._MODIFIER}"
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
        text = _fp_source.blank_comments((_fp_workspace.ROOT / path).read_text(encoding="utf-8"))
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

    Imports describe module use, not which English claim uses another claim.
    This navigation graph intentionally stays at module granularity. Recorded
    written proof routes and separately projected compiled declaration edges live
    in claim_graph/claim_query. Transitive reduction keeps this view readable;
    current counts are computed below, never embedded in the documentation.
    """
    file_to_mod = {m["file"]: name for name, m in index["modules"].items()}
    rows: dict[str, list[str]] = defaultdict(list)
    for row in ledger:
        ref = row.get("lean")
        if isinstance(ref, str) and ref.endswith(".lean"):
            mod = file_to_mod.get(_fp_identities.lean_key(ref))
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
