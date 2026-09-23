"""Local claim-to-declaration ranking; suggestions never change evidence."""
from __future__ import annotations

import re
from collections import defaultdict
from typing import Any
from . import identities as _fp_identities
from . import source as _fp_source
from . import verdicts as _fp_verdicts


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
    resolved = [r for r in ledger if len(_fp_identities.row_decls(r)) == 1]
    fires = correct = 0
    for row in resolved:
        cands = by_file.get(_fp_identities.lean_key(row.get("lean")), [])
        if len(cands) < 2:
            continue
        sw = words(row["statement"])
        ranked = sorted(cands, key=lambda d: similarity(sw, d), reverse=True)
        a, b = similarity(sw, ranked[0]), similarity(sw, ranked[1])
        if a >= 0.10 and a >= 1.5 * max(b, 1e-9):
            fires += 1
            correct += ranked[0]["name"] == _fp_identities.row_decls(row)[0]
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
    taken = {(_fp_identities.lean_key(r.get("lean")), name) for r in ledger for name in _fp_identities.row_decls(r)}

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
        key = _fp_identities.lean_key(ref)
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
    verdicts = _fp_verdicts.load_jev() if jev is None else jev
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
        named = [t for t in dict.fromkeys(_fp_source.IDENT.findall(row["statement"]))
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
            offer = ranked_all[:_fp_verdicts.JEV_SHORTLIST]
            field = _fp_verdicts._jev_field(verdict, offer, _fp_verdicts.jev_key(row, offer))
            confident = field["verdict"] == "pick" and field["confidence"] >= _fp_verdicts.JEV_REVIEW
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
        "jev": _fp_verdicts._jev_summary(out),
        "rows": out,
    }
