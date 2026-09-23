"""Pure advisory request formats, cached verdict validation and coverage records."""
from __future__ import annotations

import datetime
import hashlib
import io
import json
from typing import Any, Callable
from . import identities as _fp_identities
from . import matching as _fp_matching
from . import workspace as _fp_workspace


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
    sw = _fp_matching.words(row["statement"])
    return sorted(cands, key=lambda d: _fp_matching.similarity(sw, d), reverse=True)[:limit]


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
        text = _clip(_fp_identities.signature(d), 420)
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


def load_jev() -> dict[str, Any] | None:
    """The committed verdict record, or ``None`` when Jev has never been asked."""
    if not _fp_workspace.JEV.is_file():
        return None
    return json.load(io.open(_fp_workspace.JEV, encoding="utf-8"))


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


def _resolved(
    index: dict[str, Any], ledger: list[dict[str, Any]]
) -> list[tuple[dict[str, Any], list[dict[str, Any]], list[str]]]:
    """Rows that name their declarations, each with those declarations from the index.

    A name the index does not hold is reported rather than skipped silently: the ledger's
    own tests forbid it, so a hit here means the index is stale.  A ``REFUTED`` row is left
    out: its declaration is the refutation, and whether that covers the refuted claim is a
    different question from the retag rule.
    """
    out: list[tuple[dict[str, Any], list[dict[str, Any]], list[str]]] = []
    for row in ledger:
        names = _fp_identities.row_decls(row)
        if not names or row["tag"] == "REFUTED":
            continue
        key = _fp_identities.lean_key(row.get("lean"))
        found, missing = [], []
        for name in names:
            matches = _fp_identities.resolve_declarations(index, name, file=key)
            if len(matches) == 1:
                found.append(matches[0])
            else:
                missing.append(name)
        out.append((row, found, missing))
    return out


def coverage_state(row: dict[str, Any], decls: list[dict[str, Any]]) -> dict[str, Any]:
    """The claim beside every declaration it names, each with docstring and header."""
    return {
        "claim": row["statement"],
        "lean_file": row.get("lean") or "",
        "ledger_id": row["id"],
        "declarations": [
            {"name": d["name"], "qualified_name": d.get("qualified_name"),
             "module": d.get("module"), "docstring": _clip(d.get("doc", ""), 600),
             "statement": _fp_identities.signature(d, limit=12)}
            for d in decls
        ],
    }


def coverage_key(row: dict[str, Any], decls: list[dict[str, Any]]) -> str:
    """Unlike the offer key, this covers the declarations' text: a strengthened header or a
    corrected docstring changes what covers the claim, and re-asking one row is cheap."""
    payload = [JEV_COVERAGE_PROMPT, row["statement"], row.get("lean") or "",
               [[d["name"], d.get("doc", ""), _fp_identities.signature(d, limit=12)] for d in decls]]
    blob = json.dumps(payload, ensure_ascii=False).encode("utf-8")
    return hashlib.sha256(blob).hexdigest()[:16]


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
