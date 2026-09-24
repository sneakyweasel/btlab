"""Render review reports from source records and recorded advisory evidence."""
from __future__ import annotations

import collections
from typing import Any
from . import identities as _fp_identities
from . import matching as _fp_matching
from . import verdicts as _fp_verdicts


def coverage_digest(
    index: dict[str, Any], ledger: list[dict[str, Any]], jev: dict[str, Any] | None = None
) -> str:
    """Resolved rows whose declarations may not state the whole claim, lowest coverage first.

    The proposal digest joins rows to declarations; this one asks whether a recorded join is
    complete, which is the retag rule.  Each entry is the row's statement beside every
    declaration it names, docstring and header, with Jev's four probabilities and the failure
    mode it rates highest, so the reviewer knows what to look for before reading.
    """
    verdicts = _fp_verdicts.load_jev() if jev is None else jev
    rows = _fp_verdicts.coverage_rows(index, ledger, verdicts)
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
        f"A row is listed when coverage is below {_fp_verdicts.JEV_COVERAGE_FLAG}, lowest first: below",
        f"{_fp_verdicts.JEV_COVERAGE_LOW} it is filed as not covered, between the two as doubtful.  The other",
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
            out += [f"**Doubtful from here: coverage between {_fp_verdicts.JEV_COVERAGE_LOW} and "
                    f"{_fp_verdicts.JEV_COVERAGE_FLAG}.**", ""]
            marked = True
        out += [f"## {n}. `{r['id']}` &mdash; covers {r['covers']}", ""]
        reading = _fp_verdicts.JEV_COVERAGE_READINGS.get(r["reading"] or "")
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
            out += [f"{head} `{d['name']}` &mdash; source trust {d['trust']}, `{r['lean']}:{d['line']}`",
                    ""]
            if d.get("doc"):
                out += [f"> {d['doc']}", ""]
            out += ["```lean", _fp_identities.signature(d, limit=12) or "(could not read the declaration)",
                    "```", ""]
    return "\n".join(out) + "\n"


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
        other = docs.get((_fp_identities.lean_key(row["lean"]), jv["decl"]))
        trust = other["trust"] if other else "?"
        line = other["line"] if other else "?"
        out += [f"**Jev.** picks `{jv['decl']}` at {conf}, not the scorer's candidate.", "",
                f"**Jev's candidate.** `{jv['decl']}` &mdash; source trust {trust}, "
                f"`{row['lean']}:{line}`", ""]
        if other and other.get("doc"):
            out += [f"> {other['doc']}", ""]
        shown = (_fp_identities.signature(other) if other else "") or "(could not read the declaration)"
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
    verdicts = _fp_verdicts.load_jev() if jev is None else jev
    cal = _fp_matching.calibrate(index, ledger)
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
    proposals = _fp_matching.propose(index, ledger, jev=verdicts)
    s = proposals.get("jev")
    if s:
        out += [
            f"Jev ({', '.join(s['models'])}, last asked {s['asked']}) answered {s['answered']} of",
            f"the unresolved rows: {s['picks']} picks and {s['none']} \"none of these\".",
            f"{s['agree_with_scorer']} of the picks are the scorer's own first candidate, and",
            f"{s['confident']} are at or above {_fp_verdicts.JEV_REVIEW} confidence.  A confident pick lists",
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
            f"right {c['confident_correct']} of {c['confident']} times at or above {_fp_verdicts.JEV_REVIEW}",
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
        decl = docs.get((_fp_identities.lean_key(row["lean"]), top["decl"]))
        shown += 1
        out.append(f"## {shown}. `{row['id']}`")
        out.append("")
        out.append(f"**Row.** {row['statement'][:340]}")
        out.append("")
        out.append(f"**Candidate.** `{top['decl']}` &mdash; source trust {top['trust']}, "
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
        out.append((_fp_identities.signature(decl) if decl else "") or "(could not read the declaration)")
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
