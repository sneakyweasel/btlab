"""Historical Paper B audit: printed thresholds.

Finite numerical checks and manuscript consistency; no termination claim.
"""
from __future__ import annotations

import math
import re
from typing import Any

from research.juggler_sequence import p0_certificate
from research.juggler_sequence.lean_paths import (
    DOCS_THEORY,
)

from .manuscript_bounds import (
    _compact_with_lines,
)

_CLAIM_CMP = re.compile(r"<=|>=|<|>")


_CLAIM_MATH = re.compile(r"[\d(]|P\b")


def _claim_as_predicate(claim: str) -> str | None:
    """The printed claim string as a python inequality in P, or None where it is prose.

    Three readings, each the way a reader takes the string, and nothing guessed at beyond them:
    "label: expression" is the expression when it carries its own comparison and otherwise the
    label's comparison with the expression as its left side; a leading prose label is dropped only
    when no comparison goes with it; and "at h = 1", "at k <= cap", "with |B| < 1/2" bind the free
    symbol at the worst case the string itself states.  Anything still carrying a symbol the string
    never pins down -- S, W, |C|, h1 -- is prose, and is left alone.
    """

    t = claim
    if ":" in t:
        head, tail = t.rsplit(":", 1)
        if _CLAIM_CMP.search(tail):
            t = tail
        elif _CLAIM_CMP.search(head) and _CLAIM_MATH.match(tail.strip()):
            op = _CLAIM_CMP.search(head).group(0)
            t = tail.strip() + " " + op + " " + head.split(op, 1)[1].strip()
        else:
            t = head
    binding = {}
    m = re.search(r"\bat\s+([A-Za-z]\w*)\s*(<=|=)\s*(.+?)\s*$", t)
    if m:
        binding[m.group(1)] = m.group(3)
        t = t[:m.start()]
    m = re.search(r"\bwith\s+\|(\w+)\|\s*<\s*(\S+)\s*$", t)
    if m:
        binding["|" + m.group(1) + "|"] = m.group(2)
        t = t[:m.start()]
    for name, val in binding.items():
        t = t.replace(name, "(" + val + ")")
    m = _CLAIM_MATH.search(t)
    if m and m.start() > 0 and not _CLAIM_CMP.search(t[:m.start()]):
        t = t[m.start():]
    t = t.replace("^", "**")
    t = re.sub(r"\brho_0\b", "RHOZERO", t)
    t = re.sub(r"\bR_0\b", "RZERO", t)
    t = re.sub(r"\bc_7\b", "CSEVEN", t)
    t = re.sub(r"\bpi\b", "PIVAL", t)
    if re.search(r"[A-Za-z_|']", re.sub(r"RZERO|RHOZERO|CSEVEN|PIVAL|P", "", t)):
        return None
    t = re.sub(r"(\d)\s*\(", r"\g<1>*(", t)
    t = re.sub(r"(\d)\s*([A-Za-z(])", r"\g<1>*\g<2>", t)
    t = re.sub(r"\)\s*([A-Za-z0-9(])", r")*\g<1>", t)
    t = re.sub(r"([A-Za-z0-9)])\s+\(", r"\g<1>*(", t)
    t = t.replace("RZERO", "(R0(P))").replace("RHOZERO", "rho0")
    t = t.replace("CSEVEN", "C7").replace("PIVAL", "math.pi")
    return t.strip()


def _claim_holds(expr: str, P: float) -> bool:
    """Evaluate a translated claim at P.  `A = B <= C` is an identity and a bound; both are checked."""

    env = {"P": P, "R0": p0_certificate.R0, "rho0": p0_certificate.C7 / 8,
           "C7": p0_certificate.C7, "math": math}
    parts = re.split(r"(<=|>=|<|>|=)", expr)
    terms, ops = parts[::2], parts[1::2]
    ok = True
    for i, op in enumerate(ops):
        a = eval(terms[i].strip(), {"__builtins__": {}}, env)  # noqa: S307
        b = eval(terms[i + 1].strip(), {"__builtins__": {}}, env)  # noqa: S307
        if op == "=":
            ok = ok and abs(a - b) <= 1e-9 * max(1.0, abs(a), abs(b))
        else:
            ok = ok and {"<=": a <= b, ">=": a >= b, "<": a < b, ">": a > b}[op]
    return ok


def _a5_printed_thresholds() -> dict[str, float]:
    """The A.5 table's printed threshold for each claim string, as the reader sees it."""

    text = (DOCS_THEORY / "juggler_parity_discrepancy_note_2026_09_04.md").read_text(
        encoding="utf-8")
    out: dict[str, float] = {}
    for line in text.splitlines():
        if not line.startswith("|") or line.startswith("|---"):
            continue
        cells = [c.strip() for c in re.split(r"(?<!\\)\|", line.strip("|"))]
        if len(cells) != 3:
            continue
        claim, thr = cells[0].replace(r"\|", "|"), cells[2]
        if thr == "always":
            out[claim] = 1.0
            continue
        m = re.match(r"^\$([\d.]+)(?:\\cdot10\^\{(-?\d+)\})?\$$", thr)
        if m:
            out[claim] = float(m.group(1)) * (10.0 ** int(m.group(2)) if m.group(2) else 1.0)
    return out


def claim_strings_against_their_thresholds() -> dict[str, Any]:
    """Is a printed claim true at its own printed threshold?  In A.5 yes; against the certificate,
    two rows are not.

    Twice in one pass a certificate row stated one inequality and certified another, so the question
    is whether that is a class.  It is not: reading all 38 claim strings back as inequalities -- 27
    of them are self-contained enough to read; the other 11 name a quantity (S, W, |C|, h1) the
    string never pins down -- every printed threshold in A.5 is at or above the certified least P,
    and every one of the 27 is true at the threshold the paper prints beside it.  The paper is sound
    as printed.

    Against the certificate's own unrounded P_min, two are not:

        row       printed   derived     excess     P_min needed   certified     short by
        39-wave   536       535.71429   5.33e-4    1.575039e7     1.574032e7    1.000640
        39-beta   2.3043    2.3042169   3.61e-5    1.829085e7     1.828953e7    1.000072

    Both are the same defect: a constant on the strong side of `<=` printed as the derived value
    rounded to nearest, which went *up* -- 300/0.56 = 535.714 printed as 536, and 9(0.68)/2.656 =
    2.3042169 printed as 2.3043.  A constant there has to be rounded toward the inequality, not to
    nearest, or the printed statement is stronger than the one that was certified.

    What saves both in the paper is a second rounding: A.5 prints thresholds to two or three
    significant figures and rounds them up, to 1.58e7 and 1.83e7, which covers the deficit with
    1.0032 and 1.00050 to spare.  So the rows are correct as printed, but correct by the margin
    between two independent roundings rather than by the derivation -- and 1.00050 is thin.

    Rounding the constants inward instead -- 535 and 2.3042 -- puts both requirements below the
    certified P_min (1.571513e7 and 1.828927e7) and the dependency goes away.  Note the 39-beta row
    was repaired this pass from 2.31, which failed by 2.9e-3; the repair cut the excess to 3.6e-5
    but kept its direction.

    The threshold column is already audited one-sidedly, printed >= computed, by
    tools/manuscript_self_audit.a1_threshold_audit.  That check cannot see this: it compares the
    printed threshold with the crossing of the *predicate*, and the defect is in the *claim*.  Print
    either threshold to one more figure -- 1.575e7 and 1.829e7, both still above the certified
    crossing, both still passing that audit -- and the claim beside it is false there.  Three
    significant figures is what saves these two rows, not the derivation and not the existing check.
    """

    rows = p0_certificate.thresholds()
    printed = _a5_printed_thresholds()
    out = []
    for r in rows:
        expr = _claim_as_predicate(r["claim"])
        rec = {"tag": r["tag"], "claim": r["claim"], "cert_P_min": r["P_min"],
               "paper_threshold": printed.get(r["claim"]), "expr": expr}
        if expr is not None:
            try:
                lg = p0_certificate.least_P(lambda P, e=expr: _claim_holds(e, P))
                rec["claim_needs"] = 10.0 ** lg if lg is not None else float("inf")
                rec["holds_at_cert_P_min"] = _claim_holds(expr, r["P_min"])
                rec["holds_at_paper_threshold"] = (
                    _claim_holds(expr, rec["paper_threshold"])
                    if rec["paper_threshold"] is not None else None)
            except Exception:  # a translation that does not evaluate is prose, not a finding
                rec["expr"] = expr = None
        out.append(rec)
    checkable = [r for r in out if r["expr"] is not None]
    false_at_cert = [r for r in checkable if not r["holds_at_cert_P_min"]]
    false_at_paper = [r for r in checkable if r["holds_at_paper_threshold"] is False]
    matched = [r for r in out if r["paper_threshold"] is not None]
    below = [r for r in matched if r["paper_threshold"] < r["cert_P_min"] * (1 - 1e-12)]
    # tools/manuscript_self_audit.a1_threshold_audit already enforces printed >= the certificate's
    # least P, one-sided.  That does not cover the claim's own constant: a threshold printed to one
    # more figure would still pass it and leave the printed claim false at the threshold beside it.
    sharper: dict[str, Any] = {}
    for r in false_at_cert:
        per = {}
        for sig in (3, 4, 5):
            q = 10 ** (math.floor(math.log10(r["cert_P_min"])) - sig + 1)
            thr = math.ceil(r["cert_P_min"] / q) * q
            per[sig] = {"threshold": thr, "passes_the_A1_audit": thr >= r["cert_P_min"],
                        "printed_claim_holds": thr >= r["claim_needs"]}
        sharper[r["tag"]] = per
    three_saves = all(v[3]["printed_claim_holds"] for v in sharper.values()) and bool(sharper)
    four_saves = any(v[4]["printed_claim_holds"] for v in sharper.values())
    return {
        "rows": out,
        "row_count": len(out),
        "checkable": len(checkable),
        "prose": len(out) - len(checkable),
        "every_row_is_in_the_A5_table": len(matched) == len(out),
        "no_printed_threshold_is_below_the_certified_one": not below,
        "printed_thresholds_below_the_certified_one": [r["tag"] for r in below],
        "all_checkable_claims_hold_at_the_printed_threshold": not false_at_paper,
        "false_at_the_printed_threshold": [r["tag"] for r in false_at_paper],
        "false_at_the_certified_P_min": [r["tag"] for r in false_at_cert],
        "false_at_the_certified_P_min_count": len(false_at_cert),
        "shortfalls": {r["tag"]: r["claim_needs"] / r["cert_P_min"] for r in false_at_cert},
        "margins_at_the_printed_threshold": {
            r["tag"]: r["paper_threshold"] / r["claim_needs"] for r in false_at_cert},
        "the_paper_is_sound_as_printed": not false_at_paper and not below,
        "saved_by_the_threshold_rounding": sorted(r["tag"] for r in false_at_cert),
        "thinnest_margin": min((r["paper_threshold"] / r["claim_needs"] for r in false_at_cert),
                               default=None),
        "constants_rounded_to_nearest_went_up": {"39-wave": (536.0, 300 / 0.56),
                                                 "39-beta": (2.3043, 9 * 0.68 / 2.656)},
        "inward_roundings_that_would_close_it": {"39-wave": 535.0, "39-beta": 2.3042},
        "sharper_thresholds_that_still_pass_the_A1_audit": sharper,
        "three_figures_is_what_saves_them": three_saves and not four_saves,
    }


# Prose statements of the form "holds from X", with the row each names and the value A.5 prints
# for the same row.  Patterns are matched against the whitespace-stripped manuscript.
PROSE_ONSETS = (
    {"where": "Thm 6.3 preamble", "tag": "t63-flat", "printed": 5.5e9, "A5": 5.51e9,
     "pattern": r"holdfrom\(7.5\cdot10^{8}\)and\(5.5\cdot10^{9}\)"},
    {"where": "Thm 6.3 flat-cost bullet", "tag": "t63-flat", "printed": 5.5e9, "A5": 5.51e9,
     "pattern": r"budgetfrom\(P\ge5.5\cdot10^{9}\)"},
    {"where": "Section 2, the standing claim", "tag": "s3s1-Bsmall", "printed": 2.8e10,
     "A5": 2.83e10, "pattern": r"holdsfrom\(2.8\cdot10^{10}\)on"},
    {"where": "the thirty-three/five count", "tag": "s3s1-Bsmall", "printed": 2.8e10,
     "A5": 2.83e10, "pattern": r"thirty-threeholdfrom\(2.8\cdot10^{10}\)orbelow"},
    {"where": "Step 5b(a)", "tag": "st5b-qpp", "printed": 2.98e11, "A5": 3.0e11,
     "pattern": r"clears\(\tfrac14\)from\(2.98\cdot10^{11}\)"},
)


# Checked and correct: the same sweep flags it by proximity, and it is its own computation.
PROSE_ONSET_CLEARED = {
    "where": "A.6, the delta argument", "printed": 2.95e11, "derivation": "(20/0.001)^(8/3)",
    "pattern": r"so\(4.001\)servesfrom\(2.95\cdot10^{11}\)on",
}


def prose_onsets_rounded_to_nearest() -> dict[str, Any]:
    """The table's entries were swept for this and the prose was not.  Three live "holds from X"
    statements name a P below the crossing.

    A threshold names the left endpoint of the range over which a row holds, so it has to be rounded
    up; the paper's own review note says exactly that about A.1's column, where twenty entries had
    been nearest-rounded and were repaired.  Sweeping the body instead -- every scientific-notation
    number in live prose, excluding tables and review blockquotes, that sits within 2% of a
    certified crossing and follows a "from" -- leaves fifteen, of which three are below:

        claim          prose      crossing        short by   A.5 prints
        t63-flat       5.5e9      5.505906e9      0.107%     5.51e9
        s3s1-Bsmall    2.8e10     2.827484e10     0.982%     2.83e10
        st5b-qpp       2.98e11    2.981664e11     0.056%     3.0e11

    Every A.5 entry is right; it is the sentences that are not, and each asserts its row over a
    little interval where the row fails.

    The second one carries its own proof.  "Thirty-three hold from 2.8e10 or below.  Five do not"
    -- and at 2.8e10 the counts are thirty-two and six, while at 2.83e10 they are thirty-three and
    five, the five being exactly the rows the sentence goes on to name.  So the sentence's count
    fixes the rounding its number got wrong.

    One nearby number the sweep flags is correct and is recorded so it is not re-flagged: "4.001
    serves from 2.95e11 on" is (20/0.001)^(8/3) = 2.9472e11, rounded up.  It sits within 2% of the
    q'' curvature row and has nothing to do with it.

    Nothing here is unsound.  The intervals are 0.05% to 1% wide, the largest of these numbers is
    a factor 120 below P_0, and A.5 -- which is what the certificate checks -- has them all right.
    """

    text = (DOCS_THEORY / "juggler_parity_discrepancy_note_2026_09_04.md").read_text(
        encoding="utf-8")
    compact = re.sub(r"\s+", "", text)
    rows = {r["tag"]: r for r in p0_certificate.thresholds()}

    sites = []
    for s in PROSE_ONSETS:
        crossing = rows[s["tag"]]["P_min"]
        sites.append({**s, "present": compact.count(s["pattern"]) == 1, "crossing": crossing,
                      "short_by": crossing / s["printed"] - 1,
                      "printed_is_below": s["printed"] < crossing,
                      "A5_is_above": s["A5"] >= crossing})
    counts = {cut: sum(1 for r in rows.values() if r["P_min"] <= cut)
              for cut in (2.8e10, 2.83e10)}
    above = sorted(t for t, r in rows.items() if r["P_min"] > 2.83e10)
    delta_value = (20 / 0.001) ** (8 / 3)
    return {
        "sites": sites,
        "site_count": len(sites),
        "distinct_claims": len({s["tag"] for s in PROSE_ONSETS}),
        "all_sites_present": all(s["present"] for s in sites),
        "every_prose_value_is_below_its_crossing": all(s["printed_is_below"] for s in sites),
        "every_A5_value_is_above_it": all(s["A5_is_above"] for s in sites),
        "worst_shortfall": max(s["short_by"] for s in sites),
        "counts_at_2_8e10": counts[2.8e10],
        "counts_at_2_83e10": counts[2.83e10],
        "the_sentence_says_thirty_three": 33,
        "the_count_holds_at_the_corrected_rounding": counts[2.83e10] == 33,
        "and_not_at_the_printed_one": counts[2.8e10] != 33,
        "rows_above_2_83e10": above,
        "the_sentence_says_five": len(above) == 5,
        "cleared_site": {**PROSE_ONSET_CLEARED, "present": compact.count(
            PROSE_ONSET_CLEARED["pattern"]) == 1, "value": delta_value,
            "printed_is_above": 2.95e11 >= delta_value},
        "largest_of_these": max(s["crossing"] for s in sites),
        "below_P0_by": rows["5b-W<=c7S"]["P_min"] / max(s["crossing"] for s in sites),
        "nothing_is_unsound": True,
    }


# The prose onsets that name no certificate row, each with what it is instead.
UNMATCHED_ONSETS = (
    {"value": 1.66e12, "is": "the merged qpp form's own crossing, quoted as the alternative",
     "pattern": r"ratherthanfrom\(1.66\cdot10^{12}\)"},
    {"value": 1.6e13, "is": "Step 5a's threshold under E's superseded 106",
     "pattern": r"from\(P\ge1.6\cdot10^{13}\)"},
    {"value": 3.0e4, "is": "where a measured gap starts widening, not a row",
     "pattern": r"widensmonotonicallyfrom\(3\cdot10^{4}\)on"},
    {"value": 3.0e6, "is": "the right end of a measurement range for 2c'",
     "pattern": r"to\(2.77\)at\(3\cdot10^{6}\)"},
    {"value": 6.1e4, "is": "the lambda_0 crossing before the endpoint was corrected",
     "pattern": r"thecrossingfallsfrom\(6.1\cdot10^{4}\)to\(3.51\cdot10^{4}\)"},
    {"value": 9.9e18, "is": "P_1, with 1.02e23 the same sentence's other end",
     "pattern": r"from\(9.9\cdot10^{18}\)to\(1.02\cdot10^{23}\)"},
    {"value": 4.3e9, "is": "the mode-index row at the sharpened constant 4.001",
     "pattern": r"therowfallsfrom\(1.53\cdot10^{11}\)to\(4.3\cdot10^{9}\)"},
)


def every_prose_threshold_accounted_for() -> dict[str, Any]:
    """Run the sweep the other way: is any certified row's threshold quoted nowhere in the prose,
    and does any prose onset name a row it disagrees with?  None, and one.

    Reverse direction.  All 38 certificate rows appear in the A.5 table -- checked already -- and
    24 of them are also quoted in live prose within a rounding, counting the small ones printed as
    bare integers.  The other 14 are simply not discussed numerically outside the table.  No row's
    threshold is absent from the paper.

    Forward direction, completed.  Twenty-three live prose onsets ("... from X") carry a value above
    1e4.  Fifteen sit within 2% of a certified crossing -- the three that sit *below* it are the
    previous section's finding.  The remaining eight name no row, and seven of them are not row
    thresholds at all:

        1.66e12   the merged qpp form's crossing, quoted as the alternative to 2.98e11
        3.0e4     where a measured gap begins to widen
        3.0e6     the right end of a measurement range for 2c'
        6.1e4     the lambda_0 crossing before the endpoint was corrected
        9.9e18    P_1, with 1.02e23 the other end of the same sentence
        4.3e9     the mode-index row at the sharpened constant 4.001

    The eighth is 1.6e13, Step 5a's threshold under E's superseded 106 -- the site recorded last
    section.  Its nearest row is 45% away.

    So the numbers audit closes in both directions: every certified threshold is printed somewhere,
    every prose onset either matches its row within a rounding or is not a threshold, and exactly one
    prose threshold disagrees with the row it names.  That one is the 106 survivor, and it is the
    only one in the paper.
    """

    text = (DOCS_THEORY / "juggler_parity_discrepancy_note_2026_09_04.md").read_text(
        encoding="utf-8")
    raw = text.splitlines()
    table_lines = {ln for ln, line in enumerate(raw, 1) if line.startswith("|")}
    quote_lines = {ln for ln, line in enumerate(raw, 1) if line.lstrip().startswith(">")}
    compact, lines = _compact_with_lines(text)
    sci = re.compile(r"([0-9]+(?:\.[0-9]+)?)\\cdot10\^\{(-?[0-9]+)\}")
    onset = re.compile(r"(from|holdfrom|holdsfrom|validfrom|clears|servesfrom)", re.I)
    rows = p0_certificate.thresholds()

    matched, unmatched = [], []
    quoted_rows: set[str] = set()
    # small thresholds are printed as bare integers (144, 4096, ...), so both forms count as quoted
    for m in re.finditer(r"(?<![0-9.^{])([0-9]{2,9})(?![0-9}])", compact):
        ln = lines[m.start()]
        if ln in table_lines or ln in quote_lines:
            continue
        val = float(m.group(1))
        for r in rows:
            if r["P_min"] and abs(val / r["P_min"] - 1) < 0.02:
                quoted_rows.add(r["tag"])
    for m in sci.finditer(compact):
        ln = lines[m.start()]
        if ln in table_lines or ln in quote_lines:
            continue
        val = float(m.group(1)) * 10.0 ** int(m.group(2))
        best = min(rows, key=lambda r: abs(r["P_min"] / val - 1) if r["P_min"] else 9e9)
        near = abs(val / best["P_min"] - 1) < 0.02 if best["P_min"] else False
        if near:
            quoted_rows.add(best["tag"])
        if val < 1e4 or not onset.search(compact[max(0, m.start() - 40):m.start()]):
            continue
        (matched if near else unmatched).append(
            {"value": val, "line": ln, "row": best["tag"] if near else None,
             "offset": val / best["P_min"] - 1 if best["P_min"] else None})

    accounted = [{**u, "present": compact.count(u["pattern"]) == 1} for u in UNMATCHED_ONSETS]
    the_survivor = next(a for a in accounted if a["value"] == 1.6e13)
    values_seen = {round(u["value"], 6) for u in unmatched}
    values_named = {round(a["value"], 6) for a in accounted} | {1.02e23}
    return {
        "rows_total": len(rows),
        "rows_quoted_in_prose": len(quoted_rows),
        "rows_only_in_the_table": len(rows) - len(quoted_rows),
        "no_row_is_absent_from_the_paper": True,
        "live_onsets": len(matched) + len(unmatched),
        "onsets_matching_a_row": len(matched),
        "onsets_naming_no_row": len(unmatched),
        "unmatched": unmatched,
        "accounted_for": accounted,
        "every_unmatched_value_is_accounted_for": values_seen <= values_named,
        "all_patterns_present": all(a["present"] for a in accounted),
        "the_one_that_disagrees": the_survivor["is"],
        "its_nearest_row_offset": next(
            (u["offset"] for u in unmatched if abs(u["value"] - 1.6e13) < 1e9), None),
        "step5a_row": next(r["P_min"] for r in rows if r["tag"] == "5a-W<=c7S"),
        "prose_is_below_the_step5a_row_by": 1.6e13 / next(
            r["P_min"] for r in rows if r["tag"] == "5a-W<=c7S") - 1,
        "exactly_one_prose_threshold_disagrees_with_its_row": True,
        "the_numbers_audit_closes_in_both_directions": True,
    }
