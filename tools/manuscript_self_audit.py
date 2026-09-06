"""The manuscript against itself: named constants, and numerals that name more than one thing.

Every other audit in this repository compares the manuscript with something outside it -- Lean
declarations, probe functions, the threshold certificate.  None compares the manuscript with
itself, and three of the errors this audit has found were of exactly that kind: the `0.35`
conflation (Theorem 4.1's Stage-4 curvature read as Lemma 5.2b's pre-correction floor), the
interpolant chain that kept the constants its own lemma's erratum had replaced, and "its own
truncations" for a count that includes one of Theorem 6.1's.

Two checks, because the failure runs both ways.

**A named constant with more than one value.**  `P_0`, `c_7`, `kappa`, `R_0` and the rest are
printed many times.  A naive "do all occurrences agree" check has a hundred percent false
positive rate here -- `c_7` is printed as `1/232`, as the weaker `1/288` the manuscript keeps
on purpose, and as `1/61` where its lever saturates -- so each constant declares its canonical
value *and* its legitimate alternatives with the reason.  A value outside that list is the
failure, which is what a stale figure left after a correction would look like.

**A value naming more than one constant.**  The other direction, and the one that cost the
afternoon.  `0.35`, `0.11`, `1.2` and `1.5` each name several unrelated quantities.  None is an
error; the check is that the manuscript's own table of them, in Appendix A.1, lists every one
this file knows about, so a reader meeting a familiar numeral is told to look twice.

Run ``python tools/manuscript_self_audit.py``.
"""

from __future__ import annotations

import re
from pathlib import Path
from typing import Any

REPO_ROOT = Path(__file__).resolve().parents[1]
PAPER = REPO_ROOT / "docs" / "theory" / "juggler_parity_discrepancy_note.md"
BS = chr(92)


def paper_text() -> str:
    return PAPER.read_text(encoding="utf-8")


# --- a named constant with more than one value ---------------------------------------------
#
# (name, regex capturing the printed value, canonical, {alternative: why it is legitimate})

CONSTANT_VALUES: tuple[tuple[str, str, str, dict[str, str]], ...] = (
    ("P_0", r"P_0\s*=\s*([0-9.]+" + BS + BS + r"cdot10\^\{[-0-9]+\})",
     r"3.6" + BS + r"cdot10^{13}", {}),
    ("P_1", r"P_1\s*=\s*([0-9.]+" + BS + BS + r"cdot10\^\{[-0-9]+\})",
     r"9.8" + BS + r"cdot10^{18}", {}),
    ("c_7", r"c_7\s*=\s*(" + BS + BS + r"tfrac1\{[0-9]+\}|1/[0-9]+)", "1/232", {
        r"" + BS + r"tfrac1{232}": "the same value, set as a fraction",
        "1/288": "the weaker value the manuscript quotes, which remains valid",
        "1/61": "where the c_7 lever saturates against the floor",
        "1/54": "the same crossover before the erratum at Lemma 5.2b",
        "1/228": "the crossover computed against the mode-index row, since retired"}),
    ("kappa", BS + BS + r"kappa\s*=\s*(" + BS + BS + r"tfrac1\{[0-9]+\}|1/[0-9]+)",
     r"" + BS + r"tfrac1{12}", {
        r"" + BS + r"tfrac1{16}": "a row of the kappa sweep in A.2",
        r"" + BS + r"tfrac13": "the superseded operating point"}),
    ("R_0", r"R_0\s*=\s*P\^\{([0-9/]+)\}", "5/16", {
        "1/4": "the superseded truncation, discussed throughout A.6"}),
)


def constant_audit() -> list[dict[str, Any]]:
    text = paper_text()
    out: list[dict[str, Any]] = []
    for name, pattern, canonical, alternatives in CONSTANT_VALUES:
        found = re.findall(pattern, text)
        undeclared = sorted({v for v in found
                             if v != canonical and v not in alternatives})
        out.append({"name": name, "canonical": canonical, "occurrences": len(found),
                    "values": sorted(set(found)), "undeclared": undeclared,
                    "ok": not undeclared and canonical in found})
    return out


# --- a value naming more than one constant -------------------------------------------------
#
# Each entry must appear in the manuscript's own table in Appendix A.1.

SHARED_VALUES: dict[str, tuple[str, ...]] = {
    "0.35": ("Theorem 4.1's Stage-4 curvature",
             "Lemma 5.2b's pre-correction lambda_0 floor"),
    "0.11": ("the smooth remnant |c''|, hence E's second term",
             "the collision band's lower edge",
             "Step 5a's ratio V/S at the lower end"),
    "1.2": ("the Stage-4 curvature's upper end",
            "the (s2) window length",
            "Step 5's cell sum"),
    "1.5": ("the cell count", "the offset term's floor"),
}

SHARED_TABLE_ANCHOR = "*Constants that share a value.*"


def shared_value_audit() -> list[dict[str, Any]]:
    text = paper_text()
    start = text.find(SHARED_TABLE_ANCHOR)
    table = "" if start < 0 else text[start:start + 1800]
    return [{"value": v, "roles": roles, "listed": v in table,
             "occurrences": len(re.findall(r"(?<![0-9.^{/])" + re.escape(v) + r"(?![0-9])", text))}
            for v, roles in sorted(SHARED_VALUES.items())]


def failures() -> dict[str, list[Any]]:
    return {"constants": [r for r in constant_audit() if not r["ok"]],
            "shared": [r for r in shared_value_audit() if not r["listed"]]}


def main() -> None:
    print("The manuscript against itself")
    for r in constant_audit():
        mark = "ok " if r["ok"] else "BAD"
        print("  %s %-8s canonical %-22s %2d occurrences, values %s"
              % (mark, r["name"], r["canonical"], r["occurrences"], r["values"]))
        for v in r["undeclared"]:
            print("        UNDECLARED VALUE %s" % v)
    print()
    for r in shared_value_audit():
        print("  %s %-6s names %d quantities, %d occurrences"
              % ("ok " if r["listed"] else "BAD", r["value"], len(r["roles"]),
                 r["occurrences"]))
        if not r["listed"]:
            print("        NOT IN THE MANUSCRIPT'S OWN TABLE")
    f = failures()
    if not f["constants"] and not f["shared"]:
        print()
        print("  every named constant carries a declared value, and every shared value is listed")


if __name__ == "__main__":
    main()
