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

import collections
import re
from fractions import Fraction
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
     r"9.9" + BS + r"cdot10^{18}", {}),
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
            "Step 5's cell sum",
            "the cross-coefficient bound 63/64 <= 1.2"),
    "1.1": ("the (s2) window-boundary cost, 0.65/sqrt(0.35)",
            "Theorem 4.4's Lemma 3.3 sum",
            "Step 5b's good pieces"),
    "1.5": ("the cell count", "the offset term's floor"),
}

SHARED_TABLE_ANCHOR = "*Constants that share a value.*"

# The passage documenting this check quotes the relations it found, so it is cut from the
# scan for the same reason the shared-value table is: a checker must not read its own output.
RELATION_PROSE_ANCHOR = "A third check reads the manuscript as arithmetic."


def shared_value_audit() -> list[dict[str, Any]]:
    text = paper_text()
    start = text.find(SHARED_TABLE_ANCHOR)
    table = "" if start < 0 else text[start:start + 1800]
    return [{"value": v, "roles": roles, "listed": v in table,
             "occurrences": len(re.findall(r"(?<![0-9.^{/])" + re.escape(v) + r"(?![0-9])", text))}
            for v, roles in sorted(SHARED_VALUES.items())]



# --- generating the list rather than curating it -------------------------------------------
#
# A numeral's role is discriminated by what it multiplies: 0.11 k P^(-7/8) and
# 0.11 uh P^(-1/4) fall into different clusters.  Restricting to math mode removes section
# numbers and prose cross-references ("Theorem 4.7", "Section 1.2 Related work") at a stroke.
#
# It is a filter, not a replacement.  It cannot see a role that multiplies nothing -- 0.35's
# second is the endpoint of a bracket [0.35, 2.6] -- nor one written in another notation for
# the same number: 1.5's second role is printed as the fraction 3/2.  It found 1.1, and
# 1.2's fourth role, both of which curation had missed.  And it flags 0.35 and 1.5 for the
# wrong reason: the clusters it splits there are two notations for one quantity, while the
# actual second roles stay invisible.  The list is kept by both methods.

_MATH = re.compile(re.escape(BS + "(") + r"(.+?)" + re.escape(BS + ")")
                   + "|" + re.escape(BS + "[") + r"(.+?)" + re.escape(BS + "]"), re.S)
_DECIMAL = re.compile(r"(?<![0-9.^{/e-])([0-9]+\.[0-9]+)(?![0-9])")
_MULTIPLICAND = re.compile(r"((?:" + BS + r"[a-zA-Z]+|[A-Za-z](?:_[0-9a-z]|_\{[^}]*\})?"
                           r"|\^\{[^}]*\}|\^[0-9])+)")


def _signature(after: str) -> str:
    """What the numeral multiplies, normalised."""
    s = after
    for junk in (BS + ",", BS + "!", BS + ";", BS + " ", "{+}", "{-}", "~"):
        s = s.replace(junk, "")
    m = _MULTIPLICAND.match(s)
    return (m.group(1) if m else "(bare)")[:24]


def cluster_numerals(min_clusters: int = 2) -> list[dict[str, Any]]:
    """Every math-mode decimal, clustered by what it multiplies.

    The table this paper prints is excluded from the scan: it quotes the collisions it
    documents, and counting those would make the generator agree with itself.
    """
    text = paper_text()
    cut = text.find(SHARED_TABLE_ANCHOR)
    if cut >= 0:
        text = text[:cut] + text[cut + 1800:]
    seen: dict[str, list[str]] = {}
    for m in _MATH.finditer(text):
        span = m.group(1) or m.group(2) or ""
        for n in _DECIMAL.finditer(span):
            seen.setdefault(n.group(1), []).append(_signature(span[n.end():n.end() + 40]))
    out = []
    for value, sigs in seen.items():
        clusters = collections.Counter(s for s in sigs if s != "(bare)")
        if len(clusters) >= min_clusters:
            out.append({"value": value, "clusters": dict(clusters),
                        "cluster_count": len(clusters), "occurrences": len(sigs)})
    return sorted(out, key=lambda r: (-r["cluster_count"], -r["occurrences"]))


def cluster_coverage() -> dict[str, Any]:
    """What the generator sees of the curated list, and what it cannot see."""
    flagged = {r["value"] for r in cluster_numerals()}
    curated = set(SHARED_VALUES)
    text = paper_text()
    total = {n.group(1) for m in _MATH.finditer(text)
             for n in _DECIMAL.finditer(m.group(1) or m.group(2) or "")}
    return {"numerals_scanned": len(total),
            "flagged": sorted(flagged), "curated": sorted(curated),
            "found_by_both": sorted(flagged & curated),
            "curated_only": sorted(curated - flagged),
            # flagged, but the clusters it splits are two notations for one quantity; the
            # actual second role is invisible to a check that reads what a numeral multiplies.
            "flagged_for_the_wrong_reason": {
                "0.35": "clusters uhP^(-3/4) and uh, both the Stage-4 curvature; the second "
                        "role is the bracket endpoint [0.35, 2.6], which multiplies nothing",
                "1.5": "clusters hP^(1/2) and hY', both the cell count; the second role is "
                       "printed as the fraction 3/2"},
            "genuinely_detected": ["0.11", "1.1", "1.2"]}


# --- every printed numeric relation, evaluated -----------------------------------------------
#
# The clusterer's blind spot is notation: it reads 1.5 and 3/2 as unrelated.  Normalising every
# literal to a rational removes that, and answers a question nobody had asked -- is any decimal
# printed inconsistently with its own exact value?
#
# One was.  Claim D's shift comparison printed `1.45^36 = 1.1e6`; the value is 6.44537e5, and
# Appendix A.1's own row for it already said 6.4e5.  The prose contradicted the table, and both
# figures sit far under P_0, so nothing downstream moved.

_FRACS = tuple(re.compile(p) for p in (
    re.escape(BS) + r"t?frac\{(-?[0-9]+)\}\{([0-9]+)\}$",
    re.escape(BS) + r"t?frac(-?[0-9])\{([0-9]+)\}$",
    re.escape(BS) + r"t?frac(-?[0-9])([0-9])$"))

_STRIP = (BS + ",", BS + "!", BS + ";", BS + " ", BS + "bigl", BS + "bigr",
          BS + "Bigl", BS + "Bigr", BS + "left", BS + "right", "{+}", "{-}")


def to_expression(side: str) -> str | None:
    """A math side built only of numeric literals and arithmetic -> a Python expression."""
    s = side.strip()
    for junk in _STRIP:
        s = s.replace(junk, "")
    for _ in range(6):
        new = re.sub(re.escape(BS) + r"t?frac\{([^{}]+)\}\{([^{}]+)\}", r"((\1)/(\2))", s)
        new = re.sub(re.escape(BS) + r"t?frac([0-9])\{([^{}]+)\}", r"((\1)/(\2))", new)
        new = re.sub(re.escape(BS) + r"t?frac([0-9])([0-9])(?![0-9])", r"((\1)/(\2))", new)
        if new == s:
            break
        s = new
    s = s.replace(BS + "cdot", "*").replace(BS + "times", "*")
    s = re.sub(r"\^\{([^{}]+)\}", r"**(\1)", s)
    s = re.sub(r"\^([0-9])", r"**\1", s)
    if not re.fullmatch(r"[0-9.+\-*/() ]+", s):
        return None
    # juxtaposition is multiplication in print and a call in Python: reject it
    return None if re.search(r"[0-9)]\s*\(", s) else s


def to_rational(side: str) -> Fraction | None:
    """The same, exactly, when the side is a single literal."""
    s = side.strip()
    for junk in _STRIP:
        s = s.replace(junk, "")
    s = s.strip()
    for f in _FRACS:
        m = f.fullmatch(s)
        if m:
            return Fraction(int(m.group(1)), int(m.group(2)))
    if re.fullmatch(r"-?[0-9]+/[0-9]+", s):
        a, b = s.split("/")
        return Fraction(int(a), int(b))
    if re.fullmatch(r"-?[0-9]+(\.[0-9]+)?", s):
        return Fraction(s)
    return None


_LITERAL_HEAD = re.compile("^((?:" + re.escape(BS) + "cdot|" + re.escape(BS)
                           + "t?frac|[0-9.()+*/^{}-])+)")


def leading_literal(side: str) -> tuple[float | None, str, str]:
    """Split a side into its leading numeric factor, the symbolic remainder, and the head text.

    ``(1.20)^{1/2}(uh)^{1/2}P^{5/8}`` -> ``(1.0954..., "(uh)^{1/2}P^{5/8}", "(1.20)^{1/2}")``.
    The head text is kept because the printed precision of a side is a property of its digits,
    not of the symbols after them.  Relations whose
    two sides carry the *same* remainder are then comparable, which is most of the paper's
    displayed algebra; without this the checker only sees the handful of pure-number lines.
    """
    s = side.strip()
    for junk in _STRIP:
        s = s.replace(junk, "")
    s = s.strip()
    m = _LITERAL_HEAD.match(s)
    if not m:
        return None, s, ""
    head, tail = m.group(1), s[m.end():]
    while head and (head.count("{") != head.count("}")
                    or head.count("(") != head.count(")")
                    or head[-1] in "+-*/^"):
        head, tail = head[:-1], head[-1] + tail
    if not head:
        return None, s, ""
    expression = to_expression(head)
    if expression is None:
        return None, s, ""
    try:
        value = eval(expression, {"__builtins__": {}}, {})   # noqa: S307 - regex-gated literals
    except (ArithmeticError, SyntaxError, ValueError, TypeError):
        return None, s, ""
    return float(value), tail.strip(), head


def _split_top(span: str) -> tuple[list[str], list[str]]:
    out: list[str] = []
    ops: list[str] = []
    cur: list[str] = []
    depth = 0
    i = 0
    while i < len(span):
        ch = span[i]
        if ch == "{":
            depth += 1
        elif ch == "}":
            depth -= 1
        if depth == 0:
            if span.startswith(BS + "le", i) or span.startswith(BS + "ge", i):
                out.append("".join(cur)); ops.append(span[i:i + 3]); cur = []; i += 3; continue
            if ch == "=":
                out.append("".join(cur)); ops.append("="); cur = []; i += 1; continue
        cur.append(ch)
        i += 1
    out.append("".join(cur))
    return out, ops


def _mantissa(printed: str) -> str:
    """The printed mantissa: `2.8` from `2.8\\cdot10^{14}`, `219` from `219`."""
    s = printed.strip().split(BS + "cdot")[0].strip()
    return s if re.fullmatch(r"-?[0-9]*\.?[0-9]+", s) else ""


def _sig_figures(printed: str) -> int:
    m = _mantissa(printed).lstrip("-").lstrip("0").lstrip(".").lstrip("0")
    digits = re.sub(r"[^0-9]", "", m)
    return max(1, len(digits))


def _last_place(printed: str) -> float:
    """One unit in the last printed decimal place of the mantissa, scaled by any power of ten."""
    m = _mantissa(printed)
    if not m:
        return 0.0
    decimals = len(m.split(".")[1]) if "." in m else 0
    power = re.search(r"cdot10\^\{(-?[0-9]+)\}", printed)
    return 10.0 ** (-decimals + (int(power.group(1)) if power else 0))


def numeric_relations() -> list[dict[str, Any]]:
    """Every relation whose two sides are literal arithmetic, evaluated and classified.

    Two sides qualify either as pure numbers, or as one number times a symbolic factor that
    both sides share -- most of the paper's displayed algebra is of the second kind.

    ``exact`` when the two sides agree; ``rounded`` when the right side is the left correctly
    rounded to its own printed precision; ``bounded_up`` / ``bounded_down`` when it is within
    one unit of the last place but rounded away from nearest, in one direction or the other;
    ``WRONG`` otherwise.
    """
    text = paper_text()
    cut = text.find(RELATION_PROSE_ANCHOR)
    if cut >= 0:
        end = text.find("### ", cut)
        text = text[:cut] + (text[end:] if end >= 0 else "")
    rows: list[dict[str, Any]] = []
    for m in _MATH.finditer(text):
        span = m.group(1) or m.group(2) or ""
        sides, ops = _split_top(span)
        for k, op in enumerate(ops):
            lhs, rhs = sides[k], sides[k + 1]
            ea, eb = to_expression(lhs), to_expression(rhs)
            shared = ""
            printed = rhs.strip()
            if ea is not None and eb is not None:
                try:
                    a = eval(ea, {"__builtins__": {}}, {})   # noqa: S307 - regex-gated
                    b = eval(eb, {"__builtins__": {}}, {})   # noqa: S307
                except (ArithmeticError, SyntaxError, ValueError, TypeError):
                    continue
            else:
                a, ta, _ = leading_literal(lhs)
                b, tb, printed = leading_literal(rhs)
                if a is None or b is None or not ta or ta != tb:
                    continue
                shared = ta
            if op == "=":
                kind = classify_equality(a, b, printed)
            else:
                ok = a <= b + 1e-12 if op.endswith("le") else a >= b - 1e-12
                kind = "exact" if ok else "WRONG"
            rows.append({"lhs": lhs.strip()[:40], "op": op, "rhs": rhs.strip()[:40],
                         "left": float(a), "right": float(b), "kind": kind,
                         "shared": shared[:40]})
    return rows


# Relations whose two sides carry a factor stated in prose, outside the math span.
RELATION_EXCEPTIONS: dict[tuple[str, str], str] = {
    ("7/5800", "12.0690"): "the balance budget is quoted in units of 10^(-4), said in prose",
}


def classify_equality(a: float, b: float, printed: str) -> str:
    """How the printed decimal ``b`` (as written in ``printed``) relates to the true value ``a``.

    Separated out so the three near-miss cases can be exercised directly.  They are the whole
    point of the check: ``bounded_up`` and ``bounded_down`` are indistinguishable to any test
    that only asks whether two numbers agree to the precision shown.
    """
    if abs(a - b) < 1e-12 * max(1.0, abs(a)):
        return "exact"
    sig = _sig_figures(printed)
    ulp = _last_place(printed)
    if float("%.*e" % (sig - 1, a)) == float("%.*e" % (sig - 1, b)):
        return "rounded"
    if 0 <= b - a <= ulp:
        return "bounded_up"
    if -ulp <= b - a < 0:
        return "bounded_down"
    return "WRONG"


def rounding_directions() -> dict[str, list[dict[str, Any]]]:
    """The relations whose printed decimal is not the nearest one, split by direction.

    Both of the paper's two such decimals feed upper bounds, and both are rounded up, i.e.
    away from the inequality they serve.  A ``bounded_down`` row would be a decimal rounded
    into its own bound -- arithmetically within a unit of the last place, and yet a weaker
    claim than the paper states.  That list must stay empty.
    """
    rows = numeric_relations()
    return {"up": [r for r in rows if r["kind"] == "bounded_up"],
            "down": [r for r in rows if r["kind"] == "bounded_down"]}


def wrong_relations() -> list[dict[str, Any]]:
    return [r for r in numeric_relations()
            if r["kind"] == "WRONG"
            and (r["lhs"], r["rhs"]) not in RELATION_EXCEPTIONS]


# --- A.1's least-P column against the certificate ---------------------------------------------
#
# The column names a P from which each row holds, so its entries are not measurements and must
# not be rounded to nearest.  Claim D's shift range crosses at 644537; printing 6.4e5 asserts
# the row over [6.4e5, 644537), where it fails.  Twenty of the thirty-eight entries had been
# nearest-rounded below their crossings, and three were not roundings at all -- a threshold off
# by a factor of 373, a constant (30.5) that appears nowhere else in the paper, and an interval
# endpoint (3.94) superseded by Lemma 5.2b's own 3.90.
#
# The check is one-sided on purpose: printed >= computed, never printed == computed.

A1_ANCHOR = "### A.1 The certificate"
_A1_SPLIT = re.compile("(?<!" + re.escape(BS) + ")" + re.escape("|"))
_A1_SCI = re.compile(r"([0-9.]+)" + re.escape(BS) + r"cdot10\^\{([0-9]+)\}")


def _certificate_rows() -> dict[str, Any]:
    import importlib.util
    spec = importlib.util.spec_from_file_location(
        "p0_certificate", REPO_ROOT / "src" / "research" / "juggler_sequence" / "p0_certificate.py")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)                                    # type: ignore[union-attr]
    return {r["claim"].replace(" ", ""): r for r in module.thresholds()}


def _a1_cell_value(cell: str) -> float | None:
    c = cell.strip().strip("$")
    if c == "always":
        return 0.0
    m = _A1_SCI.fullmatch(c)
    if m:
        return float(m.group(1)) * 10 ** int(m.group(2))
    return float(c) if re.fullmatch(r"[0-9]+", c) else None


def a1_rows() -> list[dict[str, Any]]:
    """The parsed A.1 table: claim, site, printed least P."""
    text = paper_text()
    start = text.index(A1_ANCHOR)
    table = text[start:text.index("###", start + len(A1_ANCHOR))]
    out = []
    for line in table.splitlines():
        if not line.startswith("|") or set(line.rstrip()) <= set("|-: ") or "least $P$" in line:
            continue
        cells = [c.strip() for c in _A1_SPLIT.split(line)[1:-1]]
        if len(cells) != 3:
            continue
        out.append({"claim": cells[0], "site": cells[1], "cell": cells[2],
                    "printed": _a1_cell_value(cells[2])})
    return out


def a1_threshold_audit() -> list[dict[str, Any]]:
    """Each A.1 entry against the crossing `p0_certificate` computes for the same claim."""
    rows = _certificate_rows()
    out = []
    for r in a1_rows():
        key = r["claim"].replace(BS, "").replace(" ", "")
        cert = rows.get(key)
        computed = None if cert is None else cert["P_min"]
        printed = r["printed"]
        if cert is None or printed is None:
            ok = False
        elif computed is None or computed <= 1.0:
            ok = r["cell"].strip("$") == "always"
        else:
            ok = printed >= computed * (1 - 1e-9)
        out.append({"claim": r["claim"][:60], "tag": None if cert is None else cert["tag"],
                    "cell": r["cell"], "printed": printed, "computed": computed, "ok": ok,
                    "overshoot": (None if not computed or not printed or computed <= 1.0
                                  else printed / computed - 1)})
    return out


def a1_failures() -> list[dict[str, Any]]:
    return [r for r in a1_threshold_audit() if not r["ok"]]



# --- the certificate's claim strings against its own predicates --------------------------------
#
# Each certificate row carries a sentence and a lambda.  A.1 prints the sentence and the
# threshold; the threshold comes from the lambda.  Nothing had ever checked that the two describe
# the same inequality, and two rows did not.  `st5b-qpp` printed the merged bound
# 48.9 P^(-3/16) <= 1/4 while certifying the sharper unmerged form, a factor 5.574 apart, so
# 48.9 (3.0e11)^(-3/16) = 0.345 at the row's own threshold.  `39-beta` printed 2.31 where the
# derivation gives 2.30422, one part in four hundred, and failed the same way.
#
# The parser is deliberately narrow: it reads only claims that reduce to arithmetic in P, and
# reports the rest as unparsed rather than guessing.

_CLAIM_OPS = ("<=", ">=", "<", ">")
_CLAIM_AT = re.compile(r"\bat\s+([A-Za-z_][A-Za-z0-9_]*)\s*(?:=|<=|>=)\s*(.+)$")


def _claim_to_python(expr: str) -> str | None:
    """A claim fragment in P (and R_0, rho_0, pi) as a Python expression, or None."""
    s = expr.strip()
    s = s.replace("R_0", "(P**(5/16))").replace("rho_0", "(1/1856)")
    s = re.sub(r"(?<![A-Za-z0-9_])pi(?![A-Za-z0-9_])", "(3.141592653589793)", s)
    s = re.sub(r"\^\(([^()]*)\)", r"**(\1)", s)
    s = re.sub(r"\^(-?[0-9]+)", r"**(\1)", s)
    s = re.sub(r"(?<=[0-9)])\s*(?=[A-Za-z(])", "*", s)
    s = re.sub(r"(?<=[A-Za-z)])\s+(?=\()", "*", s)
    s = re.sub(r"(?<=\))\s+(?=[0-9])", "*", s)        # ") 6" -- juxtaposition after a group
    return None if re.search(r"[A-Za-z]", s.replace("P", "")) else s


def _admissible(fragment: str) -> bool:
    """A left-truncation is only a candidate if it could be a whole expression.

    Without this the truncation loop keeps sliding until *something* evaluates, and what
    evaluates is a sub-expression of the claim rather than the claim: the q'' row's
    `(1.85 P^(7/24) + R_0) 6 P^(-5/4) / (0.35 P^(-3/4))` silently became its own tail
    `P^(-5/4) / (0.35 P^(-3/4))`, crossing at 4702 instead of 2.98e11.
    """
    f = fragment.strip()
    return bool(f) and f.count("(") == f.count(")") and f[0] not in "+*/^)"


def _claim_sides(text: str) -> tuple[str, str, str] | None:
    for op in _CLAIM_OPS:
        i = text.find(op)
        if i >= 0:
            return text[:i].strip(), op, text[i + len(op):].strip()
    return None


def _claim_fragments(claim: str) -> list[tuple[str, str, str]]:
    out: list[tuple[str, str, str]] = []
    heads = [claim]
    if ":" in claim:
        head, tail = claim.split(":", 1)
        heads = [tail.strip(), head.strip(), claim]
    for h in heads:
        parts = _claim_sides(h)
        if parts is None:
            # "|c''/2|/S <= rho_0: (0.053/0.56) P^(-1/4)" -- the tail is the quantity the head
            # bounds, so it inherits the head's operator and right side
            top = _claim_sides(claim.split(":", 1)[0]) if ":" in claim else None
            if top is not None and h.strip():
                out.append((h.strip(), top[1], top[2].split(":")[0].strip()))
            continue
        lhs, op, rhs = parts
        deeper = _claim_sides(rhs)
        out.append((lhs, op, deeper[0] if deeper else rhs))
    return out


def claim_predicate(claim: str) -> tuple[Any, str] | tuple[None, None]:
    """The inequality a claim sentence states, as a function of P, plus its normalised text."""
    subs: dict[str, str] = {}
    m = _CLAIM_AT.search(claim)
    if m:
        subs[m.group(1)] = m.group(2).strip()
        claim = claim[:m.start()].strip()
    for lhs0, op, rhs0 in _claim_fragments(claim):
        for lhs1 in (lhs0.split("=") if "=" in lhs0 else [lhs0]):
            for rhs1 in (rhs0.split("=") if "=" in rhs0 else [rhs0]):
                tokens = lhs1.split()
                for i in range(len(tokens)):
                    left, right = " ".join(tokens[i:]), rhs1.strip()
                    if not _admissible(left) or not _admissible(right):
                        continue
                    for name, val in subs.items():
                        pat = "(?<![A-Za-z0-9_])" + re.escape(name) + "(?![A-Za-z0-9_])"
                        left = re.sub(pat, "(" + val + ")", left)
                        right = re.sub(pat, "(" + val + ")", right)
                    a, b = _claim_to_python(left), _claim_to_python(right)
                    if a is None or b is None or "P" not in a + b:
                        continue
                    try:
                        f = eval("lambda P: (%s) %s (%s)" % (a, op, b),   # noqa: S307
                                 {"__builtins__": {}})
                        f(1e10), f(1e2)
                    except Exception:                                    # noqa: BLE001
                        continue
                    return f, "%s %s %s" % (a, op, b)
    return None, None


def claim_predicate_audit() -> list[dict[str, Any]]:
    """Each row's claim sentence, solved independently, against the row's own crossing."""
    import importlib.util
    spec = importlib.util.spec_from_file_location(
        "p0_certificate", REPO_ROOT / "src" / "research" / "juggler_sequence" / "p0_certificate.py")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)                                    # type: ignore[union-attr]
    out = []
    for r in module.thresholds():
        f, shown = claim_predicate(r["claim"])
        if f is None:
            out.append({"tag": r["tag"], "parsed": False, "agree": None,
                        "predicate": r["P_min"], "claim": None, "reads": None})
            continue
        lp = module.least_P(f)
        claim_p = None if lp is None else 10.0 ** lp
        pred_p = r["P_min"]
        if claim_p is None or pred_p is None:
            agree = claim_p is None and pred_p is None
        else:
            agree = abs(claim_p - pred_p) <= 1e-3 * max(claim_p, pred_p)
        out.append({"tag": r["tag"], "parsed": True, "agree": agree,
                    "predicate": pred_p, "claim": claim_p, "reads": shown})
    return out


def claim_predicate_failures() -> list[dict[str, Any]]:
    return [r for r in claim_predicate_audit() if r["parsed"] and not r["agree"]]



# --- P_0 from the constants the paper prints ---------------------------------------------------
#
# P_0 is quoted to five figures and comes from one row, the Step 5b balance W = V + E <= c_7 S/2.
# Every constant in that row is printed somewhere in the manuscript, so the headline number should
# be reproducible from the paper alone.  It was not: E's definition printed 171 P^(-25/24) where
# the derivation gives 85.3 * 2 = 170.6 and Lean proves 170.6, and with 171 the crossing is
# 3.5969e13, not 3.5858e13.  Two values for one constant, and the one the paper displayed was not
# the one the number was computed from.

_BSX = re.escape(BS)
_P0_PATTERNS = {
    "E_lead": (_BSX + r"lvert f''-" + _BSX + r"Lambda" + _BSX + r"rvert" + _BSX
               + r"le([0-9.]+)P\^\{-25/24\}", "E's leading coefficient"),
    "E_tail": (r"le[0-9.]+P\^\{-25/24\}\+([0-9.]+)P\^\{-5/6\}=:E", "E's second term"),
    "lambda_0": (r"([0-9.]+)P\^\{-5/8\}" + _BSX + r"le S", "the S floor"),
    "kappa_den": (r"V:=" + _BSX + r"tfrac1\{([0-9]+)\}S\^\{1/2\}P\^\{-11/24\}", "kappa in V"),
    "c7_den": (r"c_7=" + _BSX + r"tfrac1\{([0-9]+)\}", "c_7"),
}


def printed_binding_constants() -> dict[str, Any]:
    """The five constants of the Step 5b balance, read off the manuscript."""
    text = paper_text()
    out: dict[str, Any] = {}
    for key, (pattern, label) in _P0_PATTERNS.items():
        m = re.search(pattern, text)
        out[key] = {"value": float(m.group(1)) if m else None, "role": label}
    return out


def p0_from_printed_constants() -> dict[str, Any]:
    """Re-solve the binding row from those constants alone, and compare with what is printed.

    Deliberately independent of ``p0_certificate``: the point is that the paper reproduces its
    own headline number, not that two copies of the same code agree.
    """
    c = printed_binding_constants()
    if any(v["value"] is None for v in c.values()):
        return {"ok": False, "missing": [k for k, v in c.items() if v["value"] is None]}
    e_lead, e_tail = c["E_lead"]["value"], c["E_tail"]["value"]
    lam, kappa, c7 = c["lambda_0"]["value"], 1.0 / c["kappa_den"]["value"], 1.0 / c["c7_den"]["value"]

    def holds(P: float) -> bool:
        S = lam * P**-0.625
        W = kappa * S**0.5 * P ** (-11 / 24) + e_lead * P ** (-25 / 24) + e_tail * P ** (-5 / 6)
        return W <= c7 * S / 2.0

    lo, hi = 0.0, 300.0                      # bisection in log10 P, as the certificate does
    for _ in range(400):
        mid = (lo + hi) / 2.0
        if holds(10.0**mid):
            hi = mid
        else:
            lo = mid
    solved = 10.0**hi
    m = re.search(r"([0-9]\.[0-9]{4})"
                  + re.escape(BS + "cdot10^{13}" + BS + ")."), paper_text())
    printed = float(m.group(1)) * 1e13 if m else None
    return {"ok": printed is not None and abs(solved / printed - 1.0) < 5e-5,
            "solved": solved, "printed": printed, "constants": {k: v["value"] for k, v in c.items()}}



# --- P_1 and the kappa table --------------------------------------------------------------------
#
# P_1 is the least P at which the middle band beats the trivial bound, so it is a crossing and
# rounds up for the same reason A.1's column does: printing 9.8e18 for 9.83914e18 names a P at
# which the estimate is still the weaker one.  Eleven of the kappa table's fifteen entries were
# nearest-rounded below their true values -- a second threshold table that A.1's convention had
# never been applied to.
#
# The solver is again a second implementation, reading its constants out of the manuscript.

KAPPA_TABLE_ANCHOR = r"| \(\kappa\) | \(P_0\) | \(P_1\) (A.5) | boundary coefficient |"
_KAPPA_ROW = re.compile(
    re.escape(BS) + r"tfrac1(?:" + re.escape(BS) + r"?\{?([0-9]+)\}?)"
    r"[^|]*\|" + r"[^|]*?([0-9.]+)" + re.escape(BS) + r"cdot10\^\{([0-9]+)\}"
    r"[^|]*\|" + r"[^|]*?([0-9.]+)" + re.escape(BS) + r"cdot10\^\{([0-9]+)\}"
    r"[^|]*\|" + r"[^|]*?([0-9.]+)" + re.escape(BS) + r"\)")


def p1_crossing(kappa: float, lam: float, e_lead: float, e_tail: float,
                c7: float, N: float = 3.5) -> float:
    """Least P with 4P W/(c_7 S) + P (W/(c_7 S))^(1/2) + N P^(13/24) V^(-1/2) <= P."""
    def ok(P: float) -> bool:
        S = lam * P**-0.625
        V = kappa * S**0.5 * P ** (-11 / 24)
        W = V + e_lead * P ** (-25 / 24) + e_tail * P ** (-5 / 6)
        return 4 * P * W / (c7 * S) + P * (W / (c7 * S)) ** 0.5 + N * P ** (13 / 24) * V**-0.5 <= P
    lo, hi = 1.0, 300.0
    for _ in range(400):
        mid = (lo + hi) / 2.0
        lo, hi = (lo, mid) if ok(10.0**mid) else (mid, hi)
    return 10.0**hi


def kappa_table_audit() -> list[dict[str, Any]]:
    """Every entry of the kappa table against a solve from the manuscript's own constants.

    The P_0 column needs the certificate, since it is a maximum over all thirty-eight rows; the
    P_1 column and the boundary coefficient are solved here from the printed constants alone.
    """
    import importlib.util
    spec = importlib.util.spec_from_file_location(
        "p0_certificate", REPO_ROOT / "src" / "research" / "juggler_sequence" / "p0_certificate.py")
    cert = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(cert)                                    # type: ignore[union-attr]

    c = printed_binding_constants()
    lam = c["lambda_0"]["value"]
    e1, e2 = c["E_lead"]["value"], c["E_tail"]["value"]
    c7 = 1.0 / c["c7_den"]["value"]

    text = paper_text()
    start = text.find(KAPPA_TABLE_ANCHOR)
    block = text[start:text.find(chr(10) + chr(10), start)] if start >= 0 else ""
    out = []
    for m in _KAPPA_ROW.finditer(block):
        den = int(m.group(1))
        kappa = 1.0 / den
        p0_printed = float(m.group(2)) * 10 ** int(m.group(3))
        p1_printed = float(m.group(4)) * 10 ** int(m.group(5))
        coef_printed = float(m.group(6))
        p0_true = 10.0 ** max(r["log10_P_min"] for r in cert.thresholds(kappa=kappa))
        p1_true = p1_crossing(kappa, lam, e1, e2, c7)
        coef_true = 3.5 * (kappa * lam**0.5) ** -0.5
        out.append({"kappa_den": den,
                    "P0": (p0_printed, p0_true, p0_printed >= p0_true * (1 - 1e-9)),
                    "P1": (p1_printed, p1_true, p1_printed >= p1_true * (1 - 1e-9)),
                    "coef": (coef_printed, coef_true, coef_printed >= coef_true * (1 - 1e-9))})
    return out


def kappa_table_failures() -> list[dict[str, Any]]:
    return [r for r in kappa_table_audit()
            if not (r["P0"][2] and r["P1"][2] and r["coef"][2])]



# --- A.6's exponent table -----------------------------------------------------------------------
#
# The third threshold table, and the third to be nearest-rounded: twelve of its twenty-five
# entries named a P below the crossing they stand for.  Its a = 5/16 row is four of A.1's rows at
# the exponent actually used, so the two tables must agree there, and they did not -- A.1 had been
# raised two ticks earlier and A.6 had not.  A convention stated in one appendix does not
# propagate itself.

A6_ANCHOR = r"| \(a\) | collision | \(q''\) | window | flat cost | worst |"
A6_EXPONENTS = ((1, 4), (9, 32), (5, 16), (1, 3), (3, 8))
A6_SITES = ("collision", "qpp", "window", "flat", "worst")
# the four A.1 rows the a = 5/16 row duplicates, in the table's column order
A6_SHARED_TAGS = ("st2-collision", "st5b-qpp", "t63-window", "t63-flat")


def _depth5_C(P: float) -> float:
    return (9 / 16) * 2 * P ** (1 / 96) * (2 * P) ** (3 / 16)


def a6_site_crossings(a: float) -> list[float]:
    """The four depth-five sites at Vaaler truncation R_0 = P^a, plus their maximum."""
    def solve(f: Any) -> float:
        lo, hi = 0.0, 300.0
        for _ in range(400):
            mid = (lo + hi) / 2.0
            lo, hi = (lo, mid) if f(10.0**mid) else (mid, hi)
        return 10.0**hi
    out = [solve(lambda P: 3 * P ** (a / 2) * P**0.75 <= P ** (23 / 24)),
           solve(lambda P: (1.85 * P ** (7 / 24) + P**a) * 6 * P ** (-5 / 4)
                 / (0.35 * P**-0.75) <= 0.25),
           solve(lambda P: P**a >= 8 * (1 + _depth5_C(P))),
           solve(lambda P: 8 * (1 + _depth5_C(P)) / P**a <= P ** (-1 / 96))]
    return out + [max(out)]


def a6_table_audit() -> list[dict[str, Any]]:
    text = paper_text()
    start = text.find(A6_ANCHOR)
    block = text[start:text.find(chr(10) + chr(10), start)] if start >= 0 else ""
    cells = re.findall(r"([0-9.]+)" + re.escape(BS) + r"cdot10\^\{([0-9]+)\}", block)
    out = []
    for i, (num, den) in enumerate(A6_EXPONENTS):
        row = cells[i * 5:(i + 1) * 5]
        if len(row) != 5:
            continue
        true = a6_site_crossings(num / den)
        for j, site in enumerate(A6_SITES):
            printed = float(row[j][0]) * 10 ** int(row[j][1])
            out.append({"a": "%d/%d" % (num, den), "site": site, "printed": printed,
                        "computed": true[j], "ok": printed >= true[j] * (1 - 1e-9),
                        "overshoot": printed / true[j] - 1})
    return out


def a6_failures() -> list[dict[str, Any]]:
    rows = [r for r in a6_table_audit() if not r["ok"]]
    a1 = {r["tag"]: r["printed"] for r in a1_threshold_audit()}
    shared = [r for r in a6_table_audit() if r["a"] == "5/16" and r["site"] != "worst"]
    for r, tag in zip(shared, A6_SHARED_TAGS):
        if a1.get(tag) != r["printed"]:
            rows.append({**r, "ok": False, "disagrees_with": tag, "a1": a1.get(tag)})
    return rows



# --- Proposition 7.1's density table, from the dynamic program it describes ---------------------
#
# The one table in this paper whose entries are exact integers with a stated algorithm behind
# them: N_d counts words of length d whose lattice path keeps 3^{o_t} >= 2^t throughout, "a
# two-line dynamic program over the triangle, exact in integers".  Running it reproduces all seven
# rows and all five columns.  What did not survive was a figure in the prose beside it: the
# Hoeffding-loss ratio at d = 1600 was printed 1.3e4 and is 1.13e4, where the other three values
# quoted with it are right to under a per cent.

def nd_counts(depth: int) -> list[int]:
    """N_d for every d <= depth, exactly.  N_d = #{w : 3^{o_t(w)} >= 2^t for all t <= d}."""
    omin, o, p3, p2 = [0] * (depth + 1), 0, 1, 1
    for t in range(depth + 1):
        while p3 < p2:
            o += 1
            p3 *= 3
        omin[t] = o
        p2 *= 2
    cur: dict[int, int] = {0: 1}
    out = [1]
    for t in range(1, depth + 1):
        nxt: dict[int, int] = {}
        for odd, count in cur.items():
            for step in (0, 1):                       # E contributes no odd letter, O one
                if odd + step >= omin[t]:
                    nxt[odd + step] = nxt.get(odd + step, 0) + count
        cur = nxt
        out.append(sum(cur.values()))
    return out


def endpoint_only(d: int) -> int:
    """The closed form's count: every constraint dropped but o_d >= d log2/log3."""
    import math
    thr = d * math.log(2) / math.log(3)
    return sum(math.comb(d, o) for o in range(d + 1) if o >= thr - 1e-12)


def hoeffding_c() -> float:
    """c = 2(log2/log3 - 1/2)^2, the exponent of Hoeffding's bound on the endpoint count."""
    import math
    return 2.0 * (math.log(2) / math.log(3) - 0.5) ** 2


def sharp_rate() -> float:
    """rho = min_theta (1/2)((3/2)^theta + 2^(-theta)), the true per-letter rate."""
    f = lambda t: 0.5 * (1.5**t + 2.0**-t)            # noqa: E731  strictly convex in theta
    lo, hi = -50.0, 50.0
    for _ in range(300):
        a, b = lo + (hi - lo) / 3, hi - (hi - lo) / 3
        lo, hi = (lo, b) if f(a) < f(b) else (a, hi)
    return f((lo + hi) / 2)


PROP71_ROWS = (4, 5, 6, 8, 12, 16, 24)
PROP71_RATIOS = ((5, 6.7), (10, 11.4), (40, 43.6), (1600, 1.13e4))


def prop71_audit() -> dict[str, Any]:
    """The printed table and the four ratios beside it, against the program the paper describes."""
    import math
    text = paper_text()
    start = text.find(r"| \(d\) | \(N_d\) | endpoint only |")
    block = text[start:text.find(chr(10) + chr(10), start)] if start >= 0 else ""
    printed = re.findall(r"^\|[^|]*?([0-9]+)[^|]*\|[^|]*?([0-9]+)[^|]*\|[^|]*?([0-9]+)[^|]*\|"
                         r"[^|]*?([0-9]+)[^|]*\|[^|]*?([0-9.]+)[^|]*\|[^|]*?([0-9.]+)[^|]*\|"
                         r"[^|]*?([0-9.]+)[^|]*\|$", block, re.M)
    N = nd_counts(1600)
    c, rho = hoeffding_c(), sharp_rate()
    rows = []
    for cells in printed:
        d = int(cells[0])
        rows.append({"d": d, "N_d": (int(cells[1]), N[d]), "endpoint": (int(cells[2]), endpoint_only(d)),
                     "two_d": (int(cells[3]), 2**d),
                     "ratio": (float(cells[4]), N[d] / 2**d),
                     "hoeffding": (float(cells[5]), math.exp(-c * d)),
                     "density": (float(cells[6]), 1 - N[d] / 2**d)})
    ratios = [{"d": d, "printed": want,
               "computed": math.exp(-c * d + d * math.log(2) - math.log(N[d]))}
              for d, want in PROP71_RATIOS]
    return {"rows": rows, "ratios": ratios, "c": c, "rho": rho}


def prop71_failures() -> list[dict[str, Any]]:
    a = prop71_audit()
    bad: list[dict[str, Any]] = []
    for r in a["rows"]:
        for key in ("N_d", "endpoint", "two_d"):
            if r[key][0] != r[key][1]:
                bad.append({"d": r["d"], "column": key, **{"printed": r[key][0], "computed": r[key][1]}})
        for key in ("ratio", "hoeffding", "density"):
            printed, computed = r[key]
            if abs(printed - computed) > 0.5 * 10 ** -_sig_decimals(printed):
                bad.append({"d": r["d"], "column": key, "printed": printed, "computed": computed})
    for r in a["ratios"]:
        if abs(r["computed"] / r["printed"] - 1) > 0.02:
            bad.append({"d": r["d"], "column": "loss ratio", "printed": r["printed"],
                        "computed": r["computed"]})
    return bad


def _sig_decimals(x: float) -> int:
    s = repr(x)
    return len(s.split(".")[1]) if "." in s else 0



# --- the run-length table's row sums -------------------------------------------------------------
#
# Not a threshold table: its entries are exact dyadic gains, so nothing rounds.  What it does have
# is an invariant -- the gain column is the sum of the run columns beside it -- and an exact
# invariant is worth a test precisely because no rounding convention protects it.

RUNLENGTH_ANCHOR = r"| \(d\) | gain | run \(2\) | run \(3\) | run \(4\) | run \(5\) | run \(\ge6\) |"


def runlength_rows() -> list[dict[str, Any]]:
    text = paper_text()
    start = text.find(RUNLENGTH_ANCHOR)
    block = text[start:text.find(chr(10) + chr(10), start)] if start >= 0 else ""
    out = []
    for line in block.splitlines():
        if not line.startswith("|") or set(line.rstrip()) <= set("|-: ") or "gain" in line:
            continue
        cells = [c.strip() for c in line.strip("|").split("|")]
        if len(cells) != 7:
            continue
        vals = [to_rational(c.replace(BS + "(", "").replace(BS + ")", "")) if c.strip() else Fraction(0)
                for c in cells]
        out.append({"d": vals[0], "gain": vals[1], "runs": vals[2:]})
    return out


def runlength_failures() -> list[dict[str, Any]]:
    bad = []
    for r in runlength_rows():
        if any(v is None for v in [r["gain"]] + r["runs"]):
            bad.append({"d": r["d"], "why": "unparsed cell"})
            continue
        total = sum(r["runs"], Fraction(0))
        if total != r["gain"]:
            bad.append({"d": r["d"], "gain": r["gain"], "sum_of_runs": total})
    return bad



# --- what the paper's machine-checked column actually rests on -----------------------------------
#
# `trust_boundary` checks that a cited Lean name is declared and that its module is reachable from
# the Paper B root.  Neither says the declaration is *proved*.  A `sorry` anywhere in its
# dependency graph, or a `native_decide`, leaves the name declared, the module reachable and the
# build green while the paper's machine-checked column asserts something false.
#
# `formal/AxiomCheckPaperB.lean` prints the axiom dependencies of every cited declaration and
# `AxiomCheckPaperB.expected` records the output.  All forty-six read
# [propext, Classical.choice, Quot.sound] -- Mathlib's three and nothing else.

AXIOM_CHECK = REPO_ROOT / "formal" / "AxiomCheckPaperB.lean"
AXIOM_EXPECTED = REPO_ROOT / "formal" / "AxiomCheckPaperB.expected"
MATHLIB_AXIOMS = "[propext, Classical.choice, Quot.sound]"


def axiom_check_names() -> list[str]:
    """The declarations the artifact interrogates."""
    return re.findall(r"^#print axioms ([A-Za-z0-9_']+)$",
                      AXIOM_CHECK.read_text(encoding="utf-8"), re.M)


def axiom_check_results() -> dict[str, str]:
    """Recorded output: declaration -> the axiom list it depends on."""
    out = {}
    for line in AXIOM_EXPECTED.read_text(encoding="utf-8").splitlines():
        m = re.match(r"^'Problems\.Juggler\.([A-Za-z0-9_']+)' depends on axioms: (\[.*\])$", line)
        if m:
            out[m.group(1)] = m.group(2)
    return out


def axiom_failures() -> list[dict[str, Any]]:
    """A cited declaration missing from the artifact, unrecorded, or resting on more than the three."""
    import importlib.util
    spec = importlib.util.spec_from_file_location("trust_boundary", REPO_ROOT / "tools" / "trust_boundary.py")
    tb = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(spec and tb)                              # type: ignore[arg-type]
    cited = sorted({r["name"] for r in tb.audit() if r["declared"]})
    listed, results = axiom_check_names(), axiom_check_results()
    bad: list[dict[str, Any]] = []
    for name in cited:
        if name not in listed:
            bad.append({"name": name, "why": "cited and declared, but the artifact does not ask"})
        elif name not in results:
            bad.append({"name": name, "why": "asked, but no recorded result"})
        elif results[name] != MATHLIB_AXIOMS:
            bad.append({"name": name, "why": "rests on more than Mathlib's three",
                        "axioms": results[name]})
    for name in listed:
        if name not in cited:
            bad.append({"name": name, "why": "the artifact asks about a name the paper no longer cites"})
    return bad



# --- the certificate's Lean rows, paired with the crossings they certify -------------------------
#
# `lean_numeral_audit` excludes ThresholdCertificate from its numeral audit, on the stated ground
# that "ThresholdCertificate's rows are paired by p0_certificate.LEAN_ROWS, which carries the
# substitution and the rational witness too".  There is no LEAN_ROWS in p0_certificate and never
# was, so those thirty-three theorems -- and the rational witnesses 1.92, 1.46, 0.06237, 0.65076
# on which the certified thresholds rest -- were audited by nothing.  This is the missing pairing.
#
# It also settles the count.  The manuscript said "33 theorems: the window-boundary and
# lambda_0-range rows each split in two", which would make forty, not thirty-three.  The truth is
# 38 - 7 + 2: seven rows have no Lean theorem at all.

THRESHOLD_LEAN = REPO_ROOT / "formal" / "Problems" / "Juggler" / "ThresholdCertificate.lean"
_LEAN_ROW = re.compile(r"^theorem (row_\w+)\s*\(t : " + chr(8477) + r"\)\s*\(ht : ([0-9.]+) " +
                       chr(8804) + r" t\)", re.M)
# the two rows each split into two theorems, and the three whose names do not transliterate
# the substitution exponents this paper uses; P = t^k with k a denominator of its exponent
# lattice, which is (1/96)Z.  Fitting over all of 1..96 admits neighbours of the true k.
LEAN_ROW_EXPONENTS = (1, 2, 3, 4, 6, 8, 12, 16, 24, 32, 36, 48, 72, 96)
LEAN_ROW_TAGS = {"row_5a_binding": "5a-W<=c7S", "row_5b_binding": "5b-W<=c7S",
                 "row_5b_E_only": "5b-E<=c7S", "row_s3s2_bdry_a": "s3s2-bdry",
                 "row_s3s2_bdry_b": "s3s2-bdry", "row_5b_lam0_upper": "5b-lam0-range",
                 "row_5b_lam0_lower": "5b-lam0-range"}


def _tag_of(theorem: str) -> str:
    return LEAN_ROW_TAGS.get(theorem, theorem[4:].replace("_", "-"))


def lean_rows() -> list[dict[str, Any]]:
    """Each `row_*` theorem with its rational witness t_0."""
    src = THRESHOLD_LEAN.read_text(encoding="utf-8")
    return [{"theorem": m.group(1), "tag": _tag_of(m.group(1)), "witness": float(m.group(2))}
            for m in _LEAN_ROW.finditer(src)]


def lean_row_audit() -> dict[str, Any]:
    """Every Lean row against the crossing its Python predicate bisects.

    The substitution exponent k is fitted rather than read: several claim strings quote an
    exponent the predicate does not use, so k is taken as those values in 1..96 putting
    t_0^k at or just above the crossing, and the fit is reported as a set.  A row whose
    witness certifies *below* the crossing would be a false Lean theorem, so what this
    really measures is how conservative each witness is.
    """
    import importlib.util
    import math
    spec = importlib.util.spec_from_file_location(
        "p0_certificate", REPO_ROOT / "src" / "research" / "juggler_sequence" / "p0_certificate.py")
    cert_mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(cert_mod)                                # type: ignore[union-attr]
    cert = {r["tag"]: r for r in cert_mod.thresholds()}

    rows, covered = [], set()
    for r in lean_rows():
        row = dict(r)
        c = cert.get(r["tag"])
        row["in_certificate"] = c is not None
        covered.add(r["tag"])
        pmin = c["P_min"] if c else None
        if pmin is None or pmin <= 1.0 or r["witness"] <= 1.0:
            row["k"], row["certified"], row["loss"] = [], None, None
        else:
            lw, lp = math.log(r["witness"]), math.log(pmin)
            ks = [k for k in LEAN_ROW_EXPONENTS if -1e-9 <= k * lw - lp <= math.log(4.0)]
            row["k"] = ks
            row["certified"] = math.exp(min(ks) * lw) if ks else None
            row["loss"] = (row["certified"] / pmin) if ks else None
        row["crossing"] = pmin
        rows.append(row)
    return {"rows": rows,
            "uncovered": sorted(set(cert) - covered),
            "distinct_tags": len(covered),
            "certified_P0": max((r["certified"] for r in rows if r["certified"]), default=None)}


def lean_row_failures() -> list[dict[str, Any]]:
    a = lean_row_audit()
    bad = []
    for r in a["rows"]:
        if not r["in_certificate"]:
            bad.append({"theorem": r["theorem"], "why": "names no certificate row"})
        elif r["crossing"] and r["crossing"] > 1.0 and not r["k"]:
            bad.append({"theorem": r["theorem"], "why": "no substitution puts its witness "
                        "at or just above the crossing", "witness": r["witness"],
                        "crossing": r["crossing"]})
    return bad



# --- Theorem 6.3's second exponent, across every place that prints it ----------------------------
#
# The OOEO* half of Theorem 6.3 was printed at N^(43/48) on a proof that dropped the jY/2 mode of
# the four-wave product and centered a Fourier frequency dynamically.  With both repaired the
# surviving balance is a = 1/48, so the exponent is 47/48.  That number appears in the manuscript,
# the theorem ledger, the Lean exponent checks and the Python audit, and nothing compared them --
# which is how 43/48 came to stand in six documents at once.
#
# 47/48 = 94/96 is still under 1 - 1/96 = 95/96, so Corollary 6.4 keeps its form with one
# ninety-sixth of room where the superseded value had nine.

DEPTH5_EXPONENT = Fraction(47, 48)
DEPTH5_SUPERSEDED = Fraction(43, 48)
DEPTH5_SOURCES = {
    "manuscript": ("docs/theory/juggler_parity_discrepancy_note.md",
                   r"=" + re.escape(BS) + r"tfrac N\{32\}\+O" + re.escape(BS) + r"bigl\(N\^\{(\d+)/(\d+)\+"),
    "ledger_json": ("docs/theory/theorem_ledger.json", r"OOEOO\(N\) = N/32 \+ O\(N\^\{(\d+)/(\d+)\+eps\}\)"),
    "lean": ("formal/Problems/Juggler/DepthFourFive.lean",
             r"theorem cor64_error_exponent : \((\d+)/(\d+) : " + chr(8474) + r"\)"),
    "audit": ("src/research/juggler_sequence/paper_b_audit.py",
              r"6\.4: error is the worse exponent, (\d+)/(\d+) <= 1 - 1/96"),
}


def depth5_exponents() -> dict[str, Any]:
    """The OOEO* error exponent as each file prints it."""
    out: dict[str, Any] = {}
    for name, (path, pattern) in DEPTH5_SOURCES.items():
        text = (REPO_ROOT / path).read_text(encoding="utf-8")
        hits = {Fraction(int(a), int(b)) for a, b in re.findall(pattern, text)}
        out[name] = sorted(hits)
    return out


def depth5_failures() -> list[dict[str, Any]]:
    bad = []
    for name, found in depth5_exponents().items():
        if found != [DEPTH5_EXPONENT]:
            bad.append({"source": name, "found": [str(f) for f in found],
                        "want": str(DEPTH5_EXPONENT)})
    # the arithmetic the exponent rests on, and the room it leaves Corollary 6.4
    if -Fraction(1, 32) + Fraction(1, 48) / 2 != -Fraction(1, 48):
        bad.append({"source": "balance", "why": "truncation and mixed term do not meet at 1/48"})
    if 1 - Fraction(1, 48) != DEPTH5_EXPONENT:
        bad.append({"source": "saving", "why": "1 - 1/48 is not the exponent"})
    room = 1 - Fraction(1, 96) - DEPTH5_EXPONENT
    if room != Fraction(1, 96) or room <= 0:
        bad.append({"source": "corollary 6.4", "why": "the combined error no longer absorbs it",
                    "room": str(room)})
    return bad



# --- divided bounds in Lean hypotheses -----------------------------------------------------------
#
# Scavenged from prove2.me's CircleMethod.aux_sum_min_le, whose formalization note explains why
# Vaughan's Lemma 2.2 is stated with the hypothesis `2‖kα‖ * g k ≤ 1` and not `g k ≤ 1/(2‖kα‖)`:
# in Lean `1/0 = 0`, so the divided form is silently *weaker* exactly at the singular mode, which
# is the mode that matters.  Paper B is full of divided bounds with removable singularities --
# Lemma 3.7's `min (2, 1/(π|u+B|))` among them -- so the same trap is available here.
#
# Every divided-form hypothesis in Paper B's Lean currently divides by a nonzero literal or is
# guarded by a positivity hypothesis on the same signature.  Nothing enforced that, which is what
# this does.  The denominator extraction is a heuristic on the source text, not a parse; it errs
# toward reporting, so a false positive is a prompt to write the multiplicative form rather than a
# bug in the guard.

PAPER_B_LEAN_MODULES = ("BranchFreeze", "MasterIdentity", "MeanValues", "MonomialSplitting",
                        "PaperBAssembly", "ThresholdCertificate", "DepthFourFive")
_LEAN_DECL = re.compile(r"^(?:private )?(?:theorem|lemma) (\w+)(.*?):=", re.S | re.M)
_LEAN_BINDER = re.compile(r"\((\w+)\s*:\s*([^()]*(?:\([^()]*\)[^()]*)*)\)")
_DENOM = re.compile(r"/\s*(\([^()]*\)|[0-9]+(?:\.[0-9]+)?|\w+)")
_LEAN_LITERAL = re.compile(r"^[0-9]+(?:\.[0-9]+)?$")


def _denominator_symbols(denominator: str) -> set[str]:
    return set(re.findall(r"(?<![A-Za-z0-9_])([A-Za-z]\w*)", denominator)) - {"Real", "sqrt"}


def divided_denominator_status(denominator: str, guards: str) -> str:
    """How a denominator is protected: by being a nonzero literal, by a positivity hypothesis,
    or not at all.  Separated out so the guard's teeth can be exercised directly."""
    if _LEAN_LITERAL.match(denominator):
        return "literal" if float(denominator) != 0.0 else "UNGUARDED"
    symbols = _denominator_symbols(denominator)
    if not symbols:
        return "UNGUARDED"
    for symbol in symbols:
        e = re.escape(symbol)
        if (re.search(r"0\s*<\s*" + e + r"(?![A-Za-z0-9_])", guards)
                or re.search(e + r"\s*(?:" + chr(8800) + r"|!=)\s*0", guards)
                or re.search(r"0\s*<\s*[0-9]+\s*\*\s*" + e, guards)):
            continue
        return "UNGUARDED"
    return "guarded"


def divided_hypotheses() -> list[dict[str, Any]]:
    """Every hypothesis binder in Paper B's Lean whose body divides, with how it is protected."""
    out: list[dict[str, Any]] = []
    for module in PAPER_B_LEAN_MODULES:
        path = REPO_ROOT / "formal" / "Problems" / "Juggler" / (module + ".lean")
        if not path.exists():
            continue
        src = path.read_text(encoding="utf-8")
        for decl in _LEAN_DECL.finditer(src):
            name, signature = decl.group(1), decl.group(2)
            binders = list(_LEAN_BINDER.finditer(signature))
            guards = " ".join(b.group(2) for b in binders)
            for binder in binders:
                body = " ".join(binder.group(2).split())
                if "/" not in body:
                    continue
                for denominator in _DENOM.findall(body):
                    d = denominator.strip("() ")
                    status = divided_denominator_status(d, guards)
                    out.append({"module": module, "theorem": name, "binder": binder.group(1),
                                "denominator": d, "status": status, "body": body[:70]})
    return out


def divided_hypothesis_failures() -> list[dict[str, Any]]:
    return [r for r in divided_hypotheses() if r["status"] == "UNGUARDED"]


def failures() -> dict[str, list[Any]]:
    return {"constants": [r for r in constant_audit() if not r["ok"]],
            "shared": [r for r in shared_value_audit() if not r["listed"]],
            "relations": wrong_relations(),
            "rounded_into_a_bound": rounding_directions()["down"],
            "a1_thresholds": a1_failures(),
            "claim_vs_predicate": claim_predicate_failures(),
            "p0_reproducible": [] if p0_from_printed_constants()["ok"] else
                               [p0_from_printed_constants()],
            "kappa_table": kappa_table_failures(),
            "a6_table": a6_failures(),
            "prop71": prop71_failures(),
            "runlength": runlength_failures(),
            "axioms": axiom_failures(),
            "lean_rows": lean_row_failures(),
            "depth5_exponent": depth5_failures(),
            "divided_hypotheses": divided_hypothesis_failures()}


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
