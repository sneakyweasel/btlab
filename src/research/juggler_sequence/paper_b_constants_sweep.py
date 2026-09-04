"""Paper B constants sweep, third pass: only genuine comparisons.

Shape A  c * P^(-g)  <=  margin        threshold (c/margin)^(1/g)
Shape B  c * P^a     <=  P^b   (a<b)   threshold c^(1/(b-a))

Rules that keep the earlier false positives out:
  * treat LaTeX thin spaces as whitespace so coefficients bind to their power;
  * only pair two terms when a comparison operator separates them, never a product;
  * ignore a coefficient that is the denominator of a \\tfrac immediately before P.
"""
import io
import re
from fractions import Fraction as F

PATH = "docs/theory/juggler_parity_discrepancy_note.md"
P0 = 8.9458e13
MARGIN = 0.25

CMP = re.compile(r"\\le|\\ll|\\leq|\\subseteq|\\to0")


def ev(expr: str):
    e = expr.replace("tfrac", "").replace("frac", "").replace(" ", "").replace("\\", "")
    toks = re.findall(r"[+-]?[0-9]+(?:/[0-9]+)?", e)
    if not toks or "".join(toks) != e:
        return None
    try:
        return sum(F(t) for t in toks)
    except Exception:
        return None


def terms_with_pos(line: str):
    """(coefficient, exponent, position). Coefficient 1 when absent or part of a \\tfrac."""
    s = line.replace(r"\,", " ").replace(r"\;", " ").replace(r"\ ", " ")
    out = []
    for m in re.finditer(r"(?:([0-9]+(?:\.[0-9]+)?)\s*)?P\^\{([^{}]*)\}", s):
        e = ev(m.group(2))
        if e is None:
            continue
        c = 1.0
        if m.group(1):
            pre = s[max(0, m.start(1) - 12): m.start(1)]
            if "tfrac" not in pre and "frac" not in pre:
                c = float(m.group(1))
        out.append((c, e, m.start(), m.end(), s))
    return out


def main() -> None:
    lines = io.open(PATH, encoding="utf-8").read().split("\n")
    A, B = [], []
    for i, line in enumerate(lines):
        ts = terms_with_pos(line)
        ctx = " ".join(lines[max(0, i - 2): i + 3])
        for k, (c, e, st, en, s) in enumerate(ts):
            # Shape A: a decaying term with a constant, in a domination context
            if c > 1.0 and e < 0 and re.search(r"dominated|inside|to0|o\(1\)|negligible", ctx):
                A.append({"line": i + 1, "const": c, "exp": e,
                          "thr": (c / MARGIN) ** (1 / float(-e)), "text": line.strip()[:62]})
            # Shape B: compared (not multiplied) against a later bare power of higher exponent
            if c <= 1.0:
                continue
            for (c2, e2, st2, en2, _s) in ts[k + 1:]:
                between = s[en:st2]
                if not CMP.search(between):
                    continue
                if c2 != 1.0 or e2 <= e or float(e2 - e) > 0.5:
                    break
                B.append({"line": i + 1, "const": c, "a": e, "b": e2,
                          "thr": c ** (1 / float(e2 - e)), "text": line.strip()[:62]})
                break

    for name, rows, key in (("A (decay vs margin 1/4)", A, "exp"), ("B (cost inside a power)", B, "a")):
        seen, uniq = set(), []
        for r in rows:
            k = (r["const"], r[key], r.get("b"))
            if k in seen:
                continue
            seen.add(k)
            uniq.append(r)
        uniq.sort(key=lambda r: -r["thr"])
        print("== Shape %s: %d comparisons" % (name, len(uniq)))
        for r in uniq[:12]:
            flag = "   <-- ABOVE P_0" if r["thr"] > P0 else ""
            extra = " -> %s" % r["b"] if "b" in r else ""
            print("   %-6d c=%-7s P^%s%s   holds from %.2e%s"
                  % (r["line"], r["const"], r.get("exp", r.get("a")), extra, r["thr"], flag))
            if flag:
                print("          | %s" % r["text"])
        print("   above P_0: %d" % sum(1 for r in uniq if r["thr"] > P0))
        print()


def findings() -> list[dict]:
    """The two comparisons this sweep found above P_0, now fixed in the manuscript."""
    return [
        {"site": "Claim D", "printed": "2.52 P^(7/72) <= P^(1/8)", "gap": "1/36",
         "const": 2.52, "threshold": 2.52 ** 36,
         "was": "checked against a standing P_0 of size 1e24; would have been P_0 = 2.8e14",
         "now": "resolved by carrying |t| <= 3 P^(1/24) instead of 16 P^(1/24): "
                "the constant becomes 3^(1/3) < 1.45 and the row drops to 6.4e5"},
        {"site": "Thm 5.3 St.3(a)", "printed": "23 P^(19/24) <= P^(7/8)", "gap": "1/12",
         "const": 23.0, "threshold": 23.0 ** 12,
         "was": "false at P_0 by a factor 245",
         "now": "restated against the real budget P^(23/24), true from 1.5e8"},
    ]


if __name__ == "__main__":
    main()
