"""Localizing Paper B's kernel theorem to sub-dyadic intervals.

Theorem 5.3 bounds the kernel sum ``K_c`` on a dyadic block ``n ~ P`` by
``P^{1-1/96+eps}``. This module audits how far its proof retains that
same saving. An earlier version also claimed that the resulting threshold
unlocked ``OOOEEE`` and ``OOEOEE``. That application used ``23/32``,
the inverse-length exponent of ``OOEEE``. The proposed words instead
land at exponent ``27/64``, so their broad inverse scale is
``P^{37/64}``. Since ``37/64 < 29/48``, Theorem 5.5 as stated does
not apply to them at the printed saving.

**The accounting.**  Write a cost on an interval of length ``Y = P^y`` inside
``(P, 2P]`` as ``c * Y^alpha * P^beta``.  On the full block it is ``c * P^{alpha+beta}``,
which must be the exponent the manuscript prints.  Three weights occur:

* ``alpha = 1`` *(proportional)*: a per-summand cost, or a sum over cells, windows,
  runs or pieces that partition the interval, so that their number scales with it.
* ``alpha = 0`` *(absolute)*: the cost of one of the ``O(1)`` partial objects at the two
  ends.  A unit cost is a van der Corput inverse root or a transition term, never a
  length.
* ``0 < alpha < 1``: nothing in this proof, once the per-window transition terms are
  read correctly.  They are ``alpha = 0`` costs with a large ``beta``, because
  Lemma 3.8's third term carries no window-length factor, as the manuscript says in
  Stage 5 of Lemma 5.2(i); that is what makes it summable and also what makes it the
  largest absolute cost in the chain.

An ``A``-process ``|S|^2 <= 2N^2/H + (4N/H) sum_h |T_h|`` sends each cost of the
differenced sum to ``(alpha, beta) -> ((1+alpha)/2, beta/2)``: proportional costs are
fixed points, so the printed savings localize verbatim, while an absolute cost is
pushed toward the length rather than squared away.  Three nested ``A``-processes
(Claim C inside Lemma 5.2(ii), then the two of Step 1) carry ``(0, A_1)`` to
``(7/8, A_1/8)``, that is to ``P^{(7y+A_1)/8}``.  The balance that fixes
``H_3 = t^{1/3}P^{1/12}`` is against the shift-*average* of Lemma 5.2(i), not its
maximum, and an average of proportional quantities is proportional; that single fact is
why the exponent ``1/96`` is untouched and the choices ``H_1 = P^{1/48}``,
``H_2 = P^{1/24}``, ``H_3`` are not re-optimized.

**The theorem.**  The largest absolute cost is ``A_1 = P^{25/48}``, the per-window
transition term ``(P/M)^{1/3}`` of Stage 5 of Lemma 5.2(i) at the regime-(s2) constraint
``uh > P^{3/16}``.  Hence

    |K_c(I)| << |I| P^{-1/96+eps} + P^{(7y+25/48)/8},

and the second term is dominated exactly when ``y > 25/48 + 1/12 = 29/48``.  At the
admissible reference length ``y = 23/32``, the absolute chain ends at
``P^{533/768}`` against a target ``P^{17/24} = P^{544/768}``, a margin of
``P^{11/768}``.  A slow twist ``(l/2) n^{9/16}`` with
``|l| <= P^{1/24}`` is removed after the first differencing; uniformly over
``I subset (P,2P]`` its total variation is ``O(P^{-3/8})``.

**The production-scale audit.**  Formally substituting ``y = 37/64`` into the
two-term bookkeeping display leaves the absolute tail below the trivial length by
``37/64 - (7(37/64)+25/48)/8 = 11/1536``. This does not prove a
shorter-interval theorem: ``37/64`` lies outside the theorem's hypothesis, and
the bookkeeping does not transport the exact floor and parity restrictions defining
the production. The ``11/1536`` is a possible salvage obligation, not a proved
production or a new contagion exponent.

Note that ``29/48 > 1/2``: the kernel theorem does **not** localize as far as the
depth-``<=3`` theorems of Section 3.5, which reach ``P^{1/2}``.  The obstruction is the
transition term, and it is real, not an artefact of the bookkeeping.

**What this is.**  Exponent bookkeeping over the printed costs of the manuscript: an
audit of what the existing proof yields on a shorter interval.  No constant is improved
and no step is replaced.  Two things make it checkable rather than asserted.  The
``dyadic`` column of each cost table is the exponent the manuscript prints, and the
tables' maxima must be the printed ``P^{15/16}`` of Lemma 5.2(i) and ``P^{23/24}`` of
``T_2``.  And ``coverage`` accounts for every displayed exponent at least ``1/4`` in
either proof, as a cost, a count, a length, a parameter or a hypothesis, with none left
over; the completeness of the cost tables is the one non-mechanical input, and that is
where it is checked.
"""

from __future__ import annotations

import json
import re
from fractions import Fraction as F
from pathlib import Path
from typing import Any

from research.juggler_sequence.lean_paths import DATA_ROOT, REPO_ROOT

ARTIFACT = DATA_ROOT / "localized_kernel" / "summary.json"
MANUSCRIPT = REPO_ROOT / "docs" / "theory" / "juggler_parity_discrepancy_note.md"

#: an admissible reference length used inside Theorem 5.5's stated range
REFERENCE_Y = F(23, 32)
#: proposed production landing exponent and its broad inverse-length exponent
PRODUCTION_LANDING = F(27, 64)
PRODUCTION_Y = F(37, 64)
#: retained public name, now corrected to the actual proposed-production scale
COMPANION_Y = PRODUCTION_Y
#: the paper's balancing choices, unchanged by localization
H1, H2, H3 = F(1, 48), F(1, 24), F(1, 12)
#: Stage 2 sawtooth truncation of Lemma 5.2(i)
R0 = F(5, 16)
#: the saving Theorem 5.3 prints
SAVING = F(1, 96)
#: printed maxima the cost tables must reproduce
PRINTED_LEMMA_52i = F(15, 16)
PRINTED_T2 = F(23, 24)
#: line ranges of the two proofs in the manuscript
PROOF_LINES = {"lemma_52i": (2749, 2962), "theorem_53": (3730, 4247)}
#: exponents below this cannot bind: the chain already carries P^{25/48}
COVERAGE_FLOOR = F(1, 4)


class Cost:
    """One displayed cost, as ``c * Y^weight * P^beta``.

    ``dyadic`` is the exponent the manuscript prints on a full block, worst case over
    the admissible ranges of ``k, u, h, j``; for a proportional cost ``beta`` is
    ``dyadic - 1``.  ``absolute`` is the cost of a single boundary object of the
    partition this cost sums over, at its own worst case, or ``None`` when the cost is
    per-summand and has no boundary term.
    """

    def __init__(self, name: str, dyadic: F, absolute: F | None, source: str):
        self.name = name
        self.dyadic = dyadic
        self.absolute = absolute
        self.source = source

    @property
    def proportional(self) -> F:
        return self.dyadic - 1

    def as_dict(self) -> dict[str, Any]:
        return {
            "name": self.name,
            "source": self.source,
            "dyadic": str(self.dyadic),
            "proportional": str(self.proportional),
            "absolute": None if self.absolute is None else str(self.absolute),
        }


def _c(name: str, dyadic: F, absolute: F | None, source: str) -> Cost:
    return Cost(name, dyadic, absolute, source)


# --------------------------------------------------------------- Lemma 5.2(i)
# Ranges: h <= P^{1/8}, uh <= P^{1/2}, R_0 = P^{5/16}; regime (s2) has uh > P^{3/16}.

LEMMA_52i: tuple[Cost, ...] = (
    _c("Stage 1, linearization remainder u Delta E",
       F(3, 4), None, "2 pi u P^{1/4} <= 2 pi P^{3/4} at u <= P^{1/2}"),
    _c("Stage 2, Vaaler majorant 4P/R_0",
       F(11, 16), None, "4 P^{11/16} at R_0 = P^{5/16}"),
    _c("Stage 3(s1), flat cost",
       F(1, 2), None, "12 P^{1/2} = 8(1+|B|) N / T at T = P^{1/2}"),
    _c("Stage 3(s1), mode majorant",
       F(5, 8), None, "14.2 P^{-1/16} * 4 P^{11/16}"),
    _c("Stage 3(s2), flat cost",
       F(3, 4), None, "19 P^{3/4} = 8(1+2.25P^{1/4}) N / T"),
    _c("Stage 3(s2), window boundaries",
       F(17, 32), F(9, 32),
       "1.1 P^{17/32}; (0.6P^{1/4}+1) windows at (0.35uh)^{-1/2}P^{3/8}, uh > P^{3/16}"),
    _c("Stage 4, main curvature sum (printed term 1)",
       F(7, 8), None, "1.1 (uh)^{1/2} P^{5/8} <= 1.1 P^{7/8} at uh = P^{1/2}"),
    _c("Stage 4, gap-cell boundaries (printed term 2)",
       F(15, 16), F(3, 8),
       "2.6 (h/u)^{1/2} P^{7/8} <= 2.6 P^{15/16} at u=1, h=P^{1/8}; "
       "unit lambda^{-1/2} <= 1.69 (uh)^{-1/2} P^{3/8}"),
    _c("Stage 5, collision band, length term",
       F(7, 8), None, "3.1 (uh)^{1/2} P^{5/8} <= 3.1 P^{7/8}: windows partition the block"),
    _c("Stage 5, collision band, inverse-root term",
       F(5, 8), F(9, 32), "0.37 (uh)^{-1/2} P^{5/8}; unit 0.48 (uh)^{-1/2} P^{3/8}"),
    _c("Stage 5, collision band, transition term",
       F(37, 48), F(25, 48),
       "0.47 P^{37/48}; unit 0.611 (uh)^{-1/3} P^{7/12} <= 0.611 P^{25/48} at uh > P^{3/16}; "
       "Lemma 3.8's third term carries no window-length factor, so it is per window"),
    _c("Stage 5, dominant-mode sum (printed term 5)",
       F(29, 32), F(1, 4), "3 R_0^{1/2} P^{3/4} log P = 3 P^{29/32} log P"),
    _c("Stage 5, mode tails (printed terms 3 and 4)",
       F(11, 12), F(1, 4),
       "C P^{7/8} log P in regime (s2); P^{1/24}(uh)^{-1/2}P^{7/8} <= P^{11/12} at uh = 1"),
    _c("Stage 6, decorations",
       F(7, 8), None, "dominated comparisons against 0.35 uh P^{-3/4}; no new object count"),
)

# -------------------------------------------------- Theorem 5.3, the T_2 level

THEOREM_53: tuple[Cost, ...] = (
    _c("Step 2, M_1 deletion",
       F(1, 4), None, "2.7 k h1 h2 P^{1/8} <= 2.7 P^{1/4} by (C1)"),
    _c("Step 3a, Delta_J majorant",
       F(3, 4), None, "2 * 4P/J = 8 P^{3/4} at J = P^{1/4}"),
    _c("Step 3a, flat cost",
       F(3, 4), None, "46 P^{3/4}"),
    _c("Step 3a, frozen-window residual",
       F(7, 8), None, "6.3 P^{-1/8} * P"),
    _c("Step 3a, window boundaries",
       F(17, 24), F(3, 8), "7 P^{17/24}; (2 k h_2 P^{1/4}+1) windows at 3.4 P^{3/8}"),
    _c("Step 3b, carry majorant 4P/J_2",
       F(23, 24), None, "4 P^{23/24} at J_2 = P^{1/24}: a binding proportional cost"),
    _c("Step 3c, window boundaries",
       F(11, 16), F(3, 8), "7 P^{11/16}; (2 k h_1 P^{1/4}+1) windows at 3.4 P^{3/8}"),
    _c("Step 3e, branch-arc majorant",
       F(11, 16), None, "4 P^{11/16} exact shift device, O(log P) mass"),
    _c("Step 4, wave pieces (Lemma 5.2(ii))",
       F(23, 24), None, "|t|^{-1/6} P^{23/24} summed over t: a binding proportional cost"),
    _c("Step 4, bad-shift trivial bound",
       F(23, 24), None, "368 P^2/H_3 <= 368 t^{-1/3} P^{23/12}, halved by the A-process"),
    _c("Step 5a, frozen runs, main",
       F(23, 24), None, "1.2 (k|j|)^{1/2} P^{15/16} <= 1.8 P^{23/24} at k <= P^{1/24}"),
    _c("Step 5a, frozen-run boundaries",
       F(13, 16), F(1, 16),
       "20 (|j|+1)|j|^{-1/2} k^{-1/2} P^{13/16}; unit 0.88 (k|j|)^{-1/2} P^{1/16}"),
    _c("Step 5a, collision band main",
       F(23, 24), None, "2.4 (k|j|)^{1/2} P^{15/16} log P at k <= P^{1/24}"),
    _c("Step 5a, collision band transition term",
       F(1, 36) + F(3, 4), F(3, 8),
       "0.33 P^{1/36+3/4}; unit 0.92 (k|j|)^{-1/3} P^{3/8}"),
    _c("Step 5a, collision window boundaries",
       F(1, 48) + F(7, 16), F(1, 16), "0.15 (k|j|)^{1/2} P^{7/16} at k <= P^{1/24}"),
    _c("Step 5b, anchor-dominant runs, main",
       F(3, 4), None, "1.7 (k h1 h2)^{1/2} P^{11/16} <= 1.7 P^{3/4} by (C1)"),
    _c("Step 5b, anchor-dominant run boundaries",
       F(9, 16) + F(1, 32), F(5, 16),
       "40 (h1h2/k)^{1/2} P^{9/16}; unit 1.34 (k h1 h2)^{-1/2} P^{5/16}"),
    _c("Step 5b, mode-dominant boundaries",
       F(11, 16), F(3, 8), "75 P^{11/16}; unit 3.4 (u h_1)^{-1/2} P^{3/8}"),
    _c("Step 5b, mode-dominant Lemma 5.2(i) total",
       F(15, 16), None, "((uh_1)^{1/2}P^{5/8} + (h_1/u)^{1/2}P^{7/8} + P^{7/8}) P^eps"),
    _c("Step 5b, middle band transition set",
       F(89, 96), None, "0.46 C(E) P (W/S)^{1/2}, W/S <= 0.21 P^{-7/48}"),
    _c("Step 5b, middle band piece boundaries",
       F(89, 96), F(37, 96),
       "14.1 P^{89/96}; (3.5 P^{13/24} + C(E)) pieces at 4.01 P^{37/96}"),
    _c("Step 5b, middle band good pieces",
       F(3, 4), None, "26 C'(E) P^{3/4}, S <= 610 P^{-1/2}"),
    _c("Step 6, slow modes and (D3) remnants",
       F(7, 8), None, "<< P^{7/8+eps}"),
)

# ------------------------------------------------------------------- coverage
# Every displayed exponent >= 1/4 in either proof that is not a tabulated cost, with
# the role that explains it.  "count" and "length" scale with the interval and so are
# already inside the cost entries; "parameter" and "hypothesis" are properties of the
# scale P and are untouched by restricting to a sub-interval.

NON_COST: dict[str, dict[str, str]] = {
    "lemma_52i": {
        "5/4": "length: windows of length >= P^{5/4}/(0.6uh) in regime (s2)",
        "1/2": "count: at most 1.5 h P^{1/2} + 1 gap cells (E1)",
        "5/16": "parameter: the Stage 2 truncation R_0",
        "7/12": "unit: the per-window transition term, tabulated as an absolute cost",
        "5/6": "intermediate: 0.47 (uh)^{-1/3} P^{5/6} before uh > P^{3/16} is used",
        "3/8": "unit: inverse-root per-window costs, tabulated as absolute costs",
        "1/4": "count: the window count 0.77 P^{1/4} of regime (s2)",
        "23/12": "scale: the Claim C trivial term 2P^2/H_3, an A-process input",
        "5/8": "intermediate: the printed relaxation 1.1 P^{17/32} <= P^{5/8}",
    },
    "theorem_53": {
        "1/2": "parameter: the Lemma 3.7 window T = P^{1/2}/(2h), and uh_1 <= P^{1/2}",
        "23/48": "hypothesis: T >= (1/2) P^{23/48} against 8(1+|B|) in Step 3a",
        "11/24": "hypothesis: T >= (1/2) P^{11/24} against 8(1+|B|) in Step 3c",
        "13/24": "count: at most 3.5 P^{13/24} pieces in the middle band",
        "1/3": "counterfactual: 22 P^{1/3} under (C4) alone, not the route taken",
        "5/16": "count: at most 22 h1 h2 P^{1/4} <= 22 P^{5/16} anchor-run boundaries",
        "1/4": "parameter: the Step 3a truncation J = P^{1/4}",
        "3/8": "unit: window and transition costs, tabulated as absolute costs",
        "5/8": "intermediate: 30 k h1 h2 P^{5/8} inside the Step 3a flat cost",
        "9/16": "intermediate: 40 (h1h2/k)^{1/2} P^{9/16}, tabulated with its unit",
        "23/12": "scale: the Claim C trivial term 2P^2/H_3, an A-process input",
        "37/96": "unit: the middle-band piece boundary, tabulated as an absolute cost",
        "7/16": "intermediate: 0.15 (k|j|)^{1/2} P^{7/16}, tabulated with its unit",
        "15/16": "intermediate: the Lemma 5.2(i) totals of Steps 5a and 5b",
        "13/16": "intermediate: the Step 5a run-boundary total, tabulated",
        "89/96": "intermediate: the middle-band totals, tabulated",
        "17/24": "intermediate: the Step 3a window-boundary total, tabulated",
        "11/16": "intermediate: the Step 3c and 5b totals, tabulated",
        "3/4": "intermediate: several tabulated totals",
        "7/8": "intermediate: several tabulated totals",
        "23/24": "intermediate: the binding proportional totals, tabulated",
    },
}

_EXP_PATTERNS = (
    re.compile(r"P\^\{?\\t?frac\{(-?\d+)\}\{(\d+)\}\}?"),
    re.compile(r"P\^\{(-?\d+)/(\d+)\}"),
)


def displayed_exponents(which: str) -> set[F]:
    """Every ``P``-exponent displayed in one of the two proofs."""
    lo, hi = PROOF_LINES[which]
    text = " ".join(MANUSCRIPT.read_text(encoding="utf-8").split("\n")[lo - 1:hi])
    out: set[F] = set()
    for pat in _EXP_PATTERNS:
        for m in pat.finditer(text):
            out.add(F(int(m.group(1)), int(m.group(2))))
    return out


def coverage(which: str) -> dict[str, Any]:
    """Account for every displayed exponent at or above the floor."""
    costs = LEMMA_52i if which == "lemma_52i" else THEOREM_53
    tabulated = {c.dyadic for c in costs} | {c.absolute for c in costs if c.absolute}
    named = {F(k) for k in NON_COST[which]}
    seen = {e for e in displayed_exponents(which) if e >= COVERAGE_FLOOR}
    unexplained = sorted(seen - tabulated - named)
    return {
        "displayed_at_or_above_floor": len(seen),
        "tabulated_as_a_cost": len(seen & tabulated),
        "named_as_a_non_cost": len(seen & named),
        "unexplained": [str(e) for e in unexplained],
        "complete": not unexplained,
    }


def max_dyadic(costs: tuple[Cost, ...]) -> F:
    return max(c.dyadic for c in costs)


def proportional_exponent(costs: tuple[Cost, ...]) -> F:
    return max(c.proportional for c in costs)


def absolute_exponent(costs: tuple[Cost, ...]) -> F:
    parts = [c.absolute for c in costs if c.absolute is not None]
    return max(parts) if parts else F(0)


def worst_absolute(costs: tuple[Cost, ...]) -> Cost:
    return max((c for c in costs if c.absolute is not None), key=lambda c: c.absolute)


#: Lemma 5.2(i)'s five printed terms as (P-exponent, exponent of the shift h)
PRINTED_TERMS: tuple[tuple[str, F, F], ...] = (
    ("1: (uh)^{1/2} P^{5/8}", F(5, 8), F(1, 2)),
    ("2: (h/u)^{1/2} P^{7/8}", F(7, 8), F(1, 2)),
    ("3: P^{7/8}", F(7, 8), F(0)),
    ("4: P^{1/24}(uh)^{-1/2}P^{7/8}", F(1, 24) + F(7, 8), -F(1, 2)),
    ("5: R_0^{1/2} P^{3/4}", R0 / 2 + F(3, 4), F(0)),
)


def claim_c_balance() -> dict[str, Any]:
    """The balance inside Lemma 5.2(ii), and why localization cannot disturb it.

    Claim C differences at ``H_3 = t^{1/3} P^{1/12}`` and averages Lemma 5.2(i) over the
    shift.  With ``sum_{h<=H} h^s ~ H^{s+1}/(s+1)``, the second printed term contributes
    ``(4P/H_3) t^{-1/2} (2/3) H_3^{3/2} P^{7/8} = (8/3) t^{-1/3} P^{23/12}``, exactly
    ``2P^2/H_3``; the other four are strictly dominated.  So the ``A``-process is
    balanced against an average of proportional quantities, and such an average is
    proportional: on an interval of length ``Y`` both sides carry ``(Y/P)^2`` and the
    balance is unchanged.  This is the single structural fact the localization rests on.
    """
    trivial = (-F(1, 3), 2 - H3)
    rows = []
    for name, e, s in PRINTED_TERMS:
        p_tot = 1 + s * H3 + e
        rows.append({"term": name, "exponent": str(p_tot),
                     "dominated": p_tot <= trivial[1], "balances": p_tot == trivial[1]})
    balancing = [r["term"] for r in rows if r["balances"]]
    return {
        "H3": "t^{1/3} P^{1/12}",
        "trivial_term": f"2P^2/H_3 = t^{trivial[0]} P^{trivial[1]}",
        "terms": rows,
        "balancing_terms": balancing,
        "unique_balancing_term": len(balancing) == 1,
        "all_dominated": all(r["dominated"] for r in rows),
        "output": f"|U| << t^{trivial[0] / 2} P^{trivial[1] / 2}",
        "output_is_printed": trivial[0] / 2 == F(-1, 6) and trivial[1] / 2 == F(23, 24),
    }


def a_process(prop_out: F, abs_in: F, y: F) -> tuple[F, F]:
    """One ``A``-process: ``(alpha, beta) -> ((1+alpha)/2, beta/2)`` on each cost.

    A proportional cost is a fixed point, so ``prop_out`` is the printed exponent and is
    passed in rather than recomputed.  An absolute cost ``(0, a)`` becomes
    ``(1/2, a/2)``, that is ``P^{(y+a)/2}``.
    """
    return prop_out, (y + abs_in) / 2


def chain(y: F) -> dict[str, Any]:
    """Propagate the two exponents through Lemma 5.2(i), 5.2(ii), T_2, T_1, K_c."""
    p1, a1 = proportional_exponent(LEMMA_52i), absolute_exponent(LEMMA_52i)
    p2, a2 = a_process(-H3 / 2, a1, y)
    pT2 = max(proportional_exponent(THEOREM_53), p2)
    aT2 = max(absolute_exponent(THEOREM_53), a2)
    pT1, aT1 = a_process(pT2 / 2, aT2, y)
    pK, aK = a_process(pT1 / 2, aT1, y)
    return {
        "lemma_52i": (p1, a1),
        "lemma_52ii": (p2, a2),
        "T2": (pT2, aT2),
        "T1": (pT1, aT1),
        "K": (pK, aK),
        "target": y + pK,
        "absolute_dominated": aK < y + pK,
        "margin": y + pK - aK,
    }


def absolute_tail(y: F, a1: F | None = None) -> F:
    """Closed form of the absolute exponent after the three nested ``A``-processes."""
    if a1 is None:
        a1 = absolute_exponent(LEMMA_52i)
    return (7 * y + a1) / 8


def threshold(a1: F | None = None, saving: F = SAVING) -> F:
    """Least ``y`` with ``(7y+a1)/8 <= y - saving``, i.e. ``y >= a1 + 8*saving``."""
    if a1 is None:
        a1 = absolute_exponent(LEMMA_52i)
    return a1 + 8 * saving


def twist_total_variation(y: F) -> F:
    """Exponent of ``TV(Delta_{2h_1} g)`` for a slow twist, Lemma 4.10.

    ``|g''| <= 0.13 P^{1/24-23/16}`` and ``TV <= 2 h_1 |I| sup|g''|``, ``h_1 <= P^{1/48}``.
    """
    return H1 + y + F(1, 24) - F(23, 16)


def summary(y: F = PRODUCTION_Y) -> dict[str, Any]:
    ch = chain(y)
    dy = chain(F(1))
    ref = chain(REFERENCE_Y)
    prod = chain(PRODUCTION_Y)
    thr = threshold()
    cov = {k: coverage(k) for k in PROOF_LINES}
    return {
        "statement": (
            "Theorem 5.3 localizes: for every interval I inside (P, 2P] of length "
            "|I| >= P^{29/48+delta}, |K_c(I)| << |I| P^{-1/96+eps}, a slow twist "
            "allowed. The exponent is the printed one; only the admissible length is new."
        ),
        "evaluated_length_exponent": str(y),
        "reference_length_exponent": str(REFERENCE_Y),
        "production_landing_exponent": str(PRODUCTION_LANDING),
        "production_length_exponent": str(PRODUCTION_Y),
        "threshold_length_exponent": str(thr),
        "threshold_closed_form": "y >= A_1 + 8/96 = 25/48 + 1/12 = 29/48",
        "companion_above_threshold": PRODUCTION_Y > thr,
        "production_above_threshold": PRODUCTION_Y > thr,
        "reference_above_threshold": REFERENCE_Y > thr,
        "threshold_above_one_half": thr > F(1, 2),
        "balancing_choices_unchanged": {"H1": str(H1), "H2": str(H2), "H3": str(H3)},
        "chain": {
            k: {"proportional": str(v[0]), "absolute": str(v[1])}
            for k, v in ch.items() if isinstance(v, tuple)
        },
        "saving": str(ch["K"][0]),
        "saving_is_printed_exponent": ch["K"][0] == -SAVING,
        "printed_saving_bound_applies_at_evaluated_length": ch["absolute_dominated"],
        "absolute_tail": str(ch["K"][1]),
        "absolute_tail_closed_form": str(absolute_tail(y)),
        "absolute_tail_matches_closed_form": ch["K"][1] == absolute_tail(y),
        "target": str(ch["target"]),
        "absolute_dominated": ch["absolute_dominated"],
        "margin": str(ch["margin"]),
        "reference_same_saving_margin": str(ref["margin"]),
        "production_same_saving_margin": str(prod["margin"]),
        "production_formal_effective_saving": str(PRODUCTION_Y - prod["K"][1]),
        "production_formal_effective_saving_is_11_over_1536": (
            PRODUCTION_Y - prod["K"][1] == F(11, 1536)
        ),
        "production_application": {
            "status": "OPEN_PROOF_OBLIGATION",
            "reason": (
                "37/64 is below the theorem's 29/48 same-saving threshold; the formal "
                "two-term substitution does not prove the exact floor/parity transport."
            ),
        },
        "cost_tables_reproduce_printed": {
            "lemma_52i_max": str(max_dyadic(LEMMA_52i)),
            "lemma_52i_printed": str(PRINTED_LEMMA_52i),
            "T2_max": str(max_dyadic(THEOREM_53)),
            "T2_printed": str(PRINTED_T2),
            "ok": (max_dyadic(LEMMA_52i) == PRINTED_LEMMA_52i
                   and max_dyadic(THEOREM_53) == PRINTED_T2),
        },
        "dyadic_specialization": {
            "T2": str(F(1) + dy["T2"][0]),
            "T1": str(F(1) + dy["T1"][0]),
            "K": str(F(1) + dy["K"][0]),
            "reproduces_printed": (
                F(1) + dy["T2"][0] == F(23, 24)
                and F(1) + dy["T1"][0] == F(1) - F(1, 48)
                and F(1) + dy["K"][0] == F(1) - SAVING
            ),
        },
        "coverage": cov,
        "coverage_complete": all(c["complete"] for c in cov.values()),
        "largest_absolute_cost": {
            "exponent": str(absolute_exponent(LEMMA_52i)),
            "site": worst_absolute(LEMMA_52i).name,
        },
        "largest_absolute_cost_theorem53": {
            "exponent": str(absolute_exponent(THEOREM_53)),
            "site": worst_absolute(THEOREM_53).name,
        },
        "claim_c_balance": claim_c_balance(),
        "twist": {
            "total_variation_exponent": str(twist_total_variation(y)),
            "negligible": twist_total_variation(y) < 0,
            "uniform_exponent_for_Y_at_most_P": str(twist_total_variation(F(1))),
        },
        "costs": {
            "lemma_52i": [c.as_dict() for c in LEMMA_52i],
            "theorem_53": [c.as_dict() for c in THEOREM_53],
        },
        "unlocks": [],
        "retracted_unlocks": ["OOOEEE", "OOEOEE"],
    }


def main() -> None:
    s = summary()
    ARTIFACT.parent.mkdir(parents=True, exist_ok=True)
    ARTIFACT.write_text(json.dumps(s, indent=2) + "\n", encoding="utf-8")
    t = s["cost_tables_reproduce_printed"]
    print(f"cost tables reproduce the printed exponents: {t['ok']} "
          f"(Lemma 5.2(i) {t['lemma_52i_max']}, T_2 {t['T2_max']})")
    for k, c in s["coverage"].items():
        print(f"coverage {k:<11} {c['displayed_at_or_above_floor']:>2} displayed >= 1/4: "
              f"{c['tabulated_as_a_cost']} tabulated, {c['named_as_a_non_cost']} named, "
              f"unexplained {c['unexplained'] or 'none'}")
    print(f"\nproposed productions need broad scale |I| = P^{s['production_length_exponent']}; "
          f"threshold P^{s['threshold_length_exponent']} "
          f"({'above' if s['production_above_threshold'] else 'BELOW'}); "
          f"threshold above P^(1/2): {s['threshold_above_one_half']}")
    print(f"proportional saving P^{s['saving']} (the printed exponent: "
          f"{s['saving_is_printed_exponent']}; full bound applies here: "
          f"{s['printed_saving_bound_applies_at_evaluated_length']})")
    print(f"absolute tail P^{s['absolute_tail']} vs target P^{s['target']}; "
          f"margin P^{s['margin']}; dominated: {s['absolute_dominated']}")
    print("\nchain:")
    for k, v in s["chain"].items():
        print(f"  {k:<12} Y*P^{v['proportional']:<8} + P^{v['absolute']}")
    print(f"\nlargest absolute cost P^{s['largest_absolute_cost']['exponent']} at "
          f"{s['largest_absolute_cost']['site']}")
    d = s["dyadic_specialization"]
    print(f"dyadic specialization: T_2 = P^{d['T2']}, T_1 = P^{d['T1']}, K = P^{d['K']} "
          f"(printed: {d['reproduces_printed']})")
    cb = s["claim_c_balance"]
    print(f"Claim C: {cb['trivial_term']} balanced by {cb['balancing_terms']} alone "
          f"(unique: {cb['unique_balancing_term']}); {cb['output']}")
    print(f"slow twist TV exponent {s['twist']['total_variation_exponent']} "
          f"(negligible: {s['twist']['negligible']}; uniform exponent "
          f"{s['twist']['uniform_exponent_for_Y_at_most_P']})")
    print(f"production application: {s['production_application']['status']}; "
          f"formal effective saving {s['production_formal_effective_saving']}")
    print(f"wrote {ARTIFACT}")


if __name__ == "__main__":
    main()
