"""Historical Paper B audit: provenance.

Finite numerical checks and manuscript consistency; no termination claim.
"""
from __future__ import annotations

import inspect
import itertools
import math
import random
import re
from fractions import Fraction as Fr
from typing import Any

import mpmath as mp

from research.juggler_sequence import paper_b_prefix_count
from research.juggler_sequence.lean_paths import (
    DOCS_THEORY,
    JUGGLER_DIR,
)

from .identities import (
    check_lemma_5_1_ii_iv,
)

# Every pointwise bound of the census that is printed in the block start P rather than in n.  A
# single n pins P only to [n/2, n), so a check that cannot miss a violation uses the largest
# admissible P for a lower bound and the smallest for an upper one.  With a positive exponent that
# means n below and n/2 above; with a negative one the directions swap, and P = n is already strict
# for an upper bound.  Everything else in the pointwise checkers is written in n, m, v, X or Y,
# which a single n determines, so no other bound can carry this slip.
POINTWISE_P_BOUNDS = [
    ("L5.1(iii) first bracket, lower", Fr(3, 4), "lower", "P = n"),
    ("L5.1(iii) first bracket, upper", Fr(3, 4), "upper", "P = n/2"),
    ("L5.1(iii) second bracket, lower", Fr(1, 4), "lower", "P = n"),
    ("L5.1(iii) second bracket, upper", Fr(1, 4), "upper", "P = n/2"),
    ("L5.1(iv) M_1", Fr(-7, 8), "upper", "P = n (negative exponent: already strict)"),
]


def pointwise_bound_inventory(seed: int = 2405, samples_per_range: int = 20) -> dict[str, Any]:
    """The P-stated pointwise bounds, their strict transcriptions, and whether the code uses them.

    Three bounds are stated in P: the two Lemma 5.1(iii) brackets and the M_1 bound.  The brackets
    carry positive exponents, so their strict forms differ at the two ends and using n on both was
    loose by 2^{3/4} and 2^{1/4} until this was fixed; M_1 carries -7/8, where P = n is already the
    smallest admissible right-hand side.

    Strictness is testable rather than asserted: on a strict transcription every sample must sit on
    the correct side of 1, and a bound whose printed constant is attained will approach 1 from that
    side.  The source surface is pinned too, so a new P-dependent bound cannot be added without
    updating this table.
    """

    rng = random.Random(seed)
    ranges = [(10**4, 2 * 10**4), (10**6, 2 * 10**6), (10**10, 2 * 10**10), (10**14, 2 * 10**14)]
    keys = {"L5.1(iii) first bracket, lower": ("first_ratio_lower", "lower"),
            "L5.1(iii) first bracket, upper": ("first_ratio_upper", "upper"),
            "L5.1(iii) second bracket, lower": ("second_ratio_lower", "lower"),
            "L5.1(iii) second bracket, upper": ("second_ratio_upper", "upper"),
            "L5.1(iv) M_1": ("M1_ratio", "upper")}
    extremes: dict[str, float] = {}
    inspected = 0                      # a guard that inspects nothing passes; count what it saw
    for lo, hi in ranges:
        mp.mp.dps = 60 + int(4 * math.log10(hi))
        H1, H2 = max(1, int(lo ** (1 / 48))), max(1, int(lo ** (1 / 24)))
        for _ in range(samples_per_range):
            n = rng.randrange(lo + 1, hi) | 1
            r = check_lemma_5_1_ii_iv(n, rng.randint(1, H1), rng.randint(1, H2), 1)
            for name, (key, side) in keys.items():
                val = r.get(key)
                if val is None:
                    continue
                inspected += 1
                if side == "upper":
                    extremes[name] = max(extremes.get(name, 0.0), val)
                else:
                    extremes[name] = min(extremes.get(name, float("inf")), val)
    mp.mp.dps = 60

    source = inspect.getsource(check_lemma_5_1_ii_iv)
    surface = sorted({tok for tok in ("P34", "P14", "P34_lo", "P14_lo", "mp.power(P,") if tok in source})

    rows = []
    for name, exponent, side, strict in POINTWISE_P_BOUNDS:
        extreme = extremes.get(name)
        respects = None if extreme is None else (extreme <= 1 + 1e-9 if side == "upper" else extreme >= 1 - 1e-9)
        rows.append({"bound": name, "exponent": str(exponent), "side": side,
                     "strict_transcription": strict, "extreme_ratio": extreme,
                     "respects_its_side": respects})
    return {
        "bounds": rows,
        "count": len(rows),
        "all_respect_their_side": all(r["respects_its_side"] for r in rows),
        "source_surface": surface,
        "expected_surface": ["P14", "P14_lo", "P34", "P34_lo", "mp.power(P,"],
        "surface_unchanged": surface == ["P14", "P14_lo", "P34", "P34_lo", "mp.power(P,"],
        "no_other_pointwise_bound_is_stated_in_P": True,
        # the tactic guard in test_manuscript_consistency carries "checked >= 20" for exactly this
        # reason; without a count, a probe whose ratios all came back None would pass silently.
        "samples_inspected": inspected,
        "did_not_go_blind": inspected >= 100,
    }


# Phrases that mark a "then versus now" comparison.  The referee's objection was to the development
# log, and test_paper_b_body_carries_no_draft_history polices the exact phrase "earlier draft" plus
# a whitelist of two words after "an earlier".  The family is wider, and where it appears matters:
# in Appendix A.5 and A.6, whose job is to explain why one constant was chosen over another, a
# comparison with the superseded choice is the content; in the body it is either mathematics or
# residue.
DRAFT_HISTORY_MARKERS = ("previously", "in an earlier", "used to", "no longer", "the former")


BODY_MARKERS_THAT_ARE_MATHEMATICAL = ("in an earlier defect", "no longer drift-blocked")


def draft_history_markers() -> dict[str, Any]:
    """Where the paper still compares itself with its own past, and whether that is the appendix's job.

    Nine occurrences: four in the body of Sections 4, 5 and 7, five in Appendix A.  Of the four in
    the body, two are mathematical -- "an earlier defect theta_s" is earlier in the chain, and a
    term that is "no longer drift-blocked" has just been differenced -- and two are status rather
    than mathematics: a sentence on what the Lean layer covered before, and one on a comparison the
    raised threshold made unnecessary.  The five in the appendix are the appendix's subject.

    Reported so a new body occurrence has to be looked at.  The guard in test_manuscript_consistency
    polices the phrase the referee named; this counts the family around it.
    """

    text = (DOCS_THEORY / "juggler_parity_discrepancy_note_2026_09_04.md").read_text(encoding="utf-8")
    lines = text.splitlines()
    heads = [(i, ln) for i, ln in enumerate(lines) if re.match(r"^#{1,3} ", ln)]

    def section_of(index: int) -> str:
        prior = [h for h in heads if h[0] <= index]
        return prior[-1][1].lstrip("# ").strip() if prior else "(front matter)"

    pattern = re.compile("|".join(re.escape(m) for m in DRAFT_HISTORY_MARKERS), re.I)
    rows = []
    for i, line in enumerate(lines):
        if not pattern.search(line):
            continue
        section = section_of(i)
        in_appendix = section.startswith("Appendix") or section.startswith("A.")
        joined = " ".join(lines[max(0, i - 1):i + 2])
        mathematical = any(phrase in joined for phrase in BODY_MARKERS_THAT_ARE_MATHEMATICAL)
        rows.append({"line": i + 1, "section": section, "in_appendix": in_appendix,
                     "mathematical": mathematical,
                     "needs_a_look": not in_appendix and not mathematical,
                     "text": line.strip()[:90]})
    body = [r for r in rows if not r["in_appendix"]]
    return {
        "occurrences": rows,
        "total": len(rows),
        "in_appendix": sum(r["in_appendix"] for r in rows),
        "in_body": len(body),
        "body_mathematical": sum(r["mathematical"] for r in body),
        "body_needing_a_look": [r["line"] for r in body if r["needs_a_look"]],
        "the_referees_phrase_is_gone": "earlier draft" not in text,
    }


def trust_boundary_rows() -> dict[str, Any]:
    """The Section 1.1 table, read as data, and the Section 4 sentence checked against it.

    Section 4 says five Lean statements -- fract_diff_level2, lemma51_double_gap,
    double_difference_product, lemma51_master, lemma51_brackets_le_two -- "were previously supported
    only by the probe's 60-digit sampling ... they are exact, so they are now proved rather than
    sampled".  All five appear in the table's Lemma 5.1 row and all five are declared in
    formal/Problems/Juggler/MasterIdentity.lean, so the sentence and the table agree.

    The table has no "sampled" column: its three warrants are a proof in this paper, a Lean
    identifier, and a classical input, and its preamble says the Lean layer checks identities,
    constants and thresholds and "not any estimate".  So nothing in it is carried by sampling by
    construction -- what sampling carries is this module, which the paper's repository paragraph
    calls not a proof.  What the table does mark is where the warrant is the human proof alone:
    Lemma 5.2(i)-(iii) with no Lean at all, and Theorem 5.3 with Step 5b constants only and
    explicitly "no part of the assembly".
    """

    text = (DOCS_THEORY / "juggler_parity_discrepancy_note_2026_09_04.md").read_text(encoding="utf-8")
    start = text.index("The boundary between those three kinds of warrant")
    table = text[start:text.index("### 1.2 Related work", start)]
    rows = []
    for line in table.splitlines():
        if not line.startswith("|") or line.startswith("|---") or "human proof" in line:
            continue
        cells = [c.strip() for c in line.strip("|").split("|")]
        if len(cells) < 4:
            continue
        names = re.findall(r"`([A-Za-z_][A-Za-z_0-9']*)`", cells[2])
        rows.append({"statement": cells[0].replace("**", ""), "human": cells[1].replace("**", ""),
                     "lean_names": names, "lean_count": len(names),
                     "classical": cells[3],
                     # "quoted" and "companion [22]" are other people's warrants; only "this paper"
                     # with no Lean identifier rests on an argument written here and nothing else
                     "human_proof_alone": not names and cells[1].replace("**", "").startswith("this paper"),
                     "quoted_elsewhere": not names and not cells[1].replace("**", "").startswith("this paper"),
                     "flagged": line.count("**") >= 2})
    section4 = ["fract_diff_level2", "lemma51_double_gap", "double_difference_product",
                "lemma51_master", "lemma51_brackets_le_two"]
    in_table = {n for r in rows for n in r["lean_names"]}
    lean_src = (JUGGLER_DIR / "MasterIdentity.lean").read_text(encoding="utf-8")
    return {
        "rows": rows,
        "row_count": len(rows),
        "rows_with_lean": sum(1 for r in rows if r["lean_names"]),
        "rows_on_the_human_proof_alone": [r["statement"] for r in rows if r["human_proof_alone"]],
        "rows_quoted_from_elsewhere": [r["statement"] for r in rows if r["quoted_elsewhere"]],
        "flagged_rows": [r["statement"] for r in rows if r["flagged"]],
        "section4_identifiers": section4,
        "section4_all_in_the_table": all(n in in_table for n in section4),
        "section4_all_declared": all(re.search(r"^theorem %s\b" % n, lean_src, re.M) for n in section4),
        "table_has_no_sampled_column": "sampled" not in table.lower(),
        "largest_lean_row": max(rows, key=lambda r: r["lean_count"])["statement"],
        "largest_lean_count": max(r["lean_count"] for r in rows),
    }


def proposition_7_1_word_count(max_d: int = 14) -> dict[str, Any]:
    """Proposition 7.1's N_d <= 2^d e^{-cd}, counted.  It is the row with the least company.

    Of the nine statements the trust table rests on this paper alone, Proposition 7.1 had no probe
    and no exponent check at all.  Its conclusion is conditional and asymptotic, but its engine is
    not: N_d, the number of length-d words with no contracting prefix, is bounded by 2^d e^{-cd}
    with c = 2(log2/log3 - 1/2)^2 > 0.0342, and a word's prefixes are contracting exactly when
    their scale exponent drops below 1 -- which paper_b_prefix_count computes.

    Counting them: the bound holds at every d, and the ratio N_d/(2^d e^{-cd}) falls from 0.52 at
    d = 1 to 0.053 at d = 18, so the printed rate is valid and increasingly slack.  The observed
    rate is about 0.197, roughly 5.8 times c.  Proposition 7.1 needs only c > 0, so the slack costs
    it nothing; what it costs is the sharpness of a structural count the paper displays.
    """

    c = 2 * (math.log(2) / math.log(3) - 0.5) ** 2
    rows = []
    for d in range(1, max_d + 1):
        count = 0
        for bits in itertools.product("OE", repeat=d):
            word = "".join(bits)
            if all(e >= 1 for e in paper_b_prefix_count.iterate_exponents(word)):
                count += 1
        bound = 2**d * math.exp(-c * d)
        rows.append({"d": d, "N_d": count, "printed_bound": bound, "ratio": count / bound,
                     "share_of_all_words": count / 2**d,
                     "holds": count <= bound})
    tail = rows[-1]
    observed_rate = -math.log(tail["share_of_all_words"]) / tail["d"]
    return {
        "rows": rows,
        "c": c,
        "c_exceeds_the_printed_floor": c > 0.0342,
        "bound_holds_everywhere": all(r["holds"] for r in rows),
        "ratio_at_the_top": tail["ratio"],
        "ratio_is_falling": rows[-1]["ratio"] < rows[0]["ratio"],
        "observed_rate": observed_rate,
        "observed_over_printed": observed_rate / c,
        "proposition_needs_only_positivity": True,
    }


def proposition_7_4_check(seed: int = 704, grid: int = 40000) -> dict[str, Any]:
    """Proposition 7.4's constant: where it comes from, whether it holds, and whether it is attained.

    The bound is |int_0^1 |S_lambda|^2 dlambda - L| <= (4/pi)(L/A'min)(log L + 1).  Writing the
    cross term for a pair as an integral in u = {x_t + lambda}, the shift x_t' - x_t splits it at
    one point, so each pair contributes two geometric pieces of modulus at most 1/(pi|Delta|);
    with |Delta| >= A'min |t - t'| and both orderings, the sum over pairs is at most
    (4/pi)(L/A'min) sum_k 1/k <= (4/pi)(L/A'min)(log L + 1).  The 4/pi is two pieces times two
    orderings over pi -- the constant is the derivation's output, not a choice.

    Measured: the pairwise step is essentially sharp -- at L = 2 the largest off-diagonal found is
    98% of the pairwise ceiling 4/pi -- while the assembled bound is not, because the (L-k)/k
    weights and the per-pair sines cannot saturate together.  The worst ratio to the printed bound
    is about 0.29 at L = 2 and falls to 0.09 by L = 32.
    """

    import numpy as np

    rng = np.random.default_rng(seed)

    def integral(A: Any, x: Any) -> float:
        lam = (np.arange(grid) + 0.5) / grid
        frac = np.mod(x[:, None] + lam[None, :], 1.0)
        return float(np.mean(np.abs(np.exp(2j * np.pi * (A[:, None] * frac)).sum(axis=0)) ** 2))

    def printed_bound(L: int, amin: float) -> float:
        return (4 / math.pi) * (L / amin) * (math.log(L) + 1)

    rows = []
    for L in (4, 8, 16, 32):
        for amin in (1.0, 2.0):
            for label in ("integer spacing", "jittered spacing"):
                if label == "integer spacing":
                    A = amin * np.arange(1, L + 1)
                else:
                    A = np.sort(amin * np.arange(1, L + 1) + rng.uniform(0, amin * 0.49, L))
                x = rng.random(L)
                value = integral(A, x)
                rows.append({"L": L, "A_min": amin, "family": label,
                             "integral": value, "bound": printed_bound(L, amin),
                             "ratio": abs(value - L) / printed_bound(L, amin),
                             "holds": abs(value - L) <= printed_bound(L, amin)})

    # the fixed families above do not search; a short hill climb on the gaps and the shifts finds
    # two to three times more at small L.  Reported as a lower bound on what optimisation reaches:
    # a longer run (300 restarts, 60 steps, grid 40000) gives 0.333, 0.279, 0.174 at L = 3, 4, 6.
    searched = []
    for L in (3, 4, 6):
        best = 0.0
        for _ in range(40):
            gaps = 1 + rng.random(L - 1) * 1.5
            A = np.concatenate([[rng.random()], np.cumsum(gaps) + rng.random()])
            x = rng.random(L)
            r = abs(integral(A, x) - L) / printed_bound(L, 1.0)
            for _ in range(30):
                g2 = np.clip(gaps + rng.normal(0, 0.12, L - 1), 1.0, None)
                A2 = np.concatenate([[A[0]], np.cumsum(g2) + A[0]])
                x2 = np.mod(x + rng.normal(0, 0.08, L), 1.0)
                r2 = abs(integral(A2, x2) - L) / printed_bound(L, 1.0)
                if r2 > r:
                    r, gaps, A, x = r2, g2, A2, x2
            best = max(best, r)
        searched.append({"L": L, "best_ratio_found": best})

    # the pairwise step on its own: L = 2, where the ceiling is 2 pieces x 2 orderings / pi
    best_pair = 0.0
    for _ in range(1500):
        delta = 1.0 + rng.random() * 1.2
        base = rng.random()
        A = np.array([base, base + delta])
        best_pair = max(best_pair, abs(integral(A, rng.random(2)) - 2))
    pair_ceiling = 4 / math.pi

    return {
        "rows": rows,
        "bound_holds_everywhere": all(r["holds"] for r in rows),
        "worst_ratio": max(r["ratio"] for r in rows),
        "searched": searched,
        "best_searched_ratio": max(r["best_ratio_found"] for r in searched),
        "search_beats_the_fixed_families": max(r["best_ratio_found"] for r in searched) > max(r["ratio"] for r in rows),
        "searched_ratio_falls_with_L": searched[0]["best_ratio_found"] > searched[-1]["best_ratio_found"],
        "pairwise_best": best_pair,
        "pairwise_ceiling": pair_ceiling,
        "pairwise_share_of_its_ceiling": best_pair / pair_ceiling,
        "pairwise_step_is_sharp": best_pair / pair_ceiling > 0.9,
        "assembled_bound_is_attained": max(r["ratio"] for r in rows) > 0.5,
        "constant_is_two_pieces_times_two_orderings_over_pi": abs(pair_ceiling - 2 * 2 / math.pi) < 1e-12,
    }
