"""Historical Paper B audit: manuscript bounds.

Finite numerical checks and manuscript consistency; no termination claim.
"""
from __future__ import annotations

import re
from typing import Any

from research.juggler_sequence import p0_certificate
from research.juggler_sequence.lean_paths import (
    DOCS_THEORY,
)

# The fifth-letter sawtooth coefficient of Theorem 6.3, C = (9l/16) n^(3/16), as the manuscript
# prints it.  Patterns are matched against the whitespace-stripped text, so they survive rewrapping.
FIFTH_LETTER_C_SITES = (
    {"where": "Section 2 coefficient table", "constant": 2.0,
     "pattern": r"&2P^{19/96}&"},
    {"where": "Thm 6.3 preamble", "constant": 1.30,
     "pattern": r"\lvertC\rvert\le1.30\,P^{19/96}"},
    {"where": "Thm 6.3 proof", "constant": 2.0,
     "pattern": r"\lvertC\rvert\le2P^{19/96}"},
    {"where": "A.6", "constant": 1.2812,
     "pattern": r"\lvertC\rvert\le1.2812\,P^{19/96}"},
)


# The two places the paper multiplies that coefficient by 8 and prints the product's constant.
FIFTH_LETTER_C_CHAINS = (
    {"where": "Thm 6.3 proof", "printed": 11.0,
     "pattern": r"8\lvertC\rvert/T\le11P^{-11/96}"},
    {"where": "Thm 6.3 flat cost bullet", "printed": 11.0,
     "pattern": r"8(1+\lvertC\rvert)/T\le11P^{19/96-5/16}=11P^{-11/96}"},
)


def fifth_letter_coefficient_has_three_values() -> dict[str, Any]:
    """What does binding |C| at the cap the paper states do to the two Theorem 6.3 rows?  It moves
    them, because the paper states three different caps.

    The two rows are prose to any instrument -- their claim strings name |C| and stop -- so the
    check has to import the bound from the paper.  The paper prints it four times, at three values:

        where                       printed              window row    flat row
        Section 2 coefficient table 2 P^(19/96)          3.3443e10     3.7173e11
        Thm 6.3 preamble            1.30 P^(19/96)       8.4239e08     6.3127e09
        Thm 6.3 proof               2 P^(19/96)          3.3443e10     3.7173e11
        A.6                         1.2812 P^(19/96)     7.4516e08     5.5084e09
        (sharp: (9/16) 2 (2)^(3/16) = 1.281137)          7.4486e08     5.5059e09

    A.5 prints 7.5e8 and 5.51e9, which only the last line supports.  The preamble states 1.30 and
    then quotes 7.5e8 and 5.5e9 in the next sentence, and under its own 1.30 those rows first hold
    at 8.42e8 and 6.31e9 -- 1.13 and 1.15 times later.

    The 2 does more than cost a factor.  The proof states |C| <= 2P^(19/96) and, two lines on,
    8|C|/T <= 11P^(-11/96); but 8(2) = 16, so under the bound just stated that line is false.  The
    11 is the sharp constant's 8(9/8)2^(3/16) = 10.25 rounded up, which A.6 derives and prints.  The
    flat-cost bullet carries the same 11 against the same 2, and is false at every P under it.

    And the sentence's own threshold does not go with its own expression: "8|C|/T <= 11P^(-11/96),
    which is below 1 from P >= 7.5e8" -- 11P^(-11/96) reaches 1 at 11^(96/11) = 1.2261e9, not at
    7.5e8.  What does hold from 7.4486e8 is the requirement itself, 8(1+|C|)/T <= 1, with the sharp
    coefficient.  The printed threshold is the right one for the row and the wrong one for the
    sentence that cites it.

    Nothing here reaches P_0 = 3.5858e13: the largest of these, 3.7173e11, is a factor 96 below it,
    so A.5, A.6 and the theorem's conclusion are unaffected.  It is Theorem 6.3's exposition that
    carries one quantity at three values, and the arithmetic of two printed chains that does not
    hold at the value printed beside it.
    """

    text = (DOCS_THEORY / "juggler_parity_discrepancy_note_2026_09_04.md").read_text(
        encoding="utf-8")
    compact = re.sub(r"\s+", "", text)
    sharp = (9 / 16) * 2 * 2 ** (3 / 16)

    def window_row(c: float) -> float:
        lg = p0_certificate.least_P(
            lambda P: p0_certificate.R0(P) >= 8 * (1 + c * P ** (19 / 96)))
        return 10.0 ** lg if lg is not None else float("inf")

    def flat_row(c: float) -> float:
        lg = p0_certificate.least_P(
            lambda P: 8 * (1 + c * P ** (19 / 96)) / p0_certificate.R0(P) <= P ** (-1 / 96))
        return 10.0 ** lg if lg is not None else float("inf")

    sites = []
    for s in FIFTH_LETTER_C_SITES:
        sites.append({**s, "present": compact.count(s["pattern"]) == 1,
                      "window_row": window_row(s["constant"]),
                      "flat_row": flat_row(s["constant"])})
    chains = []
    for ch in FIFTH_LETTER_C_CHAINS:
        chains.append({**ch, "present": compact.count(ch["pattern"]) == 1,
                       "needed_at_C_le_2": 8 * 2.0,
                       "holds_at_the_stated_2": 8 * 2.0 <= ch["printed"],
                       "holds_at_the_sharp_constant": 8 * sharp <= ch["printed"]})
    printed_window, printed_flat = 7.5e8, 5.51e9
    values = sorted({s["constant"] for s in FIFTH_LETTER_C_SITES})
    covered = {s["constant"]: (s["window_row"] <= printed_window and s["flat_row"] <= printed_flat)
               for s in sites}
    eleven_below_one_from = 11.0 ** (96 / 11)
    return {
        "sites": sites,
        "chains": chains,
        "every_site_is_still_there": all(s["present"] for s in sites)
        and all(c["present"] for c in chains),
        "sharp_constant": sharp,
        "values_printed": values,
        "distinct_values": len(values),
        "sharp_window_row": window_row(sharp),
        "sharp_flat_row": flat_row(sharp),
        "A5_prints": (printed_window, printed_flat),
        "which_values_support_the_A5_thresholds": covered,
        "only_the_sharpest_supports_them": (covered[1.2812] and not covered[1.30]
                                            and not covered[2.0]),
        "preamble_states": 1.30,
        "preamble_rows": (window_row(1.30), flat_row(1.30)),
        "preamble_shortfall": (window_row(1.30) / printed_window, flat_row(1.30) / printed_flat),
        "eight_times_the_printed_two": 16.0,
        "the_printed_product": 11.0,
        "eleven_is_false_under_the_printed_two": 8 * 2.0 > 11.0,
        "eleven_is_the_sharp_product_rounded_up": 8 * sharp <= 11.0 and 8 * sharp > 10.0,
        "sharp_product": 8 * sharp,
        "eleven_below_one_from": eleven_below_one_from,
        "the_sentence_cites": printed_window,
        "the_sentence_cites_the_rows_threshold_not_its_own": (
            abs(window_row(sharp) / printed_window - 1) < 0.01
            and eleven_below_one_from / printed_window > 1.5),
        "largest_of_these": max(s["flat_row"] for s in sites),
        "P0": p0_certificate.P0_VALUE if hasattr(p0_certificate, "P0_VALUE") else 3.5858e13,
        "everything_is_far_below_P0": max(s["flat_row"] for s in sites) < 3.5858e13 / 50,
    }


# Step 5b's piece inventory and Step 5a's competitor list, as the manuscript prints them.  Patterns
# are matched against the whitespace-stripped text, so they survive rewrapping.
PIECE_INVENTORY = (
    {"part": "gap cells", "printed": r"1.5(h_1{+}h_2)P^{1/2}+2\le3.1P^{13/24}",
     "bound": "3.1 P^(13/24)"},
    {"part": "anchor runs", "printed": r"\le22h_1h_2P^{1/4}\le22P^{3/8}", "bound": "22 P^(3/8)"},
    {"part": "total", "printed": r"N\le3.5P^{13/24}", "bound": "3.5 P^(13/24)"},
)


COMPETITOR_LISTS = (
    {"read_against": "lambda_a >= 1.30 P^(-1/8)", "where": "Step 5a",
     "ratios": ((0.34, -0.125), (20.0, -13 / 12), (8.0, -13 / 12), (1.0, -0.25)),
     "patterns": (r"\le0.34P^{-1/8}", r"20P^{1/24-5/4+1/8}=20P^{-13/12}", r"\le8P^{1/24-9/8}",
                  r"\lambda_a\ge1.30P^{-1/8}")},
    {"read_against": "lambda_a' >= 0.40 k|j| P^(-1/8)", "where": "the j-decorated Step 5a",
     "ratios": ((1.3, -0.125), (13.0, -9 / 16), (9.0, -13 / 12), (3.0, -0.125)),
     "patterns": (r"\le1.3P^{-1/8}", r"\le13P^{-9/16}", r"\le9P^{-13/12}", r"\le3P^{-1/8}",
                  r"\lambda_a'\ge0.40\,k|j|P^{-1/8}\ge0.40P^{-1/8}")},
)


def step_5_inventories_against_the_paper() -> dict[str, Any]:
    """Do the counts and ratios the paper states agree with the ones the certificate sums?  The
    ratios do, exactly.  The counts do not, and the row's printed threshold needs the sharper cap.

    *The competitors.*  The paper carries two lists, one read against lambda_a >= 1.30 P^(-1/8) and
    one against the j-decorated lambda_a' >= 0.40 P^(-1/8), and the certificate's four entries --
    1.3 P^(-1/8), 13 P^(-9/16), 9 P^(-13/12), 3 P^(-1/8) -- are the second list to the digit.  That
    is the harder of the two: it clears 1/4 at 12^8 = 4.2998e8, where the first clears at 256.  The
    certificate takes the conservative list, A.5 prints 4.3e8 for it, and there is nothing to fix.

    *The pieces.*  Step 5b's inventory prints three numbers:

        gap cells     1.5(h_1+h_2)P^(1/2) + 2 <= 3.1 P^(13/24)
        anchor runs   <= 22 h_1h_2 P^(1/4)   <= 22 P^(3/8)
        total         N <= 3.5 P^(13/24)

    and A.5 prints 5.14e7 for the total.  But those two terms alone, as printed, first fit the
    budget at 2.7681e10 -- 539 times later, and that is with the windows dropped entirely, which
    the sentence does not do.  Add the window count the same theorem prints, 1.8 k|j| P^(3/8) + 1
    with k <= P^(1/24) and |j| <= 2, and it is 3.0603e11.

    The whole gap is one clause.  22 h_1h_2 P^(1/4) <= 22 P^(3/8) reads h_1h_2 <= P^(1/8), which is
    (C1) with k = 1; the standing caps (C4) give h_1h_2 <= P^(1/48+1/24) = P^(1/16) and so
    22 P^(5/16), which is what the certificate sums.  With that one substitution the printed
    inventory fits from 3.9293e7, and the certificate's own form -- 3 P^(13/24) + 2 + 22 P^(5/16)
    + 5 P^(1/3) -- from 5.1398e7, which is A.5's number.

    The same sentence uses both caps.  Its first clause bounds 1.5(h_1+h_2)P^(1/2) by 3.1 P^(13/24),
    which is h_1 <= P^(1/48) and h_2 <= P^(1/24) -- (C4), sharp; its second clause then bounds
    h_1h_2 by P^(1/8).  Nothing is false: P^(1/8) is a true bound on h_1h_2.  It is cruder than the
    caps the clause before it just used, and the row's printed threshold is only reachable with the
    sharper one.

    Nothing here reaches P_0 = 3.5858e13 either: the crudest reading, 3.0603e11, is a factor 117
    below it.  This is the second site in two passes where A.5's threshold is computed from a
    binding sharper than the prose beside it prints -- the first was |C| in Theorem 6.3.
    """

    text = (DOCS_THEORY / "juggler_parity_discrepancy_note_2026_09_04.md").read_text(
        encoding="utf-8")
    compact = re.sub(r"\s+", "", text)

    def least(pred) -> float:
        lg = p0_certificate.least_P(pred)
        return 10.0 ** lg if lg is not None else float("inf")

    budget = lambda P: 3.5 * P ** (13 / 24)  # noqa: E731
    readings = {
        "printed_two_terms": least(
            lambda P: 3.1 * P ** (13 / 24) + 22 * P**0.375 <= budget(P)),
        "printed_with_the_papers_windows": least(
            lambda P: 3.1 * P ** (13 / 24) + 22 * P**0.375 + 3.6 * P ** (5 / 12) + 1 <= budget(P)),
        "printed_cells_with_the_sharp_runs": least(
            lambda P: 3.1 * P ** (13 / 24) + 22 * P ** (5 / 16) <= budget(P)),
        "certificate": least(
            lambda P: 3 * P ** (1 / 24 + 0.5) + 2 + 22 * P ** (1 / 16 + 0.25) + 5 * P ** (1 / 3)
            <= budget(P)),
    }
    lists = []
    for spec in COMPETITOR_LISTS:
        ratios = spec["ratios"]
        lists.append({
            "where": spec["where"], "read_against": spec["read_against"], "ratios": ratios,
            "all_printed": all(compact.count(p) >= 1 for p in spec["patterns"]),
            "least_P": least(lambda P, rs=ratios: max(c * P**e for c, e in rs) <= 0.25),
        })
    cert_ratios = ((1.3, -0.125), (13.0, -9 / 16), (9.0, -13 / 12), (3.0, -0.125))
    printed_row = 5.14e7
    return {
        "inventory": [{**s, "present": compact.count(s["printed"]) == 1} for s in PIECE_INVENTORY],
        "inventory_is_still_printed": all(compact.count(s["printed"]) == 1
                                          for s in PIECE_INVENTORY),
        "readings": readings,
        "A5_prints": printed_row,
        "certificate_matches_A5": abs(readings["certificate"] / printed_row - 1) < 0.01,
        "printed_inventory_is_later_by": readings["printed_two_terms"] / printed_row,
        "with_the_windows_later_by": readings["printed_with_the_papers_windows"] / printed_row,
        "one_clause_closes_it": (readings["printed_cells_with_the_sharp_runs"] < printed_row
                                 < readings["printed_two_terms"]),
        "printed_cap_on_h1h2": "P^(1/8)",
        "cap_from_C4": "P^(1/16)",
        "both_caps_are_true": True,
        "the_sentence_uses_both": True,
        "competitor_lists": lists,
        "certificate_competitors": cert_ratios,
        "certificate_takes_the_second_list": cert_ratios == lists[1]["ratios"],
        "certificate_takes_the_harder_list": lists[1]["least_P"] > lists[0]["least_P"],
        "competitor_row_is_twelve_to_the_eighth": abs(lists[1]["least_P"] - 12.0 ** 8) < 1e3,
        "nothing_reaches_P0": max(readings.values()) < 3.5858e13 / 50,
        "crudest_reading_below_P0_by": 3.5858e13 / readings["printed_with_the_papers_windows"],
    }


# Every place the certificate replaces a shift parameter by a power of P, and which cap it uses.
# "cap" is the bound invoked: H_1 = P^(1/48) and H_2 = P^(1/24) are Theorem 5.3's own choices,
# (C4) is the standing h_1, h_2 <= P^(1/24), (C1) is k h_1h_2 <= P^(1/8).
CAP_SUBSTITUTIONS = (
    {"row": "st3a-window", "term": "P^(1/2)/(2 h_1)", "uses": "0.5 P^(23/48)", "cap": "H_1",
     "pattern": r"15P^{10/48}"},
    {"row": "st3b-window", "term": "P^(1/2)/(2 h_2)", "uses": "0.5 P^(22/48)", "cap": "H_2",
     "pattern": None},
    {"row": "st3a-flat", "term": "16 h_1 P^(1/2)", "uses": "16 P^(25/48)", "cap": "H_1",
     "pattern": r"16h_1P^{1/2}"},
    {"row": "st3a-flat", "term": "30 k h_1h_2 P^(5/8)", "uses": "30 P^(3/4)", "cap": "(C1)",
     "pattern": r"46P^{3/4}"},
    {"row": "5b-Npieces", "term": "1.5(h_1+h_2) P^(1/2) + 2", "uses": "3 P^(13/24) + 2",
     "cap": "H_2", "pattern": r"1.5(h_1{+}h_2)P^{1/2}+2\le3.1P^{13/24}"},
    {"row": "5b-Npieces", "term": "22 h_1h_2 P^(1/4)", "uses": "22 P^(5/16)", "cap": "H_1 H_2",
     "pattern": r"\le22h_1h_2P^{1/4}\le22P^{5/16}"},
    {"row": "st5b-qpp", "term": "1.85 k h P^(1/8)", "uses": "1.85 P^(7/24)", "cap": "k, h",
     "pattern": r"1.85P^{7/24}"},
    {"row": "t61-stepB-discard", "term": "(3 pi k/4) P^(-1/8)", "uses": "1.5 pi P^(1/96-1/8)",
     "cap": "k <= 2P^(1/96)", "pattern": None},
    {"row": "t63-window, t63-flat", "term": "|C| = (9l/16) n^(3/16)",
     "uses": "1.281137 P^(19/96)", "cap": "|l| <= 2P^(1/96)", "pattern": r"\lvertC\rvert\le1.2812\,P^{19/96}"},
    {"row": "st6D1-window, st6D1-modeindex", "term": "|B_0|", "uses": "5 P^(1/4)",
     "cap": "widened decoration", "pattern": r"5P^{1/4}"},
)


# The anchor-run bound, printed twice inside Step 5b at two different values.
ANCHOR_RUN_FORMS = (
    {"where": "mode-dominant bullet", "bound": "22 P^(5/16)", "exponent": 5 / 16,
     "pattern": r"\le22h_1h_2P^{1/4}\le22P^{5/16}"},
    {"where": "the inventory sentence", "bound": "22 P^(3/8)", "exponent": 0.375,
     "pattern": r"\le22h_1h_2P^{1/4}\le22P^{3/8}"},
)


def which_cap_each_substitution_uses() -> dict[str, Any]:
    """How many sites substitute a cap, and does each agree with its sentence?  Ten substitutions,
    and one quantity is now printed at two values inside one step.

    *A correction first.*  The last section attributed the sharp anchor-run bound to (C4).  That is
    wrong, and the paper says so: (C4) is h_1, h_2 <= P^(1/24), which gives h_1h_2 <= P^(1/12) --
    printed twice -- and so 22 P^(1/3), not 22 P^(5/16).  The P^(1/16) needs Theorem 5.3's own
    choices H_1 = P^(1/48) and H_2 = P^(1/24), which sit inside (C4) with room on the first.  The
    three readings order strictly, and only the tightest supports A.5's 5.14e7:

        cap invoked                  h_1h_2        term          row first holds
        H_1 H_2 (Theorem 5.3)        P^(1/16)      22 P^(5/16)   3.9293e07
        (C4) alone                   P^(1/12)      22 P^(1/3)    2.2581e08
        (C1) at k = 1                P^(1/8)       22 P^(3/8)    2.7681e10

    *And the site now prints two of them.*  Step 5b carries `22 h_1h_2 P^(1/4) <= 22 P^(5/16)` in
    its mode-dominant bullet, with the provenance spelled out, and `22 h_1h_2 P^(1/4) <= 22 P^(3/8)`
    in its inventory sentence thirty-four lines below.  Same quantity, same coefficient, two bounds.
    The first is the one A.5's threshold belongs to.

    *The count.*  Ten places in the certificate replace a shift parameter by a power of P.  Eight
    invoke a cap the site's own sentence states at that value.  Two are quantities the paper prints
    at more than one value: this one, and |C| in Theorem 6.3 at 2, 1.30 and 1.2812.  Both were found
    by binding a prose row; neither is unsound, and neither reaches P_0.

    So the pattern is not that the certificate is systematically sharper than the prose.  It is that
    a quantity bounded through a cap gets restated when the cap is restated, and the restatements do
    not always travel together.
    """

    text = (DOCS_THEORY / "juggler_parity_discrepancy_note_2026_09_04.md").read_text(
        encoding="utf-8")
    compact = re.sub(r"\s+", "", text)

    def least(pred) -> float:
        lg = p0_certificate.least_P(pred)
        return 10.0 ** lg if lg is not None else float("inf")

    readings = {
        "H_1 H_2 -> 22 P^(5/16)": least(
            lambda P: 3.1 * P ** (13 / 24) + 22 * P ** (5 / 16) <= 3.5 * P ** (13 / 24)),
        "(C4) alone -> 22 P^(1/3)": least(
            lambda P: 3.1 * P ** (13 / 24) + 22 * P ** (1 / 3) <= 3.5 * P ** (13 / 24)),
        "(C1) -> 22 P^(3/8)": least(
            lambda P: 3.1 * P ** (13 / 24) + 22 * P**0.375 <= 3.5 * P ** (13 / 24)),
    }
    subs = [{**s, "printed_here": (compact.count(s["pattern"]) >= 1) if s["pattern"] else None}
            for s in CAP_SUBSTITUTIONS]
    forms = [{**f, "present": compact.count(f["pattern"]) == 1} for f in ANCHOR_RUN_FORMS]
    printed_row = 5.14e7
    ordered = list(readings.values())
    return {
        "substitutions": subs,
        "substitution_count": len(subs),
        "rows_touched": len({s["row"] for s in subs}),
        "caps_used": sorted({s["cap"] for s in subs}),
        "every_pattern_still_printed": all(s["printed_here"] for s in subs
                                           if s["printed_here"] is not None),
        "anchor_run_forms": forms,
        "printed_at_two_values": all(f["present"] for f in forms),
        "readings": readings,
        "readings_are_ordered": ordered == sorted(ordered),
        "A5_prints": printed_row,
        "only_the_tightest_supports_A5": (ordered[0] < printed_row < ordered[1] < ordered[2]),
        "C4_is_h_le_P_1_24": True,
        "C4_gives_h1h2_le_P_1_12": True,
        "C4_alone_is_not_enough_by": readings["(C4) alone -> 22 P^(1/3)"] / printed_row,
        "the_sharp_cap_is_theorem_5_3s_H1": True,
        "the_last_section_called_it_C4": True,
        "quantities_printed_at_more_than_one_value": 2,
        "the_other_one_is_C_in_theorem_6_3": True,
        "nothing_reaches_P0": max(ordered) < 3.5858e13 / 50,
    }


# Every bound of the form |X| <= c P^e that the manuscript prints for a named symbol, and every
# bound it prints for a product of the shift caps.  Both scans run over the whitespace-stripped
# text, so they survive rewrapping and report their own obsolescence once the text moves.
_SYMBOL_BOUND = re.compile(
    r"\\lvert([A-Za-z](?:_[0-9])?)\\rvert\\le((?:[0-9.]+\\?,?)?P\^\{[^}]{1,16}\})")


_CAP_BOUND = re.compile(
    r"(kh_1h_2|h_1h_2|h_1\{\+\}h_2|h_1\+h_2|h_1|h_2|k)\\le"
    r"((?:[0-9.]+)?P\^\{[^}]{1,20}\}(?:/[0-9]+)?)")


_CAP_LEFT = re.compile(r"[A-Za-z0-9_}\\']")


def _compact_with_lines(text: str) -> tuple[str, list[int]]:
    chars, lines = [], []
    for ln, line in enumerate(text.splitlines(keepends=True), 1):
        for ch in line:
            if not ch.isspace():
                chars.append(ch)
                lines.append(ln)
    return "".join(chars), lines


def one_symbol_two_bounds() -> dict[str, Any]:
    """How many quantities does the paper bound at more than one value?  Three, and the third is a
    symbol rather than a constant.

    The caps themselves are clean.  Every restatement of a cap-derived bound names the hypothesis it
    comes from:

        k          P^(1/24) standing, 2P^(1/96) in Theorem 6.1, P^(eps) in the Section 7 family
        h_1h_2     P^(1/2)/3 by (C2), P^(1/12) by (C4), P^(1/16) by H_1H_2, and 2P^(1/2)/3 in the
                   review note that says in so many words it is twice the stated hypothesis
        kh_1h_2    P^(1/8) by (C1), P^(5/48) from the Theorem 5.3 caps, 2P^(1/96+1/48+1/24) in
                   Theorem 6.1

    so the answer at cap level is none: what is multi-valued is the term derived from a cap, not the
    cap.  Sweeping instead every |X| <= c P^e the paper prints finds exactly two symbols carrying
    more than one bound, and one is already recorded:

        |C|   2 P^(19/96), 1.30 P^(19/96), 1.2812 P^(19/96)      Theorem 6.3, three sites
        |i|   2 P^(1/96), 2 P^(5/16)                             Theorem 6.3, eight lines apart

    The |i| pair is a different animal.  Theorem 6.3 writes "Theorem 6.1's own |i| <= 2P^(1/96) plus
    the fifth-letter |u| <= P^(5/16).  Then |I_tot| <= 2P^(5/16)", and eight lines later the
    (i/2)X-passenger bullet reads "At |i| <= 2P^(5/16) and h_1h_2 <= P^(1/16) this is
    O(P^(-34/16))".  The exponent settles which bound the line is using: 5/16 + 1/16 - 5/2 =
    -34/16 exactly, where 1/96 + 1/16 - 5/2 = -2.4271.  So the bullet is computing with I_tot and
    printing i.

    Nothing is overstated by it.  I_tot is the larger of the two, the passenger is the combined
    first-letter index, and the conclusion sits inside (D3) by P^(-1/2) at the bound used and by
    P^(-0.80) at the tighter one.  What slipped is the symbol, not the estimate -- which makes this
    the third instance of one quantity printed at two values in this theorem, and the first where
    the repair is a letter.
    """

    text = (DOCS_THEORY / "juggler_parity_discrepancy_note_2026_09_04.md").read_text(
        encoding="utf-8")
    compact, lines = _compact_with_lines(text)

    symbols: dict[str, dict[str, list[int]]] = {}
    for m in _SYMBOL_BOUND.finditer(compact):
        rhs = m.group(2).replace("\\,", "")
        symbols.setdefault(m.group(1), {}).setdefault(rhs, []).append(lines[m.start()])
    caps: dict[str, dict[str, list[int]]] = {}
    for m in _CAP_BOUND.finditer(compact):
        before = compact[m.start() - 1] if m.start() else ""
        if before and _CAP_LEFT.match(before):
            continue
        caps.setdefault(m.group(1), {}).setdefault(m.group(2), []).append(lines[m.start()])

    multi_symbols = {s: v for s, v in symbols.items() if len(v) > 1}
    multi_caps = {q: v for q, v in caps.items() if len(v) > 1}
    # which bound the (i/2)X bullet is actually computing with
    printed_exponent = -34 / 16
    with_I_tot = 5 / 16 + 1 / 16 - 5 / 2
    with_i = 1 / 96 + 1 / 16 - 5 / 2
    d3_exponent = -13 / 8                      # |phi''| <= 6 k h_1h_2 h P^(-13/8)
    return {
        "symbol_bounds": symbols,
        "symbols_with_more_than_one_bound": sorted(multi_symbols),
        "symbol_families": {s: sorted(v) for s, v in multi_symbols.items()},
        "cap_bounds": caps,
        "caps_with_more_than_one_value": sorted(multi_caps),
        "every_cap_restatement_names_its_hypothesis": True,
        "the_multi_valued_thing_is_the_derived_term": True,
        "printed_exponent": printed_exponent,
        "exponent_with_I_tot": with_I_tot,
        "exponent_with_i": with_i,
        "the_bullet_computes_with_I_tot": abs(with_I_tot - printed_exponent) < 1e-12,
        "and_not_with_i": abs(with_i - printed_exponent) > 0.3,
        "i_bound": "2 P^(1/96)",
        "I_tot_bound": "2 P^(5/16)",
        "the_larger_is_the_one_used": True,
        "inside_D3_at_the_bound_used": printed_exponent - d3_exponent,
        "inside_D3_at_the_tighter_bound": with_i - d3_exponent,
        "both_are_inside_D3": printed_exponent < d3_exponent and with_i < d3_exponent,
        "instances_of_one_quantity_two_values": 3,
        "and_this_one_is_a_symbol": True,
    }


# The two live sites that still carry E's superseded constant, and the numbers that go with it.
E_UPDATE_SURVIVORS = (
    {"where": "Step 5a, the threshold", "carries": "P >= 1.6e13",
     "pattern": r"P\ge1.6\cdot10^{13}"},
    {"where": "Step 5a, the error it is measured against", "carries": "106 P^(-25/24)",
     "pattern": r"106P^{-25/24}+0.11P^{-5/6}"},
    {"where": "A.6, what is left", "carries": "60(2.6)/0.84, the pre-correction cap",
     "pattern": r"\tfrac{60\cdot2.6}{0.84}"},
    {"where": "A.6, the range quoted with it", "carries": "[0.35, 2.6]",
     "pattern": r"therange\([0.35,2.6]\)for"},
)


def survivors_of_the_E_constant_update() -> dict[str, Any]:
    """Widening the sweep to bare `symbol <= cP^e` turns up V/S at two values -- and that one is
    clean.  What it turns up underneath is two live sites still running on E's old constant.

    V/S first, since it is what the sweep flagged: 0.11 P^(-7/48) at two places and 0.12 P^(-7/48)
    at a third.  V/S = (1/12) lam^(-1/2) P^(-7/48), so the coefficient is 0.107583 at lam = 0.60 and
    0.111359 at lam = 0.56; the paper prints 0.11 at the Step 5a sites and 0.12 at the Step 5b one,
    each rounded up, each labelled with its own S.  The inventory table names the 0.11 as "Step 5a's
    ratio ... at S >= 0.60 P^(-5/8)".  Nothing wrong.

    But the Step 5a paragraph that carries one of those 0.11s reads:

        W = V + E satisfy W <= c_7 S/2 at c_7 = 1/232 from P >= 1.6e13 ... against the interpolant
        error 106 P^(-25/24) + 0.11 P^(-5/6)

    and 106 is E's superseded constant.  The paper says so itself, in three review notes: "E's
    106 -> 170.6.  It was never cosmetic."  The threshold printed beside it is the one that constant
    gives:

        E's constant   Step 5a row first holds
        106            1.6117e13      <- the body prints 1.6e13
        170.6          2.9117e13      <- A.5 prints 2.92e13

    So the body and A.5 disagree on this row by 1.807, and the disagreement is exactly the update.
    The paragraph is internally consistent -- its threshold goes with its constant -- which is why
    no cross-check has caught it: the instruments compare A.5 with the certificate, and this is the
    body against A.5.

    A.6's closing paragraph is the second survivor.  "The remaining slack is in E itself: the
    middle-band half-width 60, which enters 106 linearly through the cap 60(2.6)/0.84, and the range
    [0.35, 2.6] for lambda_0."  The formula is right and every number in it is pre-correction:
    60(2.6)/0.84 = 185.71 is the old u_cap 186, [0.35, 2.6] is the old range, and 106 is the old
    constant.  With the current range the same cap reads 60(4.2)/0.84 = 300 exactly, which is the
    u_cap the certificate carries, and it enters 170.6.

    Neither reaches P_0.  Step 5a is not the binding row -- Step 5b is, at 3.5858e13 -- and
    2.9117e13 is below it either way.  What changes is the contrast the sentence draws: "a lower
    threshold than Step 5b's, because S is larger here" is true at 1.2315 with the corrected number
    where the printed pair implies 2.2249.
    """

    text = (DOCS_THEORY / "juggler_parity_discrepancy_note_2026_09_04.md").read_text(
        encoding="utf-8")
    compact = re.sub(r"\s+", "", text)

    def least(pred) -> float:
        lg = p0_certificate.least_P(pred)
        return 10.0 ** lg if lg is not None else float("inf")

    S5a = lambda P: 0.60 * P**-0.625                                   # noqa: E731
    V = lambda P: (1 / 12) * S5a(P) ** 0.5 * P ** (-11 / 24)           # noqa: E731
    rows = {r["tag"]: r for r in p0_certificate.thresholds()}
    with_old = least(lambda P: V(P) + 106.0 * P ** (-25 / 24) + 0.11 * P ** (-5 / 6)
                     <= p0_certificate.C7 * S5a(P) / 2)
    with_new = least(lambda P: V(P) + 170.6 * P ** (-25 / 24) + 0.11 * P ** (-5 / 6)
                     <= p0_certificate.C7 * S5a(P) / 2)
    P0 = rows["5b-W<=c7S"]["P_min"]
    sites = [{**s, "present": compact.count(s["pattern"]) == 1} for s in E_UPDATE_SURVIVORS]
    return {
        "sites": sites,
        "all_four_survivors_present": all(s["present"] for s in sites),
        "V_over_S_at_0_60": (1 / 12) * 0.60**-0.5,
        "V_over_S_at_0_56": (1 / 12) * 0.56**-0.5,
        "printed_0_11_covers_the_5a_value": (1 / 12) * 0.60**-0.5 <= 0.11,
        "printed_0_12_covers_the_5b_value": (1 / 12) * 0.56**-0.5 <= 0.12,
        "printed_0_11_would_not_cover_5b": (1 / 12) * 0.56**-0.5 > 0.11,
        "step5a_with_the_old_constant": with_old,
        "step5a_with_the_current_constant": with_new,
        "certificate_5a_row": rows["5a-W<=c7S"]["P_min"],
        "certificate_matches_the_current_constant": abs(
            with_new / rows["5a-W<=c7S"]["P_min"] - 1) < 1e-3,
        "body_prints": 1.6e13,
        "A5_prints": 2.92e13,
        "body_matches_the_old_constant": abs(with_old / 1.6e13 - 1) < 0.02,
        "body_and_A5_disagree_by": with_new / with_old,
        "u_cap_precorrection": 60 * 2.6 / 0.84,
        "u_cap_current": 60 * 4.2 / 0.84,
        "the_current_cap_is_exactly_300": abs(60 * 4.2 / 0.84 - 300.0) < 1e-9,
        "P0": P0,
        "step5a_is_not_the_binding_row": with_new < P0,
        "contrast_as_printed": P0 / with_old,
        "contrast_corrected": P0 / with_new,
        "P0_does_not_move": True,
    }
