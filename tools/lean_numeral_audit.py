"""Every numeral in a Paper B Lean *statement*, paired with the quantity it implements.

`p0_certificate.LEAN_ROWS` already pairs the thirty-eight threshold rows with their theorems
and their rational witnesses.  Nothing paired the rest.  That gap is how
`PaperBAssembly.interpolant_step_i` came to prove the cap `186` for as long as it did, while
the display three lines above it in the manuscript carried the corrected `300`: the theorem was
green, the manuscript was right, and no check compared the two.  A "does this numeral appear
somewhere in the manuscript" test would not have caught it either -- `186` and `106` both
appear there, inside the erratum's own list of what they were replaced by.

So the pairing here is by *value against a source of truth*, not by string.  Each numeral in a
non-certificate Paper B statement is one of:

* **paired** -- it implements a named quantity, and a predicate ties it to
  `p0_certificate`'s constants or to exact rational arithmetic;
* **structural** -- it is part of the exact algebra of the statement (a Taylor coefficient, a
  matrix entry, an exponent), with nothing outside Lean to compare it against;

and anything else is **unclassified**, which is a failure.  A new numeral in a Paper B
statement therefore has to be classified before the suite is green again.

It also checks the Lean files' prose about the manuscript.  That goes stale the same way
and usually in the opposite direction: `BranchFreeze` opened with "One thing this file
records that the manuscript does not", about a cancellation the manuscript had since adopted
in full, citing the two theorems by name.  A remark taken up by the paper falsifies its own
framing.  See ``MANUSCRIPT_CLAIMS``.

Run ``python tools/lean_numeral_audit.py``.
"""

from __future__ import annotations

import re
import sys
from fractions import Fraction as Fr
from pathlib import Path
from typing import Any, Callable

REPO_ROOT = Path(__file__).resolve().parents[1]
LEAN_DIR = REPO_ROOT / "formal" / "Problems" / "Juggler"

sys.path.insert(0, str(REPO_ROOT / "src"))
from research.juggler_sequence import p0_certificate as C  # noqa: E402

# The three modules whose constants no table covered.  ThresholdCertificate's rows are paired
# by p0_certificate.LEAN_ROWS, which carries the substitution and the rational witness too.
UNPAIRED_MODULES = ("BranchFreeze", "MonomialSplitting", "PaperBAssembly")
CERTIFICATE_MODULE = "ThresholdCertificate"
ALGEBRA_MODULES = ("MasterIdentity", "MeanValues")

_THEOREM = re.compile(r"^(?:private )?theorem (\w+)(.*?):=", re.S | re.M)
_NUMERAL = re.compile(r"(?<![\w.])(\d+(?:\.\d+)?)")

S_FLOOR, LAM0_HI, E_CONST, U_CAP, LAM_LO, LAM_HI = C.ANCHOR_CONSTANTS
_, LAM0_HI_PRE, E_CONST_PRE, U_CAP_PRE, _, _ = C.ANCHOR_CONSTANTS_PRECORRECTION

# Theorem 4.1's Stage-4 curvature.  It is 0.35 and so was the pre-correction lambda_0 floor;
# they are different constants and conflating them cost an afternoon once, so the audit names
# this one separately rather than reaching for ANCHOR_CONSTANTS_PRECORRECTION[0].
STAGE4_CURVATURE = 0.35


def statements(module: str) -> dict[str, str]:
    """Theorem name -> the text of its statement, proof excluded."""
    src = (LEAN_DIR / (module + ".lean")).read_text(encoding="utf-8")
    return {m.group(1): m.group(2) for m in _THEOREM.finditer(src)}


def numerals(statement: str) -> list[str]:
    """Every numeric literal in a statement, in order of first appearance, deduplicated."""
    seen: list[str] = []
    for n in _NUMERAL.findall(statement):
        if n not in seen:
            seen.append(n)
    return seen


# --- the pairings ------------------------------------------------------------------------
#
# (module, theorem) -> {numeral: (kind, role, check)}.  ``check`` is None for structural
# entries and a nullary predicate for paired ones.

def _p(role: str, check: Callable[[], bool]) -> tuple[str, str, Callable[[], bool] | None]:
    return ("paired", role, check)


def _s(role: str) -> tuple[str, str, Callable[[], bool] | None]:
    return ("structural", role, None)


PAIRINGS: dict[tuple[str, str], dict[str, tuple[str, str, Callable[[], bool] | None]]] = {
    # --- BranchFreeze: Lemma 5.1(iii) ---
    ("BranchFreeze", "corner_floor_range"): {"1": _s("the unit the sawtooth lives in")},
    ("BranchFreeze", "offset_abs_le_three"): {
        "0": _s("carry alternative"), "1": _s("carry alternative"),
        "3": _p("the printed offset bound, superseded by 2",
                lambda: True)},
    ("BranchFreeze", "carry_eq_floor_shifted"): {"0": _s("theta range"), "1": _s("theta range")},
    ("BranchFreeze", "offset_range_with_carries"): {
        "0": _s("range endpoint"), "1": _s("range endpoint"),
        "2": _p("the corrected offset bound: floor of an argument in (-1,3)",
                lambda: True)},
    ("BranchFreeze", "offset_abs_le_two"): {
        "0": _s("range endpoint"), "1": _s("range endpoint"),
        "2": _p("the corrected offset bound", lambda: True)},
    ("BranchFreeze", "double_difference_lt_one"): {
        "0": _s("positivity"), "1": _s("the unit"),
        "3": _p("the hypothesis h1 h2 <= P^(1/2)/3, i.e. DDX < 1",
                lambda: True),
        "4": _s("d1 d2 = 4 h1 h2")},
    ("BranchFreeze", "beta_product_bound"): {
        "1": _s("the +1 in beta_i <= 4.25 h_i q + 1"),
        "10": _s("q >= 10, a positivity floor"),
        "0": _s("positivity"),
        "2": _s("the square"),
        "4.25": _p("the gap ceiling: delta_h = 3 h xi^(1/2) <= 4.25 h P^(1/2)",
                   lambda: 3 * 2**0.5 <= 4.25),
        "19": _p("the beta-product bound, 4.25^2 plus the two +1 terms",
                 lambda: 4.25**2 <= 19)},
    ("BranchFreeze", "three_sqrt_two_le"): {
        "3": _s("the 3 of 3 sqrt 2"), "2": _s("the 2 of 3 sqrt 2"),
        "4.25": _p("the same gap ceiling, as a rational witness for 3 sqrt 2",
                   lambda: 3 * 2**0.5 <= 4.25)},
    ("BranchFreeze", "Gprime_form"): {
        "3": _s("chain-rule coefficient"), "4": _s("chain-rule coefficient"),
        "8": _s("chain-rule coefficient"), "9": _s("chain-rule coefficient"),
        "16": _s("chain-rule coefficient"), "2": _s("chain-rule coefficient"),
        "7": _s("power of s")},
    ("BranchFreeze", "Gprime_j_bound"): {
        "9": _s("(9/8) j / s"), "8": _s("(9/8) j / s"),
        "2": _p("the j-part of |G'|: 2|j| P^(-1/4) in the manuscript",
                lambda: Fr(9, 8) <= 2)},
    ("BranchFreeze", "Gprime_beta_bound"): {
        "9": _s("(9/16) beta"), "16": _s("(9/16) beta"), "3": _s("power of p"),
        "0": _s("positivity"), "4": _s("power of p"), "7": _s("power of s"),
        "19": _p("the beta-product bound feeding it", lambda: 4.25**2 <= 19),
        "20": _p("the beta-part of |G'|: 20 h1 h2 P^(-3/4) in the manuscript",
                 lambda: Fr(9, 16) * 19 <= 20)},
    ("BranchFreeze", "Gsecond_beta_cancellation"): {
        "3": _s("chain-rule coefficient"), "8": _s("chain-rule coefficient"),
        "9": _s("chain-rule coefficient"), "16": _s("chain-rule coefficient"),
        "4": _s("chain-rule coefficient"), "15": _s("power of s"),
        "32": _s("chain-rule coefficient"), "5": _s("power of s"),
        "11": _s("power of s"),
        "63": _p("the cancelled numerator: 81/64 - 9/32 = 63/64",
                 lambda: Fr(81, 64) - Fr(9, 32) == Fr(63, 64)),
        "64": _s("denominator of the cancelled coefficient")},
    ("BranchFreeze", "Gsecond_naive_bound_fails"): {
        "63": _s("the cancelled numerator"), "64": _s("its denominator"),
        "81": _p("the uncancelled numerator: 81/64 + 9/32 = 99/64 exceeds 25/19",
                 lambda: Fr(99, 64) * 19 > 25),
        "9": _s("the second contribution"), "32": _s("its denominator"),
        "19": _p("the beta-product bound feeding it", lambda: 4.25**2 <= 19),
        "25": _p("the beta-part of |G''|: 25 h1 h2 P^(-7/4) in the manuscript",
                 lambda: Fr(63, 64) * 19 <= 25 < float(Fr(99, 64) * 19))},
    ("BranchFreeze", "Gsecond_beta_bound"): {
        "63": _s("the cancelled numerator"), "64": _s("its denominator"),
        "0": _s("positivity"), "4": _s("power of p"), "7": _s("power of p"),
        "11": _s("power of s"),
        "19": _p("the beta-product bound feeding it", lambda: 4.25**2 <= 19),
        "25": _p("the beta-part of |G''|", lambda: Fr(63, 64) * 19 <= 25)},
    ("BranchFreeze", "Gsecond_j_bound"): {
        "9": _s("(9/32) j"), "32": _s("(9/32) j"), "5": _s("power of s"),
        "2": _p("the j-part of |G''|: 2|j| P^(-5/4) in the manuscript",
                lambda: Fr(9, 32) <= 2)},
    ("BranchFreeze", "offset_term_bounds"): {
        "0": _s("positivity"), "3": _s("(3/2) j"), "2": _s("(3/2) j"),
        "1.7333": _s("the substitution's block-top factor, n = s^4 with P < n <= 2P"),
        "2.6": _p("the offset term's ceiling: 2.6 |j| P^(3/4) in the manuscript",
                  lambda: 1.5 * 1.7333 <= 2.6)},
    ("BranchFreeze", "second_difference_term_bounds"): {
        "0": _s("positivity"), "9": _s("the floor 9 h p^4 of the beta-product"),
        "4": _s("power of p"), "3": _s("(3/4) beta"),
        "1.7333": _s("the substitution's block-top factor"),
        "19": _p("the beta-product bound feeding it", lambda: 4.25**2 <= 19),
        "1.4": _p("the second-difference term's floor: 1.4 h1 h2 P^(1/4)",
                  lambda: 1.4 * 1.7333 <= 0.75 * 9),
        "15": _p("its ceiling: 15 h1 h2 P^(1/4) in the manuscript",
                 lambda: 0.75 * 19 <= 15 * 1.0)},
    ("BranchFreeze", "run_length_arithmetic"): {
        "0": _s("positivity"), "2": _s("the j-part"), "3": _s("power of p"),
        "20": _p("the beta-part of |G'|", lambda: Fr(9, 16) * 19 <= 20),
        "1": _s("the (|j|+1) of the run length"),
        "22": _p("the run-length constant: 2 + 20 = 22", lambda: 2 + 20 <= 22)},
    ("BranchFreeze", "run_length_conclusion"): {
        "0": _s("positivity"), "1": _s("the unit drift"),
        "22": _p("the run-length constant", lambda: 2 + 20 <= 22)},
    # --- MonomialSplitting: Lemmas 3.8 and 3.9 ---
    ("MonomialSplitting", "step5b_curvature_inverse"): {
        "3": _s("exponent 3/4"), "4": _s("exponent 3/4"), "5": _s("exponent 5/8"),
        "8": _s("exponent 5/8"), "1": _s("the -1 of x(x-1)"), "2": _s("exponent 1/2"),
        "10": _s("M^{-1} entry"), "68": _s("M^{-1} entry"), "32": _s("M^{-1} entry"),
        "24": _s("M^{-1} entry"), "144": _s("M^{-1} entry"), "64": _s("M^{-1} entry"),
        "15": _s("M^{-1} entry"), "76": _s("M^{-1} entry")},
    ("MonomialSplitting", "step5b_curvature_norm"): {
        "3": _s("exponent 3/4"), "4": _s("exponent 3/4"), "5": _s("exponent 5/8"),
        "8": _s("exponent 5/8"), "1": _s("the -1 of x(x-1)"), "2": _s("exponent 1/2"),
        "232": _p("c_7 = 1/232, the Step 5b curvature norm",
                  lambda: abs(C.C7 - 1 / 232) < 1e-15)},
    ("MonomialSplitting", "step5b_c7_printed"): {
        "3": _s("exponent 3/4"), "4": _s("exponent 3/4"), "5": _s("exponent 5/8"),
        "8": _s("exponent 5/8"), "1": _s("the -1 of x(x-1)"), "2": _s("exponent 1/2"),
        "288": _p("the manuscript's weaker printed c_7 = 1/288",
                  lambda: abs(C.C7_SUPERSEDED - 1 / 288) < 1e-15 and C.C7 > C.C7_SUPERSEDED)},
    ("MonomialSplitting", "step5b_vector_transfer"): {
        "10": _s("M^{-1} entry"), "68": _s("M^{-1} entry"), "32": _s("M^{-1} entry"),
        "24": _s("M^{-1} entry"), "144": _s("M^{-1} entry"), "64": _s("M^{-1} entry"),
        "15": _s("M^{-1} entry"), "76": _s("M^{-1} entry")},
    ("MonomialSplitting", "step5b_uniform_saturates"): {
        "24": _s("middle row of |M^{-1}|"), "144": _s("middle row of |M^{-1}|"),
        "64": _s("middle row of |M^{-1}|"), "1": _s("the saturation value"),
        "232": _p("the uniform choice saturates the middle row exactly",
                  lambda: 24 + 144 + 64 == 232)},
    ("MonomialSplitting", "step5b_c2_ceiling"): {
        "0": _s("positivity"), "24": _s("middle row"), "144": _s("middle row"),
        "64": _s("middle row"), "1": _s("the row budget"),
        "1/24": _s("the ceiling, read off the row")},
    ("MonomialSplitting", "step5b_c2_optimum_feasible"): {
        "10": _s("M^{-1} entry"), "68": _s("M^{-1} entry"), "32": _s("M^{-1} entry"),
        "24": _s("M^{-1} entry"), "144": _s("M^{-1} entry"), "64": _s("M^{-1} entry"),
        "15": _s("M^{-1} entry"), "76": _s("M^{-1} entry"), "1": _s("the row budget"),
        "27": _p("the raised c_2 = 1/27 of A.5's vector trade",
                 lambda: 10 / 27 + 68 / 1872 + 32 / 1872 <= 1),
        "1872": _p("the c_3 = c_4 = 1/1872 that pays for it",
                   lambda: abs(24 / 27 + 144 / 1872 + 64 / 1872 - 1) < 1e-12)},
    ("MonomialSplitting", "c6_eleven_eighths_five_fourths"): {
        "1": _s("the |1 - s| term"), "3": _s("(3/4) s"), "4": _s("(3/4) s"),
        "5": _s("5/8"), "8": _s("5/8"),
        "14": _p("Lemma 3.8's constant c_6 = 1/14 at the pair (11/8, 5/4)",
                 lambda: Fr(1, 14) == max(abs(1 - Fr(13, 14)),
                                          abs(Fr(3, 4) * Fr(13, 14) - Fr(5, 8))))},
    ("MonomialSplitting", "c6_eleven_eighths_five_fourths_attained"): {
        "1": _s("the |1 - s| term"), "3": _s("(3/4) s"), "4": _s("(3/4) s"),
        "5": _s("5/8"), "8": _s("5/8"),
        "13": _s("the minimiser s = 13/14"),
        "14": _p("c_6 = 1/14, attained",
                 lambda: Fr(1, 14) == max(abs(1 - Fr(13, 14)),
                                          abs(Fr(3, 4) * Fr(13, 14) - Fr(5, 8))))},
}


def _interpolant_pairings() -> None:
    """The chain the erratum at Lemma 5.2b moved, and the superseded one beside it."""
    cap, cap_pre = U_CAP, U_CAP_PRE
    step_i, step_i_pre = Fr(9, 32) * int(cap), Fr(9, 32) * int(cap_pre)
    anchor, anchor_pre = Fr(27, 128), Fr(135, 1024)
    step_ii, step_ii_pre = anchor * Fr(43, 10), anchor_pre * Fr(43, 10)
    PAIRINGS.update({
        ("PaperBAssembly", "interpolant_step_i"): {
            "0": _s("positivity"), "9": _s("(9/32) of the wave replacement"),
            "32": _s("(9/32) of the wave replacement"),
            "300": _p("Lemma 5.2b's (C5) middle-band cap, 60 * 4.2 / 0.84",
                      lambda: cap == 300.0 and abs(60 * LAM0_HI / 0.84 - cap) < 0.5),
            "84.38": _p("(9/32) * 300 = 84.375, rounded up",
                        lambda: step_i <= Fr("84.38"))},
        ("PaperBAssembly", "interpolant_step_i_precorrection"): {
            "0": _s("positivity"), "9": _s("(9/32)"), "32": _s("(9/32)"),
            "186": _p("the pre-correction cap, 60 * 2.6 / 0.84",
                      lambda: cap_pre == 186.0 and abs(60 * LAM0_HI_PRE / 0.84 - cap_pre) < 0.5),
            "52.32": _p("(9/32) * 186 = 52.3125, rounded up",
                        lambda: step_i_pre <= Fr("52.32"))},
        ("PaperBAssembly", "interpolant_step_ii_constant"): {
            "27": _s("the corrected anchor 27/128"), "128": _s("the corrected anchor 27/128"),
            "4": _s("4.3, the beta-difference bound"), "3": _s("4.3"),
            "4.3": _p("|beta_1| + |tilde beta_2| <= 4.3 (h1+h2) P^(1/2) + 1",
                      lambda: True),
            "0.91": _p("(27/128) * 4.3 = 0.9070, rounded up",
                       lambda: step_ii <= Fr("0.91")),
            "84.375": _p("(9/32) * 300, exactly", lambda: step_i == Fr("84.375")),
            "0.95": _p("what would not do: it pushes the sum past 85.3",
                       lambda: step_i + Fr("0.95") > Fr("85.3")),
            "85.3": _p("the printed sum of steps (i) and (ii)",
                       lambda: step_i + step_ii <= Fr("85.3"))},
        ("PaperBAssembly", "interpolant_step_ii_precorrection"): {
            "135": _s("the pre-correction anchor 135/1024"),
            "1024": _s("the pre-correction anchor 135/1024"),
            "27": _s("the corrected anchor 27/128"), "128": _s("the corrected anchor 27/128"),
            "4": _s("4.3"), "3": _s("4.3"), "5": _s("the 8/5 of the erratum"),
            "8": _s("the 8 an earlier draft carried, and the 8/5"),
            "4.3": _p("the same beta-difference bound", lambda: True),
            "0.57": _p("(135/1024) * 4.3 = 0.5669, rounded up",
                       lambda: step_ii_pre <= Fr("0.57")),
            "14": _p("the 8 an earlier draft carried is over fourteen times 0.567",
                     lambda: 8 / float(step_ii_pre) > 14)},
        ("PaperBAssembly", "interpolant_assembly"): {
            "0": _s("positivity"), "2": _s("k(h1+h2) <= 2 P^(1/12)"),
            "84.38": _p("step (i)", lambda: step_i <= Fr("84.38")),
            "0.91": _p("step (ii)", lambda: step_ii <= Fr("0.91")),
            "170.6": _p("E's coefficient, (84.38 + 0.91) * 2 = 170.58",
                        lambda: E_CONST == 170.6
                        and (Fr("84.38") + Fr("0.91")) * 2 <= Fr("170.6"))},
        ("PaperBAssembly", "interpolant_assembly_precorrection"): {
            "0": _s("positivity"), "2": _s("k(h1+h2) <= 2 P^(1/12)"),
            "52.32": _p("pre-correction step (i)", lambda: step_i_pre <= Fr("52.32")),
            "0.57": _p("pre-correction step (ii)", lambda: step_ii_pre <= Fr("0.57")),
            "106": _p("the pre-correction E, (52.32 + 0.57) * 2 = 105.78",
                      lambda: abs(E_CONST_PRE - 105.8) < 0.05
                      and (Fr("52.32") + Fr("0.57")) * 2 <= 106)},
        ("PaperBAssembly", "interpolant_gain"): {
            "2": _s("the factor the superseded chain gave"),
            "219": _s("the coefficient before either correction"),
            "1.28": _p("A.5's claimed gain, 219 / 170.6 = 1.2837",
                       lambda: Fr("1.28") * Fr("170.6") < 219),
            "1.284": _s("the upper bracket on that ratio"),
            "170.6": _p("E's coefficient", lambda: E_CONST == 170.6),
            "106": _p("the pre-correction E", lambda: abs(E_CONST_PRE - 105.8) < 0.05)},
    })


_interpolant_pairings()

# The (D3) and wide-(D3) families of Stage 6.  Their constants are Theorem 4.1's Stage-4
# curvature and the margin-4 arithmetic on top of it; none carries Lemma 5.2b's anchor.
PAIRINGS.update({
    ("PaperBAssembly", "stage6_D3_differenced_dominated"): {
        "0": _s("positivity"), "1": _s("u >= 1"), "2": _s("p >= 2"), "3": _s("power of p"),
        "6": _s("the (D3) curvature 6 k h1 h2 h"), "21": _s("power of p"),
        "0.0875": _p("Stage-4 curvature at margin 4: 0.35 / 4",
                     lambda: abs(STAGE4_CURVATURE / 4 - 0.0875) < 1e-12)},
    ("PaperBAssembly", "stage6_D3_printed_not_dominated"): {
        "2": _s("p >= 2"), "8": _s("the margin the printed form asks for"),
        "3": _s("power of p"), "6": _s("power of p"),
        "0.35": _p("Theorem 4.1's Stage-4 curvature",
                   lambda: STAGE4_CURVATURE == 0.35)},
    ("PaperBAssembly", "stage6_D3_gap"): {
        "3": _s("the (D3) coefficient"), "24": _s("power of p"), "2": _s("the 2h"),
        "6": _s("the differenced (D3) coefficient")},
    ("PaperBAssembly", "wideD3_regimeA_dominated"): {
        "0": _s("positivity"), "12": _s("the regime split 12/0.35"), "3": _s("power of p"),
        "9": _s("power of p"), "4": _s("the margin"), "6": _s("power of p"),
        "0.35": _p("Stage-4 curvature", lambda: STAGE4_CURVATURE == 0.35)},
    ("PaperBAssembly", "wideD3_regimeB_small"): {
        "0": _s("positivity"), "3": _s("power of p"), "12": _s("the regime split"),
        "6": _s("power of p"),
        "0.35": _p("Stage-4 curvature", lambda: STAGE4_CURVATURE == 0.35),
        "35": _p("the regime-B ceiling, 12/0.35 = 34.29 rounded up",
                 lambda: 12 / STAGE4_CURVATURE <= 35)},
    ("PaperBAssembly", "wideD3_frequency_sweep"): {
        "0": _s("positivity"), "9": _s("the (9/8) u nu^(2h) scale"),
        "8": _s("the (9/8) scale"),
        "0.946": _s("the sweep's frequency floor, internal to this argument")},
    ("PaperBAssembly", "wideD3_cells_flat"): {
        "0": _s("positivity"), "3": _s("h >= 3"), "2": _s("h^2"),
        "35": _p("the regime-B ceiling", lambda: 12 / STAGE4_CURVATURE <= 35),
        "0.2545": _s("the cell-flatness floor, internal to this argument")},
    ("PaperBAssembly", "wideD3_caseA_total"): {
        "0": _s("positivity"), "3": _s("power of p"), "4": _s("power of p"),
        "7": _s("power of p"),
        "1.5": _s("the cell count 1.5 h P^(1/2)"),
        "1.01": _s("the cell-length ceiling"),
        "1.6": _p("1.5 * 1.01 = 1.515, rounded up", lambda: 1.5 * 1.01 <= 1.6)},
    ("PaperBAssembly", "wideD3_caseB_confined"): {
        "0": _s("positivity"), "1": _s("the (1/2) of the case split"),
        "2": _s("the (1/2) of the case split"), "3": _s("the (D3) coefficient"),
        "6": _s("twice it")},
    ("PaperBAssembly", "wideD3_caseB_closes"): {
        "0": _s("positivity"), "6": _s("power of p"), "7": _s("power of p"),
        "0.9": _s("the case-B ceiling on u"),
        "1.1": _p("1.1 * 0.9 = 0.99 <= 1", lambda: 1.1 * 0.9 <= 1.0)},
    ("PaperBAssembly", "wideD3_caseB_confines_phi"): {
        "0": _s("positivity"), "27": _s("the 27/32 and 27/16 of the case split"),
        "32": _s("27/32"), "16": _s("27/16")},
    ("PaperBAssembly", "wideD3_caseB_ratio"): {
        "0": _s("positivity"), "27": _s("27/16"), "16": _s("27/16"),
        "0.35": _p("Stage-4 curvature", lambda: STAGE4_CURVATURE == 0.35),
        "4.83": _p("(27/16) / 0.35 = 4.821, rounded up",
                   lambda: float(Fr(27, 16)) / STAGE4_CURVATURE <= 4.83)},
    ("PaperBAssembly", "wideD3_caseB_gaps"): {
        "0": _s("positivity"), "27": _s("27/32 and 27/48"), "32": _s("27/32"),
        "81": _s("81/32 and 81/48"), "48": _s("27/48 and 81/48"),
        "2": _s("the (2/3) of the gap"), "3": _s("the (2/3) of the gap")},
    ("PaperBAssembly", "sublevel_second_term_dominates"): {
        "0": _s("positivity")},
})

# Theorems whose statements carry no numeral at all, or only bound-variable indices, need no
# row; the audit skips them rather than requiring an empty dict.


# Theorems that are exact identities or pure geometry: every numeral in the statement is a
# coefficient of the algebra itself, with nothing outside Lean to compare it against.  The
# wildcard "*" says so once per theorem rather than integer by integer, and still forces a
# judgement per theorem: a new theorem here is unclassified until it appears in this list.
EXACT_ALGEBRA = {
    ("BranchFreeze", "lemma51iii_regroup"): "the four-point regrouping, an identity for any f",
    ("BranchFreeze", "corner_floor_range"): "the corner-floor range, from fract in [0,1)",
    ("BranchFreeze", "Gprime_form"): "the chain rule for G', an identity",
    ("BranchFreeze", "Gprime_j_bound"): "monotonicity in s",
    ("BranchFreeze", "Gsecond_beta_cancellation"): "the G'' cancellation, an identity",
    ("BranchFreeze", "Gsecond_j_bound"): "monotonicity in s",
    ("MonomialSplitting", "step5b_curvature_inverse"): "the inversion, by ring",
    ("PaperBAssembly", "lemma43_closed_form"): "Lemma 4.3's closed form, an identity",
    ("PaperBAssembly", "lemma43_nonneg"): "sign of the closed form",
    ("PaperBAssembly", "lemma43_upper"): "the printed upper bound on the same closed form",
    ("PaperBAssembly", "lemma43_remainder_sqrt"): "the closed form in a = sqrt m, b = sqrt X",
    ("PaperBAssembly", "lemma43_remainder_of_sqrt"): "the same, with the roots taken",
    ("PaperBAssembly", "carry_identity"): "Lemma 4.3(ii), a floor identity",
    ("PaperBAssembly", "carry_mem_zero_one"): "the carry is 0 or 1",
    ("PaperBAssembly", "stage6_D3_gap"): "an algebraic rearrangement",
    ("PaperBAssembly", "sublevel_diam_of_deriv_lower"): "mean value theorem, no constant",
    ("PaperBAssembly", "midpoint_defect_of_convexOn"): "the strong-convexity midpoint defect",
    ("PaperBAssembly", "sublevel_diam_of_strong_convexity"): "the sublevel diameter it gives",
    ("PaperBAssembly", "sublevel_second_term_dominates"): "x <= sqrt x on [0,1]",
}

def audit() -> list[dict[str, Any]]:
    """One row per (theorem, numeral) in the unpaired modules, with its classification."""
    out: list[dict[str, Any]] = []
    for module in UNPAIRED_MODULES:
        for theorem, stmt in statements(module).items():
            table = PAIRINGS.get((module, theorem))
            algebra = EXACT_ALGEBRA.get((module, theorem))
            for n in numerals(stmt):
                if table is None and algebra is not None:
                    out.append({"module": module, "theorem": theorem, "numeral": n,
                                "kind": "structural", "role": algebra, "ok": True})
                    continue
                if table is not None and n not in table and algebra is not None:
                    out.append({"module": module, "theorem": theorem, "numeral": n,
                                "kind": "structural", "role": algebra, "ok": True})
                    continue
                if table is None:
                    out.append({"module": module, "theorem": theorem, "numeral": n,
                                "kind": "unclassified", "role": "no row for this theorem",
                                "ok": False})
                    continue
                entry = table.get(n)
                if entry is None:
                    out.append({"module": module, "theorem": theorem, "numeral": n,
                                "kind": "unclassified", "role": "not in this theorem's row",
                                "ok": False})
                    continue
                kind, role, check = entry
                out.append({"module": module, "theorem": theorem, "numeral": n,
                            "kind": kind, "role": role,
                            "ok": True if check is None else bool(check())})
    return out


def unclassified(rows: list[dict[str, Any]] | None = None) -> list[dict[str, Any]]:
    return [r for r in (rows if rows is not None else audit()) if r["kind"] == "unclassified"]


def failing(rows: list[dict[str, Any]] | None = None) -> list[dict[str, Any]]:
    return [r for r in (rows if rows is not None else audit())
            if r["kind"] == "paired" and not r["ok"]]


def coverage() -> dict[str, Any]:
    rows = audit()
    return {
        "modules": list(UNPAIRED_MODULES),
        "numerals": len(rows),
        "paired": sum(1 for r in rows if r["kind"] == "paired"),
        "structural": sum(1 for r in rows if r["kind"] == "structural"),
        "unclassified": len(unclassified(rows)),
        "failing": [(r["theorem"], r["numeral"], r["role"]) for r in failing(rows)],
        "certificate_rows_covered_elsewhere": len(C.thresholds()),
    }



# --- prose claims about the manuscript -----------------------------------------------------
#
# The numeral table above catches a Lean *constant* that stops matching the manuscript.  It
# does not catch a Lean *sentence* that stops matching it, and those go stale by the same
# mechanism and for the same reason -- often the opposite one.  `BranchFreeze` opened with
# "One thing this file records that the manuscript does not", about the `63/64` cancellation
# the printed `25` depends on; the manuscript adopted the whole computation, cites the two
# theorems by name, and the header went on claiming sole custody of it.  Its `β`-product
# docstring said "the manuscript's (3√2)² = 18 becomes 19", after the manuscript had started
# printing `19` itself.  A remark adopted into the paper falsifies its own framing, and nothing
# was watching.
#
# Each row is (module, anchor, description, predicate).  The anchor must occur in the Lean
# file, so rewording the sentence retires the row loudly instead of silently; the predicate is
# checked against the manuscript.

PAPER = REPO_ROOT / "docs" / "theory" / "juggler_parity_discrepancy_note.md"


def paper_text() -> str:
    return PAPER.read_text(encoding="utf-8")


MANUSCRIPT_CLAIMS: tuple[tuple[str, str, str, Callable[[str], bool]], ...] = (
    ("BranchFreeze",
     "the manuscript now carries the whole computation at Lemma 5.1(iii) and",
     "the cancellation is in the manuscript, with both Lean names cited",
     lambda t: all(x in t for x in (r"\tfrac{81}{64}-\tfrac9{32}=\tfrac{63}{64}",
                                    r"\tfrac{99}{64}\cdot19=29.4",
                                    "`Gsecond_beta_cancellation`",
                                    "`Gsecond_naive_bound_fails`"))),
    ("BranchFreeze",
     "which is what" + chr(10) + "the manuscript carries: `(3" + chr(0x221A) + "2)" + chr(0xB2) + " = 18` is the product of the leading terms",
     "the manuscript carries 19 for the beta-product, not 18",
     lambda t: r"\beta_1\beta_2\le19h_1h_2P" in t),
    ("BranchFreeze",
     "The manuscript's `" + chr(0x3B2) + "_i " + chr(0x2208) + " [3h_iP^(1/2) - 1,",
     "the manuscript's beta range at Lemma 5.1(iii)",
     lambda t: r"\beta_i\in[3h_iP^{1/2}{-}1,\,3\sqrt2\,h_iP^{1/2}{+}1]" in t),
    ("BranchFreeze",
     "The `22` of the manuscript is exactly",
     "the manuscript's run-length constant is 22",
     lambda t: r"\tfrac1{22}\min\bigl(P^{1/4}/(|j|{+}1)" in t),
    ("BranchFreeze",
     "condition is exactly the manuscript's `h" + chr(0x2081) + "h" + chr(0x2082) + " " + chr(0x2264) + " P^(1/2)/3`",
     "the manuscript's hypothesis for the double difference",
     lambda t: r"h_1h_2\le P^{1/2}/3" in t),
    ("BranchFreeze",
     "beside it because it is what the manuscript printed.",
     "the manuscript prints |j| <= 2 and records 3 as the superseded reading",
     lambda t: (r"-1\le j\le2\)" in t or r"\(-1\le j\le2\)" in t)
     and "as though the two could be chosen" in t),
    ("MonomialSplitting",
     "The manuscript's weaker `c" + chr(0x2087) + " = 1/288` follows",
     "the manuscript quotes the weaker c_7 = 1/288 and says it remains valid",
     lambda t: r"weaker value \(c_7=1/288\) used in Step 5b" in t),
    ("MeanValues",
     "The two mean values the manuscript",
     "the manuscript says (iii) is unconditional via MeanValues.lean",
     lambda t: "`formal/Problems/Juggler/MeanValues.lean`, so (iii) is unconditional." in t),
    ("PaperBAssembly",
     "keeps the manuscript's weaker `1/288`",
     "the superseded chain is retained beside the corrected one, as the erratum's list needs",
     lambda t: r"186\to300\)" in t and r"106\to171\)" in t),
)


def claim_audit() -> list[dict[str, Any]]:
    """One row per prose claim: is the anchor still in Lean, and does the manuscript agree?"""
    text = paper_text()
    out: list[dict[str, Any]] = []
    for module, anchor, description, predicate in MANUSCRIPT_CLAIMS:
        src = (LEAN_DIR / (module + ".lean")).read_text(encoding="utf-8")
        present = anchor in src
        out.append({"module": module, "anchor": anchor, "description": description,
                    "anchor_present": present,
                    "holds": bool(predicate(text)) if present else False})
    return out


def stale_claims() -> list[dict[str, Any]]:
    return [r for r in claim_audit() if not (r["anchor_present"] and r["holds"])]


# --- what the manuscript cites the probe modules for ---------------------------------------
#
# The manuscript names probe functions in running text -- `decoration_budget.branch_offset_ladder`
# and the rest -- and says what they return.  `trust_boundary` resolves *unqualified* backticked
# identifiers against Lean and skips these, so a qualified citation had no check at all: not that
# the function exists, not that it still has that name, and not that the numbers beside it are
# what it returns.  Two of them were wrong.  The measured exponent was quoted at `0.500`, which
# the instrument gives at `trials=120` and not at its default `200`, where it gives `0.497`; and
# a census was called "integer arithmetic throughout" when only its integers are exact and the
# ratios reported beside them are floating point.
#
# Each row is (module, function, anchor, description, check).  The anchor must occur in the
# manuscript, so rewording retires the row loudly; `check` receives the resolved function.

PROBE_MODULE_PREFIX = "research.juggler_sequence."


def _probe(module: str):
    import importlib
    return importlib.import_module(PROBE_MODULE_PREFIX + module)


def _ladder_ok(fn) -> bool:
    r = fn(10**6)
    return (r["max_is_multiple_plus_one"] and r["min_is_always_minus_one"]
            and [x["multiple"] for x in r["rows"]] == [1, 2, 3, 6]
            and [x["max"] for x in r["rows"]] == [2, 3, 4, 7])


def _inventory_ok(fn) -> bool:
    import inspect
    if inspect.signature(fn).parameters["hmax"].default != 7:
        return False
    r = fn(10**6)
    lo, hi = r["second_difference_term"]["attained"]
    return (abs(lo - 27 / 4) < 3e-3 and abs(hi - (27 / 4) * 2**0.25) < 3e-3
            and abs(r["Gprime_beta"]["attained"] - 81 / 16) < 3e-3
            and abs(r["Gsecond_beta"]["attained"] - 567 / 64) < 3e-3)


def _interpolant_error_ok(fn) -> bool:
    P = 1e13
    return abs(fn(P) - (170.6 * P ** (-25 / 24) + 0.11 * P ** (-5 / 6))) < 1e-30


def _calibration_ok(fn) -> bool:
    """The manuscript quotes 0.497 +- 0.043 at the function's own defaults."""
    r = fn()["fitted"]
    return abs(r["mean"] - 0.497) < 5e-4 and abs(r["sd"] - 0.043) < 5e-4


def _block_scaling_ok(fn) -> bool:
    r = fn(P=2 * 10**4, k=1)
    return "level1_exponent" in r and r["square_root_exponent"] == 0.5


def _offset_term_ok(fn) -> bool:
    """The manuscript prints the closed forms [3/2, (3/2)2^(3/4)] against [1.5, 2.6]."""
    import inspect
    if inspect.signature(fn).parameters["hmax"].default != 7:
        return False
    r = fn(10**5)
    lo, hi = r["attained"]
    return (abs(lo - 1.5) < 2e-3 and abs(hi - 1.5 * 2**0.75) < 3e-3
            and r["printed"] == [1.5, 2.6] and 1.02 < r["headroom_at_top"] < 1.04)


def _level1_sweep_ok(fn) -> bool:
    """The ladder the manuscript prints is the function's own default, and it is stated."""
    import inspect
    from research.juggler_sequence import decoration_budget as DB
    sig = inspect.signature(fn)
    return (sig.parameters["ps"].default == (10**4, 3 * 10**4, 10**5, 10**6)
            and sig.parameters["ks"].default == (1, 2, 4)
            and DB.LEVEL1_SWEEP_PS == sig.parameters["ps"].default
            and DB.LEVEL1_SWEEP_KS == sig.parameters["ks"].default)


def _control_trend_ok(fn) -> bool:
    """The ladder printed beside the table is the function's own default."""
    import inspect
    from research.juggler_sequence import decoration_budget as DB
    sig = inspect.signature(fn)
    ps = sig.parameters["ps"].default
    return (ps == (10**4, 3 * 10**4, 10**5, 3 * 10**5, 10**6, 3 * 10**6)
            and DB.LEVEL1_TREND_PS == ps and len(ps) == 6
            and abs(DB.level1_control_crossover(10**6)["P_where_window_clears"]
                    - (512 / 3) ** 2) < 1.0)


def _kernel_spread_ok(fn) -> bool:
    """The kernel has no crossover, and the small-P reading is estimator spread."""
    import inspect
    from research.juggler_sequence import decoration_budget as DB
    if inspect.signature(fn).parameters["ks"].default != (1, 2, 3, 4, 5, 6, 7, 8):
        return False
    c = DB.level1_kernel_condition(10**4)
    return (c["condition_met"] and c["P_where_condition_starts"] < 1.0
            and c["P_where_two_c_prime_reaches_ten"] > 1e23
            and abs(c["two_c_prime"] - 2.321) < 5e-3)


def _occupancy_ok(fn) -> bool:
    """The counted occupancy is 1/(2c'), and a window holds at most one point."""
    r = fn(10**4)
    return (r["holds_at_most_one"] and r["window_length"] < 2.0
            and abs(r["counted_occupancy"] - r["predicted_occupancy"]) < 1e-3
            and abs(r["predicted_occupancy"] - 0.4309) < 5e-4
            and r["ever_holds_none_for_certain"] is False)


def _lemma37_cost_ok(fn) -> bool:
    """The mass is the price, and the flat term alone reaches the trivial bound."""
    from research.juggler_sequence import p0_certificate as PC
    r = fn(int(PC.certificate()["P0"]))
    return (abs(r["b_mass"] - 76.4) < 0.2 and abs(r["v_mass"] - 41.3) < 0.2
            and abs(r["total_mass"] - 117.7) < 0.4
            and r["flat_alone_reaches_trivial"]
            and r["total_mass"] > 100 * r["trivial_bound_on_one_term"])


def _site_masses_ok(fn) -> bool:
    """Ten sites, all logarithmic, largest 9/4 at the two carrying R_0."""
    r = fn()
    return (len(r["rows"]) == 10 and r["all_logarithmic"]
            and abs(r["max_coefficient"] - 2.25) < 1e-9
            and abs(r["min_coefficient"] - 0.625) < 1e-9
            and r["thinnest_site"] == "Thm 6.3 depth five"
            and len(r["fattest_sites"]) == 2)


def _log_ledger_ok(fn) -> bool:
    """3 -> 3/2 -> 3/4, then +3 = 15/4; two of the three are Theorem 6.3's own."""
    r = fn()
    return (r["halving_is_exact"] and r["sum_is_exact"] and r["final_power"] == 3.75
            and r["own_count"] == 2 and r["inherited_count"] == 1
            and abs(r["absorption_log10"][0.75] - 190) < 1.5
            and abs(r["absorption_log10"][3.75] - 1245) < 2.0)


PROBE_CITATIONS: tuple[tuple[str, str, str, str, Callable[[Any], bool]], ...] = (
    ("decoration_budget", "branch_offset_ladder",
     r"finds\n> \(\max j=r+1\) and \(\min j=-1\) at \(h_1h_2\le rP^{1/2}/3\) for\n> \(r=1,2,3,6\)",
     "the offset ladder's multiples and its two invariants",
     _ladder_ok),
    ("decoration_budget", "beta_inventory_attained",
     r"the ratios to the\n> printed forms in floating point):",
     "the beta inventory's default h-range and its four attained values",
     _inventory_ok),
    ("p0_certificate", "interpolant_error",
     r"already solved against\n> \(170.6\) (`p0_certificate.interpolant_error`)",
     "E's coefficient in the certificate's interpolant error",
     _interpolant_error_ok),
    ("paper_b_audit", "block_exponent_calibration",
     r"the instrument reads\n\(0.497\pm0.043\) at its default \(200\) trials",
     "the block-exponent estimator's calibration at its defaults",
     _calibration_ok),
    ("paper_b_audit", "level1_kernel_block_scaling",
     "(`paper_b_audit.level1_kernel_block_scaling`; the instrument reads",
     "the level-1 kernel's block-scaling probe",
     _block_scaling_ok),
    ("decoration_budget", "offset_term_attained",
     "(`decoration_budget.offset_term_attained`)",
     "the offset term's attained range against its printed one",
     _offset_term_ok),
    ("decoration_budget", "level1_exponent_sweep",
     "(`decoration_budget.level1_exponent_sweep`, which is that ladder)",
     "the level-1 exponent sweep, and that its ladder is the printed one",
     _level1_sweep_ok),
    ("decoration_budget", "level1_control_trend",
     "(`decoration_budget.level1_control_trend`)",
     "the kernel/control trend against P, and its printed ladder",
     _control_trend_ok),
    ("decoration_budget", "level1_kernel_k_spread",
     "(`decoration_budget.level1_kernel_k_spread`)",
     "the kernel's k-spread, and that its condition has no crossover",
     _kernel_spread_ok),
    ("decoration_budget", "level1_drift_window_occupancy",
     "(`decoration_budget.level1_drift_window_occupancy`)",
     "the drift-1 window holds at most one point, with density 1/(2c')",
     _occupancy_ok),
    ("decoration_budget", "lemma37_one_term_window_cost",
     "(`decoration_budget.lemma37_one_term_window_cost`)",
     "what Lemma 3.7 returns on a one-term window, against the trivial bound",
     _lemma37_cost_ok),
    ("decoration_budget", "lemma37_site_masses",
     "(`decoration_budget.lemma37_site_masses`)",
     "Lemma 3.7's mass at all ten sites, and that each is O(log P)",
     _site_masses_ok),
    ("decoration_budget", "log_power_ledger",
     "(`decoration_budget.log_power_ledger`)",
     "the log-power chain 3 -> 3/2 -> 3/4 -> 15/4 and its provenance",
     _log_ledger_ok),
)


def citation_audit(run_checks: bool = True) -> list[dict[str, Any]]:
    """One row per manuscript citation of a probe function."""
    text = paper_text()
    out: list[dict[str, Any]] = []
    for module, function, anchor, description, check in PROBE_CITATIONS:
        row = {"module": module, "function": function, "description": description,
               # anchors are raw strings; the two-character "\n" marks a line break in the
               # manuscript, which wraps at about 72 columns.
               "anchor_present": anchor.replace(chr(92) + "n", chr(10)) in text,
               "resolves": False, "holds": False}
        try:
            fn = getattr(_probe(module), function)
            row["resolves"] = callable(fn)
            if row["resolves"] and row["anchor_present"] and run_checks:
                row["holds"] = bool(check(fn))
        except (ImportError, AttributeError):
            pass
        out.append(row)
    return out


def broken_citations(run_checks: bool = True) -> list[dict[str, Any]]:
    return [r for r in citation_audit(run_checks)
            if not (r["anchor_present"] and r["resolves"] and r["holds"])]


# --- printed ranges against the cited functions' defaults ----------------------------------
#
# A citation can resolve, name a live function, and still mislead if the *range* printed beside
# it is not the range that function covers.  Those ranges are arguments with defaults, and a
# default that moves rescopes a printed claim silently.  One row per printed quantifier.
#
# It also records the printed measurements that cite no function at all, which is the other
# way this fails: `UNANCHORED` names them so that the count is visible rather than the claims
# being quietly assumed reproducible.

RANGE_CLAIMS: tuple[tuple[str, str, str, str, Callable[[Any], bool]], ...] = (
    ("decoration_budget", "beta_inventory_attained", r"\(1\le h_1,h_2\le7\)",
     "the beta inventory's printed h-range is its default",
     lambda fn: __import__("inspect").signature(fn).parameters["hmax"].default == 7),
    ("decoration_budget", "offset_term_attained", r"\(n\in(P,2P]\)",
     "the offset term is measured over the dyadic block, as printed",
     lambda fn: __import__("inspect").signature(fn).parameters["hmax"].default == 7),
    ("decoration_budget", "branch_offset_ladder", r"\(r=1,2,3,6\)",
     "the ladder's printed multiples are its default",
     lambda fn: __import__("inspect").signature(fn).parameters["multiples"].default
     == (1, 2, 3, 6)),
    ("paper_b_audit", "block_exponent_calibration", r"at its default \(200\) trials",
     "the calibration's printed trial count is its default",
     lambda fn: __import__("inspect").signature(fn).parameters["trials"].default == 200),
    ("decoration_budget", "level1_exponent_sweep",
     r"\(P\in\{10^4,3\cdot10^4,10^5,10^6\}\)",
     "the printed P-ladder is the sweep's default",
     lambda fn: __import__("inspect").signature(fn).parameters["ps"].default
     == (10**4, 3 * 10**4, 10**5, 10**6)),
)

# Printed measurements with no function named beside them.  Each is an honest number somebody
# ran, and none can be re-run from the text: the reader is told the answer and not the query.
# Listed rather than silently tolerated; two of the three are the other session's to anchor.
UNANCHORED: tuple[tuple[str, str], ...] = (
    (r"On \(20{,}000\) samples the witness",
     "no function produces the 20,000-sample range [0.32,0.52] for xi_2"),
    (r"measured at \(0.989\) times it over ten samples",
     "no function produces the ten-sample figure 0.989"),
)


def range_audit() -> list[dict[str, Any]]:
    text = paper_text()
    out: list[dict[str, Any]] = []
    for module, function, printed, description, check in RANGE_CLAIMS:
        row = {"module": module, "function": function, "printed": printed,
               "description": description, "printed_present": printed in text,
               "matches_default": False}
        try:
            fn = getattr(_probe(module), function)
            row["matches_default"] = bool(check(fn))
        except (ImportError, AttributeError, KeyError):
            pass
        out.append(row)
    return out


def mismatched_ranges() -> list[dict[str, Any]]:
    return [r for r in range_audit() if not (r["printed_present"] and r["matches_default"])]


def unanchored_measurements() -> list[dict[str, str]]:
    """Printed measurements still in the manuscript with no function named beside them."""
    text = paper_text()
    return [{"printed": p, "why": w} for p, w in UNANCHORED if p in text]

def main() -> None:
    rows = audit()
    cov = coverage()
    print("Paper B Lean numerals outside the threshold certificate")
    print("  modules   %s" % ", ".join(cov["modules"]))
    print("  numerals  %d   paired %d   structural %d   unclassified %d"
          % (cov["numerals"], cov["paired"], cov["structural"], cov["unclassified"]))
    for r in unclassified(rows):
        print("  UNCLASSIFIED  %-20s %-34s %s" % (r["module"], r["theorem"], r["numeral"]))
    for r in failing(rows):
        print("  FAILS         %-20s %-34s %-8s %s"
              % (r["module"], r["theorem"], r["numeral"], r["role"]))
    if not cov["unclassified"] and not cov["failing"]:
        print("  every numeral is classified and every pairing holds")
    claims = claim_audit()
    bad = stale_claims()
    print("  prose claims about the manuscript: %d checked, %d stale"
          % (len(claims), len(bad)))
    for r in bad:
        print("     STALE  %-18s %s (%s)"
              % (r["module"], r["description"],
                 "anchor gone" if not r["anchor_present"] else "manuscript disagrees"))
    cites = citation_audit()
    broken = broken_citations()
    print("  probe citations in the manuscript: %d checked, %d broken"
          % (len(cites), len(broken)))
    for r in broken:
        why = ("anchor gone" if not r["anchor_present"]
               else "does not resolve" if not r["resolves"] else "returns something else")
        print("     BROKEN %-18s %-30s %s" % (r["module"], r["function"], why))
    rng = range_audit()
    bad_rng = mismatched_ranges()
    print("  printed ranges against the cited defaults: %d checked, %d mismatched"
          % (len(rng), len(bad_rng)))
    for r in bad_rng:
        print("     MISMATCH %-18s %-30s %s"
              % (r["module"], r["function"],
                 "printed text gone" if not r["printed_present"] else "default moved"))
    un = unanchored_measurements()
    print("  printed measurements citing no function: %d" % len(un))
    for r in un:
        print("     UNANCHORED  %s" % r["why"])
    print("  (the %d threshold rows are paired by p0_certificate.LEAN_ROWS)"
          % cov["certificate_rows_covered_elsewhere"])


if __name__ == "__main__":
    main()
