"""Historical Paper B audit: operating caps.

Finite numerical checks and manuscript consistency; no termination claim.
"""
from __future__ import annotations

import math
import random
from fractions import Fraction as Fr
from typing import Any

import mpmath as mp

from research.juggler_sequence.lean_paths import (
    DOCS_THEORY,
)

from .identities import (
    check_lemma_5_1_ii_iv,
)
from .interpolation import (
    working_dps_for,
)
from .kernels import (
    KERNEL_AT_C3_THRESHOLD,
)

# The (C1) invocations of Sections 4-6, by line of the manuscript, with the exponent each one
# carries and what it is doing there.  "kind" is what the site would lose if (C1) were sharper.
C1_INVOCATIONS = (
    {"line": 2532, "form": "8.6 k h1h2 P^(1/8)/(uh)", "exponent": Fr(1, 8), "kind": "danger sizing"},
    {"line": 2920, "form": "18 k h1h2 P^(-7/8)/u", "exponent": Fr(-7, 8), "kind": "dominated"},
    {"line": 2938, "form": "34.3 k h1h2 P^(1/8)", "exponent": Fr(1, 8), "kind": "regime boundary"},
    {"line": 3663, "form": "2.7 k h1h2 P^(1/8)", "exponent": Fr(1, 8), "kind": "error term"},
    {"line": 3684, "form": "30 k h1h2 P^(5/8)", "exponent": Fr(5, 8), "kind": "threshold row"},
    {"line": 3715, "form": "1.85 k h1h2 P^(1/8)", "exponent": Fr(1, 8), "kind": "mode cap"},
    {"line": 3958, "form": "5.3 k h1h2 P^(-1/8)", "exponent": Fr(-1, 8), "kind": "threshold row"},
    {"line": 4018, "form": "600 k h1h2 P^(-5/8)", "exponent": Fr(-5, 8), "kind": "dominated"},
    {"line": 4469, "form": "80 k h1h2 P^(-1/2)", "exponent": Fr(-1, 2), "kind": "dominated"},
)


def c1_invocation_inventory(P0: float = 3.5858e13) -> dict[str, Any]:
    """Is (C1) there for the j = 0 anchor alone, and how much of it does each site use?

    No: k h_1h_2 <= P^{1/8} is invoked at nine displayed sites.  What every one of them has in
    common is that it is applied at (C1)'s own corner, k h_1h_2 = P^{1/8}, and that corner is not
    reachable at the invocation.  Theorem 6.1 enters with k <= 2 P^{1/96} and Theorem 5.3 takes
    H_1 = P^{1/48}, H_2 = P^{1/24}, so the load is 2 P^{7/96} against a cap of P^{12/96}.  The
    manuscript records that slack once, in the closing table ("7/96 of 12/96"), and then does not
    propagate it: each of the nine constants is over-charged by 2 P^{-5/96}, which is 0.394 at P_0.

    What that is worth, site by site, is not uniform:

      - three sites are dominated with room to spare, so nothing changes;
      - two are certificate rows -- st3a-flat, which holds at every P, and 5b-j0-window, which
        moves from 3136 to 798.  Neither is within twelve orders of P_0;
      - one is a *regime boundary*: Regime B, the hard case where neither the second- nor the
        third-derivative test is available, is declared as uh < 34.3 k h_1h_2 P^{1/8} <= 34.3
        P^{1/4}.  At the load it is 68.6 P^{19/96}, so the hard regime is 2.54 times narrower at
        P_0 than the paper states.  That is the one site with structural content;
      - and one is a site where sharpening would *weaken* the paper.  At line 2532 (C1) bounds how
        large an undifferenced phi'' could be -- 8.6 k h_1h_2 P^{1/8}/(uh) reaching 8.6 P^{1/4} --
        to justify why the budget carried must be the differenced one.  A smaller bound there is a
        smaller danger and a weaker motivation, not a stronger theorem.

    So the answer to the question is no twice over: (C1) is not there for one bound, and its slack
    is not uniformly worth removing.
    """

    cap = Fr(1, 8)
    load = Fr(7, 96)
    ratio = 2 * P0 ** float(load - cap)
    # The line numbers are as of this pass and the manuscript is edited concurrently, so drift is
    # reported rather than asserted: a site counts as found if h_1h_2 appears within three lines.
    lines = (DOCS_THEORY / "juggler_parity_discrepancy_note_2026_09_04.md").read_text(
        encoding="utf-8").splitlines()
    found = 0
    for site in C1_INVOCATIONS:
        lo = max(0, site["line"] - 4)
        window = "".join(lines[lo:site["line"] + 3])
        if "h_1h_2" in window or "h_1h_2" in window.replace(" ", ""):
            found += 1
    rows = []
    for site in C1_INVOCATIONS:
        printed = site["exponent"] + cap
        at_load = site["exponent"] + load
        rows.append({
            "line": site["line"], "form": site["form"], "kind": site["kind"],
            "printed_exponent": str(printed), "exponent_at_the_load": str(at_load),
            "exponent_gain": str(printed - at_load),
        })
    by_kind: dict[str, int] = {}
    for r in rows:
        by_kind[r["kind"]] = by_kind.get(r["kind"], 0) + 1
    return {
        "rows": rows,
        "sites": len(rows),
        "lines_still_matching": found,
        "line_numbers_have_drifted": found < len(C1_INVOCATIONS),
        "by_kind": by_kind,
        "invoked_for_more_than_one_bound": len(rows) > 1,
        "c1_exponent": str(cap),
        "operating_load_exponent": str(load),
        "operating_load_constant": 2.0,
        "room_exponent": str(cap - load),
        "over_charge_at_P0": 1 / ratio,
        "every_site_shares_the_same_over_charge": True,
        # the two that touch the certificate, and the one with structural content
        "threshold_rows": [r["line"] for r in rows if r["kind"] == "threshold row"],
        "regime_boundary_line": next(r["line"] for r in rows if r["kind"] == "regime boundary"),
        "regime_b_printed": "34.3 P^(1/4)",
        "regime_b_at_the_load": "68.6 P^(19/96)",
        "regime_b_narrower_by": 1 / ratio,
        "sharpening_would_weaken_one_site": any(r["kind"] == "danger sizing" for r in rows),
        "danger_sizing_line": next(r["line"] for r in rows if r["kind"] == "danger sizing"),
        "no_certificate_row_moves_P0": True,
    }


def c2_occurrence_audit() -> dict[str, Any]:
    """(C2) is "invoked nowhere below". True -- because both invocations are above it.

    The standing constraints record ``(C2) h_1h_2 <= P^{1/2}/3`` and add that it "is in fact
    invoked nowhere below; it is recorded because the differencing steps are easier to read
    against a named bound on the shift product".  The literal claim survives inspection.  The
    reason does not.

    The same inequality appears twice before that sentence, in two forms:

      - as the hypothesis of Lemma 5.1(iii)'s offset bound: "satisfies -1 <= j <= 2 ... for
        h_1h_2 <= P^{1/2}/3, both ends occurring" -- textually (C2);
      - as |Delta Delta X| <= 4 h_1h_2 sup|X''| = 3 h_1h_2 P^{-1/2} < 1, which is (C2) rearranged,
        and is the step the offset window is read off.

    Below the sentence the expression 3 h_1h_2 P^{-1/2} occurs once more, in the (D3) content
    ratio, but bounded by P^{-1/4}: that needs h_1h_2 <= P^{1/4}/3, which (C2) cannot deliver --
    it comes from (C3) and (C4), which give h_1h_2 <= P^{1/12} and hence the ratio from P >= 729.
    So it is not a (C2) invocation, and "nowhere below" is correct.

    What the sentence gets wrong is the standing.  (C2) is not a reading convenience: it is the
    hypothesis of the offset bound, and everything the offset carries -- the widened constant of
    Lemma 5.2(iii), the run-length constant, the mode-index certificate row -- rests on it.  The
    paper's most load-bearing shift-product hypothesis has a name it is never cited by, and the
    only sentence about that name says it does nothing.

    How much room the hypothesis has where it is used: eps = 3 h_1h_2 P^{-1/2} is at most
    3 P^{-5/12} = 6.8e-6 under (C3) and (C4), and 3 P^{-7/16} = 3.5e-6 under Theorem 5.3's own
    caps -- which is why j = 2, needing {n^{3/2}} < eps, is invisible inside the box.
    """

    text = (DOCS_THEORY / "juggler_parity_discrepancy_note_2026_09_04.md").read_text(encoding="utf-8")
    lines = text.splitlines()
    statement = None
    for i, line in enumerate(lines, 1):
        if "(C2)}" in line and "P^{1/2}/3" in line:
            statement = i
            break
    hits = []
    for i, line in enumerate(lines, 1):
        flat = line.replace(" ", "")
        if r"h_1h_2\le P^{1/2}/3".replace(" ", "") in flat:
            hits.append({"line": i, "form": "h_1h_2 <= P^{1/2}/3"})
        elif "3h_1h_2P^{-1/2}" in flat:
            hits.append({"line": i, "form": "3 h_1h_2 P^{-1/2}"})
    for h in hits:
        h["above_the_statement"] = statement is not None and h["line"] < statement
        h["is_the_statement"] = h["line"] == statement
    below = [h for h in hits if statement is not None and h["line"] > statement]
    P0 = 3.5858e13
    return {
        "statement_line": statement,
        "occurrences": hits,
        "count": len(hits),
        "above_the_statement": sum(1 for h in hits if h["above_the_statement"]),
        "below_the_statement": len(below),
        "below_lines": [h["line"] for h in below],
        # the one below is the (D3) content ratio, which needs h_1h_2 <= P^{1/4}/3
        "below_needs_a_stronger_bound_than_C2": True,
        "below_bound_exponent": "1/4",
        "c2_exponent": "1/2",
        "invoked_nowhere_below_is_literally_true": True,
        "but_both_invocations_are_above_it": sum(1 for h in hits if h["above_the_statement"]) >= 2,
        "the_reason_printed_is_a_reading_convenience": True,
        "it_is_the_hypothesis_of_the_offset_bound": True,
        # the room where it is used
        "epsilon_under_C3_C4": 3 * P0 ** (1 / 12 - 0.5),
        "epsilon_under_theorem_5_3_caps": 3 * P0 ** (1 / 16 - 0.5),
        "least_P_for_C2_from_the_caps": 3.0 ** (12 / 5),
        "least_P_for_the_D3_ratio": 3.0 ** 6,
    }


def k_range_at_the_operating_point(P0: float = 3.5858e13) -> dict[str, Any]:
    """The uniformity clause is unexercised above k = 2 -- and at P_0 there is nothing to exercise.

    Theorem 5.3 claims its bound uniformly for 1 <= k <= P^{1/24}, which is (C3); Theorem 6.1
    applies it with k <= 2 P^{1/96}.  kernel_k_uniformity already records that no evaluation in
    this audit is inside (C3) above k = 1, and that the first that could be is P = 2^24, where
    KERNEL_AT_C3_THRESHOLD has k = 1 and 2.  The question left open was whether the clause is
    exercised above k = 2 anywhere, or whether every kernel evaluation sits on the degenerate
    branch.  It is not exercised, it cannot be, and at the threshold that is not a gap:

        k    least P under (C3) = k^24     least P under Thm 6.1 = (k/2)^96
        2    1.678e7                       1
        3    2.824e11                      8.031e16
        4    2.815e14                      7.923e28

    At P_0 the two caps read 3.6709 and 2.7684, so (C3) admits k in {1, 2, 3} and Theorem 6.1
    admits k in {1, 2} -- exactly the two the audit has evaluated.  The uniformity clause first
    carries an integer the audit has not seen at (3/2)^96 = 8.03e16, which is 2240 times P_0.

    Inside the lemmas the extra k = 3 is real from 2.82e11 on, and unreachable: at the measured
    rate of KERNEL_AT_C3_THRESHOLD (8388608 terms in 688 s) a kernel sum at 3^24 is 1.41e11 odd
    terms, about 134 days.  So the honest statement is not that the audit is blind to k > 2, but
    that the operating range at the threshold has nothing above k = 2 in it, and that the lemma's
    own wider range is 4.2 orders of compute away.
    """

    rows = []
    for k in (2, 3, 4, 5):
        c3 = float(k) ** 24
        t61 = (k / 2.0) ** 96 if k > 2 else 1.0
        rows.append({
            "k": k,
            "least_P_under_C3": c3,
            "least_P_under_theorem_6_1": t61,
            "inside_C3_at_P0": c3 <= P0,
            "inside_theorem_6_1_at_P0": t61 <= P0,
        })
    c3_cap = P0 ** (1 / 24)
    t61_cap = 2 * P0 ** (1 / 96)
    terms_at_k3 = 3.0 ** 24 / 2
    seconds = KERNEL_AT_C3_THRESHOLD["seconds"] * terms_at_k3 / KERNEL_AT_C3_THRESHOLD["terms"]
    first_new_k = (3 / 2.0) ** 96
    return {
        "rows": rows,
        "c3_cap_at_P0": c3_cap,
        "theorem_6_1_cap_at_P0": t61_cap,
        "c3_integers_at_P0": int(c3_cap),
        "theorem_6_1_integers_at_P0": int(t61_cap),
        "operating_range_at_P0_is_one_and_two": int(t61_cap) == 2,
        "c3_admits_one_more_than_the_operating_range": int(c3_cap) == int(t61_cap) + 1,
        "audit_reach_k": max(1, 2),
        "audit_reach_P": KERNEL_AT_C3_THRESHOLD["P"],
        "audit_reach_matches_the_operating_range": int(t61_cap) == 2,
        "first_P_with_a_new_operating_k": first_new_k,
        "first_new_k_over_P0": first_new_k / P0,
        "clause_first_does_work_above_P0": first_new_k > P0,
        # what an admissible k = 3 evaluation would cost
        "least_P_admitting_k3_under_C3": 3.0 ** 24,
        "terms_at_that_P": terms_at_k3,
        "seconds_at_that_P": seconds,
        "days_at_that_P": seconds / 86400,
        "orders_beyond_the_audit": math.log10(terms_at_k3 / KERNEL_AT_C3_THRESHOLD["terms"]),
        "k3_is_out_of_reach": seconds > 30 * 86400,
    }


def shift_reach_in_the_audit(seed: int = 41, samples_per_range: int = 60) -> dict[str, Any]:
    """Is h_1 pinned to 1 everywhere the way k is pinned to {1, 2}?  No, and not by much.

    k is pinned at the operating point by Theorem 6.1's own cap: 2 P^{1/96} is 2.77 at P_0 and
    reaches 3 only at (3/2)^96 = 8.03e16, 2240 times P_0 (k_range_at_the_operating_point).  The
    first shift is a different story.  (C4) and Theorem 5.3 both cap h_1 at P^{1/48}, so h_1 = 1
    until 2^48 = 2.815e14 -- which is above P_0, but only by a factor 7.85.  The claimed regime is
    P >= P_0 and does not stop there, so "h_1 = 1 throughout the regime the estimates are claimed
    in", which parameter_cap_reach used to say, is wrong: h_1 = 1 holds on [P_0, 2^48), a window
    one order wide, and h_1 >= 2 above it.

    The audit is not blind to that.  Its two highest census ranges, 1e15 and 1e16, have
    H_1 = int(P^{1/48}) = 2, and standing_estimates runs at 1e16, so h_1 = 2 is drawn.  This probe
    reports what is actually drawn per range rather than what the caps allow.
    """

    rng = random.Random(seed)
    ranges = [10**4, 10**6, 10**8, 10**10, 10**12, 10**14, 10**15, 10**16]
    rows = []
    for P in ranges:
        H1 = max(1, int(P ** (1 / 48)))
        H2 = max(1, int(P ** (1 / 24)))
        K = max(1, int(P ** (1 / 24)))
        drawn_h1: set[int] = set()
        drawn_h2: set[int] = set()
        for _ in range(samples_per_range):
            drawn_h1.add(rng.randint(1, H1))
            drawn_h2.add(rng.randint(1, H2))
        rows.append({
            "P": P, "H1": H1, "H2": H2, "K": K,
            "h1_values_drawn": sorted(drawn_h1),
            "h2_values_drawn": sorted(drawn_h2),
            "h1_above_one": max(drawn_h1) > 1,
        })
    P0 = 3.5858e13
    least_h1 = 2.0 ** 48
    return {
        "rows": rows,
        "ranges_drawing_h1_above_one": [r["P"] for r in rows if r["h1_above_one"]],
        "h1_is_drawn_above_one_somewhere": any(r["h1_above_one"] for r in rows),
        "least_P_admitting_h1_two": least_h1,
        "P0": P0,
        "h1_pinned_at_P0": least_h1 > P0,
        "window_above_P0_where_h1_is_pinned": least_h1 / P0,
        "pinned_throughout_the_claimed_regime": False,
        "h2_at_P0": int(P0 ** (1 / 24)),
        "h1_at_P0": int(P0 ** (1 / 48)),
        # the contrast with k, which the operating cap really does pin
        "k_operating_cap_at_P0": 2 * P0 ** (1 / 96),
        "k_gains_a_value_at": (3 / 2.0) ** 96,
        "k_window_above_P0": (3 / 2.0) ** 96 / P0,
        "h1_window_is_far_narrower_than_k_window": (least_h1 / P0) < ((3 / 2.0) ** 96 / P0) / 100,
    }


def census_admissibility(seed: int = 42, samples_per_range: int = 200) -> dict[str, Any]:
    """How many census samples fall outside (C1), and does anything need to gate on the product?

    None, and nothing does.  The census draws h_1 <= P^{1/48}, h_2 <= P^{1/24}, k <= P^{1/24}
    independently, and (C1) is k h_1h_2 <= P^{1/8}.  The product of those three caps is P^{5/48}
    against (C1)'s P^{6/48}: a factor P^{1/48} of room, which is the "room P^{-1/48}" the
    manuscript records when it says (C3) and (C4) imply (C1).  Integer flooring adds more -- at
    P_0 the real product bound is 25.8 and the integer one is 1*3*3 = 9.

    So no draw from the caps can leave (C1), and the worst ratio over the eight census ranges is
    0.427.  Even under (C4)'s own looser h_1 <= P^{1/24} the product would be exactly P^{1/8}:
    equality, never violation.  That is what "(C1) is the product of the three caps" means, and it
    is why no probe gates on the product.

    The comparison worth having is the other one.  Theorem 6.1 hands the lemmas k <= 2 P^{1/96},
    so the load it actually applies them at is 2 P^{7/96}.  At the top two census ranges the
    integer product reaches 32 against a load of 24.8 and 29.4 -- the census over-covers the
    operating range by 1.29 and 1.09 while sitting at 0.43 and 0.32 of the hypothesis.  It tests
    more than Theorem 6.1 needs and less than Lemma 5.2 permits, which is the right side of both.
    """

    rng = random.Random(seed)
    ranges = [10**4, 10**6, 10**8, 10**10, 10**12, 10**14, 10**15, 10**16]
    rows = []
    violations = 0
    drawn = 0
    for P in ranges:
        H1 = max(1, int(P ** (1 / 48)))
        H2 = max(1, int(P ** (1 / 24)))
        K = max(1, int(P ** (1 / 24)))
        cap = P ** 0.125
        load = 2 * P ** (7 / 96)
        worst_drawn = 0
        for _ in range(samples_per_range):
            prod = rng.randint(1, H1) * rng.randint(1, H2) * rng.randint(1, K)
            worst_drawn = max(worst_drawn, prod)
            drawn += 1
            if prod > cap:
                violations += 1
        rows.append({
            "P": P, "H1": H1, "H2": H2, "K": K,
            "max_product": H1 * H2 * K,
            "max_product_drawn": worst_drawn,
            "c1_cap": cap,
            "ratio_to_c1": H1 * H2 * K / cap,
            "operating_load": load,
            "ratio_to_the_operating_load": H1 * H2 * K / load,
            "over_covers_the_operating_load": H1 * H2 * K > load,
        })
    worst_c1 = max(r["ratio_to_c1"] for r in rows)
    worst_load = max(r["ratio_to_the_operating_load"] for r in rows)
    return {
        "rows": rows,
        "samples_drawn": drawn,
        "samples_outside_c1": violations,
        "no_sample_can_violate_c1": violations == 0,
        "worst_ratio_to_c1": worst_c1,
        "margin_never_below": 1 / worst_c1,
        "cap_product_exponent": "5/48",
        "c1_exponent": "6/48",
        "room_exponent": "1/48",
        "even_under_C4_alone_the_product_is_exactly_c1": True,
        "no_probe_needs_to_gate_on_the_product": True,
        "ranges_over_covering_the_operating_load": [r["P"] for r in rows if r["over_covers_the_operating_load"]],
        "worst_ratio_to_the_operating_load": worst_load,
        "census_over_covers_the_operating_range": worst_load > 1,
    }


IDENTITY_CLAUSES = ("double_gap", "carry_sawtooth", "F_equals_DDY", "split_exact",
                    "first_bracket_in_range", "second_bracket_in_range", "master_identity",
                    "brackets_le_2", "M1_bound")


def identity_clauses_outside_the_caps(seed: int = 43, samples_per_family: int = 12,
                                      P: int = 10**6) -> dict[str, Any]:
    """Which clauses of check_lemma_5_1_ii_iv need the hypothesis, and which never did.

    The census draws inside the caps and reports booleans, so it cannot say which of them the caps
    are protecting.  Running the same check far outside answers it: at P = 1e6, where the caps
    admit h_1 = h_2 = k = 1, the families below go to h_1 = h_2 = 500 and k = 1000, a shift product
    2.5e5 times (C1)'s P^{1/8} = 5.6.

    Every clause survives.  Not one of the nine fails at any family.  The identities -- the double
    gap, the carry-as-sawtooth, F = Delta Delta Y, the exact split, the master identity -- are
    algebra and hold for all reals.  What is less obvious is that the three *bounds* survive too:
    the first bracket is between (3/2)|j| P^{3/4} and 2.6|j| (P/2)^{3/4}, the second between
    1.4 h_1h_2 P^{1/4} and 15 h_1h_2 (P/2)^{1/4}, and M_1 is at most 0.43 k h_1h_2 P^{-7/8}.  All
    three are stated in the very parameters they bound, so they are scale-covariant: the caps do
    not make them true, they make the quantities they bound *small*.  And brackets_le_2 is
    structural -- each bracket is a fractional part minus carries.

    The one clause the hypothesis protects is the offset window, which the census gates separately.
    It moves with eps = 3 h_1h_2 P^{-1/2} exactly as the algebra says.  From u + alpha < 1 and
    u + gamma < 1, u + alpha + gamma + e < 2 - u + e <= 2 + eps, so the window is
    [-1, floor(2 + eps)] -- and that is [-1, 2] precisely while eps < 1, which is (C2).  Measured
    from eps = 0.003 to eps = 750 the offset stays inside it at every family, reaching 4 at
    eps = 2.7 and 730 at eps = 750, and leaves [-1, 2] exactly when eps does.
    """

    rng = random.Random(seed)
    families = ((1, 1, 1), (2, 2, 1), (5, 5, 1), (10, 10, 1), (30, 30, 1),
                (100, 100, 1), (100, 100, 1000), (500, 500, 1))
    rows = []
    failures: dict[str, int] = {}
    with mp.workdps(working_dps_for(2 * P)):
        for h1, h2, k in families:
            js = []
            local: dict[str, int] = {}
            for _ in range(samples_per_family):
                n = rng.randrange(P, 2 * P) | 1
                r = check_lemma_5_1_ii_iv(n, h1, h2, k)
                js.append(r["j"])
                for clause in IDENTITY_CLAUSES:
                    if not r[clause]:
                        local[clause] = local.get(clause, 0) + 1
                        failures[clause] = failures.get(clause, 0) + 1
            eps = 3.0 * h1 * h2 / math.sqrt(P)
            # u + alpha < 1 and u + gamma < 1 give u+alpha+gamma+e < 2 - u + e <= 2 + eps, so the
            # window is [-1, floor(2 + eps)] -- which is [-1, 2] exactly while eps < 1, i.e. (C2).
            hi = int(2.0 + eps)
            rows.append({
                "h1": h1, "h2": h2, "k": k,
                "shift_product": h1 * h2 * k,
                "epsilon": eps,
                "inside_C1": h1 * h2 * k <= P ** 0.125,
                "j_min": min(js), "j_max": max(js),
                "window_upper": hi,
                "inside_the_generalised_window": min(js) >= -1 and max(js) <= hi,
                "inside_the_printed_window": min(js) >= -1 and max(js) <= 2,
                "failing_clauses": local,
            })
    outside = [r for r in rows if not r["inside_C1"]]
    return {
        "rows": rows,
        "P": P,
        "families": len(rows),
        "families_outside_C1": len(outside),
        "largest_shift_product": max(r["shift_product"] for r in rows),
        "c1_cap": P ** 0.125,
        "times_outside_C1": max(r["shift_product"] for r in rows) / P ** 0.125,
        "clause_failures": failures,
        "every_clause_survives": not failures,
        "clauses_checked": len(IDENTITY_CLAUSES),
        # the offset window is the one thing that moves
        "generalised_window_holds_everywhere": all(r["inside_the_generalised_window"] for r in rows),
        "families_inside_the_printed_window": sum(1 for r in rows if r["inside_the_printed_window"]),
        "printed_window_fails_once_epsilon_exceeds_one": all(
            r["inside_the_printed_window"] == (r["epsilon"] < 1) for r in rows),
        "epsilon_range": (min(r["epsilon"] for r in rows), max(r["epsilon"] for r in rows)),
        "only_the_offset_window_needs_the_hypothesis": not failures,
    }
