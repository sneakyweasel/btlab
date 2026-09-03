"""Multi-step word-parity census on odd Juggler starts.

Phase-0 falsifier for the two-step parity discrepancy branch. Exact
integer counting only: does the joint parity word of the first four
word letters on odd starts converge to the product densities,
and with what empirical discrepancy exponent?

Not a Research Engine control-layer experiment. Not a frequency
theorem, not a predictive-state claim (theta bins and residue states
stay REFUTED/CLOSE), and not a termination theorem. The census gated
the depth-2 analytic lemma; that lemma is now proved, and the depth-4
extension (triple parity discrepancy, OOEE density N/16, certified
four-step descent class 13/16) is proved as well (ledger rows
J-nested-parity-linearization, J-nested-parity-discrepancy,
J-fourth-letter-linearization, J-triple-parity-discrepancy,
J-four-step-descent-density; proofs in
docs/research/juggler_two_step_parity_lemma.md). This module also
hosts the exact validators used by both review passes.
"""

from __future__ import annotations

import json
from math import floor, isqrt, log, sqrt
from pathlib import Path
from typing import Any

REPO_ROOT = Path(__file__).resolve().parents[3]
JSON_PATH = REPO_ROOT / "docs" / "research" / "juggler_two_step_parity.json"
DOC_PATH = REPO_ROOT / "docs" / "research" / "juggler_two_step_parity.md"

N_MAX = 10_000_000
DEPTH = 4
COARSE_GRID = (
    10_000,
    100_000,
    1_000_000,
    *(1 << k for k in range(14, 24)),
    N_MAX,
)
ENVELOPE_RATIO = 1.06

WORDS4 = tuple(
    "O" + "".join(w)
    for w in (
        (a, b, c)
        for a in "EO"
        for b in "EO"
        for c in "EO"
    )
)

# The only length-4 contracting continuation of an odd-to-odd start:
# 3^2 < 2^4 forces image^16 <= n^9, hence a four-step certificate.
CONTRACTING_TARGET = "OOEE"

ANTI_OVERCLAIM = {
    "global_termination": False,
    "parity_frequency_theorem": False,
    "predictive_state_claim": False,
    "reopen_landing_theta": False,
    "reopen_2adic_bridge": False,
    # Flipped by the Phase-2 review pass: Theorem C is EXACT — HUMAN
    # PROOF (ledger row J-nested-parity-discrepancy). Ambient counting
    # only; the flags above stay False.
    "depth2_analytic_lemma_proved": True,
    # Flipped by the Phase-3 review pass: Theorem E and Corollary F
    # are EXACT — HUMAN PROOF (rows J-triple-parity-discrepancy,
    # J-four-step-descent-density). Even-branch fourth letter only;
    # the OOO* classes remain open.
    "depth4_even_branch_proved": True,
    # Phase 4: the conditional implication (equidistribution at all
    # depths => density-one descent) is a theorem. No unconditional
    # density-one claim (depth >= 5 equidistribution is open).
    "tier2_analytic_lemma_proved": True,
    "density_one_claimed": False,
    # Phase 5: Proposition L closes the OE-branch third letter, so all
    # depth-3 word classes are proved.
    "depth3_words_proved": True,
    # Phases 8-9: the tier-2 kernel bound (Theorem R, formerly
    # Conjecture O) is EXACT — HUMAN PROOF after the Phase-9
    # adversarial review (row J-kernel-cancellation), and Theorem S
    # closes OOO*: depth-4 equidistribution is complete
    # (row J-depth4-complete).
    "kernel_bound_proved": True,
    # Phase 6: Theorem Q closes the OE** splits (growing layer on the
    # slow variable w).
    "depth4_slow_branch_proved": True,
    # Phase 8 draft, upgraded by the Phase-9 review.
    "kernel_double_differencing_draft": True,
    "depth4_complete_proved": True,
    # Phase 17: Phase-0 falsifiers for the two post-BB theories.
    # OBSERVATION only — pair statistics of the dispersion amplitude
    # are Poissonian and level-3 defects are block-random. Neither
    # theory is proved; Conjecture V stays open and no K3 bound is
    # claimed.
    "dispersion_phase0_alive": True,
    "transport_phase0_alive": True,
    # Phase 18: Proposition CC — the dispersion route cannot complete
    # the depth-5 count (Vaaler weights concentrate at bounded k where
    # family averages are vacuous; the Selberg pair-count route is
    # circular). Dispersion CLOSED as a completion method; its spacing
    # statistics stand as observations.
    "dispersion_count_route_refuted": True,
    # Phase 18: Lemma DD — on blocks of L = P^{1/4} odd steps the
    # level-2 data collapses exactly (O(1) defects) to an affine base
    # plus rotation carries amplified by W ~ P^{3/4}. The transport
    # inductive step (Conjecture EE) is stated on this substrate.
    # No K3 bound, no density move; Conjecture V stays open.
    "transport_substrate_exact": True,
    # Phase 19: Lemma FF — theta_3 and the kernel phase on DD-blocks
    # are explicit polynomials in (mu, s, d, {F}); the product form
    # forces theta_3 precision P^{-27/16}. Census: in-block kernel
    # sums are at the random-phase scale (R ~ Exp(1)) at P = 10^6,
    # 10^8, 10^10, with no gamma-resonance elevation (OBSERVATION).
    # Conjecture EE's cancellation target is empirically comfortable;
    # EE itself and the K3 bound stay open.
    "level3_block_model_exact": True,
    "in_block_cancellation_observed": True,
    # Phase 20: Proposition GG — the intra-block harmonic program is
    # obstructed: the kernel product's Fourier window drifts by
    # kC' ~ P^{11/16} per step (inner sums shorter than one step at
    # every block length), and every algebraic re-form transfers the
    # P^{27/16} amplitude instead of destroying it (floor-splitting,
    # pure-phase identity -> 45/16 W-family, differencing, interval
    # splitting). The intra-block program is PARKED; Conjectures V
    # and EE stay open. The distilled crystal is Conjecture HH: the
    # pure amplitude-product model sum e(A(t){B(t)}) with monomials
    # 1 << A' << A, which cancels empirically (Exp(1) census) but
    # sits outside every toolkit and the PS literature (A' << 1).
    "intra_block_harmonic_parked": True,
    "pure_model_cancellation_observed": True,
    # Phase 21: Lemma II — the shift-averaged second moment of the
    # pure model is L(1 + O(A'^{-1} log L)), two-sided, by direct
    # integration (no characters): square-root cancellation for
    # almost every shift of the fractional argument, for arbitrary
    # x_t. Proposition JJ — the de-randomization to lambda = 0 is
    # obstructed: no second averaging variable exists (amplitude
    # separation forces Delta n = 0; family averages re-enter
    # BB/GG), the concentration inverse is self-similar (arc
    # discrepancy of A{B} mod 1 = the same class at amplitude jA),
    # and the lambda-correlation scale 1/A ~ P^{-27/16} leaves
    # ~P^{27/16} cells no measure argument can pin. HH remains open
    # at lambda = 0; no K3 bound, no density move.
    "pure_model_shift_average_proved": True,
    "hh_derandomization_parked": True,
    # Phase 27 repaired Theorem T / Corollary U: fifth-letter
    # X-modes are Lemma 5.2 Stage-2 r-modes (|u| <= P^{1/4}), not
    # (D1) decorations; OOEO* λ₂ sign is Lemma 3.10-invariant.
    # Laboratory certified density 7/8. Paper B stays at 13/16.
    # OOOO* at depth 5 remains open.
    "depth5_contracting_proved": True,
    # Phase 11: the OOOO* fifth letter is the isolated level-3
    # floor-defect kernel K3 (Lemma V1). No bound, no density move.
    "depth5_kernel_isolated": True,
    "depth5_kernel_bound_proved": False,
    # Phase 12: copying Theorem R to K3 is REFUTED (no v-level
    # b-runs; forced inner linearization produces α = 45/16).
    "scale_invariant_R_extension_refuted": True,
    # Phase 13 drafted OOEOOEE / OOOEOEE and density 57/64; Phase 26
    # withdrew both (Taylor remainder grows like n^{9/32}; Corollary
    # R' never rerun). OOOOEEE still needs K3.
    "depth7_engine_contracting_proved": False,
    # Phase 14: differencing K3 first, then increment-linearizing
    # on X-cell b-runs, is REFUTED (no J-runs on those cells;
    # unfreezing J reintroduces α = 45/16).
    "increment_first_k3_refuted": True,
    # Phase 15: X1-style absorption of the K3 leftover into a
    # freezing integer is REFUTED (X1 lands on floor(F); F = Y
    # has Y'' > 1, and v minus any polynomial in the freezing
    # integers still has run length 1).
    "x1_absorption_k3_refuted": True,
    # Phase 16: the R/X1/increment toolkit cannot bound K3.
    # Conjecture V stays open; the bound program is parked.
    "k3_toolkit_parked": True,
    # Phase 23 drafted the length-8 quartet and density 29/32;
    # Phase 26 withdrew the counting theorems (|E|<1 without E').
    # Phase 40: the envelope rate |E| ≪ n^{-45/128} makes Vaaler
    # discard legal (Lemma AA2); crude |E|<1 discard stays dead.
    # The contraction algebra (3^a < 2^L) and the subcritical
    # eighth-letter coefficient bound remain unconditional.
    # Theorem AA stays CONJECTURE (inherits Theorem X).
    "depth8_engine_quartet_proved": False,
    "depth8_chains_subcritical": True,
    "length8_remainder_discard_proved": True,
    # Phase 28: Theorem R rerun at the single monomial family
    # alpha = 33/32 (intended Corollary R' consumer). The
    # family-for-all-alpha claim stays CONJECTURE.
    "w_family_alpha_33_32_proved": True,
    # Phase 29: the Lemma X1 remainder k E, E ≍ v^{1/8} ≍ n^{9/32},
    # is an engine in the argument n^{9/8} (not a discardable
    # decaying remainder, not a (D3) decoration). Theorem X
    # still needs the passenger rerun.
    "length7_remainder_engine_proved": True,
    # Phase 34: "Theorem T applies as a passenger" is the wrong
    # slot. Sixth-letter θ_p modes are n^{27/16}-chirps at
    # |u| ≍ P^{27/32}; remainder modes are n^{9/8} at
    # |u| ≍ P^{31/96}. Neither is Stage 2. Theorem X stays
    # CONJECTURE.
    "length7_passenger_theorem_t_refuted": True,
    # Phase 35: isolated e(u n^{27/16}) and e(C n^{3/2}) close
    # by one A-process + Lemma 3.3 inside P^{23/24}. The
    # w^{3/2} = n^{27/16} + O(n^{3/16} θ_2) reduction is not
    # a (D1)/(D3) decoration (spawned amplitude can exceed n).
    # Theorem X stays CONJECTURE.
    "length7_vdc3_chirps_proved": True,
    # Phase 37: X3-runs plus the Q/R3 carry do not close
    # e(u w^{3/2}). kappa_w has mean run O(1); the sawtooth
    # coefficient (3u/2) U^{1/2} exceeds n. Theorem X stays
    # CONJECTURE.
    "length7_x3_qr3_carry_refuted": True,
    # Phase 38: the Phase-13 integer-w block e(ξ w) with
    # ξ ≍ n^{45/32} is the naive θ_w coefficient Lemma X1
    # eliminated. Independently it sits above the engine
    # line (ξ > n, ξ' ≫ 1). Same Phase-5 wall. Theorem X
    # stays CONJECTURE.
    "length7_integer_w_engine_line_refuted": True,
    # Phase 41: the harvest counting program is
    # laboratory-terminal. Every reading of e(u w^{3/2})
    # is a killed route, a nearby reformulation, an
    # isolated monomial already in Lemma X5, or a nested
    # floor / new decoration class that is not a Juggler
    # construction. Theorems X and AA stay CONJECTURE.
    "harvest_counting_terminal": True,
}


def juggler_step(x: int) -> int:
    if x % 2 == 1:
        return isqrt(x * x * x)
    return isqrt(x)


# --- Phase 1: exact validation of the linearization and gap structure ---

SCALE = 10**30


def _sqrt_scaled(x: int, scale: int = SCALE) -> int:
    """floor(sqrt(x) * scale) in exact integer arithmetic."""
    return isqrt(x * scale * scale)


def _quartic_scaled(x: int, scale: int = SCALE) -> int:
    """floor(x^{1/4} * scale) in exact integer arithmetic."""
    return isqrt(isqrt(x * scale**4))


def identity_error_scaled(n: int, scale: int = SCALE) -> tuple[int, int]:
    """(E(n)*scale, bound*scale) for the exact linearization at odd n.

    Lemma A: m^{3/2} = (3/2) m n^{3/4} - (1/2) n^{9/4} + E(n) with
    0 <= E(n) <= (3/8) (n^{3/2}-1)^{-1/2} <= (1/2) n^{-3/4}, where
    m = floor(n^{3/2}). Returned values carry integer-rounding slack of
    a few units times m, negligible at this scale.
    """
    if n < 3 or n % 2 == 0:
        raise ValueError("odd n >= 3 required")
    m = isqrt(n**3)
    m32 = _sqrt_scaled(m**3, scale)
    n94 = _quartic_scaled(n**9, scale)
    n34 = _quartic_scaled(n**3, scale)
    err = m32 + n94 // 2 - (3 * m * n34) // 2
    bound = (scale * scale) // (2 * n34)
    return err, bound


def identity_scan(samples: tuple[int, ...]) -> dict[str, Any]:
    """Check 0 <= E(n) <= (1/2) n^{-3/4} on the given odd samples."""
    slack_units = 8
    worst_ratio = 0.0
    for n in samples:
        err, bound = identity_error_scaled(n)
        m = isqrt(n**3)
        slack = slack_units * max(m, 1)
        if err < -slack or err > bound + slack:
            return {"holds": False, "witness": n}
        if bound > 0:
            worst_ratio = max(worst_ratio, err / bound)
    return {"holds": True, "count": len(samples), "worst_ratio": round(worst_ratio, 6)}


def smooth_cancellation_check(n: int, h: int) -> float:
    """|A1''(n)| * n^{7/4} / h^2 for the smooth difference part (j = 1).

    A1(n) = -(1/4)[(n+2h)^{9/4} - n^{9/4}]
            + (3/4) n^{3/2} [(n+2h)^{3/4} - n^{3/4}].
    The leading n^{5/4}-scale terms cancel, leaving A1'' = O(h^2 n^{-7/4});
    this returns the normalized ratio via an exact scaled second
    difference (step 2), which must stay O(1).
    """
    scale = SCALE

    def a1_scaled(x: int) -> int:
        q9 = _quartic_scaled(x**9, scale)
        q9h = _quartic_scaled((x + 2 * h) ** 9, scale)
        q34 = _quartic_scaled(x**3, scale)
        q34h = _quartic_scaled((x + 2 * h) ** 3, scale)
        s32 = _sqrt_scaled(x**3, scale)
        return -(q9h - q9) // 4 + (3 * s32 * (q34h - q34)) // (4 * scale)

    d2 = a1_scaled(n + 2) - 2 * a1_scaled(n) + a1_scaled(n - 2)
    n74 = _quartic_scaled(n**7, scale)
    # A1'' ~ d2 / (4 * scale); ratio = |A1''| n^{7/4} / h^2.
    return abs(d2) * n74 / (4 * scale * scale * h * h)


def _eighth_scaled(x: int, scale: int = SCALE) -> int:
    """floor(x^{1/8} * scale) in exact integer arithmetic."""
    return isqrt(isqrt(isqrt(x * scale**8)))


def fourth_letter_smoothing_check(n: int, scale: int = SCALE) -> tuple[int, int]:
    """(D(n)*scale, bound*scale) for the fourth-letter linearization.

    Lemma D: v^{1/2} = n^{9/8} + D(n) with
    -(3/4) n^{-3/8} - n^{-9/8} <= D(n) <= 0, where m = floor(n^{3/2}),
    v = floor(m^{3/2}). Composition of the exact linearizations of
    m^{3/4} and (m^{3/2} - theta_2)^{1/2}; all amplitudes decay.
    """
    if n < 3 or n % 2 == 0:
        raise ValueError("odd n >= 3 required")
    m = isqrt(n**3)
    v = isqrt(m**3)
    v12 = _sqrt_scaled(v, scale)
    n98 = _eighth_scaled(n**9, scale)
    diff = v12 - n98
    n38 = _eighth_scaled(n**3, scale)
    bound = (3 * scale * scale) // (4 * n38) + (scale * scale) // n98
    return diff, bound


def fourth_letter_scan(samples: tuple[int, ...]) -> dict[str, Any]:
    """Check -(3/4) n^{-3/8} - n^{-9/8} <= D(n) <= 0 on odd samples."""
    slack = 8
    worst_ratio = 0.0
    for n in samples:
        diff, bound = fourth_letter_smoothing_check(n)
        if diff > slack or diff < -bound - slack:
            return {"holds": False, "witness": n}
        if bound > 0:
            worst_ratio = max(worst_ratio, -diff / bound)
    return {"holds": True, "count": len(samples), "worst_ratio": round(worst_ratio, 6)}


def ooee_indicator_identity_check(n_max: int) -> dict[str, Any]:
    """Exact branch-consistency check of the OOEE sign algebra.

    itinerary_word(n, 4) == 'OOEE' iff ((-1)^m, (-1)^v, (-1)^isqrt(v))
    equals (-1, +1, +1) with m = isqrt(n^3), v = isqrt(m^3): the
    (1+psi_2) factor restricts to even v, exactly where J^3 takes the
    even branch, so psi_3 may be evaluated unconditionally.
    """
    for n in range(3, n_max + 1, 2):
        m = isqrt(n**3)
        v = isqrt(m**3)
        signs = (m % 2 == 1, v % 2 == 0, isqrt(v) % 2 == 0)
        if (itinerary_word(n, 4) == "OOEE") != all(signs):
            return {"holds": False, "witness": n}
    return {"holds": True, "n_max": n_max}


def deep_word_counts(n_max: int, depth: int) -> dict[str, int]:
    """Exact census of length-`depth` word words on odd starts."""
    counts: dict[str, int] = {}
    for n in range(3, n_max + 1, 2):
        w = itinerary_word(n, depth)
        counts[w] = counts.get(w, 0) + 1
    return dict(sorted(counts.items()))


# --- Phase 6: the OEO* split (growing layer on the slow variable) ---


def lemma_a_prime_check(n: int, scale: int = SCALE) -> tuple[int, int]:
    """(E*scale, bound*scale) for the w-level linearization (Lemma A').

    With m = floor(n^{3/2}), U = m^{1/2}, w = floor(U), theta_w = U - w:
    w^{3/2} = -(1/2) m^{3/4} + (3/2) w m^{1/4} + E,
    0 <= E <= (3/8)(U-1)^{-1/2}. Since U m^{1/4} = m^{3/4} exactly, this
    rearranges to w^{3/2} = m^{3/4} - (3/2) m^{1/4} theta_w + E: the
    entire OEO* fourth-letter phase is one decaying-smooth term plus
    one growing sawtooth of amplitude (3/2) m^{1/4} ~ n^{3/8}.
    """
    if n < 5 or n % 2 == 0:
        raise ValueError("odd n >= 5 required")
    m = isqrt(n**3)
    w = isqrt(m)
    lhs = isqrt(w**3 * scale * scale)
    r34m = isqrt(isqrt(m**3 * scale**4))
    r14m = isqrt(isqrt(m * scale**4))
    poly = -r34m // 2 + 3 * w * r14m // 2
    bound = 3 * scale // (8 * isqrt(w - 1))
    return lhs - poly, bound


def lemma_a_prime_scan(samples: tuple[int, ...]) -> dict[str, Any]:
    for n in samples:
        diff, bound = lemma_a_prime_check(n)
        if not (-4 * n <= diff <= bound + 4 * n):
            return {"holds": False, "witness": n}
    return {"holds": True, "count": len(samples)}


def oeo_smoothing_check(n: int, scale: int = SCALE) -> tuple[int, int, int]:
    """(d2*scale, lo*scale, hi*scale) for the full OEO* smoothing.

    d2 = w^{3/2} - n^{9/8} + (3/2) m^{1/4} theta_w collects Lemma A'
    plus the m^{3/4} -> n^{9/8} substitution:
    -(3/4) n^{-3/8} - (3/32)(X-1)^{-5/4} <= d2 <= (3/8)(U-1)^{-1/2}.
    All error terms decay, so the phase (k/2) w^{3/2} equals
    (k/2) n^{9/8} - (3k/4) m^{1/4} theta_w + absorbable.
    """
    if n < 5 or n % 2 == 0:
        raise ValueError("odd n >= 5 required")
    m = isqrt(n**3)
    w = isqrt(m)
    t_w = isqrt(w**3 * scale * scale)
    r98 = _eighth_scaled(n**9, scale)
    r38 = _eighth_scaled(n**3, scale)
    r14m = isqrt(isqrt(m * scale**4))
    th_w = isqrt(m * scale * scale) - w * scale
    d2 = t_w - r98 + 3 * (r14m * th_w) // (2 * scale)
    lo = -(3 * scale * scale) // (4 * r38)
    hi = 3 * scale // (8 * isqrt(w - 1))
    return d2, lo, hi


def oeo_smoothing_scan(samples: tuple[int, ...]) -> dict[str, Any]:
    for n in samples:
        d2, lo, hi = oeo_smoothing_check(n)
        if not (lo - 4 * n <= d2 <= hi + 4 * n):
            return {"holds": False, "witness": n}
    return {"holds": True, "count": len(samples)}


def oeo_indicator_identity_check(n_max: int) -> dict[str, Any]:
    """Branch consistency for all four OE** depth-4 words.

    For odd n with m = floor(n^{3/2}) even and w = isqrt(m): the word
    is 'OE' + parity(w) + parity(isqrt(w^3) if w odd else isqrt(w)).
    The (1-(-1)^w)/2 factor vanishes exactly where J^3 would take the
    even branch, so psi(w^{3/2}) evaluates unconditionally.
    """
    checked = 0
    for n in range(3, n_max + 1, 2):
        m = isqrt(n**3)
        if m % 2 == 1:
            continue
        w = isqrt(m)
        if w % 2 == 1:
            fourth = isqrt(w**3)
        else:
            fourth = isqrt(w)
        expected = (
            "OE"
            + ("O" if w % 2 == 1 else "E")
            + ("O" if fourth % 2 == 1 else "E")
        )
        if itinerary_word(n, 4) != expected:
            return {"holds": False, "witness": n}
        checked += 1
    return {"holds": True, "checked": checked, "n_max": n_max}


def _sixteenth_scaled(x: int, scale: int = SCALE) -> int:
    """floor(x^{1/16} * scale) via four nested isqrts."""
    return isqrt(isqrt(isqrt(isqrt(x * scale**16))))


def oooee_smoothing_check(n: int, scale: int = SCALE) -> tuple[int, int]:
    """(d5*scale, bound*scale) for the OOOE* fifth-letter smoothing.

    z = floor(v^{3/2}), v = floor(m^{3/2}), m = floor(n^{3/2}):
    z^{1/2} = n^{27/16} - (9/8) n^{3/16} theta + D5, with D5 decaying
    (the theta_2 and theta_z amplitudes are O(n^{-9/16})). The only
    growing sawtooth has coefficient n^{3/16} < n — engine side.
    """
    if n < 5 or n % 2 == 0:
        raise ValueError("odd n >= 5 required")
    m = isqrt(n**3)
    v = isqrt(m**3)
    z = isqrt(v**3)
    z12 = isqrt(z * scale * scale)
    r27 = _sixteenth_scaled(n**27, scale)
    r3 = _sixteenth_scaled(n**3, scale)
    th = isqrt(n**3 * scale * scale) - m * scale
    d5 = z12 - r27 + 9 * (r3 * th) // (8 * scale)
    # Decaying envelope: (3/4) m^{-3/8} + (1/2) v^{-3/4} + (9/128) n^{-7/16}.
    r38m = isqrt(isqrt(isqrt(m**3 * scale**8)))
    r34v = isqrt(isqrt(v**3 * scale**4))
    r7 = _sixteenth_scaled(n**7, scale)
    bound = 3 * scale * scale // (4 * r38m) + scale * scale // (2 * r34v) + 9 * scale * scale // (128 * r7)
    return d5, bound


def oooee_smoothing_scan(samples: tuple[int, ...]) -> dict[str, Any]:
    for n in samples:
        d5, bound = oooee_smoothing_check(n)
        if not (-bound - 8 * n <= d5 <= bound + 8 * n):
            return {"holds": False, "witness": n, "d5": d5, "bound": bound}
    return {"holds": True, "count": len(samples)}


def ooeoe_smoothing_check(n: int, scale: int = SCALE) -> tuple[int, int]:
    """(d5*scale, bound*scale) for the OOEO* fifth-letter linearization.

    w = floor(v^{1/2}), v = floor(m^{3/2}): Lemma A' at the w-level
    plus the v^{3/4} -> n^{27/16} chain gives
    w^{3/2} = n^{27/16} - (9/8) n^{3/16} theta - (3/2) v^{1/4} theta_w + D,
    D decaying. Two engine sawtooths: coeff n^{3/16} (theta) and
    n^{9/16} (theta_w); both grow slower than n.
    """
    if n < 5 or n % 2 == 0:
        raise ValueError("odd n >= 5 required")
    m = isqrt(n**3)
    v = isqrt(m**3)
    w = isqrt(v)
    t_w = isqrt(w**3 * scale * scale)
    r27 = _sixteenth_scaled(n**27, scale)
    r3 = _sixteenth_scaled(n**3, scale)
    th = isqrt(n**3 * scale * scale) - m * scale
    r14v = isqrt(isqrt(v * scale**4))
    th_w = isqrt(v * scale * scale) - w * scale
    d5 = t_w - r27 + 9 * (r3 * th) // (8 * scale) + 3 * (r14v * th_w) // (2 * scale)
    r38m = isqrt(isqrt(isqrt(m**3 * scale**8)))
    bound = 3 * scale * scale // (4 * r38m) + 3 * scale // (8 * isqrt(max(w, 2) - 1))
    return d5, bound


def ooeoe_smoothing_scan(samples: tuple[int, ...]) -> dict[str, Any]:
    for n in samples:
        d5, bound = ooeoe_smoothing_check(n)
        if not (-bound - 8 * n <= d5 <= bound + 8 * n):
            return {"holds": False, "witness": n, "d5": d5, "bound": bound}
    return {"holds": True, "count": len(samples)}


def oooee_indicator_identity_check(n_max: int) -> dict[str, Any]:
    """Branch consistency: OOOE* fifth letter is parity of isqrt(z)."""
    checked = 0
    for n in range(3, n_max + 1, 2):
        word = itinerary_word(n, 5)
        if not word.startswith("OOOE"):
            continue
        m = isqrt(n**3)
        v = isqrt(m**3)
        z = isqrt(v**3)
        expected = "OOOE" + ("O" if isqrt(z) % 2 == 1 else "E")
        if word != expected:
            return {"holds": False, "witness": n}
        checked += 1
    return {"holds": True, "checked": checked, "n_max": n_max}


def ooeoe_indicator_identity_check(n_max: int) -> dict[str, Any]:
    """Branch consistency: OOEO* fifth letter is parity of isqrt(w^3)."""
    checked = 0
    for n in range(3, n_max + 1, 2):
        word = itinerary_word(n, 5)
        if not word.startswith("OOEO"):
            continue
        m = isqrt(n**3)
        v = isqrt(m**3)
        w = isqrt(v)
        expected = "OOEO" + ("O" if isqrt(w**3) % 2 == 1 else "E")
        if word != expected:
            return {"holds": False, "witness": n}
        checked += 1
    return {"holds": True, "checked": checked, "n_max": n_max}


def ooeoe_mode_probe(p_block: int) -> dict[str, Any]:
    """Float probe of sum e((1/2) w^{3/2}) on the OOEO cylinder, n ~ P."""
    from math import cos, pi, sin

    s = 10**12
    re = im = 0.0
    cnt = 0
    n = p_block + 1
    while n < 2 * p_block:
        m = isqrt(n**3)
        if m % 2 == 0:
            n += 2
            continue
        v = isqrt(m**3)
        if v % 2 == 1:
            n += 2
            continue
        w = isqrt(v)
        if w % 2 == 0:
            n += 2
            continue
        t_w = isqrt(w**3 * s * s)
        frac = (t_w % (2 * s)) / (2 * s)
        ph = 2 * pi * frac
        re += cos(ph)
        im += sin(ph)
        cnt += 1
        n += 2
    return {"count": cnt, "abs_sum": round((re * re + im * im) ** 0.5, 1)}


def oooee_mode_probe(p_block: int) -> dict[str, Any]:
    """Float probe of sum e((1/2) z^{1/2}) on the OOOE cylinder, n ~ P."""
    from math import cos, pi, sin

    s = 10**12
    re = im = 0.0
    cnt = 0
    n = p_block + 1
    while n < 2 * p_block:
        m = isqrt(n**3)
        if m % 2 == 0:
            n += 2
            continue
        v = isqrt(m**3)
        if v % 2 == 0:
            n += 2
            continue
        z = isqrt(v**3)
        if z % 2 == 1:
            n += 2
            continue
        t = isqrt(z * s * s)
        frac = (t % (2 * s)) / (2 * s)
        ph = 2 * pi * frac
        re += cos(ph)
        im += sin(ph)
        cnt += 1
        n += 2
    return {"count": cnt, "abs_sum": round((re * re + im * im) ** 0.5, 1)}


# --- Phase 11: OOOO* kernel isolation (level-3 floor defect) ---


def level3_reformulation_check(n: int, scale: int = 10**40) -> tuple[int, int]:
    """(diff*scale, bound*scale) for the level-3 kernel reformulation.

    With Z = v^{3/2}, z = floor(Z), theta_3 = Z - z:
    (1/2)(v^{9/4} - z^{3/2}) - (3/4) z^{1/2} theta_3 = R3 in
    [0, (3/16) z^{-1/2}] (Taylor of (z + theta_3)^{3/2} at z, one-signed
    remainder). Hence the central kernel phase c*theta_3 with
    c = (3k/4) z^{1/2} equals (k/2)(v^{9/4} - z^{3/2}) up to k R3:
    the OOOO* kernel is the exponential sum of the level-3 local
    floor defect. Lemma R1 with (m, v) replaced by (v, z).
    """
    if n < 5 or n % 2 == 0:
        raise ValueError("odd n >= 5 required")
    m = isqrt(n**3)
    v = isqrt(m**3)
    z = isqrt(v**3)
    v94 = isqrt(isqrt(v**9 * scale**4))
    z32 = isqrt(z**3 * scale * scale)
    z12 = isqrt(z * scale * scale)
    th3 = isqrt(v**3 * scale * scale) - z * scale
    diff = (v94 - z32) // 2 - (3 * z12 * th3) // (4 * scale)
    # Floor slack: z12 and th3 each carry O(1) scaled-unit error;
    # the cross product propagates them at z^{1/2} ~ n^{27/16} units.
    slack = isqrt(z) + 10**6
    bound = (3 * scale * scale) // (16 * z12) + slack
    return diff, bound


def level3_reformulation_scan(samples: tuple[int, ...]) -> dict[str, Any]:
    """Check 0 <= diff <= bound on odd samples (slack folded into bound)."""
    slack = 10**7
    for n in samples:
        diff, bound = level3_reformulation_check(n)
        if diff < -slack or diff > bound:
            return {"holds": False, "witness": n}
    return {"holds": True, "count": len(samples)}


def _level3_phase_scaled(n: int, coeff_num: int, coeff_den: int) -> float:
    """{c(n) theta_3(n)} with c = (num/den) z^{1/2}, exact scaled ints."""
    s = 10**12
    s30 = 10**30
    v = isqrt(isqrt(n**3) ** 3)
    z = isqrt(v**3)
    t3 = isqrt(v**3 * s * s)
    th3 = t3 - (t3 // s) * s
    z12 = isqrt(z * s30 * s30)
    prod = (coeff_num * z12 * th3) // coeff_den
    return (prod % (s30 * s)) / (s30 * s)


def level3_kernel_probe(
    p_block: int, coeff_num: int = 3, coeff_den: int = 4
) -> dict[str, Any]:
    """Float probe of the isolated level-3 kernel K3 = sum e(c {v^{3/2}}).

    c(n) = (coeff_num/coeff_den) z^{1/2}, the natural z^{1/2}-scale of
    the OOOO* reduction (z = floor(v^{3/2}) ~ n^{27/8}, so
    c ~ n^{27/16}). Exact scaled phase arithmetic; float only in the
    final exponential. Not a proof; supports or refutes Conjecture V.
    """
    from math import cos, pi, sin

    re = im = 0.0
    cnt = 0
    n = p_block + 1
    while n < 2 * p_block:
        frac = _level3_phase_scaled(n, coeff_num, coeff_den)
        ph = 2 * pi * frac
        re += cos(ph)
        im += sin(ph)
        cnt += 1
        n += 2
    return {"count": cnt, "abs_sum": round((re * re + im * im) ** 0.5, 1)}


def differenced_level3_kernel_probe(
    p_block: int,
    h1: int,
    h2: int = 0,
    h3: int = 0,
    coeff_num: int = 3,
    coeff_den: int = 4,
) -> dict[str, Any]:
    """Once-, twice- or thrice-differenced level-3 kernel sums.

    Same corner construction as differenced_kernel_probe; phase is
    c theta_3 with c = (coeff_num/coeff_den) z^{1/2}. Not a proof.
    """
    from math import cos, pi, sin

    corners = [(1, 2 * h1), (-1, 0)]
    for h in (h2, h3):
        if h > 0:
            corners = [(s, d + 2 * h) for s, d in corners] + [
                (-s, d) for s, d in corners
            ]
    re = im = 0.0
    cnt = 0
    n = p_block + 1
    while n < 2 * p_block:
        ph = 0.0
        for sgn, d in corners:
            ph += sgn * _level3_phase_scaled(n + d, coeff_num, coeff_den)
        theta = 2 * pi * ph
        re += cos(theta)
        im += sin(theta)
        cnt += 1
        n += 2
    return {
        "count": cnt,
        "abs_sum": round((re * re + im * im) ** 0.5, 1),
        "sqrt_count": round(cnt**0.5, 1),
    }


_U_SCALE = 10**15


def _dispersion_amplitude_scaled(n: int) -> int:
    """floor({(3/4) z^{1/2} theta_3} * 10^15), exact scaled integers.

    The dispersion amplitude u(n) = (3/4) z^{1/2} theta_3 mod 1: the
    K3 phase at k = 1, so the k-family phase is k*u. theta_3 is
    computed at scale 10^24 because the z^{1/2} ~ n^{27/16} factor
    amplifies theta_3 error by ~10^10; the result is exact to ~10^-13
    at n = 10^6, far below the census resolution 1/J.
    """
    s24 = 10**24
    s30 = 10**30
    v = isqrt(isqrt(n**3) ** 3)
    z = isqrt(v**3)
    t3 = isqrt(v**3 * s24 * s24)
    th3 = t3 - z * s24
    z12 = isqrt(z * s30 * s30)
    prod = (3 * z12 * th3) // 4
    return (prod % (s30 * s24)) // (s30 * s24 // _U_SCALE)


def dispersion_spacing_census(
    p_block: int,
    sample_cap: int = 50_000,
    j_scale: int = 32,
    lags: tuple[int, ...] = (1, 2, 3, 4),
) -> dict[str, Any]:
    """Phase-0 falsifier for the bilinear-dispersion attack on K3.

    The dispersion route (double large sieve on the k-family) needs
    (a) near-Poissonian pair statistics of u(n) mod 1 at scale 1/J:
        #{pairs with ||u_i - u_j|| < 1/J} ~ N^2/J, and
    (b) no short-lag rigidity: u(n+2h) - u(n) mod 1 equidistributed
        (|mean e(u(n+2h)-u(n))| at the sqrt-N noise floor), since a
        sieve cannot decouple nearby terms.
    Coincidence excess or lag concentration kills the route.
    OBSERVATION-level evidence only; not a proof either way.
    """
    from math import cos, pi, sin

    max_lag = max(lags)
    us: list[int] = []
    n = p_block + 1
    while n < 2 * p_block and len(us) < sample_cap + max_lag:
        us.append(_dispersion_amplitude_scaled(n))
        n += 2
    count = min(len(us) - max_lag, sample_cap)

    # (a) near-coincidence pairs at circular scale eps = 1/j_scale.
    # Extended-array two-pointer: each unordered pair with circular
    # gap < eps is counted exactly once (eps << 1/2).
    eps = _U_SCALE // j_scale
    vals = sorted(us[:count])
    ext = vals + [x + _U_SCALE for x in vals]
    near = 0
    j = 0
    for i in range(count):
        if j < i + 1:
            j = i + 1
        while j < i + count and ext[j] - vals[i] < eps:
            j += 1
        near += j - i - 1
    expected = count * (count - 1) / j_scale
    ratio = near / expected if expected else 0.0

    # (b) short-lag difference concentration.
    lag_r: dict[str, float] = {}
    for h in lags:
        re = im = 0.0
        for i in range(count):
            d = (us[i + h] - us[i]) / _U_SCALE
            ph = 2 * pi * d
            re += cos(ph)
            im += sin(ph)
        lag_r[f"h={h}"] = round((re * re + im * im) ** 0.5 / count, 4)

    return {
        "count": count,
        "j_scale": j_scale,
        "near_pairs": near,
        "poisson_expected": round(expected, 1),
        "coincidence_ratio": round(ratio, 4),
        "lag_concentration": lag_r,
        "noise_floor": round(count**-0.5, 4),
    }


def block_m_affine_model_check(
    p_block: int, n_blocks: int = 50
) -> dict[str, Any]:
    """Lemma DD(i) validator: on blocks of L = P^{1/4} odd steps,
    m(t) = floor(X_0 + D t) + defect with |defect| bounded.

    X_0, D are the scaled value and first increment of X = n^{3/2} at
    the block start; the X-quadratic over the block is O(1)
    ((3/2) t^2 P^{-1/2} <= 3/2 at t = P^{1/4}), so the affine model
    is exact up to a bounded defect. Exact scaled integers.
    """
    s = 10**12
    block_len = max(4, isqrt(isqrt(p_block)))
    worst = 0
    n0 = p_block + 1
    for _ in range(n_blocks):
        x0 = isqrt(n0**3 * s * s)
        d = isqrt((n0 + 2) ** 3 * s * s) - x0
        for t in range(block_len):
            m_true = isqrt((n0 + 2 * t) ** 3)
            m_model = (x0 + d * t) // s
            worst = max(worst, abs(m_true - m_model))
        n0 += 2 * block_len
    return {
        "block_len": block_len,
        "n_blocks": n_blocks,
        "max_defect": worst,
    }


def block_v_amplified_model_check(
    p_block: int, n_blocks: int = 50
) -> dict[str, Any]:
    """Lemma DD(ii) validator: on blocks of L = P^{1/4} odd steps,
    v(t) = floor(mu(t)^{3/2} + (3/2) mu(t)^{1/2} s(t)) + defect,
    |defect| bounded, where mu(t) = m_0 + A t is the affine base
    (A the realized first m-gap) and s(t) = m(t) - mu(t) is the
    realized rotation-carry sequence.

    The level-2 block data is a smooth function of the affine base
    plus the one-dimensional carry sequence amplified by
    W = (3/2) mu^{1/2} ~ P^{3/4}: the transport substrate. The
    Taylor remainder (3/8) xi^{-1/2} s^2 ~ P^{-3/4} P^{1/2} < 1.
    Exact scaled integers.
    """
    s = 10**12
    block_len = max(4, isqrt(isqrt(p_block)))
    worst = 0
    worst_s = 0
    n0 = p_block + 1
    for _ in range(n_blocks):
        m0 = isqrt(n0**3)
        a = isqrt((n0 + 2) ** 3) - m0
        for t in range(block_len):
            m_true = isqrt((n0 + 2 * t) ** 3)
            mu = m0 + a * t
            st = m_true - mu
            worst_s = max(worst_s, abs(st))
            v_true = isqrt(m_true**3)
            y_mu = isqrt(mu**3 * s * s)
            w_mu = 3 * isqrt(mu * s * s) // 2
            v_model = (y_mu + w_mu * st) // s
            worst = max(worst, abs(v_true - v_model))
        n0 += 2 * block_len
    return {
        "block_len": block_len,
        "n_blocks": n_blocks,
        "max_defect": worst,
        "max_carry": worst_s,
    }


def carry_multiplier_probe(p_block: int, sample_cap: int = 20_000) -> dict[str, Any]:
    """Equidistribution probe for the transport pair-decay multiplier.

    A unit carry in v changes the kernel phase c theta_3 by
    beta = {c ((v+1)^{3/2} - v^{3/2})} mod 1 (c = (3/4) z^{1/2}, the
    k = 1 family member). The entropy mechanism of the transport
    inductive step needs beta to be non-degenerate on average:
    |mean e(beta)| at the noise floor. Exact scaled integers;
    OBSERVATION only.
    """
    from math import cos, pi, sin

    s24 = 10**24
    s30 = 10**30
    re = im = 0.0
    cnt = 0
    n = p_block + 1
    while n < 2 * p_block and cnt < sample_cap:
        v = isqrt(isqrt(n**3) ** 3)
        z = isqrt(v**3)
        jump = isqrt((v + 1) ** 3 * s24 * s24) - isqrt(v**3 * s24 * s24)
        z12 = isqrt(z * s30 * s30)
        prod = (3 * z12 * jump) // 4
        beta = (prod % (s30 * s24)) / (s30 * s24)
        ph = 2 * pi * beta
        re += cos(ph)
        im += sin(ph)
        cnt += 1
        n += 2
    return {
        "count": cnt,
        "mean_abs": round((re * re + im * im) ** 0.5 / cnt, 4),
        "noise_floor": round(cnt**-0.5, 4),
    }


def level3_block_model_check(
    p_block: int, n_blocks: int = 20
) -> dict[str, Any]:
    """Lemma FF validator: the level-3 block phase model.

    On DD-blocks, with F = mu^{3/2} + (3/2) mu^{1/2} s, v = floor(F) + d,
    e = d - {F}:

      theta_3 = { mu^{9/4} + (9/4) mu^{5/4} s + (27/32) mu^{1/4} s^2
                  - (27/128) mu^{-3/4} s^3 + (243/2048) mu^{-7/4} s^4
                  + ((3/2) mu^{3/4} + (9/8) mu^{-1/4} s
                     - (27/64) mu^{-5/4} s^2) e
                  + (3/8) mu^{-3/4} e^2 }
                + O(P^{-19/16}),

    The product form u = (3/4) z^{1/2} theta_3 mod 1 amplifies the
    theta_3 model error by z^{1/2} ~ P^{27/16}, so the model must be
    kept to precision P^{-27/16}: the terms of scales P^{-9/8},
    P^{-11/8}, P^{-13/8} above are all mandatory for the kernel phase
    even though each is sub-unit. With the coefficient
    (3/4) z^{1/2} = (3/4)(mu^{9/8} + (9/8) mu^{1/8} s) + corrections
    of scales P^{-9/16} (the (3/4) F^{-1/4} e term) and P^{-13/16}
    (the F^{3/4} s^2 term), u is modelled to ~P^{-15/16}. The nested
    level-3 defect on a block is an explicit polynomial in the carry
    s with mu-monomial coefficients plus a (3/2) mu^{3/4}-amplified
    level-2 fractional term. Exact scaled integers; returns worst
    circular errors.
    """
    sc = 10**48
    block_len = max(4, isqrt(isqrt(p_block)))
    worst_t3 = 0.0
    worst_u = 0.0
    n0 = p_block + 1
    for _ in range(n_blocks):
        m0 = isqrt(n0**3)
        a = isqrt((n0 + 2) ** 3) - m0
        for t in range(block_len):
            n = n0 + 2 * t
            m_true = isqrt(n**3)
            v_true = isqrt(m_true**3)
            z = isqrt(v_true**3)
            mu = m0 + a * t
            st = m_true - mu
            f = isqrt(mu**3 * sc * sc) + 3 * isqrt(mu * sc * sc) * st // 2
            d = v_true - f // sc
            f_frac = f % sc
            t3_true = isqrt(v_true**3 * sc * sc) - z * sc

            mu94 = isqrt(isqrt(mu**9 * sc**4))
            mu54 = isqrt(isqrt(mu**5 * sc**4))
            mu34 = isqrt(isqrt(mu**3 * sc**4))
            mu14 = isqrt(isqrt(mu * sc**4))
            df = d * sc - f_frac
            theta = (
                mu94
                + 9 * mu54 * st // 4
                + 27 * mu14 * st * st // 32
                - 27 * st**3 * sc * sc // (128 * mu34)
                + 243 * st**4 * sc * sc // (2048 * mu34 * mu)
                + 3 * mu34 * df // (2 * sc)
                + 9 * st * df * sc // (8 * mu14)
                - 27 * st * st * df * sc // (64 * mu14 * mu)
                + 3 * df * df // (8 * mu34)
            )
            t3_model = theta % sc
            e3 = abs(t3_true - t3_model)
            e3 = min(e3, sc - e3) / sc
            worst_t3 = max(worst_t3, e3)

            mu98 = isqrt(mu94 * sc)
            mu18 = isqrt(mu14 * sc)
            mu38 = isqrt(mu34 * sc)
            coeff = (
                3
                * (
                    mu98
                    + 9 * st * mu18 // 8
                    - 27 * st * st * mu18 // (128 * mu)
                )
                // 4
            )
            u_model = (
                coeff * t3_model // sc
                + 9 * df * t3_model // (16 * mu38)
            ) % sc
            z12 = isqrt(z * sc * sc)
            u_true = 3 * z12 * t3_true // 4 % (sc * sc) // sc
            eu = abs(u_true - u_model)
            eu = min(eu, sc - eu) / sc
            worst_u = max(worst_u, eu)
        n0 += 2 * block_len
    return {
        "block_len": block_len,
        "n_blocks": n_blocks,
        "max_theta3_err": worst_t3,
        "max_u_err": worst_u,
        "theta3_scale": p_block ** (-9 / 8),
        "u_scale": p_block ** (-9 / 16),
    }


def block_kernel_sum_census(
    p_block: int,
    n_blocks: int = 200,
    ks: tuple[int, ...] = (1, 2, 3),
) -> dict[str, Any]:
    """Census gate for Conjecture EE: in-block kernel-sum cancellation.

    For blocks B of L = P^{1/4} consecutive odd steps, computes
    R_k(B) = |sum_{t<L} e(k u)|^2 / L (u the exact K3 amplitude).
    Conjecture EE needs |S_k(B)| <= L^{1-delta} for most blocks; the
    random-phase prediction is R_k ~ Exp(1) (mean 1, thin tails).
    Also reports the mean R among the most rotation-resonant decile
    of blocks (gamma = D - A near a rational p/q, q <= 8), as an
    exploratory diagnostic for the harmonic-skeleton mechanism.
    OBSERVATION only.
    """
    from math import cos, pi, sin

    s24 = 10**24
    block_len = max(4, isqrt(isqrt(p_block)))
    rs: dict[int, list[float]] = {k: [] for k in ks}
    resonance: list[float] = []
    n0 = p_block + 1
    for _ in range(n_blocks):
        x0 = isqrt(n0**3 * s24 * s24)
        d_s = isqrt((n0 + 2) ** 3 * s24 * s24) - x0
        gamma = (d_s % s24) / s24
        res = min(
            abs(q * gamma - round(q * gamma)) / q for q in range(1, 9)
        )
        resonance.append(res)
        us = [
            _dispersion_amplitude_scaled(n0 + 2 * t) / _U_SCALE
            for t in range(block_len)
        ]
        for k in ks:
            re = im = 0.0
            for u in us:
                ph = 2 * pi * ((k * u) % 1.0)
                re += cos(ph)
                im += sin(ph)
            rs[k].append((re * re + im * im) / block_len)
        n0 += 2 * block_len

    order = sorted(range(n_blocks), key=lambda i: resonance[i])
    decile = max(1, n_blocks // 10)
    out: dict[str, Any] = {
        "block_len": block_len,
        "n_blocks": n_blocks,
    }
    for k in ks:
        vals = sorted(rs[k])
        out[f"k={k}"] = {
            "mean_R": round(sum(vals) / n_blocks, 3),
            "median_R": round(vals[n_blocks // 2], 3),
            "max_R": round(vals[-1], 2),
            "frac_R>4": round(
                sum(1 for x in vals if x > 4) / n_blocks, 4
            ),
            "mean_R_resonant_decile": round(
                sum(rs[k][i] for i in order[:decile]) / decile, 3
            ),
        }
    return out


def pure_model_census(
    p_block: int, n_blocks: int = 200, k: int = 1
) -> dict[str, Any]:
    """Census for Conjecture HH: the pure amplitude-product model.

    The carry-free crystal of the kernel block sums: for smooth
    monomials A(t) = (3k/4) mu(t)^{9/8} and B(t) = mu(t)^{9/4} with
    mu(t) = mu_0 + a t (a ~ 3 P^{1/2}, the realized m-slope scale),
    compute R(B) = |sum_{t<L} e(A(t) {B(t)})|^2 / L over blocks.
    This is the object Proposition GG shows is untouchable by the
    laboratory toolkit whenever 1 << A' << A (here A' ~ P^{11/16}):
    the Piatetski-Shapiro literature handles A' << 1 only, where
    partial summation makes the amplitude a tame passenger.
    Conjecture HH asserts random-phase cancellation; the census
    checks it (expect R ~ Exp(1)). Exact scaled integers;
    OBSERVATION only.
    """
    from math import cos, pi, sin

    sc = 10**30
    block_len = max(4, isqrt(isqrt(p_block)))
    mu0 = isqrt(p_block**3)
    a = 3 * isqrt(p_block)
    rs: list[float] = []
    for b in range(n_blocks):
        base = mu0 + 2 * a * block_len * b
        re = im = 0.0
        for t in range(block_len):
            mu = base + a * t
            mu94 = isqrt(isqrt(mu**9 * sc**4))
            mu98 = isqrt(mu94 * sc)
            frac = mu94 % sc
            x = 3 * k * mu98 * frac // (4 * sc) % sc
            ph = 2 * pi * (x / sc)
            re += cos(ph)
            im += sin(ph)
        rs.append((re * re + im * im) / block_len)
    vals = sorted(rs)
    return {
        "block_len": block_len,
        "n_blocks": n_blocks,
        "k": k,
        "mean_R": round(sum(vals) / n_blocks, 3),
        "median_R": round(vals[n_blocks // 2], 3),
        "max_R": round(vals[-1], 2),
        "frac_R>4": round(sum(1 for x in vals if x > 4) / n_blocks, 4),
    }


def shift_average_probe(
    p_block: int,
    n_lambda: int = 64,
    n_blocks: int = 100,
    k: int = 1,
) -> dict[str, Any]:
    """Validator for Lemma II (shift average) and Proposition JJ (iii).

    Lemma II: for S_lambda = sum_{t<L} e(A_t {x_t + lambda}) with
    amplitude separation |A_t - A_t'| >= A'_min |t - t'|, direct
    integration over the shift (no characters) gives
    | E_lambda |S|^2 - L | <= (6/pi)(L/A'_min)(log L + 1) —
    two-sided square-root cancellation for almost every shift,
    for ARBITRARY x_t. The probe measures mean_R = E|S|^2/L over a
    lambda-grid for the pure model and compares with the predicted
    correction. It also measures the lambda-correlation scale of
    S_lambda: increments |S_{lambda+delta} - S_lambda|/sqrt(L) at
    delta = m/(2 pi A), m in {0.1, 1, 10} — the ~1/A stability
    radius of Proposition JJ (iii), which is why almost-all-shift
    results cannot pin lambda = 0. OBSERVATION for the probe; the
    lemma itself is EXACT — HUMAN PROOF.
    """
    from math import cos, log, pi, sin

    sc = 10**30
    block_len = max(4, isqrt(isqrt(p_block)))
    mu0 = isqrt(p_block**3)
    a = 3 * isqrt(p_block)

    def block_pre(base: int) -> list[tuple[int, int]]:
        pre = []
        for t in range(block_len):
            mu = base + a * t
            mu94 = isqrt(isqrt(mu**9 * sc**4))
            pre.append((mu94 % sc, isqrt(mu94 * sc)))
        return pre

    def s_val(pre: list[tuple[int, int]], lam: int) -> complex:
        re = im = 0.0
        for frac, mu98 in pre:
            x = 3 * k * mu98 * ((frac + lam) % sc) // (4 * sc) % sc
            ph = 2 * pi * (x / sc)
            re += cos(ph)
            im += sin(ph)
        return complex(re, im)

    total = 0.0
    count = 0
    for b in range(n_blocks):
        pre = block_pre(mu0 + 2 * a * block_len * b)
        for j in range(n_lambda):
            s = s_val(pre, j * sc // n_lambda)
            total += (s.real * s.real + s.imag * s.imag) / block_len
            count += 1
    mean_r = total / count

    # Predicted Lemma II correction: A'_min ~ (27k/32) mu^{1/8} a.
    a_prime = (27 * k / 32) * p_block ** (3 / 16) * (3 * p_block**0.5)
    corr = (6 / pi) * (log(block_len) + 1) / a_prime

    # JJ (iii): lambda-stability at delta = m / (2 pi A).
    pre0 = block_pre(mu0)
    a_amp = 3 * k * pre0[block_len // 2][1] // (4 * sc)
    s0 = s_val(pre0, 0)
    stability = {}
    for m_lbl, m_num, m_den in (("0.1", 1, 10), ("1", 1, 1), ("10", 10, 1)):
        delta = sc * m_num // (int(2 * pi * a_amp) * m_den)
        sd = s_val(pre0, delta)
        stability[f"m={m_lbl}"] = round(
            abs(sd - s0) / block_len**0.5, 3
        )
    return {
        "block_len": block_len,
        "n_blocks": n_blocks,
        "n_lambda": n_lambda,
        "mean_R_over_shifts": round(mean_r, 4),
        "lemma_II_correction": corr,
        "sample_noise": round(count**-0.5, 4),
        "stability_increments": stability,
    }


# --- Phase 23: the length-8 engine quartet (depth-8 contracting ring) ---

DEPTH8_QUARTET = ("OOEOOEOE", "OOEOOOEE", "OOOEOEOE", "OOOEOOEE")


def word_orbit(n: int, word: str) -> list[int]:
    """Word-dictated floor compositions x_1 = n, x_{t+1} = branch(x_t).

    Applies floor(x^{3/2}) on 'O' letters and floor(sqrt(x)) on 'E'
    letters following `word`, regardless of actual parities; on the
    cylinder of `word` this is exactly the Juggler orbit.
    """
    xs = [n]
    for c in word[:-1]:
        xs.append(isqrt(xs[-1] ** 3) if c == "O" else isqrt(xs[-1]))
    return xs


def depth8_quartet_census(n_max: int) -> dict[str, Any]:
    """Exact census of the four contracting length-8 words.

    Each word extends a counted expanding length-7 cylinder
    (Theorem X) by one letter and contracts (3^5 = 243 < 256 = 2^8).
    Expected density: odds/128 per word, odds/64 per parent. Guard:
    J^8(n) < n on every quartet member (Corollary 2.3 instance).
    """
    counts = {w: 0 for w in DEPTH8_QUARTET}
    parents = {w[:7]: 0 for w in DEPTH8_QUARTET}
    odds = 0
    descent_violations = 0
    for n in range(3, n_max + 1, 2):
        odds += 1
        w = itinerary_word(n, 8)
        if w[:7] in parents:
            parents[w[:7]] += 1
        if w in counts:
            counts[w] += 1
            x = n
            for _ in range(8):
                x = juggler_step(x)
            if x >= n and n > 2:
                descent_violations += 1
    expected = odds / 128
    deviations = {
        w: round((c - expected) / max(expected, 1) ** 0.5, 3)
        for w, c in counts.items()
    }
    return {
        "n_max": n_max,
        "odds": odds,
        "counts": counts,
        "parent_counts": parents,
        "expected_per_word": round(expected, 1),
        "normalized_deviations": deviations,
        "max_abs_normalized_deviation": max(
            abs(d) for d in deviations.values()
        ),
        "descent_violations": descent_violations,
    }


def _pow2root_scaled(x: int, num: int, den: int, scale: int = SCALE) -> int:
    """floor(x^{num/den} * scale) for den a power of two, exact isqrt only."""
    val = x**num * scale**den
    while den > 1:
        val = isqrt(val)
        den //= 2
    return val


def eighth_letter_chain_check(n: int, scale: int = SCALE) -> dict[str, Any]:
    """Exact scaled validation of the OOEOOEO* eighth-letter chain.

    On the OOEOOEO pattern (x_t via itinerary_orbit) the eighth-letter
    phase argument x8 = x7^{3/2} linearizes down all six levels:

      x8 = n^{243/128}
           - (81/64) n^{51/128} theta_1      (theta_1 = n^{3/2} - x2)
           - (27/32) Y2^{-5/32}  theta_2     (Y2 = x2^{3/2}, x3 = floor(Y2))
           - (27/16) U3^{11/16}  theta_3     (U3 = x3^{1/2}, x4 = floor(U3))
           - (9/8)   Y4^{1/8}    theta_4     (Y4 = x4^{3/2}, x5 = floor(Y4))
           - (3/4)   Y5^{-1/4}   theta_5     (Y5 = x5^{3/2}, x6 = floor(Y5))
           - (3/2)   x6^{1/4}    theta_6     (U6 = x6^{1/2}, x7 = floor(U6))
           + E,

    where E is a sum of six one-signed second-order Taylor remainders,
    |E| < 1 for all n >= 51. Every sawtooth coefficient is subcritical:
    the largest is (27/16) U3^{11/16} ~ n^{99/128} << n, with drift
    n^{-29/128} < 1. Returns the scaled residual, the two-sided
    envelope, and the measured coefficient exponents.
    """
    if n < 51 or n % 2 == 0:
        raise ValueError("odd n >= 51 required")
    xs = word_orbit(n, "OOEOOEO" + "E")
    x2, x3, x4, x5, x6, x7 = xs[1], xs[2], xs[3], xs[4], xs[5], xs[6]

    th1 = isqrt(n**3 * scale * scale) - x2 * scale
    th2 = isqrt(x2**3 * scale * scale) - x3 * scale
    th3 = isqrt(x3 * scale * scale) - x4 * scale
    th4 = isqrt(x4**3 * scale * scale) - x5 * scale
    th5 = isqrt(x5**3 * scale * scale) - x6 * scale
    th6 = isqrt(x6 * scale * scale) - x7 * scale

    main = _pow2root_scaled(n, 243, 128, scale)
    c1 = _pow2root_scaled(n, 51, 128, scale)
    t1 = 81 * c1 * th1 // (64 * scale)
    y2_532 = _pow2root_scaled(x2, 15, 64, scale)
    t2 = 27 * th2 * scale // (32 * y2_532)
    c3 = _pow2root_scaled(x3, 11, 32, scale)
    t3 = 27 * c3 * th3 // (16 * scale)
    c4 = _pow2root_scaled(x4, 3, 16, scale)
    t4 = 9 * c4 * th4 // (8 * scale)
    y5_14 = _pow2root_scaled(x5, 3, 8, scale)
    t5 = 3 * th5 * scale // (4 * y5_14)
    c6 = _pow2root_scaled(x6, 1, 4, scale)
    t6 = 3 * c6 * th6 // (2 * scale)

    x8 = isqrt(x7**3 * scale * scale)
    residual = x8 - (main - t1 - t2 - t3 - t4 - t5 - t6)

    # One-signed remainder envelopes (E1, E3, E4, E6 >= 0; E2, E5 <= 0).
    pos_env = (
        3 * scale // (8 * isqrt(x7 - 1))
        + 9 * scale // (128 * _pow2root_scaled(x5 - 1, 7, 8, 1))
        + 297 * scale // (512 * _pow2root_scaled(x4 - 1, 5, 16, 1))
        + 1377 * scale // (8192 * _pow2root_scaled(x2 - 1, 47, 64, 1))
    )
    neg_env = (
        3 * scale // (32 * _pow2root_scaled(x6 - 1, 5, 4, 1))
        + 135 * scale // (2048 * _pow2root_scaled(x3 - 1, 37, 32, 1))
    )
    slack = 64 * ((c1 + c3 + c4 + c6) // scale + 8)
    ln = log(n)
    exponents = {
        "theta1": round(log(81 * c1 / (64 * scale)) / ln, 4),
        "theta3": round(log(27 * c3 / (16 * scale)) / ln, 4),
        "theta4": round(log(9 * c4 / (8 * scale)) / ln, 4),
        "theta6": round(log(3 * c6 / (2 * scale)) / ln, 4),
    }
    return {
        "holds": -neg_env - slack <= residual <= pos_env + slack,
        "residual_scaled": residual,
        "pos_env_scaled": pos_env,
        "neg_env_scaled": neg_env,
        "coefficient_exponents": exponents,
        "all_subcritical": max(exponents.values()) < 1.0,
    }


def depth8_chain_scan(samples: tuple[int, ...]) -> dict[str, Any]:
    """Run the eighth-letter chain check over odd samples."""
    worst_exp = 0.0
    for n in samples:
        row = eighth_letter_chain_check(n)
        if not row["holds"] or not row["all_subcritical"]:
            return {"holds": False, "witness": n, "row": row}
        worst_exp = max(worst_exp, max(row["coefficient_exponents"].values()))
    return {"holds": True, "count": len(samples), "max_exponent": worst_exp}


def eighth_remainder_rate_scan(samples: tuple[int, ...]) -> dict[str, Any]:
    """Phase 40: |E| tracks n^{-45/128}; finite-difference E' tracks n^{-29/128}.

    On the OOEOOEO formal chain the AA1 remainder E is the
    scaled residual of eighth_letter_chain_check. The leading
    Taylor envelope is the x4^{-5/16} term ≍ n^{-45/128}.
    Returns whether every sample lies inside the one-sided
    envelopes with no slack, the max |E| n^{45/128} ratio,
    and the max |ΔE/2| n^{29/128} drift ratio.
    """
    max_size_ratio = 0.0
    max_drift_ratio = 0.0
    outside = 0
    for n in samples:
        if n < 51 or n % 2 == 0:
            raise ValueError("odd n >= 51 required")
        row = eighth_letter_chain_check(n)
        e = row["residual_scaled"] / SCALE
        pos = row["pos_env_scaled"] / SCALE
        neg = row["neg_env_scaled"] / SCALE
        if not (-neg <= e <= pos):
            outside += 1
        size_ratio = abs(e) * (n ** (45 / 128))
        e2 = eighth_letter_chain_check(n + 2)["residual_scaled"] / SCALE
        drift_ratio = abs(e2 - e) / 2.0 * (n ** (29 / 128))
        max_size_ratio = max(max_size_ratio, size_ratio)
        max_drift_ratio = max(max_drift_ratio, drift_ratio)
    return {
        "holds": (
            outside == 0
            and max_size_ratio < 1.0
            and max_drift_ratio < 1.0
        ),
        "count": len(samples),
        "outside_envelope": outside,
        "max_size_ratio": round(max_size_ratio, 4),
        "max_drift_ratio": round(max_drift_ratio, 4),
    }


def depth8_mode_probe(n_max: int, k: int = 1) -> dict[str, Any]:
    """Eighth-wave mode sums on the four parent cylinders.

    For each counted expanding length-7 cylinder, sums
    e((k/2) X7(n)) over cylinder members n <= n_max, where
    X7 = x7^{3/2} (seventh letter O) or x7^{1/2} (seventh letter E)
    is the real number whose floor parity is the eighth letter.
    Cancellation (|S| << members) is the Phase-0 gate for the
    engine bound; ratio near 1 is the falsifier.
    """
    from math import cos, pi, sin

    sc = SCALE
    out: dict[str, Any] = {"n_max": n_max, "k": k}
    sums = {w[:7]: [0.0, 0.0, 0] for w in DEPTH8_QUARTET}
    for n in range(3, n_max + 1, 2):
        w7 = itinerary_word(n, 7)
        if w7 not in sums:
            continue
        x = n
        for _ in range(6):
            x = juggler_step(x)
        x7sc = isqrt(x**3 * sc * sc) if w7[6] == "O" else isqrt(x * sc * sc)
        frac = (k * x7sc) % (2 * sc)
        ph = pi * frac / sc
        acc = sums[w7]
        acc[0] += cos(ph)
        acc[1] += sin(ph)
        acc[2] += 1
    for w7, (re, im, cnt) in sums.items():
        out[w7] = {
            "members": cnt,
            "abs_sum": round((re * re + im * im) ** 0.5, 2),
            "ratio": round((re * re + im * im) ** 0.5 / max(cnt, 1), 4),
        }
    return out


def transport_block_variance(
    p_block: int,
    block_len: int = 256,
    max_blocks: int = 200,
    r_modes: tuple[int, ...] = (1, 2, 4, 8),
    auto_lags: tuple[int, ...] = (1, 2, 4, 8),
) -> dict[str, Any]:
    """Phase-0 falsifier for the L2-transport attack (block randomness).

    The transport route needs level-3 defects to be block-random: for
    most consecutive blocks B of odd n, (a) the block mode sums
    S_r(B) = sum_{n in B} e(r theta_3) have mean square ~ |B| (the
    random-phase scale), and (b) the fifth letter eps5 = parity of
    floor(z^{3/2}) has block variance ~ |B| and no short-lag
    autocorrelation. Systematic block coherence (variance ratio >> 1)
    kills the route. OBSERVATION-level evidence only.
    """
    from math import cos, pi, sin

    s12 = 10**12
    max_lag = max(auto_lags)
    need = block_len * max_blocks + max_lag
    th3s: list[float] = []
    eps5: list[int] = []
    n = p_block + 1
    while n < 2 * p_block and len(th3s) < need:
        v = isqrt(isqrt(n**3) ** 3)
        z = isqrt(v**3)
        t3 = isqrt(v**3 * s12 * s12)
        th3s.append((t3 - z * s12) / s12)
        eps5.append(1 if isqrt(z**3) % 2 == 1 else -1)
        n += 2
    n_blocks = min(max_blocks, (len(th3s) - max_lag) // block_len)
    total = n_blocks * block_len

    var_ratio: dict[str, float] = {}
    for r in r_modes:
        acc = 0.0
        for b in range(n_blocks):
            re = im = 0.0
            for i in range(b * block_len, (b + 1) * block_len):
                ph = 2 * pi * r * th3s[i]
                re += cos(ph)
                im += sin(ph)
            acc += re * re + im * im
        var_ratio[f"r={r}"] = round(acc / (n_blocks * block_len), 3)

    acc = 0.0
    for b in range(n_blocks):
        t = sum(eps5[b * block_len : (b + 1) * block_len])
        acc += t * t
    letter_ratio = acc / (n_blocks * block_len)

    autocorr: dict[str, float] = {}
    for h in auto_lags:
        a = sum(eps5[i] * eps5[i + h] for i in range(total))
        autocorr[f"h={h}"] = round(a / total, 4)

    return {
        "block_len": block_len,
        "n_blocks": n_blocks,
        "mode_variance_ratio": var_ratio,
        "letter_variance_ratio": round(letter_ratio, 3),
        "letter_autocorr": autocorr,
        "noise_floor": round(total**-0.5, 4),
    }


def level3_raw_gap_wildness(p_block: int, window: int = 80) -> dict[str, Any]:
    """Raw third/fourth differences of Z = v^{3/2} are not frozen.

    The smooth model G(n) = n^{27/8} has G''' ≍ P^{3/8} ≫ 1 and
    G^{(4)} ≍ P^{-5/8} ≪ 1, so three Weyl steps freeze the smooth
    content. The discrete Z inherits jumps from both inner floors
    (m and v), and |Δ⁴ Z| stays ≫ 1 — the Phase-8 raw-freeze
    falsifier one layer up. A freeze argument that ignores the
    nested carry lattice is dead on arrival.
    """
    s = 10**12
    step = 2

    def z_real(x: int) -> float:
        v = isqrt(isqrt(x**3) ** 3)
        return isqrt(v**3 * s * s) / s

    d3s: list[float] = []
    d4s: list[float] = []
    n = p_block + 1
    for _ in range(window):
        vals = [z_real(n + k * step) for k in range(5)]
        d3s.append(abs(vals[3] - 3 * vals[2] + 3 * vals[1] - vals[0]))
        d4s.append(
            abs(vals[4] - 4 * vals[3] + 6 * vals[2] - 4 * vals[1] + vals[0])
        )
        n += 2
    d3_mean = sum(d3s) / len(d3s)
    d4_mean = sum(d4s) / len(d4s)
    pred3 = (27 / 8) * (19 / 8) * (11 / 8) * p_block ** (3 / 8) * step**3
    return {
        "window": window,
        "d3_mean": round(d3_mean, 3),
        "d4_mean": round(d4_mean, 3),
        "smooth_d3_pred": round(pred3, 3),
        "raw_d4_wild": d4_mean > 1.0,
        "d3_above_smooth": d3_mean > 10 * pred3,
    }


def oooo_indicator_identity_check(n_max: int) -> dict[str, Any]:
    """Branch consistency: OOOO* fifth letter is parity of isqrt(z^3)."""
    checked = 0
    for n in range(3, n_max + 1, 2):
        word = itinerary_word(n, 5)
        if not word.startswith("OOOO"):
            continue
        m = isqrt(n**3)
        v = isqrt(m**3)
        z = isqrt(v**3)
        expected = "OOOO" + ("O" if isqrt(z**3) % 2 == 1 else "E")
        if word != expected:
            return {"holds": False, "witness": n}
        checked += 1
    return {"holds": True, "checked": checked, "n_max": n_max}


def level3_inner_linearization_check(
    n: int, scale: int = 10**40
) -> tuple[int, int]:
    """(E*scale, bound*scale) for the forced inner linearization (V2).

    v^{3/2} = m^{9/4} - (3/2) m^{3/4} theta_2 + E, with
    0 ≤ E ≤ (3/8) v^{-1/2} (Taylor of (Y - theta_2)^{3/2} at Y).
    The main term produces the W-family phase C theta_2 with
    C = (3c/2) m^{3/4} ≍ k n^{45/16} once the outer coefficient
    c ≍ k z^{1/2} is restored — past the engine line α = 9/4 of
    Theorem R's Step-3 θ-coefficients.
    """
    if n < 5 or n % 2 == 0:
        raise ValueError("odd n >= 5 required")
    m = isqrt(n**3)
    v = isqrt(m**3)
    v32 = isqrt(v**3 * scale * scale)
    m94 = isqrt(isqrt(m**9 * scale**4))
    m34 = isqrt(isqrt(m**3 * scale**4))
    th2 = isqrt(m**3 * scale * scale) - v * scale
    err = v32 - m94 + (3 * m34 * th2) // (2 * scale)
    v12 = isqrt(v * scale * scale)
    slack = isqrt(v) + 10**6
    bound = (3 * scale * scale) // (8 * v12) + slack
    return err, bound


def level3_inner_linearization_scan(samples: tuple[int, ...]) -> dict[str, Any]:
    slack = 10**7
    for n in samples:
        err, bound = level3_inner_linearization_check(n)
        if err < -slack or err > bound:
            return {"holds": False, "witness": n}
    return {"holds": True, "count": len(samples)}


def v_level_cell_scan(p_block: int, window: int = 400) -> dict[str, Any]:
    """Run lengths of floor(ΔY) and Δv at step 2.

    Theorem R needs b-runs of floor(ΔX) of length ≍ P^{1/2}/h.
    The v-level analogue — runs of floor(ΔY) or of Δv — has mean
    length 1 at every tested scale: Y' ≍ P^{5/4} so the first
    difference of Y changes by ≍ P^{1/4} ≫ 1 at every step.
    A copy of Lemma R3 at the v-level cannot even be stated.
    """
    s = 10**12

    def y_scaled(x: int) -> int:
        return isqrt(isqrt(x**3) ** 3 * s * s)

    def v_of(x: int) -> int:
        return isqrt(isqrt(x**3) ** 3)

    floor_runs: list[int] = []
    dv_runs: list[int] = []
    prev_f = prev_dv = None
    f_run = dv_run = 0
    n = p_block + 1
    for _ in range(window):
        floor_dy = (y_scaled(n + 2) - y_scaled(n)) // s
        dv = v_of(n + 2) - v_of(n)
        if prev_f is None or floor_dy != prev_f:
            if f_run:
                floor_runs.append(f_run)
            f_run = 1
            prev_f = floor_dy
        else:
            f_run += 1
        if prev_dv is None or dv != prev_dv:
            if dv_run:
                dv_runs.append(dv_run)
            dv_run = 1
            prev_dv = dv
        else:
            dv_run += 1
        n += 2
    if f_run:
        floor_runs.append(f_run)
    if dv_run:
        dv_runs.append(dv_run)
    return {
        "window": window,
        "floor_dY_mean_run": sum(floor_runs) / len(floor_runs),
        "floor_dY_max_run": max(floor_runs),
        "dv_mean_run": sum(dv_runs) / len(dv_runs),
        "dv_max_run": max(dv_runs),
        "no_v_level_cells": max(floor_runs) == 1 and max(dv_runs) == 1,
    }


def increment_linearization_check(
    n: int, scale: int = 10**24
) -> tuple[int, int]:
    """(E*scale, bound*scale) for the increment identity (Z1).

    F_J(y) = (y+J)^{3/2} - y^{3/2} at J = Δv (step 2). Taylor in the
    single variable θ₂ = {Y} at fixed J:

        F_J(v) = F_J(Y) - F_J'(Y) θ₂ + R_J,

    equivalently E = F_J(Y) - F_J(v) - F_J'(Y) θ₂ satisfies
    0 ≤ E ≤ (3/8) v^{-1/2} (F_J'' < 0, ξ ≥ v). Restoring
    c ≍ k z^{1/2} leaves a W-family C θ₂ with
    C = c F_J'(Y) ≍ k n^{29/16} at the identity-step gap, plus an
    engine-side remainder. An algebraic identity only: it does not
    produce runs on which J is frozen.
    """
    if n < 5 or n % 2 == 0:
        raise ValueError("odd n >= 5 required")
    d = 2
    m = isqrt(n**3)
    v = isqrt(m**3)
    J = isqrt(isqrt((n + d) ** 3) ** 3) - v
    if J <= 0:
        raise ValueError("positive increment J required")
    ys = isqrt(m**3 * scale * scale)
    fv = isqrt((v + J) ** 3 * scale * scale) - isqrt(v**3 * scale * scale)
    fy = isqrt((ys + J * scale) ** 3 // scale) - isqrt(ys**3 // scale)
    y12 = isqrt(ys * scale)
    yj12 = isqrt((ys + J * scale) * scale)
    fp = (3 * (yj12 - y12)) // 2
    th2 = ys - v * scale
    err = fy - fv - (fp * th2) // scale
    v12 = isqrt(v * scale * scale)
    slack = isqrt(max(v, 1)) + 10**6
    bound = (3 * scale * scale) // (8 * max(v12, 1)) + slack
    return err, bound


def increment_linearization_scan(samples: tuple[int, ...]) -> dict[str, Any]:
    slack = 10**7
    checked = 0
    for n in samples:
        try:
            err, bound = increment_linearization_check(n)
        except ValueError:
            continue
        if err < -slack or err > bound:
            return {"holds": False, "witness": n, "err": err, "bound": bound}
        checked += 1
    return {"holds": True, "count": checked}


def increment_j_derivative_check(n: int) -> dict[str, float]:
    """c (F_{J+1}(v) - F_J(v)) / n^{45/16} against the limit 9/8.

    ∂F_J/∂J = (3/2)(v+J)^{1/2}, so unfreezing J by 1 produces the
    Phase-12 leftover c · (3/2) v^{1/2} ≍ n^{45/16}. Scaled integers
    (float only in the final ratio).
    """
    if n < 5 or n % 2 == 0:
        raise ValueError("odd n >= 5 required")
    m = isqrt(n**3)
    v = isqrt(m**3)
    z = isqrt(v**3)
    J = isqrt(isqrt((n + 2) ** 3) ** 3) - v
    if J <= 0:
        raise ValueError("positive increment J required")
    s = 10**12
    df = isqrt((v + J + 1) ** 3 * s * s) - isqrt((v + J) ** 3 * s * s)
    c = (3 * isqrt(z * s * s)) // 4
    phase = c * df
    # n^{45/16} s^2 = n^2 n^{13/16} s^2
    n13s = isqrt(isqrt(isqrt(isqrt(n**13 * s**16))))
    target = (9 * (n**2) * n13s * s) // 8
    ratio = phase / target if target else 0.0
    return {
        "n": float(n),
        "J": float(J),
        "ratio": ratio,
        "limit": 1.0,
    }


def increment_j_derivative_scan(samples: tuple[int, ...]) -> dict[str, Any]:
    """The J-derivative ratio stays near 9/8 through the sample."""
    ratios = []
    for n in samples:
        try:
            row = increment_j_derivative_check(n)
        except ValueError:
            continue
        if not (0.99 <= row["ratio"] <= 1.02):
            return {"holds": False, "witness": n, "ratio": row["ratio"]}
        ratios.append(row["ratio"])
    return {"holds": True, "count": len(ratios), "ratios": ratios}


def x_cell_increment_scan(
    p_block: int, window: int = 400, h: int = 1
) -> dict[str, Any]:
    """Run lengths of floor(ΔY) and Δv *inside* X-cell b-runs.

    The increment-first attack needs frozen J = floor(ΔY) on
    b-runs of floor(Δ_h X) (length ≍ P^{1/2}/h). On those cells
    m advances by b ≍ h P^{1/2} per step, while the m-freeze
    length of floor((m+b)^{3/2}-m^{3/2}) is ≍ P^{1/4}/h, and
    P^{1/2} > P^{1/4}: J changes at every in-cell step. Measured
    mean and max run 1, with mean |Δ floor(ΔY)| ≍ P^{1/4}.
    """
    d = 2 * h
    s = 10**12

    def floor_dx(n: int) -> int:
        # Real gap floor(ΔX), not Δm = floor(ΔX)+κ (the carry flickers).
        return (
            isqrt((n + d) ** 3 * s * s) - isqrt(n**3 * s * s)
        ) // s

    def floor_dy(n: int) -> int:
        m = isqrt(n**3)
        m1 = isqrt((n + d) ** 3)
        return (isqrt(m1**3 * s * s) - isqrt(m**3 * s * s)) // s

    def dv_of(n: int) -> int:
        return isqrt(isqrt((n + d) ** 3) ** 3) - isqrt(isqrt(n**3) ** 3)

    def branch_floor(m: int, gap: int) -> int:
        return (isqrt((m + gap) ** 3 * s * s) - isqrt(m**3 * s * s)) // s

    floor_runs: list[int] = []
    dv_runs: list[int] = []
    b_runs: list[int] = []
    branch_runs: dict[int, list[int]] = {0: [], 1: []}
    dy_changes: list[int] = []
    current_b: int | None = None
    b_run = 0
    prev_f = prev_dv = None
    prev_br: dict[int, int | None] = {0: None, 1: None}
    br_run = {0: 0, 1: 0}
    f_run = dv_run = 0
    last_dy: int | None = None
    n = p_block + 1
    for _ in range(window):
        b = floor_dx(n)
        if current_b is None:
            current_b = b
            b_run = 1
        elif b != current_b:
            if f_run:
                floor_runs.append(f_run)
            if dv_run:
                dv_runs.append(dv_run)
            if b_run:
                b_runs.append(b_run)
            for kap in (0, 1):
                if br_run[kap]:
                    branch_runs[kap].append(br_run[kap])
                br_run[kap] = 0
                prev_br[kap] = None
            f_run = dv_run = 0
            prev_f = prev_dv = None
            last_dy = None
            current_b = b
            b_run = 1
        else:
            b_run += 1
        fdY = floor_dy(n)
        dvt = dv_of(n)
        m = isqrt(n**3)
        if last_dy is not None:
            dy_changes.append(abs(fdY - last_dy))
        last_dy = fdY
        if prev_f is None or fdY != prev_f:
            if f_run:
                floor_runs.append(f_run)
            f_run = 1
            prev_f = fdY
        else:
            f_run += 1
        if prev_dv is None or dvt != prev_dv:
            if dv_run:
                dv_runs.append(dv_run)
            dv_run = 1
            prev_dv = dvt
        else:
            dv_run += 1
        for kap in (0, 1):
            bf = branch_floor(m, b + kap)
            if prev_br[kap] is None or bf != prev_br[kap]:
                if br_run[kap]:
                    branch_runs[kap].append(br_run[kap])
                br_run[kap] = 1
                prev_br[kap] = bf
            else:
                br_run[kap] += 1
        n += 2
    if f_run:
        floor_runs.append(f_run)
    if dv_run:
        dv_runs.append(dv_run)
    if b_run:
        b_runs.append(b_run)
    for kap in (0, 1):
        if br_run[kap]:
            branch_runs[kap].append(br_run[kap])
    branch_max = max(
        (max(branch_runs[k]) for k in (0, 1) if branch_runs[k]),
        default=0,
    )
    return {
        "window": window,
        "n_b_runs": len(b_runs),
        "b_run_max": max(b_runs) if b_runs else 0,
        "b_run_mean": (sum(b_runs) / len(b_runs)) if b_runs else 0.0,
        "floor_dY_mean_run": (
            sum(floor_runs) / len(floor_runs) if floor_runs else 0.0
        ),
        "floor_dY_max_run": max(floor_runs) if floor_runs else 0,
        "dv_mean_run": sum(dv_runs) / len(dv_runs) if dv_runs else 0.0,
        "dv_max_run": max(dv_runs) if dv_runs else 0,
        "branch_j_max_run": branch_max,
        "mean_abs_d_floor_dY": (
            sum(dy_changes) / len(dy_changes) if dy_changes else 0.0
        ),
        "pred_P14": p_block**0.25,
        "no_j_runs_on_x_cells": (
            bool(floor_runs)
            and bool(dv_runs)
            and max(floor_runs) == 1
            and max(dv_runs) == 1
            and branch_max == 1
            and max(b_runs) >= 2
        ),
    }


def x1_landing_gap_scan(p_block: int, window: int = 400) -> dict[str, Any]:
    """X1 landing criterion: which integers have frozen first gaps?

    X1 writes C{F} = C F - C floor(F). The integer I = floor(F)
    has a usable frozen gap iff floor(ΔF) is constant on long
    runs, which requires F'' < 1. Controls: floor(Δ v^{1/2}) and
    floor(Δ m^{1/2}) freeze on the whole window (F'' < 1). The
    K3 leftover is {Y}, Y'' ≍ P^{1/4} > 1: floor(ΔY) and Δv have
    run length 1. Hybrids v - w_m^3, v - m w_m, v - w^2 also
    have run length 1 — subtracting a freezing polynomial does
    not create a v-level cell.
    """
    s = 10**12
    d = 2

    def tower(n: int) -> tuple[int, int, int, int]:
        m = isqrt(n**3)
        v = isqrt(m**3)
        w = isqrt(v)
        wm = isqrt(m)
        return m, v, w, wm

    def floor_d_real(a: int, b: int) -> int:
        return (isqrt(b * s * s) - isqrt(a * s * s)) // s

    keys = (
        "floor_dY",
        "dv",
        "floor_dU",
        "floor_dWm",
        "d_v_minus_wm3",
        "d_v_minus_m_wm",
        "d_v_minus_w2",
    )
    runs: dict[str, list[int]] = {k: [] for k in keys}
    cur = {k: 0 for k in keys}
    last: dict[str, int | None] = {k: None for k in keys}
    n = p_block + 1
    for _ in range(window):
        m, v, w, wm = tower(n)
        m1, v1, w1, wm1 = tower(n + d)
        deltas = {
            "floor_dY": (isqrt(m1**3 * s * s) - isqrt(m**3 * s * s)) // s,
            "dv": v1 - v,
            "floor_dU": floor_d_real(v, v1),
            "floor_dWm": floor_d_real(m, m1),
            "d_v_minus_wm3": (v1 - wm1**3) - (v - wm**3),
            "d_v_minus_m_wm": (v1 - m1 * wm1) - (v - m * wm),
            "d_v_minus_w2": (v1 - w1**2) - (v - w**2),
        }
        for k, val in deltas.items():
            if last[k] is None or val != last[k]:
                if cur[k]:
                    runs[k].append(cur[k])
                cur[k] = 1
                last[k] = val
            else:
                cur[k] += 1
        n += 2
    for k in keys:
        if cur[k]:
            runs[k].append(cur[k])

    def stats(k: str) -> dict[str, float]:
        r = runs[k]
        return {
            "mean": (sum(r) / len(r)) if r else 0.0,
            "max": float(max(r)) if r else 0.0,
        }

    out: dict[str, Any] = {k: stats(k) for k in keys}
    out["window"] = window
    out["slow_floors_frozen"] = (
        out["floor_dU"]["mean"] >= 8 and out["floor_dWm"]["mean"] >= 8
    )
    out["y_and_hybrids_unfrozen"] = (
        out["floor_dY"]["max"] == 1.0
        and out["dv"]["max"] == 1.0
        and out["d_v_minus_wm3"]["max"] == 1.0
        and out["d_v_minus_m_wm"]["max"] == 1.0
        and out["d_v_minus_w2"]["max"] == 1.0
    )
    return out


def v2_amplitude_drift_check(n: int) -> dict[str, float]:
    """ΔC / n^{29/16} against (405/64) = 6.328125.

    C = (9/8) z^{1/2} m^{3/4} is the V2 leftover coefficient
    (α = 45/16). Then C(n+2)-C(n) ~ 2 C' ~ (45/8)(9/8) n^{29/16}
    = (405/64) n^{29/16}. The amplitude itself jumps by
    ≫ 1 per step, so Theorem R's quasi-static window
    bookkeeping cannot be run at this α, even if the engine
    line moved from 9/4 toward 2.
    """
    if n < 5 or n % 2 == 0:
        raise ValueError("odd n >= 5 required")

    def coeff(x: int) -> float:
        m = isqrt(x**3)
        v = isqrt(m**3)
        z = isqrt(v**3)
        return (9 / 8) * (z**0.5) * (m**0.75)

    delta = coeff(n + 2) - coeff(n)
    ratio = delta / n ** (29 / 16)
    return {"n": float(n), "ratio": ratio, "limit": 405 / 64}


def v2_amplitude_drift_scan(samples: tuple[int, ...]) -> dict[str, Any]:
    ratios = []
    for n in samples:
        row = v2_amplitude_drift_check(n)
        if not (6.0 <= row["ratio"] <= 6.6):
            return {"holds": False, "witness": n, "ratio": row["ratio"]}
        ratios.append(row["ratio"])
    return {"holds": True, "count": len(ratios), "ratios": ratios}


# --- Phase 13: length-7 engine contractors (OOEOOEE, OOOEOEE) ---


def sixth_ooeoo_check(n: int, scale: int = SCALE) -> tuple[int, int]:
    """(E*scale, bound*scale) for the OOEOO* sixth-letter rearrangement.

    p = floor(w^{3/2}), w = floor(v^{1/2}):
    p^{3/2} = -(5/4) v^{9/8} + (9/4) w v^{5/8} - (3/2) w^{3/4} theta_p + E
    with 0 ≤ E ≤ (3/8) p^{-1/2} + (45/32) v^{1/8} (Taylor remainders
    of (W - theta_p)^{3/2} and (U - theta_w)^{9/4}). The naive
    theta_w coefficient n^{45/32} is absorbed into the integer w;
    no supercritical sawtooth remains.
    """
    if n < 5 or n % 2 == 0:
        raise ValueError("odd n >= 5 required")
    m = isqrt(n**3)
    v = isqrt(m**3)
    w = isqrt(v)
    p = isqrt(w**3)
    p32 = isqrt(p**3 * scale * scale)
    v98 = _eighth_scaled(v**9, scale)
    v58 = _eighth_scaled(v**5, scale)
    w34 = isqrt(isqrt(w**3 * scale**4))
    th_p = isqrt(w**3 * scale * scale) - p * scale
    err = p32 + (5 * v98) // 4 - (9 * w * v58) // 4 + (
        3 * w34 * th_p
    ) // (2 * scale)
    p12 = isqrt(p * scale * scale)
    v18 = _eighth_scaled(v, scale)
    bound = (
        3 * scale * scale // (8 * max(p12, 1))
        + (45 * v18) // 32
        + isqrt(max(v, 1))
        + 10**6
    )
    return err, bound


def sixth_ooeoo_scan(samples: tuple[int, ...]) -> dict[str, Any]:
    slack = 10**7
    for n in samples:
        err, bound = sixth_ooeoo_check(n)
        if err < -slack or err > bound:
            return {"holds": False, "witness": n, "err": err, "bound": bound}
    return {"holds": True, "count": len(samples)}


def x1_remainder_reduction_scan(samples: tuple[int, ...]) -> dict[str, Any]:
    """Seal for Part XIV: {v^{1/2}} tracks {n^{9/8}} to O(n^{-3/8}).

    On the OO prefix, v = floor(m^{3/2}) with m = floor(n^{3/2}), so
    v^{1/2} = n^{9/8} - (3/4) n^{-3/8} theta_2 + O(n^{-9/8}). The
    fractional parts therefore differ by O(n^{-3/8}) except when
    {n^{9/8}} is within that of an integer (one-step wrap). Float
    seal only; n <= 10^6 keeps sqrt(v) inside the 53-bit mantissa.
    """
    near = 0
    far_ok = 0
    far_fail = 0
    max_far = 0.0
    for n in samples:
        if n < 5 or n % 2 == 0 or n > 10**6:
            continue
        m = isqrt(n * n * n)
        v = isqrt(m * m * m)
        w = isqrt(v)
        frac_u = sqrt(v) - w
        n98 = n ** (9 / 8)
        frac_n = n98 - floor(n98)
        delta = abs(frac_u - frac_n)
        delta = min(delta, 1.0 - delta)
        thresh = 2.0 * n ** (-3 / 8) + 0.05
        if min(frac_n, 1.0 - frac_n) < n ** (-3 / 8) + 0.02:
            near += 1
            continue
        if delta <= thresh:
            far_ok += 1
            if delta > max_far:
                max_far = delta
        else:
            far_fail += 1
            return {
                "holds": False,
                "witness": n,
                "delta": delta,
                "thresh": thresh,
            }
    return {
        "holds": far_fail == 0 and far_ok > 0,
        "far_ok": far_ok,
        "near_integer": near,
        "max_far_delta": max_far,
    }


def sixth_oooeo_check(n: int, scale: int = SCALE) -> tuple[int, int]:
    """(E*scale, bound*scale) for the OOOEO* sixth-letter A' form.

    s = floor(z^{1/2}), z = floor(v^{3/2}):
    s^{3/2} = -(1/2) z^{3/4} + (3/2) s z^{1/4} + E,
    0 ≤ E ≤ (3/8)(U-1)^{-1/2}, U = z^{1/2}. Lemma A' at base z.
    """
    if n < 5 or n % 2 == 0:
        raise ValueError("odd n >= 5 required")
    m = isqrt(n**3)
    v = isqrt(m**3)
    z = isqrt(v**3)
    s = isqrt(z)
    t = isqrt(s**3 * scale * scale)
    z34 = isqrt(isqrt(z**3 * scale**4))
    z14 = isqrt(isqrt(z * scale**4))
    err = t + z34 // 2 - (3 * s * z14) // 2
    u = max(s, 2)
    # Floor slack: z14 error O(1) times (3/2)s ~ n^{27/16}.
    slack = 2 * s + 10**6
    bound = 3 * scale // (8 * isqrt(u - 1)) + slack
    return err, bound


def sixth_oooeo_scan(samples: tuple[int, ...]) -> dict[str, Any]:
    slack = 10**7
    for n in samples:
        err, bound = sixth_oooeo_check(n)
        if err < -slack or err > bound:
            return {"holds": False, "witness": n, "err": err, "bound": bound}
    return {"holds": True, "count": len(samples)}


def w_gap_freeze_scan(p_block: int, window: int = 400) -> dict[str, Any]:
    """floor(Δ v^{1/2}) freezes on the OOEO cylinder (long runs).

    Predicted run length ≍ P^{7/8}: (v^{1/2})'' ≍ P^{-7/8} < 1.
    The integer first gap of w is this frozen floor plus a 0/1 carry.
    """
    s = 10**12
    runs: list[int] = []
    prev = None
    run = 0
    n = p_block + 1
    got = 0
    while got < window and n < 20 * p_block:
        m = isqrt(n**3)
        if m % 2 == 0:
            n += 2
            continue
        v = isqrt(m**3)
        if v % 2 == 1:
            n += 2
            continue
        u0 = isqrt(v * s * s)
        n2 = n + 2
        v2 = isqrt(isqrt(n2**3) ** 3)
        u1 = isqrt(v2 * s * s)
        floor_du = (u1 - u0) // s
        if prev is None or floor_du != prev:
            if run:
                runs.append(run)
            run = 1
            prev = floor_du
        else:
            run += 1
        got += 1
        n += 2
    if run:
        runs.append(run)
    return {
        "got": got,
        "mean_run": sum(runs) / len(runs) if runs else 0.0,
        "max_run": max(runs) if runs else 0,
        "n_runs": len(runs),
        "frozen": bool(runs) and (sum(runs) / len(runs) >= 8),
    }


def w_carry_run_scan(p_block: int, window: int = 400) -> dict[str, Any]:
    """kappa_w run length on OOEO, interior of frozen floor(dU) runs.

    Lemma X3 freezes J = floor(Delta v^{1/2}). The carry is
    kappa_w = Delta w - J in {0, 1}. U' ~ P^{1/8} >> 1, so {U}
    rotates by {Delta U} each odd step. On the interior of a
    J-run, {Delta U} is bounded away from the wrap, and kappa
    cannot stay constant on the A-process window H ~ P^{5/32}.
    """
    s = 10**12
    records: list[tuple[int, int]] = []
    n = p_block + 1
    got = 0
    while got < window and n < 20 * p_block:
        m = isqrt(n**3)
        if m % 2 == 0:
            n += 2
            continue
        v = isqrt(m**3)
        if v % 2 == 1:
            n += 2
            continue
        w = isqrt(v)
        u0 = isqrt(v * s * s)
        n2 = n + 2
        v2 = isqrt(isqrt(n2**3) ** 3)
        w2 = isqrt(v2)
        u1 = isqrt(v2 * s * s)
        floor_du = (u1 - u0) // s
        kappa = w2 - w - floor_du
        records.append((floor_du, kappa))
        got += 1
        n += 2

    j_runs: list[list[int]] = []
    current: list[int] = []
    prev_j = None
    for floor_du, kappa in records:
        if prev_j is None or floor_du != prev_j:
            if current:
                j_runs.append(current)
            current = [kappa]
            prev_j = floor_du
        else:
            current.append(kappa)
    if current:
        j_runs.append(current)

    kappa_runs: list[int] = []
    interior_terms = 0
    for run in j_runs:
        if len(run) < 10:
            continue
        interior = run[2:-2]
        interior_terms += len(interior)
        prev = None
        length = 0
        for kap in interior:
            if prev is None or kap != prev:
                if length:
                    kappa_runs.append(length)
                length = 1
                prev = kap
            else:
                length += 1
        if length:
            kappa_runs.append(length)

    h_proxy = max(1, int(p_block ** (5 / 32)))
    max_kappa = max(kappa_runs) if kappa_runs else 0
    mean_kappa = sum(kappa_runs) / len(kappa_runs) if kappa_runs else 0.0
    kappa_vals = {kap for _, kap in records}
    return {
        "got": got,
        "n_j_runs": len(j_runs),
        "j_mean_run": (
            sum(len(r) for r in j_runs) / len(j_runs) if j_runs else 0.0
        ),
        "j_max_run": max((len(r) for r in j_runs), default=0),
        "interior_terms": interior_terms,
        "kappa_mean_run": mean_kappa,
        "kappa_max_run": max_kappa,
        "h_proxy": h_proxy,
        "kappa_binary": kappa_vals <= {0, 1},
        "no_affine_carry_freeze": bool(kappa_runs) and mean_kappa <= 4,
    }


def ooeooee_indicator_identity_check(n_max: int) -> dict[str, Any]:
    """Branch consistency: OOEOOEE is OOEOO plus even p^{3/2} and even q^{1/2}."""
    checked = 0
    for n in range(3, n_max + 1, 2):
        word = itinerary_word(n, 7)
        if not word.startswith("OOEOO"):
            continue
        m = isqrt(n**3)
        v = isqrt(m**3)
        w = isqrt(v)
        p = isqrt(w**3)
        q = isqrt(p**3)
        expected = (
            "OOEOO"
            + ("O" if q % 2 == 1 else "E")
            + ("O" if isqrt(q) % 2 == 1 else "E")
        )
        if q % 2 == 0:
            expected = "OOEOO" + "E" + ("O" if isqrt(q) % 2 == 1 else "E")
        else:
            expected = "OOEOO" + "O" + ("O" if isqrt(q**3) % 2 == 1 else "E")
        if word != expected:
            return {"holds": False, "witness": n, "got": word, "expected": expected}
        checked += 1
    return {"holds": True, "checked": checked, "n_max": n_max}


def oooeoee_indicator_identity_check(n_max: int) -> dict[str, Any]:
    """Branch consistency: OOOEO* sixth letter is parity of isqrt(s^3)."""
    checked = 0
    for n in range(3, n_max + 1, 2):
        word = itinerary_word(n, 7)
        if not word.startswith("OOOEO"):
            continue
        m = isqrt(n**3)
        v = isqrt(m**3)
        z = isqrt(v**3)
        s = isqrt(z)
        q = isqrt(s**3)
        if q % 2 == 0:
            expected = "OOOEO" + "E" + ("O" if isqrt(q) % 2 == 1 else "E")
        else:
            expected = "OOOEO" + "O" + ("O" if isqrt(q**3) % 2 == 1 else "E")
        if word != expected:
            return {"holds": False, "witness": n, "got": word, "expected": expected}
        checked += 1
    return {"holds": True, "checked": checked, "n_max": n_max}


def oeo_mode_probe(p_block: int) -> dict[str, Any]:
    """Float probe of the OEO* mode sum sum e((1/2) w^{3/2}) on n ~ P.

    Exact scaled phase; float only in the exponential. Cancellation
    here is what Theorem Q proves.
    """
    from math import cos, pi, sin

    s = 10**12
    re = im = 0.0
    cnt = 0
    n = p_block + 1
    while n < 2 * p_block:
        w = isqrt(isqrt(n**3))
        t_w = isqrt(w**3 * s * s)
        frac = (t_w % (2 * s)) / (2 * s)
        ph = 2 * pi * frac
        re += cos(ph)
        im += sin(ph)
        cnt += 1
        n += 2
    return {"count": cnt, "abs_sum": round((re * re + im * im) ** 0.5, 1)}


# --- Phase 5: even-branch third letter, tier-2 bricks, kernel probe ---


def m12_smoothing_check(n: int, scale: int = SCALE) -> tuple[int, int]:
    """(D1(n)*scale, bound*scale) for the OE-branch third-letter smoothing.

    Proposition L brick: m^{1/2} = n^{3/4} + D1(n) with
    -(1/2) n^{-3/4} - n^{-9/4} <= D1 <= 0, where m = floor(n^{3/2}).
    Decaying amplitudes only; same pattern as Lemma D.
    """
    if n < 3 or n % 2 == 0:
        raise ValueError("odd n >= 3 required")
    m = isqrt(n**3)
    m12 = isqrt(m * scale * scale)
    n34 = isqrt(isqrt(n**3 * scale**4))
    diff = m12 - n34
    r94 = isqrt(isqrt(n**9 * scale**4))
    bound = scale * scale // (2 * n34) + scale * scale // r94
    return diff, bound


def m12_scan(samples: tuple[int, ...]) -> dict[str, Any]:
    slack = 8
    for n in samples:
        diff, bound = m12_smoothing_check(n)
        if diff > slack or diff < -bound - slack:
            return {"holds": False, "witness": n}
    return {"holds": True, "count": len(samples)}


def oe_indicator_identity_check(n_max: int) -> dict[str, Any]:
    """Branch consistency for the OE-branch third letter.

    itinerary_word(n, 3) == 'OEE' iff m even and isqrt(m) even: the
    (1+psi_1) factor restricts to even m, exactly where J^2 takes the
    even branch, so psi(m^{1/2}) evaluates unconditionally.
    """
    for n in range(3, n_max + 1, 2):
        m = isqrt(n**3)
        if (itinerary_word(n, 3) == "OEE") != (m % 2 == 0 and isqrt(m) % 2 == 0):
            return {"holds": False, "witness": n}
    return {"holds": True, "n_max": n_max}


def lemma_m_checks(n: int, big_g: int, scale: int = 10**60) -> dict[str, tuple[int, int]]:
    """Exact scaled validation of the Lemma M second-order forms.

    (i)  m^{3/2} = -(1/8) X^{3/2} + (3/4) m X^{1/2} + (3/8) m^2 X^{-1/2}
         + R5,  0 <= R5 <= (1/16)(X-1)^{-3/2};
    (ii) (m+G)^{3/2} = Z^{3/2} - (3/2) X Z^{1/2} + (3/8) X^2 Z^{-1/2}
         + m [ (3/2) Z^{1/2} - (3/4) X Z^{-1/2} ] + (3/8) m^2 Z^{-1/2}
         + R6,  0 <= R6 <= (1/16)(Z-1)^{-3/2},
    (both remainders are the positive third-order Taylor terms of
    t -> (X-t)^{3/2} resp. (Z-t)^{3/2}, since f''' > 0 and theta > 0)
    with X = n^{3/2}, Z = X + G. These carry the differenced tier-2
    phase; remainders are absorbable against the W ~ k n^{9/8} weight.
    """
    if n < 5 or n % 2 == 0:
        raise ValueError("odd n >= 5 required")
    s2 = scale * scale
    m = isqrt(n**3)
    xs = isqrt(n**3 * s2)                          # X * scale
    x12 = isqrt(isqrt(n**3 * scale**4))            # X^{1/2} * scale
    x32 = isqrt(isqrt(n**9 * scale**4))            # X^{3/2} * scale

    lhs_i = isqrt(m**3 * s2)
    poly_i = -x32 // 8 + 3 * m * x12 // 4 + 3 * m * m * s2 // (8 * x12)
    bound_i = s2 // (14 * x32) + 4 * n**3 + 1000

    zs = xs + big_g * scale                        # Z * scale
    z12 = isqrt(zs * scale)                        # Z^{1/2} * scale
    z32 = zs * z12 // scale                        # Z^{3/2} * scale
    lhs_ii = isqrt((m + big_g) ** 3 * s2)
    poly_ii = (
        z32
        - 3 * xs * z12 // (2 * scale)
        + 3 * n**3 * s2 // (8 * z12)
        + m * (3 * z12 // 2 - 3 * xs * scale // (4 * z12))
        + 3 * m * m * s2 // (8 * z12)
    )
    bound_ii = s2 // (14 * z32) + 4 * n**3 + 1000
    return {
        "m32": (poly_i - lhs_i, bound_i),
        "shifted": (poly_ii - lhs_ii, bound_ii),
    }


def lemma_m_scan(samples: tuple[int, ...], h: int = 1) -> dict[str, Any]:
    """Check both Lemma M identities on samples with realized gaps G."""
    for n in samples:
        big_g = isqrt((n + 2 * h) ** 3) - isqrt(n**3)
        res = lemma_m_checks(n, big_g)
        # poly - lhs = -R with R the positive Taylor remainder: window [-bound, slack].
        for which in ("m32", "shifted"):
            diff, bound = res[which]
            if not (-bound <= diff <= 4 * n**3 + 1000):
                return {"holds": False, "witness": n, "which": which}
    return {"holds": True, "count": len(samples)}


def level2_gap_check(start: int, count: int, h: int) -> dict[str, Any]:
    """Lemma N: g2 = floor(DY) + [theta2 >= 1 - {DY}] with DY = Y+ - Y.

    Exact check on realized orbit data; boundary-ambiguous samples
    (fractional parts within a guard band of 0/1) are skipped, as in
    gap_decomposition_check.
    """
    s = 10**24
    guard = 10**6
    matches = skipped = 0
    n = start if start % 2 == 1 else start + 1
    for _ in range(count):
        m0 = isqrt(n**3)
        m1 = isqrt((n + 2 * h) ** 3)
        v0, v1 = isqrt(m0**3), isqrt(m1**3)
        y0 = isqrt(m0**3 * s * s)
        y1 = isqrt(m1**3 * s * s)
        dys = y1 - y0
        fdy, frac_dy = divmod(dys, s)
        th2 = y0 - v0 * s
        if frac_dy < guard or frac_dy > s - guard or abs(th2 - (s - frac_dy)) < guard:
            skipped += 1
            n += 2
            continue
        kappa2 = 1 if th2 >= s - frac_dy else 0
        if v1 - v0 != fdy + kappa2:
            return {"holds": False, "witness": n}
        matches += 1
        n += 2
    return {"holds": True, "matches": matches, "skipped": skipped}


def kernel_probe(p_block: int, coeff_num: int = 3, coeff_den: int = 4) -> dict[str, Any]:
    """Float probe of the isolated tier-2 kernel K = sum e(c(n) {m^{3/2}}).

    c(n) = (coeff_num/coeff_den) n^{9/8}, the natural W-scale of the
    OOO* reduction. Exact scaled phase arithmetic; float only in the
    final exponential. Not a proof; supports or refutes Conjecture L.
    """
    from math import cos, pi, sin

    s = 10**12
    s30 = 10**30
    re = im = 0.0
    cnt = 0
    n = p_block + 1
    while n < 2 * p_block:
        m = isqrt(n**3)
        t2 = isqrt(m**3 * s * s)
        th2 = t2 - (t2 // s) * s                     # {m^{3/2}} * s
        r9 = _eighth_scaled(n**9, s30)               # n^{9/8} * s30
        prod = (coeff_num * r9 * th2) // coeff_den   # c*theta2 * s30*s
        frac = (prod % (s30 * s)) / (s30 * s)
        ph = 2 * pi * frac
        re += cos(ph)
        im += sin(ph)
        cnt += 1
        n += 2
    return {"count": cnt, "abs_sum": round((re * re + im * im) ** 0.5, 1)}


# --- Phase 8: the kernel — double-differencing validators and probes ---


def kernel_reformulation_check(n: int, scale: int = 10**40) -> tuple[int, int]:
    """(diff*scale, bound*scale) for the kernel reformulation (Lemma R1).

    With Y = m^{3/2}, v = floor(Y), theta_2 = Y - v:
    (1/2)(m^{9/4} - v^{3/2}) - (3/4) v^{1/2} theta_2 = R in
    [0, (3/16) v^{-1/2}] (Taylor of (v + theta_2)^{3/2} at v, one-signed
    remainder). Hence the central kernel phase c*theta_2 with
    c = (3k/4) v^{1/2} equals (k/2)(m^{9/4} - v^{3/2}) up to kR: the
    kernel is the exponential sum of the level-2 local floor defect.
    """
    if n < 5 or n % 2 == 0:
        raise ValueError("odd n >= 5 required")
    m = isqrt(n**3)
    v = isqrt(m**3)
    m94 = isqrt(isqrt(m**9 * scale**4))
    v32 = isqrt(v**3 * scale * scale)
    v12 = isqrt(v * scale * scale)
    th2 = isqrt(m**3 * scale * scale) - v * scale
    diff = (m94 - v32) // 2 - (3 * v12 * th2) // (4 * scale)
    # Floor slack: th2 and v12 each carry O(1) scaled-unit error, and
    # the cross products propagate them at v^{1/2} ~ n^{9/8} units.
    slack = isqrt(n**9) + 10**6
    bound = (3 * scale * scale) // (16 * v12) + slack
    return diff, bound


def kernel_reformulation_scan(samples: tuple[int, ...]) -> dict[str, Any]:
    """Check 0 <= diff <= bound on odd samples (slack folded into bound)."""
    slack = 10**7
    for n in samples:
        diff, bound = kernel_reformulation_check(n)
        if diff < -slack or diff > bound:
            return {"holds": False, "witness": n}
    return {"holds": True, "count": len(samples)}


def double_gap_identity_check(
    start: int, count: int, h1: int, h2: int
) -> dict[str, Any]:
    """Lemma R2: the second difference of the level-2 gap decomposes as

    D2 g2 = floor(D2 D1 Y) + kappa'' + D2 kappa_2,

    with W = D1 Y, kappa'' = [{W} >= 1 - {D2 W}] (gap identity on the
    sequence W) and kappa_2 = [theta_2 >= 1 - {W}] (Lemma N). Exact on
    orbit data; boundary-ambiguous samples are skipped (guard band),
    as in level2_gap_check. Lean: seq_floor_gap applied twice
    (seq_floor_gap_second in GapCells.lean).
    """
    s = 10**24
    guard = 10**6
    matches = skipped = 0
    n = start if start % 2 == 1 else start + 1
    d1, d2 = 2 * h1, 2 * h2

    def y_scaled(x: int) -> int:
        return isqrt(isqrt(x**3) ** 3 * s * s)

    def v_of(x: int) -> int:
        return isqrt(isqrt(x**3) ** 3)

    for _ in range(count):
        y00, y10 = y_scaled(n), y_scaled(n + d1)
        y01, y11 = y_scaled(n + d2), y_scaled(n + d1 + d2)
        v00, v10, v01, v11 = v_of(n), v_of(n + d1), v_of(n + d2), v_of(n + d1 + d2)
        w0 = y10 - y00                      # W(n) * s
        w1 = y11 - y01                      # W(n + d2) * s
        dw = w1 - w0                        # (D2 D1 Y) * s
        fdw, frac_dw = divmod(dw, s)
        frac_w0 = w0 % s
        frac_w1 = w1 % s
        th2_0 = y00 - v00 * s
        th2_1 = y01 - v01 * s
        fracs = (frac_dw, frac_w0, frac_w1, th2_0, th2_1)
        pairs = (
            (frac_w0, s - frac_dw),
            (th2_0, s - frac_w0),
            (th2_1, s - frac_w1),
        )
        if any(f < guard or f > s - guard for f in fracs) or any(
            abs(a - b) < guard for a, b in pairs
        ):
            skipped += 1
            n += 2
            continue
        kappa_dd = 1 if frac_w0 >= s - frac_dw else 0
        kappa2_0 = 1 if th2_0 >= s - frac_w0 else 0
        kappa2_1 = 1 if th2_1 >= s - frac_w1 else 0
        lhs = (v11 - v01) - (v10 - v00)     # D2 g2
        rhs = fdw + kappa_dd + (kappa2_1 - kappa2_0)
        if lhs != rhs:
            return {"holds": False, "witness": n}
        matches += 1
        n += 2
    return {"holds": True, "matches": matches, "skipped": skipped}


def branch_freeze_scan(
    p_block: int, h1: int, h2: int, window: int
) -> dict[str, Any]:
    """Lemma R3 support: the branch values of D2 D1 Y freeze.

    Raw floor(D2 D1 Y) is NOT frozen: the level-1 second gap
    j1 = D2 g1 flickers at every step and shifts D2 D1 Y by
    (3/2) j1 m^{1/2} ~ n^{3/4}. The proof's organization conditions on
    the cell gaps (G1, G2) and the bounded j1 = j; the branch function
    F_j(m) = (m+G1+G2+j)^{3/2} - (m+G1)^{3/2} - (m+G2)^{3/2} + m^{3/2}
    is smooth in m with n-drift ~ (9/8) j n^{-1/4} + O(h1 h2 n^{-3/4})
    < 1, so its floor is constant on long runs; the flicker lives in
    the indicator [j1 = j], never in the branch. This scan evaluates
    each branch j in {-1, 0, 1} at every n of a window inside a cell
    intersection and reports the distinct-floor counts against the
    drift prediction.
    """
    s = 10**24
    d1, d2 = 2 * h1, 2 * h2
    n0 = p_block + 1
    m0 = isqrt(n0**3)
    big_g1 = isqrt((n0 + d1) ** 3) - m0
    big_g2 = isqrt((n0 + d2) ** 3) - m0

    def branch_floor(m: int, j: int) -> int:
        val = (
            isqrt((m + big_g1 + big_g2 + j) ** 3 * s * s)
            - isqrt((m + big_g1) ** 3 * s * s)
            - isqrt((m + big_g2) ** 3 * s * s)
            + isqrt(m**3 * s * s)
        )
        return val // s

    out: dict[str, Any] = {"window": window}
    in_cell = 0
    values: dict[int, set[int]] = {-1: set(), 0: set(), 1: set()}
    n = n0
    for _ in range(window):
        m = isqrt(n**3)
        if (
            isqrt((n + d1) ** 3) - m != big_g1
            or isqrt((n + d2) ** 3) - m != big_g2
        ):
            break
        in_cell += 1
        for j in (-1, 0, 1):
            values[j].add(branch_floor(m, j))
        n += 2
    for j in (-1, 0, 1):
        drift = 1.125 * abs(j) / p_block**0.25 + h1 * h2 / p_block**0.75
        out[f"branch_{j}"] = {
            "distinct": len(values[j]),
            "predicted": round(1 + 2 * in_cell * drift, 1),
        }
    out["in_cell"] = in_cell
    return out


def master_identity_check(
    start: int, count: int, h1: int, h2: int
) -> dict[str, Any]:
    """Paper B Section 5 master identity (Phase 25 gate).

    With c any weight (here c = n, exact), theta_2 = {m^{3/2}},
    W = D1 Y, kappa_2 = [theta_2 >= 1 - {W}],
    kappa'' = [{W} >= 1 - {DD Y}]:

    DD(c theta_2) = (DD c) theta_2
                  + (D2 c)(n+d1) ({W} - kappa_2)
                  + (D1 c)(n+d2) ({W'} - kappa_2')
                  + c_11 ({DD Y} - kappa'' - D2 kappa_2),

    where W' = D2 Y and kappa_2' is the d2-analogue. Exact scaled
    integers; boundary-ambiguous samples skipped. This is the exact
    rearrangement of level2_gap_check + double_gap_identity_check
    used by the rewritten kernel proof; the gate catches bookkeeping
    slips in the assembly.
    """
    s = 10**24
    guard = 10**6
    matches = skipped = 0
    n = start if start % 2 == 1 else start + 1
    d1, d2 = 2 * h1, 2 * h2

    def y_scaled(x: int) -> int:
        return isqrt(isqrt(x**3) ** 3 * s * s)

    for _ in range(count):
        y00, y10 = y_scaled(n), y_scaled(n + d1)
        y01, y11 = y_scaled(n + d2), y_scaled(n + d1 + d2)
        th = {key: y - (y // s) * s for key, y in
              (("00", y00), ("10", y10), ("01", y01), ("11", y11))}
        w0, w1 = y10 - y00, y11 - y01          # W(n), W(n+d2), scaled
        wp0 = y01 - y00                        # W'(n) = D2 Y, scaled
        ddy = w1 - w0                          # DD Y, scaled
        frac_w0, frac_w1 = w0 % s, w1 % s
        frac_wp0 = wp0 % s
        frac_ddy = ddy % s
        fracs = (th["00"], th["10"], th["01"], th["11"],
                 frac_w0, frac_w1, frac_wp0, frac_ddy)
        pairs = (
            (th["00"], s - frac_w0), (th["01"], s - frac_w1),
            (th["00"], s - frac_wp0), (frac_w0, s - frac_ddy),
        )
        if any(f < guard or f > s - guard for f in fracs) or any(
            abs(a - b) < guard for a, b in pairs
        ):
            skipped += 1
            n += 2
            continue
        k2_0 = 1 if th["00"] >= s - frac_w0 else 0
        k2_1 = 1 if th["01"] >= s - frac_w1 else 0
        k2p = 1 if th["00"] >= s - frac_wp0 else 0
        kdd = 1 if frac_w0 >= s - frac_ddy else 0
        c00, c10, c01, c11 = n * n, (n + d1) ** 2, (n + d2) ** 2, (n + d1 + d2) ** 2
        lhs = (c11 * th["11"] - c01 * th["01"]
               - c10 * th["10"] + c00 * th["00"])
        ddc = c11 - c01 - c10 + c00
        # product rule: DD(cf) = c11 DD f + (D2 c)(n+d1) D1 f
        #               + (D1 c)(n+d2) D2 f + (DD c) f
        d1_th2 = frac_w0 - k2_0 * s            # D1 theta_2 = {W} - kappa_2
        d2_th2 = frac_wp0 - k2p * s            # D2 theta_2 = {W'} - kappa_2'
        dd_th2 = frac_ddy - (kdd + k2_1 - k2_0) * s
        rhs = (c11 * dd_th2 + (c11 - c10) * d1_th2
               + (c11 - c01) * d2_th2 + ddc * th["00"])
        if lhs != rhs:
            return {"holds": False, "witness": n}
        matches += 1
        n += 2
    return {"holds": True, "matches": matches, "skipped": skipped}


def kernel_margin_scan(p_block: int, h3: int = 1, k: int = 1) -> dict[str, Any]:
    """Numerical gate for the two displayed sign margins (Phase 25).

    (m1) differenced-kernel main curvature: with beta = exact level-1
    gap at shift 2*h3, G(n) = W3(X(n)) = (X+beta)^{3/2} - X^{3/2},
    the proof displays G'' = -(9/32) beta n^{-5/4} (1+o(1)), i.e.
    -(27/32) h3 n^{-3/4} at beta ~ 3 h3 n^{1/2}: the two contributions
    (9/16) beta n^{-5/4} and -(27/32) beta n^{-5/4} do not cancel.

    (m2) window-centre composite for the class-(i) decoration:
    lambda_2 = (c F)'' + u X'' at u = -B(n0) is
    (945/512 - 27/64) k j n^{-1/8} (1+o(1)) ~ 1.42 k j n^{-1/8}:
    single-signed with ratio 945/512 : 27/64 = 4.375.
    """
    out: dict[str, Any] = {}
    n = float(p_block) * 1.5
    x = n**1.5
    beta = float(isqrt((int(n) + 2 * h3) ** 3) - isqrt(int(n) ** 3))
    w3p = 1.5 * ((x + beta) ** 0.5 - x**0.5)
    w3pp = 0.75 * ((x + beta) ** -0.5 - x**-0.5)
    xp, xpp = 1.5 * n**0.5, 0.75 * n**-0.5
    g2 = w3pp * xp * xp + w3p * xpp
    out["m1"] = {
        "computed": g2,
        "predicted": -(9.0 / 32.0) * beta * n**-1.25,
        "ratio": g2 / (-(9.0 / 32.0) * beta * n**-1.25),
    }
    j = 1
    cf_pp = (945.0 / 512.0) * k * j * n**-0.125
    u_term = -(27.0 / 64.0) * k * j * n**-0.125
    out["m2"] = {
        "cf_pp": cf_pp,
        "u_term": u_term,
        "sum_over_kj": (cf_pp + u_term) / (k * j * n**-0.125),
        "ratio": abs(cf_pp / u_term),
    }
    return out


# Paper B printed coefficients for the sign-critical composites.
_E6_SMOOTH = 945.0 / 512.0
_E6_WINDOW = 27.0 / 64.0
_THM61_WINDOW = 540.0 / 512.0
_THM61_ZERO = 8.27
_STAGE4_LO = 0.30
_STAGE4_HI = 1.35
_DECORATED_B_FACTOR = 2.5  # (45/32) / (9/16)


def _odd_near(x: float) -> int:
    v = int(round(x))
    if v % 2 == 0:
        v += 1
    return max(v, 3)


def _in_standing(p: int, h1: int, h2: int, k: int) -> bool:
    """Standing range (C1)–(C3) of Paper B Section 5."""
    if h1 < 1 or h2 < 1 or k < 1:
        return False
    if k * h1 * h2 > p ** 0.125 * (1.0 + 1e-12):
        return False
    if h1 * h2 > p ** 0.5 / 3.0 * (1.0 + 1e-12):
        return False
    if k > p ** (1.0 / 24.0) * (1.0 + 1e-12):
        return False
    return True


def _standing_corners(p: int, *, fast: bool) -> list[tuple[int, int, int]]:
    weyl1 = max(1, int(p ** (1.0 / 48.0)))
    weyl2 = max(1, int(p ** (1.0 / 24.0)))
    k_max = max(1, int(p ** (1.0 / 24.0)))
    h_c1 = max(1, int(p ** 0.125))
    raw = [(1, 1, 1), (weyl1, weyl2, 1)]
    if not fast:
        raw.extend([(1, 1, k_max), (1, h_c1, 1)])
    seen: set[tuple[int, int, int]] = set()
    out: list[tuple[int, int, int]] = []
    for trip in raw:
        if trip not in seen and _in_standing(p, *trip):
            seen.add(trip)
            out.append(trip)
    return out


def _sample_ns(p: int) -> tuple[int, ...]:
    return (p + 1, _odd_near(1.5 * p), 2 * p - 1)


def _frozen_gaps(n: int, h1: int, h2: int) -> tuple[float, float]:
    m0 = isqrt(n**3)
    return (
        float(isqrt((n + 2 * h1) ** 3) - m0),
        float(isqrt((n + 2 * h2) ** 3) - m0),
    )


def _branch_f_derivs(m: float, b1: float, b2: float, j: int) -> tuple[float, float, float]:
    """Lemma 5.1(iii) mean-value forms; midpoints keep the relative O((β+|j|)/m)."""
    xi1 = 0.5 * (b1 + b2 + j)
    xi2 = 0.5 * (b1 + b2)
    t = m + xi1
    u = m + xi2
    st = sqrt(t)
    su = sqrt(u)
    f = 1.5 * j * st + 0.75 * b1 * b2 / su
    fp = 0.75 * j / st - 0.375 * b1 * b2 / (u * su)
    fpp = -0.375 * j / (t * st) + 0.5625 * b1 * b2 / (u * u * su)
    return f, fp, fpp


def _weight_c(n: float, k: int) -> tuple[float, float, float]:
    """c = (3k/4) n^{9/8} and its first two n-derivatives."""
    c = 0.75 * k * n ** 1.125
    cp = (27.0 / 32.0) * k * n ** 0.125
    cpp = (27.0 / 256.0) * k * n ** -0.875
    return c, cp, cpp


def _cg_second(n: float, k: int, b1: float, b2: float, j: int) -> tuple[float, float, float]:
    """((c F_j) ∘ X)'' and the kernel window term -B X'' with B = c F'(X)."""
    x = n ** 1.5
    xp = 1.5 * n ** 0.5
    xpp = 0.75 * n ** -0.5
    f, fp, fpp = _branch_f_derivs(x, b1, b2, j)
    c, cp, cpp = _weight_c(n, k)
    gp = fp * xp
    gpp = fpp * xp * xp + fp * xpp
    smooth = cpp * f + 2.0 * cp * gp + c * gpp
    window = -c * fp * xpp
    return smooth, window, smooth + window


def _w3_second(n: float, n_int: int, h: int) -> tuple[float, float]:
    """Second n-derivative of (X+β)^{3/2}-X^{3/2} with β the frozen level-1 gap."""
    x = n ** 1.5
    xp = 1.5 * n ** 0.5
    xpp = 0.75 * n ** -0.5
    beta = float(isqrt((n_int + 2 * h) ** 3) - isqrt(n_int ** 3))
    sx = sqrt(x)
    sxb = sqrt(x + beta)
    w3p = 1.5 * beta / (sxb + sx)
    w3pp = 0.75 * (-beta) / (sxb * sx * (sxb + sx))
    return w3pp * xp * xp + w3p * xpp, beta


def _thm61_zero_curvature(n: float, h1: int, h2: int, k: int) -> float:
    """Second n-derivative of Δ_{2h1} Δ_{2h2} [(k/2) n^{27/8}].

    Written as the double integral of φ^{(4)} over the shift rectangle.
    A four-point average of t^{-5/8} keeps the (1+O(h P^{-1/2})) content
    without cancelling n^{11/8} terms (naive mixed differences die by P=10^8).
    """
    d1, d2 = 2.0 * h1, 2.0 * h2
    lead = 0.5 * k * (27.0 / 8.0) * (19.0 / 8.0) * (11.0 / 8.0) * (3.0 / 8.0)
    acc = 0.0
    for sa, ta in ((0.25, 0.25), (0.25, 0.75), (0.75, 0.25), (0.75, 0.75)):
        acc += (n + sa * d1 + ta * d2) ** -0.625
    return lead * d1 * d2 * (acc / 4.0)


def _empty_piece() -> dict[str, Any]:
    return {
        "worst_ratio": None,
        "worst_ratio_witness": None,
        "min_sign_margin": None,
        "min_sign_margin_witness": None,
        "first_sign_loss_P": None,
        "first_sign_loss_witness": None,
        "n_ok": 0,
        "n_loss": 0,
    }


def _record_piece(
    piece: dict[str, Any],
    *,
    p: int,
    ratio: float | None,
    sign_margin: float,
    worse_is_larger: bool,
    witness: dict[str, Any],
) -> None:
    if sign_margin <= 0.0:
        piece["n_loss"] += 1
        if piece["first_sign_loss_P"] is None:
            piece["first_sign_loss_P"] = p
            piece["first_sign_loss_witness"] = dict(witness)
    else:
        piece["n_ok"] += 1
    if piece["min_sign_margin"] is None or sign_margin < piece["min_sign_margin"]:
        piece["min_sign_margin"] = sign_margin
        piece["min_sign_margin_witness"] = dict(witness)
    if ratio is None:
        return
    current = piece["worst_ratio"]
    worse = current is None or (
        ratio > current if worse_is_larger else ratio < current
    )
    if worse:
        piece["worst_ratio"] = ratio
        piece["worst_ratio_witness"] = dict(witness)


def sign_critical_domain_scan(
    p_grid: tuple[int, ...] | None = None,
    *,
    fast: bool = False,
) -> dict[str, Any]:
    """Domain scan of the four written Paper B sign-critical composites.

    Evaluates the actual Lemma 5.1(iii) interpolants on (n,h1,h2,k,j)
    in the standing range (C1)–(C3). Does not plug predicted coefficients
    into themselves. kernel_margin_scan remains the one-point algebraic
    gate.

    Pieces:
      e6_step5a          (cF)'' vs B X'' at j ≠ 0; predicted 945/512 − 27/64
      thm61_offset       withdrawn moving-gap interpolant vs 2.5× kernel B
                         (printed 405/512). Live Step E is
                         paper_b_audit.frozen_total_phase_samples (243/512).
      thm61_zero_offset  withdrawn mixed fourth derivative of (k/2) n^{27/8}
                         vs 8.27. Live zero-offset is 1095/1024.
      lemma52_stage4     W3'' against −9/32 β n^{-5/4} and [0.30, 1.35] uh P^{-3/4}
      lemma52_stage6     (D1) actual / (D2)(D3) printed vs 0.30 uh P^{-3/4}
    """
    if p_grid is None:
        p_grid = (10**6, 10**8) if fast else (
            10**4, 10**5, 10**6, 10**8, 10**10, 10**12,
        )
    pieces = {
        "e6_step5a": _empty_piece(),
        "thm61_offset": _empty_piece(),
        "thm61_zero_offset": _empty_piece(),
        "lemma52_stage4": _empty_piece(),
        "lemma52_stage6": _empty_piece(),
    }
    pieces["lemma52_stage4"]["n_band_fail"] = 0
    pieces["lemma52_stage6"]["by_class"] = {
        "D1": None, "D2": None, "D3": None,
    }
    n_samples = 0
    js_offset = (-1, 1) if fast else (-3, -2, -1, 1, 2, 3)

    for p in p_grid:
        ns = _sample_ns(p)
        corners = _standing_corners(p, fast=fast)
        p_m34 = p ** -0.75
        q_max = p ** (1.0 / 16.0)
        h_stage = [1]
        h_big = max(1, int(p ** 0.125))
        if h_big not in h_stage:
            h_stage.append(h_big)
        uh_vals = [1, max(1, int(p ** 0.5))]
        hp_pairs: list[tuple[int, int]] = []
        for h in h_stage:
            for uh in uh_vals:
                u = uh // h
                if u >= 1:
                    hp_pairs.append((h, u))
        if not hp_pairs:
            hp_pairs = [(1, 1)]
        hprimes = [1]
        if not fast:
            hp2 = max(1, int(2 * p ** (1.0 / 24.0)))
            if hp2 not in hprimes:
                hprimes.append(hp2)

        for n in ns:
            for h1, h2, k in corners:
                b1, b2 = _frozen_gaps(n, h1, h2)
                nf = float(n)
                n_samples += 1

                for j in js_offset:
                    smooth, window, composite = _cg_second(nf, k, b1, b2, j)
                    pred_lead = ( _E6_SMOOTH - _E6_WINDOW ) * k * j * nf ** -0.125
                    ratio = abs(smooth / window) if window != 0.0 else None
                    sign_margin = composite / pred_lead if pred_lead != 0.0 else composite
                    wit = {
                        "P": p, "n": n, "h1": h1, "h2": h2, "k": k, "j": j,
                        "smooth": smooth, "window": window, "composite": composite,
                    }
                    _record_piece(
                        pieces["e6_step5a"],
                        p=p, ratio=ratio, sign_margin=sign_margin,
                        worse_is_larger=False, witness=wit,
                    )
                    window61 = _DECORATED_B_FACTOR * window
                    composite61 = smooth + window61
                    pred61 = ( _E6_SMOOTH - _THM61_WINDOW ) * k * j * nf ** -0.125
                    ratio61 = abs(smooth / window61) if window61 != 0.0 else None
                    margin61 = composite61 / pred61 if pred61 != 0.0 else composite61
                    wit61 = {
                        "P": p, "n": n, "h1": h1, "h2": h2, "k": k, "j": j,
                        "smooth": smooth, "window": window61, "composite": composite61,
                    }
                    _record_piece(
                        pieces["thm61_offset"],
                        p=p, ratio=ratio61, sign_margin=margin61,
                        worse_is_larger=False, witness=wit61,
                    )

                measured0 = _thm61_zero_curvature(nf, h1, h2, k)
                predicted0 = _THM61_ZERO * k * h1 * h2 * nf ** -0.625
                ratio0 = measured0 / predicted0 if predicted0 != 0.0 else None
                interval_scale = k * h1 * h2 * p ** -0.625
                sign_margin0 = measured0 / predicted0 if predicted0 != 0.0 else measured0
                wit0 = {
                    "P": p, "n": n, "h1": h1, "h2": h2, "k": k, "j": 0,
                    "measured": measured0, "predicted": predicted0,
                    "over_P_scale": (
                        measured0 / interval_scale if interval_scale != 0.0 else None
                    ),
                }
                _record_piece(
                    pieces["thm61_zero_offset"],
                    p=p, ratio=ratio0, sign_margin=sign_margin0,
                    worse_is_larger=False, witness=wit0,
                )

                for h, u in hp_pairs:
                    g2, beta = _w3_second(nf, n, h)
                    pred4 = -(9.0 / 32.0) * beta * nf ** -1.25
                    ratio4 = g2 / pred4 if pred4 != 0.0 else None
                    band = abs(g2) / (h * p_m34) if h * p_m34 != 0.0 else None
                    sign_margin4 = ratio4 if ratio4 is not None else -1.0
                    in_band = (
                        band is not None and _STAGE4_LO <= band <= _STAGE4_HI
                    )
                    wit4 = {
                        "P": p, "n": n, "h": h, "u": u, "beta": beta,
                        "g2": g2, "predicted": pred4, "band": band,
                        "in_band": in_band,
                    }
                    _record_piece(
                        pieces["lemma52_stage4"],
                        p=p, ratio=ratio4, sign_margin=sign_margin4,
                        worse_is_larger=False, witness=wit4,
                    )
                    if not in_band:
                        pieces["lemma52_stage4"]["n_band_fail"] += 1

                    main = _STAGE4_LO * u * h * p_m34
                    for hprime in hprimes:
                        for jp in ((1,) if fast else (1, 3)):
                            _b1, _b2 = _frozen_gaps(n, h, hprime)
                            _f, fp, fpp = _branch_f_derivs(nf ** 1.5, _b1, _b2, jp)
                            xp = 1.5 * nf ** 0.5
                            xpp = 0.75 * nf ** -0.5
                            gpp = fpp * xp * xp + fp * xpp
                            d1_curv = abs(q_max * gpp)
                            d1_ratio = d1_curv / main if main != 0.0 else None
                            d2_curv = (
                                7.0 * k * h * abs(jp) * p ** -1.125
                                + 28.0 * k * h * h1 * h2 * p ** -1.625
                            )
                            d2_ratio = d2_curv / main if main != 0.0 else None
                            d3_curv = 2.0 * h * 3.0 * k * h1 * h2 * p ** -1.625
                            d3_ratio = d3_curv / main if main != 0.0 else None
                            for cls, rr in (
                                ("D1", d1_ratio), ("D2", d2_ratio), ("D3", d3_ratio),
                            ):
                                if rr is None:
                                    continue
                                prev = pieces["lemma52_stage6"]["by_class"][cls]
                                if prev is None or rr > prev:
                                    pieces["lemma52_stage6"]["by_class"][cls] = rr
                            worst6 = max(
                                r for r in (d1_ratio, d2_ratio, d3_ratio) if r is not None
                            )
                            wit6 = {
                                "P": p, "n": n, "h1": h1, "h2": h2, "k": k,
                                "h": h, "u": u, "hprime": hprime, "j": jp,
                                "D1": d1_ratio, "D2": d2_ratio, "D3": d3_ratio,
                            }
                            # Stage 6 "sign loss" is a domination failure.
                            _record_piece(
                                pieces["lemma52_stage6"],
                                p=p, ratio=worst6,
                                sign_margin=1.0 - worst6,
                                worse_is_larger=True, witness=wit6,
                            )

    return {
        "n_samples": n_samples,
        "p_grid": list(p_grid),
        "fast": fast,
        "pieces": pieces,
    }


def _kernel_phase_scaled(n: int, coeff_num: int, coeff_den: int) -> float:
    """{c(n) theta_2(n)} with c = (num/den) n^{9/8}, exact scaled ints."""
    s = 10**12
    s30 = 10**30
    m = isqrt(n**3)
    t2 = isqrt(m**3 * s * s)
    th2 = t2 - (t2 // s) * s
    r9 = _eighth_scaled(n**9, s30)
    prod = (coeff_num * r9 * th2) // coeff_den
    return (prod % (s30 * s)) / (s30 * s)


def differenced_kernel_probe(
    p_block: int,
    h1: int,
    h2: int = 0,
    h3: int = 0,
    coeff_num: int = 3,
    coeff_den: int = 4,
) -> dict[str, Any]:
    """Float probe of the once-, twice- or thrice-differenced kernel sums.

    h2 = 0: T1 = sum e(phi(n+2h1) - phi(n)).
    h2 > 0: T2, the second Weyl difference over the (h1, h2) rectangle.
    h3 > 0: T3, the third difference (the targeted extra differencing of
    the review pass, applied to the kernel itself as a proxy for the
    mixed pieces). phi = c theta_2 with c = (coeff_num/coeff_den)
    n^{9/8}. Exact scaled phases, float only in the final exponential.
    Supports or refutes the differencing route; not a proof.
    """
    from math import cos, pi, sin

    # Build signed corner shifts for up to three nested differences.
    corners = [(1, 2 * h1), (-1, 0)]
    for h in (h2, h3):
        if h > 0:
            corners = [(s, d + 2 * h) for s, d in corners] + [
                (-s, d) for s, d in corners
            ]
    re = im = 0.0
    cnt = 0
    n = p_block + 1
    while n < 2 * p_block:
        ph = 0.0
        for sgn, d in corners:
            ph += sgn * _kernel_phase_scaled(n + d, coeff_num, coeff_den)
        theta = 2 * pi * ph
        re += cos(theta)
        im += sin(theta)
        cnt += 1
        n += 2
    return {
        "count": cnt,
        "abs_sum": round((re * re + im * im) ** 0.5, 1),
        "sqrt_count": round(cnt**0.5, 1),
    }


# --- Phase 4: second-order linearization bricks for the OOO* layer ---

SCALE2 = 10**60


def _eighth_scaled2(x: int, scale: int = SCALE2) -> int:
    return isqrt(isqrt(isqrt(x * scale**8)))


def second_order_checks(n: int, scale: int = SCALE2) -> dict[str, tuple[int, int]]:
    """Exact scaled validation of the three Lemma G / Proposition H identities.

    (a) m^{3/4} = (5/32) n^{9/8} + (15/16) m n^{-3/8} - (3/32) m^2 n^{-15/8} - R3,
        0 <= R3 <= (5/128)(n^{3/2}-1)^{-9/4};
    (b) m^{9/4} = (5/32) n^{27/8} - (9/16) m n^{15/8} + (45/32) m^2 n^{3/8} + R4,
        -(15/128)(n^{3/2}-1)^{-3/4} <= R4 <= 0;
    (c) v^{3/2} = -(5/64) n^{27/8} + (9/32) m n^{15/8} - (45/64) m^2 n^{3/8}
        + (15/64) v n^{9/8} + (45/32) v m n^{-3/8} - (9/64) v m^2 n^{-15/8} + err,
        |err| <= (3/4) n^{-9/8}.

    Returns {name: (diff_scaled, bound_scaled)} at SCALE2 (needed because the
    identities cancel to n^{-9/8} out of n^{27/8}-size terms).
    """
    if n < 5 or n % 2 == 0:
        raise ValueError("odd n >= 5 required")
    m = isqrt(n**3)
    v = isqrt(m**3)
    s2 = scale * scale
    r3 = _eighth_scaled2(n**3, scale)      # n^{3/8}  * scale
    r9 = _eighth_scaled2(n**9, scale)      # n^{9/8}  * scale
    r15 = _eighth_scaled2(n**15, scale)    # n^{15/8} * scale
    r27 = _eighth_scaled2(n**27, scale)    # n^{27/8} * scale

    # Negative powers are computed as direct divisions by the scaled
    # roots (never as products with a scaled inverse): the floor error
    # is then relative ~1/(n^a * scale) instead of absolute, keeping
    # every term's rounding at O(n^3) scaled units.
    m34 = isqrt(isqrt(m**3 * scale**4))
    poly_a = 5 * r9 // 32 + 15 * m * s2 // (16 * r3) - 3 * m * m * s2 // (32 * r15)
    bound_a = 5 * s2 // (128 * r27) + n + 100

    m94 = isqrt(isqrt(m**9 * scale**4))
    poly_b = 5 * r27 // 32 - 9 * m * r15 // 16 + 45 * m * m * r3 // 32
    bound_b = 15 * s2 // (128 * r9) + n + 100

    v32 = isqrt(v**3 * scale * scale)
    poly_c = (
        -(5 * r27) // 64
        + 9 * m * r15 // 32
        - 45 * m * m * r3 // 64
        + 15 * v * r9 // 64
        + 45 * v * m * s2 // (32 * r3)
        - 9 * v * m * m * s2 // (64 * r15)
    )
    bound_c = 3 * s2 // (4 * r9) + n + 100

    return {
        "m34": (poly_a - m34, bound_a),
        "m94": (m94 - poly_b, bound_b),
        "v32": (v32 - poly_c, bound_c),
    }


def second_order_scan(samples: tuple[int, ...]) -> dict[str, Any]:
    """Check R3 in [0, bound], R4 in [-bound, 0], |err| <= bound on samples.

    Slack covers integer-division rounding: each term contributes up to
    ~(45/32) m^2 = O(n^3) scaled units of floor error, so 4 n^3 covers
    the sum; that is <= 10^{-23} in value for n <= 10^{12}, far below
    the n^{-9/8}-scale remainder bounds.
    """
    for n in samples:
        slack = 4 * n**3 + 1000
        res = second_order_checks(n)
        da, ba = res["m34"]
        if not (-slack <= da <= ba + slack):
            return {"holds": False, "witness": n, "which": "m34"}
        db, bb = res["m94"]
        if not (-bb - slack <= db <= slack):
            return {"holds": False, "witness": n, "which": "m94"}
        dc, bc = res["v32"]
        if abs(dc) > bc + slack:
            return {"holds": False, "witness": n, "which": "v32"}
    return {"holds": True, "count": len(samples)}


def ooo_indicator_identity_check(n_max: int) -> dict[str, Any]:
    """Branch consistency of the OOO* sign algebra.

    itinerary_word(n, 4) == 'OOOE' iff m odd, v odd, isqrt(v^3) even:
    the (1-psi_2) factor restricts to odd v, exactly where J^3 takes
    the odd branch, so psi_4 = psi(v^{3/2}) evaluates unconditionally.
    """
    for n in range(3, n_max + 1, 2):
        m = isqrt(n**3)
        v = isqrt(m**3)
        signs = (m % 2 == 1, v % 2 == 1, isqrt(v**3) % 2 == 0)
        if (itinerary_word(n, 4) == "OOOE") != all(signs):
            return {"holds": False, "witness": n}
    return {"holds": True, "n_max": n_max}


def second_gap_collision_check(start: int, count: int, h: int) -> dict[str, Any]:
    """Quantify the composed-cell obstruction.

    On maximal runs (cells) where g1 = m(n+2h) - m(n) is constant, count
    the distinct values of g2 = v(n+2h) - v(n). Ratio near 1 means g2
    changes at almost every point of the cell: there is no usable
    second-level cell structure, so the naive composition of Lemma B
    across two growing layers fails.
    """
    cells: list[tuple[int, int]] = []  # (cell length, distinct g2 count)
    prev_g1 = None
    g2_set: set[int] = set()
    length = 0
    n = start if start % 2 == 1 else start + 1
    for _ in range(count):
        m0, m1 = isqrt(n**3), isqrt((n + 2 * h) ** 3)
        g1 = m1 - m0
        g2 = isqrt(m1**3) - isqrt(m0**3)
        if g1 != prev_g1 and prev_g1 is not None:
            cells.append((length, len(g2_set)))
            g2_set, length = set(), 0
        prev_g1 = g1
        g2_set.add(g2)
        length += 1
        n += 2
    interior = cells[1:] if len(cells) > 2 else cells
    total_len = sum(c[0] for c in interior)
    total_distinct = sum(c[1] for c in interior)
    return {
        "cells": len(interior),
        "mean_cell_length": round(total_len / max(1, len(interior)), 2),
        "distinct_ratio": round(total_distinct / max(1, total_len), 4),
    }


def gap_decomposition_check(start: int, count: int, h: int) -> dict[str, Any]:
    """Verify g(n) = floor(delta) + kappa on `count` consecutive odd n.

    g(n) = m(n+2h) - m(n), delta(n) = (n+2h)^{3/2} - n^{3/2}, and
    kappa = [ {n^{3/2}} >= 1 - {delta(n)} ]. Exact scaled integers;
    samples within a tiny window of a cell boundary are skipped and
    counted separately.
    """
    scale = SCALE
    tol = 10
    matches = skipped = 0
    for i in range(count):
        n = start + 2 * i
        m0 = isqrt(n**3)
        m1 = isqrt((n + 2 * h) ** 3)
        g = m1 - m0
        s0 = _sqrt_scaled(n**3, scale)
        s1 = _sqrt_scaled((n + 2 * h) ** 3, scale)
        delta_scaled = s1 - s0
        floor_delta = delta_scaled // scale
        frac_delta = delta_scaled % scale
        frac_n = s0 - m0 * scale
        threshold = scale - frac_delta
        if abs(frac_n - threshold) <= tol:
            skipped += 1
            continue
        kappa = 1 if frac_n >= threshold else 0
        if g != floor_delta + kappa:
            return {"holds": False, "witness": n}
        matches += 1
    return {"holds": True, "matches": matches, "skipped": skipped}


def itinerary_word(n: int, depth: int = DEPTH) -> str:
    """Parity letters of n, J(n), ..., J^{depth-1}(n). Exact isqrt only."""
    letters = []
    x = n
    for _ in range(depth):
        letters.append("O" if x % 2 == 1 else "E")
        x = juggler_step(x)
    return "".join(letters)


def word_counts(n_max: int, depth: int = DEPTH) -> dict[str, int]:
    """Exact counts of depth-letter word itineraries over odd n in [3, n_max]."""
    counts = {w: 0 for w in WORDS4} if depth == 4 else {}
    for n in range(3, n_max + 1, 2):
        w = itinerary_word(n, depth)
        counts[w] = counts.get(w, 0) + 1
    return counts


def _prefix_counts(counts4: dict[str, int], depth: int) -> dict[str, int]:
    out: dict[str, int] = {}
    for w, c in counts4.items():
        key = w[:depth]
        out[key] = out.get(key, 0) + c
    return out


def _discrepancies(counts4: dict[str, int], odds: int) -> dict[str, float]:
    """D_w = count_w - odds * 2^{-(|w|-1)} for every word of length 2..4."""
    out: dict[str, float] = {}
    for depth in (2, 3, 4):
        expected = odds / (1 << (depth - 1))
        for w, c in _prefix_counts(counts4, depth).items():
            out[w] = c - expected
    return out


def _fit_exponent(points: list[tuple[int, float]]) -> float | None:
    """Least-squares slope of log max|D| vs log N on the top half of points."""
    usable = [(n, v) for n, v in points if v > 0]
    if len(usable) < 8:
        return None
    tail = usable[len(usable) // 2:]
    xs = [log(n) for n, _ in tail]
    ys = [log(v) for _, v in tail]
    mx = sum(xs) / len(xs)
    my = sum(ys) / len(ys)
    den = sum((x - mx) ** 2 for x in xs)
    if den == 0:
        return None
    return round(sum((x - mx) * (y - my) for x, y in zip(xs, ys)) / den, 4)


def scan(n_max: int = N_MAX) -> dict[str, Any]:
    """One exact pass over odd starts with a geometric discrepancy envelope."""
    counts4 = {w: 0 for w in WORDS4}
    odds = 0
    ooee_descent_violations = 0
    max_abs: dict[int, float] = {2: 0.0, 3: 0.0, 4: 0.0}
    envelope: dict[int, list[tuple[int, float]]] = {2: [], 3: [], 4: []}
    rows: list[dict[str, Any]] = []
    coarse = {n for n in COARSE_GRID if n <= n_max} | {n_max}
    next_sample = 1024

    for n in range(3, n_max + 1, 2):
        letters = []
        x = n
        for _ in range(DEPTH):
            letters.append("O" if x % 2 == 1 else "E")
            x = juggler_step(x)
        w = "".join(letters)
        counts4[w] += 1
        odds += 1
        if w == CONTRACTING_TARGET and x >= n:
            ooee_descent_violations += 1
        boundary = n + 1
        if boundary >= next_sample or boundary >= n_max - 1:
            disc = _discrepancies(counts4, odds)
            for depth in (2, 3, 4):
                depth_max = max(abs(v) for k, v in disc.items() if len(k) == depth)
                if depth_max > max_abs[depth]:
                    max_abs[depth] = depth_max
                envelope[depth].append((boundary, max_abs[depth]))
            if boundary in coarse or boundary - 1 in coarse:
                rows.append(
                    {
                        "n": boundary,
                        "odds": odds,
                        "counts4": dict(counts4),
                        "D": {k: round(v, 4) for k, v in disc.items()},
                        "max_abs_D": {str(d): round(max_abs[d], 4) for d in (2, 3, 4)},
                        "max_over_n12": {
                            str(d): round(max_abs[d] / boundary**0.5, 6)
                            for d in (2, 3, 4)
                        },
                        "max_over_n13": {
                            str(d): round(max_abs[d] / boundary ** (1 / 3), 6)
                            for d in (2, 3, 4)
                        },
                    }
                )
            while next_sample <= boundary:
                next_sample = int(next_sample * ENVELOPE_RATIO) + 1

    final = rows[-1]
    fitted = {str(d): _fit_exponent(envelope[d]) for d in (2, 3, 4)}
    ooee_count = counts4[CONTRACTING_TARGET]
    return {
        "n_max": n_max,
        "depth": DEPTH,
        "checkpoints": rows,
        "final": final,
        "max_abs_D": {str(d): round(max_abs[d], 4) for d in (2, 3, 4)},
        "fitted_exponent": fitted,
        "ooee": {
            "count": ooee_count,
            "fraction_of_odds": round(ooee_count / final["odds"], 6),
            "expected_fraction": 0.125,
            "descent_violations": ooee_descent_violations,
        },
        "anti_overclaim": dict(ANTI_OVERCLAIM),
    }


def write_json(row: dict[str, Any], path: Path = JSON_PATH) -> None:
    path.write_text(json.dumps(row, indent=2) + "\n", encoding="utf-8")


def write_docs(row: dict[str, Any], path: Path = DOC_PATH) -> None:
    final = row["final"]
    fit = row["fitted_exponent"]
    ooee = row["ooee"]
    lines = [
        "# Juggler multi-step word-parity census",
        "",
        "Status: **COMPUTATIONALLY VERIFIED** counts; every depth-4 word",
        "class is **EXACT — HUMAN PROOF**",
        "(`J-nested-parity-discrepancy`, `J-triple-parity-discrepancy`,",
        "`J-even-branch-third-letter`, `J-four-step-descent-density`,",
        "`J-depth4-slow-branch`, `J-kernel-cancellation`,",
        "`J-depth4-complete`; proofs in",
        "`juggler_two_step_parity_lemma.md`). Laboratory certified",
        "descent density 7/8 (Phase 27 length-5 repair). Paper B",
        "prints 13/16. W-family instance alpha = 33/32 is EXACT",
        "(Phase 28); length-7 remainder is an engine (Phase 29);",
        "Theorem-T passenger slogan REFUTED (Phase 34).",
        "Length-7/8 harvest rows stay CONJECTURE",
        "(Phase 26). OOOO* kernel isolated (Lemma V1); the",
        "scale-invariant copy of Theorem R, the increment-first",
        "K3 attack, and X1-absorption of K3 are **REFUTED**;",
        "the K3 toolkit is **PARKED**.",
        "",
        "Exact census of the joint parity word of the first four word",
        "letters on odd starts. Phase-0 falsifier for iterating the one-step",
        "discrepancy bound (Theorem 5.1 in the finite-dynamics note) to",
        "depth two and beyond. Not a frequency theorem, not a predictive",
        "state, not a termination claim.",
        "",
        f"Window: odd `n <= {row['n_max']}`. Expected class fraction of a",
        "depth-`d` word within odd starts is `2^{-(d-1)}`.",
        "",
        "| depth | max|D_w| on window | max|D|/N^{1/2} | max|D|/N^{1/3} | fitted exponent |",
        "| --- | --- | --- | --- | --- |",
    ]
    for d in ("2", "3", "4"):
        lines.append(
            f"| {d} | {row['max_abs_D'][d]} | "
            f"{final['max_over_n12'][d]} | {final['max_over_n13'][d]} | "
            f"{fit[d]} |"
        )
    lines += [
        "",
        f"Depth-4 counts at `N = {final['n']}` (odds = {final['odds']}):",
        "",
        "| word | count | D_w |",
        "| --- | --- | --- |",
    ]
    for w in sorted(final["counts4"]):
        lines.append(f"| {w} | {final['counts4'][w]} | {final['D'][w]} |")
    lines += [
        "",
        "## OOEE class",
        "",
        f"`OOEE` count {ooee['count']} = {ooee['fraction_of_odds']} of odd",
        f"starts (product density {ooee['expected_fraction']}). Every census",
        "OOEE start satisfied the four-step descent `T^4(n) < n`",
        f"(violations: {ooee['descent_violations']}); this instantiates the",
        "contraction `3^2 < 2^4` and is a guard, not a new theorem.",
        "",
        "## Reading",
        "",
        "The fitted exponents are envelope slopes on a geometric sample,",
        "label **OBSERVATION**. The analytic statements they probe are",
        "now theorems at every depth <= 4. Laboratory certified",
        "descent density is 7/8 (J-five-step-descent-density,",
        "Phase 27). Paper B prints 13/16. The W-family instance",
        "alpha = 33/32 is EXACT (Phase 28); the length-7",
        "remainder is an engine (Phase 29); the Theorem-T",
        "passenger slogan is REFUTED (Phase 34). Length-7/8 densities",
        "57/64 and 29/32 stay CONJECTURE (Phase 26 holes). ",
        "the OOOO* kernel K3 is isolated",
        "and the scale-invariant copy of Theorem R, the",
        "increment-first K3 attack, and X1-absorption of K3",
        "are REFUTED; the K3 toolkit is PARKED.",
        "",
    ]
    path.write_text("\n".join(lines), encoding="utf-8")


def main() -> None:
    row = scan()
    write_json(row)
    write_docs(row)
    print(
        "fitted exponents",
        row["fitted_exponent"],
        "ooee fraction",
        row["ooee"]["fraction_of_odds"],
    )


if __name__ == "__main__":
    main()
