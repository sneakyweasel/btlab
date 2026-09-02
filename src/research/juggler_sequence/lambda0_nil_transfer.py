"""Does the Heisenberg lift transfer Proposition 7.4 to lambda = 0?

Not a K3 bound, not a density-one claim, not a Paper B edit, and not
a reopen of differencing (BB) or character windows (GG). The only
candidate method under test is the Heisenberg dictionary of the
Proposition 7.4 shift.

**Identity (EXACT — HUMAN PROOF).** For arbitrary reals A, B, lambda,

    A {B + lambda} = A B + A lambda - A floor(B + lambda).

The last term, reduced mod 1, is the vertical Mal'cev coordinate of
the Heisenberg element

    g_lambda = [[1, A, 0], [0, 1, B + lambda], [0, 0, 1]]:

right-multiply by gamma with y-entry -floor(B + lambda) to obtain
(A, {B + lambda}, -A floor(B + lambda)), then reduce x and z.
This is the lambda-family of `J-tower-heisenberg-coordinate`
(replace B by B + lambda). The lift is group algebra, valid for
arbitrary real entries.

**Identity-section classification.** The special arithmetic of the
instance is the real parabola A^2 = (9/4) B (tower pair
A = (3/2) v^{3/4}, B = v^{3/2}) or A^2 = (9 k^2 / 16) B (pure-model
pair A = (3k/4) mu^{9/8}, B = mu^{9/4}). A parabola is not a
Leibman horizontal character k1 A + k2 B in Z, so it does not close
the horizontal torus and does not pin lambda = 0 as a
closed / rational / resonant fiber. The identity section is one
fiber of a free center circle. The parabola is consumed by making
A B a Hardy monomial — the reason the unshifted lift stays in the
coordinate ring — and does not distinguish the section.

**JJ dictionary.** (i) Integration over lambda is Haar measure on
the center (equivalently on the y-circle before reduction); pinning
the identity section is the same specific-point problem. No new
second averaging variable appears; the named family averages
(block index, mu_0, k-family) stay forbidden. (ii) A Fourier mode
j of the vertical coordinate is the same orbit at amplitude j A —
inverse self-similarity survives. (iii) The center-translation
speed is A, so S_lambda decorrelates at scale 1/A_max, the same
P^{-27/16} of JJ (iii). All three clauses survive.

Consequence: the Heisenberg lift is a dictionary for the
Proposition 7.4 shift, not a method outside BB/GG/JJ. The
quantitative K3 / HH line stays PARKED. Typicality of |S_0| on the
existing lambda-grid is a witness, not a transfer.

Probe contents (exact scaled-integer; cheap typicality only):

- `shifted_malcev_check`: Fraction identity and scaled-integer
  witnesses of A{B+lambda} = AB + A lambda - A floor(B+lambda).
- `identity_section`: algebraic parabola table plus a small
  horizontal-character sample (no Leibman form stays near 0).
- `jj_dictionary`: the three clauses in Heisenberg language.
- `typicality_witness`: place |S_0|/sqrt(L) in the existing
  shift_average_probe lambda-grid. Not a science window.
"""

from __future__ import annotations

import json
from fractions import Fraction
from math import floor, isqrt
from pathlib import Path
from typing import Any

from research.juggler_sequence.bracket_nil_lift import scaled_root4, tower_data
from research.juggler_sequence.power_itineraries import ANTI_OVERCLAIM
from research.juggler_sequence.two_step_parity import shift_average_probe

REPO_ROOT = Path(__file__).resolve().parents[3]
DATA_DIR = REPO_ROOT / "data" / "research" / "juggler" / "lambda0_nil_transfer"
JSON_PATH = DATA_DIR / "summary.json"

DIGITS = 22
# cheap typicality: reuse the existing oracle, not a P=10^10 census
TYPICALITY_P = 10**6
TEST_TYPICALITY_P = 10**4
TYPICALITY_LAMBDAS = 32
TYPICALITY_BLOCKS = 8
TEST_TYPICALITY_LAMBDAS = 16
TEST_TYPICALITY_BLOCKS = 4

CLASS_CLOSED = "LAMBDA0_NIL_TRANSFER_CLOSED"
CLASS_RESONANT = "LAMBDA0_NIL_TRANSFER_RESONANT"
CLASS_VIOLATED = "LAMBDA0_NIL_TRANSFER_VIOLATED"

ANTI = {
    **ANTI_OVERCLAIM,
    "equidistribution_claimed": False,
    "k3_bound_claimed": False,
    "hh_proved": False,
    "lambda0_transferred": False,
    "toolkit_reopened": False,
    "paper_b_modified": False,
    "typicality_is_not_a_transfer": True,
}


def shifted_malcev_pair(
    a: Fraction, b: Fraction, lam: Fraction
) -> dict[str, Fraction]:
    """Exact A{B+lambda} = AB + A lambda - A floor(B+lambda)."""

    frac = (b + lam) - floor(b + lam)
    lhs = a * frac
    rhs = a * b + a * lam - a * floor(b + lam)
    vertical = -a * floor(b + lam)
    return {
        "lhs": lhs,
        "rhs": rhs,
        "vertical": vertical,
        "abelian": a * b + a * lam,
    }


def shifted_malcev_check() -> dict[str, Any]:
    """Exact Fraction witnesses and one scaled tower witness."""

    pairs = (
        (Fraction(37, 13), Fraction(155, 17), Fraction(0)),
        (Fraction(37, 13), Fraction(155, 17), Fraction(2, 5)),
        (Fraction(12345, 8), Fraction(998, 3), Fraction(-4, 7)),
        (Fraction(3, 2), Fraction(9, 4), Fraction(1, 3)),
    )
    exact_ok = True
    for a, b, lam in pairs:
        d = shifted_malcev_pair(a, b, lam)
        if d["lhs"] != d["rhs"]:
            exact_ok = False
        if d["lhs"] != d["abelian"] + d["vertical"]:
            exact_ok = False

    # scaled tower witness at lambda = 0: A{B} = AB - A floor(B).
    # Combine at the product scale 2 * scale^2 so the identity is
    # an integer: r_b = z * scale + theta, hence
    # r_a34 * theta + r_a34 * z * scale = r_a34 * r_b.
    scale = 10**DIGITS
    n = 100_001
    td = tower_data(n, DIGITS)
    theta = td["r_b"] % scale
    lhs = 3 * td["r_a34"] * theta
    vert = 3 * td["r_a34"] * td["z"] * scale
    ab = 3 * td["r_a34"] * td["r_b"]
    scaled_gap = abs(lhs + vert - ab)
    return {
        "exact_pairs": len(pairs),
        "exact_identity": exact_ok,
        "scaled_n": n,
        "scaled_gap": int(scaled_gap),
        "scaled_identity": scaled_gap == 0,
        "heisenberg_dictionary": (
            "-A floor(B+lambda) mod 1 is the vertical Mal'cev "
            "coordinate of g_lambda = ((A, B+lambda, 0))"
        ),
    }


def _torus_dist(x: float) -> float:
    f = x - floor(x)
    return min(f, 1.0 - f)


def _character_sample(n_values: list[int]) -> dict[str, Any]:
    """Leibman horizontal forms k1 A + k2 B on a handful of tower starts.

    A resonance that pins the identity section would keep some
    nonzero (k1, k2) near Z at every sample. A growing monomial
    pair cannot do that.
    """

    scale = 10**DIGITS
    worst_near_z = 1.0
    worst_k = (0, 0)
    max_spread = 0.0
    ks = [(k1, k2) for k1 in range(-2, 3) for k2 in range(-2, 3) if k1 or k2]
    for k1, k2 in ks:
        vals = []
        for n in n_values:
            td = tower_data(n, DIGITS)
            # k1 A + k2 B ~ (k1 * 3 r_a34 + k2 * 2 r_b) / (2 scale)
            num = k1 * 3 * td["r_a34"] + k2 * 2 * td["r_b"]
            vals.append(_torus_dist(num / (2 * scale)))
        near = min(vals)
        spread = max(vals) - min(vals)
        if near < worst_near_z:
            worst_near_z = near
            worst_k = (k1, k2)
        max_spread = max(max_spread, spread)
    return {
        "samples": n_values,
        "forms": len(ks),
        "min_torus_dist": worst_near_z,
        "worst_form": list(worst_k),
        "max_spread": max_spread,
        "no_constant_character": worst_near_z > 1e-4 or max_spread > 0.05,
    }


def identity_section() -> dict[str, Any]:
    """Classify lambda = 0 against the special arithmetic A^2 ~ B."""

    scale = 10**DIGITS
    n = 100_001
    td = tower_data(n, DIGITS)
    # (v^{3/4})^2 = v^{3/2}: r_a34^2 / scale ~ r_b
    parabola_gap = abs(td["r_a34"] ** 2 - td["r_b"] * scale)
    parabola_ok = parabola_gap <= 2 * td["r_a34"] + scale

    # pure-model pair at an integer mu: A = (3/4) mu^{9/8}, B = mu^{9/4}.
    # mu^{9/8} = sqrt(mu^{9/4}), so isqrt(mu94 * scale) ~ mu^{9/8} * scale
    # and the parabola (mu^{9/8})^2 = mu^{9/4} is mu98^2 ~ mu94 * scale.
    mu = 10**6 + 3
    mu94 = scaled_root4(mu**9, DIGITS)
    mu98 = isqrt(mu94 * scale)
    pure_gap = abs(mu98**2 - mu94 * scale)
    pure_ok = pure_gap <= 2 * mu98 + 1

    chars = _character_sample([10001, 54321, 100_001, 200_001, 400_001])
    free_fiber = (
        parabola_ok
        and pure_ok
        and chars["no_constant_character"]
    )
    return {
        "tower_parabola": "A^2 = (9/4) B for A = (3/2) v^{3/4}, B = v^{3/2}",
        "tower_parabola_exact_algebra": True,
        "tower_scaled_ok": parabola_ok,
        "tower_scaled_gap": int(parabola_gap),
        "pure_parabola": "A^2 = (9 k^2 / 16) B for A = (3k/4) mu^{9/8}",
        "pure_parabola_exact_algebra": True,
        "pure_scaled_ok": pure_ok,
        "leibman_character": (
            "k1 A + k2 B in Z is a linear form; A^2 - (9/4) B = 0 "
            "is a real parabola and is not a horizontal character"
        ),
        "character_sample": chars,
        "fiber_type": "free_center_fiber" if free_fiber else "resonant_or_failed",
        "lambda0_special": False if free_fiber else True,
        "reason": (
            "the parabola is consumed by making AB a Hardy monomial; "
            "it does not close the horizontal torus and does not pin "
            "the identity section among center fibers"
        ),
    }


def jj_dictionary() -> dict[str, Any]:
    """Translate JJ (i)-(iii) into Heisenberg language. No retest."""

    return {
        "i": {
            "jj": (
                "no second averaging variable; family averages "
                "(block index, mu_0, k-family) re-enter BB/GG/CC"
            ),
            "heisenberg": (
                "integration over lambda is Haar on the center "
                "(y-circle before reduction); pinning lambda = 0 is "
                "pinning the identity section. No new lattice "
                "direction appears: amplitude separation still forces "
                "A(p) ~ A(q) to imply p = q. Named family averages "
                "stay forbidden and are not retested"
            ),
            "verdict": "survives",
        },
        "ii": {
            "jj": (
                "concentration inverse for A{B} is sum e(j A {B}) — "
                "the same class at amplitude j A"
            ),
            "heisenberg": (
                "a Fourier mode j of the vertical Mal'cev coordinate "
                "is the orbit at amplitude j A; the class is closed "
                "under its own inverse theory on the nilmanifold too"
            ),
            "verdict": "survives",
        },
        "iii": {
            "jj": (
                "|dS/dlambda| <= 2 pi A_max L; decorrelation at "
                "1/A_max ~ P^{-27/16}"
            ),
            "heisenberg": (
                "y-translation deposits -A lambda in the center; the "
                "translation speed is A, so the correlation length on "
                "the center circle is 1/A — the same scale, not a "
                "new one"
            ),
            "verdict": "survives",
        },
        "new_average": False,
        "new_scale": False,
        "all_survive": True,
    }


def typicality_witness(
    p_block: int = TYPICALITY_P,
    n_lambda: int = TYPICALITY_LAMBDAS,
    n_blocks: int = TYPICALITY_BLOCKS,
    k: int = 1,
) -> dict[str, Any]:
    """Place |S_0|/sqrt(L) in the existing lambda-grid distribution.

    Reuses the exact scaled-integer model of `shift_average_probe`.
    Typicality is a witness, not a transfer (ANTI flag).
    """

    from math import cos, pi, sin

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

    def s_abs(pre: list[tuple[int, int]], lam: int) -> float:
        re = im = 0.0
        for frac, mu98 in pre:
            x = 3 * k * mu98 * ((frac + lam) % sc) // (4 * sc) % sc
            ph = 2 * pi * (x / sc)
            re += cos(ph)
            im += sin(ph)
        return (re * re + im * im) ** 0.5

    ratios_0: list[float] = []
    ratios_all: list[float] = []
    ranks: list[int] = []
    for b in range(n_blocks):
        pre = block_pre(mu0 + 2 * a * block_len * b)
        vals = [s_abs(pre, j * sc // n_lambda) / block_len**0.5 for j in range(n_lambda)]
        ratios_all.extend(vals)
        r0 = vals[0]
        ratios_0.append(r0)
        ranks.append(sum(1 for v in vals if v <= r0))

    oracle = shift_average_probe(
        p_block, n_lambda=min(n_lambda, 16), n_blocks=min(n_blocks, 8), k=k
    )
    mean_0 = sum(ratios_0) / len(ratios_0)
    mean_all = sum(ratios_all) / len(ratios_all)
    # Rayleigh(1) for |complex Gaussian| / sqrt(L) has mean ~1; we only
    # ask that S_0 is not a unique extreme (falsifier b empirically)
    typical = mean_0 < 4.0 and max(ratios_0) < 8.0
    return {
        "p_block": p_block,
        "block_len": block_len,
        "n_lambda": n_lambda,
        "n_blocks": n_blocks,
        "mean_abs_S0_over_sqrt_L": round(mean_0, 4),
        "mean_abs_S_lambda_over_sqrt_L": round(mean_all, 4),
        "max_abs_S0_over_sqrt_L": round(max(ratios_0), 4),
        "median_rank_of_S0_among_grid": sorted(ranks)[len(ranks) // 2],
        "grid_size": n_lambda,
        "typical": typical,
        "typicality_is_not_a_transfer": True,
        "shift_average_oracle": {
            "mean_R_over_shifts": oracle["mean_R_over_shifts"],
            "stability_increments": oracle["stability_increments"],
        },
    }


def build_summary(
    *,
    p_block: int = TYPICALITY_P,
    n_lambda: int = TYPICALITY_LAMBDAS,
    n_blocks: int = TYPICALITY_BLOCKS,
) -> dict[str, Any]:
    identity = shifted_malcev_check()
    section = identity_section()
    dictionary = jj_dictionary()
    typicality = typicality_witness(p_block, n_lambda, n_blocks)
    identity_ok = identity["exact_identity"] and identity["scaled_identity"]
    free = section["fiber_type"] == "free_center_fiber"
    if not identity_ok:
        classification = CLASS_VIOLATED
    elif not free:
        classification = CLASS_RESONANT
    else:
        classification = CLASS_CLOSED
    return {
        "experiment": "juggler_lambda0_nil_transfer",
        "anti_overclaim": ANTI,
        "shifted_malcev": identity,
        "identity_section": section,
        "jj_dictionary": dictionary,
        "typicality": typicality,
        "decision": {
            "classification": classification,
            "reopen": "CLOSE",
            "v_hh_status": "PARKED",
            "new_average": False,
            "notes": (
                "the Heisenberg lift is a dictionary for the "
                "Proposition 7.4 shift; JJ (i)-(iii) survive; "
                "lambda = 0 is a free center fiber; Conjectures "
                "V/HH stay PARKED"
            ),
        },
    }


def write_artifacts(summary: dict[str, Any] | None = None) -> dict[str, Any]:
    if summary is None:
        summary = build_summary()
    DATA_DIR.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(
        json.dumps(summary, indent=2, ensure_ascii=False) + "\n", encoding="utf-8"
    )
    return summary


if __name__ == "__main__":
    result = write_artifacts()
    for key in (
        "decision",
        "shifted_malcev",
        "identity_section",
        "jj_dictionary",
        "typicality",
    ):
        print(key, json.dumps(result[key], indent=2, default=str))
