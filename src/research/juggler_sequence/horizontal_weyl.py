"""Species classification of the horizontal nil-orbit Weyl sums.

Not an equidistribution theorem, not a K3 bound, not a Paper B edit,
and not a reopen of the parked toolkit line (BB/GG/JJ stay final).

The nil-lift (`J-tower-heisenberg-coordinate`) reduced the rate-free
tower target to equidistribution of the floor-Hardy orbit
    n |-> ((3/2) v^{3/4}, v^{3/2}, 0) Gamma  x  (1/2) v^{9/4}
with v = floor(n^{3/2}) (Paper B's m).  The recorded best next
question was whether the FIXED-harmonic Weyl sums of the horizontal
triple admit power savings by Theorem R's van der Corput chain.

This branch answers that question by species, not by a new bound.

**Identities (EXACT — HUMAN PROOF, `J-horizontal-axis-species`).**
Let X = n^{3/2}, v = floor(X), theta = {X}.  Lagrange Taylor of
x |-> x^alpha at X with remainder (1/2) f''(xi) theta^2,
xi in (v, X), gives three exact unwinds:

    v^{3/4}  = n^{9/8}  - (3/4) n^{-3/8} theta + R_{3/4},
        -(3/32) v^{-5/4} theta^2 <= R_{3/4} <= 0
    v^{3/2}  = n^{9/4}  - (3/2) n^{3/4}  theta + R_{3/2},
        0 <= R_{3/2} <= (3/8) v^{-1/2} theta^2
    v^{9/4}  = n^{27/8} - (9/4) n^{15/8} theta + R_{9/4},
        (45/32) v^{1/4} theta^2 <= R_{9/4} <= (45/32) X^{1/4} theta^2

(The keep-m forms of the first and third are Lemma G,
`J-second-order-linearization`; they are reused, not re-proved.)

**First-difference of the abelian axis.**  For odd n, step 2,
    v(n+2) - v(n) = floor(Delta X) + kappa,   kappa in {0,1},
and by the mean-value theorem
    v(n+2)^{9/4} - v(n)^{9/4} = (9/4) xi^{5/4} (v(n+2)-v(n)).
The carry term has amplitude C = (9/4) xi^{5/4} ~ n^{15/8} (below
Theorem R's engine line 9/4) and derivative C' ~ n^{7/8} >> 1
(GG species: no drift-1 window).

**Species table.**

- axis v^{3/4}: leftover A ~ n^{-3/8} decaying.  Classical van der
  Corput on e(k n^{9/8}).  Reduction lemma.
- axis v^{3/2}: leftover A ~ n^{3/4}, A' ~ n^{-1/4} << 1.  Tame
  amplitude-product; Theorem C substrate.  Theorem R at alpha = 0
  is not citable (`J-w-family-below-nine-eighths` is CONJECTURE,
  Corollary R' withdrawn).
- axis v^{9/4} unwind: A ~ n^{15/8}, A' ~ n^{7/8} >> 1.  HH species.
  Forbidden as a proof route by `J-nested-floor-without-W-family`
  (do not replace nested floors by smooth powers).
- axis v^{9/4} one Weyl step: spawned carry amp 15/8 < 9/4, but
  C' >> 1.  GG species.  The Theorem-R shortcut dies
  (`J-horizontal-theorem-r-shortcut`, REFUTED).

Mixed harmonics with k_3 != 0 are dominated by the 9/4 axis.
The rate-free conjecture is unharmed: it never needed a rate.

Probe contents (exact scaled-integer roots, sample scan — not a
new Weyl census; the nil-lift already has 124 harmonics at
square-root scale):

- `unwind_check`: remainder ratios against the three Taylor
  constants.
- `lemma_g_check`: reuse `second_order_scan` as the keep-m oracle.
- `first_difference_check`: mean-value enclosure, carry in {0,1},
  C / n^{15/8} and C' / n^{7/8} against the exact leading
  coefficients 9/4 and 135/32.
- `species`: the A/A' table and ledger match.
"""

from __future__ import annotations

import json
from math import isqrt
from pathlib import Path
from typing import Any

from research.juggler_sequence.bracket_nil_lift import scaled_root4, scaled_sqrt
from research.juggler_sequence.power_itineraries import ANTI_OVERCLAIM
from research.juggler_sequence.two_step_parity import second_order_scan

REPO_ROOT = Path(__file__).resolve().parents[3]
DATA_DIR = REPO_ROOT / "data" / "research" / "juggler" / "horizontal_weyl"
JSON_PATH = DATA_DIR / "summary.json"

DIGITS = 40
THETA_MIN = 1e-8
ENGINE_LINE = 9.0 / 4.0  # Theorem R Step-3 theta-coefficient line
BOUND_34 = 3.0 / 32.0
BOUND_32 = 3.0 / 8.0
BOUND_94 = 45.0 / 32.0
C_LEADING = 9.0 / 4.0  # C / n^{15/8} -> 9/4
CPRIME_LEADING = 135.0 / 32.0  # C' / n^{7/8} -> 135/32

IDENTITY_SAMPLES: tuple[int, ...] = tuple(range(5, 501, 2)) + (
    10**4 + 1,
    10**5 + 1,
    10**6 + 1,
    10**8 + 1,
    10**10 + 1,
    10**12 + 1,
)
LEMMA_G_SAMPLES: tuple[int, ...] = tuple(range(5, 501, 2)) + (
    10**6 + 1,
    10**9 + 1,
)
# consecutive odd stretches for the first-difference engine-line check
DIFF_BLOCKS: tuple[tuple[int, int], ...] = (
    (10**6 + 1, 10**6 + 1 + 400),  # 200 odd steps
    (10**8 + 1, 10**8 + 1 + 80),  # 40 odd steps
)

CLASS_GREEN = "HORIZONTAL_WEYL_GREEN"
CLASS_VIOLATED = "HORIZONTAL_WEYL_VIOLATED"

ANTI = {
    **ANTI_OVERCLAIM,
    "equidistribution_claimed": False,
    "k3_bound_claimed": False,
    "toolkit_reopened": False,
    "paper_b_modified": False,
    "theorem_r_cited_at_alpha_zero": False,
    "density_one_claimed": False,
}


def scaled_eighth(m: int, digits: int) -> int:
    """floor-ish of m^{1/8} * 10^digits up to a few units."""

    return isqrt(isqrt(isqrt(m * 10 ** (8 * digits))))


def _axis_data(n: int, digits: int = DIGITS) -> dict[str, Any]:
    """Scaled roots for the three unwind identities at one odd n."""

    scale = 10**digits
    v = isqrt(n * n * n)
    r_x = scaled_sqrt(n * n * n, digits)  # X = n^{3/2}
    theta_scaled = r_x % scale
    r_n38 = scaled_eighth(n**3, digits)  # n^{3/8}
    r_n98 = scaled_eighth(n**9, digits)  # n^{9/8}
    r_n34 = scaled_root4(n**3, digits)  # n^{3/4}
    r_n94 = scaled_root4(n**9, digits)  # n^{9/4}
    r_n158 = scaled_eighth(n**15, digits)  # n^{15/8}
    r_n278 = scaled_eighth(n**27, digits)  # n^{27/8}
    r_v34 = scaled_root4(v**3, digits)  # v^{3/4}
    r_v32 = scaled_sqrt(v**3, digits)  # v^{3/2}
    r_v94 = scaled_root4(v**9, digits)  # v^{9/4}
    r_v14 = scaled_root4(v, digits)  # v^{1/4}
    r_v12 = scaled_sqrt(v, digits)  # v^{1/2}
    r_v54 = scaled_root4(v**5, digits)  # v^{5/4}
    return {
        "n": n,
        "v": v,
        "scale": scale,
        "theta": theta_scaled / scale,
        "theta_scaled": theta_scaled,
        "r_x": r_x,
        "r_n38": r_n38,
        "r_n98": r_n98,
        "r_n34": r_n34,
        "r_n94": r_n94,
        "r_n158": r_n158,
        "r_n278": r_n278,
        "r_v34": r_v34,
        "r_v32": r_v32,
        "r_v94": r_v94,
        "r_v14": r_v14,
        "r_v12": r_v12,
        "r_v54": r_v54,
    }


def floor_sqrt_diff(a: int, b: int) -> int:
    """floor(sqrt(a) - sqrt(b)) for integers a > b > 0, exact."""

    num = a - b

    def leq(m: int) -> bool:
        if m <= 0:
            return True
        rhs = num * num - m * m * (a + b)
        if rhs < 0:
            return False
        return 4 * m * m * m * m * a * b <= rhs * rhs

    lo, hi = 0, isqrt(a) - isqrt(b) + 1
    while lo < hi:
        mid = (lo + hi + 1) // 2
        if leq(mid):
            lo = mid
        else:
            hi = mid - 1
    return lo


def _remainders(d: dict[str, Any]) -> dict[str, float]:
    """Exact-combination remainders for the three unwind identities.

    Each remainder is assembled as one integer before any float
    division (nil-lift precision lesson).
    """

    s = d["scale"]
    th = d["theta_scaled"]
    # R_34 = v^{3/4} - n^{9/8} + (3/4) n^{-3/8} theta
    #      = (r_v34 - r_n98)/s + (3/4) th / r_n38
    num_34 = 4 * d["r_n38"] * (d["r_v34"] - d["r_n98"]) + 3 * th * s
    r34 = num_34 / (4 * s * d["r_n38"])
    # R_32 = v^{3/2} - n^{9/4} + (3/2) n^{3/4} theta
    num_32 = 2 * s * (d["r_v32"] - d["r_n94"]) + 3 * d["r_n34"] * th
    r32 = num_32 / (2 * s * s)
    # R_94 = v^{9/4} - n^{27/8} + (9/4) n^{15/8} theta
    num_94 = 4 * s * (d["r_v94"] - d["r_n278"]) + 9 * d["r_n158"] * th
    r94 = num_94 / (4 * s * s)
    return {"r34": r34, "r32": r32, "r94": r94}


def unwind_check(
    samples: tuple[int, ...] = IDENTITY_SAMPLES, digits: int = DIGITS
) -> dict[str, Any]:
    """Witness the three Taylor remainder bounds on a sample list."""

    worst_34 = 0.0
    worst_32 = 0.0
    worst_94_hi = 0.0
    worst_94_lo = float("inf")
    worst_n = {"34": 0, "32": 0, "94": 0}
    used = 0
    failed: list[dict[str, Any]] = []
    for n in samples:
        if n < 5 or n % 2 == 0:
            continue
        d = _axis_data(n, digits)
        theta = d["theta"]
        if theta < THETA_MIN:
            continue
        rem = _remainders(d)
        used += 1
        v14 = d["r_v14"] / d["scale"]
        v12 = d["r_v12"] / d["scale"]
        v54 = d["v"] * v14  # v^{5/4} = v * v^{1/4}
        ratio_34 = abs(rem["r34"]) * v54 / (theta * theta)
        ratio_32 = rem["r32"] * v12 / (theta * theta)
        x14 = d["r_n38"] / d["scale"]  # n^{3/8} = X^{1/4}
        ratio_94_hi = rem["r94"] / (x14 * theta * theta) if theta > 0 else 0.0
        ratio_94_lo = rem["r94"] / (v14 * theta * theta) if theta > 0 else 0.0
        if ratio_34 > worst_34:
            worst_34 = ratio_34
            worst_n["34"] = n
        if ratio_32 > worst_32:
            worst_32 = ratio_32
            worst_n["32"] = n
        if ratio_94_hi > worst_94_hi:
            worst_94_hi = ratio_94_hi
            worst_n["94"] = n
        if ratio_94_lo < worst_94_lo:
            worst_94_lo = ratio_94_lo
        slack = 1.0 + 1e-4
        ok_34 = rem["r34"] <= 1e-12 and ratio_34 <= BOUND_34 * slack
        ok_32 = rem["r32"] >= -1e-12 and ratio_32 <= BOUND_32 * slack
        ok_94 = (
            rem["r94"] >= -1e-12
            and ratio_94_hi <= BOUND_94 * slack
            and ratio_94_lo >= BOUND_94 / slack
        )
        if not (ok_34 and ok_32 and ok_94):
            failed.append(
                {
                    "n": n,
                    "ok_34": ok_34,
                    "ok_32": ok_32,
                    "ok_94": ok_94,
                    "ratio_34": ratio_34,
                    "ratio_32": ratio_32,
                    "ratio_94_hi": ratio_94_hi,
                    "ratio_94_lo": ratio_94_lo,
                }
            )
    return {
        "samples_used": used,
        "worst_ratio_34": worst_34,
        "worst_ratio_32": worst_32,
        "worst_ratio_94_hi": worst_94_hi,
        "worst_ratio_94_lo": worst_94_lo if worst_94_lo < float("inf") else 0.0,
        "worst_n": worst_n,
        "bound_34": BOUND_34,
        "bound_32": BOUND_32,
        "bound_94": BOUND_94,
        "failed": failed[:5],
        "holds": used > 0 and not failed,
    }


def first_difference_check(
    blocks: tuple[tuple[int, int], ...] = DIFF_BLOCKS, digits: int = DIGITS
) -> dict[str, Any]:
    """Mean-value enclosure, carry in {0,1}, C and C' leading ratios.

    C(n) = (9/4) v(n)^{5/4} is the spawned carry amplitude of one
    Weyl step on v^{9/4}.  The engine-line comparison is exact
    arithmetic on exponents (15/8 < 9/4); the probe witnesses
    C ~ n^{15/8} and C' ~ n^{7/8} >> 1 on the sample.
    """

    mvt_ok = 0
    mvt_fail = 0
    carry_ok = 0
    carry_fail = 0
    carries = 0
    c_ratios: list[float] = []
    cprime_ratios: list[float] = []
    min_c = float("inf")
    min_cprime = float("inf")
    for start, stop in blocks:
        prev: dict[str, Any] | None = None
        n = start if start % 2 == 1 else start + 1
        while n <= stop:
            d = _axis_data(n, digits)
            if prev is not None:
                v1, v2 = prev["v"], d["v"]
                dv = v2 - v1
                # Delta (v^{9/4}) from scaled roots
                dphi = (d["r_v94"] - prev["r_v94"]) / d["scale"]
                # (9/4) v^{5/4} bounds
                lo = C_LEADING * (prev["r_v54"] / prev["scale"]) * dv
                hi = C_LEADING * (d["r_v54"] / d["scale"]) * dv
                if dv > 0 and lo - 1e-6 <= dphi <= hi + 1e-6:
                    mvt_ok += 1
                else:
                    mvt_fail += 1
                # carry: Delta v = floor(Delta X) + kappa, kappa in {0,1}
                n_prev = prev["n"]
                floor_dx = floor_sqrt_diff((n_prev + 2) ** 3, n_prev**3)
                kappa = dv - floor_dx
                if kappa in (0, 1):
                    carry_ok += 1
                    carries += kappa
                else:
                    carry_fail += 1
                c = C_LEADING * (d["r_v54"] / d["scale"])
                n15 = d["r_n158"] / d["scale"]  # n^{15/8}
                if n15 > 0:
                    c_ratios.append(c / n15)
                    min_c = min(min_c, c)
                if prev is not None:
                    c_prev = C_LEADING * (prev["r_v54"] / prev["scale"])
                    cprime = abs(c - c_prev) / 2.0
                    r_n18 = scaled_eighth(n, digits)
                    n78 = n / (r_n18 / d["scale"]) if r_n18 else 0.0
                    if n78 > 0:
                        cprime_ratios.append(cprime / n78)
                        min_cprime = min(min_cprime, cprime)
            prev = d
            n += 2
    mean_c = sum(c_ratios) / len(c_ratios) if c_ratios else 0.0
    mean_cp = sum(cprime_ratios) / len(cprime_ratios) if cprime_ratios else 0.0
    return {
        "pairs": mvt_ok + mvt_fail,
        "mvt_holds": mvt_fail == 0 and mvt_ok > 0,
        "mvt_ok": mvt_ok,
        "carry_holds": carry_fail == 0 and carry_ok > 0,
        "carry_ok": carry_ok,
        "carry_ones": carries,
        "mean_c_over_n15": mean_c,
        "mean_cprime_over_n78": mean_cp,
        "c_leading": C_LEADING,
        "cprime_leading": CPRIME_LEADING,
        "min_c": min_c if min_c < float("inf") else 0.0,
        "min_cprime": min_cprime if min_cprime < float("inf") else 0.0,
        "c_below_engine": True,  # 15/8 < 9/4, exact
        "c_exponent": 15.0 / 8.0,
        "cprime_exponent": 7.0 / 8.0,
        "engine_line": ENGINE_LINE,
        "cprime_gg": min_cprime > 1.0 if min_cprime < float("inf") else False,
        "leading_c_close": abs(mean_c - C_LEADING) < 0.05,
        "leading_cprime_close": abs(mean_cp - CPRIME_LEADING) < 0.15,
    }


def species_table(diff: dict[str, Any]) -> dict[str, Any]:
    """A/A' classification and ledger match.  Exponents are exact."""

    return {
        "engine_line": ENGINE_LINE,
        "axes": [
            {
                "axis": "v^{3/4}",
                "unwind_A_exponent": -3.0 / 8.0,
                "unwind_Aprime_exponent": -11.0 / 8.0,
                "species": "decaying",
                "ledger_match": "classical van der Corput on e(k n^{9/8}); Proposition L style",
                "theorem_r_citable": False,
                "reduction_lemma": True,
            },
            {
                "axis": "v^{3/2}",
                "unwind_A_exponent": 3.0 / 4.0,
                "unwind_Aprime_exponent": -1.0 / 4.0,
                "species": "tame_amplitude_product",
                "ledger_match": (
                    "Theorem C substrate (J-nested-parity-discrepancy); "
                    "Theorem R at alpha=0 not citable "
                    "(J-w-family-below-nine-eighths is CONJECTURE)"
                ),
                "theorem_r_citable": False,
                "reduction_lemma": True,
            },
            {
                "axis": "v^{9/4}_unwind",
                "unwind_A_exponent": 15.0 / 8.0,
                "unwind_Aprime_exponent": 7.0 / 8.0,
                "species": "HH",
                "ledger_match": (
                    "J-nested-floor-without-W-family (REFUTED): do not "
                    "replace nested floors by smooth powers"
                ),
                "theorem_r_citable": False,
                "reduction_lemma": False,
            },
            {
                "axis": "v^{9/4}_weyl1",
                "unwind_A_exponent": 15.0 / 8.0,
                "unwind_Aprime_exponent": 7.0 / 8.0,
                "species": "GG",
                "ledger_match": (
                    "spawned carry amp 15/8 < 9/4 (BB does not fire) "
                    "but C' ~ n^{7/8} >> 1 (J-intra-block-harmonic-obstruction "
                    "species: no drift-1 window)"
                ),
                "theorem_r_citable": False,
                "reduction_lemma": False,
                "c_below_engine": diff["c_below_engine"],
                "cprime_gg": diff["cprime_gg"],
            },
        ],
        "mixed_harmonics": "k_3 != 0 dominated by the 9/4 axis",
        "shortcut_dead": True,
        "rate_free_target_unharmed": True,
    }


def build_summary(
    *,
    identity_samples: tuple[int, ...] = IDENTITY_SAMPLES,
    lemma_g_samples: tuple[int, ...] = LEMMA_G_SAMPLES,
    diff_blocks: tuple[tuple[int, int], ...] = DIFF_BLOCKS,
) -> dict[str, Any]:
    unwind = unwind_check(identity_samples)
    lemma_g = second_order_scan(lemma_g_samples)
    diff = first_difference_check(diff_blocks)
    species = species_table(diff)
    # falsifier (b): the 9/4 leftover is actually tame
    falsifier_b = not diff["cprime_gg"]
    ok = (
        unwind["holds"]
        and bool(lemma_g.get("holds"))
        and diff["mvt_holds"]
        and diff["carry_holds"]
        and diff["cprime_gg"]
        and diff["c_below_engine"]
        and not falsifier_b
    )
    summary: dict[str, Any] = {
        "experiment": "juggler_horizontal_weyl",
        "anti_overclaim": ANTI,
        "unwind": unwind,
        "lemma_g": {"holds": bool(lemma_g.get("holds")), "count": lemma_g.get("count")},
        "first_difference": diff,
        "species": species,
        "notes": {
            "identities": (
                "v^{3/4}=n^{9/8}-(3/4)n^{-3/8}theta+R, "
                "v^{3/2}=n^{9/4}-(3/2)n^{3/4}theta+R, "
                "v^{9/4}=n^{27/8}-(9/4)n^{15/8}theta+R, "
                "with the recorded Lagrange remainders"
            ),
            "shortcut": (
                "the Theorem-R shortcut for the horizontal half is closed: "
                "one Weyl step on v^{9/4} lands in GG species (C'>>1); "
                "unwinding v^{9/4} is HH and is forbidden by "
                "J-nested-floor-without-W-family"
            ),
            "target": "conjectures/active/juggler_tower_rate_free_equidistribution.json",
        },
    }
    summary["decision"] = {
        "classification": CLASS_GREEN if ok else CLASS_VIOLATED,
        "shortcut_dead": True,
        "falsifier_b": falsifier_b,
    }
    return summary


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
    for key in ("decision", "unwind", "lemma_g", "first_difference", "species"):
        print(key, json.dumps(result[key], indent=2))
