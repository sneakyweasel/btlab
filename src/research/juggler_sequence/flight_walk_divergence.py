"""Flight walk-divergence: no descent-free flight has bounded walk.

Not a halt theorem, not a divergence-orbit existence claim, not a
Paper A or Paper B edit, and not a reopen of the parked
asymptotic-descent envelope program or the refuted ambient-to-orbit
parity transfer.

The theorem (EXACT - HUMAN PROOF; components Lean) recorded by this
branch: every descent-free Juggler flight (an infinite orbit with
x_k >= n for all k) has unbounded exponent walk
u_k = a_k log2 3 - k. Proof skeleton:

1. u_k <= B for all k forces x_k <= n^{2^B} (Lean upper envelope,
   power_bound_word / follows_log_le_walkWeight);
2. finitely many states force eventual periodicity (pigeonhole);
3. a realized period word is strictly expanding (Lean
   cycle_strict_envelope: 2^p < 3^o, since 3^o = 2^p is impossible
   for p >= 1 and a contracting return contradicts itself);
4. so u gains delta = log2(3^o / 2^p) > 0 per period - unbounded.

Consequences quantified here with exact integer arithmetic:

- The hug walk band: the exact hug rule keeps 2^k <= 3^{a_k} < 3*2^k
  (Lean hugOdds_pow_ge / hugOdds_pow_lt), i.e. u in [0, log2 3);
  states of a hug-hugging flight would sit in [n, n^3).
- Drift table: for the hug pairs (L, o_min) at the leftover /
  survivor-lattice lengths, the per-period walk gain
  delta(L) = log2(3^o / 2^L) > 0 exactly (integer comparison), with
  the escape time (number of period traversals to exceed a given
  walk excess B) - how fast a hypothetical near-hug eventual cycle
  is forced away from the hug band.

Float logarithms are diagnostic; every inequality verdict
(3^o > 2^L, hug band) is exact integer arithmetic.
"""

from __future__ import annotations

import json
import math
from pathlib import Path
from typing import Any

from research.juggler_sequence.lean_paths import (
    LAYERS,
    has_named,
)
from research.juggler_sequence.power_itineraries import ANTI_OVERCLAIM

REPO_ROOT = Path(__file__).resolve().parents[3]
DATA_DIR = REPO_ROOT / "data" / "research" / "juggler" / "flight_walk_divergence"
JSON_PATH = DATA_DIR / "summary.json"

LOG2_3 = math.log2(3.0)

HUG_BAND_WINDOW = 200_000
TEST_BAND_WINDOW = 5_000

# leftover / survivor-lattice lengths (hug pairs (L, hugOdds L))
DRIFT_LENGTHS = (84, 1054, 25781, 50508, 176251, 301994, 478245)
ESCAPE_EXCESS = (2.0, 10.0, 100.0)

CLASS_CONFIRMED = "FLIGHT_WALK_DIVERGENCE_CONFIRMED"
CLASS_VIOLATED = "FLIGHT_WALK_DIVERGENCE_VIOLATED"

ANTI = {
    **ANTI_OVERCLAIM,
    "halt_theorem": False,
    "divergent_orbit_exists": False,
    "all_flights_killed": False,
    "paper_b_pointwise_transfer": False,
    "ambient_transfer_reopened": False,
    "asymptotic_descent_program_reopened": False,
    "paper_a_modified": False,
    "paper_b_modified": False,
}

REQUIRED_LEAN = (
    ("Envelope", "power_bound_word"),
    ("Envelope", "cycle_strict_envelope"),
    ("WalkChargeItineraries", "hugOdds_pow_ge"),
    ("WalkChargeItineraries", "hugOdds_pow_lt"),
    ("WalkTransport", "follows_log_le_walkWeight"),
    ("WalkTransport", "aboveAnchor_height_of_walk"),
    ("CycleCore", "aboveAnchor_prefix_pow_le"),
)


def _log2_pow3(o: int) -> float:
    """log2(3^o) to ~1e-10 absolute, without float overflow."""

    x = 3**o
    bits = x.bit_length()
    if bits <= 900:
        return math.log2(x)
    top = x >> (bits - 64)
    return (bits - 64) + math.log2(top)


def hug_band_check(k_max: int) -> dict[str, Any]:
    """Exact mirror of hugOdds_pow_ge / hugOdds_pow_lt on [0, k_max].

    The exact hug rule (play E iff 3^a >= 2^{k+1}) keeps
    2^k <= 3^{a_k} < 3 * 2^k, i.e. u_k in [0, log2 3).
    """

    a = 0
    pow3 = 1
    pow2 = 1
    violations = 0
    u_max = 0.0
    for k in range(1, k_max + 1):
        if pow3 < 2 * pow2:  # u < 1: play O
            a += 1
            pow3 *= 3
        pow2 *= 2
        if not (pow2 <= pow3 < 3 * pow2):
            violations += 1
        u = a * LOG2_3 - k
        if u > u_max:
            u_max = u
    return {
        "window": k_max,
        "violations": violations,
        "band_ok": violations == 0,
        "u_max": round(u_max, 8),
        "u_band_top": round(LOG2_3, 8),
        "state_band_exponent": 3.0,  # 2^{1+log2(3/2)} = 3 exactly
    }


def hug_odds(k_max: int) -> int:
    """hugOdds(k_max) = min{a : 2^k <= 3^a} = ceil(k log_3 2).

    Float estimate corrected by exact big-integer comparisons
    (`hugOdds_least` in Lean identifies the two definitions).
    """

    if k_max == 0:
        return 0
    a = math.ceil(k_max * math.log(2.0) / math.log(3.0))
    while 3**a < 2**k_max:
        a += 1
    while a >= 1 and 3 ** (a - 1) >= 2**k_max:
        a -= 1
    return a


def drift_row(length: int) -> dict[str, Any]:
    """Exact expansion drift of the hug pair (L, hugOdds L).

    delta = log2(3^o / 2^L) > 0 is the walk gain per traversal of a
    hypothetical eventual cycle with the minimal (hug) odd budget.
    Escape time t(B) = ceil(B / delta) traversals, ~ t(B) * L steps.
    """

    o = hug_odds(length)
    strictly_expanding = 3**o > 2**length
    delta = _log2_pow3(o) - length
    escapes = {
        str(b): {
            "traversals": math.ceil(b / delta) if delta > 0 else None,
            "steps_approx": math.ceil(b / delta) * length if delta > 0 else None,
        }
        for b in ESCAPE_EXCESS
    }
    return {
        "L": length,
        "o_hug": o,
        "strictly_expanding": strictly_expanding,
        "delta_log2_per_period": delta,
        "escape": escapes,
    }


def lean_wired() -> dict[str, bool]:
    texts = {
        module: LAYERS[module].read_text(encoding="utf-8")
        for module in {m for m, _ in REQUIRED_LEAN}
    }
    return {
        f"{module}.{name}": has_named(texts[module], name)
        for module, name in REQUIRED_LEAN
    }


def classify(summary: dict[str, Any]) -> str:
    band_ok = summary["hug_band"]["band_ok"]
    drifts_ok = all(r["strictly_expanding"] for r in summary["drift_table"])
    return CLASS_CONFIRMED if band_ok and drifts_ok else CLASS_VIOLATED


def build_summary(k_max: int = HUG_BAND_WINDOW) -> dict[str, Any]:
    summary: dict[str, Any] = {
        "experiment": "juggler_flight_walk_divergence",
        "anti_overclaim": ANTI,
        "hug_band": hug_band_check(k_max),
        "drift_table": [drift_row(length) for length in DRIFT_LENGTHS],
        "lean": lean_wired(),
        "notes": {
            "theorem": "every descent-free flight has unbounded exponent walk: bounded walk -> bounded states (Lean envelope) -> eventually periodic (pigeonhole) -> strictly expanding period word (Lean cycle_strict_envelope) -> walk grows by delta > 0 per period, contradiction",
            "delta": "per-period walk gain log2(3^o/2^L) of a hypothetical eventual cycle at the hug odd budget; positive for every L, so no eventual cycle keeps the walk in a band",
            "escape": "traversals of the period needed to exceed walk excess B over the hug band",
            "paper_b": "the proved Paper B depth-<=4 layer is ambient-density and stays transfer-blocked (TRANSFER_COMPLEX); it is not the killer and is not used",
        },
    }
    summary["classification"] = classify(summary)
    return summary


def main() -> dict[str, Any]:
    summary = build_summary()
    DATA_DIR.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(summary, indent=2), encoding="utf-8")
    print(
        json.dumps(
            {
                "classification": summary["classification"],
                "hug_band": summary["hug_band"],
                "drift_table": [
                    {
                        "L": r["L"],
                        "o_hug": r["o_hug"],
                        "delta": r["delta_log2_per_period"],
                        "escape_10_steps": r["escape"]["10.0"]["steps_approx"],
                    }
                    for r in summary["drift_table"]
                ],
                "lean": summary["lean"],
            },
            indent=2,
        )
    )
    return summary


if __name__ == "__main__":
    main()
