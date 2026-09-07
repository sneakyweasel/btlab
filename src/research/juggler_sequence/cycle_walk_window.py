"""Uniform census-free envelope on the whole length window.

Phase 0: for every L in [50508, 301994) at the certified floor, the
budgeted hug word at (L, o_min) equals the exact IET prefix (human
counting argument), the greedy Ostrowski digit sum obeys
s(L) <= sum a_{j+1} <= 46, and 2 s(L)/L stays under the J-gap, so
C_L < 1/(ln 3 ln n') for every window length with no census and no
DP. Envelope only: no new kills are claimed, the per-length finance
comparison still decides, and near-convergents such as L = 176251
still survive. Not a halt theorem, not a floor raise, not a uniform
B/theta claim.

Dossier: docs/problems/juggler_cycle_walk_window.md.
"""

from __future__ import annotations

from research.juggler_sequence.lean_paths import (
    DATA_ROOT,
)

import json
import math
from pathlib import Path
from typing import Any

from research.juggler_sequence.cycle_finance import git_commit
from research.juggler_sequence.cycle_walk_charge import (
    CERTIFIED_FLOOR,
    deficit_D,
)
from research.juggler_sequence.cycle_walk_envelope import gap_lower
from research.juggler_sequence.cycle_walk_greedy import hug_word
from research.juggler_sequence.cycle_walk_ostrowski import (
    X_HI,
    X_LO,
    certified_theta_cf,
    certify_x_bounds,
    exact_hug_word,
)

DATA_DIR = (
    DATA_ROOT
    / "cycle_walk_window"
)

WINDOW_LO = 50_508
WINDOW_HI = 301_994  # q_13 of theta, exclusive

# Extra non-leftover lengths for word-identity spot checks.
WORD_CHECK_LENGTHS = (60_000, 123_456, 250_000, 301_993)

CLASS_GREEN = "WALK_WINDOW_GREEN"
CLASS_PARK = "WALK_WINDOW_PARK"
CLASS_CLOSED = "WALK_WINDOW_CLOSED"


def o_min(length: int) -> int:
    """Exact minimal odd count: ceil(L x), decided by the x-sandwich."""

    f_lo = length * X_LO[0] // X_LO[1]
    f_hi = length * X_HI[0] // X_HI[1]
    if f_lo != f_hi:
        raise RuntimeError(f"o_min undecided at L={length}")
    return f_lo + 1


def digit_caps(cf: dict[str, Any]) -> dict[int, int]:
    """Greedy digit cap a_{j+1} per denominator q_j (top level: 1)."""

    quotients = cf["partial_quotients"]
    denominators = cf["denominators"]
    caps: dict[int, int] = {}
    for j, q in enumerate(denominators):
        caps[q] = quotients[j + 1] if j + 1 < len(quotients) else 1
    return caps


def window_scan(cf: dict[str, Any], n0: int = CERTIFIED_FLOOR) -> dict[str, Any]:
    denominators = sorted(set(cf["denominators"]), reverse=True)
    caps = digit_caps(cf)
    n = n0 + 1
    log_floor = math.log(n)
    cap_sum = sum(caps.values())
    max_seen: dict[int, int] = {q: 0 for q in denominators}
    s_hist: dict[int, int] = {}
    max_s = -1
    argmax_s = 0
    worst: list[tuple[float, int, int]] = []  # (ratio, L, s)
    caps_ok = True
    for length in range(WINDOW_LO, WINDOW_HI):
        rem = length
        s = 0
        for q in denominators:
            if q <= rem:
                b = rem // q
                rem -= b * q
                s += b
                if b > max_seen[q]:
                    max_seen[q] = b
                    if b > caps[q]:
                        caps_ok = False
        odd = o_min(length)
        log_n = log_floor - deficit_D(length, odd, n)
        ratio = (2.0 * s / length) / gap_lower(log_n)
        s_hist[s] = s_hist.get(s, 0) + 1
        if s > max_s:
            max_s, argmax_s = s, length
        worst.append((ratio, length, s))
        if len(worst) > 10 and length % 4096 == 0:
            worst.sort(reverse=True)
            del worst[10:]
    worst.sort(reverse=True)
    del worst[10:]
    return {
        "window": [WINDOW_LO, WINDOW_HI],
        "n_lengths": WINDOW_HI - WINDOW_LO,
        "digit_caps": {str(q): caps[q] for q in denominators},
        "max_digit_per_level": {str(q): max_seen[q] for q in denominators},
        "caps_ok": caps_ok,
        "cap_sum": cap_sum,
        "max_digit_sum": max_s,
        "argmax_digit_sum": argmax_s,
        "digit_sum_histogram": {str(k): s_hist[k] for k in sorted(s_hist)},
        "max_ratio": worst[0][0],
        "min_envelope_margin": 1.0 / worst[0][0],
        "worst_rows": [
            {"length": lg, "digit_sum": sv, "ratio_to_gap": rt}
            for rt, lg, sv in worst
        ],
        "all_below_gap": worst[0][0] < 1.0,
    }


def word_identity_checks(lengths: tuple[int, ...] = WORD_CHECK_LENGTHS) -> dict[str, Any]:
    rows = []
    for length in lengths:
        odd = o_min(length)
        word, exact_odds = exact_hug_word(length)
        budgeted = hug_word(length, odd)
        rows.append(
            {
                "length": length,
                "o_min": odd,
                "odds_match": exact_odds == odd,
                "word_matches": word == budgeted,
            }
        )
    return {
        "rows": rows,
        "all_match": all(r["odds_match"] and r["word_matches"] for r in rows),
    }


def classify(
    bounds: dict[str, Any],
    scan: dict[str, Any],
    words: dict[str, Any],
) -> dict[str, Any]:
    if (
        bounds["certified"]
        and scan["caps_ok"]
        and scan["max_digit_sum"] <= scan["cap_sum"]
        and scan["all_below_gap"]
        and words["all_match"]
    ):
        return {
            "label": CLASS_GREEN,
            "reason": (
                "every window length has greedy digits within the "
                "partial-quotient caps, digit sum at most "
                f"{scan['max_digit_sum']} <= {scan['cap_sum']}, and "
                "2s/L strictly under the J-gap, so the DK envelope "
                "prices C_L < 1/(ln 3 ln n') for every L in "
                "[50508, 301994) census-free; the budgeted hug is the "
                "exact IET prefix (human counting argument, spot-"
                "checked); no new kills claimed"
            ),
        }
    if not scan["all_below_gap"] or not scan["caps_ok"]:
        return {
            "label": CLASS_CLOSED,
            "reason": "a window length breaks the digit cap or the J-gap",
        }
    return {
        "label": CLASS_PARK,
        "reason": "scan holds but certification or word identity failed",
    }


def probe_payload() -> dict[str, Any]:
    bounds = certify_x_bounds()
    cf = certified_theta_cf()
    scan = window_scan(cf)
    words = word_identity_checks()
    return {
        "model": (
            "word identity: hug at (L, o_min) equals the exact IET "
            "prefix for every L because u stays in [0, 1+alpha) and a "
            "counting argument forbids budget divergence; uniform "
            "envelope: greedy Ostrowski digits obey b_j <= a_{j+1}, so "
            "s(L) <= sum a_{j+1} on [50508, 301994) and "
            "|C_L - C_*| <= 2 s(L)/L < J-gap for every window length"
        ),
        "x_certification": bounds,
        "theta_cf": cf,
        "scan": scan,
        "word_identity": words,
        "classification": classify(bounds, scan, words),
        "no_new_kills": True,
        "not_a_halt_theorem": True,
        "no_cycle_all_lengths": False,
        "not_a_uniform_ratio_theorem": True,
        "git_commit": git_commit(),
    }


def write_artifacts(payload: dict[str, Any] | None = None) -> dict[str, Any]:
    payload = payload or probe_payload()
    DATA_DIR.mkdir(parents=True, exist_ok=True)
    (DATA_DIR / "summary.json").write_text(
        json.dumps(payload, indent=2) + "\n", encoding="utf-8"
    )
    return payload


def main() -> None:
    payload = write_artifacts()
    scan = payload["scan"]
    words = payload["word_identity"]
    print(
        f"x bounds certified={payload['x_certification']['certified']}"
    )
    print(
        f"caps_ok={scan['caps_ok']} max_s={scan['max_digit_sum']} "
        f"(cap sum {scan['cap_sum']}) at L={scan['argmax_digit_sum']}"
    )
    print(
        f"max 2s/L over gap = {scan['max_ratio']:.4f} "
        f"(min envelope margin {scan['min_envelope_margin']:.3f}) "
        f"all_below_gap={scan['all_below_gap']}"
    )
    print(f"word identity spot checks all_match={words['all_match']}")
    print(payload["classification"]["label"])
    print(payload["classification"]["reason"])


if __name__ == "__main__":
    main()
