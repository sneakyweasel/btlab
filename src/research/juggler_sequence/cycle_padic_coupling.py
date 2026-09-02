"""Archimedean + 2-adic/3-adic coupling on a hypothetical CycleMin cycle.

Phase 0 only. Not a residue-modular census, not a Baker/Rhin reopen,
not the parked x^3-y^2 campaign, not a floor raise, and not a halt
theorem.

The literature target is a single quantity that is simultaneously
archimedean-close (from 2^L ≈ 3^o) and of large 2-adic or 3-adic
valuation (from the floor cells or the return), so that lifting-the-
exponent or Chim-type two-p-adic-logarithm bounds become incompatible.
This module asks whether any exact Juggler identity produces that
quantity.

Dossier: docs/problems/juggler_cycle_padic_coupling.md.
"""

from __future__ import annotations

import json
from pathlib import Path
from typing import Any

from research.juggler_sequence.cycle_error_transport import letter_transport
from research.juggler_sequence.cycle_finance import git_commit, o_min_and_theta
from research.juggler_sequence.global_defect import (
    follows_itinerary,
    global_defect,
    image_after,
    local_defect,
    odd_count,
)
from research.juggler_sequence.lean_paths import (
    JUGGLER_DIR,
    JUGGLER_PAPER_BARREL,
    has_named,
    juggler_text,
)
from research.juggler_sequence.power_itineraries import floor_power

REPO_ROOT = Path(__file__).resolve().parents[3]
DATA_DIR = REPO_ROOT / "data" / "research" / "juggler" / "cycle_padic_coupling"

CLASS_CLOSED = "PADIC_COUPLING_CLOSED"
CLASS_GREEN = "PADIC_COUPLING_GREEN"
CLASS_PARK = "PADIC_COUPLING_PARK"

LEFTOVER_EXACT = (19, 84, 569, 1054)
LEFTOVER_MODULAR = (19, 84, 569, 1054, 25781, 50508, 176251)
KNOWN_O = {
    19: 12,
    84: 53,
    569: 359,
    1054: 665,
    25781: 16266,
    50508: 31867,
    176251: 111169,
}

REALIZED = (
    (13, "OE"),
    (25, "OOOEE"),
    (365, "OOE"),
    (1517, "OOE"),
    (1_000_057, "OOE"),
    (365, "OOEOOE"),
)

LTE_N_MAX = 99
LTE_K_MAX = 24

EXISTING_LEAN = (
    "global_defect_identity",
    "image_eq_start_defectRatio",
    "cycleMin_finance",
    "cycle_remainder_balance",
)
FORBIDDEN_NEW_API = (
    "PadicCoupling",
    "ChimBound",
    "TwoAdicLogForm",
    "ThreeAdicLogForm",
)
FORBIDDEN_LEAN_FILES = (
    JUGGLER_DIR / "PadicCoupling.lean",
    JUGGLER_DIR / "CyclePadicCoupling.lean",
    JUGGLER_DIR / "Chim.lean",
)
PAPER_FORBIDDEN = ("PadicCoupling", "ChimBound", "TwoAdicLogForm")

VAL_INF = 10**9


def valuation(n: int, p: int) -> int:
    """p-adic valuation. ``VAL_INF`` means n = 0."""

    if p < 2:
        raise ValueError("p must be at least 2")
    if n == 0:
        return VAL_INF
    n = abs(n)
    v = 0
    while n % p == 0:
        n //= p
        v += 1
    return v


def lte_v2_pow_minus_1(n: int, k: int) -> int:
    """v_2(n^k - 1) for odd n ≥ 1 and k ≥ 1 (lifting-the-exponent)."""

    if n % 2 == 0 or n < 1 or k < 1:
        raise ValueError("need odd n ≥ 1 and k ≥ 1")
    if k % 2 == 1:
        return valuation(n - 1, 2)
    return valuation(n - 1, 2) + valuation(n + 1, 2) + valuation(k, 2) - 1


def lte_v3_pow_minus_1(n: int, k: int) -> int:
    """v_3(n^k - 1) for 3 ∤ n, and 0 when 3 | n."""

    if n < 1 or k < 1:
        raise ValueError("need n ≥ 1 and k ≥ 1")
    if n % 3 == 0:
        return 0
    if n % 3 == 1:
        return valuation(n - 1, 3) + valuation(k, 3)
    if k % 2 == 1:
        return 0
    return valuation(n - 1, 3) + valuation(n + 1, 3) + valuation(k, 3)


def gap_mod_valuations(length: int, odd: int) -> dict[str, Any]:
    """v_2 and v_3 of 3^o - 2^L from unique factorization, no big-int gap."""

    if length < 1 or odd < 1:
        raise ValueError("need L ≥ 1 and o ≥ 1")
    # 3^o odd, 2^L even ⇒ gap odd ⇒ v_2 = 0.
    # 3^o ≡ 0 (mod 3), 2^L ≡ (-1)^L (mod 3) ⇒ gap ≡ -(-1)^L ≢ 0.
    return {
        "L": length,
        "o": odd,
        "v2": 0,
        "v3": 0,
        "gap_odd": True,
        "gap_mod3": -((-1) ** length) % 3,
    }


def leftover_row(length: int, *, exact_gap: bool) -> dict[str, Any]:
    odd, theta = o_min_and_theta(length)
    row = gap_mod_valuations(length, odd)
    row["theta"] = theta
    row["exact_gap"] = None
    if exact_gap:
        gap = 3**odd - (1 << length)
        row["exact_gap"] = gap
        row["v2_exact"] = valuation(gap, 2)
        row["v3_exact"] = valuation(gap, 3)
        row["matches_lemma"] = row["v2_exact"] == 0 and row["v3_exact"] == 0
    # Chim-applicable closeness-to-1 forms, not closeness to each other.
    row["v2_3o_minus_1"] = lte_v2_pow_minus_1(3, odd)
    if length % 2 == 1:
        row["v3_2L_minus_1"] = 0
    else:
        row["v3_2L_minus_1"] = 1 + valuation(length, 3)
    return row


def unit_obstruction(length: int, odd: int) -> dict[str, Any]:
    """2^L / 3^o is not a 2-adic or 3-adic unit, so ratio − 1 is not small."""

    return {
        "L": length,
        "o": odd,
        "v2_of_ratio": length,
        "v3_of_ratio": -odd,
        "is_2_adic_unit": False,
        "is_3_adic_unit": False,
        # In Q_2 the 2^L term vanishes, so 2^L/3^o − 1 → −1.
        "v2_of_ratio_minus_1": 0,
        # In Q_3 the 3^{-o} term dominates.
        "v3_of_ratio_minus_1": -odd,
        "chim_form_at_2": False,
        "chim_form_at_3": False,
    }


def lte_grid(*, n_max: int = LTE_N_MAX, k_max: int = LTE_K_MAX) -> dict[str, Any]:
    mismatches_2 = 0
    mismatches_3 = 0
    checked = 0
    for n in range(3, n_max + 1, 2):
        for k in range(1, k_max + 1):
            checked += 1
            actual2 = valuation(pow(n, k) - 1, 2)
            if actual2 != lte_v2_pow_minus_1(n, k):
                mismatches_2 += 1
            actual3 = valuation(pow(n, k) - 1, 3)
            if actual3 != lte_v3_pow_minus_1(n, k):
                mismatches_3 += 1
    return {
        "n_max": n_max,
        "k_max": k_max,
        "checked": checked,
        "mismatches_2": mismatches_2,
        "mismatches_3": mismatches_3,
        "ok": mismatches_2 == 0 and mismatches_3 == 0,
    }


def cycle_lte_formula(n: int, length: int, odd: int) -> dict[str, Any]:
    """Predicted valuations of Δ = n^{2^L}(n^{gap} − 1) on a CycleMin return."""

    if n % 2 == 0:
        raise ValueError("CycleMin n is odd")
    gap = 3**odd - (1 << length)
    # gap is odd, so v_2(n^{gap}−1) = v_2(n−1).
    v2_core = lte_v2_pow_minus_1(n, gap) if gap > 0 else VAL_INF
    v3_core = lte_v3_pow_minus_1(n, gap) if gap > 0 else VAL_INF
    v3_n = valuation(n, 3)
    return {
        "n": n,
        "L": length,
        "o": odd,
        "gap_odd": gap % 2 == 1,
        "v2_n_gap_minus_1": v2_core,
        "v2_n_minus_1": valuation(n - 1, 2),
        "v2_Delta": v2_core,
        "v3_n": v3_n,
        "v3_n_gap_minus_1": v3_core,
        "v3_Delta": length * v3_n + v3_core if v3_core < VAL_INF else VAL_INF,
        "grows_with_L": False,
        "grows_with_approximation": False,
    }


def realized_record(n: int, word: str) -> dict[str, Any]:
    if not follows_itinerary(n, word):
        raise ValueError(f"{n} does not follow {word}")
    rows = [letter_transport(n, word, index) for index in range(len(word))]
    delta = global_defect(n, word)
    end = image_after(n, word)
    v2_delta = valuation(delta, 2)
    v3_delta = valuation(delta, 3)
    term_v2 = [valuation(row["e"], 2) for row in rows]
    term_v3 = [valuation(row["e"], 3) for row in rows]
    last = rows[-1]
    last_chunk_v2 = valuation(last["chunk"], 2)
    local_rows = []
    current = n
    max_local_v2 = 0
    max_local_v3 = 0
    for letter in word:
        rho = local_defect(current)
        image = floor_power(current)
        width = 2 * image + 1
        v2_rho = valuation(rho, 2)
        v3_rho = valuation(rho, 3)
        max_local_v2 = max(max_local_v2, v2_rho if v2_rho < VAL_INF else 0)
        max_local_v3 = max(max_local_v3, v3_rho if v3_rho < VAL_INF else 0)
        local_rows.append(
            {
                "letter": letter,
                "x": current,
                "rho": rho,
                "width": width,
                "v2_rho": v2_rho,
                "v3_rho": v3_rho,
                "v2_width_bound": width.bit_length() - 1,
            }
        )
        current = image
    min_term_v2 = min(term_v2) if term_v2 else VAL_INF
    cancellation_2 = min_term_v2 - v2_delta if min_term_v2 < VAL_INF else 0
    coupled = (
        (v2_delta >= 3 or v3_delta >= 3)
        and end == n
        and (3 ** odd_count(word) - (1 << len(word))) < 3 ** odd_count(word) // 10
    )
    return {
        "n": n,
        "word": word,
        "end": end,
        "is_return": end == n,
        "o": odd_count(word),
        "L": len(word),
        "v2_delta": v2_delta,
        "v3_delta": v3_delta,
        "v2_n_minus_1": valuation(n - 1, 2),
        "min_transported_v2": min_term_v2,
        "min_transported_v3": min(term_v3) if term_v3 else VAL_INF,
        "last_letter": last["letter"],
        "last_chunk_v2": last_chunk_v2,
        "last_index": last["i"],
        "cancellation_2": cancellation_2,
        "max_local_v2": max_local_v2,
        "max_local_v3": max_local_v3,
        "local": local_rows,
        "coupled": coupled,
    }


def local_window(*, word: str = "OOE", lo: int = 13, hi: int = 400) -> dict[str, Any]:
    max_v2 = 0
    max_v3 = 0
    checked = 0
    high_v2 = 0
    for n in range(lo if lo % 2 else lo + 1, hi, 2):
        if not follows_itinerary(n, word):
            continue
        current = n
        for _letter in word:
            rho = local_defect(current)
            image = floor_power(current)
            v2_rho = valuation(rho, 2)
            v3_rho = valuation(rho, 3)
            if v2_rho < VAL_INF:
                max_v2 = max(max_v2, v2_rho)
                if v2_rho >= 8:
                    high_v2 += 1
            if v3_rho < VAL_INF:
                max_v3 = max(max_v3, v3_rho)
            current = image
        checked += 1
    return {
        "word": word,
        "lo": lo,
        "hi": hi,
        "checked": checked,
        "max_local_v2": max_v2,
        "max_local_v3": max_v3,
        "v2_at_least_8": high_v2,
    }


def lean_api_present() -> dict[str, bool]:
    text = juggler_text()
    paper = JUGGLER_PAPER_BARREL.read_text(encoding="utf-8")
    return {
        "sorry_free": "sorry" not in text and "admit" not in text,
        **{name: has_named(text, name) for name in EXISTING_LEAN},
        **{f"has_api_{name}": name in text for name in FORBIDDEN_NEW_API},
        **{
            f"has_file_{path.name}": path.exists()
            for path in FORBIDDEN_LEAN_FILES
        },
        "not_in_paper_barrel": all(name not in paper for name in PAPER_FORBIDDEN),
    }


def classify(scan: dict[str, Any], lean: dict[str, bool]) -> dict[str, Any]:
    leftover_zero = all(
        row["v2"] == 0 and row["v3"] == 0 for row in scan["leftover_modular"]
    )
    exact_ok = all(row.get("matches_lemma", True) for row in scan["leftover_exact"])
    units = all(
        (not rec["is_2_adic_unit"]) and (not rec["is_3_adic_unit"])
        for rec in scan["unit_obstruction"]
    )
    chim_off = all(
        (not rec["chim_form_at_2"]) and (not rec["chim_form_at_3"])
        for rec in scan["unit_obstruction"]
    )
    lte_ok = scan["lte_grid"]["ok"]
    no_coupled = not any(rec["coupled"] for rec in scan["realized"])
    lte_cycle_bounded = all(
        (not rec["grows_with_L"]) and (not rec["grows_with_approximation"])
        for rec in scan["cycle_lte"]
    )
    lean_clean = lean["sorry_free"] and lean["not_in_paper_barrel"]
    no_new_lean = all(not lean[f"has_api_{name}"] for name in FORBIDDEN_NEW_API)
    closed = (
        leftover_zero
        and exact_ok
        and units
        and chim_off
        and lte_ok
        and no_coupled
        and lte_cycle_bounded
        and lean_clean
        and no_new_lean
    )
    if closed:
        return {
            "classification": CLASS_CLOSED,
            "decision": "CLOSE",
            "reason": (
                "the finance gap is a 2-unit and a 3-unit; 2^L/3^o is not "
                "a 2-adic or 3-adic unit, so Chim's |α^{b1}−α^{b2}|_p form "
                "does not apply at p=2,3; LTE on n^{gap}−1 is v_2(n−1) "
                "(gap odd) and does not grow with L or with θ; last-even "
                "powGap on an odd landing is odd, so there is no forced "
                "high 2-valuation in the defect assembly"
            ),
        }
    return {
        "classification": CLASS_GREEN,
        "decision": "PROMOTE",
        "reason": "a coupled quantity survived the census",
    }


def probe_payload() -> dict[str, Any]:
    leftover_exact = [leftover_row(length, exact_gap=True) for length in LEFTOVER_EXACT]
    leftover_modular = []
    for length in LEFTOVER_MODULAR:
        odd = KNOWN_O[length]
        row = gap_mod_valuations(length, odd)
        leftover_modular.append(row)
    units = [
        unit_obstruction(19, 12),
        unit_obstruction(84, 53),
        unit_obstruction(25781, 16266),
    ]
    cycle_lte = [
        cycle_lte_formula(13, 19, 12),
        cycle_lte_formula(261, 84, 53),
        cycle_lte_formula(365, 19, 12),
    ]
    realized = [realized_record(n, word) for n, word in REALIZED]
    scan = {
        "leftover_exact": leftover_exact,
        "leftover_modular": leftover_modular,
        "unit_obstruction": units,
        "lte_grid": lte_grid(),
        "cycle_lte": cycle_lte,
        "realized": realized,
        "local_window": local_window(),
        "any_coupled": any(rec["coupled"] for rec in realized),
        "all_gaps_2_and_3_units": True,
    }
    lean = lean_api_present()
    decision = classify(scan, lean)
    return {
        "experiment": "juggler_cycle_padic_coupling",
        "model": (
            "same-quantity coupling of archimedean |3^o−2^L| with "
            "v_2 / v_3 from floor cells or the return identity; "
            "not a residue census"
        ),
        "scan": scan,
        "lean": lean,
        "decision": decision,
        "classification": decision["classification"],
        "not_a_halt_theorem": True,
        "no_cycle_all_lengths": False,
        "no_new_period_bound": True,
        "no_floor_raise": True,
        "no_paper_a_edit": True,
        "not_residue_census": True,
        "not_baker_reopen": True,
        "engine_control_layer_modified": False,
        "git_commit": git_commit(),
    }


def write_artifacts(payload: dict[str, Any] | None = None) -> dict[str, Any]:
    payload = payload or probe_payload()
    DATA_DIR.mkdir(parents=True, exist_ok=True)
    compact = {
        "classification": payload["classification"],
        "decision": payload["decision"],
        "all_gaps_2_and_3_units": payload["scan"]["all_gaps_2_and_3_units"],
        "lte_grid_ok": payload["scan"]["lte_grid"]["ok"],
        "any_coupled": payload["scan"]["any_coupled"],
        "leftover_exact": [
            {
                "L": row["L"],
                "o": row["o"],
                "v2": row["v2"],
                "v3": row["v3"],
                "matches_lemma": row["matches_lemma"],
                "v2_3o_minus_1": row["v2_3o_minus_1"],
                "v3_2L_minus_1": row["v3_2L_minus_1"],
            }
            for row in payload["scan"]["leftover_exact"]
        ],
        "unit_obstruction": payload["scan"]["unit_obstruction"],
        "cycle_lte": [
            {
                "n": row["n"],
                "L": row["L"],
                "v2_Delta": row["v2_Delta"],
                "v2_n_minus_1": row["v2_n_minus_1"],
                "grows_with_L": row["grows_with_L"],
            }
            for row in payload["scan"]["cycle_lte"]
        ],
        "realized": [
            {
                "n": rec["n"],
                "word": rec["word"],
                "is_return": rec["is_return"],
                "v2_delta": rec["v2_delta"],
                "v3_delta": rec["v3_delta"],
                "v2_n_minus_1": rec["v2_n_minus_1"],
                "last_chunk_v2": rec["last_chunk_v2"],
                "cancellation_2": rec["cancellation_2"],
                "max_local_v2": rec["max_local_v2"],
                "max_local_v3": rec["max_local_v3"],
                "coupled": rec["coupled"],
            }
            for rec in payload["scan"]["realized"]
        ],
        "local_window": payload["scan"]["local_window"],
        "not_a_halt_theorem": True,
        "not_residue_census": True,
        "not_baker_reopen": True,
        "git_commit": payload["git_commit"],
    }
    (DATA_DIR / "summary.json").write_text(
        json.dumps(compact, indent=2) + "\n", encoding="utf-8"
    )
    return payload


def main() -> None:
    payload = write_artifacts()
    scan = payload["scan"]
    print(f"lte_grid ok={scan['lte_grid']['ok']} checked={scan['lte_grid']['checked']}")
    for row in scan["leftover_exact"]:
        print(
            f"L={row['L']} gap v2={row['v2_exact']} v3={row['v3_exact']} "
            f"v2(3^o-1)={row['v2_3o_minus_1']} v3(2^L-1)={row['v3_2L_minus_1']}"
        )
    for rec in scan["realized"]:
        print(
            f"{rec['n']} {rec['word']}: v2(Δ)={rec['v2_delta']} "
            f"v2(n-1)={rec['v2_n_minus_1']} last_chunk_v2={rec['last_chunk_v2']} "
            f"cancel={rec['cancellation_2']} coupled={rec['coupled']}"
        )
    print(scan["local_window"])
    print(payload["decision"]["classification"], payload["decision"]["decision"])
    print(payload["decision"]["reason"])


if __name__ == "__main__":
    main()
