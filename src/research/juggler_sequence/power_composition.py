"""Near-equality stress-test and realized-word composition helpers.

Reuses `power_itineraries`. Not a Research Engine control-layer experiment.
The one-sided law T_w(n)^{2^k} <= n^{3^o} is the object under attack.
"""

from __future__ import annotations

import json
from pathlib import Path
from typing import Any

from research.juggler_sequence.lean_paths import juggler_text
from research.juggler_sequence.power_itineraries import (
    ANTI_OVERCLAIM,
    LEAN_PATH,
    WORD_OOOEE,
    cmp_pow,
    floor_power,
    itinerary,
    maybe_delta,
    odd_count,
    word_of,
)

REPO_ROOT = Path(__file__).resolve().parents[3]
JSON_PATH = REPO_ROOT / "docs" / "research" / "juggler_power_composition.json"
DOC_PATH = REPO_ROOT / "docs" / "research" / "juggler_power_composition.md"
PRIOR_JSON = REPO_ROOT / "docs" / "research" / "juggler_power_itineraries.json"

LEAN_EMPTY = "power_bound_empty"
LEAN_EVEN = "power_bound_append_even"
LEAN_ODD = "power_bound_append_odd"
LEAN_FOLLOWS = "power_bound_follows"
LEAN_CONTRACTS = "power_bound_contracts"

CLASS_GREEN = "POWER_COMPOSITION_GREEN"
CLASS_COUNTER = "POWER_COMPOSITION_COUNTEREXAMPLE"
CLASS_REPR = "POWER_COMPOSITION_REPRESENTATION_FAILURE"
CLASS_LOCAL = "POWER_COMPOSITION_LOCAL_ONLY"

K_MAX = 8
NEAR_EQ_N_MAX = 50_000


def square_towers(limit: int) -> list[int]:
    """Even perfect-power towers 2^(2^j) while they stay in range, plus even squares."""

    towers = []
    n = 2
    while n <= limit:
        towers.append(n)
        if n > limit // n:
            break
        n = n * n
    squares = [k * k for k in range(2, int(limit**0.5) + 1) if (k * k) % 2 == 0]
    return sorted(set(towers + squares))


def gap_record(n: int, word: str, m: int) -> dict[str, Any]:
    k = len(word)
    o = odd_count(word)
    a = 1 << k
    b = 3**o
    cmp = cmp_pow(m, a, n, b)
    return {
        "word": word,
        "n": n,
        "k": k,
        "odd_count": o,
        "m": m,
        "cmp": cmp,
        "onesided_holds": cmp <= 0,
        "equality": cmp == 0,
        "delta": maybe_delta(n, b, m, a),
        "mixed": "O" in word and "E" in word,
    }


def scan_path(n: int, k_max: int = K_MAX) -> list[dict[str, Any]]:
    path = itinerary(n, k_max)
    rows = []
    for k in range(1, k_max + 1):
        word = word_of(path[: k + 1])
        rows.append(gap_record(n, word, path[k]))
    return rows


def power_bound_holds(n: int, word: str) -> bool:
    path = itinerary(n, len(word))
    if word_of(path) != word:
        return False
    rec = gap_record(n, word, path[-1])
    return rec["onesided_holds"]


def append_even_algebra(m: int, n: int, k: int, o: int) -> bool:
    """Numerical check of P_k(m,n,o) and even m => P_{k+1}(T(m),n,o)."""

    if m % 2 != 0 or m < 1 or n < 1:
        return True
    if cmp_pow(m, 1 << k, n, 3**o) > 0:
        return True
    image = floor_power(m)
    return cmp_pow(image, 1 << (k + 1), n, 3**o) <= 0


def append_odd_algebra(m: int, n: int, k: int, o: int) -> bool:
    if m % 2 != 1 or m < 1 or n < 1:
        return True
    if cmp_pow(m, 1 << k, n, 3**o) > 0:
        return True
    image = floor_power(m)
    return cmp_pow(image, 1 << (k + 1), n, 3 ** (o + 1)) <= 0


def run_near_equality(
    n_max: int = NEAR_EQ_N_MAX, k_max: int = K_MAX
) -> dict[str, Any]:
    onesided_failures: list[dict[str, Any]] = []
    equalities: list[dict[str, Any]] = []
    mixed_equalities: list[dict[str, Any]] = []
    smallest_positive: list[dict[str, Any]] = []
    focus_n = set(square_towers(n_max))
    focus_n.update({1, 2, 3, 4, 5, 9, 11, 13, 15, 16, 17, 25, 36, 39, 255, 256, 257})
    focus_n.update(range(1, min(n_max, 400) + 1))
    for extra in (65535, 65536, 65537):
        if extra <= n_max:
            focus_n.add(extra)

    for n in sorted(x for x in focus_n if 1 <= x <= n_max):
        for rec in scan_path(n, k_max):
            if not rec["onesided_holds"]:
                onesided_failures.append(rec)
            if rec["equality"]:
                equalities.append(rec)
                if rec["mixed"]:
                    mixed_equalities.append(rec)
            delta = rec["delta"]
            if delta is not None and delta > 0 and rec["mixed"]:
                smallest_positive.append(rec)

    smallest_positive.sort(key=lambda rec: (rec["delta"], rec["n"], rec["word"]))
    # Dedup by word, keep smallest gap
    by_word: dict[str, dict[str, Any]] = {}
    for rec in smallest_positive:
        prev = by_word.get(rec["word"])
        if prev is None or rec["delta"] < prev["delta"]:
            by_word[rec["word"]] = rec

    above_towers = []
    for tower in square_towers(n_max):
        if tower + 2 <= n_max:
            above_towers.extend(scan_path(tower + 2, min(4, k_max)))

    prior_onesided = None
    if PRIOR_JSON.is_file():
        prior = json.loads(PRIOR_JSON.read_text(encoding="utf-8"))
        prior_onesided = {
            "n_max": prior.get("n_max"),
            "onesided_holds": prior.get("decision", {}).get("onesided_holds"),
            "onesided_failures": prior.get("onesided_failures"),
        }

    return {
        "n_max": n_max,
        "k_max": k_max,
        "onesided_failures": onesided_failures[:20],
        "onesided_failure_count": len(onesided_failures),
        "equalities_sample": equalities[:24],
        "mixed_equalities": mixed_equalities,
        "pure_even_or_n1_equalities": [
            rec for rec in equalities if rec["odd_count"] == 0 or rec["n"] == 1
        ][:16],
        "smallest_mixed_positive_gaps": sorted(
            by_word.values(), key=lambda rec: (rec["delta"], rec["word"])
        )[:12],
        "above_tower_onesided": all(rec["onesided_holds"] for rec in above_towers),
        "prior_sweep": prior_onesided,
        "append_even_check": all(
            append_even_algebra(m, n, k, o)
            for n in (4, 16, 36, 100)
            for m in (n,)
            for k, o in ((0, 0), (1, 0), (2, 1))
            if m % 2 == 0
        ),
        "append_odd_check": all(
            append_odd_algebra(m, n, k, o)
            for n, m in ((3, 3), (5, 5), (9, 9), (15, 15))
            for k, o in ((0, 0), (1, 1), (2, 1))
            if m % 2 == 1
        ),
    }


def lean_api_present() -> dict[str, bool]:
    text = juggler_text()
    names = (LEAN_EMPTY, LEAN_EVEN, LEAN_ODD, LEAN_FOLLOWS, LEAN_CONTRACTS)
    return {
        "sorry_free": "sorry" not in text and "admit" not in text,
        **{name: f"theorem {name}" in text for name in names},
        "oooee_intact": f"theorem floorPower_oooee_five_step_lt" in text,
        "oooeeeoo_intact": f"theorem floorPower_oooeeeoo_eight_step_lt" in text,
    }


def classify(near: dict[str, Any], lean: dict[str, bool]) -> dict[str, Any]:
    if near["onesided_failure_count"] or (
        near.get("prior_sweep") or {}
    ).get("onesided_holds") is False:
        return {
            "classification": CLASS_COUNTER,
            "reason": "a realized word violates T_w(n)^{2^k} <= n^{3^o}",
            "lean_gate_open": False,
        }
    api = all(lean[name] for name in (LEAN_EMPTY, LEAN_EVEN, LEAN_ODD, LEAN_FOLLOWS, LEAN_CONTRACTS))
    if api and lean["sorry_free"]:
        return {
            "classification": CLASS_GREEN,
            "reason": (
                "The weak bound is an inductive floor-power composition on "
                "realized finite itineraries; strict contraction follows from the "
                "exponent gap at n>=2"
            ),
            "lean_gate_open": True,
        }
    return {
        "classification": CLASS_REPR,
        "reason": "the inequality survived computationally but the Lean API is incomplete",
        "lean_gate_open": False,
    }


def probe_payload(
    *, n_max: int = NEAR_EQ_N_MAX, k_max: int = K_MAX
) -> dict[str, Any]:
    near = run_near_equality(n_max=n_max, k_max=k_max)
    lean = lean_api_present()
    decision = classify(near, lean)
    return {
        "experiment": "juggler_power_composition",
        "engine_control_layer_modified": False,
        "anti_overclaim": dict(ANTI_OVERCLAIM),
        "oooee_calibration": WORD_OOOEE,
        "near_equality": near,
        "lean": lean,
        "decision": decision,
        "predicate": "PowerBound m n k o := m ^ (2 ^ k) <= n ^ (3 ^ o)",
        "append_even": "(k,o) -> (k+1,o)",
        "append_odd": "(k,o) -> (k+1,o+1)",
        "strict_corollary": "3^o < 2^k and n>=2 implies T_w(n) < n",
    }


def render_markdown(payload: dict[str, Any]) -> str:
    decision = payload["decision"]
    near = payload["near_equality"]
    lean = payload["lean"]
    lines = [
        "# Juggler one-sided floor-power composition",
        "",
        f"Status: **{decision['classification']}**",
        "",
        "Standalone application phase. Not a Research Engine experiment, not a",
        "termination theorem, and not a parity-frequency theorem. The Phase-13",
        "two-sided exponent law remains `POWER_WORD_COUNTEREXAMPLE`. This page",
        "records whether the surviving one-sided envelope is a finite-word theorem.",
        "",
        "## Branch budget",
        "",
        "```text",
        "Mathematical target     Does every realized finite parity word satisfy",
        "                        T_w(n)^{2^k} <= n^{3^o} by inductive floor composition?",
        "Novelty hypothesis      OOOEE / OOOEEEOO are instances of one weak bound plus",
        "                        an exponent-gap contraction corollary.",
        "Falsifier               A realized (w,n) with T_w(n)^{2^k} > n^{3^o}.",
        "Existing machinery      power_itineraries cmp_pow; FloorPower even/odd square bounds;",
        "                        pow_sq_le / pow_sq_le_cube.",
        "Maximum Phase-0 scope   Near-equality scan reusing power_itineraries; then a tiny",
        "                        Lean API if the weak bound survives. No engine edits.",
        "```",
        "",
        "## Metadata",
        "",
        f"- n_max (near-equality focus): `{near['n_max']}`",
        f"- k_max: `{near['k_max']}`",
        f"- engine control layer modified: `{payload['engine_control_layer_modified']}`",
        f"- classification: **{decision['classification']}**",
        f"- Lean empty/even/odd/follows/contracts: "
        f"`{lean.get(LEAN_EMPTY)}`/`{lean.get(LEAN_EVEN)}`/`{lean.get(LEAN_ODD)}`/"
        f"`{lean.get(LEAN_FOLLOWS)}`/`{lean.get(LEAN_CONTRACTS)}`",
        f"- sorry-free: `{lean['sorry_free']}`",
        "",
        decision["reason"] + ".",
        "",
        "## Weak composition law",
        "",
        "`PowerBound m n k o` means `m^{2^k} <= n^{3^o}`.",
        "",
        "- empty: `PowerBound n n 0 0`",
        "- append even: `(k,o) -> (k+1,o)` via `T(m)^2 <= m`",
        "- append odd: `(k,o) -> (k+1,o+1)` via `T(m)^2 <= m^3`",
        "",
        f"Numerical append-even check: `{near['append_even_check']}`.",
        f"Numerical append-odd check: `{near['append_odd_check']}`.",
        "",
        "## Near-equality",
        "",
        f"- onesided failures in the focus scan: `{near['onesided_failure_count']}`",
        f"- mixed-word equalities: `{near['mixed_equalities']}`",
        f"- states immediately above square towers still one-sided: `{near['above_tower_onesided']}`",
        "",
        "Smallest positive mixed gaps (raw `G_w` when it fits in 4096 bits):",
        "",
        "| word | n | G_w | m |",
        "| --- | --- | --- | --- |",
    ]
    for rec in near["smallest_mixed_positive_gaps"]:
        lines.append(
            f"| `{rec['word']}` | {rec['n']} | {rec['delta']} | {rec['m']} |"
        )
    lines.extend(
        [
            "",
            "Equality observed in the focus scan is the square-tower / `n=1` family,",
            "not mixed itineraries. The weak theorem is therefore non-strict by design.",
            "",
            "## Strict corollary",
            "",
            "If `3^o < 2^k` and `n>=2`, then `n^{3^o} < n^{2^k}`, so the weak bound",
            "implies `T_w(n) < n`. At `n=1` both powers are 1 and the gap is silent.",
            "",
            "## Anti-overclaim",
            "",
        ]
    )
    for key, value in payload["anti_overclaim"].items():
        lines.append(f"- {key}: `{value}`")
    lines.extend(
        [
            "",
            "## Decision",
            "",
            f"**{decision['classification']}**",
            "",
            decision["reason"] + ".",
            "",
        ]
    )
    return "\n".join(lines) + "\n"


def write_artifacts(
    payload: dict[str, Any] | None = None,
    *,
    n_max: int = NEAR_EQ_N_MAX,
    k_max: int = K_MAX,
) -> dict[str, Any]:
    data = payload if payload is not None else probe_payload(n_max=n_max, k_max=k_max)
    JSON_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(data, indent=2) + "\n", encoding="utf-8")
    DOC_PATH.write_text(render_markdown(data), encoding="utf-8")
    return data


def main() -> None:
    payload = write_artifacts()
    print(payload["decision"]["classification"])
    print(payload["decision"]["reason"])


if __name__ == "__main__":
    main()
