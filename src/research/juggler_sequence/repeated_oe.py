"""Repeated OE scale budget on a hypothetical minimal non-1 Juggler orbit.

Not a Research Engine control-layer experiment. Not a frequency theorem
and not a halt theorem. Quantifies what consecutive OE blocks force if
they occur.
"""

from __future__ import annotations

import json
from pathlib import Path
from typing import Any

from research.juggler_sequence.capture_certificates import classify_block
from research.juggler_sequence.compensated_contraction import follows_itinerary, image_after
from research.juggler_sequence.power_itineraries import ANTI_OVERCLAIM, floor_power, word_of
from research.juggler_sequence.lean_paths import (
    ENVELOPE,
    MINIMAL,
    SCALE,
    has_named,
    juggler_text,
)

REPO_ROOT = Path(__file__).resolve().parents[3]
JSON_PATH = REPO_ROOT / "docs" / "research" / "juggler_repeated_oe.json"
DOC_PATH = REPO_ROOT / "docs" / "research" / "juggler_repeated_oe.md"
LEAN_PATH = SCALE
MIN_PATH = MINIMAL
FLOOR_PATH = ENVELOPE

CLASS_GREEN = "REPEATED_OE_SCALE_GREEN"
CLASS_FORBIDDEN = "OE_RUN_FORBIDDEN_GREEN"
CLASS_COUNTER = "BLOCK_SCALE_COUNTEREXAMPLE"
CLASS_INCOMPLETE = "REPEATED_OE_INCOMPLETE"

N_MAX = 80
PREFIX_CAP = 40
CALIBRATION = (
    (13, "OE"),
    (27, "OE"),
    (25, "OOOE"),
)

LEAN_THEOREMS = (
    "itineraryOE",
    "repeatedOE",
    "oe_block_scale",
    "oe_block_contracts",
    "repeated_oe_scale",
    "repeated_oe_scale_barrier",
    "oe_requires_scale",
    "minimal_nonterm_not_repeated_oe",
)

CERTIFICATE_UNCHANGED = (
    "power_bound_word",
    "power_bound_compensated_contracts",
    "even_run_scale_barrier",
    "minimal_counterexample_normal_form",
    "minimal_nonterm_odd_image_odd",
)


def oe_envelope_holds(x: int) -> bool:
    if not follows_itinerary(x, "OE"):
        return True
    image = image_after(x, "OE")
    return image ** 4 <= x ** 3


def repeated_oe_envelope_holds(x: int, r: int) -> bool:
    word = "OE" * r
    if not follows_itinerary(x, word):
        return True
    image = image_after(x, word)
    return image ** (4 ** r) <= x ** (3 ** r)


def scale_barrier_holds(start: int, x: int, r: int, image: int) -> bool:
    if image < start:
        return True
    return start ** (4 ** r) <= x ** (3 ** r)


def consecutive_oe_runs(n: int, cap: int = PREFIX_CAP) -> list[dict[str, Any]]:
    path = [n]
    current = n
    for _ in range(cap):
        current = floor_power(current)
        path.append(current)
    word = word_of(tuple(path))
    rows: list[dict[str, Any]] = []
    index = 0
    while index + 1 < len(word):
        if word[index : index + 2] != "OE":
            index += 1
            continue
        end = index
        while end + 1 < len(word) and word[end : end + 2] == "OE":
            end += 2
        r = (end - index) // 2
        start_state = path[index]
        image = path[end]
        rows.append(
            {
                "n": n,
                "x": start_state,
                "r": r,
                "image": image,
                "exit_ge_n": image >= n,
                "envelope_ok": repeated_oe_envelope_holds(start_state, r),
                "scale_ok": scale_barrier_holds(n, start_state, r, image),
            }
        )
        index = end
    return rows


def oe_census(*, n_max: int = N_MAX, cap: int = PREFIX_CAP) -> dict[str, Any]:
    rows: list[dict[str, Any]] = []
    for n in range(2, n_max + 1):
        rows.extend(consecutive_oe_runs(n, cap))
    stay = [row for row in rows if row["exit_ge_n"]]
    fail_env = [row for row in rows if not row["envelope_ok"]]
    fail_scale = [row for row in stay if not row["scale_ok"]]
    max_r = max((row["r"] for row in rows), default=0)
    max_r_stay = max((row["r"] for row in stay), default=0)
    longest_stay = max(stay, key=lambda row: (row["r"], row["x"])) if stay else None
    return {
        "n_max": n_max,
        "run_count": len(rows),
        "stay_ge_n": len(stay),
        "envelope_fail": len(fail_env),
        "scale_fail": len(fail_scale),
        "max_r": max_r,
        "max_r_stay": max_r_stay,
        "longest_stay": longest_stay,
        "samples_stay": stay[:8],
    }


def calibration_rows() -> list[dict[str, Any]]:
    rows = []
    for n, word in CALIBRATION:
        if not follows_itinerary(n, word):
            rows.append({"n": n, "word": word, "follows": False})
            continue
        image = image_after(n, word)
        rows.append(
            {
                "n": n,
                "word": word,
                "follows": True,
                "image": image,
                "kind": classify_block(n, word),
                "oe_envelope": oe_envelope_holds(n) if word == "OE" else None,
            }
        )
    return rows


def lean_api_present() -> dict[str, bool]:
    text = LEAN_PATH.read_text(encoding="utf-8")
    minimum = MIN_PATH.read_text(encoding="utf-8")
    floor = juggler_text()
    combined = text + minimum + floor
    return {
        "sorry_free": "sorry" not in combined and "admit" not in combined,
        **{name: has_named(combined, name) for name in LEAN_THEOREMS},
        "certificate_present": all(
            f"theorem {name}" in combined for name in CERTIFICATE_UNCHANGED
        ),
        "PowerHeight_absent": "PowerHeight" not in combined,
        "no_lower_envelope_structure": "structure LowerEnvelope" not in combined,
        "no_global_termination_theorem": "theorem juggler_reaches_one" not in combined,
        "no_infinite_path_type": "coinductive" not in text.lower()
        and "def InfinitePath" not in text,
        "no_frequency_theorem": "theorem oe_frequency" not in text,
    }


def classify(census: dict[str, Any], lean: dict[str, bool]) -> dict[str, Any]:
    if census["envelope_fail"] > 0:
        return {
            "classification": CLASS_COUNTER,
            "reason": f"OE envelope failed: {census['envelope_fail']} runs",
        }
    if census["scale_fail"] > 0:
        return {
            "classification": CLASS_COUNTER,
            "reason": f"repeated-OE scale n^{{4^r}} <= x^{{3^r}} failed on a stay-ge-n run",
        }
    lean_ok = (
        lean["sorry_free"]
        and lean["oe_block_scale"]
        and lean["repeated_oe_scale"]
        and lean["repeated_oe_scale_barrier"]
        and lean["oe_requires_scale"]
        and lean["minimal_nonterm_not_repeated_oe"]
        and lean["no_global_termination_theorem"]
        and lean["no_frequency_theorem"]
    )
    if lean_ok:
        return {
            "classification": CLASS_GREEN,
            "secondary": CLASS_FORBIDDEN,
            "reason": (
                "r consecutive OE blocks on a minimal non-1 orbit require "
                "n^{4^r} <= x^{3^r}; (OE)^r cannot start at n_* itself"
            ),
        }
    return {
        "classification": CLASS_INCOMPLETE,
        "reason": f"lean_ok={lean_ok}",
    }


def run_probe() -> dict[str, Any]:
    return {
        "census": oe_census(),
        "calibration": calibration_rows(),
        "basin": [1],
    }


def probe_payload() -> dict[str, Any]:
    scan = run_probe()
    lean = lean_api_present()
    decision = classify(scan["census"], lean)
    anti = dict(ANTI_OVERCLAIM)
    anti["all_odd_orbit"] = False
    anti["oe_frequency_theorem"] = False
    return {
        "experiment": "juggler_repeated_oe",
        "engine_control_layer_modified": False,
        "anti_overclaim": anti,
        "scan": scan,
        "lean": lean,
        "decision": decision,
        "search_method": (
            "consecutive OE runs on realized prefixes; envelope T^{2r}(x)^{4^r}"
            "<=x^{3^r}; scale n^{4^r}<=x^{3^r} when exit>=n; no frequency claim"
        ),
    }


def render_markdown(payload: dict[str, Any]) -> str:
    decision = payload["decision"]
    scan = payload["scan"]
    lean = payload["lean"]
    census = scan["census"]
    longest = census["longest_stay"]
    lines = [
        "# Juggler repeated OE scale budget",
        "",
        f"Status: **{decision['classification']}**",
        "",
        "Standalone application phase. Not a Research Engine experiment,",
        "not a frequency theorem, and not a termination theorem. If a",
        "minimal non-1 orbit contains `r` consecutive `OE` blocks from `x`,",
        "then `n^{4^r} ≤ x^{3^r}`.",
        "",
        "## Branch budget",
        "",
        "```text",
        "Mathematical target     r consecutive OE blocks require n^{4^r} <= x^{3^r}",
        "Novelty hypothesis      Repeated OE is a finite scale budget",
        "Falsifier               Envelope fail, or stay-ge-n run with x^{3^r} < n^{4^r}",
        "Existing machinery      power_bound_word, MinimalNonTerm, even_run_scale_barrier",
        "Maximum Phase-0 scope   OE/(OE)^r envelope; barrier; start-forbidden (OE)^r",
        "```",
        "",
        "## Metadata",
        "",
        f"- basin: `{scan['basin']}`",
        f"- engine control layer modified: `{payload['engine_control_layer_modified']}`",
        f"- classification: **{decision['classification']}**",
        f"- sorry-free: `{lean['sorry_free']}`",
        "",
        decision["reason"] + ".",
        "",
        "## Consecutive OE census",
        "",
        f"- realized OE runs: `{census['run_count']}`",
        f"- runs with exit >= n: `{census['stay_ge_n']}`",
        f"- envelope failures: `{census['envelope_fail']}`",
        f"- scale failures on stay-ge-n: `{census['scale_fail']}`",
        f"- max consecutive r: `{census['max_r']}`",
        f"- max r with exit >= n: `{census['max_r_stay']}`",
        "",
    ]
    if longest is not None:
        lines.append(
            f"- longest stay-ge-n: n=`{longest['n']}` x=`{longest['x']}` "
            f"r=`{longest['r']}` image=`{longest['image']}`"
        )
    lines.extend(["", "## Calibration", ""])
    for row in scan["calibration"]:
        if not row.get("follows", True):
            lines.append(f"- n=`{row['n']}` word=`{row['word']}` follows=`False`")
            continue
        lines.append(
            f"- n=`{row['n']}` word=`{row['word']}` T=`{row['image']}` "
            f"kind=`{row['kind']}`"
        )
    lines.extend(["", "## Lean", ""])
    for name in LEAN_THEOREMS:
        lines.append(f"- `{name}`: `{lean.get(name)}`")
    lines.extend(
        [
            f"- certificate unchanged: `{lean.get('certificate_present')}`",
            f"- `PowerHeight` absent: `{lean.get('PowerHeight_absent')}`",
            f"- no infinite-path type: `{lean.get('no_infinite_path_type')}`",
            f"- no frequency theorem: `{lean.get('no_frequency_theorem')}`",
            f"- no global halt theorem: `{lean.get('no_global_termination_theorem')}`",
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
            "This is not a halt result and not an OE-frequency theorem.",
            "",
        ]
    )
    return "\n".join(lines) + "\n"


def write_artifacts(payload: dict[str, Any] | None = None) -> dict[str, Any]:
    data = payload if payload is not None else probe_payload()
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
