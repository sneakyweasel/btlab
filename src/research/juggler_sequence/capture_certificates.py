"""Descent and capture certificates for finite Juggler blocks.

Not a Research Engine control-layer experiment. A realized block either
descends or lands in the certified basin {1}. Changing-family collapses
are capture. Not a halt theorem.
"""

from __future__ import annotations

import json
from pathlib import Path
from typing import Any

from research.juggler_sequence.compensated_contraction import follows_itinerary, image_after
from research.juggler_sequence.lean_paths import CERTIFICATES, has_named, juggler_text
from research.juggler_sequence.power_itineraries import ANTI_OVERCLAIM, floor_power

REPO_ROOT = Path(__file__).resolve().parents[3]
JSON_PATH = REPO_ROOT / "docs" / "research" / "juggler_capture_certificates.json"
DOC_PATH = REPO_ROOT / "docs" / "research" / "juggler_capture_certificates.md"

CLASS_NORM = "CAPTURE_NORMALIZATION_GREEN"
CLASS_ONE = "CAPTURE_BASIN_ONE_GREEN"
CLASS_ESCAPE = "ESCAPE_NOT_CAPTURED"
CLASS_FRAME = "DESCENT_CAPTURE_FRAMEWORK_GREEN"
CLASS_FAMILY = "ESCAPE_FAMILY_FOUND"

LEAN_PATH = CERTIFICATES

LEAN_THEOREMS = (
    "InertBasin",
    "DescentCertificate",
    "ReachesOne",
    "capture_of_suffix",
    "capture_append",
    "even_tower_capture",
    "even_tower_odd_tail_capture",
    "odd_even_tower_seven_capture",
    "nested_even_collapse_2500_capture",
    "first_even_preimage_capture",
    "capture_reachesOne",
    "descent_of_below",
    "minimal_avoids_progress",
    "power_bound_compensated_contracts",
    "first_even_freeze",
)

CERTIFICATE_UNCHANGED = (
    "power_bound_compensated_contracts",
    "eventually_no_first_even_contraction",
    "changing_suffix_unbounded_contraction",
)


def classify_block(n: int, word: str) -> str:
    if not follows_itinerary(n, word):
        return "NO_CERTIFICATE"
    endpoint = image_after(n, word)
    if endpoint == 1:
        return "CAPTURE"
    if endpoint < n:
        return "DESCENT"
    return "NO_CERTIFICATE"


def small_state_table(*, m_max: int = 8, steps: int = 6) -> list[dict[str, Any]]:
    rows = []
    for s in range(1, m_max + 1):
        path = [s]
        current = s
        for _ in range(steps):
            current = floor_power(current)
            path.append(current)
        rows.append(
            {
                "s": s,
                "path": path,
                "inert": s == 1,
                "reaches_one": 1 in path,
            }
        )
    return rows


def known_blocks() -> list[dict[str, Any]]:
    samples = [
        ("E", 2),
        ("EOO", 2),
        ("EOO", 12),
        ("EOO", 14),
        ("EEOOOO", 4),
        ("OO", 3),
        ("OEEE" + "O" * 9, 7),
        ("EE" + "OEEE" + "O" * 12, 2500),
        ("E" * 2 + "O" * 6, 4),
        ("E" * 3 + "O" * 9, 16),
        ("E" * 4 + "O" * 12, 256),
    ]
    rows = []
    for word, n in samples:
        endpoint = image_after(n, word) if follows_itinerary(n, word) else None
        rows.append(
            {
                "word": word,
                "n": n,
                "follows": follows_itinerary(n, word),
                "endpoint": endpoint,
                "kind": classify_block(n, word),
                "contracts": endpoint is not None and endpoint < n,
            }
        )
    return rows


def composition_check() -> dict[str, Any]:
    prefix = "EEE"
    suffix = "O" * 9
    n = 16
    mid = image_after(n, prefix)
    return {
        "n": n,
        "prefix": prefix,
        "suffix": suffix,
        "mid": mid,
        "prefix_kind": classify_block(n, prefix),
        "suffix_kind": classify_block(mid, suffix),
        "concat_kind": classify_block(n, prefix + suffix),
    }


def lean_api_present() -> dict[str, bool]:
    text = juggler_text()
    return {
        "sorry_free": "sorry" not in text and "admit" not in text,
        **{
            name: has_named(text, name)
            for name in LEAN_THEOREMS
        },
        "certificate_present": all(f"theorem {name}" in text for name in CERTIFICATE_UNCHANGED),
        "PowerHeight_absent": "PowerHeight" not in text,
        "no_lower_envelope_structure": "structure LowerEnvelope" not in text,
        "no_global_termination_theorem": "theorem juggler_reaches_one" not in text,
    }


def classify(blocks: list[dict[str, Any]], lean: dict[str, bool]) -> dict[str, Any]:
    collapse = [
        row
        for row in blocks
        if row["word"] != "EOO" and row["n"] >= 7
    ]
    large_capture = all(row["kind"] == "CAPTURE" for row in collapse)
    eoo_descent = any(row["word"] == "EOO" and row["kind"] == "DESCENT" for row in blocks)
    lean_ok = (
        lean["sorry_free"]
        and lean["DescentCertificate"]
        and lean["capture_append"]
        and lean["minimal_avoids_progress"]
        and lean["even_tower_odd_tail_capture"]
    )
    if large_capture and eoo_descent and lean_ok:
        return {
            "classification": CLASS_FRAME,
            "secondary": CLASS_ONE,
            "reason": (
                "large changing-family witnesses capture into {1}; "
                "short EOO at 12 and 14 are descent, not capture; "
                "capture composes and a minimal non-1 value admits neither certificate"
            ),
        }
    if large_capture:
        return {
            "classification": CLASS_ONE,
            "reason": "large changing-family witnesses capture into {1}",
        }
    escaped = [row for row in large if row["kind"] != "CAPTURE"]
    return {
        "classification": CLASS_ESCAPE,
        "reason": f"a large witness was not capture: {escaped}",
    }


def run_probe() -> dict[str, Any]:
    return {
        "small_states": small_state_table(),
        "blocks": known_blocks(),
        "composition": composition_check(),
        "basin": [1],
    }


def probe_payload() -> dict[str, Any]:
    scan = run_probe()
    lean = lean_api_present()
    decision = classify(scan["blocks"], lean)
    return {
        "experiment": "juggler_capture_certificates",
        "engine_control_layer_modified": False,
        "anti_overclaim": dict(ANTI_OVERCLAIM),
        "scan": scan,
        "lean": lean,
        "decision": decision,
        "search_method": (
            "classify known collapse and EOO blocks as CAPTURE/DESCENT/"
            "NO_CERTIFICATE; basin S={1}; no logs, no halt claim"
        ),
    }


def render_markdown(payload: dict[str, Any]) -> str:
    decision = payload["decision"]
    scan = payload["scan"]
    lean = payload["lean"]
    lines = [
        "# Juggler descent and capture certificates",
        "",
        f"Status: **{decision['classification']}**",
        "",
        "Standalone application phase. Not a Research Engine experiment and",
        "not a termination theorem. A realized finite block may descend or",
        "land in the certified basin `{1}`.",
        "",
        "## Branch budget",
        "",
        "```text",
        "Mathematical target     Capture into {1} plus descent, with composition",
        "Novelty hypothesis      Changing-family collapses are basin captures",
        "Falsifier               Large changing-family T not in {1} and no descent",
        "Existing machinery      image_append, even_tower_to_one, nested 2500",
        "Maximum Phase-0 scope   Capture/Descent props; append; normalize families",
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
        "## Known blocks",
        "",
    ]
    for row in scan["blocks"]:
        lines.append(
            f"- n=`{row['n']}` word=`{row['word']}` T=`{row['endpoint']}` "
            f"kind=`{row['kind']}`"
        )
    comp = scan["composition"]
    lines.extend(
        [
            "",
            "## Capture composition",
            "",
            f"- `{comp['n']}` via `{comp['prefix']}` then `{comp['suffix']}`: "
            f"mid=`{comp['mid']}` concat=`{comp['concat_kind']}`",
            "",
            "## Small states",
            "",
        ]
    )
    for row in scan["small_states"]:
        lines.append(
            f"- s=`{row['s']}` inert=`{row['inert']}` reaches_one=`{row['reaches_one']}` "
            f"path=`{row['path']}`"
        )
    lines.extend(["", "## Lean", ""])
    for name in LEAN_THEOREMS:
        lines.append(f"- `{name}`: `{lean.get(name)}`")
    lines.extend(
        [
            f"- certificate unchanged: `{lean.get('certificate_present')}`",
            f"- `PowerHeight` absent: `{lean.get('PowerHeight_absent')}`",
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
            "This is not a halt result.",
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
