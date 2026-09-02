"""Strong-induction coverage gap for Juggler finite progress.

Not a Research Engine control-layer experiment. Not a halt theorem.
Records that even states and odd-to-even states have FiniteProgress,
and that the leftover automatic class is odd-to-odd. Does not prove
FiniteProgress on that class.
"""

from __future__ import annotations

import json
from pathlib import Path
from typing import Any

from research.juggler_sequence.compensated_contraction import follows_itinerary, image_after
from research.juggler_sequence.power_itineraries import ANTI_OVERCLAIM, floor_power
from research.juggler_sequence.lean_paths import (
    ENVELOPE,
    PROGRESS,
    juggler_text,
    engine_floor_text,
    has_named,
)

REPO_ROOT = Path(__file__).resolve().parents[3]
JSON_PATH = REPO_ROOT / "docs" / "research" / "juggler_progress_coverage.json"
DOC_PATH = REPO_ROOT / "docs" / "research" / "juggler_progress_coverage.md"
LEAN_PATH = PROGRESS
FLOOR_PATH = ENVELOPE

CLASS_SPINE = "INDUCTION_SPINE_GREEN"
CLASS_FRONTIER = "ODD_ODD_FRONTIER_GREEN"
CLASS_RESIDUAL = "RESIDUAL_CLASS_IDENTIFIED"
CLASS_HALT = "FINITE_PROGRESS_GREEN"
CLASS_INCOMPLETE = "PROGRESS_COVERAGE_INCOMPLETE"

N_MAX = 80
FIRST_EVEN_CAP = 16
CALIBRATION = (2, 3, 5, 7, 13, 25, 69, 77)

LEAN_THEOREMS = (
    "FiniteProgress",
    "finiteProgress_of_descent",
    "finiteProgress_of_capture",
    "reachesOne_of_finiteProgress",
    "reachesOne_of_all_finiteProgress",
    "even_finiteProgress",
    "odd_even_finiteProgress",
    "finiteProgress_of_not_odd_odd",
    "unresolved_is_odd_odd",
    "odd_odd_image_gt",
)

CERTIFICATE_UNCHANGED = (
    "power_bound_word",
    "power_bound_contracts",
    "floorPower_odd_even_two_step_lt",
    "floorPower_odd_odd_two_step_gt",
    "even_itinerary_contracts",
    "descent_of_below",
    "ReachesOne",
    "DescentCertificate",
    "descent_of_below",
)


def is_odd_odd(n: int) -> bool:
    return n % 2 == 1 and floor_power(n) % 2 == 1


def coverage_bucket(n: int) -> str:
    if n < 2:
        return "EXCLUDED"
    if n % 2 == 0:
        return "EVEN_PROGRESS"
    if floor_power(n) % 2 == 0:
        return "OE_PROGRESS"
    return "ODD_ODD"


def first_even_residual(n: int, cap: int = FIRST_EVEN_CAP) -> dict[str, Any] | None:
    if n % 2 == 0:
        return {
            "n": n,
            "a": 0,
            "xa": n,
            "y": floor_power(n),
            "kind": "EVEN_START",
        }
    current = n
    for a in range(1, cap + 1):
        current = floor_power(current)
        if current % 2 == 0:
            y = floor_power(current)
            if y == 1:
                kind = "FIRST_EVEN_REACHES_ONE"
            elif y < n:
                kind = "FIRST_EVEN_WITH_DESCENT"
            else:
                kind = "FIRST_EVEN_STAYS_ABOVE_START"
            return {"n": n, "a": a, "xa": current, "y": y, "kind": kind}
    return {"n": n, "a": None, "kind": "NO_EVEN_WITHIN_HORIZON"}


def coverage_census(*, n_max: int = N_MAX, cap: int = FIRST_EVEN_CAP) -> dict[str, Any]:
    buckets = {"EVEN_PROGRESS": 0, "OE_PROGRESS": 0, "ODD_ODD": 0}
    odd_odd_rows: list[dict[str, Any]] = []
    kinds: dict[str, int] = {}
    for n in range(2, n_max + 1):
        bucket = coverage_bucket(n)
        buckets[bucket] += 1
        if bucket != "ODD_ODD":
            continue
        row = first_even_residual(n, cap)
        assert row is not None
        kinds[row["kind"]] = kinds.get(row["kind"], 0) + 1
        odd_odd_rows.append(row)
    stay = [row for row in odd_odd_rows if row["kind"] == "FIRST_EVEN_STAYS_ABOVE_START"]
    return {
        "n_max": n_max,
        "even_progress": buckets["EVEN_PROGRESS"],
        "oe_progress": buckets["OE_PROGRESS"],
        "odd_odd": buckets["ODD_ODD"],
        "first_even_kinds": kinds,
        "stay_above_start": len(stay),
        "first_even_descent": kinds.get("FIRST_EVEN_WITH_DESCENT", 0),
        "no_even_horizon": kinds.get("NO_EVEN_WITHIN_HORIZON", 0),
        "a_values": sorted({row["a"] for row in odd_odd_rows if row.get("a") is not None}),
        "stay_samples": stay[:8],
    }


def calibration_rows() -> list[dict[str, Any]]:
    rows = []
    for n in CALIBRATION:
        t = floor_power(n)
        row: dict[str, Any] = {
            "n": n,
            "T": t,
            "bucket": coverage_bucket(n),
            "odd_odd": is_odd_odd(n),
        }
        if n % 2 == 0:
            row["E_image"] = t
            row["E_lt"] = t < n
        elif t % 2 == 0:
            row["OE_follows"] = follows_itinerary(n, "OE")
            row["OE_image"] = image_after(n, "OE")
            row["OE_lt"] = image_after(n, "OE") < n
        else:
            row["first_even"] = first_even_residual(n)
            row["T_gt"] = t > n
        rows.append(row)
    return rows


def lean_api_present() -> dict[str, bool]:
    text = LEAN_PATH.read_text(encoding="utf-8")
    corpus = juggler_text()
    floor = engine_floor_text()
    combined = text + corpus
    return {
        "sorry_free": "sorry" not in combined and "admit" not in combined,
        **{
            name: (f"theorem {name}" in text or f"def {name}" in text)
            for name in LEAN_THEOREMS
        },
        "certificate_present": all(
            (has_named(combined, name))
            for name in CERTIFICATE_UNCHANGED
        ),
        "PowerHeight_absent": "PowerHeight" not in combined,
        "no_lower_envelope_structure": "structure LowerEnvelope" not in combined,
        "no_global_termination_theorem": "theorem juggler_reaches_one" not in combined,
        "no_all_finiteProgress_proved": "theorem all_finiteProgress" not in text,
        "no_infinite_path_type": "coinductive" not in text.lower()
        and "def InfinitePath" not in text,
        "no_frequency_theorem": "theorem odd_run_frequency" not in text,
        "no_progress_tactic": "findProgress" not in text,
        "FloorPower_not_rewritten": "FiniteProgress" not in floor,
    }


def classify(census: dict[str, Any], lean: dict[str, bool]) -> dict[str, Any]:
    lean_ok = (
        lean["sorry_free"]
        and lean["FiniteProgress"]
        and lean["reachesOne_of_all_finiteProgress"]
        and lean["finiteProgress_of_not_odd_odd"]
        and lean["unresolved_is_odd_odd"]
        and lean["even_finiteProgress"]
        and lean["odd_even_finiteProgress"]
        and lean["no_global_termination_theorem"]
        and lean["no_all_finiteProgress_proved"]
        and lean["FloorPower_not_rewritten"]
    )
    if not lean_ok:
        return {
            "classification": CLASS_INCOMPLETE,
            "reason": f"lean_ok={lean_ok}",
        }
    residual = (
        census["odd_odd"] > 0
        and census["stay_above_start"] == census["odd_odd"]
        and census["first_even_descent"] == 0
    )
    if residual:
        return {
            "classification": CLASS_FRONTIER,
            "secondary": [CLASS_SPINE, CLASS_RESIDUAL],
            "reason": (
                "even and OE states have FiniteProgress; the leftover class "
                "is odd-to-odd, and in the window the first even residual "
                "stays at or above the start"
            ),
        }
    return {
        "classification": CLASS_FRONTIER,
        "secondary": [CLASS_SPINE],
        "reason": (
            "even and OE states have FiniteProgress; the leftover class "
            "is odd-to-odd"
        ),
    }


def run_probe() -> dict[str, Any]:
    return {
        "census": coverage_census(),
        "calibration": calibration_rows(),
        "basin": [1],
    }


def probe_payload() -> dict[str, Any]:
    scan = run_probe()
    lean = lean_api_present()
    decision = classify(scan["census"], lean)
    anti = dict(ANTI_OVERCLAIM)
    anti["all_odd_orbit"] = False
    anti["finite_progress_for_all"] = False
    anti["odd_odd_is_nonterminating"] = False
    anti["cycle_obstruction"] = False
    return {
        "experiment": "juggler_progress_coverage",
        "engine_control_layer_modified": False,
        "anti_overclaim": anti,
        "scan": scan,
        "lean": lean,
        "decision": decision,
        "search_method": (
            "classify n>=2 as even / OE / odd-odd; first even residual on "
            "odd-odd starts only; no FiniteProgress search used as a proof"
        ),
    }


def render_markdown(payload: dict[str, Any]) -> str:
    decision = payload["decision"]
    scan = payload["scan"]
    lean = payload["lean"]
    census = scan["census"]
    lines = [
        "# Juggler finite-progress coverage",
        "",
        f"Status: **{decision['classification']}**",
        "",
        "Standalone application phase. Not a Research Engine experiment",
        "and not a termination theorem. Strong induction reduces",
        "`ReachesOne` to `FiniteProgress`. Even states and odd-to-even",
        "states are covered. The leftover automatic class is odd-to-odd.",
        "",
        "## Branch budget",
        "",
        "```text",
        "Mathematical target     isolate the FiniteProgress coverage gap after even and OE",
        "Novelty hypothesis      leftover class is odd-to-odd; first even residual stays >= n",
        "Falsifier               even or OE without FiniteProgress, or a halt theorem",
        "Existing machinery      even_itinerary_contracts, floorPower_odd_even_two_step_lt, ReachesOne",
        "Maximum Phase-0 scope   induction spine; even/OE coverage; odd-odd leftover census",
        "```",
        "",
        "## Metadata",
        "",
        f"- basin: `{scan['basin']}`",
        f"- engine control layer modified: `{payload['engine_control_layer_modified']}`",
        f"- classification: **{decision['classification']}**",
        f"- secondary: `{decision.get('secondary')}`",
        f"- sorry-free: `{lean['sorry_free']}`",
        "",
        decision["reason"] + ".",
        "",
        "## Coverage census",
        "",
        f"- even FiniteProgress: `{census['even_progress']}`",
        f"- OE FiniteProgress: `{census['oe_progress']}`",
        f"- odd-odd leftover: `{census['odd_odd']}`",
        f"- first-even stays above start: `{census['stay_above_start']}`",
        f"- first-even descent: `{census['first_even_descent']}`",
        f"- no even within horizon: `{census['no_even_horizon']}`",
        f"- odd-run lengths a: `{census['a_values']}`",
        "",
        "## Stay-above samples",
        "",
    ]
    for row in census["stay_samples"]:
        lines.append(
            f"- n=`{row['n']}` a=`{row['a']}` xa=`{row['xa']}` y=`{row['y']}`"
        )
    lines.extend(["", "## Calibration", ""])
    for row in scan["calibration"]:
        extra = ""
        if "OE_image" in row:
            extra = f" OE=`{row['OE_image']}` lt=`{row['OE_lt']}`"
        elif "first_even" in row and row["first_even"] is not None:
            fe = row["first_even"]
            extra = f" a=`{fe.get('a')}` y=`{fe.get('y')}` kind=`{fe.get('kind')}`"
        lines.append(
            f"- n=`{row['n']}` T=`{row['T']}` bucket=`{row['bucket']}`{extra}"
        )
    lines.extend(["", "## Lean", ""])
    for name in LEAN_THEOREMS:
        lines.append(f"- `{name}`: `{lean.get(name)}`")
    lines.extend(
        [
            f"- certificate unchanged: `{lean.get('certificate_present')}`",
            f"- `PowerHeight` absent: `{lean.get('PowerHeight_absent')}`",
            f"- FloorPower not rewritten: `{lean.get('FloorPower_not_rewritten')}`",
            f"- no all-FiniteProgress theorem: `{lean.get('no_all_finiteProgress_proved')}`",
            f"- no progress tactic: `{lean.get('no_progress_tactic')}`",
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
            "This is not a halt result. FiniteProgress is not proved for",
            "odd-to-odd states.",
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
