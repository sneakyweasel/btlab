"""Baker / linear forms on |3^o - 2^L| for Juggler cycle finance.

Not a halt theorem, not a no-cycle-of-any-length theorem, not the
parked Baker/Thue/Mordell campaign on x^3 - y^2, and not a Lean
import of Rhin or Laurent-Mignotte-Nesterenko.

Cycle finance already gives n ln n <= (6/5) L 3^o / (3^o - 2^L).
Simons-de Weger (2005) combine a Collatz financing upper bound on
Lambda = (K+L) ln 2 - K ln 3 with Rhin's lower bound
Lambda > exp(-13.3 (0.46057 + ln K)). The Collatz upper bound is
exponentially small in K (m-cycle geometry). Juggler finance only
gives |L ln 2 - o ln 3| <= (6/5) L / (n ln n). This module maps
the published Rhin/SdW lower bound into the Juggler inequality and
records that the squeeze never fires on leftover lengths.

Dossier: docs/problems/juggler_cycle_gap_baker.md
"""

from __future__ import annotations

import json
import math
import subprocess
from pathlib import Path
from typing import Any

from research.juggler_sequence.cycle_finance import EPS_CONST, n_max_from_bound
from research.juggler_sequence.lean_paths import (
    CYCLE_FINANCE,
    JUGGLER_DIR,
    JUGGLER_PAPER_BARREL,
    has_named,
    juggler_text,
)

REPO_ROOT = Path(__file__).resolve().parents[3]
JSON_PATH = REPO_ROOT / "docs" / "research" / "juggler_cycle_gap_baker.json"
DOC_PATH = REPO_ROOT / "docs" / "research" / "juggler_cycle_gap_baker.md"
DATA_DIR = REPO_ROOT / "data" / "research" / "juggler" / "cycle_gap_baker"

CLASS_CLOSED = "CYCLE_GAP_BAKER_CLOSED"
CLASS_GREEN = "CYCLE_GAP_BAKER_GREEN"
CLASS_INCOMPLETE = "CYCLE_GAP_BAKER_INCOMPLETE"

# Simons-de Weger Lemma 12, from Rhin 1987 Prop. p. 160.
RHIN_C = 13.3
RHIN_SHIFT = 0.46057

LEAN_FLOOR = 53
PYTHON_FLOOR = 1_000_000
HYPOTHETICAL_FLOOR = 1_000_000_000
REPORT_FLOORS = (LEAN_FLOOR, PYTHON_FLOOR, HYPOTHETICAL_FLOOR)

# Known finance record (near-convergent) lengths. Large ones are
# evaluated individually; the dense table stops earlier.
RECORD_LENGTHS = (1, 3, 11, 19, 84, 569, 1054, 25781, 50508)
LEFTOVER_RECORDS = (19, 84, 569, 1054, 25781, 50508)

SCIENCE_L_MAX = 2_000
TEST_L_MAX = 400
N_MAX_CAP = 10**18

EXISTING_LEAN = (
    "cycleMin_finance",
    "cycle_finance_min_fifty_three",
    "cycle_itinerary_length_nineteen_or_ge_thirty",
)
FORBIDDEN_THEOREMS = (
    "juggler_reaches_one",
    "no_cycle_itinerary_any_length",
    "rhin_excludes_length",
    "baker_excludes_length",
    "no_cycle_itinerary_length_nineteen",
)
FORBIDDEN_NEW_API = (
    "BakerGap",
    "RhinBound",
    "LinearFormLambda",
)
FORBIDDEN_LEAN_FILES = (
    JUGGLER_DIR / "Baker.lean",
    JUGGLER_DIR / "CycleGapBaker.lean",
    JUGGLER_DIR / "LinearForms.lean",
)
PAPER_FORBIDDEN = ("CycleGapBaker", "BakerGap", "RhinBound")


def git_commit() -> str:
    try:
        return subprocess.check_output(
            ["git", "rev-parse", "HEAD"],
            cwd=REPO_ROOT,
            text=True,
            stderr=subprocess.DEVNULL,
        ).strip()
    except (OSError, subprocess.CalledProcessError):
        return "unknown"


def o_min(length: int) -> int:
    """Minimal o with 3^o > 2^L."""

    if length < 1:
        raise ValueError("length must be positive")
    pow2 = 1 << length
    pow3 = 1
    odd = 0
    while pow3 <= pow2:
        pow3 *= 3
        odd += 1
    return odd


def exact_gap(length: int) -> dict[str, Any]:
    """Exact 3^{o_min} - 2^L and the relative gap theta."""

    odd = o_min(length)
    pow2 = 1 << length
    pow3 = 3**odd
    gap = pow3 - pow2
    theta = gap / pow3
    return {"L": length, "o": odd, "gap": gap, "theta": theta}


def lambda_abs(length: int, odd: int) -> float:
    """|L ln 2 - o ln 3|."""

    return abs(length * math.log(2) - odd * math.log(3))


def theta_from_lambda(lam: float) -> float:
    """theta = 1 - exp(-Lambda) when 2^L < 3^o."""

    if lam <= 0.0:
        return 0.0
    if lam >= 40.0:
        return 1.0
    return -math.expm1(-lam)


def rhin_lambda_lower(height: int) -> float:
    """SdW Lemma 12: Lambda > exp(-13.3 (0.46057 + ln H))."""

    if height < 1:
        raise ValueError("height must be positive")
    exponent = -RHIN_C * (RHIN_SHIFT + math.log(height))
    if exponent < -700.0:
        return 0.0
    return math.exp(exponent)


def n_max_from_theta(length: int, theta: float) -> int:
    if theta <= 0.0:
        return N_MAX_CAP
    bound = EPS_CONST * length / theta
    if bound >= 1e18:
        return N_MAX_CAP
    return min(n_max_from_bound(bound), N_MAX_CAP)


def finance_theta_cap(length: int, floor: int) -> float:
    """Any cycle with min >= floor must have theta <= this."""

    return EPS_CONST * length / (floor * math.log(floor))


def bound_row(length: int) -> dict[str, Any]:
    """Exact gap versus Rhin/SdW at one length."""

    exact = exact_gap(length)
    odd = exact["o"]
    height = max(length, odd)
    lam_exact = lambda_abs(length, odd)
    rhin_lam = rhin_lambda_lower(height)
    rhin_theta = theta_from_lambda(rhin_lam)
    exact_n_max = n_max_from_theta(length, exact["theta"])
    rhin_n_max = n_max_from_theta(length, rhin_theta)
    gap = exact["gap"]
    gap_bits = gap.bit_length()
    return {
        "L": length,
        "o": odd,
        "height": height,
        "exact_gap": gap if gap_bits <= 256 else None,
        "exact_gap_bits": gap_bits,
        "exact_theta": exact["theta"],
        "exact_lambda": lam_exact,
        "exact_n_max": exact_n_max,
        "rhin_lambda": rhin_lam,
        "rhin_theta": rhin_theta,
        "rhin_n_max": rhin_n_max,
        "rhin_weaker_than_exact": rhin_theta <= exact["theta"] + 1e-15,
        "rhin_n_max_ge_exact": rhin_n_max >= exact_n_max,
    }


def squeeze_row(length: int, floor: int) -> dict[str, Any]:
    row = bound_row(length)
    cap = finance_theta_cap(length, floor)
    rhin_theta = row["rhin_theta"]
    fires = rhin_theta > cap
    return {
        "L": length,
        "o": row["o"],
        "floor": floor,
        "finance_theta_cap": cap,
        "rhin_theta": rhin_theta,
        "exact_theta": row["exact_theta"],
        "fires": fires,
        "exact_already_excludes": row["exact_n_max"] <= floor,
    }


def leftover_exclusions(
    rows: list[dict[str, Any]],
    floor: int,
) -> dict[str, Any]:
    """Lengths exact finance keeps, but Rhin would exclude."""

    leftover = [
        row for row in rows if row["exact_n_max"] > floor
    ]
    killed = [row["L"] for row in leftover if row["rhin_n_max"] <= floor]
    return {
        "floor": floor,
        "leftover_count": len(leftover),
        "rhin_killed": killed,
        "rhin_killed_count": len(killed),
    }


def needed_floor_for_rhin(length: int) -> int:
    """Smallest n with n ln n >= (6/5) L / rhin_theta.

    This is the verified-orbit floor that would make the Rhin
    squeeze fire at this length. Not a recommended computation.
    """

    row = bound_row(length)
    theta = row["rhin_theta"]
    if theta <= 0.0:
        return N_MAX_CAP
    target = EPS_CONST * length / theta
    if target >= 1e18:
        return N_MAX_CAP
    return min(n_max_from_bound(target) + 1, N_MAX_CAP)


def dominance_holds(rows: list[dict[str, Any]]) -> bool:
    return all(row["rhin_weaker_than_exact"] and row["rhin_n_max_ge_exact"] for row in rows)


def lean_api_present() -> dict[str, bool]:
    combined = juggler_text()
    named = {name: has_named(combined, name) for name in EXISTING_LEAN}
    forbidden = {
        f"has_{name}": has_named(combined, name) for name in FORBIDDEN_THEOREMS
    }
    paper = JUGGLER_PAPER_BARREL.read_text(encoding="utf-8")
    return {
        "sorry_free": "sorry" not in combined and "admit" not in combined,
        **named,
        **forbidden,
        **{
            f"has_api_{name}": has_named(combined, name)
            for name in FORBIDDEN_NEW_API
        },
        "cycle_finance_present": CYCLE_FINANCE.is_file(),
        "no_baker_lean": not any(path.is_file() for path in FORBIDDEN_LEAN_FILES),
        "not_in_paper_barrel": all(name not in paper for name in PAPER_FORBIDDEN),
    }


def run_probe(*, l_max: int = TEST_L_MAX) -> dict[str, Any]:
    dense = [bound_row(length) for length in range(1, l_max + 1)]
    records = [bound_row(length) for length in RECORD_LENGTHS]
    exclusions = [leftover_exclusions(dense, floor) for floor in REPORT_FLOORS]
    record_exclusions = [
        leftover_exclusions(records, floor) for floor in REPORT_FLOORS
    ]
    squeeze = [
        squeeze_row(length, floor)
        for floor in REPORT_FLOORS
        for length in LEFTOVER_RECORDS
    ]
    leftover_nineteen = next(row for row in records if row["L"] == 19)
    return {
        "l_max": l_max,
        "floors": list(REPORT_FLOORS),
        "records": records,
        "dense_count": len(dense),
        "dominance": dominance_holds(dense) and dominance_holds(records),
        "exclusions": exclusions,
        "record_exclusions": record_exclusions,
        "squeeze": squeeze,
        "squeeze_fires_on_leftover_records": any(row["fires"] for row in squeeze),
        "length_nineteen": leftover_nineteen,
        "rhin_floor_for_nineteen": needed_floor_for_rhin(19),
        "perfect_gap_kills_nineteen_at_lean_floor": leftover_nineteen["exact_n_max"]
        <= LEAN_FLOOR,
        "git": git_commit(),
        "halt_theorem": False,
        "no_cycle_all_lengths": False,
        "x3_y2_campaign": False,
    }


def classify(scan: dict[str, Any], lean: dict[str, bool]) -> dict[str, Any]:
    lean_ok = (
        lean["sorry_free"]
        and all(lean[name] for name in EXISTING_LEAN)
        and not any(lean[f"has_{name}"] for name in FORBIDDEN_THEOREMS)
        and not any(lean[f"has_api_{name}"] for name in FORBIDDEN_NEW_API)
        and lean["cycle_finance_present"]
        and lean["no_baker_lean"]
        and lean["not_in_paper_barrel"]
    )
    if not lean_ok:
        return {"classification": CLASS_INCOMPLETE, "reason": f"lean_ok={lean_ok}"}
    if scan["halt_theorem"] or scan["no_cycle_all_lengths"] or scan["x3_y2_campaign"]:
        return {
            "classification": CLASS_INCOMPLETE,
            "reason": "out-of-scope claim",
        }
    if not scan["dominance"]:
        return {
            "classification": CLASS_INCOMPLETE,
            "reason": (
                "Rhin theta exceeded the exact gap on a tested length; "
                "the published bound was applied outside its range"
            ),
        }
    rhin_kills = sum(item["rhin_killed_count"] for item in scan["exclusions"])
    rhin_kills += sum(item["rhin_killed_count"] for item in scan["record_exclusions"])
    if rhin_kills > 0 or scan["squeeze_fires_on_leftover_records"]:
        return {
            "classification": CLASS_GREEN,
            "reason": (
                "a published lower bound excluded a leftover near-convergent "
                "or the Rhin/finance squeeze fired"
            ),
        }
    return {
        "classification": CLASS_CLOSED,
        "reason": (
            "Rhin/SdW Lemma 12 is strictly weaker than the exact gap on "
            "every tested length; the squeeze never fires on leftover "
            "record lengths at floors 53, 10^6, or 10^9; even the exact "
            "gap leaves L=19 alive at the Lean floor 53, so no correct "
            "transcendence lower bound can kill every near-convergent "
            "at a realistic floor"
        ),
    }


def probe_payload(*, l_max: int = TEST_L_MAX) -> dict[str, Any]:
    scan = run_probe(l_max=l_max)
    lean = lean_api_present()
    decision = classify(scan, lean)
    return {
        "experiment": "juggler_cycle_gap_baker",
        "engine_control_layer_modified": False,
        "anti_overclaim": {
            "halt_theorem": False,
            "no_cycle_all_lengths": False,
            "x3_y2_campaign": False,
            "baker_solver": False,
            "lean_rhin_imported": False,
            "new_lean_file": False,
        },
        "scan": scan,
        "lean": lean,
        "decision": decision,
        "search_method": (
            f"exact gap versus Rhin/SdW Lemma 12 on L<= {l_max} and "
            f"record lengths {list(RECORD_LENGTHS)}; squeeze at floors "
            f"{list(REPORT_FLOORS)}"
        ),
    }


def _fmt_float(value: float) -> str:
    if value == 0.0:
        return "0"
    if value < 1e-6 or value >= 1e6:
        return f"{value:.3e}"
    return f"{value:.6g}"


def render_markdown(payload: dict[str, Any]) -> str:
    decision = payload["decision"]
    scan = payload["scan"]
    nineteen = scan["length_nineteen"]
    lines = [
        "# Juggler cycle-gap Baker transfer",
        "",
        f"Status: **{decision['classification']}**",
        "",
        "Map the unused Simons-de Weger half (Rhin linear forms on",
        "|3^o - 2^L|) into Juggler cycle finance. Not a halt theorem.",
        "Not the parked x^3 - y^2 campaign.",
        "",
        "## Metadata",
        "",
        f"- classification: **{decision['classification']}**",
        f"- dense table: L <= `{scan['l_max']}`",
        f"- record lengths: `{list(RECORD_LENGTHS)}`",
        f"- dominance (Rhin weaker than exact): `{scan['dominance']}`",
        f"- squeeze fires on leftover records: "
        f"`{scan['squeeze_fires_on_leftover_records']}`",
        f"- exact gap kills L=19 at Lean floor 53: "
        f"`{scan['perfect_gap_kills_nineteen_at_lean_floor']}`",
        f"- Rhin floor that would exclude L=19: "
        f"`{scan['rhin_floor_for_nineteen']}`",
        "",
        decision["reason"] + ".",
        "",
        "## Record lengths: exact gap versus Rhin/SdW",
        "",
    ]
    for row in scan["records"]:
        lines.append(
            f"- L=`{row['L']}` o=`{row['o']}` exact theta=`{_fmt_float(row['exact_theta'])}` "
            f"n_max=`{row['exact_n_max']}` rhin theta=`{_fmt_float(row['rhin_theta'])}` "
            f"rhin n_max=`{row['rhin_n_max']}`"
        )
    lines.extend(
        [
            "",
            "## Leftover exclusions by floor",
            "",
        ]
    )
    for item in scan["exclusions"]:
        lines.append(
            f"- dense L<=`{scan['l_max']}`, floor `{item['floor']}`: "
            f"leftover `{item['leftover_count']}`, Rhin killed `{item['rhin_killed']}`"
        )
    for item in scan["record_exclusions"]:
        lines.append(
            f"- records, floor `{item['floor']}`: leftover `{item['leftover_count']}`, "
            f"Rhin killed `{item['rhin_killed']}`"
        )
    lines.extend(
        [
            "",
            "## Squeeze on leftover records",
            "",
        ]
    )
    for row in scan["squeeze"]:
        lines.append(
            f"- L=`{row['L']}` floor `{row['floor']}`: "
            f"finance cap `{_fmt_float(row['finance_theta_cap'])}`, "
            f"Rhin `{_fmt_float(row['rhin_theta'])}`, fires `{row['fires']}`"
        )
    lines.extend(
        [
            "",
            "## Length 19",
            "",
            f"- exact gap `3^{nineteen['o']} - 2^{nineteen['L']} = {nineteen['exact_gap']}`",
            f"- exact n_max `{nineteen['exact_n_max']}` (Lean floor is 53)",
            f"- Rhin n_max `{nineteen['rhin_n_max']}`",
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


def write_data_artifacts(payload: dict[str, Any]) -> None:
    DATA_DIR.mkdir(parents=True, exist_ok=True)
    scan = payload["scan"]
    (DATA_DIR / "records.json").write_text(
        json.dumps(scan["records"], indent=2) + "\n", encoding="utf-8"
    )
    (DATA_DIR / "exclusions.json").write_text(
        json.dumps(
            {
                "dense": scan["exclusions"],
                "records": scan["record_exclusions"],
            },
            indent=2,
        )
        + "\n",
        encoding="utf-8",
    )
    (DATA_DIR / "squeeze.json").write_text(
        json.dumps(scan["squeeze"], indent=2) + "\n", encoding="utf-8"
    )
    summary = {
        "classification": payload["decision"]["classification"],
        "reason": payload["decision"]["reason"],
        "l_max": scan["l_max"],
        "dominance": scan["dominance"],
        "squeeze_fires_on_leftover_records": scan[
            "squeeze_fires_on_leftover_records"
        ],
        "perfect_gap_kills_nineteen_at_lean_floor": scan[
            "perfect_gap_kills_nineteen_at_lean_floor"
        ],
        "rhin_floor_for_nineteen": scan["rhin_floor_for_nineteen"],
        "rhin_killed_dense": {
            str(item["floor"]): item["rhin_killed_count"]
            for item in scan["exclusions"]
        },
        "git": scan["git"],
    }
    (DATA_DIR / "summary.json").write_text(
        json.dumps(summary, indent=2) + "\n", encoding="utf-8"
    )
    (DATA_DIR / "README.md").write_text(
        "# Cycle-gap Baker transfer\n\n"
        "Rhin/SdW Lemma 12 versus the exact Juggler finance gap.\n"
        "Not a halt theorem. Not a Baker solver.\n\n"
        "Regenerate with `python -m research.juggler_sequence.cycle_gap_baker`.\n",
        encoding="utf-8",
    )


def write_artifacts(payload: dict[str, Any] | None = None) -> dict[str, Any]:
    data = payload if payload is not None else probe_payload()
    JSON_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(data, indent=2) + "\n", encoding="utf-8")
    DOC_PATH.write_text(render_markdown(data), encoding="utf-8")
    write_data_artifacts(data)
    return data


def main() -> None:
    payload = probe_payload(l_max=SCIENCE_L_MAX)
    write_artifacts(payload)
    decision = payload["decision"]
    scan = payload["scan"]
    print(decision["classification"])
    print(decision["reason"])
    print(
        f"dominance={scan['dominance']} "
        f"squeeze={scan['squeeze_fires_on_leftover_records']} "
        f"L19_exact_n_max={scan['length_nineteen']['exact_n_max']} "
        f"rhin_floor_19={scan['rhin_floor_for_nineteen']}"
    )


if __name__ == "__main__":
    main()
