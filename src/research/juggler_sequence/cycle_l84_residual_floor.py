"""L=84 residual-floor leftover census (Phase-0).

Not a Lean floor factory, not a Paper A edit, not a walk-charge
reopen, and not a halt theorem. Asks whether killing leftover 84
for all m at residual floor 1981 (joint/height) or 4756 (global)
renames the laboratory leftover to an 84-multiple or jumps it to
the next record 569.

Dossier: docs/problems/juggler_cycle_l84_residual_floor.md.
"""

from __future__ import annotations

import json
import math
import subprocess
from pathlib import Path
from typing import Any, Callable

from research.juggler_sequence.atlas.native import find_binary, parse_harvest_tsv, run_harvest
from research.juggler_sequence.certificate_harvest import first_certificate
from research.juggler_sequence.cycle_finance import EPS_CONST, finance_rows, git_commit
from research.juggler_sequence.cycle_floor_sensitivity import VERIFY_DIR, verify_floor_certified
from research.juggler_sequence.cycle_m_finance import steiner_rhs
from research.juggler_sequence.cycle_position_finance import (
    CURRENT_LEAN_RESIDUAL_FLOOR,
    l84_exclusion_floors,
    odd_run_heights,
    position_rhs,
    smallest_n_ln_gt,
)
from research.juggler_sequence.power_itineraries import ANTI_OVERCLAIM

REPO_ROOT = Path(__file__).resolve().parents[3]
DATA_DIR = REPO_ROOT / "data" / "research" / "juggler" / "cycle_position_finance"
HARVEST_DIR = REPO_ROOT / "data" / "research" / "juggler" / "cycle_l84_residual_floor"
N162_CERT = (
    REPO_ROOT
    / "data"
    / "research"
    / "juggler"
    / "cycle_finance"
    / "floor_verify"
    / "N162849448"
    / "certificate.json"
)

CLASS_PARK = "L84_RESIDUAL_FLOOR_PARK"
CLASS_JUMP = "L84_RESIDUAL_FLOOR_JUMP"
CLASS_INCOMPLETE = "L84_RESIDUAL_FLOOR_INCOMPLETE"

LIVE_FLOOR = CURRENT_LEAN_RESIDUAL_FLOOR
HEIGHT_ALL_M_FLOOR = 1981
GLOBAL_CONST1_FLOOR = 4756
CENSUS_L_MAX = 600
FAMILY_LENGTHS = (84, 168, 252, 336, 420, 504, 569, 588)
N162_FLOOR = 162_849_448
EVEN_SQUARE_CUT = 53 * 53
HARVEST_K_MAX = 20
SMOKE_FLOOR = 273


def _m_max(length: int, odd_count: int) -> int:
    even_count = length - odd_count
    return max(even_count, 1)


def _need(length: int, theta: float, const: float) -> float:
    return const * length / theta


def global_survives(n0: int, length: int, theta: float, const: float) -> bool:
    return n0 * math.log(n0) <= _need(length, theta, const)


def global_kill_floor(length: int, theta: float, const: float) -> int:
    return smallest_n_ln_gt(_need(length, theta, const))


def all_m_killed(
    n0: int,
    length: int,
    odd_count: int,
    theta: float,
    *,
    method: str,
    const: float,
    heights: list[int] | None = None,
) -> bool:
    levels = heights if heights is not None else odd_run_heights(n0)
    m_max = _m_max(length, odd_count)
    if method == "joint":
        return all(
            theta > steiner_rhs(n0, length, odd_count, m, const=const)
            for m in range(1, m_max + 1)
        )
    if method == "height":
        return all(
            theta
            > position_rhs(
                n0, length, odd_count, m, const=const, heights=levels
            )
            for m in range(1, m_max + 1)
        )
    raise ValueError(f"unknown method {method}")


def first_odd_kill_floor(
    pred: Callable[[int], bool],
    *,
    lo: int = 3,
    hi: int = 200_000,
) -> int | None:
    """Least odd n in [lo, hi] for which pred(n) holds."""

    left = lo if lo % 2 else lo + 1
    right = hi if hi % 2 else hi - 1
    if right < left:
        return None
    if not pred(right):
        return None
    if pred(left):
        return left
    while left + 2 < right:
        mid = left + ((right - left) // 4) * 2
        if mid <= left:
            mid = left + 2
        if pred(mid):
            right = mid
        else:
            left = mid
    return right


def method_kill_floor(
    length: int,
    odd_count: int,
    theta: float,
    *,
    method: str,
    const: float,
    lo: int = 3,
    hi: int = 200_000,
) -> int | None:
    return first_odd_kill_floor(
        lambda n: all_m_killed(
            n, length, odd_count, theta, method=method, const=const
        ),
        lo=lo,
        hi=hi,
    )


def named_leftover(rows: list[dict[str, Any]], *, method: str) -> dict[str, Any]:
    """Smallest L that still survives the method at this floor.

    Global leftover: smallest L with global_survives.
    Joint/height leftover: smallest L that survives global and is
    not killed for every m by that bound.
    """

    for row in rows:
        if method == "global":
            if row["global_survives"]:
                return {"L": row["L"], "kind": "named", **_focus(row)}
        elif method == "joint":
            if row["global_survives"] and not row["joint_kills_all_m"]:
                return {"L": row["L"], "kind": "named", **_focus(row)}
        elif method == "height":
            if row["global_survives"] and not row["height_kills_all_m"]:
                return {"L": row["L"], "kind": "named", **_focus(row)}
        else:
            raise ValueError(f"unknown method {method}")
    last = rows[-1]["L"] if rows else 0
    return {"L": last + 1, "kind": "ge", "o": None, "theta": None}


def _focus(row: dict[str, Any]) -> dict[str, Any]:
    return {
        "o": row["o"],
        "theta": row["theta"],
        "even_count": row["even_count"],
        "global_kill_floor": row["global_kill_floor"],
    }


def census_at_floor(
    n0: int,
    *,
    l_max: int = CENSUS_L_MAX,
    const: float = 1.0,
) -> dict[str, Any]:
    heights = odd_run_heights(n0)
    rows: list[dict[str, Any]] = []
    for item in finance_rows(l_max):
        length, odd_count, theta = item["L"], item["o"], item["theta"]
        survives = global_survives(n0, length, theta, const)
        joint_all = all_m_killed(
            n0,
            length,
            odd_count,
            theta,
            method="joint",
            const=const,
            heights=heights,
        )
        height_all = all_m_killed(
            n0,
            length,
            odd_count,
            theta,
            method="height",
            const=const,
            heights=heights,
        )
        rows.append(
            {
                "L": length,
                "o": odd_count,
                "theta": theta,
                "even_count": length - odd_count,
                "six_fifths_n_max": item["n_max"],
                "global_kill_floor": global_kill_floor(length, theta, const),
                "global_survives": survives,
                "joint_kills_all_m": joint_all,
                "height_kills_all_m": height_all,
            }
        )
    survivors = [row for row in rows if row["global_survives"]]
    return {
        "n0": n0,
        "const": const,
        "l_max": l_max,
        "n_ln_n": n0 * math.log(n0),
        "global_survivors": [row["L"] for row in survivors],
        "joint_survivors": [
            row["L"]
            for row in survivors
            if not row["joint_kills_all_m"]
        ],
        "height_survivors": [
            row["L"]
            for row in survivors
            if not row["height_kills_all_m"]
        ],
        "named": {
            "global": named_leftover(rows, method="global"),
            "joint": named_leftover(rows, method="joint"),
            "height": named_leftover(rows, method="height"),
        },
        "survivor_rows": survivors,
    }


def family_kill_floors(*, const: float = 1.0) -> list[dict[str, Any]]:
    by_length = {row["L"]: row for row in finance_rows(max(FAMILY_LENGTHS))}
    out: list[dict[str, Any]] = []
    for length in FAMILY_LENGTHS:
        row = by_length[length]
        odd_count, theta = row["o"], row["theta"]
        out.append(
            {
                "L": length,
                "o": odd_count,
                "theta": theta,
                "even_count": length - odd_count,
                "is_84_multiple": length % 84 == 0,
                "is_record": length == 569,
                "global": global_kill_floor(length, theta, const),
                "joint_all_m": method_kill_floor(
                    length, odd_count, theta, method="joint", const=const
                ),
                "height_all_m": method_kill_floor(
                    length, odd_count, theta, method="height", const=const
                ),
            }
        )
    return out


def leftover_census() -> dict[str, Any]:
    l84 = l84_exclusion_floors()
    const1 = {
        str(n0): census_at_floor(n0, const=1.0)
        for n0 in (HEIGHT_ALL_M_FLOOR, GLOBAL_CONST1_FLOOR)
    }
    six = {
        str(n0): census_at_floor(n0, const=EPS_CONST)
        for n0 in (HEIGHT_ALL_M_FLOOR, GLOBAL_CONST1_FLOOR)
    }
    family = {
        "const_1": family_kill_floors(const=1.0),
        "six_fifths": family_kill_floors(const=EPS_CONST),
    }
    height_1981 = const1[str(HEIGHT_ALL_M_FLOOR)]["named"]["height"]
    return {
        "live_lean_floor": LIVE_FLOOR,
        "height_all_m_floor": HEIGHT_ALL_M_FLOOR,
        "global_const1_floor": GLOBAL_CONST1_FLOOR,
        "even_square_cut": EVEN_SQUARE_CUT,
        "even_lt_sq_unchanged_at_1981": HEIGHT_ALL_M_FLOOR < EVEN_SQUARE_CUT,
        "l84_floors": {
            "const_1": l84["const_1"],
            "six_fifths": l84["six_fifths"],
        },
        "const_1": const1,
        "six_fifths": six,
        "family_kill_floors": family,
        "named_height_leftover_at_1981": height_1981,
    }


def cite_n162_certificate() -> dict[str, Any]:
    if not N162_CERT.is_file():
        return {"present": False, "path": str(N162_CERT)}
    cert = json.loads(N162_CERT.read_text(encoding="utf-8"))
    return {
        "present": True,
        "path": str(N162_CERT.relative_to(REPO_ROOT)).replace("\\", "/"),
        "N0": cert["N0"],
        "covers_1981": cert["N0"] >= HEIGHT_ALL_M_FLOOR,
        "covers_4756": cert["N0"] >= GLOBAL_CONST1_FLOOR,
        "sha256_chunks": cert["sha256_chunks"],
        "verified": cert["verified"],
        "halt_theorem": False,
    }


def run_floor_checksums(
    *,
    floors: tuple[int, ...] = (HEIGHT_ALL_M_FLOOR, GLOBAL_CONST1_FLOOR),
) -> dict[str, Any]:
    out: dict[str, Any] = {}
    for n_top in floors:
        cert = verify_floor_certified(
            n_top,
            progress=False,
            workers=1,
            resume=True,
            out_dir=VERIFY_DIR / f"N{n_top}",
        )
        out[str(n_top)] = {
            "verified": cert["verified"],
            "odds_walked": cert["odds_walked"],
            "max_stopping_time": cert["max_stopping_time"],
            "hardest_seed": cert["hardest_seed"],
            "max_bits": cert["max_bits"],
            "max_bits_seed": cert["max_bits_seed"],
            "sha256_chunks": cert["sha256_chunks"],
            "path": f"data/research/juggler/cycle_finance/floor_verify/N{n_top}/certificate.json",
            "implied_by_N162849448": True,
        }
    return out


def _python_harvest_window(n_begin: int, n_max: int, *, k_max: int) -> dict[str, Any]:
    coarse = {"E": 0, "OE": 0, "OOEE": 0, "leftover": 0, "uncapped": 0}
    overflow = 0
    leftover_itineraries: dict[str, int] = {}
    for n in range(n_begin, n_max + 1):
        if n % 2 == 0:
            coarse["E"] += 1
            continue
        rec = first_certificate(n, k_max=k_max)
        cls = rec["cls"]
        if cls == "uncapped":
            coarse["uncapped"] += 1
            overflow += 1
            continue
        if cls in coarse:
            coarse[cls] += 1
        if cls == "leftover":
            leftover_itineraries[rec["word"]] = leftover_itineraries.get(rec["word"], 0) + 1
    return {
        "backend": "python",
        "n_begin": n_begin,
        "n_max": n_max,
        "k_max": k_max,
        "coarse": coarse,
        "overflow_count": overflow,
        "leftover_types": len(leftover_itineraries),
        "leftover_itineraries": leftover_itineraries,
    }


def run_harvest_companion(
    *,
    n_begin: int = LIVE_FLOOR,
    n_max: int = GLOBAL_CONST1_FLOOR,
    k_max: int = HARVEST_K_MAX,
) -> dict[str, Any]:
    binary = find_binary()
    HARVEST_DIR.mkdir(parents=True, exist_ok=True)
    if binary is None:
        rec = _python_harvest_window(n_begin, n_max, k_max=k_max)
        rec["cuda_available"] = False
        rec["note"] = "atlas binary missing; python first-descent fallback"
        return rec
    tsv = HARVEST_DIR / f"harvest_{n_begin}_{n_max}.tsv"
    try:
        run_harvest(
            k_max=k_max,
            n_max=n_max,
            n_begin=n_begin,
            backend="cuda",
            output=tsv,
        )
        parsed = parse_harvest_tsv(tsv)
        return {
            "backend": "cuda",
            "cuda_available": True,
            "n_begin": n_begin,
            "n_max": n_max,
            "k_max": k_max,
            "overflow_count": int(parsed.get("count_overflow") or 0),
            "coarse": {
                "E": int(parsed.get("count_e") or 0),
                "OE": int(parsed.get("count_oe") or 0),
                "OOEE": int(parsed.get("count_ooee") or 0),
                "leftover": int(parsed.get("count_leftover") or 0),
                "uncapped": int(parsed.get("count_uncapped") or 0),
            },
            "tsv": str(tsv.relative_to(REPO_ROOT)).replace("\\", "/"),
        }
    except (OSError, FileNotFoundError, subprocess.CalledProcessError) as exc:
        rec = _python_harvest_window(n_begin, n_max, k_max=k_max)
        rec["cuda_available"] = True
        rec["cuda_error"] = str(exc)
        rec["note"] = "cuda harvest failed; python first-descent fallback"
        return rec


def is_84_family(length: int) -> bool:
    return length % 84 == 0 and length > 0


def classify_census(census: dict[str, Any]) -> dict[str, Any]:
    named = census["named_height_leftover_at_1981"]
    leftover = int(named["L"])
    if leftover == 84:
        return {
            "classification": CLASS_INCOMPLETE,
            "reason": "height at 1981 did not kill L=84; l84_floors.json is contradicted",
        }
    if leftover == 569:
        return {
            "classification": CLASS_JUMP,
            "reason": (
                "height at 1981 kills the 84-family through 504 and "
                "the named leftover jumps to the next record 569"
            ),
            "named_leftover": leftover,
        }
    if is_84_family(leftover):
        return {
            "classification": CLASS_PARK,
            "reason": (
                f"height at 1981 kills L=84 and the named leftover "
                f"becomes {leftover}, an 84-multiple with global floor "
                "still at the 84-scale; leftover rename"
            ),
            "named_leftover": leftover,
        }
    return {
        "classification": CLASS_PARK,
        "reason": (
            f"height at 1981 kills L=84; the named leftover is {leftover}, "
            "not a jump to 569"
        ),
        "named_leftover": leftover,
    }


def probe_payload(*, certificates: bool = False) -> dict[str, Any]:
    census = leftover_census()
    decision = classify_census(census)
    anti = dict(ANTI_OVERCLAIM)
    anti.update(
        {
            "halt_theorem": False,
            "no_cycle_all_lengths": False,
            "lean_floor_raise": False,
            "paper_a_edit": False,
            "walk_charge_reopened": False,
            "new_cuda_kernel": False,
            "n0_raised": False,
        }
    )
    payload = {
        "experiment": "juggler_cycle_l84_residual_floor",
        "engine_control_layer_modified": False,
        "anti_overclaim": anti,
        "census": census,
        "decision": decision,
        "certificates": {
            "n162849448": cite_n162_certificate(),
        },
        "git": git_commit(),
        "halt_theorem": False,
        "no_cycle_all_lengths": False,
        "new_lean": False,
        "new_paper": False,
        "search_method": (
            "const-1 and 6/5 leftover census at residual floors 1981 "
            "and 4756; family kill floors for "
            f"{list(FAMILY_LENGTHS)}; N162849448 cited as totality"
        ),
    }
    if certificates:
        payload["certificates"]["checksums"] = run_floor_checksums()
        payload["certificates"]["harvest"] = run_harvest_companion()
    return payload


def write_data_artifacts(payload: dict[str, Any]) -> None:
    DATA_DIR.mkdir(parents=True, exist_ok=True)
    census = payload["census"]
    artifact = {
        "live_lean_floor": census["live_lean_floor"],
        "height_all_m_floor": census["height_all_m_floor"],
        "global_const1_floor": census["global_const1_floor"],
        "even_lt_sq_unchanged_at_1981": census["even_lt_sq_unchanged_at_1981"],
        "named_height_leftover_at_1981": census["named_height_leftover_at_1981"],
        "named_at_floors": {
            "const_1": {
                key: value["named"] for key, value in census["const_1"].items()
            },
            "six_fifths": {
                key: value["named"] for key, value in census["six_fifths"].items()
            },
        },
        "global_survivors": {
            "const_1": {
                key: value["global_survivors"]
                for key, value in census["const_1"].items()
            },
            "six_fifths": {
                key: value["global_survivors"]
                for key, value in census["six_fifths"].items()
            },
        },
        "height_survivors": {
            "const_1": {
                key: value["height_survivors"]
                for key, value in census["const_1"].items()
            }
        },
        "family_kill_floors": census["family_kill_floors"],
        "l84_floors": census["l84_floors"],
        "certificates": payload["certificates"],
        "decision": payload["decision"],
        "git": payload["git"],
        "halt_theorem": False,
        "no_cycle_all_lengths": False,
    }
    (DATA_DIR / "leftover_at_floors.json").write_text(
        json.dumps(artifact, indent=2) + "\n", encoding="utf-8"
    )


def main() -> None:
    payload = probe_payload(certificates=True)
    write_data_artifacts(payload)
    decision = payload["decision"]
    named = payload["census"]["named_height_leftover_at_1981"]
    print(decision["classification"])
    print(decision["reason"])
    print(f"named_height_leftover_at_1981={named}")
    print(f"certificates={payload['certificates'].keys()}")


if __name__ == "__main__":
    main()
