"""Population survival sets B_k(N;X) and inverse mass.

Not a Research Engine control-layer experiment. Not a halt theorem.
Not a reopen of survivor-phase histograms, prefix cylinders,
excursion transfer, backward-geometry rank, or the Terras program.
Not a new atlas language tag and not SurvivalSet.lean.

Phase 0 forward-computes tau_N on several anchors and scaled
windows and asks whether S_{k+1}/S_k admits a stable rho<1
beyond the even leak. Density is not emptiness.
Absence is NOT_OBSERVED_WITHIN_BOUND.
"""

from __future__ import annotations

import json
import math
import subprocess
from math import isqrt
from pathlib import Path
from typing import Any

from research.juggler_sequence.atlas.schema import CLAIM_NOT_OBSERVED
from research.juggler_sequence.lean_paths import (
    JUGGLER_DIR,
    JUGGLER_PAPER_BARREL,
    engine_floor_text,
    has_named,
    juggler_text,
)
from research.juggler_sequence.power_itineraries import ANTI_OVERCLAIM, floor_power

REPO_ROOT = Path(__file__).resolve().parents[3]
JSON_PATH = REPO_ROOT / "docs" / "research" / "juggler_survival_set.json"
DOC_PATH = REPO_ROOT / "docs" / "research" / "juggler_survival_set.md"
DATA_DIR = REPO_ROOT / "data" / "research" / "juggler" / "survival_sets"

CLASS_CLOSED = "SURVIVAL_SET_CLOSED"
CLASS_PARK = "SURVIVAL_SET_PARK"
CLASS_GREEN = "SURVIVAL_SET_GREEN"
CLASS_INCOMPLETE = "SURVIVAL_SET_INCOMPLETE"

SCIENCE_ANCHORS = (2, 3, 5, 10, 50, 100, 1000)
SCIENCE_WINDOWS = (500_000, 1_000_000, 2_000_000, 4_000_000)
SCIENCE_K_MAX = 40
SCIENCE_BIT_CAP = 1024
TEST_ANCHORS = (3, 10)
TEST_WINDOWS = (80, 160)
TEST_K_MAX = 12
TEST_BIT_CAP = 256
THETAS = (0.5, 1.0)
RHO_CUT = 0.95
KEEP_CORE = 12

EXISTING_LEAN = (
    "even_itinerary_contracts",
    "floorPower_odd_even_two_step_lt",
    "even_preimage_iff",
    "AboveAnchor",
)

FORBIDDEN_THEOREMS = (
    "juggler_reaches_one",
    "no_juggler_escape",
    "all_finiteProgress",
)

FORBIDDEN_NEW_API = (
    "SurvivalSet",
    "InverseMass",
    "SurvivalCore",
    "WeightedContraction",
)

NEW_LEAN_FILES = (
    JUGGLER_DIR / "SurvivalSet.lean",
    JUGGLER_DIR / "InverseMass.lean",
    JUGGLER_DIR / "SurvivalCore.lean",
)


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


def tau_n(
    n: int,
    floor: int,
    *,
    k_max: int,
    bit_cap: int,
) -> tuple[int, str]:
    """Largest k <= k_max with T^j(n) >= floor for all j <= k."""

    if n < floor:
        return -1, "BELOW"
    x = n
    for step in range(k_max):
        if x.bit_length() > bit_cap:
            return step, "BIT_CAP"
        x = floor_power(x)
        if x < floor:
            return step, "RETURNED"
    return k_max, "HORIZON"


def interval_inverse_mass(anchor: int, x_max: int) -> dict[str, int]:
    """Windowed P([N,X]) counts. Exact integer arithmetic."""

    if x_max < anchor:
        return {"P_E": 0, "P_O": 0, "A": 0}
    size = x_max - anchor + 1
    even_lo = max(anchor, anchor * anchor)
    if even_lo % 2:
        even_lo += 1
    p_e = 0
    if even_lo <= x_max:
        p_e = ((x_max - even_lo) // 2) + 1
    odd_hi = 0
    lo = 1
    hi = x_max
    while lo <= hi:
        mid = (lo + hi) // 2
        cube = mid * mid * mid
        if isqrt(cube) <= x_max:
            odd_hi = mid
            lo = mid + 1
        else:
            hi = mid - 1
    odd_lo = anchor if anchor % 2 else anchor + 1
    p_o = 0
    if odd_hi >= odd_lo:
        p_o = ((odd_hi - odd_lo) // 2) + 1
    return {"P_E": p_e, "P_O": p_o, "A": size}


def even_leak_count(anchor: int, x_max: int) -> int:
    """Evens in [N, X] with n < N^2, hence T(n) < N."""

    if x_max < anchor:
        return 0
    hi = min(x_max, anchor * anchor - 1)
    lo = anchor + (anchor % 2)
    if lo > hi:
        return 0
    return ((hi - lo) // 2) + 1


def _empty_bucket(k_max: int) -> dict[str, Any]:
    return {
        "S": [0] * (k_max + 1),
        "even_S": [0] * (k_max + 1),
        "odd_S": [0] * (k_max + 1),
        "mu": {str(theta): [0.0] * (k_max + 1) for theta in THETAS},
        "starts": 0,
        "horizon": 0,
        "bit_cap": 0,
        "core": [],
    }


def _add_tau(
    bucket: dict[str, Any],
    n: int,
    tau: int,
    status: str,
    k_max: int,
) -> None:
    bucket["starts"] += 1
    if status == "HORIZON":
        bucket["horizon"] += 1
    elif status == "BIT_CAP":
        bucket["bit_cap"] += 1
    odd = n % 2 == 1
    weights = {str(theta): n ** (-theta) for theta in THETAS}
    limit = min(tau, k_max)
    for k in range(limit + 1):
        bucket["S"][k] += 1
        if odd:
            bucket["odd_S"][k] += 1
        else:
            bucket["even_S"][k] += 1
        for key, value in weights.items():
            bucket["mu"][key][k] += value
    if tau >= k_max and len(bucket["core"]) < KEEP_CORE:
        bucket["core"].append({"n": n, "tau": tau, "status": status})


def _profile_of(bucket: dict[str, Any], anchor: int, x_max: int, k_max: int) -> dict[str, Any]:
    total = x_max - anchor + 1 if x_max >= anchor else 0
    s = bucket["S"]
    ratios = []
    densities = []
    for k, count in enumerate(s):
        densities.append(count / total if total else 0.0)
        if k + 1 < len(s) and count:
            ratios.append(s[k + 1] / count)
        elif k + 1 < len(s):
            ratios.append(0.0)
    mu_ratio = {}
    for key, series in bucket["mu"].items():
        row = []
        for k in range(len(series) - 1):
            row.append(series[k + 1] / series[k] if series[k] else 0.0)
        mu_ratio[key] = row
    inv = interval_inverse_mass(anchor, x_max)
    leak = even_leak_count(anchor, x_max)
    s1_pred = total - leak
    max_r = max(ratios[1:], default=0.0) if len(ratios) > 1 else 0.0
    late = [r for r in ratios[max(1, k_max // 4) :] if r]
    late_mean = sum(late) / len(late) if late else 0.0
    return {
        "N": anchor,
        "X": x_max,
        "starts": bucket["starts"],
        "horizon": bucket["horizon"],
        "bit_cap": bucket["bit_cap"],
        "S": s,
        "even_S": bucket["even_S"],
        "odd_S": bucket["odd_S"],
        "R": ratios,
        "density": densities,
        "mu_R": mu_ratio,
        "interval_P": inv,
        "even_leak": leak,
        "S1_minus_even_leak": s[1] - s1_pred if len(s) > 1 else None,
        "max_R_after_0": max_r,
        "late_R_mean": late_mean,
        "core": bucket["core"],
    }


def run_probe(
    *,
    anchors: tuple[int, ...] = TEST_ANCHORS,
    windows: tuple[int, ...] = TEST_WINDOWS,
    k_max: int = TEST_K_MAX,
    bit_cap: int = TEST_BIT_CAP,
) -> dict[str, Any]:
    x_max = max(windows)
    buckets: dict[tuple[int, int], dict[str, Any]] = {
        (anchor, window): _empty_bucket(k_max)
        for anchor in anchors
        for window in windows
    }
    for n in range(2, x_max + 1):
        path: list[int] = [n]
        x = n
        status = "HORIZON"
        for _ in range(k_max):
            if x.bit_length() > bit_cap:
                status = "BIT_CAP"
                break
            x = floor_power(x)
            path.append(x)
            if x < 2:
                status = "RETURNED"
                break
        else:
            status = "HORIZON"
        for anchor in anchors:
            if n < anchor:
                continue
            tau = k_max
            row_status = status
            for j, value in enumerate(path):
                if value < anchor:
                    tau = j - 1
                    row_status = "RETURNED"
                    break
            for window in windows:
                if n <= window:
                    _add_tau(buckets[(anchor, window)], n, tau, row_status, k_max)

    profiles = [
        _profile_of(buckets[(anchor, window)], anchor, window, k_max)
        for anchor in anchors
        for window in windows
    ]
    scale_rows = []
    for anchor in anchors:
        by_x = {row["X"]: row for row in profiles if row["N"] == anchor}
        ordered = [by_x[window] for window in windows if window in by_x]
        if len(ordered) < 2:
            continue
        small, large = ordered[0], ordered[-1]
        dens_growth = []
        for k, (a, b) in enumerate(zip(small["density"], large["density"])):
            dens_growth.append({"k": k, "small": a, "large": b, "grows": b > a + 1e-6})
        scale_rows.append(
            {
                "N": anchor,
                "X_small": small["X"],
                "X_large": large["X"],
                "density_grows_at_k": [
                    row["k"] for row in dens_growth if row["grows"]
                ],
                "late_R_small": small["late_R_mean"],
                "late_R_large": large["late_R_mean"],
            }
        )

    uniform_rho = True
    only_even_s1 = True
    density_grows = False
    late_near_one = False
    for row in profiles:
        if row["max_R_after_0"] >= RHO_CUT:
            uniform_rho = False
        if row["S1_minus_even_leak"] not in (0, None) and abs(
            row["S1_minus_even_leak"] or 0
        ) > 0:
            only_even_s1 = False
        if row["late_R_mean"] >= RHO_CUT:
            late_near_one = True
    for row in scale_rows:
        if any(k >= 1 for k in row["density_grows_at_k"]):
            density_grows = True

    return {
        "anchors": list(anchors),
        "windows": list(windows),
        "k_max": k_max,
        "profiles": profiles,
        "scale": scale_rows,
        "uniform_rho": uniform_rho,
        "only_even_s1": only_even_s1,
        "density_grows_with_X": density_grows,
        "late_R_near_one": late_near_one,
        "git": git_commit(),
        "letter_chain": False,
        "itinerary_language_reopen": False,
        "phase_reopen": False,
        "terras_reopen": False,
        "halt_theorem": False,
        "survival_set_lean": False,
        "density_is_emptiness": False,
        "claim": CLAIM_NOT_OBSERVED,
    }


def lean_api_present() -> dict[str, bool]:
    combined = juggler_text()
    named = {name: has_named(combined, name) for name in EXISTING_LEAN}
    forbidden = {name: has_named(combined, name) for name in FORBIDDEN_THEOREMS}
    paper = JUGGLER_PAPER_BARREL.read_text(encoding="utf-8")
    return {
        "sorry_free": "sorry" not in combined and "admit" not in combined,
        **named,
        **{f"has_{name}": present for name, present in forbidden.items()},
        **{
            f"has_api_{name}": has_named(combined, name)
            for name in FORBIDDEN_NEW_API
        },
        "new_lean_file": any(path.is_file() for path in NEW_LEAN_FILES),
        "not_in_paper_barrel": all(
            name not in paper for name in FORBIDDEN_NEW_API
        ),
        "no_atlas_lang": "LANG_SURVIVAL" not in combined,
        "FloorPower_not_rewritten": "CycleItinerary" not in engine_floor_text(),
    }


def classify(scan: dict[str, Any], lean: dict[str, bool]) -> dict[str, Any]:
    lean_ok = (
        lean["sorry_free"]
        and all(lean[name] for name in EXISTING_LEAN)
        and not lean["has_juggler_reaches_one"]
        and not lean["new_lean_file"]
        and not any(lean[f"has_api_{name}"] for name in FORBIDDEN_NEW_API)
        and lean["not_in_paper_barrel"]
        and lean["no_atlas_lang"]
    )
    if not lean_ok:
        return {"classification": CLASS_INCOMPLETE, "reason": f"lean_ok={lean_ok}"}
    if (
        scan["letter_chain"]
        or scan["itinerary_language_reopen"]
        or scan["phase_reopen"]
        or scan["terras_reopen"]
        or scan["halt_theorem"]
        or scan["survival_set_lean"]
        or scan["density_is_emptiness"]
    ):
        return {
            "classification": CLASS_INCOMPLETE,
            "reason": "out-of-scope claim",
        }
    if scan["uniform_rho"]:
        return {
            "classification": CLASS_GREEN,
            "reason": (
                "S_{k+1}/S_k stayed below a uniform rho<1 across anchors "
                "and scaled windows"
            ),
        }
    if (
        scan["only_even_s1"]
        and (scan["density_grows_with_X"] or scan["late_R_near_one"])
        and not scan["uniform_rho"]
    ):
        return {
            "classification": CLASS_CLOSED,
            "reason": (
                "the first-step leak is the even FiniteProgress cut n<N^2; "
                "later R_k is not a uniform rho<1; density of B_k grows "
                "with X or late ratios return toward 1; no route from "
                "windowed rarity to arithmetic emptiness"
            ),
        }
    return {
        "classification": CLASS_PARK,
        "reason": (
            "windowed S_k decays in k but the decay is not a stable "
            "weighted contraction and is not isolated from the even leak"
        ),
    }


def probe_payload(
    *,
    anchors: tuple[int, ...] = TEST_ANCHORS,
    windows: tuple[int, ...] = TEST_WINDOWS,
    k_max: int = TEST_K_MAX,
    bit_cap: int = TEST_BIT_CAP,
) -> dict[str, Any]:
    scan = run_probe(
        anchors=anchors,
        windows=windows,
        k_max=k_max,
        bit_cap=bit_cap,
    )
    lean = lean_api_present()
    decision = classify(scan, lean)
    anti = dict(ANTI_OVERCLAIM)
    anti.update(
        {
            "density_is_emptiness": False,
            "survival_set_lean": False,
            "invariant_measure_theorem": False,
            "terras_reopen": False,
            "phase_reopen": False,
            "itinerary_language_reopen": False,
            "global_non_realizability": False,
        }
    )
    return {
        "experiment": "juggler_survival_set",
        "engine_control_layer_modified": False,
        "anti_overclaim": anti,
        "scan": scan,
        "lean": lean,
        "decision": decision,
        "search_method": (
            f"forward tau_N census; anchors {list(anchors)}; "
            f"windows {list(windows)}; k<={k_max}"
        ),
    }


def render_markdown(payload: dict[str, Any]) -> str:
    decision = payload["decision"]
    scan = payload["scan"]
    lean = payload["lean"]
    lines = [
        "# Juggler survival-set inverse mass",
        "",
        f"Status: **{decision['classification']}**",
        "",
        "Population B_k(N;X) and windowed inverse mass.",
        "Not a halt theorem. Density is not emptiness.",
        "Absence is NOT_OBSERVED_WITHIN_BOUND.",
        "",
        "## Branch budget",
        "",
        "```text",
        "Mathematical target     stable rho<1 inverse contraction beyond the even leak",
        "Novelty hypothesis      the survivor population cannot sustain itself",
        "Maximum Phase-0 scope   tau_N census; several N; scaled X; no Lean",
        "```",
        "",
        "## Metadata",
        "",
        f"- classification: **{decision['classification']}**",
        f"- anchors: `{scan['anchors']}` windows: `{scan['windows']}` "
        f"k_max: `{scan['k_max']}`",
        f"- uniform rho: `{scan['uniform_rho']}`",
        f"- S1 is even leak: `{scan['only_even_s1']}`",
        f"- density grows with X: `{scan['density_grows_with_X']}`",
        f"- late R near 1: `{scan['late_R_near_one']}`",
        "",
        decision["reason"] + ".",
        "",
        "## Profiles",
        "",
    ]
    for row in scan["profiles"]:
        lines.append(
            f"- N=`{row['N']}` X=`{row['X']}` S0=`{row['S'][0]}` "
            f"S1=`{row['S'][1] if len(row['S'])>1 else None}` "
            f"S_last=`{row['S'][-1]}` even_leak=`{row['even_leak']}` "
            f"late_R=`{row['late_R_mean']:.4f}` "
            f"P_E=`{row['interval_P']['P_E']}` P_O=`{row['interval_P']['P_O']}`"
        )
    lines.extend(["", "## Scale", ""])
    for row in scan["scale"]:
        lines.append(
            f"- N=`{row['N']}` density grows at k=`{row['density_grows_at_k'][:12]}` "
            f"late_R `{row['late_R_small']:.4f}` → `{row['late_R_large']:.4f}`"
        )
    lines.extend(
        [
            "",
            "## Existing Lean (unchanged)",
            "",
        ]
    )
    for name in EXISTING_LEAN:
        lines.append(f"- `{name}`: `{lean[name]}`")
    lines.extend(
        [
            f"- new Lean file: `{lean['new_lean_file']}`",
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
    for name in (
        "anchor_profiles",
        "inverse_mass",
        "weighted_mass",
        "survivor_cores",
        "tail_distributions",
        "exceptional_families",
    ):
        (DATA_DIR / name).mkdir(parents=True, exist_ok=True)
    scan = payload["scan"]
    (DATA_DIR / "anchor_profiles" / "profiles.json").write_text(
        json.dumps(
            [
                {
                    "N": row["N"],
                    "X": row["X"],
                    "S": row["S"],
                    "R": row["R"],
                    "density": row["density"],
                }
                for row in scan["profiles"]
            ],
            indent=2,
        )
        + "\n",
        encoding="utf-8",
    )
    (DATA_DIR / "inverse_mass" / "interval.json").write_text(
        json.dumps(
            [
                {
                    "N": row["N"],
                    "X": row["X"],
                    "P": row["interval_P"],
                    "even_leak": row["even_leak"],
                    "even_S": row["even_S"],
                    "odd_S": row["odd_S"],
                }
                for row in scan["profiles"]
            ],
            indent=2,
        )
        + "\n",
        encoding="utf-8",
    )
    (DATA_DIR / "weighted_mass" / "mu_R.json").write_text(
        json.dumps(
            [{"N": row["N"], "X": row["X"], "mu_R": row["mu_R"]} for row in scan["profiles"]],
            indent=2,
        )
        + "\n",
        encoding="utf-8",
    )
    (DATA_DIR / "survivor_cores" / "cores.json").write_text(
        json.dumps(
            [{"N": row["N"], "X": row["X"], "core": row["core"]} for row in scan["profiles"]],
            indent=2,
        )
        + "\n",
        encoding="utf-8",
    )
    (DATA_DIR / "tail_distributions" / "density.json").write_text(
        json.dumps(scan["scale"], indent=2) + "\n", encoding="utf-8"
    )
    (DATA_DIR / "exceptional_families" / "horizon.json").write_text(
        json.dumps(
            [
                {
                    "N": row["N"],
                    "X": row["X"],
                    "horizon": row["horizon"],
                    "bit_cap": row["bit_cap"],
                    "S_last": row["S"][-1],
                }
                for row in scan["profiles"]
            ],
            indent=2,
        )
        + "\n",
        encoding="utf-8",
    )
    summary = {
        "classification": payload["decision"]["classification"],
        "reason": payload["decision"]["reason"],
        "anchors": scan["anchors"],
        "windows": scan["windows"],
        "uniform_rho": scan["uniform_rho"],
        "only_even_s1": scan["only_even_s1"],
        "density_grows_with_X": scan["density_grows_with_X"],
        "claim": CLAIM_NOT_OBSERVED,
        "git": scan["git"],
    }
    (DATA_DIR / "summary.json").write_text(
        json.dumps(summary, indent=2) + "\n", encoding="utf-8"
    )
    (DATA_DIR / "README.md").write_text(
        "# Survival-set inverse mass\n\n"
        "Bounded B_k(N;X) census. Density is not emptiness.\n"
        "Absence is NOT_OBSERVED_WITHIN_BOUND.\n\n"
        "Regenerate with `python -m research.juggler_sequence.survival_set`.\n",
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
    payload = probe_payload(
        anchors=SCIENCE_ANCHORS,
        windows=SCIENCE_WINDOWS,
        k_max=SCIENCE_K_MAX,
        bit_cap=SCIENCE_BIT_CAP,
    )
    write_artifacts(payload)
    print(payload["decision"]["classification"])
    print(payload["decision"]["reason"])
    scan = payload["scan"]
    print(
        f"uniform_rho={scan['uniform_rho']} even_s1={scan['only_even_s1']} "
        f"dens_grows={scan['density_grows_with_X']} late1={scan['late_R_near_one']}"
    )


if __name__ == "__main__":
    main()
