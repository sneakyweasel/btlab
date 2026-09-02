"""Fixed-family descent density inside the odd-to-odd class.

Not a Research Engine control-layer experiment. Not a halt theorem.
Not Terras's theorem and not a density of ReachesOne. Does not reopen
image-discrepancy transfer, cycle leftovers, or a FiniteProgress tactic.
"""

from __future__ import annotations

import json
from pathlib import Path
from typing import Any

from research.juggler_sequence.lean_paths import ENVELOPE, PROGRESS, has_named, juggler_text
from research.juggler_sequence.power_itineraries import ANTI_OVERCLAIM, floor_power

REPO_ROOT = Path(__file__).resolve().parents[3]
JSON_PATH = REPO_ROOT / "docs" / "research" / "juggler_oo_descent_density.json"
DOC_PATH = REPO_ROOT / "docs" / "research" / "juggler_oo_descent_density.md"
DOSSIER_PATH = REPO_ROOT / "docs" / "problems" / "juggler_oo_descent_density.md"

WORD_OOOEE = "OOOEE"
WORD_OOEOE = "OOEOE"
WORDS = (WORD_OOOEE, WORD_OOEOE)
HORIZONS = (5, 10, 20, 40)
EXACT_HORIZON = 20
SNAPSHOTS = (1_000, 10_000, 100_000, 1_000_000)
N_MAX = SNAPSHOTS[-1]
BIT_CAP = 4096

# Math-note Proposition 4.4 (legacy artifact key: prop45), N=10^3 row.
PROP45_N1000 = {"oo": 252, "oo_return20": 221, "all_return20": 968}

CLASS_VANISHING = "FIXED_FAMILY_VANISHING"
CLASS_LEFTOVER = "FIXED_FAMILY_POSITIVE_LEFTOVER"
CLASS_REPACK = "REPARAMETERIZATION"
CLASS_INCOMPLETE = "OO_DESCENT_DENSITY_INCOMPLETE"

PLATEAU_MIN = 0.02
PLATEAU_DELTA = 0.03

LEAN_THEOREMS = (
    "FiniteProgress",
    "unresolved_is_odd_odd",
    "power_bound_contracts",
    "floorPower_oooee_of_follows",
    "itineraryOOOEE",
    "odd_preimage_unique",
)


def is_odd_odd(n: int) -> bool:
    return n >= 3 and n % 2 == 1 and floor_power(n) % 2 == 1


def walk_prefix(
    n: int,
    horizon: int = HORIZONS[-1],
    *,
    bit_cap: int | None = BIT_CAP,
) -> dict[str, Any]:
    """Parity prefix and first strict return of an OO start."""

    letters: list[str] = []
    current = n
    tau: int | None = None
    bit_cap_hit = False
    for step in range(1, horizon + 1):
        letters.append("E" if current % 2 == 0 else "O")
        current = floor_power(current)
        if bit_cap is not None and current.bit_length() > bit_cap:
            bit_cap_hit = True
            break
        if current < n:
            tau = step
            break
    prefix = "".join(letters)
    return {
        "n": n,
        "prefix": prefix,
        "tau": tau,
        "bit_cap_hit": bit_cap_hit,
        "steps_computed": len(letters),
        "oooee": prefix.startswith(WORD_OOOEE),
        "ooeoe": prefix.startswith(WORD_OOEOE),
    }


def _empty_row() -> dict[str, int]:
    row = {
        "n_max": 0,
        "all_starts": 0,
        "oo": 0,
        "oooee": 0,
        "ooeoe": 0,
        "word_union": 0,
        "bit_cap_40": 0,
        "unresolved_through_20": 0,
    }
    for k in HORIZONS:
        row[f"oo_return_{k}"] = 0
        row[f"all_return_{k}"] = 0
    return row


def _snapshot_row(acc: dict[str, int], n_max: int) -> dict[str, Any]:
    oo = acc["oo"]
    row: dict[str, Any] = {
        "n_max": n_max,
        "all_starts": acc["all_starts"],
        "oo": oo,
        "oooee": acc["oooee"],
        "ooeoe": acc["ooeoe"],
        "word_union": acc["word_union"],
        "bit_cap_40": acc["bit_cap_40"],
        "unresolved_through_20": acc["unresolved_through_20"],
        "exact_through_horizon": EXACT_HORIZON,
    }
    for k in HORIZONS:
        oo_ret = acc[f"oo_return_{k}"]
        all_ret = acc[f"all_return_{k}"]
        row[f"oo_return_{k}"] = oo_ret
        row[f"all_return_{k}"] = all_ret
        row[f"oo_return_rate_{k}"] = round(oo_ret / oo, 8) if oo else None
        row[f"all_return_rate_{k}"] = (
            round(all_ret / acc["all_starts"], 8) if acc["all_starts"] else None
        )
        row[f"oo_leftover_{k}"] = oo - oo_ret
        row[f"oo_leftover_rate_{k}"] = round((oo - oo_ret) / oo, 8) if oo else None
    row["oooee_rate"] = round(acc["oooee"] / oo, 8) if oo else None
    row["ooeoe_rate"] = round(acc["ooeoe"] / oo, 8) if oo else None
    row["word_union_rate"] = round(acc["word_union"] / oo, 8) if oo else None
    row["oooee_leftover_rate"] = round((oo - acc["oooee"]) / oo, 8) if oo else None
    row["ooeoe_leftover_rate"] = round((oo - acc["ooeoe"]) / oo, 8) if oo else None
    row["word_union_leftover_rate"] = (
        round((oo - acc["word_union"]) / oo, 8) if oo else None
    )
    return row


def window_census(n_max: int, snapshots: tuple[int, ...] | None = None) -> list[dict[str, Any]]:
    """One pass through 2..n_max, recording rows at each snapshot ≤ n_max."""

    wanted = tuple(s for s in (snapshots or SNAPSHOTS) if s <= n_max)
    if n_max not in wanted:
        wanted = (*wanted, n_max)
    acc = _empty_row()
    rows: list[dict[str, Any]] = []
    snap_i = 0
    for n in range(2, n_max + 1):
        acc["all_starts"] += 1
        if n % 2 == 0:
            for k in HORIZONS:
                acc[f"all_return_{k}"] += 1
        else:
            t1 = floor_power(n)
            if t1 % 2 == 0:
                for k in HORIZONS:
                    if k >= 2:
                        acc[f"all_return_{k}"] += 1
            else:
                acc["oo"] += 1
                walked = walk_prefix(n)
                if walked["bit_cap_hit"] and walked["tau"] is None:
                    acc["bit_cap_40"] += 1
                if walked["oooee"]:
                    acc["oooee"] += 1
                if walked["ooeoe"]:
                    acc["ooeoe"] += 1
                if walked["oooee"] or walked["ooeoe"]:
                    acc["word_union"] += 1
                if (
                    walked["bit_cap_hit"]
                    and walked["tau"] is None
                    and walked["steps_computed"] <= EXACT_HORIZON
                ):
                    exact_tau = walk_prefix(
                        n, EXACT_HORIZON, bit_cap=None
                    )["tau"]
                else:
                    exact_tau = (
                        walked["tau"]
                        if walked["tau"] is not None
                        and walked["tau"] <= EXACT_HORIZON
                        else None
                    )
                for k in HORIZONS:
                    tau = exact_tau if k <= EXACT_HORIZON else walked["tau"]
                    if k > EXACT_HORIZON and exact_tau is not None:
                        tau = exact_tau
                    if tau is not None and tau <= k:
                        acc[f"oo_return_{k}"] += 1
                        acc[f"all_return_{k}"] += 1
        while snap_i < len(wanted) and n == wanted[snap_i]:
            rows.append(_snapshot_row(acc, n))
            snap_i += 1
    return rows


def leftover_series(rows: list[dict[str, Any]], key: str) -> list[float]:
    return [float(row[key]) for row in rows if row[key] is not None]


def is_plateau(fracs: list[float]) -> bool:
    if len(fracs) < 2:
        return False
    if fracs[-1] < PLATEAU_MIN:
        return False
    return abs(fracs[-1] - fracs[-2]) <= PLATEAU_DELTA


def is_vanishing(fracs: list[float]) -> bool:
    if not fracs:
        return False
    if fracs[-1] < PLATEAU_MIN:
        return True
    return len(fracs) >= 2 and fracs[-1] <= 0.5 * fracs[0] and fracs[-1] < 0.05


def family_leftovers(rows: list[dict[str, Any]]) -> dict[str, list[float]]:
    phase0 = [row for row in rows if row["n_max"] in (10_000, 100_000, 1_000_000)]
    source = phase0 if len(phase0) >= 2 else rows
    keys = {
        "oooee": "oooee_leftover_rate",
        "ooeoe": "ooeoe_leftover_rate",
        "word_union": "word_union_leftover_rate",
        "horizon_5": "oo_leftover_rate_5",
        "horizon_10": "oo_leftover_rate_10",
        "horizon_20": "oo_leftover_rate_20",
        "horizon_40": "oo_leftover_rate_40",
    }
    return {name: leftover_series(source, key) for name, key in keys.items()}


def reproduce_prop45(rows: list[dict[str, Any]]) -> dict[str, Any]:
    match = next((row for row in rows if row["n_max"] == 1_000), None)
    if match is None:
        return {"present": False, "ok": False}
    ok = (
        match["oo"] == PROP45_N1000["oo"]
        and match["oo_return_20"] == PROP45_N1000["oo_return20"]
        and match["all_return_20"] == PROP45_N1000["all_return20"]
    )
    return {
        "present": True,
        "ok": ok,
        "oo": match["oo"],
        "oo_return_20": match["oo_return_20"],
        "all_return_20": match["all_return_20"],
        "expected": dict(PROP45_N1000),
    }


def lean_api_present() -> dict[str, bool]:
    text = juggler_text()
    progress = PROGRESS.read_text(encoding="utf-8")
    envelope = ENVELOPE.read_text(encoding="utf-8")
    combined = text
    return {
        "sorry_free": "sorry" not in combined and "admit" not in combined,
        **{name: has_named(combined, name) for name in LEAN_THEOREMS},
        "no_global_termination_theorem": "theorem juggler_reaches_one" not in combined,
        "no_all_finiteProgress_proved": "theorem all_finiteProgress" not in progress,
        "no_progress_tactic": "findProgress" not in combined,
        "no_length_seven_cycle_theorem": "theorem no_cycle_itinerary_length_seven"
        not in combined,
        "Envelope_not_rewritten_as_density": "oo_descent_density" not in envelope,
    }


def classify(rows: list[dict[str, Any]], lean: dict[str, bool]) -> dict[str, Any]:
    lean_ok = (
        lean["sorry_free"]
        and lean["FiniteProgress"]
        and lean["floorPower_oooee_of_follows"]
        and lean["no_global_termination_theorem"]
        and lean["no_all_finiteProgress_proved"]
        and lean["no_progress_tactic"]
    )
    if not lean_ok or len(rows) < 2:
        return {
            "classification": CLASS_INCOMPLETE,
            "reason": f"lean_ok={lean_ok} rows={len(rows)}",
        }
    families = family_leftovers(rows)
    vanishing = {name: is_vanishing(fracs) for name, fracs in families.items()}
    plateaus = {name: is_plateau(fracs) for name, fracs in families.items()}
    last = {name: (fracs[-1] if fracs else None) for name, fracs in families.items()}
    prop45 = reproduce_prop45(rows)
    if any(vanishing.values()):
        hit = [name for name, flag in vanishing.items() if flag]
        return {
            "classification": CLASS_VANISHING,
            "secondary": [],
            "vanishing": vanishing,
            "plateaus": plateaus,
            "last_leftover": last,
            "prop45": prop45,
            "reason": (
                "leftover of a named fixed family appears to go to 0: "
                + ", ".join(hit)
            ),
        }
    if all(plateaus.values()):
        if prop45.get("ok") and _only_restates_prop45(rows, last):
            return {
                "classification": CLASS_REPACK,
                "secondary": [],
                "vanishing": vanishing,
                "plateaus": plateaus,
                "last_leftover": last,
                "prop45": prop45,
                "reason": (
                    "census reproduces Proposition 4.5 and adds no split "
                    "beyond the horizon-20 leftover"
                ),
            }
        return {
            "classification": CLASS_LEFTOVER,
            "secondary": [],
            "vanishing": vanishing,
            "plateaus": plateaus,
            "last_leftover": last,
            "prop45": prop45,
            "reason": (
                "every tested fixed family has a stable leftover fraction "
                "bounded away from 0"
            ),
        }
    return {
        "classification": CLASS_INCOMPLETE,
        "vanishing": vanishing,
        "plateaus": plateaus,
        "last_leftover": last,
        "prop45": prop45,
        "reason": "leftover series are neither uniformly vanishing nor plateaus",
    }


def _only_restates_prop45(rows: list[dict[str, Any]], last: dict[str, float | None]) -> bool:
    """True only if words were not measured as a separate split."""

    del rows
    word_keys = ("oooee", "ooeoe", "word_union")
    return all(last.get(name) is None for name in word_keys)


def run_probe(n_max: int = N_MAX) -> dict[str, Any]:
    rows = window_census(n_max)
    return {
        "basin": [1],
        "n_max": n_max,
        "words": list(WORDS),
        "horizons": list(HORIZONS),
        "snapshots": [row["n_max"] for row in rows],
        "rows": rows,
        "families": family_leftovers(rows),
        "prop45": reproduce_prop45(rows),
    }


def probe_payload(n_max: int = N_MAX) -> dict[str, Any]:
    scan = run_probe(n_max)
    lean = lean_api_present()
    decision = classify(scan["rows"], lean)
    anti = dict(ANTI_OVERCLAIM)
    anti.update(
        {
            "almost_all_finiteProgress": False,
            "almost_all_reachesOne": False,
            "terras_for_juggler": False,
            "image_discrepancy_transfer": False,
            "finite_progress_for_all": False,
            "cycle_obstruction": False,
        }
    )
    return {
        "experiment": "juggler_oo_descent_density",
        "engine_control_layer_modified": False,
        "anti_overclaim": anti,
        "scan": scan,
        "lean": lean,
        "decision": decision,
        "search_method": (
            "one pass n=2..N; OO is odd with odd first image; "
            "OOOEE/OOEOE prefixes and first strict return at K=5,10,20,40; "
            "K<=20 exact with uncapped reruns; K=40 is capped; "
            "no FiniteProgress tactic"
        ),
    }


def render_markdown(payload: dict[str, Any]) -> str:
    decision = payload["decision"]
    scan = payload["scan"]
    lean = payload["lean"]
    lines = [
        "# Juggler odd-to-odd descent density",
        "",
        f"Status: **{decision['classification']}**",
        "",
        "Standalone application phase. Not a Research Engine experiment",
        "and not a termination theorem. Fixed finite certificate families",
        "inside the odd-to-odd class: `OOOEE`, `OOEOE`, and first return",
        "in at most `K` steps. This is not Terras's theorem.",
        "",
        "## Branch budget",
        "",
        "```text",
        "Mathematical target     Does any fixed finite certificate family",
        "                        cover almost all of OO, or is leftover",
        "                        density bounded away from 0?",
        "Novelty hypothesis      leftover o(|OO|) for a named word or horizon,",
        "                        or a positive leftover plateau",
        "Falsifier               leftover plateau for every fixed family,",
        "                        or a rewrite of Corollary 5.2 / Prop 4.5",
        "Existing machinery      FiniteProgress; itineraryOOOEE; Prop 4.5",
        "Maximum Phase-0 scope   OOOEE, OOEOE, K=5,10,20,40; N=10^4,10^5,10^6",
        "```",
        "",
        "## Metadata",
        "",
        f"- basin: `{scan['basin']}`",
        f"- engine control layer modified: `{payload['engine_control_layer_modified']}`",
        f"- classification: **{decision['classification']}**",
        f"- words: `{scan['words']}`",
        f"- horizons: `{scan['horizons']}`",
        f"- sorry-free: `{lean['sorry_free']}`",
        "",
        decision["reason"] + ".",
        "",
        "## Census",
        "",
    ]
    for row in scan["rows"]:
        lines.append(f"### N=`{row['n_max']}`")
        lines.append("")
        lines.append(f"- OO starts: `{row['oo']}`")
        lines.append(f"- all starts: `{row['all_starts']}`")
        lines.append(f"- realize OOOEE: `{row['oooee']}` rate=`{row['oooee_rate']}` leftover=`{row['oooee_leftover_rate']}`")
        lines.append(f"- realize OOEOE: `{row['ooeoe']}` rate=`{row['ooeoe_rate']}` leftover=`{row['ooeoe_leftover_rate']}`")
        lines.append(
            f"- word union: `{row['word_union']}` rate=`{row['word_union_rate']}` leftover=`{row['word_union_leftover_rate']}`"
        )
        for k in HORIZONS:
            lines.append(
                f"- OO return ≤{k}: `{row[f'oo_return_{k}']}` rate=`{row[f'oo_return_rate_{k}']}` leftover=`{row[f'oo_leftover_{k}']}` leftover_rate=`{row[f'oo_leftover_rate_{k}']}`"
            )
        lines.append(f"- all-start return ≤20: `{row['all_return_20']}` rate=`{row['all_return_rate_20']}`")
        lines.append(f"- exact through horizon: `{row['exact_through_horizon']}`")
        lines.append(f"- unresolved through horizon 20: `{row['unresolved_through_20']}`")
        lines.append(f"- horizon-40 bit-cap exits: `{row['bit_cap_40']}`")
        lines.append("")
    prop45 = scan["prop45"]
    lines.extend(
        [
            "## Proposition 4.4 reproduction",
            "",
            f"- present: `{prop45.get('present')}`",
            f"- matches N=10^3 row: `{prop45.get('ok')}`",
            f"- observed: OO=`{prop45.get('oo')}` return20=`{prop45.get('oo_return_20')}` all20=`{prop45.get('all_return_20')}`",
            "",
            "## Lean witnesses",
            "",
        ]
    )
    for name in LEAN_THEOREMS:
        lines.append(f"- `{name}`: `{lean.get(name)}`")
    lines.extend(
        [
            f"- no halt theorem: `{lean.get('no_global_termination_theorem')}`",
            f"- no all-FiniteProgress theorem: `{lean.get('no_all_finiteProgress_proved')}`",
            f"- no progress tactic: `{lean.get('no_progress_tactic')}`",
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
            "This is not a halt result. It is not almost-all FiniteProgress",
            "and not a density of ReachesOne.",
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
    for row in payload["scan"]["rows"]:
        print(
            row["n_max"],
            row["oo"],
            row["oooee_leftover_rate"],
            row["word_union_leftover_rate"],
            row["oo_leftover_rate_20"],
            row["oo_leftover_rate_40"],
        )


if __name__ == "__main__":
    main()
