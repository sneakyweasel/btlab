"""Residual-step certificate propagation on odd-to-odd Juggler starts.

Not a Research Engine control-layer experiment. Not a halt theorem.
Records that ReachesOne, Capture, and ReturnBelow propagate backward
along a residual excursion, while Descent at the residual need not.
"""

from __future__ import annotations

import json
from pathlib import Path
from typing import Any

from research.juggler_sequence.odd_odd_frontier import (
    even_run_end,
    first_even_residual,
    post_even_kind,
)
from research.juggler_sequence.power_itineraries import ANTI_OVERCLAIM, floor_power
from research.juggler_sequence.progress_coverage import coverage_bucket, is_odd_odd
from research.juggler_sequence.lean_paths import (
    ENVELOPE,
    MINIMAL,
    PROGRESS,
    RESIDUALS,
    juggler_text,
    engine_floor_text,
    has_named,
)

REPO_ROOT = Path(__file__).resolve().parents[3]
JSON_PATH = REPO_ROOT / "docs" / "research" / "juggler_residual_chain.json"
DOC_PATH = REPO_ROOT / "docs" / "research" / "juggler_residual_chain.md"
LEAN_PATH = RESIDUALS
FRONTIER_PATH = RESIDUALS
PROGRESS_PATH = PROGRESS
FLOOR_PATH = ENVELOPE
MIN_PATH = MINIMAL

CLASS_GREEN = "RESIDUAL_CHAIN_GREEN"
CLASS_CLOSURE = "RESIDUAL_CERTIFICATE_CLOSURE_GREEN"
CLASS_PERSISTENT = "PERSISTENT_ODD_RESIDUAL_COUNTEREXAMPLE"
CLASS_REDUCES = "RESIDUAL_CHAIN_REDUCES_NO_FURTHER"
CLASS_INCOMPLETE = "RESIDUAL_CHAIN_INCOMPLETE"

N_MAX = 80
FIRST_EVEN_CAP = 24
CHAIN_CAP = 8
HARD_PROBES = (9, 37, 49, 69, 77)

LEAN_THEOREMS = (
    "ResidualStep",
    "PersistentOddResidual",
    "residualStep_word",
    "reachesOne_of_residualStep",
    "finiteProgress_of_residual_capture",
    "finiteProgress_of_residual_returnBelow",
    "residual_descent_not_below",
    "persistent_odd_odd",
    "persistent_residual_preserves_frontier",
    "minimal_residual_scale",
    "ResidualChain",
    "reachesOne_of_residualChain",
    "finiteProgress_of_residualChain_returnBelow",
    "finiteProgress_of_residualChain_capture",
)

CERTIFICATE_UNCHANGED = (
    "FiniteProgress",
    "ReachesOne",
    "DescentCertificate",
    "descent_of_below",
    "ReturnBelow",
    "MinimalNonTerm",
    "reachesOne_of_image",
    "capture_of_suffix",
)


def residual_excursion(x: int, cap: int = FIRST_EVEN_CAP) -> dict[str, Any] | None:
    if x <= 1:
        return None
    if x % 2 == 0:
        a, z = 0, x
    else:
        fe = first_even_residual(x, cap)
        if fe is None:
            return None
        a, z = fe["a"], fe["z"]
    e = floor_power(z)
    b, y = even_run_end(z)
    if b < 1:
        return None
    return {"a": a, "z": z, "e": e, "b": b, "y": y}


def residual_class(n: int, y: int) -> str:
    if y == 1:
        return "CAPTURE"
    if y < n:
        return "RETURN_BELOW"
    if y == n:
        return "CYCLE"
    if y % 2 == 0:
        return "STAY_EVEN"
    if is_odd_odd(y):
        return "PERSISTENT_ODD_ODD"
    return "STAY_AUTO_FP"


def first_residual_class(n: int, cap: int = FIRST_EVEN_CAP) -> str:
    if not is_odd_odd(n):
        return "NOT_ODD_ODD"
    step = residual_excursion(n, cap)
    if step is None:
        return "NO_EVEN"
    return residual_class(n, step["y"])


def residual_chain(n: int, *, max_steps: int = CHAIN_CAP) -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    current = n
    for index in range(max_steps):
        if current <= 1:
            break
        step = residual_excursion(current)
        if step is None:
            break
        y = step["y"]
        row = {
            "i": index,
            "x": current,
            "x_odd_odd": current >= 2 and is_odd_odd(current),
            "a": step["a"],
            "z": step["z"],
            "b": step["b"],
            "y": y,
            "y_parity": "even" if y % 2 == 0 else "odd",
            "y_bucket": "ONE" if y == 1 else coverage_bucket(y) if y >= 2 else "ZERO",
            "y_odd_odd": y >= 2 and is_odd_odd(y),
            "vs_n": post_even_kind(n, y),
            "vs_x": post_even_kind(current, y),
            "kind": residual_class(n, y),
            "persistent": y > current and y >= 2 and is_odd_odd(y),
            "auto_fp": y >= 2 and not is_odd_odd(y) and y != 1,
            "y_lt_n": y < n,
        }
        rows.append(row)
        if y < n or y == 1:
            break
        current = y
    return rows


def residual_census(*, n_max: int = N_MAX) -> dict[str, Any]:
    counts = {
        "CAPTURE": 0,
        "RETURN_BELOW": 0,
        "CYCLE": 0,
        "STAY_AUTO_FP": 0,
        "PERSISTENT_ODD_ODD": 0,
        "STAY_EVEN": 0,
        "NO_EVEN": 0,
    }
    stay_auto: list[int] = []
    persistent: list[int] = []
    odd_odd = 0
    for n in range(2, n_max + 1):
        if not is_odd_odd(n):
            continue
        odd_odd += 1
        cls = first_residual_class(n)
        counts[cls] = counts.get(cls, 0) + 1
        if cls == "STAY_AUTO_FP":
            stay_auto.append(n)
        elif cls == "PERSISTENT_ODD_ODD":
            persistent.append(n)
    return {
        "n_max": n_max,
        "odd_odd": odd_odd,
        "first_kinds": counts,
        "stay_auto_fp": stay_auto,
        "persistent_odd_odd": persistent,
        "propagating": counts["CAPTURE"] + counts["RETURN_BELOW"],
    }


def lean_api_present() -> dict[str, bool]:
    text = LEAN_PATH.read_text(encoding="utf-8")
    frontier = FRONTIER_PATH.read_text(encoding="utf-8")
    progress = PROGRESS_PATH.read_text(encoding="utf-8")
    corpus = juggler_text()
    floor = engine_floor_text()
    minimum = MIN_PATH.read_text(encoding="utf-8")
    combined = text + frontier + progress + corpus + minimum
    named = {}
    for name in LEAN_THEOREMS:
        if name in {"ResidualStep", "PersistentOddResidual", "ResidualChain"}:
            named[name] = f"def {name}" in text or f"inductive {name}" in text
        else:
            named[name] = f"theorem {name}" in text
    return {
        "sorry_free": "sorry" not in combined and "admit" not in combined,
        **named,
        "certificate_present": all(
            (has_named(combined, name))
            for name in CERTIFICATE_UNCHANGED
        ),
        "ReturnBelow_distinct": "def ReturnBelow" in frontier
        and "inductive DescentCertificate" in corpus
        and "inductive DescentCertificate" in corpus
        and "def ReachesOne" in corpus,
        "PowerHeight_absent": "PowerHeight" not in combined,
        "no_global_termination_theorem": "theorem juggler_reaches_one" not in combined,
        "no_finiteProgress_propagation": "theorem finiteProgress_of_residual_finiteProgress"
        not in text
        and "theorem finiteProgress_of_residualStep" not in text,
        "no_infinite_path_type": "coinductive" not in text.lower()
        and "def InfinitePath" not in text,
        "no_frequency_theorem": "theorem odd_run_frequency" not in text,
        "no_cycle_engine": "def CycleSearch" not in text,
        "FloorPower_not_rewritten": "ResidualStep" not in floor
        and "PersistentOddResidual" not in floor,
        "Progress_unchanged": "ResidualStep" not in progress
        and "PersistentOddResidual" not in progress,
        "MinimalNonTerm_unchanged": "ResidualStep" not in minimum,
    }


def classify(census: dict[str, Any], lean: dict[str, bool]) -> dict[str, Any]:
    lean_ok = (
        lean["sorry_free"]
        and lean["ResidualStep"]
        and lean["reachesOne_of_residualStep"]
        and lean["finiteProgress_of_residual_returnBelow"]
        and lean["residual_descent_not_below"]
        and lean["PersistentOddResidual"]
        and lean["minimal_residual_scale"]
        and lean["ResidualChain"]
        and lean["no_global_termination_theorem"]
        and lean["no_finiteProgress_propagation"]
        and lean["FloorPower_not_rewritten"]
        and lean["Progress_unchanged"]
    )
    if not lean_ok:
        return {"classification": CLASS_INCOMPLETE, "reason": f"lean_ok={lean_ok}"}
    if not census["persistent_odd_odd"] and not census["stay_auto_fp"]:
        return {
            "classification": CLASS_CLOSURE,
            "reason": "window has no leftover residual; do not promote a general closure",
        }
    return {
        "classification": CLASS_GREEN,
        "secondary": [],
        "reason": (
            "residual steps compose ReachesOne, Capture, and ReturnBelow; "
            "Descent at y with image ≥ n is not Descent at n; persistent "
            f"odd-odd leftovers {census['persistent_odd_odd']}; automatic "
            f"FiniteProgress stay {census['stay_auto_fp']}"
        ),
    }


def run_probe() -> dict[str, Any]:
    return {
        "census": residual_census(),
        "hard": [{"n": n, "chain": residual_chain(n)} for n in HARD_PROBES],
        "basin": [1],
    }


def probe_payload() -> dict[str, Any]:
    scan = run_probe()
    lean = lean_api_present()
    decision = classify(scan["census"], lean)
    anti = dict(ANTI_OVERCLAIM)
    anti["all_odd_orbit"] = False
    anti["finite_progress_for_all"] = False
    anti["finite_progress_propagates"] = False
    anti["residual_descent_is_progress"] = False
    anti["uniform_residual_horizon"] = False
    anti["overshoot_is_progress"] = False
    return {
        "experiment": "juggler_residual_chain",
        "engine_control_layer_modified": False,
        "anti_overclaim": anti,
        "scan": scan,
        "lean": lean,
        "decision": decision,
        "search_method": (
            "odd-odd starts; first O^a E^b residual class; hard residual "
            "chains; no FiniteProgress(y)⇒FiniteProgress(n) theorem"
        ),
    }


def render_markdown(payload: dict[str, Any]) -> str:
    decision = payload["decision"]
    scan = payload["scan"]
    lean = payload["lean"]
    census = scan["census"]
    lines = [
        "# Juggler residual-chain certificate propagation",
        "",
        f"Status: **{decision['classification']}**",
        "",
        "Standalone application phase. Not a Research Engine experiment",
        "and not a termination theorem. A residual step is one realized",
        "`O^a E^b` excursion. ReachesOne, Capture, and ReturnBelow",
        "propagate backward. Residual Descent need not.",
        "",
        "## Branch budget",
        "",
        "```text",
        "Mathematical target     which residual certificates propagate, and which leftover is recursive",
        "Novelty hypothesis      Descent at y with image ≥ n is not progress at n; persistent odd-odd is a subclass",
        "Falsifier               FiniteProgress(y) ⇒ FiniteProgress(n); or every stay residual is odd-odd",
        "Existing machinery      reachesOne_of_image, capture_of_suffix, ReturnBelow, oddEvenBlock",
        "Maximum Phase-0 scope   ResidualStep; compose/non-compose; PersistentOddResidual; hard-chain census",
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
        "## First residual census",
        "",
        f"- odd-odd starts: `{census['odd_odd']}`",
        f"- first residual kinds: `{census['first_kinds']}`",
        f"- propagating (Capture or ReturnBelow): `{census['propagating']}`",
        f"- stay with automatic FiniteProgress: `{census['stay_auto_fp']}`",
        f"- persistent odd-odd: `{census['persistent_odd_odd']}`",
        "",
        "## Hard residual chains",
        "",
    ]
    for item in scan["hard"]:
        lines.append(f"### n = {item['n']}")
        lines.append("")
        for row in item["chain"]:
            lines.append(
                f"- x=`{row['x']}` O^{row['a']}E^{row['b']} z=`{row['z']}` "
                f"y=`{row['y']}` bucket=`{row['y_bucket']}` vs_n=`{row['vs_n']}` "
                f"kind=`{row['kind']}` persistent=`{row['persistent']}`"
            )
        lines.append("")
    lines.extend(["## Lean", ""])
    for name in LEAN_THEOREMS:
        lines.append(f"- `{name}`: `{lean.get(name)}`")
    lines.extend(
        [
            f"- certificate unchanged: `{lean.get('certificate_present')}`",
            f"- ReturnBelow distinct: `{lean.get('ReturnBelow_distinct')}`",
            f"- `PowerHeight` absent: `{lean.get('PowerHeight_absent')}`",
            f"- FloorPower not rewritten: `{lean.get('FloorPower_not_rewritten')}`",
            f"- Progress unchanged: `{lean.get('Progress_unchanged')}`",
            f"- MinimalNonTerm unchanged: `{lean.get('MinimalNonTerm_unchanged')}`",
            f"- no FiniteProgress propagation theorem: `{lean.get('no_finiteProgress_propagation')}`",
            f"- no cycle engine: `{lean.get('no_cycle_engine')}`",
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
            "This is not a halt result. FiniteProgress at a residual is not",
            "FiniteProgress at the start. There is no uniform residual horizon.",
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
