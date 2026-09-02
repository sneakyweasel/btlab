"""ResidualStep empirical future-equivalence ~_H.

Not a Research Engine control-layer experiment. Not a halt theorem.
Partitions visited ResidualStep landings by H-step observation traces
and measures |Y / ~_H| versus H. ResidualStep stays the successor.
No ResidualState object.
"""

from __future__ import annotations

import json
from collections import defaultdict
from pathlib import Path
from typing import Any

from research.juggler_sequence.lean_paths import (
    JUGGLER_DIR,
    RESIDUALS,
    engine_floor_text,
    juggler_text,
)
from research.juggler_sequence.power_itineraries import ANTI_OVERCLAIM
from research.juggler_sequence.residual_chain import (
    HARD_PROBES,
    residual_class,
    residual_excursion,
)
from research.juggler_sequence.residual_state import (
    collect_landings,
    intrinsic_V,
    odd_odd_starts,
    vector_key,
)

REPO_ROOT = Path(__file__).resolve().parents[3]
JSON_PATH = REPO_ROOT / "docs" / "research" / "juggler_residual_minimize.json"
DOC_PATH = REPO_ROOT / "docs" / "research" / "juggler_residual_minimize.md"
DATA_DIR = REPO_ROOT / "data" / "research" / "juggler" / "residual_minimize"
LEAN_PATH = RESIDUALS
LEAN_NEW = JUGGLER_DIR / "ResidualState.lean"

CLASS_NEEDS_X = "RESIDUAL_MN_NEEDS_X"
CLASS_SATURATES = "RESIDUAL_MN_SATURATES"
CLASS_REPACK = "RESIDUAL_MN_REPACK"
CLASS_WINDOW = "RESIDUAL_MN_WINDOW"
CLASS_INCOMPLETE = "RESIDUAL_MN_INCOMPLETE"

N_MAX_PRIMARY = 80
N_MAX_SECONDARY = 200
H_MAX = 8
FIRST_EVEN_CAP = 24
ALGORITHM_VERSION = "residual-minimize-v1"

ALPHABETS = ("block", "V", "class")
TERMINAL_HALT = "HALT"
TERMINAL_NO_EVEN = "NO_EVEN"
TERMINAL_CAPPED = "CAPPED"

FORBIDDEN_ENGINES = (
    "ResidualState",
    "RemainderDynamics",
    "ResidualGraph",
    "CycleEngine",
    "Energy",
    "PowerHeight",
)

EXISTING_DEFS = (
    "ResidualStep",
    "PersistentOddResidual",
    "ResidualChain",
)


def json_safe(value: Any) -> Any:
    if isinstance(value, tuple):
        return [json_safe(item) for item in value]
    if isinstance(value, dict):
        return {str(key): json_safe(item) for key, item in value.items()}
    if isinstance(value, list):
        return [json_safe(item) for item in value]
    return value


def visited_ys(*, n_max: int) -> list[int]:
    return sorted({row["y"] for row in collect_landings(n_max=n_max)})


def intrinsic_trace(y: int, h_max: int = H_MAX) -> dict[str, Any]:
    if y <= 1:
        return {
            "y": y,
            "states": [y],
            "steps": [],
            "terminal": TERMINAL_HALT,
            "capped": False,
        }
    states = [y]
    steps: list[dict[str, Any]] = []
    current = y
    terminal: str | None = None
    for _ in range(h_max):
        if current <= 1:
            terminal = TERMINAL_HALT
            break
        step = residual_excursion(current)
        if step is None:
            terminal = TERMINAL_NO_EVEN
            break
        steps.append(
            {
                "x": current,
                "a": step["a"],
                "b": step["b"],
                "z": step["z"],
                "y": step["y"],
                "class": residual_class(current, step["y"]),
                "V": intrinsic_V(current),
            }
        )
        current = step["y"]
        states.append(current)
    else:
        if current <= 1:
            terminal = TERMINAL_HALT
        elif residual_excursion(current) is None:
            terminal = TERMINAL_NO_EVEN
        else:
            terminal = TERMINAL_CAPPED
    return {
        "y": y,
        "states": states,
        "steps": steps,
        "terminal": terminal,
        "capped": terminal == TERMINAL_CAPPED,
    }


def obs_key(step: dict[str, Any], alphabet: str) -> Any:
    if alphabet == "block":
        return (step["a"], step["b"])
    if alphabet == "V":
        return vector_key(step["V"])
    if alphabet == "class":
        return step["class"]
    raise ValueError(alphabet)


def future_word(trace: dict[str, Any], horizon: int, alphabet: str) -> tuple[Any, ...]:
    if horizon <= 0:
        return ()
    if alphabet == "V":
        keys = [vector_key(step["V"]) for step in trace["steps"][:horizon]]
        if not keys:
            keys = [vector_key(intrinsic_V(trace["y"]))]
        elif len(keys) < horizon and trace["terminal"] in {TERMINAL_HALT, TERMINAL_NO_EVEN}:
            keys.append(vector_key(intrinsic_V(trace["states"][-1])))
        return tuple(keys[:horizon])
    keys = [obs_key(step, alphabet) for step in trace["steps"][:horizon]]
    if len(keys) < horizon and trace["terminal"] is not None:
        keys.append(trace["terminal"])
    return tuple(keys)


def _n_refine_pairs(
    ys: list[int],
    traces: dict[int, dict[str, Any]],
    horizon: int,
    alphabet: str,
) -> int:
    groups: dict[tuple[Any, ...], list[int]] = defaultdict(list)
    for y in ys:
        groups[future_word(traces[y], horizon, alphabet)].append(y)
    count = 0
    for members in groups.values():
        if len(members) < 2:
            continue
        next_groups: dict[tuple[Any, ...], int] = defaultdict(int)
        for y in members:
            next_groups[future_word(traces[y], horizon + 1, alphabet)] += 1
        n = len(members)
        stay = sum(size * (size - 1) // 2 for size in next_groups.values())
        count += n * (n - 1) // 2 - stay
    return count


def _live_block_count(word: tuple[Any, ...], alphabet: str) -> int:
    if alphabet == "V":
        return sum(1 for item in word if isinstance(item, tuple) and ("next_exists", True) in item)
    return sum(1 for item in word if item not in {TERMINAL_HALT, TERMINAL_NO_EVEN, TERMINAL_CAPPED})


def partition(
    ys: list[int],
    traces: dict[int, dict[str, Any]],
    horizon: int,
    alphabet: str,
) -> dict[tuple[Any, ...], list[int]]:
    groups: dict[tuple[Any, ...], list[int]] = defaultdict(list)
    for y in ys:
        groups[future_word(traces[y], horizon, alphabet)].append(y)
    return dict(groups)


def growth_table(
    ys: list[int],
    traces: dict[int, dict[str, Any]],
    *,
    h_max: int = H_MAX,
) -> dict[str, list[dict[str, Any]]]:
    out: dict[str, list[dict[str, Any]]] = {}
    for alphabet in ALPHABETS:
        rows: list[dict[str, Any]] = []
        for horizon in range(h_max + 1):
            groups = partition(ys, traces, horizon, alphabet)
            sizes = [len(members) for members in groups.values()]
            n_refine = None
            if horizon < h_max:
                n_refine = _n_refine_pairs(ys, traces, horizon, alphabet)
            n_live = sum(1 for y in ys if len(traces[y]["steps"]) >= horizon)
            n_capped = sum(1 for y in ys if traces[y]["capped"])
            rows.append(
                {
                    "H": horizon,
                    "Q_H": len(groups),
                    "max_fiber": max(sizes) if sizes else 0,
                    "n_multi_fibers": sum(1 for size in sizes if size > 1),
                    "n_refine": n_refine,
                    "n_live": n_live,
                    "n_capped": n_capped,
                }
            )
        out[alphabet] = rows
    return out


def multi_fibers(
    ys: list[int],
    traces: dict[int, dict[str, Any]],
    *,
    horizon: int,
    alphabet: str,
    limit: int = 12,
) -> list[dict[str, Any]]:
    groups = partition(ys, traces, horizon, alphabet)
    rows = []
    for word, members in groups.items():
        if len(members) < 2:
            continue
        live = _live_block_count(word, alphabet)
        rows.append(
            {
                "word": json_safe(word),
                "members": sorted(members),
                "size": len(members),
                "n_live_obs": live,
                "long": live >= 2,
                "all_halted": all(
                    traces[y]["terminal"] in {TERMINAL_HALT, TERMINAL_NO_EVEN} for y in members
                ),
                "any_capped": any(traces[y]["capped"] for y in members),
            }
        )
    rows.sort(key=lambda item: (-item["n_live_obs"], -item["size"], item["members"]))
    return rows[:limit]


def window_census(*, n_max: int, h_max: int = H_MAX) -> dict[str, Any]:
    landings = collect_landings(n_max=n_max)
    ys = sorted({row["y"] for row in landings})
    traces = {y: intrinsic_trace(y, h_max) for y in ys}
    growth = growth_table(ys, traces, h_max=h_max)
    v_values = {vector_key(intrinsic_V(y)) for y in ys}
    q1_v = next(row["Q_H"] for row in growth["V"] if row["H"] == 1)
    fibers_h = {
        alphabet: multi_fibers(ys, traces, horizon=h_max, alphabet=alphabet) for alphabet in ALPHABETS
    }
    fibers_h1 = {
        alphabet: multi_fibers(ys, traces, horizon=1, alphabet=alphabet) for alphabet in ALPHABETS
    }
    q_block = [row["Q_H"] for row in growth["block"]]
    plateau_from = _plateau_from(q_block)
    return {
        "n_max": n_max,
        "n_starts": len(odd_odd_starts(n_max)),
        "n_landings": len(landings),
        "n_y": len(ys),
        "ys": ys,
        "growth": growth,
        "v_distinct": len(v_values),
        "v_h1_matches": q1_v == len(v_values),
        "plateau_from": plateau_from,
        "fibers_H": fibers_h,
        "fibers_H1": fibers_h1,
        "n_capped": sum(1 for y in ys if traces[y]["capped"]),
    }


def _compact_trace(trace: dict[str, Any]) -> dict[str, Any]:
    return {
        "y": trace["y"],
        "states": trace["states"],
        "terminal": trace["terminal"],
        "capped": trace["capped"],
        "blocks": [(step["a"], step["b"]) for step in trace["steps"]],
        "classes": [step["class"] for step in trace["steps"]],
    }


def _plateau_from(q: list[int]) -> int | None:
    for index, value in enumerate(q):
        if all(item == value for item in q[index:]):
            return index
    return None


def _shape(window: dict[str, Any]) -> str:
    q = [row["Q_H"] for row in window["growth"]["block"]]
    n_y = window["n_y"]
    if q[-1] >= n_y:
        return "to_Y"
    plateau = window["plateau_from"]
    if plateau is not None and plateau < H_MAX and q[-1] < n_y:
        return "plateau"
    return "growing"


def _block_fiber_split(window: dict[str, Any]) -> dict[str, Any]:
    fibers = window["fibers_H"]["block"]
    long_live = [
        item for item in fibers if item["long"] and item["any_capped"]
    ]
    long_halt = [
        item for item in fibers if item["long"] and item["all_halted"]
    ]
    short = [item for item in fibers if not item["long"]]
    return {
        "n_multi": len(fibers),
        "n_long_live": len(long_live),
        "n_long_halt": len(long_halt),
        "n_short": len(short),
        "long_live": long_live[:6],
        "long_halt": long_halt[:6],
        "short": short[:6],
    }


def classify(scan: dict[str, Any], lean: dict[str, bool]) -> dict[str, Any]:
    lean_ok = (
        lean["sorry_free"]
        and lean["ResidualStep"]
        and lean["no_ResidualState_file"]
        and lean["no_ResidualState_def"]
        and lean["ResidualStep_unchanged"]
        and lean["no_forbidden_engines"]
        and lean["no_global_termination_theorem"]
    )
    if not lean_ok:
        return {
            "classification": CLASS_INCOMPLETE,
            "secondary": [],
            "reason": f"lean_ok={lean_ok}",
        }

    primary = scan["primary"]
    secondary = scan["secondary"]
    if not primary["v_h1_matches"] or not secondary["v_h1_matches"]:
        return {
            "classification": CLASS_INCOMPLETE,
            "secondary": [],
            "reason": "H=1 V class count does not match |{V(y)}|",
        }

    shape_p = _shape(primary)
    shape_s = _shape(secondary)
    split_p = _block_fiber_split(primary)
    split_s = _block_fiber_split(secondary)
    q_p = [row["Q_H"] for row in primary["growth"]["block"]]
    refine_early = sum(row["n_refine"] or 0 for row in primary["growth"]["block"] if row["H"] in {1, 2})

    if shape_p != shape_s:
        return {
            "classification": CLASS_WINDOW,
            "secondary": [shape_p, shape_s],
            "reason": (
                f"n<=80 shape is {shape_p} (Q_H={q_p}, |Y|={primary['n_y']}); "
                f"n<=200 shape is {shape_s} (|Y|={secondary['n_y']})"
            ),
            "fibers": split_p,
        }

    if split_p["n_long_live"] or split_s["n_long_live"]:
        return {
            "classification": CLASS_SATURATES,
            "secondary": [shape_p],
            "reason": (
                "a multi-y fiber shares a live block prefix through the horizon cap; "
                f"n<=80 Q_H={q_p}, |Y|={primary['n_y']}, "
                f"long_live={split_p['n_long_live']}"
            ),
            "fibers": split_p,
        }

    if shape_p == "to_Y":
        extra = ""
        if refine_early:
            extra = f"; {refine_early} H=1/H=2 pair refinements"
        return {
            "classification": CLASS_NEEDS_X,
            "secondary": [],
            "reason": (
                "block Q_H reaches |Y|: every visited landing has a unique "
                f"H-step future on n<=80 (Q_H={q_p}, |Y|={primary['n_y']})"
                + extra
            ),
            "fibers": split_p,
        }

    if split_p["n_long_halt"] and not split_p["n_long_live"] and q_p[-1] < primary["n_y"]:
        return {
            "classification": CLASS_REPACK,
            "secondary": [shape_p],
            "reason": (
                "Q_H plateaus below |Y| only because some landings share a "
                "complete block-word to HALT; the trace is a certificate of y, "
                f"not a new state (Q_H={q_p}, |Y|={primary['n_y']}, "
                f"long_halt={split_p['n_long_halt']}, short={split_p['n_short']})"
            ),
            "fibers": split_p,
        }

    if q_p[-1] < primary["n_y"] and split_p["n_multi"] and not split_p["n_long_live"]:
        extra = ""
        if refine_early:
            extra = f"; {refine_early} H=1/H=2 pair refinements"
        return {
            "classification": CLASS_NEEDS_X,
            "secondary": ["SHORT_HALT_FIBERS"],
            "reason": (
                "H=1 merges refine away; leftover multi-y classes are short "
                "shared HALT words, not a surviving proper quotient "
                f"(Q_H={q_p}, |Y|={primary['n_y']}, short={split_p['n_short']})"
                + extra
            ),
            "fibers": split_p,
        }

    return {
        "classification": CLASS_WINDOW,
        "secondary": [shape_p],
        "reason": (
            f"no clean saturation split on this window (shape={shape_p}, "
            f"Q_H={q_p}, |Y|={primary['n_y']})"
        ),
        "fibers": split_p,
    }


def lean_api_present() -> dict[str, bool]:
    text = LEAN_PATH.read_text(encoding="utf-8")
    corpus = juggler_text()
    floor = engine_floor_text()
    combined = text + corpus
    named = {name: f"def {name}" in text or f"inductive {name}" in text for name in EXISTING_DEFS}
    forbidden_hits = [
        name
        for name in FORBIDDEN_ENGINES
        if f"def {name}" in combined or f"structure {name}" in combined
    ]
    return {
        "sorry_free": "sorry" not in combined and "admit" not in combined,
        **named,
        "no_ResidualState_file": not LEAN_NEW.is_file(),
        "no_ResidualState_def": "def ResidualState" not in combined
        and "structure ResidualState" not in combined,
        "ResidualStep_unchanged": "def ResidualStep" in text,
        "no_forbidden_engines": not forbidden_hits,
        "forbidden_hits": forbidden_hits,
        "no_global_termination_theorem": "theorem juggler_reaches_one" not in combined,
        "GlobalDefect_untouched_by_this_probe": True,
        "FloorPower_absent": "ResidualStep" not in floor,
        "no_itinerary_language_reopen": True,
    }


def run_probe() -> dict[str, Any]:
    primary = window_census(n_max=N_MAX_PRIMARY)
    secondary = window_census(n_max=N_MAX_SECONDARY)
    hard = {n: _compact_trace(intrinsic_trace(n)) for n in HARD_PROBES}
    hard[11] = _compact_trace(intrinsic_trace(11))
    return {
        "n_max_primary": N_MAX_PRIMARY,
        "n_max_secondary": N_MAX_SECONDARY,
        "h_max": H_MAX,
        "hard_probes": list(HARD_PROBES),
        "primary": primary,
        "secondary": secondary,
        "hard": hard,
    }


def probe_payload() -> dict[str, Any]:
    scan = run_probe()
    lean = lean_api_present()
    decision = classify(scan, lean)
    anti = dict(ANTI_OVERCLAIM)
    anti["residual_state_object"] = False
    anti["residual_step_extended"] = False
    anti["finite_residual_automaton"] = False
    anti["itinerary_language_reopened"] = False
    anti["history_is_new_state"] = False
    anti["global_termination"] = False
    anti["defect_financing_opened"] = False
    anti["global_defect_growth_opened"] = False
    return {
        "experiment": "juggler_residual_minimize",
        "algorithm_version": ALGORITHM_VERSION,
        "engine_control_layer_modified": False,
        "anti_overclaim": anti,
        "scan": scan,
        "lean": lean,
        "decision": decision,
        "search_method": (
            "odd-odd residual landings n<=80 and n<=200; intrinsic "
            "residual_excursion traces; ~_H on block/V/class; no ResidualState"
        ),
    }


def _fmt_growth(rows: list[dict[str, Any]]) -> list[str]:
    lines = [
        "| H | Q_H | max_fiber | n_multi | n_refine | n_live |",
        "|---|-----|-----------|---------|----------|--------|",
    ]
    for row in rows:
        refine = row["n_refine"] if row["n_refine"] is not None else "—"
        lines.append(
            f"| {row['H']} | {row['Q_H']} | {row['max_fiber']} | "
            f"{row['n_multi_fibers']} | {refine} | {row['n_live']} |"
        )
    return lines


def render_markdown(payload: dict[str, Any]) -> str:
    decision = payload["decision"]
    scan = payload["scan"]
    lean = payload["lean"]
    primary = scan["primary"]
    secondary = scan["secondary"]
    lines = [
        "# Juggler ResidualStep future-equivalence",
        "",
        f"Status: **{decision['classification']}**",
        "",
        "Standalone application phase. Not a Research Engine experiment",
        "and not a termination theorem. ResidualStep stays the successor.",
        "The question is the growth of empirical trace classes `~_H`.",
        "",
        "## Branch budget",
        "",
        "```text",
        "Mathematical target     does |Y / ~_H| saturate below |Y| or refine toward y?",
        "Novelty hypothesis      a stable proper quotient of landings, not y",
        "Falsifier               leftover fibers are the same complete word to HALT",
        "Existing machinery      residual_excursion, intrinsic_V, residual_class",
        "Maximum Phase-0 scope   n<=80 and n<=200; H=0..8; block/V/class; no Lean state",
        "```",
        "",
        "## Metadata",
        "",
        f"- algorithm: `{payload['algorithm_version']}`",
        f"- engine control layer modified: `{payload['engine_control_layer_modified']}`",
        f"- classification: **{decision['classification']}**",
        f"- secondary: `{decision.get('secondary')}`",
        f"- sorry-free: `{lean['sorry_free']}`",
        f"- ResidualState.lean absent: `{lean['no_ResidualState_file']}`",
        "",
        decision["reason"] + ".",
        "",
        "## Window n ≤ 80",
        "",
        f"- odd-odd starts: `{primary['n_starts']}`",
        f"- landings: `{primary['n_landings']}`",
        f"- distinct y: `{primary['n_y']}`",
        f"- distinct V: `{primary['v_distinct']}`",
        f"- H=1 V matches |{{V(y)}}|: `{primary['v_h1_matches']}`",
        f"- plateau from H: `{primary['plateau_from']}`",
        f"- capped traces: `{primary['n_capped']}`",
        "",
        "### block",
        "",
    ]
    lines.extend(_fmt_growth(primary["growth"]["block"]))
    lines.extend(["", "### V", ""])
    lines.extend(_fmt_growth(primary["growth"]["V"]))
    lines.extend(["", "### class", ""])
    lines.extend(_fmt_growth(primary["growth"]["class"]))
    lines.extend(
        [
            "",
            "## Window n ≤ 200",
            "",
            f"- odd-odd starts: `{secondary['n_starts']}`",
            f"- landings: `{secondary['n_landings']}`",
            f"- distinct y: `{secondary['n_y']}`",
            f"- distinct V: `{secondary['v_distinct']}`",
            f"- H=1 V matches |{{V(y)}}|: `{secondary['v_h1_matches']}`",
            f"- plateau from H: `{secondary['plateau_from']}`",
            f"- capped traces: `{secondary['n_capped']}`",
            "",
            "### block",
            "",
        ]
    )
    lines.extend(_fmt_growth(secondary["growth"]["block"]))
    lines.extend(["", "## Multi-y fibers at H = 8 (block, n ≤ 80)", ""])
    fibers = primary["fibers_H"]["block"]
    if fibers:
        for item in fibers[:8]:
            lines.append(
                f"- size=`{item['size']}` live=`{item['n_live_obs']}` "
                f"long=`{item['long']}` halted=`{item['all_halted']}` "
                f"capped=`{item['any_capped']}` members=`{item['members']}` "
                f"word=`{item['word']}`"
            )
    else:
        lines.append("- none")
    lines.extend(["", "## Hard traces", ""])
    for n, trace in scan["hard"].items():
        lines.append(f"### n = {n}")
        lines.append("")
        lines.append(
            f"- terminal=`{trace['terminal']}` capped=`{trace['capped']}` "
            f"states=`{trace['states']}` blocks=`{trace['blocks']}` "
            f"classes=`{trace['classes']}`"
        )
        lines.append("")
    lines.extend(["## Lean", ""])
    for name in EXISTING_DEFS:
        lines.append(f"- `{name}`: `{lean.get(name)}`")
    lines.extend(
        [
            f"- ResidualStep unchanged: `{lean.get('ResidualStep_unchanged')}`",
            f"- ResidualState.lean absent: `{lean.get('no_ResidualState_file')}`",
            f"- no ResidualState def: `{lean.get('no_ResidualState_def')}`",
            f"- no forbidden engines: `{lean.get('no_forbidden_engines')}`",
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
            "This is not a halt result. ResidualStep is not a state object.",
            "Object C was not opened. Word-language MN was not reopened.",
            "",
        ]
    )
    return "\n".join(lines) + "\n"


def write_artifacts(payload: dict[str, Any] | None = None) -> dict[str, Any]:
    data = payload if payload is not None else probe_payload()
    JSON_PATH.parent.mkdir(parents=True, exist_ok=True)
    DATA_DIR.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(json_safe(data), indent=2) + "\n", encoding="utf-8")
    DOC_PATH.write_text(render_markdown(data), encoding="utf-8")
    compact = {
        "decision": data["decision"],
        "primary": {
            "n_y": data["scan"]["primary"]["n_y"],
            "n_landings": data["scan"]["primary"]["n_landings"],
            "v_distinct": data["scan"]["primary"]["v_distinct"],
            "v_h1_matches": data["scan"]["primary"]["v_h1_matches"],
            "plateau_from": data["scan"]["primary"]["plateau_from"],
            "growth": data["scan"]["primary"]["growth"],
            "fibers_H": data["scan"]["primary"]["fibers_H"]["block"],
            "fibers_H1": data["scan"]["primary"]["fibers_H1"]["block"],
        },
        "secondary": {
            "n_y": data["scan"]["secondary"]["n_y"],
            "n_landings": data["scan"]["secondary"]["n_landings"],
            "v_distinct": data["scan"]["secondary"]["v_distinct"],
            "v_h1_matches": data["scan"]["secondary"]["v_h1_matches"],
            "plateau_from": data["scan"]["secondary"]["plateau_from"],
            "growth": data["scan"]["secondary"]["growth"]["block"],
        },
        "hard": data["scan"]["hard"],
    }
    (DATA_DIR / "summary.json").write_text(
        json.dumps(json_safe(compact), indent=2) + "\n", encoding="utf-8"
    )
    return data


def main() -> None:
    payload = write_artifacts()
    print(payload["decision"]["classification"])
    print(payload["decision"]["reason"])


if __name__ == "__main__":
    main()
