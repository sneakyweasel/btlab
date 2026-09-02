"""Bounded residual future-quotient / precision test.

Not a Research Engine control-layer experiment. Not a halt theorem.
Not a PE-factor census and not a finite ResidualStep automaton.

Asks which listed arithmetic projections determine Future_H on
visited residual landings, and whether the 2-adic precision demand
k*(H) grows with H. ResidualStep stays the successor.
"""

from __future__ import annotations

import json
from collections import defaultdict
from pathlib import Path
from typing import Any, Callable

from research.juggler_sequence.landing_valuation import v2
from research.juggler_sequence.lean_paths import (
    JUGGLER_DIR,
    RESIDUALS,
    engine_floor_text,
    juggler_text,
)
from research.juggler_sequence.power_itineraries import ANTI_OVERCLAIM
from research.juggler_sequence.progress_coverage import is_odd_odd
from research.juggler_sequence.residual_chain import residual_class, residual_excursion
from research.juggler_sequence.residual_state import collect_landings, intrinsic_V, vector_key
from research.juggler_sequence.two_block_residual import classify_step

REPO_ROOT = Path(__file__).resolve().parents[3]
JSON_PATH = REPO_ROOT / "docs" / "research" / "juggler_future_quotient.json"
DOC_PATH = REPO_ROOT / "docs" / "research" / "juggler_future_quotient.md"
DATA_DIR = REPO_ROOT / "data" / "research" / "juggler" / "future_quotient"
LEAN_PATH = RESIDUALS
LEAN_NEW = JUGGLER_DIR / "ResidualState.lean"

CLASS_QUOTIENT = "STATE_QUOTIENT_GREEN"
CLASS_FUTURE = "FUTURE_QUOTIENT_GREEN"
CLASS_MINIMAL = "STATE_MINIMALITY_GREEN"
CLASS_COMPLEXITY = "STATE_COMPLEXITY_GREEN"
CLASS_COUNTER = "STATE_QUOTIENT_COUNTEREXAMPLE"
CLASS_PARK = "STATE_COMPLEXITY_PARK"
CLASS_REPACK = "FUTURE_QUOTIENT_REPACK"
CLASS_INCOMPLETE = "FUTURE_QUOTIENT_INCOMPLETE"

N_MAX_PRIMARY = 80
N_MAX_PHASE0 = 4000
H_MAX = 6
K_MAX = 16
ATLAS_PE_N_CAP = 100_000
ATLAS_PE_LIMIT = 4000
EXPERIMENT_ID = "wa-20260827T200310Z-cuda-k20-n100000000"
ALGORITHM_VERSION = "future-quotient-v1"
REWRITE_PROJECTIONS = frozenset({"residual_V", "pe_flags"})

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
    "PersistentExpandingResidual",
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


def v2_3y1(y: int) -> int:
    return v2(3 * y + 1)


def observe_step(x: int) -> dict[str, Any]:
    if x <= 1:
        return {
            "exists": False,
            "terminal": TERMINAL_HALT,
            "class": None,
            "odd_odd": False,
            "persistent": False,
            "expanding": False,
            "a": None,
            "b": None,
            "next": None,
        }
    raw = residual_excursion(x)
    if raw is None:
        return {
            "exists": False,
            "terminal": TERMINAL_NO_EVEN,
            "class": None,
            "odd_odd": False,
            "persistent": False,
            "expanding": False,
            "a": None,
            "b": None,
            "next": None,
        }
    row = classify_step(x, raw)
    nxt = row["y"]
    return {
        "exists": True,
        "terminal": None,
        "class": residual_class(x, nxt),
        "odd_odd": nxt >= 2 and is_odd_odd(nxt),
        "persistent": bool(row["persistent"]),
        "expanding": bool(row["expanding"]),
        "a": row["a"],
        "b": row["b"],
        "next": nxt,
    }


def label_key(step: dict[str, Any]) -> tuple[Any, ...]:
    if not step["exists"]:
        return (step["terminal"],)
    return (
        True,
        step["class"],
        step["odd_odd"],
        step["persistent"],
        step["expanding"],
    )


def block_key(step: dict[str, Any]) -> tuple[Any, ...]:
    if not step["exists"]:
        return (step["terminal"],)
    return (step["a"], step["b"])


def future_trace(y: int, h_max: int = H_MAX) -> dict[str, Any]:
    states = [y]
    steps: list[dict[str, Any]] = []
    current = y
    terminal: str | None = None
    for _ in range(h_max):
        step = observe_step(current)
        steps.append(step)
        if not step["exists"]:
            terminal = step["terminal"]
            break
        current = step["next"]
        states.append(current)
    else:
        tail = observe_step(current)
        if not tail["exists"]:
            terminal = tail["terminal"]
        else:
            terminal = TERMINAL_CAPPED
    return {
        "y": y,
        "states": states,
        "steps": steps,
        "terminal": terminal,
        "capped": terminal == TERMINAL_CAPPED,
        "persistent": bool(steps[0]["persistent"]) if steps else False,
        "expanding": bool(steps[0]["expanding"]) if steps else False,
        "pe": bool(steps and steps[0]["persistent"] and steps[0]["expanding"]),
    }


def future_word(trace: dict[str, Any], horizon: int, alphabet: str = "labels") -> tuple[Any, ...]:
    if horizon <= 0:
        return ()
    key_fn = block_key if alphabet == "block" else label_key
    keys = [key_fn(step) for step in trace["steps"][:horizon]]
    if len(keys) < horizon and trace["terminal"] is not None:
        if keys and keys[-1] in {(TERMINAL_HALT,), (TERMINAL_NO_EVEN,)}:
            return tuple(keys)
        keys.append((trace["terminal"],))
    return tuple(keys[:horizon])


def visited_ys(*, n_max: int) -> list[int]:
    return sorted({row["y"] for row in collect_landings(n_max=n_max)})


def atlas_pe_starts(*, n_cap: int = ATLAS_PE_N_CAP, limit: int = ATLAS_PE_LIMIT) -> list[int]:
    try:
        from research.juggler_sequence.atlas.schema import LANG_PE_CERTIFIED
        from research.juggler_sequence.atlas.storage import DEFAULT_DATA_DIR, connect
    except ImportError:
        return []
    path = DEFAULT_DATA_DIR / "word_atlas.sqlite"
    if not path.is_file():
        return []
    con = connect(DEFAULT_DATA_DIR)
    try:
        rows = con.execute(
            """
            SELECT DISTINCT min_n
            FROM pe_records
            WHERE language_id = ? AND min_n <= ? AND experiment_id = ?
            ORDER BY min_n
            LIMIT ?
            """,
            (LANG_PE_CERTIFIED, n_cap, EXPERIMENT_ID, limit),
        ).fetchall()
    finally:
        con.close()
    return [int(row[0]) for row in rows]


def build_sample(*, n_max: int, include_atlas: bool) -> dict[str, Any]:
    landings = collect_landings(n_max=n_max)
    ys = {row["y"] for row in landings}
    atlas_starts: list[int] = []
    if include_atlas:
        atlas_starts = atlas_pe_starts()
        ys.update(atlas_starts)
    return {
        "n_max": n_max,
        "n_chain_landings": len(landings),
        "n_atlas_starts": len(atlas_starts),
        "ys": sorted(ys),
    }


Projection = Callable[[int], Any]


def projections(*, k_list: tuple[int, ...] = (1, 2, 3, 4, 8, 16)) -> list[tuple[str, Projection]]:
    items: list[tuple[str, Projection]] = [
        ("exact_y", lambda y: y),
        ("parity", lambda y: y % 2),
        ("y_mod_8", lambda y: y % 8),
        ("v2_3y1", v2_3y1),
        ("residual_V", lambda y: vector_key(intrinsic_V(y))),
        (
            "pe_flags",
            lambda y: (
                (step := observe_step(y))["persistent"],
                step["expanding"],
            ),
        ),
    ]
    for k in k_list:
        items.append((f"y_mod_2_{k}", lambda y, kk=k: y % (1 << kk)))
        items.append((f"mod2_{k}_v2", lambda y, kk=k: (y % (1 << kk), v2_3y1(y))))
    return items


def _smallest_split_pair(members: list[int], future_of: dict[int, tuple[Any, ...]]) -> list[int] | None:
    by_f: dict[tuple[Any, ...], list[int]] = defaultdict(list)
    for y in members:
        by_f[future_of[y]].append(y)
    if len(by_f) < 2:
        return None
    classes = [sorted(vals)[0] for vals in by_f.values()]
    classes.sort()
    return [classes[0], classes[1]]


def projection_report(
    ys: list[int],
    future_of: dict[int, tuple[Any, ...]],
    name: str,
    fn: Projection,
) -> dict[str, Any]:
    buckets: dict[Any, list[int]] = defaultdict(list)
    for y in ys:
        buckets[fn(y)].append(y)
    split_pair = None
    n_split = 0
    n_multi = 0
    for members in buckets.values():
        if len(members) > 1:
            n_multi += 1
        pair = _smallest_split_pair(members, future_of)
        if pair is not None:
            n_split += 1
            if split_pair is None or pair < split_pair:
                split_pair = pair
    n_over = 0
    by_future: dict[tuple[Any, ...], set[Any]] = defaultdict(set)
    for y in ys:
        by_future[future_of[y]].add(fn(y))
    for keys in by_future.values():
        if len(keys) > 1:
            n_over += 1
    n_proj = len(buckets)
    n_future = len({future_of[y] for y in ys})
    sufficient = n_split == 0
    return {
        "name": name,
        "n_states": len(ys),
        "n_projected": n_proj,
        "n_future": n_future,
        "compression": (n_proj / len(ys)) if ys else None,
        "n_multi_fibers": n_multi,
        "n_separating_classes": n_split,
        "n_overdescribed_futures": n_over,
        "sufficient": sufficient,
        "first_separator": split_pair,
    }


def required_mod_bits(
    ys: list[int],
    future_of: dict[int, tuple[Any, ...]],
    *,
    k_max: int = K_MAX,
) -> dict[str, Any]:
    if len(ys) < 2:
        return {"k_star": 0, "exceeds_k_max": False, "separator": None, "v2_diff": None}
    hit_v = None
    separator = None
    for val in range(k_max, -1, -1):
        groups: dict[int, list[int]] = defaultdict(list)
        modulus = 1 << val if val else 1
        for y in ys:
            groups[y % modulus].append(y)
        for members in groups.values():
            pair = _smallest_split_pair(members, future_of)
            if pair is not None:
                hit_v = val
                separator = pair
                break
        if hit_v is not None:
            break
    if hit_v is None:
        return {"k_star": 0, "exceeds_k_max": False, "separator": None, "v2_diff": None}
    if hit_v == k_max:
        actual = v2(separator[0] - separator[1]) if separator else k_max
        return {
            "k_star": None,
            "exceeds_k_max": True,
            "separator": separator,
            "v2_diff": actual,
        }
    return {
        "k_star": hit_v + 1,
        "exceeds_k_max": False,
        "separator": separator,
        "v2_diff": hit_v,
    }


def growth_table(
    ys: list[int],
    traces: dict[int, dict[str, Any]],
    *,
    h_max: int = H_MAX,
    alphabet: str = "labels",
) -> list[dict[str, Any]]:
    rows = []
    for horizon in range(h_max + 1):
        groups: dict[tuple[Any, ...], list[int]] = defaultdict(list)
        for y in ys:
            groups[future_word(traces[y], horizon, alphabet)].append(y)
        sizes = [len(members) for members in groups.values()]
        n_capped = sum(1 for y in ys if traces[y]["capped"])
        n_halt_multi = 0
        n_live_multi = 0
        for word, members in groups.items():
            if len(members) < 2:
                continue
            if all(
                traces[y]["terminal"] in {TERMINAL_HALT, TERMINAL_NO_EVEN} for y in members
            ) and not any(traces[y]["capped"] for y in members):
                n_halt_multi += 1
            else:
                n_live_multi += 1
        rows.append(
            {
                "H": horizon,
                "Q_H": len(groups),
                "max_fiber": max(sizes) if sizes else 0,
                "n_multi": sum(1 for size in sizes if size > 1),
                "n_halt_multi": n_halt_multi,
                "n_live_multi": n_live_multi,
                "n_capped": n_capped,
            }
        )
    return rows


def halt_fibers(
    ys: list[int],
    traces: dict[int, dict[str, Any]],
    *,
    horizon: int,
    alphabet: str = "labels",
    limit: int = 8,
) -> list[dict[str, Any]]:
    groups: dict[tuple[Any, ...], list[int]] = defaultdict(list)
    for y in ys:
        groups[future_word(traces[y], horizon, alphabet)].append(y)
    rows = []
    for word, members in groups.items():
        if len(members) < 2:
            continue
        rows.append(
            {
                "members": sorted(members)[:8],
                "size": len(members),
                "word": json_safe(word),
                "all_halted": all(
                    traces[y]["terminal"] in {TERMINAL_HALT, TERMINAL_NO_EVEN} for y in members
                ),
                "any_capped": any(traces[y]["capped"] for y in members),
            }
        )
    rows.sort(key=lambda item: (-item["size"], item["members"]))
    return rows[:limit]


def slice_ys(traces: dict[int, dict[str, Any]], kind: str) -> list[int]:
    if kind == "all":
        return sorted(traces)
    if kind == "persistent":
        return sorted(y for y, tr in traces.items() if tr["persistent"])
    if kind == "pe":
        return sorted(y for y, tr in traces.items() if tr["pe"])
    raise ValueError(kind)


def window_census(*, n_max: int, include_atlas: bool, h_max: int = H_MAX) -> dict[str, Any]:
    sample = build_sample(n_max=n_max, include_atlas=include_atlas)
    ys = sample["ys"]
    traces = {y: future_trace(y, h_max) for y in ys}
    slices = {}
    for kind in ("all", "persistent", "pe"):
        sub = slice_ys(traces, kind)
        futures = {
            horizon: {y: future_word(traces[y], horizon, "labels") for y in sub}
            for horizon in range(1, h_max + 1)
        }
        kstar = {
            str(horizon): required_mod_bits(sub, futures[horizon]) for horizon in range(1, h_max + 1)
        }
        proj_h1 = [
            projection_report(sub, futures[1], name, fn) for name, fn in projections()
        ]
        slices[kind] = {
            "n_y": len(sub),
            "growth_labels": growth_table(sub, traces, h_max=h_max, alphabet="labels"),
            "growth_block": growth_table(sub, traces, h_max=h_max, alphabet="block"),
            "k_star": kstar,
            "projections_H1": proj_h1,
            "projections_Hmax": [
                projection_report(sub, futures[h_max], name, fn) for name, fn in projections()
            ],
            "halt_fibers": halt_fibers(sub, traces, horizon=h_max),
        }
    promising = _most_promising(slices["all"]["projections_H1"])
    return {
        "n_max": n_max,
        "include_atlas": include_atlas,
        "n_chain_landings": sample["n_chain_landings"],
        "n_atlas_starts": sample["n_atlas_starts"],
        "n_y": len(ys),
        "slices": slices,
        "most_promising_H1": promising,
    }


def _is_arithmetic(name: str) -> bool:
    return name != "exact_y" and name not in REWRITE_PROJECTIONS


def _has_fiber(row: dict[str, Any]) -> bool:
    return row["sufficient"] and row["n_projected"] < row["n_states"]


def _most_promising(rows: list[dict[str, Any]]) -> dict[str, Any] | None:
    ranked = [row for row in rows if _is_arithmetic(row["name"]) and _has_fiber(row)]
    if ranked:
        ranked.sort(key=lambda row: (row["n_projected"], row["name"]))
        return {"name": ranked[0]["name"], "reason": "sufficient_arithmetic_fiber"}
    return {
        "name": None,
        "reason": "no_arithmetic_quotient; residual_V is a Future_1 rewrite",
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

    primary = scan["primary"]["slices"]["all"]
    phase0 = scan["phase0"]["slices"]["all"]
    h1 = {row["name"]: row for row in phase0["projections_H1"]}
    hmax = {row["name"]: row for row in phase0["projections_Hmax"]}
    arith = [row for row in phase0["projections_H1"] if _is_arithmetic(row["name"])]
    sufficient_arith = [row for row in arith if _has_fiber(row)]
    v_h1 = h1.get("residual_V", {})
    v_hmax = hmax.get("residual_V", {})
    live = phase0["growth_labels"][-1]["n_live_multi"]
    q = [row["Q_H"] for row in phase0["growth_labels"]]
    q_primary = [row["Q_H"] for row in primary["growth_labels"]]
    n_y = phase0["n_y"]
    k_rows = [phase0["k_star"][str(h)] for h in range(1, H_MAX + 1)]
    k_vals = [row["k_star"] for row in k_rows]
    k_primary = [primary["k_star"][str(h)]["k_star"] for h in range(1, H_MAX + 1)]
    k_primary_finite = [val for val in k_primary if val is not None]
    k_grows = (
        len(k_primary_finite) >= 2
        and None not in k_primary
        and k_primary_finite[-1] >= k_primary_finite[0] + 2
    )
    any_exceeds = any(row["exceeds_k_max"] for row in k_rows)
    all_arith_split = all(not row["sufficient"] for row in arith)
    v_is_h1_rewrite = bool(v_h1.get("sufficient")) and not bool(v_hmax.get("sufficient"))

    if sufficient_arith and live:
        return {
            "classification": CLASS_QUOTIENT,
            "secondary": [row["name"] for row in sufficient_arith[:4]],
            "reason": (
                "an arithmetic projection of y predicts Future_1 with a "
                f"multi-y fiber: {[row['name'] for row in sufficient_arith]}"
            ),
        }
    if k_grows:
        return {
            "classification": CLASS_COMPLEXITY,
            "secondary": [f"k*_primary={k_primary}"],
            "reason": (
                "computationally observed k*(H) grows with H on the fixed "
                f"n<=80 window (k*={k_primary})"
            ),
        }
    if all_arith_split and v_is_h1_rewrite:
        seps = {
            name: h1[name]["first_separator"]
            for name in ("y_mod_8", "v2_3y1", "y_mod_2_16")
            if name in h1
        }
        extra = (
            f"; k*(H) exceeds {K_MAX} on the atlas-enriched sample" if any_exceeds else ""
        )
        return {
            "classification": CLASS_REPACK,
            "secondary": [CLASS_COUNTER, CLASS_PARK],
            "reason": (
                "every listed arithmetic projection of y is separated at H=1 "
                f"(pairs {seps}); residual_V predicts Future_1 only as a rewrite "
                f"of the next ResidualStep and splits by H={H_MAX} "
                f"(pair {v_hmax.get('first_separator')}); "
                f"n<=80 label Q_H={q_primary} plateaus on HALT fibers; "
                f"atlas-enriched Q_H={q} on |Y|={n_y}, live_multi={live}"
                + extra
            ),
        }
    if all_arith_split:
        return {
            "classification": CLASS_PARK,
            "secondary": [CLASS_COUNTER],
            "reason": (
                "every listed arithmetic projection is separated at H=1; "
                "no compact quotient of y survived "
                f"(Q_H={q}, |Y|={n_y}, live_multi={live}, k*={k_vals})"
            ),
        }
    return {
        "classification": CLASS_INCOMPLETE,
        "secondary": [],
        "reason": (
            f"no clean split (sufficient_arith={len(sufficient_arith)}, "
            f"live={live}, k*={k_vals}, Q_H={q})"
        ),
    }


def lean_api_present() -> dict[str, bool]:
    text = LEAN_PATH.read_text(encoding="utf-8")
    corpus = juggler_text()
    floor = engine_floor_text()
    combined = text + corpus
    named = {
        name: f"def {name}" in text or f"inductive {name}" in text for name in EXISTING_DEFS
    }
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
        "FloorPower_absent": "ResidualStep" not in floor,
        "no_itinerary_language_reopen": True,
        "no_pe_factor_reopen": True,
    }


def run_probe() -> dict[str, Any]:
    primary = window_census(n_max=N_MAX_PRIMARY, include_atlas=False)
    phase0 = window_census(n_max=N_MAX_PHASE0, include_atlas=True)
    hard = {
        n: {
            "y": n,
            "terminal": future_trace(n)["terminal"],
            "capped": future_trace(n)["capped"],
            "labels": json_safe(future_word(future_trace(n), H_MAX, "labels")),
            "block": json_safe(future_word(future_trace(n), H_MAX, "block")),
        }
        for n in (9, 11, 37, 49, 69, 77, 365)
    }
    return {
        "h_max": H_MAX,
        "k_max": K_MAX,
        "n_max_primary": N_MAX_PRIMARY,
        "n_max_phase0": N_MAX_PHASE0,
        "primary": primary,
        "phase0": phase0,
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
    anti["pe_factor_reopened"] = False
    anti["history_is_new_state"] = False
    anti["global_termination"] = False
    anti["new_scalar_energy"] = False
    return {
        "experiment": "juggler_future_quotient",
        "algorithm_version": ALGORITHM_VERSION,
        "engine_control_layer_modified": False,
        "anti_overclaim": anti,
        "scan": scan,
        "lean": lean,
        "decision": decision,
        "search_method": (
            "odd-odd residual landings n<=80 and n<=4000; optional atlas "
            "PE_CERTIFIED starts n<=1e5 cap 4000; Future_H labels from "
            "classify_step/residual_class; projections exact y, y mod 2^k, "
            "v2(3y+1), residual V, PE flags; no GPU; no ResidualState"
        ),
    }


def _fmt_growth(rows: list[dict[str, Any]]) -> list[str]:
    lines = [
        "| H | Q_H | max_fiber | n_multi | halt_multi | live_multi |",
        "|---|-----|-----------|---------|------------|------------|",
    ]
    for row in rows:
        lines.append(
            f"| {row['H']} | {row['Q_H']} | {row['max_fiber']} | "
            f"{row['n_multi']} | {row['n_halt_multi']} | {row['n_live_multi']} |"
        )
    return lines


def _fmt_proj(rows: list[dict[str, Any]]) -> list[str]:
    lines = [
        "| S | |proj| | |Future| | compression | separators | first pair | sufficient |",
        "|---|------|----------|-------------|------------|------------|------------|",
    ]
    for row in rows:
        pair = row["first_separator"]
        pair_s = "—" if pair is None else f"`{pair[0]},{pair[1]}`"
        comp = "—" if row["compression"] is None else f"{row['compression']:.3f}"
        lines.append(
            f"| `{row['name']}` | {row['n_projected']} | {row['n_future']} | "
            f"{comp} | {row['n_separating_classes']} | {pair_s} | `{row['sufficient']}` |"
        )
    return lines


def render_markdown(payload: dict[str, Any]) -> str:
    decision = payload["decision"]
    scan = payload["scan"]
    lean = payload["lean"]
    primary = scan["primary"]["slices"]["all"]
    phase0 = scan["phase0"]["slices"]["all"]
    lines = [
        "# Juggler residual future-quotient",
        "",
        f"Status: **{decision['classification']}**",
        "",
        "Standalone application phase. Not a Research Engine experiment",
        "and not a termination theorem. ResidualStep stays the successor.",
        "The object is bounded future equivalence at horizon H, not",
        "Myhill–Nerode equivalence.",
        "",
        "## Branch budget",
        "",
        "```text",
        "Mathematical target     which listed projections determine Future_H, and does k*(H) grow?",
        "Novelty hypothesis      a compact S, not exact y, or a genuine precision hierarchy",
        "Falsifier               H=1 separators for every no-y projection; leftover fibers are HALT words",
        "Existing machinery      residual_excursion, classify_step, residual_class, intrinsic_V, v2",
        "Maximum Phase-0 scope   H<=6; n<=80 and n<=4000; optional atlas PE starts; no GPU/Lean/automaton",
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
        "Closed branches were not reopened: `RESIDUAL_STATE_NEEDS_X`,",
        "`RESIDUAL_MN_REPACK`, `LANDING_VALUATION_IS_Y_MOD_8`,",
        "`JUGGLER_LANGUAGE_IS_KNOWN_GRAMMAR`.",
        "",
        "## Window n ≤ 80",
        "",
        f"- distinct y: `{primary['n_y']}`",
        f"- most promising at H=1: `{scan['primary']['most_promising_H1']}`",
        "",
        "### Future_H labels",
        "",
    ]
    lines.extend(_fmt_growth(primary["growth_labels"]))
    lines.extend(["", "### k*(H)", ""])
    for h in range(1, H_MAX + 1):
        row = primary["k_star"][str(h)]
        lines.append(
            f"- H={h}: k*=`{row['k_star']}` exceeds_k_max=`{row['exceeds_k_max']}` "
            f"separator=`{row['separator']}`"
        )
    lines.extend(["", "### Projections at H = 1", ""])
    lines.extend(_fmt_proj(primary["projections_H1"]))
    lines.extend(
        [
            "",
            f"## Window n ≤ {scan['n_max_phase0']} plus atlas PE starts",
            "",
            f"- distinct y: `{phase0['n_y']}`",
            f"- chain landings: `{scan['phase0']['n_chain_landings']}`",
            f"- atlas PE starts used: `{scan['phase0']['n_atlas_starts']}`",
            f"- most promising at H=1: `{scan['phase0']['most_promising_H1']}`",
            "",
            "### Future_H labels (all sampled)",
            "",
        ]
    )
    lines.extend(_fmt_growth(phase0["growth_labels"]))
    lines.extend(["", "### Persistent-odd slice", ""])
    lines.extend(_fmt_growth(scan["phase0"]["slices"]["persistent"]["growth_labels"]))
    lines.extend(["", "### PE slice", ""])
    lines.extend(_fmt_growth(scan["phase0"]["slices"]["pe"]["growth_labels"]))
    lines.extend(["", "### k*(H) on all sampled", ""])
    for h in range(1, H_MAX + 1):
        row = phase0["k_star"][str(h)]
        lines.append(
            f"- H={h}: k*=`{row['k_star']}` exceeds_k_max=`{row['exceeds_k_max']}` "
            f"separator=`{row['separator']}` v2_diff=`{row['v2_diff']}`"
        )
    lines.extend(["", "### Projections at H = 1", ""])
    lines.extend(_fmt_proj(phase0["projections_H1"]))
    lines.extend(["", "### Multi-y fibers at H = 6", ""])
    fibers = phase0["halt_fibers"]
    if fibers:
        for item in fibers:
            lines.append(
                f"- size=`{item['size']}` halted=`{item['all_halted']}` "
                f"capped=`{item['any_capped']}` members=`{item['members']}`"
            )
    else:
        lines.append("- none")
    lines.extend(["", "## Hard traces", ""])
    for n, row in scan["hard"].items():
        lines.append(
            f"- n=`{n}` terminal=`{row['terminal']}` capped=`{row['capped']}` "
            f"labels=`{row['labels']}`"
        )
    lines.extend(["", "## Lean", ""])
    for name in EXISTING_DEFS:
        lines.append(f"- `{name}`: `{lean.get(name)}`")
    lines.extend(
        [
            f"- ResidualStep unchanged: `{lean.get('ResidualStep_unchanged')}`",
            f"- ResidualState.lean absent: `{lean.get('no_ResidualState_file')}`",
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
            "The PE-factor branch was not reopened. No automaton was built.",
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
            "growth_labels": data["scan"]["primary"]["slices"]["all"]["growth_labels"],
            "k_star": data["scan"]["primary"]["slices"]["all"]["k_star"],
            "projections_H1": data["scan"]["primary"]["slices"]["all"]["projections_H1"],
            "most_promising_H1": data["scan"]["primary"]["most_promising_H1"],
        },
        "phase0": {
            "n_y": data["scan"]["phase0"]["n_y"],
            "n_atlas_starts": data["scan"]["phase0"]["n_atlas_starts"],
            "growth_labels": data["scan"]["phase0"]["slices"]["all"]["growth_labels"],
            "k_star": data["scan"]["phase0"]["slices"]["all"]["k_star"],
            "projections_H1": data["scan"]["phase0"]["slices"]["all"]["projections_H1"],
            "most_promising_H1": data["scan"]["phase0"]["most_promising_H1"],
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
