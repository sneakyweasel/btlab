"""Landing-image geometry of the Juggler prefix trie.

Not a Research Engine control-layer experiment. Not a halt theorem.
Does not reopen PE-factor, residual-future, summed-rho, or R_w-as-branching
explanations. d(w) = parity support of Y_w is the definition of the child
split, not a discovery.
"""

from __future__ import annotations

import json
from collections import Counter
from pathlib import Path
from typing import Any

from research.juggler_sequence.compensated_contraction import follows_itinerary, image_after
from research.juggler_sequence.lean_paths import CELLS, DYNAMICS, ITINERARY
from research.juggler_sequence.power_itineraries import ANTI_OVERCLAIM, floor_power
from research.juggler_sequence.realization_geometry import collect_realizing

REPO_ROOT = Path(__file__).resolve().parents[3]
JSON_PATH = REPO_ROOT / "docs" / "research" / "juggler_landing_image.json"
DOC_PATH = REPO_ROOT / "docs" / "research" / "juggler_landing_image.md"

DIAG_N = 4000
DIAG_K = 12
CONFIRM_N = 100_000

CLASS_MONOTONE = "IMAGE_MONOTONE_GREEN"
CLASS_CELL = "IMAGE_CELL_GREEN"
CLASS_RECUR = "IMAGE_RECURRENCE_GREEN"
CLASS_BRANCH = "IMAGE_BRANCHING_GREEN"
CLASS_THAW = "IMAGE_THAW_GREEN"
CLASS_SCALE = "IMAGE_SCALE_GREEN"
CLASS_COMPLEX = "IMAGE_GEOMETRY_COMPLEX"
CLASS_COUNTER = "IMAGE_GEOMETRY_COUNTEREXAMPLE"

FORBIDDEN_ENGINES = (
    "ResidualGraph",
    "ResidualState",
    "MilestoneGraph",
    "PowerHeight",
    "CycleEngine",
)

SPECIAL = tuple(
    ["E" * r for r in range(1, 7)]
    + ["O" * r for r in range(1, 7)]
    + [f"{'E' * r}O" for r in range(1, 6)]
    + [f"{'E' * r}OE" for r in range(1, 5)]
    + [f"{'E' * r}OO" for r in range(1, 5)]
    + [f"{'O' * r}E" for r in range(1, 6)]
    + [f"{'O' * r}EO" for r in range(1, 5)]
    + ["EO", "EOE", "EOO", "OEO", "OOE", "EEO", "OEEEE", "OOOOE", "EEEE"]
)


def phi(ys: list[int], letter: str) -> list[int]:
    out: set[int] = set()
    for y in ys:
        if letter == "E" and y % 2 == 0:
            out.add(floor_power(y))
        elif letter == "O" and y % 2 == 1:
            out.add(floor_power(y))
        elif letter not in {"O", "E"}:
            raise ValueError(f"invalid letter {letter!r}")
    return sorted(out)


def components(xs: list[int]) -> list[tuple[int, int]]:
    if not xs:
        return []
    runs = []
    lo = prev = xs[0]
    for x in xs[1:]:
        if x == prev + 1:
            prev = x
            continue
        runs.append((lo, prev))
        lo = prev = x
    runs.append((lo, prev))
    return runs


def interval_class(n_comp: int) -> str:
    if n_comp == 0:
        return "UNKNOWN"
    if n_comp == 1:
        return "SINGLE_INTERVAL"
    if n_comp <= 4:
        return "FEW_INTERVALS"
    return "FRAGMENTED"


def parity_support(ys: list[int]) -> str:
    has_o = any(y & 1 for y in ys)
    has_e = any(y % 2 == 0 for y in ys)
    if has_o and has_e:
        return "MIXED"
    if has_o:
        return "O_ONLY"
    if has_e:
        return "E_ONLY"
    return "EMPTY"


def image_of(word: str, starts: list[int]) -> list[int]:
    return sorted({image_after(n, word) for n in starts})


def first_inversion(word: str, starts: list[int]) -> dict[str, int] | None:
    prev_n: int | None = None
    prev_y: int | None = None
    for n in starts:
        y = image_after(n, word)
        if prev_n is not None and prev_y is not None and y < prev_y:
            return {"n1": prev_n, "n2": n, "y1": prev_y, "y2": y, "word": word}
        prev_n, prev_y = n, y
    return None


def image_row(word: str, starts: list[int]) -> dict[str, Any]:
    ys = image_of(word, starts)
    odds = [y for y in ys if y & 1]
    evens = [y for y in ys if y % 2 == 0]
    comps = components(ys)
    hull = (ys[-1] - ys[0] + 1 - len(ys)) if ys else 0
    inv = first_inversion(word, starts)
    endpoints_ok = True
    if starts and ys:
        endpoints_ok = (
            image_after(starts[0], word) == ys[0]
            and image_after(starts[-1], word) == ys[-1]
        )
    support = parity_support(ys)
    degree = {"": 0, "EMPTY": 0, "O_ONLY": 1, "E_ONLY": 1, "MIXED": 2}[support]
    return {
        "word": word,
        "length": len(word),
        "n_realizers": len(starts),
        "min_n": starts[0] if starts else None,
        "max_n": starts[-1] if starts else None,
        "y_size": len(ys),
        "y_min": ys[0] if ys else None,
        "y_max": ys[-1] if ys else None,
        "y_span": (ys[-1] - ys[0]) if ys else None,
        "y_odd": len(odds),
        "y_even": len(evens),
        "odd_min": odds[0] if odds else None,
        "odd_max": odds[-1] if odds else None,
        "even_min": evens[0] if evens else None,
        "even_max": evens[-1] if evens else None,
        "component_count": len(comps),
        "largest_component": max((hi - lo + 1 for lo, hi in comps), default=0),
        "max_gap": max((b[0] - a[1] for a, b in zip(comps, comps[1:])), default=0),
        "hull_defect": hull,
        "interval_class": interval_class(len(comps)),
        "parity_support": support,
        "degree": degree,
        "monotone": inv is None,
        "inversion": inv,
        "endpoints_control_hull": endpoints_ok,
        "compression": (len(ys) / len(starts)) if starts else None,
    }


def window_images(realizing: dict[str, list[int]]) -> dict[str, Any]:
    rows = [image_row(word, starts) for word, starts in realizing.items()]
    inversions = [row["inversion"] for row in rows if row["inversion"]]
    phi_fail = None
    phi_checks = 0
    for word, starts in realizing.items():
        if len(word) >= 12:
            continue
        ys = image_of(word, starts)
        for letter in "OE":
            child = word + letter
            if child not in realizing:
                continue
            got = image_of(child, realizing[child])
            expect = phi(ys, letter)
            phi_checks += 1
            if got != expect and phi_fail is None:
                phi_fail = {"word": word, "letter": letter, "got": got[:12], "expect": expect[:12]}
    by_class = Counter(row["interval_class"] for row in rows)
    by_support = Counter(row["parity_support"] for row in rows)
    unary = [row for row in rows if row["degree"] == 1]
    binary = [row for row in rows if row["degree"] == 2]
    unary_interval = Counter(row["interval_class"] for row in unary)
    binary_interval = Counter(row["interval_class"] for row in binary)
    unary_singleton = sum(1 for row in unary if row["y_size"] == 1)
    binary_single_interval = sum(1 for row in binary if row["interval_class"] == "SINGLE_INTERVAL")
    thaws = []
    for row in rows:
        if row["degree"] != 1:
            continue
        letter = "O" if row["parity_support"] == "O_ONLY" else "E"
        child = row["word"] + letter
        child_row = next((r for r in rows if r["word"] == child), None)
        if child_row and child_row["degree"] == 2:
            thaws.append(
                {
                    "ancestor": row["word"],
                    "descendant": child,
                    "y_w": [row["y_min"], row["y_max"], row["y_size"], row["parity_support"]],
                    "y_v": [
                        child_row["y_min"],
                        child_row["y_max"],
                        child_row["y_size"],
                        child_row["parity_support"],
                    ],
                    "event": "image_gained_second_parity",
                }
            )
    return {
        "n_words": len(rows),
        "inversions": inversions[:10],
        "inversion_count": len(inversions),
        "monotone_all": not inversions,
        "endpoints_ok": all(row["endpoints_control_hull"] for row in rows),
        "phi_checks": phi_checks,
        "phi_fail": phi_fail,
        "interval_class_counts": dict(by_class),
        "parity_support_counts": dict(by_support),
        "unary": len(unary),
        "binary": len(binary),
        "unary_singleton": unary_singleton,
        "unary_interval_class": dict(unary_interval),
        "binary_interval_class": dict(binary_interval),
        "binary_single_interval": binary_single_interval,
        "thaws": thaws[:12],
        "thaw_count": len(thaws),
        "special": [image_row(w, realizing[w]) for w in SPECIAL if w in realizing],
    }


def selected_confirm(*, n_max: int = CONFIRM_N) -> dict[str, Any]:
    rows = []
    inversions = []
    for word in SPECIAL:
        starts = [n for n in range(1, n_max + 1) if follows_itinerary(n, word)]
        if not starts:
            continue
        row = image_row(word, starts)
        rows.append(row)
        if row["inversion"]:
            inversions.append(row["inversion"])
    return {
        "n_max": n_max,
        "n_words": len(rows),
        "inversion_count": len(inversions),
        "inversions": inversions[:5],
        "monotone_all": not inversions,
        "rows": [
            {
                "word": r["word"],
                "y_size": r["y_size"],
                "y_min": r["y_min"],
                "y_max": r["y_max"],
                "interval_class": r["interval_class"],
                "parity_support": r["parity_support"],
                "degree": r["degree"],
                "component_count": r["component_count"],
                "hull_defect": r["hull_defect"],
                "compression": r["compression"],
            }
            for r in rows
        ],
    }


def lean_api_present() -> dict[str, Any]:
    text = (
        DYNAMICS.read_text(encoding="utf-8")
        + CELLS.read_text(encoding="utf-8")
        + ITINERARY.read_text(encoding="utf-8")
    )
    return {
        "sorry_free": "sorry" not in text and "admit" not in text,
        "floorPower": "def floorPower" in text,
        "follows": "def follows" in text,
        "image": "def image" in text,
        "even_preimage_iff": "theorem even_preimage_iff" in text,
        "floorPower_even_mono": "theorem floorPower_even_mono" in text,
        "floorPower_odd_mono": "theorem floorPower_odd_mono" in text,
        "image_monotone_of_follows": "theorem image_monotone_of_follows" in text,
        "no_forbidden_engines": all(name not in text for name in FORBIDDEN_ENGINES),
        "no_global_termination_theorem": "theorem juggler_reaches_one" not in text,
    }


def classify(scan: dict[str, Any]) -> dict[str, Any]:
    diag = scan["diagnostic"]
    confirm = scan["confirm"]
    if diag["inversion_count"] or confirm["inversion_count"]:
        return {
            "classification": CLASS_COUNTER,
            "reason": "T_w inversion on R_w; landing-image monotonicity failed",
        }
    if diag["phi_fail"] is not None:
        return {
            "classification": CLASS_COUNTER,
            "reason": "Y_{wb} != Phi_b(Y_w) on the diagnostic window",
        }
    mixed_fragmented = diag["interval_class_counts"].get("FRAGMENTED", 0)
    unary_not_singleton = diag["unary"] - diag["unary_singleton"]
    if (
        diag["monotone_all"]
        and confirm["monotone_all"]
        and diag["endpoints_ok"]
        and diag["phi_fail"] is None
    ):
        extra = (
            " Mixed-word images are often fragmented "
            f"({mixed_fragmented} FRAGMENTED rows; "
            f"{unary_not_singleton} non-singleton unary images). "
            "Interval structure does not give a new branching rule beyond "
            "parity support of Y_w."
        )
        return {
            "classification": CLASS_MONOTONE,
            "secondary": CLASS_RECUR,
            "reason": (
                "T_w is monotone on R_w in both windows, so endpoints of R_w "
                "control the hull of Y_w. Y_{wb} = Phi_b(Y_w) holds exactly. "
                + extra
            ),
        }
    return {
        "classification": CLASS_COMPLEX,
        "reason": "no stable low-complexity image structure beyond landing parity",
    }


def run_probe() -> dict[str, Any]:
    realizing = collect_realizing(n_max=DIAG_N, k_max=DIAG_K)
    return {
        "diagnostic": {**window_images(realizing), "n_max": DIAG_N, "k_max": DIAG_K},
        "confirm": selected_confirm(),
    }


def probe_payload() -> dict[str, Any]:
    scan = run_probe()
    lean = lean_api_present()
    decision = classify(scan)
    anti = dict(ANTI_OVERCLAIM)
    anti.update(
        {
            "forbidden_factor_law": False,
            "global_termination": False,
            "reopen_pe_factors": False,
            "reopen_residual_quotient": False,
            "reopen_summed_rho": False,
            "automaton": False,
            "landing_parity_as_discovery": False,
        }
    )
    return {
        "experiment": "juggler_landing_image",
        "engine_control_layer_modified": False,
        "anti_overclaim": anti,
        "scan": scan,
        "lean": lean,
        "decision": decision,
        "search_method": (
            "Y_w = image_after(R_w); Phi_E/Phi_O recurrence; interval components; "
            "monotone inversion hunt; selected confirm at n<=1e5"
        ),
    }


def _fmt(row: dict[str, Any]) -> str:
    return (
        f"- `{row['word']}` class=`{row['interval_class']}` support=`{row['parity_support']}` "
        f"|Y|=`{row['y_size']}` [{row['y_min']},{row['y_max']}] comps=`{row['component_count']}` "
        f"defect=`{row['hull_defect']}` d=`{row['degree']}`"
    )


def render_markdown(payload: dict[str, Any]) -> str:
    decision = payload["decision"]
    scan = payload["scan"]
    diag = scan["diagnostic"]
    confirm = scan["confirm"]
    lean = payload["lean"]
    lines = [
        "# Juggler landing-image geometry",
        "",
        f"Status: **{decision['classification']}**",
        "",
        "Standalone application phase. Not a Research Engine experiment",
        "and not a termination theorem. Studies `Y_w = T_w(R_w)`. Does not",
        "reopen PE-factor, residual-future, or summed-rho branches.",
        "`d(w)` as parity support of `Y_w` is the child-split definition,",
        "not a result.",
        "",
        "## Branch budget",
        "",
        "```text",
        "Mathematical target     Is Y_w a low-complexity exact image object?",
        "Novelty hypothesis      monotone / cell / Phi calculus stronger than parity",
        "Falsifier               inversions; Y_{wb} != Phi_b(Y_w); only tautologies",
        "Existing machinery      image_after, floor_power, collect_realizing, even_preimage",
        "Maximum Phase-0 scope   N<=4000 all prefixes k<=12; selected confirm 1e5",
        "```",
        "",
        "## Metadata",
        "",
        f"- diagnostic: `n<= {diag['n_max']}`, `k<= {diag['k_max']}`",
        f"- confirm selected words: `n<= {confirm['n_max']}`",
        f"- engine control layer modified: `{payload['engine_control_layer_modified']}`",
        f"- classification: **{decision['classification']}**",
        f"- sorry-free: `{lean['sorry_free']}`",
        "",
        decision["reason"],
        "",
        "## Diagnostic window",
        "",
        f"- words: `{diag['n_words']}`",
        f"- inversions: `{diag['inversion_count']}`",
        f"- endpoints control hull: `{diag['endpoints_ok']}`",
        f"- Phi checks: `{diag['phi_checks']}` fail `{diag['phi_fail']}`",
        f"- unary `{diag['unary']}` (singleton `{diag['unary_singleton']}`) binary `{diag['binary']}`",
        f"- interval classes: `{diag['interval_class_counts']}`",
        f"- unary interval classes: `{diag['unary_interval_class']}`",
        f"- binary interval classes: `{diag['binary_interval_class']}`",
        f"- binary single-interval: `{diag['binary_single_interval']}`",
        f"- thaw events: `{diag['thaw_count']}`",
        "",
        "Special families:",
        "",
    ]
    for row in diag["special"]:
        lines.append(_fmt(row))
    lines.extend(["", "Thaw examples (unary ancestor → binary child):", ""])
    if not diag["thaws"]:
        lines.append("- none in the diagnostic window")
    for rec in diag["thaws"][:8]:
        lines.append(
            f"- `{rec['ancestor']}` → `{rec['descendant']}` "
            f"Y_w=`{rec['y_w']}` Y_v=`{rec['y_v']}` event=`{rec['event']}`"
        )
    lines.extend(
        [
            "",
            "## Confirm window (selected words)",
            "",
            f"- words: `{confirm['n_words']}` inversions `{confirm['inversion_count']}`",
            "",
        ]
    )
    for row in confirm["rows"]:
        lines.append(
            f"- `{row['word']}` |Y|=`{row['y_size']}` [{row['y_min']},{row['y_max']}] "
            f"`{row['interval_class']}` `{row['parity_support']}` d=`{row['degree']}` "
            f"comps=`{row['component_count']}` defect=`{row['hull_defect']}`"
        )
    lines.extend(["", "## Lean", ""])
    for key in (
        "floorPower",
        "follows",
        "image",
        "even_preimage_iff",
        "floorPower_even_mono",
        "floorPower_odd_mono",
        "image_monotone_of_follows",
        "no_forbidden_engines",
        "no_global_termination_theorem",
    ):
        lines.append(f"- `{key}`: `{lean.get(key)}`")
    lines.extend(["", "## Anti-overclaim", ""])
    for key, value in payload["anti_overclaim"].items():
        lines.append(f"- {key}: `{value}`")
    lines.extend(
        [
            "",
            "## Decision",
            "",
            f"**{decision['classification']}**",
            "",
            decision["reason"],
            "",
            "This is not a halt result and not a residual quotient.",
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
