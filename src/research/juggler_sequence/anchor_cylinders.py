"""Nested AboveAnchor start-sets along hard prefix chains.

Not a Research Engine control-layer experiment. Not a halt theorem.
Not a reopen of the closed formal-versus-realized word census.
Not a new atlas language tag and not an automaton.

Phase 0 distinguishes R_w(X) from A_w(X) and asks whether nested
integer support of hard histories decays or migrates in a
scale-stable way. Absence is NOT_OBSERVED_WITHIN_BOUND.
"""

from __future__ import annotations

import json
from collections import defaultdict
from pathlib import Path
from typing import Any

from research.juggler_sequence.atlas.packed import pack_word, unpack_word, word_id
from research.juggler_sequence.atlas.schema import CLAIM_NOT_OBSERVED
from research.juggler_sequence.formal_realized_gap import walk_aa
from research.juggler_sequence.landing_image import components
from research.juggler_sequence.lean_paths import (
    JUGGLER_DIR,
    JUGGLER_PAPER_BARREL,
    engine_floor_text,
    has_named,
    juggler_text,
)
from research.juggler_sequence.minimum_relative import above_anchor
from research.juggler_sequence.near_extremal_prefixes import prefix_noncontracting
from research.juggler_sequence.power_itineraries import ANTI_OVERCLAIM, floor_power

REPO_ROOT = Path(__file__).resolve().parents[3]
JSON_PATH = REPO_ROOT / "docs" / "research" / "juggler_anchor_cylinders.json"
DOC_PATH = REPO_ROOT / "docs" / "research" / "juggler_anchor_cylinders.md"
DATA_DIR = REPO_ROOT / "data" / "research" / "juggler" / "anchor_cylinders"

CLASS_CLOSED = "ANCHOR_CYLINDER_CLOSED"
CLASS_PARK = "ANCHOR_CYLINDER_PARK"
CLASS_GREEN = "ANCHOR_CYLINDER_GREEN"
CLASS_INCOMPLETE = "ANCHOR_CYLINDER_INCOMPLETE"

SCIENCE_K_MAX = 20
SCIENCE_WINDOWS = (100_000, 1_000_000)
TEST_K_MAX = 8
TEST_WINDOWS = (400,)
HARD_LABS = (37, 69, 89, 365, 501, 1517, 6187, 329, 33391)
BOTTLENECK_RATIO = 0.25

EXISTING_LEAN = (
    "AboveAnchor",
    "aboveAnchor_of_prefix",
    "prefixNoncontracting",
    "aboveAnchor_not_envelope_drop",
    "follows",
)

FORBIDDEN_THEOREMS = (
    "juggler_reaches_one",
    "no_juggler_escape",
    "all_finiteProgress",
)

FORBIDDEN_NEW_API = (
    "AnchorCylinder",
    "NestedAnchor",
    "SupportDecay",
    "MinimalAnchorGrowth",
)

NEW_LEAN_FILES = (
    JUGGLER_DIR / "AnchorCylinder.lean",
    JUGGLER_DIR / "NestedAnchor.lean",
    JUGGLER_DIR / "SupportDecay.lean",
)


def prefix_packed(packed: int, length: int) -> int:
    return packed & ((1 << length) - 1)


def census(
    *,
    x_max: int,
    k_max: int,
    n_begin: int = 3,
    extras: tuple[int, ...] = HARD_LABS,
    watch_ids: set[int] | None = None,
) -> dict[str, Any]:
    """One-pass R_w and A_w counts for odd starts n <= x_max.

    extras larger than x_max contribute only their word, not a start.
    """

    if x_max < 1 or k_max < 0:
        raise ValueError("invalid census bounds")
    a_count: dict[int, int] = defaultdict(int)
    r_count: dict[int, int] = defaultdict(int)
    a_min: dict[int, int] = {}
    r_min: dict[int, int] = {}
    watched: dict[int, list[int]] = {wid: [] for wid in (watch_ids or ())}
    scanned = 0
    starts = set(range(n_begin + (n_begin % 2 == 0), x_max + 1, 2))
    starts.update(n for n in extras if 2 <= n <= x_max)
    for n in sorted(starts):
        packed = 0
        state = n
        aa_alive = True
        scanned += 1
        for depth in range(1, k_max + 1):
            packed |= (state & 1) << (depth - 1)
            nxt = floor_power(state)
            wid = word_id(depth, packed)
            r_count[wid] += 1
            prev_r = r_min.get(wid)
            if prev_r is None or n < prev_r:
                r_min[wid] = n
            if aa_alive:
                if nxt < n:
                    aa_alive = False
                else:
                    a_count[wid] += 1
                    prev_a = a_min.get(wid)
                    if prev_a is None or n < prev_a:
                        a_min[wid] = n
                    bucket = watched.get(wid)
                    if bucket is not None:
                        bucket.append(n)
            state = nxt
    return {
        "x_max": x_max,
        "k_max": k_max,
        "scanned": scanned,
        "a_count": dict(a_count),
        "r_count": dict(r_count),
        "a_min": a_min,
        "r_min": r_min,
        "watched": watched,
    }


def lookup(stats: dict[str, Any], word: str) -> dict[str, Any]:
    if not word:
        return {
            "word": "",
            "length": 0,
            "a_count": stats["scanned"],
            "r_count": stats["scanned"],
            "a_min": None,
            "r_min": None,
            "a_frac": 1.0,
        }
    length, packed = pack_word(word)
    wid = word_id(length, packed)
    a = int(stats["a_count"].get(wid, 0))
    r = int(stats["r_count"].get(wid, 0))
    x_max = stats["x_max"]
    return {
        "word": word,
        "length": length,
        "a_count": a,
        "r_count": r,
        "a_min": stats["a_min"].get(wid),
        "r_min": stats["r_min"].get(wid),
        "a_frac": a / x_max if x_max else 0.0,
    }


def hard_word(n: int, k_max: int) -> str:
    packed, depth = walk_aa(n, k_max)
    return unpack_word(depth, packed) if depth else ""


def chain_rows(word: str, stats: dict[str, Any]) -> list[dict[str, Any]]:
    rows = []
    parent_a = stats["scanned"]
    for length in range(1, len(word) + 1):
        row = lookup(stats, word[:length])
        child_a = row["a_count"]
        row["C"] = (child_a / parent_a) if parent_a else 0.0
        parent_a = child_a
        rows.append(row)
    return rows


def first_bottleneck(rows: list[dict[str, Any]]) -> dict[str, Any] | None:
    for index, row in enumerate(rows):
        if row["C"] <= BOTTLENECK_RATIO and row["length"] >= 2:
            parent = rows[index - 1]
            return {
                "k": row["length"],
                "parent": parent["word"],
                "child": row["word"],
                "S_parent": parent["a_count"],
                "S_child": row["a_count"],
                "C": row["C"],
            }
    return None


def max_support_by_length(stats: dict[str, Any], k_max: int) -> list[int]:
    best = [0] * (k_max + 1)
    for wid, count in stats["a_count"].items():
        length = wid >> 32
        if 1 <= length <= k_max and count > best[length]:
            best[length] = count
    return best


def interval_geometry(starts: list[int]) -> dict[str, Any]:
    ordered = sorted(starts)
    comps = components(ordered)
    widths = [hi - lo + 1 for lo, hi in comps]
    gaps = [ordered[i] - ordered[i - 1] for i in range(1, len(ordered))]
    return {
        "n_starts": len(ordered),
        "n_components": len(comps),
        "min": ordered[0] if ordered else None,
        "max": ordered[-1] if ordered else None,
        "width_sum": sum(widths),
        "max_width": max(widths) if widths else 0,
        "median_gap": sorted(gaps)[len(gaps) // 2] if gaps else 0,
    }


def analyze_lab(
    n: int,
    k_max: int,
    windows: dict[int, dict[str, Any]],
) -> dict[str, Any]:
    word = hard_word(n, k_max)
    by_x = {}
    for x_max, stats in windows.items():
        rows = chain_rows(word, stats)
        by_x[str(x_max)] = {
            "rows": rows,
            "bottleneck": first_bottleneck(rows),
            "final": rows[-1] if rows else None,
        }
    scales = sorted(windows)
    scale_cmp = None
    if len(scales) >= 2 and word:
        small, large = scales[0], scales[-1]
        small_final = by_x[str(small)]["final"]
        large_final = by_x[str(large)]["final"]
        if small_final and large_final:
            scale_cmp = {
                "small_X": small,
                "large_X": large,
                "S_small": small_final["a_count"],
                "S_large": large_final["a_count"],
                "frac_small": small_final["a_frac"],
                "frac_large": large_final["a_frac"],
                "n_min_small": small_final["a_min"],
                "n_min_large": large_final["a_min"],
                "n_min_stable": small_final["a_min"] == large_final["a_min"],
            }
    return {
        "n": n,
        "S": len(word),
        "word": word,
        "formal": prefix_noncontracting(word) if word else True,
        "by_X": by_x,
        "scale": scale_cmp,
    }


def sibling_split(word: str, stats: dict[str, Any]) -> dict[str, Any] | None:
    if not word:
        return None
    parent = lookup(stats, word)
    odd = lookup(stats, word + "O")
    even = lookup(stats, word + "E")
    total = odd["a_count"] + even["a_count"]
    return {
        "parent": parent["a_count"],
        "O": odd["a_count"],
        "E": even["a_count"],
        "child_sum": total,
        "drop_loss": parent["a_count"] - total,
        "B": (total / parent["a_count"]) if parent["a_count"] else 0.0,
    }


def run_probe(
    *,
    k_max: int = TEST_K_MAX,
    windows: tuple[int, ...] = TEST_WINDOWS,
    labs: tuple[int, ...] = HARD_LABS,
    collect_intervals: bool = False,
) -> dict[str, Any]:
    watch_ids: set[int] = set()
    lab_words = {n: hard_word(n, k_max) for n in labs}
    if collect_intervals:
        small_x = min(windows)
        for word in lab_words.values():
            for length in range(1, len(word) + 1):
                length_i, packed = pack_word(word[:length])
                watch_ids.add(word_id(length_i, packed))
        del small_x
    window_stats = {}
    for x_max in windows:
        window_stats[x_max] = census(
            x_max=x_max,
            k_max=k_max,
            extras=labs,
            watch_ids=watch_ids if collect_intervals and x_max == min(windows) else None,
        )
    lab_rows = [analyze_lab(n, k_max, window_stats) for n in labs]
    large = window_stats[max(windows)]
    m_k = max_support_by_length(large, k_max)
    hard_m = [0] * (k_max + 1)
    for lab in lab_rows:
        rows = lab["by_X"][str(max(windows))]["rows"]
        for row in rows:
            length = row["length"]
            if row["a_count"] > hard_m[length]:
                hard_m[length] = row["a_count"]
    isolation = []
    for lab in lab_rows:
        final = lab["by_X"][str(max(windows))]["final"]
        if final:
            isolation.append(
                {
                    "n": lab["n"],
                    "k": final["length"],
                    "S": final["a_count"],
                    "N_min": final["a_min"],
                    "frac": final["a_frac"],
                    "isolated": final["a_count"] <= 4,
                }
            )
    n_min_growth = []
    for lab in lab_rows:
        rows = lab["by_X"][str(max(windows))]["rows"]
        mins = [row["a_min"] for row in rows if row["a_min"] is not None]
        if mins:
            n_min_growth.append(
                {
                    "n": lab["n"],
                    "first": mins[0],
                    "last": mins[-1],
                    "grows": mins[-1] > mins[0],
                    "equals_lab": mins[-1] == lab["n"],
                }
            )
    siblings = []
    for lab in lab_rows:
        word = lab["word"]
        if len(word) >= 2:
            siblings.append({"n": lab["n"], **(sibling_split(word[:-1], large) or {})})
    intervals = {}
    if collect_intervals:
        small = window_stats[min(windows)]
        for lab in lab_rows:
            word = lab["word"]
            if not word:
                continue
            wid = word_id(*pack_word(word))
            intervals[str(lab["n"])] = interval_geometry(small["watched"].get(wid, []))
    oe = lookup(large, "OE")
    ooe = lookup(large, "OOE")
    extra_aa_not_formal = 0
    for wid, count in large["a_count"].items():
        if count <= 0:
            continue
        length = wid >> 32
        packed = wid & 0xFFFFFFFF
        word = unpack_word(length, packed)
        if not prefix_noncontracting(word):
            extra_aa_not_formal += 1
    return {
        "basin": "ordinary_integers",
        "k_max": k_max,
        "windows": list(windows),
        "labs": list(labs),
        "scanned": {str(x): window_stats[x]["scanned"] for x in windows},
        "labs_detail": lab_rows,
        "M_k": m_k[1:],
        "M_k_hard": hard_m[1:],
        "hard_thinner_max": bool(m_k[-1] and hard_m[-1] + 1e-12 < 0.5 * m_k[-1]),
        "isolation": isolation,
        "n_min_growth": n_min_growth,
        "siblings": siblings,
        "intervals": intervals,
        "oe": oe,
        "ooe": ooe,
        "oe_a_empty": oe["a_count"] == 0,
        "oe_r_positive": oe["r_count"] > 0,
        "extra_aa_not_formal": extra_aa_not_formal,
        "letter_chain": False,
        "itinerary_language_reopen": False,
        "anchor_cylinder_lean": False,
        "paper_a_modified": False,
        "halt_theorem": False,
    }


def lean_api_present() -> dict[str, bool]:
    combined = juggler_text()
    named = {name: has_named(combined, name) for name in EXISTING_LEAN}
    forbidden = {name: has_named(combined, name) for name in FORBIDDEN_THEOREMS}
    new_api = {name: has_named(combined, name) for name in FORBIDDEN_NEW_API}
    paper = JUGGLER_PAPER_BARREL.read_text(encoding="utf-8")
    schema = (
        REPO_ROOT / "src" / "research" / "juggler_sequence" / "atlas" / "schema.py"
    ).read_text(encoding="utf-8")
    return {
        "sorry_free": "sorry" not in combined and "admit" not in combined,
        **named,
        **{f"has_{name}": present for name, present in forbidden.items()},
        **{f"has_api_{name}": present for name, present in new_api.items()},
        "new_lean_file": any(path.is_file() for path in NEW_LEAN_FILES),
        "not_in_paper_barrel": "AnchorCylinder" not in paper
        and "NestedAnchor" not in paper,
        "no_atlas_lang": "LANG_ANCHOR" not in schema and "LANG_CYLINDER" not in schema,
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
        or scan["halt_theorem"]
        or scan["anchor_cylinder_lean"]
        or scan["extra_aa_not_formal"]
        or not scan["oe_a_empty"]
        or not scan["oe_r_positive"]
    ):
        return {
            "classification": CLASS_INCOMPLETE,
            "reason": "out-of-scope claim or R/A collapse",
        }

    isolations = scan["isolation"]
    isolated_frac = (
        sum(1 for row in isolations if row["isolated"]) / len(isolations)
        if isolations
        else 0.0
    )
    density_like = False
    for lab in scan["labs_detail"]:
        cmp = lab.get("scale")
        if not cmp:
            continue
        if (
            cmp["frac_large"] >= 0.005
            and cmp["frac_small"] >= 0.005
            and abs(cmp["frac_large"] - cmp["frac_small"]) <= 0.05
        ):
            density_like = True
    large_x = max(scan["windows"]) if scan["windows"] else 1
    trivial_depth = large_x.bit_length() - 1
    early_isolation = [
        row
        for row in isolations
        if row["isolated"] and row["k"] + 4 < trivial_depth
    ]
    m_k = scan["M_k"]
    m_hard = scan["M_k_hard"]
    generic_tail = bool(m_k) and m_k[-1] <= 16
    hard_tracks_generic = not scan["hard_thinner_max"]

    if early_isolation and not hard_tracks_generic:
        return {
            "classification": CLASS_GREEN,
            "reason": (
                "hard prefixes isolate well before the X/2^k window scale "
                "and are thinner than generic max support"
            ),
        }
    if density_like or (hard_tracks_generic and generic_tail):
        return {
            "classification": CLASS_CLOSED,
            "reason": (
                "nested |A_w| follows the generic ~X/2^k occupancy of a "
                "length-k word; short leftovers keep a scale-stable positive "
                "fraction; late O(1) support is the window scale, not a new law"
            ),
        }
    if isolated_frac >= 0.5 and hard_tracks_generic:
        return {
            "classification": CLASS_CLOSED,
            "reason": (
                "deep uniqueness coincides with generic M_k = O(1) at "
                "k ~ log2(X); hard branches are not a thinner family"
            ),
        }
    return {
        "classification": CLASS_PARK,
        "reason": (
            "support thins along some hard chains but the decay is not "
            "separated from generic X/2^k occupancy"
        ),
    }


def probe_payload(
    *,
    k_max: int = TEST_K_MAX,
    windows: tuple[int, ...] = TEST_WINDOWS,
    collect_intervals: bool = False,
) -> dict[str, Any]:
    scan = run_probe(
        k_max=k_max,
        windows=windows,
        collect_intervals=collect_intervals,
    )
    lean = lean_api_present()
    decision = classify(scan, lean)
    anti = dict(ANTI_OVERCLAIM)
    anti.update(
        {
            "global_non_realizability": False,
            "A_w_empty_from_window": False,
            "search_horizon_is_L": False,
            "density_theorem": False,
            "anchor_cylinder_lean": False,
            "itinerary_language_reopen": False,
            "global_termination": False,
        }
    )
    return {
        "experiment": "juggler_anchor_cylinders",
        "engine_control_layer_modified": False,
        "anti_overclaim": anti,
        "scan": scan,
        "lean": lean,
        "decision": decision,
        "search_method": (
            "one-pass R_w / A_w counts; hard-chain C-ratios and N_min; "
            f"k<={k_max}, X in {list(windows)}; labs {list(HARD_LABS)}"
        ),
    }


def _lab_line(lab: dict[str, Any], x_max: int) -> str:
    final = lab["by_X"][str(x_max)]["final"]
    if not final:
        return f"- `{lab['n']}`: empty word"
    bn = lab["by_X"][str(x_max)]["bottleneck"]
    bn_s = f" bottleneck k=`{bn['k']}` C=`{bn['C']:.4f}`" if bn else " no bottleneck"
    return (
        f"- `{lab['n']}`: S=`{lab['S']}` |A|=`{final['a_count']}` "
        f"N_min=`{final['a_min']}` frac=`{final['a_frac']:.6f}` "
        f"word=`{lab['word']}`{bn_s}"
    )


def render_markdown(payload: dict[str, Any]) -> str:
    decision = payload["decision"]
    scan = payload["scan"]
    lean = payload["lean"]
    large = max(scan["windows"])
    lines = [
        "# Juggler nested anchor cylinders",
        "",
        f"Status: **{decision['classification']}**",
        "",
        "R_w versus A_w start-sets on hard AboveAnchor prefix chains.",
        "Not a halt theorem. Absence is NOT_OBSERVED_WITHIN_BOUND.",
        "",
        "## Branch budget",
        "",
        "```text",
        "Mathematical target     scale-stable nested A_w decay or N_min growth",
        "Novelty hypothesis      finite histories occur; one anchor cannot",
        "Maximum Phase-0 scope   two-scale counts; hard chains; no Lean",
        "```",
        "",
        "## Metadata",
        "",
        f"- classification: **{decision['classification']}**",
        f"- k_max: `{scan['k_max']}` windows: `{scan['windows']}`",
        f"- scanned: `{scan['scanned']}`",
        f"- OE A empty / R positive: `{scan['oe_a_empty']}` / `{scan['oe_r_positive']}`",
        f"- extra AA not formal: `{scan['extra_aa_not_formal']}`",
        f"- hard thinner than max |A_w|: `{scan['hard_thinner_max']}`",
        "",
        decision["reason"] + ".",
        "",
        "## Hard laboratories",
        "",
    ]
    for lab in scan["labs_detail"]:
        lines.append(_lab_line(lab, large))
    lines.extend(
        [
            "",
            "## M_k versus M_k^hard",
            "",
            f"- M_k: `{scan['M_k']}`",
            f"- M_k^hard: `{scan['M_k_hard']}`",
            "",
            "## Isolation and N_min",
            "",
            f"- isolation: `{scan['isolation']}`",
            f"- N_min growth: `{scan['n_min_growth']}`",
            "",
            "## R versus A on OE / OOE",
            "",
            f"- OE: A=`{scan['oe']['a_count']}` R=`{scan['oe']['r_count']}`",
            f"- OOE: A=`{scan['ooe']['a_count']}` R=`{scan['ooe']['r_count']}` "
            f"N_min_A=`{scan['ooe']['a_min']}`",
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
    (DATA_DIR / "hard_branches").mkdir(parents=True, exist_ok=True)
    (DATA_DIR / "minimum_anchor").mkdir(parents=True, exist_ok=True)
    (DATA_DIR / "prefix_counts").mkdir(parents=True, exist_ok=True)
    (DATA_DIR / "interval_geometry").mkdir(parents=True, exist_ok=True)
    (DATA_DIR / "scale_stability").mkdir(parents=True, exist_ok=True)
    scan = payload["scan"]
    large = max(scan["windows"])
    prefix_rows = []
    min_rows = []
    scale_rows = []
    for lab in scan["labs_detail"]:
        (DATA_DIR / "hard_branches" / f"n_{lab['n']}.json").write_text(
            json.dumps(lab, indent=2) + "\n", encoding="utf-8"
        )
        final = lab["by_X"][str(large)]["final"]
        if final:
            prefix_rows.append(
                {
                    "n": lab["n"],
                    "word": lab["word"],
                    "a_count": final["a_count"],
                    "r_count": final["r_count"],
                    "N_min": final["a_min"],
                    "status": CLAIM_NOT_OBSERVED,
                }
            )
            min_rows.append(
                {"n": lab["n"], "N_min": final["a_min"], "k": final["length"]}
            )
        if lab.get("scale"):
            scale_rows.append({"n": lab["n"], **lab["scale"]})
    (DATA_DIR / "prefix_counts" / "hard_final.json").write_text(
        json.dumps(prefix_rows, indent=2) + "\n", encoding="utf-8"
    )
    (DATA_DIR / "minimum_anchor" / "labs.json").write_text(
        json.dumps(min_rows, indent=2) + "\n", encoding="utf-8"
    )
    (DATA_DIR / "scale_stability" / "two_window.json").write_text(
        json.dumps(scale_rows, indent=2) + "\n", encoding="utf-8"
    )
    (DATA_DIR / "interval_geometry" / "hard_final.json").write_text(
        json.dumps(scan["intervals"], indent=2) + "\n", encoding="utf-8"
    )
    summary = {
        "classification": payload["decision"]["classification"],
        "reason": payload["decision"]["reason"],
        "k_max": scan["k_max"],
        "windows": scan["windows"],
        "hard_thinner_max": scan["hard_thinner_max"],
        "isolation": scan["isolation"],
        "claim": CLAIM_NOT_OBSERVED,
    }
    (DATA_DIR / "summary.json").write_text(
        json.dumps(summary, indent=2) + "\n", encoding="utf-8"
    )
    (DATA_DIR / "README.md").write_text(
        "# Nested AboveAnchor cylinders\n\n"
        "Bounded R_w / A_w start-set census along hard prefix chains.\n"
        "A missing start is NOT_OBSERVED_WITHIN_BOUND.\n\n"
        "Regenerate with `python -m research.juggler_sequence.anchor_cylinders`.\n",
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
        k_max=SCIENCE_K_MAX,
        windows=SCIENCE_WINDOWS,
        collect_intervals=True,
    )
    write_artifacts(payload)
    print(payload["decision"]["classification"])
    print(payload["decision"]["reason"])
    large = max(payload["scan"]["windows"])
    for lab in payload["scan"]["labs_detail"]:
        print(_lab_line(lab, large))


if __name__ == "__main__":
    main()
