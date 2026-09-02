"""Structural constraints on hypothetical no-progress Juggler prefixes.

Not a Research Engine control-layer experiment. Phase A is already
`minimal_avoids_progress`. This probe records collapse-without-capture,
defect-reset, and finite-prefix annotation until first progress. Not a
halt theorem and not a new certificate type.
"""

from __future__ import annotations

import json
from pathlib import Path
from typing import Any

from research.juggler_sequence.capture_certificates import classify_block
from research.juggler_sequence.envelope_defect import tiny_deficit
from research.juggler_sequence.lean_paths import juggler_text
from research.juggler_sequence.power_itineraries import (
    ANTI_OVERCLAIM,
    LEAN_PATH,
    floor_power,
    odd_count,
    word_of,
)

REPO_ROOT = Path(__file__).resolve().parents[3]
JSON_PATH = REPO_ROOT / "docs" / "research" / "juggler_no_progress_paths.json"
DOC_PATH = REPO_ROOT / "docs" / "research" / "juggler_no_progress_paths.md"

CLASS_GREEN = "NO_PROGRESS_STRUCTURE_GREEN"
CLASS_COLLAPSE = "COLLAPSE_WITHOUT_CAPTURE_COUNTEREXAMPLE"
CLASS_RESET = "DEFECT_RESET_COUNTEREXAMPLE"
CLASS_INCOMPLETE = "NO_PROGRESS_INCOMPLETE"

N_MAX = 80
PREFIX_CAP = 24
BIT_LIMIT = 80
ANNOTATED_STARTS = (3, 7, 13, 41)
CHEAP_REACHES_ONE = (1, 2, 4, 6, 8)
SUFFIX_WINDOW = 8

LEAN_THEOREMS = (
    "two_reachesOne",
    "four_reachesOne",
    "six_reachesOne",
    "eight_reachesOne",
    "image_two_reachesOne",
    "image_four_reachesOne",
    "image_six_reachesOne",
    "image_eight_reachesOne",
    "reachesOne_of_image",
    "minimal_avoids_reachesOne_image",
    "even_itinerary_descent",
    "minimal_odd_start",
    "minimal_avoids_progress",
    "reachesOne_of_iterate",
    "even_itinerary_contracts",
    "floorPower_two",
)

CERTIFICATE_UNCHANGED = (
    "power_bound_compensated_contracts",
    "first_even_freeze",
    "eventually_no_first_even_contraction",
    "changing_suffix_unbounded_contraction",
)


def cheap_reaches_one(y: int) -> bool:
    return y in CHEAP_REACHES_ONE


def realized_prefix(n: int, cap: int = PREFIX_CAP) -> dict[str, Any]:
    if n < 1 or cap < 0:
        raise ValueError("realized_prefix requires n >= 1 and cap >= 0")
    path = [n]
    prefixes: list[dict[str, Any]] = []
    first_progress: dict[str, Any] | None = None
    current = n
    word = ""
    for step in range(cap):
        current = floor_power(current)
        path.append(current)
        word = word_of(tuple(path))
        kind = classify_block(n, word)
        row = {
            "step": step + 1,
            "word": word,
            "image": current,
            "kind": kind,
            "reaches_one_implied": cheap_reaches_one(current),
        }
        prefixes.append(row)
        if kind in ("DESCENT", "CAPTURE"):
            first_progress = row
            break
    return {
        "n": n,
        "path": path,
        "word": word_of(tuple(path)),
        "prefixes": prefixes,
        "first_progress": first_progress,
        "started_odd": n % 2 == 1,
        "started_even": n % 2 == 0,
    }


def even_collapses(path: list[int]) -> list[dict[str, Any]]:
    """Internal even runs `x --E^r--> y` with `y > 1`, including run prefixes."""

    if len(path) < 2:
        return []
    rows: list[dict[str, Any]] = []
    index = 0
    while index < len(path) - 1:
        if path[index] % 2 == 1:
            index += 1
            continue
        start = index
        while index < len(path) - 1 and path[index] % 2 == 0:
            index += 1
            residual = path[index]
            if residual > 1:
                rows.append(
                    {
                        "x": path[start],
                        "y": residual,
                        "r": index - start,
                        "start_index": start,
                    }
                )
    return rows


def collapse_bucket(n: int, y: int) -> str:
    if y == 1:
        return "CAPTURE"
    if 1 < y < n:
        return "DESCENT"
    if y == 2:
        return "REACHES_ONE"
    if cheap_reaches_one(y):
        return "REACHES_ONE"
    return "NO_CERTIFICATE"


def classify_collapse_row(n: int, run: dict[str, Any], word: str) -> dict[str, Any]:
    y = run["y"]
    prefix = word[: run["start_index"] + run["r"]]
    kind = classify_block(n, prefix) if prefix else "NO_CERTIFICATE"
    return {
        **run,
        "n": n,
        "prefix": prefix,
        "prefix_kind": kind,
        "bucket": collapse_bucket(n, y),
        "ratio_num": run["x"],
        "ratio_den": y,
        "extra_constraint": kind == "NO_CERTIFICATE" and cheap_reaches_one(y),
        "uncertified_ge_n": y >= n > 1 and not cheap_reaches_one(y),
    }


def deficits_along(n: int, path: list[int], *, bit_limit: int = BIT_LIMIT) -> list[dict[str, Any]]:
    word = word_of(tuple(path)) if len(path) >= 2 else ""
    rows = []
    for length in range(len(path)):
        image = path[length]
        if length == 0:
            rows.append({"k": 0, "word": "", "image": image, "delta": 0, "odds": 0})
            continue
        prefix = word[:length]
        odds = odd_count(prefix)
        rows.append(
            {
                "k": length,
                "word": prefix,
                "image": image,
                "delta": tiny_deficit(n, image, length, odds, bit_limit=bit_limit),
                "odds": odds,
            }
        )
    return rows


def defect_reset_witness(rows: list[dict[str, Any]]) -> dict[str, Any] | None:
    seen_positive = False
    for row in rows:
        delta = row["delta"]
        if delta is None:
            continue
        if delta > 0:
            seen_positive = True
        elif delta == 0 and seen_positive:
            return row
    return None


def annotate_start(n: int, cap: int = PREFIX_CAP) -> dict[str, Any]:
    record = realized_prefix(n, cap)
    progress = record["first_progress"]
    images_before = [
        row["image"]
        for row in record["prefixes"]
        if progress is None or row["step"] < progress["step"]
    ]
    even_residual = None
    if progress is not None:
        even_residual = progress["image"]
    pattern = {
        "starts_odd": record["started_odd"],
        "odd_expansion_ge_n": all(image >= n for image in images_before),
        "first_progress_kind": None if progress is None else progress["kind"],
        "first_progress_image": None if progress is None else progress["image"],
        "even_residual_lt_n_or_one_or_two": even_residual is not None
        and (even_residual < n or even_residual in (1, 2)),
        "even_residual_cheap_reaches_one": even_residual is not None
        and cheap_reaches_one(even_residual),
    }
    return {**record, "pattern": pattern}


def collapse_census(*, n_max: int = N_MAX, cap: int = PREFIX_CAP) -> dict[str, Any]:
    extra: list[dict[str, Any]] = []
    uncertified: list[dict[str, Any]] = []
    descent_collapses = 0
    capture_collapses = 0
    reaches_one_collapses = 0
    even_starts_progress = 0
    even_starts = 0
    for n in range(2, n_max + 1):
        record = realized_prefix(n, cap)
        if record["started_even"]:
            even_starts += 1
            progress = record["first_progress"]
            if progress is not None and progress["step"] == 1:
                even_starts_progress += 1
        word = record["word"]
        for run in even_collapses(record["path"]):
            row = classify_collapse_row(n, run, word)
            if row["bucket"] == "DESCENT":
                descent_collapses += 1
            elif row["bucket"] == "CAPTURE":
                capture_collapses += 1
            elif row["bucket"] == "REACHES_ONE":
                reaches_one_collapses += 1
            if row["extra_constraint"]:
                extra.append(row)
            if row["uncertified_ge_n"]:
                uncertified.append(row)
    extra.sort(key=lambda row: (row["n"], len(row["prefix"]), row["x"]))
    uncertified.sort(key=lambda row: (row["n"], len(row["prefix"]), -row["x"]))
    largest = None
    for row in uncertified:
        if largest is None or row["x"] * largest["y"] > largest["x"] * row["y"]:
            largest = row
    return {
        "n_max": n_max,
        "cap": cap,
        "even_starts": even_starts,
        "even_starts_first_step_progress": even_starts_progress,
        "descent_collapses": descent_collapses,
        "capture_collapses": capture_collapses,
        "reaches_one_collapses": reaches_one_collapses,
        "extra_constraint_count": len(extra),
        "uncertified_ge_n_count": len(uncertified),
        "extra_constraint_witnesses": extra[:8],
        "uncertified_ge_n_witnesses": uncertified[:8],
        "minimized_extra_constraint": extra[0] if extra else None,
        "minimized_uncertified_ge_n": uncertified[0] if uncertified else None,
        "largest_uncertified_ge_n": largest,
    }


def defect_reset_scan(*, n_max: int = N_MAX, cap: int = PREFIX_CAP) -> dict[str, Any]:
    witnesses: list[dict[str, Any]] = []
    scanned = 0
    positive_seen = 0
    for n in range(2, n_max + 1):
        record = realized_prefix(n, cap)
        rows = deficits_along(n, record["path"])
        scanned += 1
        if any(row["delta"] is not None and row["delta"] > 0 for row in rows):
            positive_seen += 1
        hit = defect_reset_witness(rows)
        if hit is not None:
            witnesses.append({"n": n, **hit})
    return {
        "n_max": n_max,
        "scanned": scanned,
        "positive_defect_orbits": positive_seen,
        "reset_count": len(witnesses),
        "resets": witnesses[:8],
    }


def stubborn_uncertified(
    *, n_max: int = N_MAX, cap: int = PREFIX_CAP, window: int = SUFFIX_WINDOW
) -> list[dict[str, Any]]:
    """Uncertified y≥n collapses whose short suffix is still not progress."""

    stubborn: list[dict[str, Any]] = []
    for n in range(2, n_max + 1):
        record = realized_prefix(n, cap)
        word = record["word"]
        for run in even_collapses(record["path"]):
            row = classify_collapse_row(n, run, word)
            if not row["uncertified_ge_n"]:
                continue
            end = run["start_index"] + run["r"]
            later = record["prefixes"][end : end + window]
            if not later:
                continue
            if any(
                item["kind"] in ("DESCENT", "CAPTURE") or item["reaches_one_implied"]
                for item in later
            ):
                continue
            stubborn.append({**row, "suffix_kinds": [item["kind"] for item in later]})
    return stubborn


def lean_api_present() -> dict[str, bool]:
    text = juggler_text()
    return {
        "sorry_free": "sorry" not in text and "admit" not in text,
        **{
            name: (f"theorem {name}" in text or f"def {name}" in text)
            for name in LEAN_THEOREMS
        },
        "certificate_present": all(f"theorem {name}" in text for name in CERTIFICATE_UNCHANGED),
        "PowerHeight_absent": "PowerHeight" not in text,
        "no_lower_envelope_structure": "structure LowerEnvelope" not in text,
        "no_global_termination_theorem": "theorem juggler_reaches_one" not in text,
        "no_no_progress_prefix_type": "def no_progress_prefix" not in text
        and "structure NoProgressPrefix" not in text,
    }


def classify(
    census: dict[str, Any],
    defects: dict[str, Any],
    annotations: list[dict[str, Any]],
    stubborn: list[dict[str, Any]],
    lean: dict[str, bool],
) -> dict[str, Any]:
    if defects["reset_count"] > 0:
        return {
            "classification": CLASS_RESET,
            "reason": f"integer deficit returned to 0 after a positive defect: {defects['resets'][:2]}",
        }
    even_broken = (
        census["even_starts"] > 0
        and census["even_starts_first_step_progress"] != census["even_starts"]
    )
    if even_broken:
        return {
            "classification": CLASS_COLLAPSE,
            "reason": (
                "an even start n>=2 had a first step that was not descent or capture"
            ),
        }
    lean_ok = (
        lean["sorry_free"]
        and lean["two_reachesOne"]
        and lean["image_two_reachesOne"]
        and lean["reachesOne_of_image"]
        and lean["minimal_avoids_reachesOne_image"]
        and lean["even_itinerary_descent"]
        and lean["minimal_odd_start"]
        and lean["minimal_avoids_progress"]
        and lean["no_no_progress_prefix_type"]
        and lean["no_global_termination_theorem"]
    )
    extra = census["minimized_extra_constraint"]
    even_ok = (
        census["even_starts"] > 0
        and census["even_starts_first_step_progress"] == census["even_starts"]
    )
    annotated_ok = all(
        item["pattern"]["starts_odd"]
        and item["pattern"]["odd_expansion_ge_n"]
        and item["first_progress"] is not None
        for item in annotations
    )
    extra_ok = extra is not None and extra["extra_constraint"] is True
    if lean_ok and even_ok and annotated_ok and extra_ok and defects["reset_count"] == 0:
        return {
            "classification": CLASS_GREEN,
            "reason": (
                "orbit avoids every ReachesOne state; even prefixes at n>=2 are "
                "descent; landing at 2,4,6,8 is ReachesOne-implied even when "
                "the image is at least n (OOE at 5 lands at 6); no defect reset"
            ),
        }
    return {
        "classification": CLASS_INCOMPLETE,
        "reason": (
            f"lean_ok={lean_ok} even_ok={even_ok} annotated_ok={annotated_ok} "
            f"extra_ok={extra_ok} extra={extra}"
        ),
    }


def run_probe() -> dict[str, Any]:
    annotations = [annotate_start(n) for n in ANNOTATED_STARTS]
    census = collapse_census()
    defects = defect_reset_scan()
    stubborn = stubborn_uncertified()
    return {
        "annotations": annotations,
        "census": census,
        "defects": defects,
        "stubborn_uncertified": stubborn,
        "cheap_reaches_one": list(CHEAP_REACHES_ONE),
        "basin": [1],
    }


def probe_payload() -> dict[str, Any]:
    scan = run_probe()
    lean = lean_api_present()
    decision = classify(
        scan["census"],
        scan["defects"],
        scan["annotations"],
        scan["stubborn_uncertified"],
        lean,
    )
    return {
        "experiment": "juggler_no_progress_paths",
        "engine_control_layer_modified": False,
        "anti_overclaim": dict(ANTI_OVERCLAIM),
        "scan": scan,
        "lean": lean,
        "decision": decision,
        "search_method": (
            "realized-orbit prefixes to first DESCENT/CAPTURE; even-run "
            "residuals y>1; integer deficit reset; cheap ReachesOne {1,2,4,6,8}; "
            "no logs, no halt claim"
        ),
    }


def render_markdown(payload: dict[str, Any]) -> str:
    decision = payload["decision"]
    scan = payload["scan"]
    lean = payload["lean"]
    census = scan["census"]
    defects = scan["defects"]
    extra = census["minimized_extra_constraint"]
    uncert = census["minimized_uncertified_ge_n"]
    largest = census.get("largest_uncertified_ge_n")
    lines = [
        "# Juggler no-progress path structure",
        "",
        f"Status: **{decision['classification']}**",
        "",
        "Standalone application phase. Not a Research Engine experiment and",
        "not a termination theorem. Phase A is already `minimal_avoids_progress`.",
        "A hypothetical minimal non-1 orbit avoids every `ReachesOne` state,",
        "not only `[1, n)`.",
        "",
        "## Branch budget",
        "",
        "```text",
        "Mathematical target     Necessary C on a long NO_CERTIFICATE prefix",
        "Novelty hypothesis      Collapse-without-capture is ReachesOne or descent",
        "Falsifier               Large even collapse to m>1 with no certificate",
        "Existing machinery      minimal_avoids_progress, ReachesOne closure",
        "Maximum Phase-0 scope   Census plus cheap ReachesOne wrappers",
        "```",
        "",
        "## Metadata",
        "",
        f"- basin: `{scan['basin']}`",
        f"- cheap ReachesOne: `{scan['cheap_reaches_one']}`",
        f"- engine control layer modified: `{payload['engine_control_layer_modified']}`",
        f"- classification: **{decision['classification']}**",
        f"- sorry-free: `{lean['sorry_free']}`",
        "",
        decision["reason"] + ".",
        "",
        "## Annotated prefixes",
        "",
    ]
    for item in scan["annotations"]:
        progress = item["first_progress"]
        lines.append(
            f"- n=`{item['n']}` word=`{item['word']}` first_progress="
            f"`{None if progress is None else progress['kind']}` "
            f"image=`{None if progress is None else progress['image']}` "
            f"path=`{item['path']}`"
        )
    lines.extend(
        [
            "",
            "## Collapse-without-capture",
            "",
            f"- even starts whose first step is already progress: "
            f"`{census['even_starts_first_step_progress']}/{census['even_starts']}`",
            f"- descent collapses: `{census['descent_collapses']}`",
            f"- reaches-one collapses: `{census['reaches_one_collapses']}`",
            f"- extra-constraint (NO_CERTIFICATE image, cheap ReachesOne): "
            f"`{census['extra_constraint_count']}`",
            f"- uncertified y>=n: `{census['uncertified_ge_n_count']}`",
            f"- large collapse with delayed short-suffix progress: "
            f"`{len(scan['stubborn_uncertified'])}` "
            "(observation; not a refutation of ReachesOne-avoidance)",
            "",
        ]
    )
    if extra is not None:
        lines.append(
            f"- minimized extra constraint: n=`{extra['n']}` word=`{extra['prefix']}` "
            f"`{extra['x']} --E^{extra['r']}--> {extra['y']}` kind=`{extra['prefix_kind']}`"
        )
    if uncert is not None:
        lines.append(
            f"- minimized uncertified y>=n: n=`{uncert['n']}` word=`{uncert['prefix']}` "
            f"`{uncert['x']} --E^{uncert['r']}--> {uncert['y']}` kind=`{uncert['prefix_kind']}`"
        )
    if largest is not None:
        lines.append(
            f"- largest-ratio uncertified y>=n: n=`{largest['n']}` word=`{largest['prefix']}` "
            f"`{largest['x']} --E^{largest['r']}--> {largest['y']}` kind=`{largest['prefix_kind']}`"
        )
    lines.extend(
        [
            "",
            "## Defect reset",
            "",
            f"- orbits with a positive deficit: `{defects['positive_defect_orbits']}`",
            f"- resets to 0 after a first positive defect: `{defects['reset_count']}`",
            "",
            "No persistent-defect object is introduced. Existing strict",
            "power-bound continuation already forbids a return to equality.",
            "",
            "## Lean",
            "",
        ]
    )
    for name in LEAN_THEOREMS:
        lines.append(f"- `{name}`: `{lean.get(name)}`")
    lines.extend(
        [
            f"- certificate unchanged: `{lean.get('certificate_present')}`",
            f"- `PowerHeight` absent: `{lean.get('PowerHeight_absent')}`",
            f"- no `no_progress_prefix` type: `{lean.get('no_no_progress_prefix_type')}`",
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
            "This is not a halt result.",
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
