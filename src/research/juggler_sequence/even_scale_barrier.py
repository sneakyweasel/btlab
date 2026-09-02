"""Even-run scale barriers on a hypothetical minimal non-1 Juggler orbit.

Not a Research Engine control-layer experiment. Not a halt theorem.
Not an all-odd orbit claim: an even state above n_* may still map to a
non-terminating square root, but then the entry must be at least
n_*^{2^r}.
"""

from __future__ import annotations

import json
from pathlib import Path
from typing import Any

from research.juggler_sequence.capture_certificates import classify_block
from research.juggler_sequence.compensated_contraction import follows_itinerary, image_after
from research.juggler_sequence.no_progress_paths import even_collapses, realized_prefix
from research.juggler_sequence.power_itineraries import ANTI_OVERCLAIM, floor_power
from research.juggler_sequence.lean_paths import (
    ENVELOPE,
    MINIMAL,
    has_named,
    juggler_text,
)

REPO_ROOT = Path(__file__).resolve().parents[3]
JSON_PATH = REPO_ROOT / "docs" / "research" / "juggler_even_scale_barrier.json"
DOC_PATH = REPO_ROOT / "docs" / "research" / "juggler_even_scale_barrier.md"
LEAN_PATH = MINIMAL
FLOOR_PATH = ENVELOPE

CLASS_GREEN = "MINIMAL_NORMAL_FORM_GREEN"
CLASS_BARRIER = "EVEN_SCALE_BARRIER_GREEN"
CLASS_COLLAPSE = "INTERNAL_COLLAPSE_BELOW_MINIMAL"
CLASS_INCOMPLETE = "EVEN_SCALE_INCOMPLETE"

N_MAX = 80
PREFIX_CAP = 24
PATTERNS = ("OE", "OOE", "OEO", "OEE", "OOEE", "OOOE")
PATTERN_STARTS = (13, 25, 37, 41)

LEAN_THEOREMS = (
    "MinimalNonTerm",
    "minimal_nonterm_ge_of_not_reachesOne",
    "even_run_pow_le",
    "even_run_exit_ge",
    "even_run_scale_barrier",
    "minimal_nonterm_even_ge_sq",
    "minimal_nonterm_first_even_ge_sq",
    "minimal_nonterm_avoid_even_lt_sq_twelve",
    "even_tower_not_on_minimal",
    "minimal_nonterm_oe_descent",
    "minimal_nonterm_odd_image_odd",
    "minimal_counterexample_normal_form",
    "minimal_nonterm_odd",
    "minimal_nonterm_image_ge",
)

CERTIFICATE_UNCHANGED = (
    "power_bound_compensated_contracts",
    "first_even_freeze",
    "eventually_no_first_even_contraction",
    "changing_suffix_unbounded_contraction",
    "even_itinerary_contracts",
    "reachesOne_of_lt_twelve",
)


def even_pow_holds(entry: int, r: int, exit_state: int) -> bool:
    return exit_state ** (1 << r) <= entry


def scale_holds(start: int, entry: int, r: int, exit_state: int) -> bool:
    if exit_state < start:
        return True
    return start ** (1 << r) <= entry


def even_run_census(*, n_max: int = N_MAX, cap: int = PREFIX_CAP) -> dict[str, Any]:
    rows: list[dict[str, Any]] = []
    pow_fail = 0
    scale_fail = 0
    stay_ge_n = 0
    exit_below_n = 0
    even_above_start = 0
    for n in range(2, n_max + 1):
        record = realized_prefix(n, cap)
        path = record["path"]
        for run in even_collapses(path):
            entry, residual, r = run["x"], run["y"], run["r"]
            if residual <= 1 and r >= 1:
                # include y>1 only from even_collapses; also count full runs to 1 separately
                pass
            ok_pow = even_pow_holds(entry, r, residual)
            ok_scale = scale_holds(n, entry, r, residual)
            if not ok_pow:
                pow_fail += 1
            if residual >= n:
                stay_ge_n += 1
                if not ok_scale:
                    scale_fail += 1
            else:
                exit_below_n += 1
            if entry > n and entry % 2 == 0:
                even_above_start += 1
            rows.append(
                {
                    "n": n,
                    "entry": entry,
                    "r": r,
                    "exit": residual,
                    "pow_ok": ok_pow,
                    "scale_ok": ok_scale,
                    "exit_ge_n": residual >= n,
                }
            )
    rows.sort(key=lambda row: (row["n"], -row["r"], -row["entry"]))
    return {
        "n_max": n_max,
        "run_count": len(rows),
        "pow_fail": pow_fail,
        "scale_fail_when_exit_ge_n": scale_fail,
        "exit_ge_n": stay_ge_n,
        "exit_below_n": exit_below_n,
        "even_entry_above_start": even_above_start,
        "samples": rows[:8],
    }


def pattern_rows() -> list[dict[str, Any]]:
    rows = []
    for n in PATTERN_STARTS:
        for word in PATTERNS:
            if not follows_itinerary(n, word):
                rows.append({"n": n, "word": word, "follows": False, "kind": "NO_FOLLOW"})
                continue
            image = image_after(n, word)
            kind = classify_block(n, word)
            even_images = []
            current = n
            for letter in word:
                if current % 2 == 0:
                    even_images.append(current)
                current = floor_power(current)
            scale_ok = all(img >= n * n for img in even_images)
            rows.append(
                {
                    "n": n,
                    "word": word,
                    "follows": True,
                    "image": image,
                    "kind": kind,
                    "even_images": even_images,
                    "even_ge_sq": scale_ok,
                }
            )
    return rows


def changing_family_forbidden() -> list[dict[str, Any]]:
    samples = [
        ("E", 2),
        ("EEE" + "O" * 9, 16),
        ("OEEE" + "O" * 9, 7),
        ("EE" + "OEEE" + "O" * 12, 2500),
    ]
    rows = []
    for word, n in samples:
        rows.append(
            {
                "n": n,
                "word": word,
                "kind": classify_block(n, word),
                "image": image_after(n, word) if follows_itinerary(n, word) else None,
            }
        )
    return rows


def first_image_parity(*, n_max: int = N_MAX) -> dict[str, Any]:
    odd_start_even_image = []
    for n in range(13, n_max + 1, 2):
        image = floor_power(n)
        if image % 2 == 0:
            odd_start_even_image.append({"n": n, "image": image, "kind": classify_block(n, "OE")})
    return {
        "odd_starts": (n_max - 12 + 1) // 2 if n_max >= 13 else 0,
        "first_image_even": odd_start_even_image[:8],
        "first_image_even_count": len(odd_start_even_image),
        "all_those_oe_descent": all(row["kind"] == "DESCENT" for row in odd_start_even_image),
    }


def lean_api_present() -> dict[str, bool]:
    text = LEAN_PATH.read_text(encoding="utf-8")
    floor = juggler_text()
    combined = text + floor
    return {
        "sorry_free": "sorry" not in combined and "admit" not in combined,
        **{name: has_named(combined, name) for name in LEAN_THEOREMS},
        "certificate_present": all(f"theorem {name}" in floor for name in CERTIFICATE_UNCHANGED),
        "PowerHeight_absent": "PowerHeight" not in text and "PowerHeight" not in floor,
        "no_lower_envelope_structure": "structure LowerEnvelope" not in text
        and "structure LowerEnvelope" not in floor,
        "no_global_termination_theorem": "theorem juggler_reaches_one" not in text
        and "theorem juggler_reaches_one" not in floor,
        "no_infinite_path_type": "coinductive" not in text.lower()
        and "def InfinitePath" not in text
        and "def no_progress_prefix" not in text,
        "no_all_odd_orbit_theorem": "theorem minimal_nonterm_all_odd" not in text,
    }


def classify(
    census: dict[str, Any],
    patterns: list[dict[str, Any]],
    families: list[dict[str, Any]],
    parity: dict[str, Any],
    lean: dict[str, bool],
) -> dict[str, Any]:
    if census["pow_fail"] > 0:
        return {
            "classification": CLASS_COLLAPSE,
            "reason": "even-run power envelope T^r(m)^{2^r} <= m failed on a realized run",
        }
    if census["scale_fail_when_exit_ge_n"] > 0:
        return {
            "classification": CLASS_COLLAPSE,
            "reason": "scale n^{2^r} <= entry failed on a run whose exit stayed >= n",
        }
    lean_ok = (
        lean["sorry_free"]
        and lean["even_run_scale_barrier"]
        and lean["minimal_counterexample_normal_form"]
        and lean["minimal_nonterm_even_ge_sq"]
        and lean["minimal_nonterm_odd_image_odd"]
        and lean["no_all_odd_orbit_theorem"]
        and lean["no_global_termination_theorem"]
    )
    oe_ok = parity["all_those_oe_descent"]
    capture_ok = all(row["kind"] == "CAPTURE" for row in families)
    if lean_ok and oe_ok and capture_ok and census["even_entry_above_start"] > 0:
        return {
            "classification": CLASS_GREEN,
            "secondary": CLASS_BARRIER,
            "reason": (
                "E^r on a minimal non-1 orbit forces entry >= n^{2^r}; "
                "normal form packages scale, no descent below n, no capture, "
                "and first image odd; even states above n remain allowed"
            ),
        }
    if lean_ok:
        return {
            "classification": CLASS_BARRIER,
            "reason": "scale barrier proved; normal-form packaging incomplete in the census",
        }
    return {
        "classification": CLASS_INCOMPLETE,
        "reason": f"lean_ok={lean_ok} oe_ok={oe_ok} capture_ok={capture_ok}",
    }


def run_probe() -> dict[str, Any]:
    return {
        "census": even_run_census(),
        "patterns": pattern_rows(),
        "changing_families": changing_family_forbidden(),
        "first_image_parity": first_image_parity(),
        "basin": [1],
    }


def probe_payload() -> dict[str, Any]:
    scan = run_probe()
    lean = lean_api_present()
    decision = classify(
        scan["census"],
        scan["patterns"],
        scan["changing_families"],
        scan["first_image_parity"],
        lean,
    )
    anti = dict(ANTI_OVERCLAIM)
    anti["all_odd_orbit"] = False
    return {
        "experiment": "juggler_even_scale_barrier",
        "engine_control_layer_modified": False,
        "anti_overclaim": anti,
        "scan": scan,
        "lean": lean,
        "decision": decision,
        "search_method": (
            "realized even runs: T^r(m)^{2^r}<=m and n^{2^r}<=entry when exit>=n; "
            "short odd-start patterns; changing-family capture; no all-odd claim"
        ),
    }


def render_markdown(payload: dict[str, Any]) -> str:
    decision = payload["decision"]
    scan = payload["scan"]
    lean = payload["lean"]
    census = scan["census"]
    lines = [
        "# Juggler even-run scale barrier",
        "",
        f"Status: **{decision['classification']}**",
        "",
        "Standalone application phase. Not a Research Engine experiment and",
        "not a termination theorem. A hypothetical minimal non-1 orbit is",
        "not forced to be all-odd. Every even run `E^r` on it must start at",
        "scale `n^{2^r}`.",
        "",
        "## Branch budget",
        "",
        "```text",
        "Mathematical target     E^r on a minimal non-1 orbit implies entry >= n^{2^r}",
        "Novelty hypothesis      Minimality plus even square-root gives a scale barrier",
        "Falsifier               An even run with exit >= n but entry < n^{2^r}",
        "Existing machinery      ReachesOne closure, even_itinerary_contracts, even_run identities",
        "Maximum Phase-0 scope   MinimalNonTerm; barrier; normal form; short pattern census",
        "```",
        "",
        "## Metadata",
        "",
        f"- basin: `{scan['basin']}`",
        f"- engine control layer modified: `{payload['engine_control_layer_modified']}`",
        f"- classification: **{decision['classification']}**",
        f"- sorry-free: `{lean['sorry_free']}`",
        "",
        decision["reason"] + ".",
        "",
        "## Even-run census",
        "",
        f"- realized runs: `{census['run_count']}`",
        f"- power-envelope failures: `{census['pow_fail']}`",
        f"- scale failures with exit >= n: `{census['scale_fail_when_exit_ge_n']}`",
        f"- runs that stay >= n: `{census['exit_ge_n']}`",
        f"- runs that exit below n: `{census['exit_below_n']}`",
        f"- even entries above the start (allowed, not all-odd): `{census['even_entry_above_start']}`",
        "",
        "## Short patterns",
        "",
    ]
    for row in scan["patterns"]:
        if not row["follows"]:
            lines.append(f"- n=`{row['n']}` word=`{row['word']}` follows=`False`")
            continue
        lines.append(
            f"- n=`{row['n']}` word=`{row['word']}` T=`{row['image']}` "
            f"kind=`{row['kind']}` even_ge_sq=`{row['even_ge_sq']}`"
        )
    lines.extend(["", "## Changing-family capture", ""])
    for row in scan["changing_families"]:
        lines.append(f"- n=`{row['n']}` word=`{row['word']}` kind=`{row['kind']}` T=`{row['image']}`")
    parity = scan["first_image_parity"]
    lines.extend(
        [
            "",
            "## First image after an odd start",
            "",
            f"- odd starts in `13..{N_MAX}` with even first image: "
            f"`{parity['first_image_even_count']}`",
            f"- all of those `OE` prefixes are descent: `{parity['all_those_oe_descent']}`",
            "",
            "A hypothetical minimal start cannot do this. Later even states",
            "above `n^2` remain allowed.",
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
            f"- no infinite-path type: `{lean.get('no_infinite_path_type')}`",
            f"- no all-odd orbit theorem: `{lean.get('no_all_odd_orbit_theorem')}`",
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
            "This is not a halt result and not an all-odd orbit theorem.",
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
