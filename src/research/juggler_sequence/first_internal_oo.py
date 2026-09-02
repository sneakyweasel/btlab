"""First internal OO after first-even overshoot and isolated OE transport.

Not a Research Engine control-layer experiment. Not a halt theorem.
Not a bunched-short tail table, not a leftover-suffix path, not Z5,
not a length-11 assembler, and not a four-even leftover cell.

The terminal-cluster program is frozen. Phase 0 asks what constraint
the first internal OO creates on a CycleMin-shaped word

    O^{a0} E (OE)^r O^b E v

with a0 >= 2, r >= 0, b >= 2, and v unconstrained.
"""

from __future__ import annotations

import json
from collections import Counter
from pathlib import Path
from typing import Any

from research.juggler_sequence.cycle_itinerary import follows_itinerary, image_after
from research.juggler_sequence.lean_paths import (
    CYCLE_OBSTRUCTIONS,
    ENVELOPE,
    FIRST_INTERNAL_OO,
    JUGGLER_PAPER_BARREL,
    MINIMUM_RELATIVE,
    SCALE,
    SMALL_CYCLE_CENSUS,
    engine_floor_text,
    has_named,
    juggler_text,
)
from research.juggler_sequence.power_itineraries import ANTI_OVERCLAIM, floor_power

REPO_ROOT = Path(__file__).resolve().parents[3]
JSON_PATH = REPO_ROOT / "docs" / "research" / "juggler_first_internal_oo.json"
DOC_PATH = REPO_ROOT / "docs" / "research" / "juggler_first_internal_oo.md"

CLASS_GREEN = "FIRST_OO_GREEN"
CLASS_PARK = "FIRST_OO_PARK"
CLASS_CLOSE = "FIRST_OO_CLOSE"
CLASS_REMAINS = "FIRST_OO_REMAINS"
CLASS_INCOMPLETE = "FIRST_OO_INCOMPLETE"

N_MIN = 12
N_HI = 801
A0_CAP = 16
POST_CAP = 200
R_TABLE = {2: 0, 3: 1, 4: 3, 5: 4, 6: 6, 7: 7, 8: 8, 9: 10, 10: 11, 11: 13, 12: 14}

# First-OO events with r >= 2. Not a terminal-cell table.
R_GE_TWO_WITNESSES: tuple[tuple[int, int, int, int], ...] = (
    (2155, 5, 2, 2),
    (2503, 4, 2, 2),
    (2985, 9, 2, 2),
)

# Long post-OO stay; first OO is not an instant kill.
LONG_STAY_WITNESS = {"n": 193, "a0": 3, "r": 0, "b": 7, "steps_to_drop": 66}

LEAN_THEOREMS = (
    "CycleMin",
    "cycleMin_ge_twelve",
    "cycleMin_first_even_overshoots",
    "cycleMin_transport_second_oo",
    "oe_block_contracts",
    "oe_block_scale",
    "repeated_oe_scale",
    "power_bound_word",
    "isolatedPrefix",
    "firstOOState",
    "firstInternalOOWord",
    "FirstInternalOO",
    "firstInternalOO_decomp",
    "isolated_oe_ge_implies_exponent",
    "isolated_oe_lt_of_scale_gap",
    "no_cycleMin_prefix_ooe_oe",
    "isolated_oe_r_max_two",
    "AboveAnchor",
    "isolatedOddSurvival_bound",
    "aboveAnchor_isolated_two",
    "finiteProgress_of_ooe_oe",
    "cycleMin_isolated_two",
    "minimal_isolated_two",
)

FORBIDDEN_THEOREMS = (
    "no_cycle_itinerary_length_eleven",
    "no_cycleMin_four_even",
    "no_cycleMin_five_even",
    "no_juggler_cycle",
)


def isolated_oe_exponent_ok(a0: int, r: int) -> bool:
    """Necessary integer condition for B^r(x1) >= n after O^{a0}E.

    From power_bound_word on O^{a0}E and repeated_oe_scale on (OE)^r:
    2^{2r + a0 + 1} <= 3^{a0 + r}.
    """
    if a0 < 0 or r < 0:
        raise ValueError("a0 and r must be nonnegative")
    return (1 << (2 * r + a0 + 1)) <= 3 ** (a0 + r)


def isolated_oe_r_max(a0: int) -> int:
    """Largest r with isolated_oe_exponent_ok(a0, r), or -1 if none."""
    if a0 < 0:
        raise ValueError("a0 must be nonnegative")
    r = 0
    last = -1
    while isolated_oe_exponent_ok(a0, r):
        last = r
        r += 1
        if r > 64:
            break
    return last


def first_oo_decompose(word: str) -> tuple[int, int, int, str] | None:
    """Split w = O^{a0} E (OE)^r O^b E v with a0 >= 2, b >= 2.

    The displayed O^b is the first internal odd run of length at least 2.
    The suffix v is not classified. Words that leave the isolated-OE
    corridor by a second even letter (EE) return None.
    """
    if not word or word[0] != "O":
        return None
    i = 0
    while i < len(word) and word[i] == "O":
        i += 1
    a0 = i
    if a0 < 2 or i >= len(word) or word[i] != "E":
        return None
    i += 1
    r = 0
    while i + 1 < len(word) and word[i] == "O" and word[i + 1] == "E":
        r += 1
        i += 2
    if i >= len(word) or word[i] != "O":
        return None
    j = i
    while j < len(word) and word[j] == "O":
        j += 1
    b = j - i
    if b < 2:
        return None
    if j >= len(word):
        return a0, r, b, ""
    if word[j] != "E":
        return None
    return a0, r, b, word[j + 1:]


def first_oo_prefix(a0: int, r: int, b: int) -> str:
    if a0 < 2 or r < 0 or b < 2:
        raise ValueError("need a0 >= 2, r >= 0, b >= 2")
    return "O" * a0 + "E" + "OE" * r + "O" * b


def block_map(x: int) -> int | None:
    if x % 2 == 0:
        return None
    mid = floor_power(x)
    if mid % 2 == 1:
        return None
    return floor_power(mid)


def first_even_isolated(n: int, *, cap: int = A0_CAP) -> tuple[int, int] | None:
    """If the orbit begins O^{a0}E with a0 >= 2 and odd landing x1 >= n."""
    if n % 2 == 0:
        return None
    current = n
    a0 = 0
    while current % 2 == 1 and a0 < cap:
        current = floor_power(current)
        a0 += 1
    if a0 < 2 or current % 2 == 1:
        return None
    x1 = floor_power(current)
    if x1 % 2 == 0 or x1 < n:
        return None
    return a0, x1


def iterate_isolated_oe(x: int, n: int) -> tuple[int, int]:
    """Largest r with B^r(x) >= n, and that landing."""
    r = 0
    current = x
    while True:
        image = block_map(current)
        if image is None or image < n:
            return r, current
        r += 1
        current = image
        if r > 64:
            return r, current


def first_oo_event(n: int, *, post_cap: int = POST_CAP) -> dict[str, Any] | None:
    """Geometry of the first internal OO on the isolated-OE corridor."""
    fe = first_even_isolated(n)
    if fe is None:
        return None
    a0, x1 = fe
    current = x1
    r = 0
    while current >= n:
        if current % 2 == 0:
            return None
        nxt = floor_power(current)
        if nxt % 2 == 1:
            xj = current
            b = 1
            state = nxt
            while state % 2 == 1:
                state = floor_power(state)
                b += 1
                if b > 64:
                    break
            after_odds = state
            after_block = (
                floor_power(after_odds) if after_odds % 2 == 0 else after_odds
            )
            later_min = min(xj, after_odds)
            steps = 0
            hit_n = False
            letters: list[str] = []
            walk = xj
            for _ in range(post_cap):
                letters.append("O" if walk % 2 else "E")
                walk = floor_power(walk)
                steps += 1
                if walk < later_min:
                    later_min = walk
                if walk < n:
                    break
                if walk == n:
                    hit_n = True
                    break
            else:
                steps = -1
            return {
                "n": n,
                "a0": a0,
                "r": r,
                "b": b,
                "x1": x1,
                "xj": xj,
                "after_odds": after_odds,
                "after_block": after_block,
                "later_min": later_min,
                "steps_to_drop": steps,
                "hit_n": hit_n,
                "stayed": later_min >= n,
                "t2": floor_power(floor_power(xj)),
                "generic_sq": (xj + 1) ** 2,
                "drop_word": "".join(letters),
                "r_max": isolated_oe_r_max(a0),
            }
        current = floor_power(nxt)
        r += 1
    return None


def scan_window(n_hi: int = N_HI) -> dict[str, Any]:
    events: list[dict[str, Any]] = []
    iso_starts = 0
    exceed = 0
    a0_lt2 = 0
    x1_even = 0
    drop_before = 0
    even_exit = 0
    r_surv_by_a0: dict[int, Counter[int]] = {}
    for n in range(13, n_hi, 2):
        current = n
        a0 = 0
        while current % 2 == 1 and a0 < A0_CAP:
            current = floor_power(current)
            a0 += 1
        if a0 < 2:
            a0_lt2 += 1
            continue
        if current % 2 == 1:
            continue
        x1 = floor_power(current)
        if x1 % 2 == 0:
            x1_even += 1
            continue
        if x1 < n:
            drop_before += 1
            continue
        iso_starts += 1
        r_surv, _land = iterate_isolated_oe(x1, n)
        r_surv_by_a0.setdefault(a0, Counter())[r_surv] += 1
        if r_surv > isolated_oe_r_max(a0):
            exceed += 1
        event = first_oo_event(n)
        if event is None:
            even_exit += 1
            continue
        if event["r"] > event["r_max"]:
            exceed += 1
        events.append(event)
    r_counts: Counter[int] = Counter()
    a0_counts: Counter[int] = Counter()
    b_counts: Counter[int] = Counter()
    drop_prefix: Counter[str] = Counter()
    steps_hist: Counter[int] = Counter()
    t2_strict = 0
    t2_tight = 0
    ooe_ge = 0
    ooe_lt = 0
    for event in events:
        r_counts[event["r"]] += 1
        a0_counts[event["a0"]] += 1
        b_counts[event["b"]] += 1
        steps_hist[event["steps_to_drop"]] += 1
        drop_prefix[event["drop_word"][:4]] += 1
        if event["t2"] > event["generic_sq"]:
            t2_strict += 1
        elif event["t2"] == event["generic_sq"]:
            t2_tight += 1
        if event["b"] == 2:
            if event["after_block"] >= event["n"]:
                ooe_ge += 1
            else:
                ooe_lt += 1
    samples = [
        {
            "n": event["n"],
            "a0": event["a0"],
            "r": event["r"],
            "b": event["b"],
            "steps": event["steps_to_drop"],
            "drop": event["drop_word"][:12],
        }
        for event in events[:8]
    ]
    r_ge2 = [event for event in events if event["r"] >= 2]
    return {
        "n_hi": n_hi,
        "iso_starts": iso_starts,
        "events": len(events),
        "a0_lt2": a0_lt2,
        "x1_even": x1_even,
        "drop_before": drop_before,
        "even_exit": even_exit,
        "exceed_R": exceed,
        "r_counts": {str(k): v for k, v in sorted(r_counts.items())},
        "a0_counts": {str(k): v for k, v in sorted(a0_counts.items())},
        "b_counts": {str(k): v for k, v in sorted(b_counts.items())},
        "r_surv_by_a0": {
            str(a0): {str(r): c for r, c in sorted(counter.items())}
            for a0, counter in sorted(r_surv_by_a0.items())
        },
        "drop_prefix4": {k: v for k, v in drop_prefix.most_common(8)},
        "steps_hist": {str(k): v for k, v in steps_hist.most_common(8)},
        "stay": sum(1 for event in events if event["stayed"]),
        "hit_n": sum(1 for event in events if event["hit_n"]),
        "drop_below_n": sum(1 for event in events if event["later_min"] < event["n"]),
        "t2_strict": t2_strict,
        "t2_tight": t2_tight,
        "ooe_land_ge_n": ooe_ge,
        "ooe_land_lt_n": ooe_lt,
        "max_r": max((event["r"] for event in events), default=None),
        "a0_2_r": r_counts.get(0, 0) if 2 in a0_counts else 0,
        "a0_2_events": a0_counts.get(2, 0),
        "a0_2_nonzero_r": sum(
            1 for event in events if event["a0"] == 2 and event["r"] != 0
        ),
        "window_r_ge2": len(r_ge2),
        "samples": samples,
    }


def witness_rows() -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    for n, a0, r, b in R_GE_TWO_WITNESSES:
        event = first_oo_event(n)
        if event is None:
            rows.append({"n": n, "missing": True})
            continue
        rows.append(
            {
                "n": event["n"],
                "a0": event["a0"],
                "r": event["r"],
                "b": event["b"],
                "expected": [a0, r, b],
                "xj_over_n": event["xj"] / event["n"],
                "steps": event["steps_to_drop"],
                "drop": event["drop_word"][:12],
                "within_R": event["r"] <= isolated_oe_r_max(event["a0"]),
            }
        )
    return rows


def long_stay_row() -> dict[str, Any]:
    event = first_oo_event(LONG_STAY_WITNESS["n"], post_cap=400)
    if event is None:
        return {"missing": True}
    return {
        "n": event["n"],
        "a0": event["a0"],
        "r": event["r"],
        "b": event["b"],
        "steps": event["steps_to_drop"],
        "drop": event["drop_word"][:16],
        "matches": event["steps_to_drop"] == LONG_STAY_WITNESS["steps_to_drop"],
    }


def r_table_scan() -> dict[str, Any]:
    values = {a0: isolated_oe_r_max(a0) for a0 in range(2, 13)}
    return {
        "values": {str(k): v for k, v in values.items()},
        "matches_table": values == R_TABLE,
        "a0_2_is_zero": values[2] == 0,
        "a0_3_is_one": values[3] == 1,
    }


def small_power_check() -> dict[str, Any]:
    """Numeric sandwich of the two Lean bounds on a tiny domain."""
    ok = 0
    fail = 0
    for n in range(13, 51, 2):
        for a0 in (2, 3):
            word = "O" * a0 + "E"
            if not follows_itinerary(n, word):
                continue
            x1 = image_after(n, word)
            if x1 ** (1 << (a0 + 1)) > n ** (3**a0):
                fail += 1
                continue
            image = block_map(x1)
            if image is None:
                ok += 1
                continue
            if image**4 > x1**3:
                fail += 1
                continue
            if image >= n and not isolated_oe_exponent_ok(a0, 1):
                fail += 1
                continue
            ok += 1
    return {"ok": ok, "fail": fail}


def run_probe() -> dict[str, Any]:
    return {
        "basin": [1],
        "n_min": N_MIN,
        "n_hi": N_HI,
        "r_table": r_table_scan(),
        "small_power": small_power_check(),
        "window": scan_window(),
        "r_ge2_witnesses": witness_rows(),
        "long_stay": long_stay_row(),
        "length_eleven_census": False,
        "z5_cells": False,
        "four_even_assembler": False,
        "leftover_suffix_retest": False,
        "terminal_cluster_reopen": False,
    }


def lean_api_present() -> dict[str, bool]:
    combined = juggler_text()
    if SCALE.is_file():
        combined += SCALE.read_text(encoding="utf-8")
    if ENVELOPE.is_file():
        combined += ENVELOPE.read_text(encoding="utf-8")
    if FIRST_INTERNAL_OO.is_file():
        combined += FIRST_INTERNAL_OO.read_text(encoding="utf-8")
    if MINIMUM_RELATIVE.is_file():
        combined += MINIMUM_RELATIVE.read_text(encoding="utf-8")
    named = {name: has_named(combined, name) for name in LEAN_THEOREMS}
    forbidden = {name: has_named(combined, name) for name in FORBIDDEN_THEOREMS}
    paper = JUGGLER_PAPER_BARREL.read_text(encoding="utf-8")
    first_oo = FIRST_INTERNAL_OO.read_text(encoding="utf-8") if FIRST_INTERNAL_OO.is_file() else ""
    shared = MINIMUM_RELATIVE.read_text(encoding="utf-8") if MINIMUM_RELATIVE.is_file() else ""
    cycle_obs = (
        CYCLE_OBSTRUCTIONS.read_text(encoding="utf-8")
        if CYCLE_OBSTRUCTIONS.is_file()
        else ""
    )
    return {
        "sorry_free": "sorry" not in combined
        and "admit" not in combined
        and "sorry" not in first_oo
        and "admit" not in first_oo,
        **named,
        **{f"has_{name}": present for name, present in forbidden.items()},
        "no_global_termination_theorem": "theorem juggler_reaches_one"
        not in combined,
        "not_in_paper_barrel": "FirstInternalOO" not in paper
        and "MinimumRelative" not in paper,
        "length_eight_open_in_census": "Length eight is open"
        in SMALL_CYCLE_CENSUS.read_text(encoding="utf-8"),
        "FloorPower_not_rewritten": "CycleItinerary" not in engine_floor_text(),
        "first_oo_lean": "theorem isolated_oe_ge_implies_exponent" in first_oo
        and "theorem isolatedOddSurvival_bound" in first_oo
        and "theorem aboveAnchor_isolated_two" in shared
        and "theorem no_cycleMin_prefix_ooe_oe" in cycle_obs,
    }


def classify(scan: dict[str, Any], lean: dict[str, bool]) -> dict[str, Any]:
    lean_ok = (
        lean["sorry_free"]
        and lean["CycleMin"]
        and lean["cycleMin_first_even_overshoots"]
        and lean["oe_block_contracts"]
        and lean["repeated_oe_scale"]
        and lean["power_bound_word"]
        and not lean["has_no_cycle_itinerary_length_eleven"]
        and not lean["has_no_cycleMin_four_even"]
        and not lean["has_no_juggler_cycle"]
        and lean["not_in_paper_barrel"]
        and lean["first_oo_lean"]
    )
    if not lean_ok:
        return {"classification": CLASS_INCOMPLETE, "reason": f"lean_ok={lean_ok}"}
    if (
        scan["length_eleven_census"]
        or scan["z5_cells"]
        or scan["four_even_assembler"]
        or scan["leftover_suffix_retest"]
        or scan["terminal_cluster_reopen"]
    ):
        return {"classification": CLASS_INCOMPLETE, "reason": "out-of-scope search"}
    if not scan["r_table"]["matches_table"] or scan["small_power"]["fail"]:
        return {
            "classification": CLASS_REMAINS,
            "reason": "the isolated-OE exponent comparison failed a numeric check",
        }
    window = scan["window"]
    if window["exceed_R"]:
        return {
            "classification": CLASS_REMAINS,
            "reason": "an isolated-OE prefix stayed >= n past R(a0)",
        }
    if window["a0_2_nonzero_r"]:
        return {
            "classification": CLASS_REMAINS,
            "reason": "an a0=2 first-OO event had r >= 1",
        }
    if window["hit_n"]:
        return {
            "classification": CLASS_REMAINS,
            "reason": "a first-OO orbit returned to n in the window",
        }
    witnesses_ok = all(
        (not row.get("missing")) and row.get("within_R")
        for row in scan["r_ge2_witnesses"]
    )
    long_ok = scan["long_stay"].get("matches")
    if not witnesses_ok or not long_ok:
        return {
            "classification": CLASS_INCOMPLETE,
            "reason": "named first-OO witnesses failed",
        }
    return {
        "classification": CLASS_GREEN,
        "reason": (
            "B^r(x1) >= n after O^{a0}E forces 2^{2r+a0+1} <= 3^{a0+r}, "
            "so r <= R(a0) with R(2)=0; the first-OO dichotomy and the "
            "irreversible-surplus claim are not theorems"
        ),
    }


def probe_payload() -> dict[str, Any]:
    scan = run_probe()
    lean = lean_api_present()
    decision = classify(scan, lean)
    anti = dict(ANTI_OVERCLAIM)
    anti.update(
        {
            "cycles_impossible": False,
            "length_eleven_census": False,
            "z5_cells": False,
            "four_even_assembler": False,
        }
    )
    return {
        "experiment": "juggler_first_internal_oo",
        "engine_control_layer_modified": False,
        "anti_overclaim": anti,
        "scan": scan,
        "lean": lean,
        "decision": decision,
        "search_method": (
            "first-OO decomposition O^{a0}E(OE)^r O^b E v; isolated-OE "
            "exponent comparison from power_bound_word and repeated_oe_scale; "
            "forward first-OO geometry on actual orbits; no terminal cell, "
            "no leftover suffix, no Z5, no length-11"
        ),
    }


def render_markdown(payload: dict[str, Any]) -> str:
    decision = payload["decision"]
    scan = payload["scan"]
    lean = payload["lean"]
    window = scan["window"]
    lines = [
        "# Juggler first internal OO after isolated OE transport",
        "",
        f"Status: **{decision['classification']}**",
        "",
        "Standalone application phase. Not a Research Engine experiment",
        "and not a termination theorem. First internal `OO` after",
        "first-even overshoot and isolated `OE` transport; the suffix",
        "after that `OO` is not classified. Not Z5, not a length-11",
        "assembler, and not a terminal-cluster reopen.",
        "",
        "## Branch budget",
        "",
        "```text",
        "Mathematical target     first-even overshoot + isolated OE",
        "                        + first OO => FiniteProgress or",
        "                        existing obstruction, or a bound on r",
        "Novelty hypothesis      first OO creates an irreversible",
        "                        return-cost surplus",
        "Existing machinery      power_bound_word; repeated_oe_scale;",
        "                        first-even overshoot; oe_block_contracts",
        "Maximum Phase-0 scope   first-OO decomposition; r-bound;",
        "                        forward geometry; Lean scale",
        "```",
        "",
        "## Metadata",
        "",
        f"- basin: `{scan['basin']}`",
        f"- engine control layer modified: `{payload['engine_control_layer_modified']}`",
        f"- classification: **{decision['classification']}**",
        f"- sorry-free: `{lean['sorry_free']}`",
        f"- R(a0): `{scan['r_table']['values']}`",
        f"- isolated starts / first-OO events: `{window['iso_starts']}` / `{window['events']}`",
        f"- exceed R: `{window['exceed_R']}`",
        f"- a0=2 events / nonzero r: `{window['a0_2_events']}` / `{window['a0_2_nonzero_r']}`",
        f"- r counts: `{window['r_counts']}`",
        f"- drop below n / stay / hit n: `{window['drop_below_n']}` / `{window['stay']}` / `{window['hit_n']}`",
        f"- OOE landing >= n / < n: `{window['ooe_land_ge_n']}` / `{window['ooe_land_lt_n']}`",
        f"- T^2 > (xj+1)^2 / tight: `{window['t2_strict']}` / `{window['t2_tight']}`",
        f"- x1 even (outside corridor): `{window['x1_even']}`",
        "",
        decision["reason"] + ".",
        "",
        "## Attack 1 — isolated-OE r-bound",
        "",
        "If `O^{a0}E` follows at `n` and `(OE)^r` follows at the",
        "first-even landing `x1`, and `B^r(x1) >= n`, then",
        "`2^{2r+a0+1} <= 3^{a0+r}`. In particular `R(2)=0`:",
        "a CycleMin-shaped `a0=2` prefix cannot complete one `OE`",
        "after the first even while staying `>= n`.",
        "",
        "## Attack 2 — first-OO geometry",
        "",
        f"On odd `13 <= n < {window['n_hi']}` the isolated corridor has",
        f"`{window['events']}` first-OO events, all with `r <= R(a0)`,",
        "all dropping below `n`, none returning to `n`.",
        f"Drop prefixes: `{window['drop_prefix4']}`.",
        "",
        "## Attack 3 — surplus falsifiers",
        "",
        "Immediate kill is false: `n=193` stays 66 steps after its",
        "first `OO`. `OOE` itself lands `>= n` on every `b=2` event",
        "in the window. Families with `r >= 2` exist and still obey",
        "`r <= R(a0)`; `r -> infinity` with `xj >= n` is false.",
        "",
    ]
    if window["samples"]:
        lines.append("## Window samples")
        lines.append("")
        for row in window["samples"]:
            lines.append(
                f"- n=`{row['n']}` a0=`{row['a0']}` r=`{row['r']}` "
                f"b=`{row['b']}` steps=`{row['steps']}` drop=`{row['drop']}`"
            )
        lines.append("")
    lines.append("## Named r>=2 witnesses")
    lines.append("")
    for row in scan["r_ge2_witnesses"]:
        if row.get("missing"):
            lines.append(f"- n=`{row['n']}` missing")
            continue
        lines.append(
            f"- n=`{row['n']}` a0=`{row['a0']}` r=`{row['r']}` b=`{row['b']}` "
            f"xj/n=`{row['xj_over_n']:.3g}` steps=`{row['steps']}` "
            f"drop=`{row['drop']}`"
        )
    lines.extend(["", "## Lean", ""])
    for name in LEAN_THEOREMS:
        lines.append(f"- `{name}`: `{lean[name]}`")
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
            decision["reason"] + ".",
            "",
            "This is not a halt result, not a Z5 exclusion, and not a",
            "length-11 assembler. Terminal clusters stay frozen.",
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
    decision = payload["decision"]
    window = payload["scan"]["window"]
    print(decision["classification"])
    print(decision["reason"])
    print(
        f"events={window['events']} exceed={window['exceed_R']} "
        f"a0_2={window['a0_2_events']} r={window['r_counts']}"
    )


if __name__ == "__main__":
    main()
