"""Exact-floor impact census. Phase 0 only.

Tag every first-descent step where floor is a no-op (the state is a
perfect square) and record its accounted impact. The local package is
already a theorem: exact iff square, crumb 0, next letter equals the
current letter, tower iff the image is a square. This probe asks
whether isolated exact steps bias first-descent class or PE
continuation beyond that package.

Not a halt theorem, not an word-atlas recensus, not a floor-boundary
reopen, and not a Paper A edit.
"""

from __future__ import annotations

import json
from collections import Counter, defaultdict
from math import isqrt
from pathlib import Path
from typing import Any

from research.juggler_sequence.global_defect import local_defect
from research.juggler_sequence.lean_paths import JUGGLER_DIR, has_named, juggler_text
from research.juggler_sequence.power_algebra import is_square, local_tight
from research.juggler_sequence.power_itineraries import ANTI_OVERCLAIM, floor_power
from research.juggler_sequence.residual_chain import residual_excursion
from research.juggler_sequence.saturation_budget import saturation_prefix
from research.juggler_sequence.two_block_residual import classify_step, odd_odd_starts
from research.juggler_sequence.walk_coboundary import leading_drift

REPO_ROOT = Path(__file__).resolve().parents[3]
DATA_DIR = REPO_ROOT / "data" / "research" / "juggler" / "exact_floor_impact"
JSON_PATH = DATA_DIR / "summary.json"
DOC_PATH = REPO_ROOT / "docs" / "research" / "juggler_exact_floor_impact.md"
DOSSIER_PATH = REPO_ROOT / "docs" / "problems" / "juggler_exact_floor_impact.md"

CLASS_KNOWN = "EXACT_FLOOR_IMPACT_KNOWN"
CLASS_BIAS = "EXACT_FLOOR_IMPACT_BIASED"
CLASS_NEW = "EXACT_FLOOR_IMPACT_NEW_LAW"

SCIENCE_N_MAX = 100_000
TEST_N_MAX = 400
STEP_CAP = 40
PE_N_MAX = 4_000
PE_CHAIN_CAP = 6
EVENT_SAMPLE = 40
RATIO_LO = 0.2
RATIO_HI = 5.0
TV_CUT = 0.2

EXISTING_LEAN = (
    "floorPower_even_sq_eq_iff_square",
    "floorPower_odd_sq_eq_cube_iff_square",
    "localDefectEven_eq_zero_iff",
    "localDefectOdd_eq_zero_iff",
    "power_bound_eq_implies_monochrome",
)
FORBIDDEN_THEOREMS = (
    "juggler_reaches_one",
    "no_juggler_escape",
    "all_finiteProgress",
)
NEW_LEAN_FILES = (
    JUGGLER_DIR / "ExactFloorImpact.lean",
    JUGGLER_DIR / "ExactFloorCensus.lean",
)

BINS = (
    (2, 10),
    (10, 100),
    (100, 1_000),
    (1_000, 10_000),
    (10_000, 100_000),
    (100_000, 1_000_000),
    (1_000_000, 10_000_000),
    (10_000_000, 100_000_000),
    (100_000_000, 10**12),
)

def letter_of(n: int) -> str:
    return "O" if n % 2 else "E"


def classify_certificate(word: str) -> str:
    if word == "E":
        return "E"
    if word == "OE":
        return "OE"
    if word == "OOEE":
        return "OOEE"
    return "leftover"


def first_descent_path(n: int, *, step_cap: int = STEP_CAP) -> dict[str, Any]:
    """Walk T until the image drops below the start, or hit step_cap."""

    if n < 2:
        raise ValueError("first_descent_path requires n >= 2")
    states = [n]
    letters: list[str] = []
    current = n
    for _ in range(step_cap):
        letters.append(letter_of(current))
        nxt = floor_power(current)
        states.append(nxt)
        if nxt < n:
            word = "".join(letters)
            return {
                "n": n,
                "states": states,
                "word": word,
                "cls": classify_certificate(word),
                "uncapped": False,
            }
        current = nxt
    word = "".join(letters)
    return {
        "n": n,
        "states": states,
        "word": word,
        "cls": "uncapped",
        "uncapped": True,
    }


def walk_increment(src: int, dst: int) -> float | None:
    if src < 3 or dst < 3:
        return None
    return leading_drift(src, dst)


def exact_event(start: int, index: int, state: int, image: int, *, contracting: bool, cert: str) -> dict[str, Any]:
    crumb = local_defect(state)
    tight = local_tight(state)
    square = is_square(state)
    image_square = is_square(image)
    letter = letter_of(state)
    next_letter = letter_of(image) if image >= 1 else None
    tower = saturation_prefix(state, 8)
    increment = walk_increment(state, image)
    return {
        "start": start,
        "index": index,
        "state": state,
        "image": image,
        "letter": letter,
        "next_letter": next_letter,
        "crumb": crumb,
        "exact": tight,
        "square": square,
        "isolated": tight and not image_square,
        "tower_len": tower["length"],
        "walk_increment": increment,
        "cert": cert,
        "contracting": contracting,
        "letter_forced": next_letter == letter,
        "identity_ok": tight == square and (not tight or crumb == 0),
    }


def fixture_nine() -> dict[str, Any]:
    ev = exact_event(9, 0, 9, 27, contracting=False, cert="leftover")
    ev["path"] = first_descent_path(9)
    return ev


def fixture_thirty_six() -> dict[str, Any]:
    path = first_descent_path(3)
    idx = path["states"].index(36)
    ev = exact_event(3, idx, 36, 6, contracting=False, cert=path["cls"])
    ev["path_word"] = path["word"]
    return ev


def fixture_sixteen() -> dict[str, Any]:
    path = first_descent_path(16)
    ev = exact_event(16, 0, 16, 4, contracting=False, cert=path["cls"])
    ev["path_word"] = path["word"]
    ev["path_states"] = path["states"]
    return ev


def _bin_of(n: int) -> tuple[int, int] | None:
    for lo, hi in BINS:
        if lo <= n < hi:
            return (lo, hi)
    return None


def _parity_squares(lo: int, hi: int, odd: bool) -> int:
    count = 0
    k = isqrt(lo)
    if k * k < lo:
        k += 1
    while k * k < hi:
        if (k % 2 == 1) == odd:
            count += 1
        k += 1
    return count


def _parity_integers(lo: int, hi: int, odd: bool) -> int:
    first = lo if (lo % 2 == 1) == odd else lo + 1
    if first >= hi:
        return 0
    return (hi - 1 - first) // 2 + 1


def _tv(p: dict[str, float], q: dict[str, float]) -> float:
    keys = set(p) | set(q)
    return 0.5 * sum(abs(p.get(k, 0.0) - q.get(k, 0.0)) for k in keys)


def _share(counter: Counter[str]) -> dict[str, float]:
    total = sum(counter.values())
    if total == 0:
        return {}
    return {key: counter[key] / total for key in counter}


def scan_first_descent(*, n_max: int, step_cap: int = STEP_CAP) -> dict[str, Any]:
    visited: dict[str, set[int]] = {"E": set(), "O": set()}
    exact_states: dict[str, set[int]] = {"E": set(), "O": set()}
    mismatches: list[dict[str, Any]] = []
    letter_fail = 0
    walk_fail = 0
    n_exact = 0
    n_isolated = 0
    n_tower = 0
    n_contracting_exact = 0
    e_certs = 0
    e_certs_exact = 0
    class_all: Counter[str] = Counter()
    class_start_square: Counter[str] = Counter()
    class_mid_isolated: Counter[str] = Counter()
    class_none: Counter[str] = Counter()
    class_n: Counter[str] = Counter()
    class_mid_n: Counter[str] = Counter()
    class_len_sum: Counter[str] = Counter()
    mid_by_bin: dict[tuple[int, int], Counter[str]] = defaultdict(Counter)
    none_by_bin: dict[tuple[int, int], Counter[str]] = defaultdict(Counter)
    isolated_sample: list[dict[str, Any]] = []
    uncapped = 0

    for n in range(2, n_max + 1):
        path = first_descent_path(n, step_cap=step_cap)
        if path["uncapped"]:
            uncapped += 1
            continue
        word = path["word"]
        cls = path["cls"]
        states = path["states"]
        class_all[cls] += 1
        class_n[cls] += 1
        class_len_sum[cls] += len(word)
        if cls == "E":
            e_certs += 1
            if is_square(n):
                e_certs_exact += 1
        start_square = is_square(n)
        saw_mid_isolated = False
        last = len(states) - 2
        for index in range(last + 1):
            state = states[index]
            image = states[index + 1]
            letter = letter_of(state)
            visited[letter].add(state)
            tight = local_tight(state)
            square = is_square(state)
            crumb = local_defect(state)
            if tight != square or (tight and crumb != 0):
                mismatches.append({"n": n, "state": state, "tight": tight, "square": square, "crumb": crumb})
            if not tight:
                continue
            n_exact += 1
            exact_states[letter].add(state)
            image_square = is_square(image)
            isolated = not image_square
            if isolated:
                n_isolated += 1
                if not start_square:
                    saw_mid_isolated = True
                if len(isolated_sample) < EVENT_SAMPLE:
                    isolated_sample.append(
                        exact_event(
                            n,
                            index,
                            state,
                            image,
                            contracting=image < n,
                            cert=cls,
                        )
                    )
            else:
                n_tower += 1
            if letter_of(image) != letter:
                letter_fail += 1
            increment = walk_increment(state, image)
            if letter == "E" and state >= 16 and increment is not None and increment != -1.0:
                walk_fail += 1
            if image < n:
                n_contracting_exact += 1
        if start_square:
            class_start_square[cls] += 1
        elif saw_mid_isolated:
            class_mid_n[cls] += 1
            class_mid_isolated[cls] += 1
            if n % 2 == 1:
                bucket = _bin_of(n)
                if bucket is not None:
                    mid_by_bin[bucket][cls] += 1
        else:
            class_none[cls] += 1
            if n % 2 == 1:
                bucket = _bin_of(n)
                if bucket is not None:
                    none_by_bin[bucket][cls] += 1

    density_rows: list[dict[str, Any]] = []
    density_ok = True
    for lo, hi in BINS:
        for odd, letter in ((False, "E"), (True, "O")):
            visited_here = [x for x in visited[letter] if lo <= x < hi]
            exact_here = [x for x in exact_states[letter] if lo <= x < hi]
            n_vis = len(visited_here)
            n_ex = len(exact_here)
            lo_v = min(visited_here) if visited_here else lo
            hi_v = max(visited_here) + 1 if visited_here else hi
            n_ints = _parity_integers(lo, hi, odd)
            n_sq = _parity_squares(lo, hi, odd)
            expected = sum(x**-0.5 for x in visited_here) if visited_here else None
            baseline = (expected / n_vis) if n_vis and expected is not None else None
            observed = (n_ex / n_vis) if n_vis else None
            ratio = (
                (n_ex / expected)
                if expected not in (None, 0.0)
                else None
            )
            row_ok = True
            if n_vis >= 50 and ratio is not None and expected is not None:
                if expected < 5.0:
                    sigma = expected**0.5
                    row_ok = n_ex <= expected + 3.0 * sigma + 1.0
                else:
                    row_ok = RATIO_LO <= ratio <= RATIO_HI
                density_ok = density_ok and row_ok
            density_rows.append(
                {
                    "lo": lo,
                    "hi": hi,
                    "lo_visited": lo_v,
                    "hi_visited": hi_v,
                    "letter": letter,
                    "n_visited": n_vis,
                    "n_exact": n_ex,
                    "n_integers": n_ints,
                    "n_squares": n_sq,
                    "baseline": baseline,
                    "observed": observed,
                    "ratio": ratio,
                    "expected": expected,
                    "ok": row_ok,
                }
            )

    e_baseline = (
        _parity_squares(2, n_max + 1, False) / max(1, (n_max // 2))
    )
    e_observed = (e_certs_exact / e_certs) if e_certs else None
    e_ratio = (
        (e_observed / e_baseline)
        if e_observed is not None and e_baseline
        else None
    )
    e_ok = e_ratio is not None and RATIO_LO <= e_ratio <= RATIO_HI

    odd_mid = Counter({k: v for k, v in class_mid_isolated.items() if k != "E"})
    odd_none = Counter({k: v for k, v in class_none.items() if k != "E"})
    mid_share = _share(odd_mid)
    none_share = _share(odd_none)
    tv_global = _tv(mid_share, none_share) if mid_share and none_share else 0.0
    rate_rows: list[dict[str, Any]] = []
    for cls in ("E", "OE", "OOEE", "leftover"):
        n_cls = class_n[cls]
        n_mid = class_mid_n[cls]
        mean_len = (class_len_sum[cls] / n_cls) if n_cls else 0.0
        rate_rows.append(
            {
                "cls": cls,
                "n": n_cls,
                "n_mid": n_mid,
                "rate": (n_mid / n_cls) if n_cls else 0.0,
                "mean_len": mean_len,
            }
        )
    by_cls = {row["cls"]: row for row in rate_rows}
    e_rate = by_cls["E"]["rate"]
    oe_rate = by_cls["OE"]["rate"]
    long_rate = max(by_cls["OOEE"]["rate"], by_cls["leftover"]["rate"])
    rates_follow_length = e_rate == 0.0 and oe_rate <= long_rate + 1e-12
    bin_tvs: list[dict[str, Any]] = []
    tv_ok = True
    for lo, hi in BINS:
        mid_c = mid_by_bin.get((lo, hi), Counter())
        none_c = none_by_bin.get((lo, hi), Counter())
        if sum(mid_c.values()) < 8 or sum(none_c.values()) < 8:
            continue
        tv = _tv(_share(mid_c), _share(none_c))
        ok = tv <= TV_CUT
        tv_ok = tv_ok and ok
        bin_tvs.append(
            {
                "lo": lo,
                "hi": hi,
                "n_mid": sum(mid_c.values()),
                "n_none": sum(none_c.values()),
                "tv": tv,
                "ok": ok,
                "mid": dict(mid_c),
                "none": dict(none_c),
            }
        )

    identity_ok = not mismatches and letter_fail == 0 and walk_fail == 0
    return {
        "n_max": n_max,
        "step_cap": step_cap,
        "n_starts": n_max - 1,
        "uncapped": uncapped,
        "n_exact_events": n_exact,
        "n_isolated": n_isolated,
        "n_tower": n_tower,
        "n_contracting_exact": n_contracting_exact,
        "n_visited_even": len(visited["E"]),
        "n_visited_odd": len(visited["O"]),
        "identity_ok": identity_ok,
        "n_mismatches": len(mismatches),
        "letter_fail": letter_fail,
        "walk_fail": walk_fail,
        "density": density_rows,
        "density_ok": density_ok,
        "e_certs": e_certs,
        "e_certs_exact": e_certs_exact,
        "e_baseline": e_baseline,
        "e_observed": e_observed,
        "e_ratio": e_ratio,
        "e_ok": e_ok,
        "class_all": dict(class_all),
        "class_start_square": dict(class_start_square),
        "class_mid_isolated": dict(class_mid_isolated),
        "class_none": dict(class_none),
        "tv_global": tv_global,
        "bin_tvs": bin_tvs,
        "rate_by_class": rate_rows,
        "rates_follow_length": rates_follow_length,
        "tv_ok": tv_ok or rates_follow_length,
        "isolated_sample": isolated_sample,
    }


def _pe_block_states(x: int, y: int, *, cap: int = 64) -> list[int]:
    path = [x]
    current = x
    for _ in range(cap):
        if current == y:
            return path
        current = floor_power(current)
        path.append(current)
    return path


def pe_census(*, n_max: int = PE_N_MAX, chain_cap: int = PE_CHAIN_CAP) -> dict[str, Any]:
    n_pe = 0
    n_exact = 0
    extra = 0
    not_square = 0
    hits: list[dict[str, Any]] = []
    seen: set[int] = set()
    for x in odd_odd_starts(n_max):
        current = x
        ran = False
        for _ in range(chain_cap):
            if current in seen or current <= 1:
                break
            raw = residual_excursion(current)
            if raw is None:
                break
            row = classify_step(current, raw)
            if not (row["persistent"] and row["expanding"]):
                break
            ran = True
            seen.add(current)
            y = row["y"]
            path = _pe_block_states(current, y)
            for state, image in zip(path[:-1], path[1:]):
                if not local_tight(state):
                    continue
                n_exact += 1
                root = isqrt(state)
                if not is_square(state):
                    not_square += 1
                expected = root * root * root if state % 2 else root
                if image != expected:
                    extra += 1
                if len(hits) < EVENT_SAMPLE:
                    hits.append(
                        {
                            "pe_start": x,
                            "state": state,
                            "image": image,
                            "expected": expected,
                            "odd": state % 2 == 1,
                            "square": is_square(state),
                            "block": row["word"],
                        }
                    )
            current = y
        if ran:
            n_pe += 1
    continuation_ok = extra == 0 and not_square == 0
    return {
        "n_max": n_max,
        "n_pe_starts": n_pe,
        "n_exact_hits": n_exact,
        "not_square": not_square,
        "extra_continuation": extra,
        "continuation_ok": continuation_ok,
        "hits": hits,
    }


def lean_api_present() -> dict[str, Any]:
    text = juggler_text()
    return {
        **{name: has_named(text, name) for name in EXISTING_LEAN},
        "sorry_free": "sorry" not in text and "admit" not in text,
        "new_lean_file": any(path.exists() for path in NEW_LEAN_FILES),
        **{f"has_{name}": has_named(text, name) for name in FORBIDDEN_THEOREMS},
    }


def anti_overclaim() -> dict[str, Any]:
    return {
        "halt_theorem": False,
        "paper_a_modified": False,
        "n0_raised": False,
        "atlas_recensus": False,
        "floor_boundary_reopened": False,
        "new_lean_file": False,
        "companion_edited": False,
        "global_termination": dict(ANTI_OVERCLAIM)["global_termination"],
    }


def classify(summary: dict[str, Any]) -> str:
    descent = summary["descent"]
    pe = summary["pe"]
    lean = summary["lean"]
    local_ok = (
        descent["identity_ok"]
        and descent["density_ok"]
        and descent["e_ok"]
        and descent["tv_ok"]
        and pe["continuation_ok"]
        and lean["localDefectEven_eq_zero_iff"]
        and not lean["new_lean_file"]
    )
    if local_ok:
        return CLASS_KNOWN
    if descent["identity_ok"] and pe["continuation_ok"]:
        return CLASS_BIAS
    return CLASS_NEW


def build_summary(*, n_max: int = SCIENCE_N_MAX, pe_n_max: int = PE_N_MAX) -> dict[str, Any]:
    descent = scan_first_descent(n_max=n_max)
    pe = pe_census(n_max=pe_n_max)
    fixtures = {
        "nine": fixture_nine(),
        "thirty_six": fixture_thirty_six(),
        "sixteen": fixture_sixteen(),
    }
    summary: dict[str, Any] = {
        "experiment": "juggler_exact_floor_impact",
        "anti_overclaim": anti_overclaim(),
        "fixtures": {
            "nine": {
                "state": fixtures["nine"]["state"],
                "image": fixtures["nine"]["image"],
                "letter": fixtures["nine"]["letter"],
                "next_letter": fixtures["nine"]["next_letter"],
                "crumb": fixtures["nine"]["crumb"],
                "isolated": fixtures["nine"]["isolated"],
                "word": fixtures["nine"]["path"]["word"],
            },
            "thirty_six": {
                "state": fixtures["thirty_six"]["state"],
                "image": fixtures["thirty_six"]["image"],
                "letter": fixtures["thirty_six"]["letter"],
                "next_letter": fixtures["thirty_six"]["next_letter"],
                "crumb": fixtures["thirty_six"]["crumb"],
                "isolated": fixtures["thirty_six"]["isolated"],
                "start_word": fixtures["thirty_six"]["path_word"],
            },
            "sixteen": {
                "state": fixtures["sixteen"]["state"],
                "image": fixtures["sixteen"]["image"],
                "letter": fixtures["sixteen"]["letter"],
                "isolated": fixtures["sixteen"]["isolated"],
                "tower_len": fixtures["sixteen"]["tower_len"],
                "path_states": fixtures["sixteen"]["path_states"],
            },
        },
        "descent": descent,
        "pe": pe,
        "lean": lean_api_present(),
    }
    summary["classification"] = classify(summary)
    return summary


def _fmt_pct(value: float | None) -> str:
    if value is None:
        return "n/a"
    return f"{100.0 * value:.3f}%"


def write_research_note(summary: dict[str, Any]) -> None:
    descent = summary["descent"]
    pe = summary["pe"]
    lines = [
        "# Juggler exact-floor impact",
        "",
        "Phase-0 census of first-descent steps where the Juggler floor is a",
        "no-op because the state is already an integer power (a perfect",
        "square). Local exactness is the existing square package. This note",
        "records the tagged events and their measured impact.",
        "",
        f"Classification **{summary['classification']}**.",
        "",
        "## Bounds",
        "",
        f"- First-descent starts n <= {descent['n_max']}, step cap {descent['step_cap']}.",
        f"- PE subsample odd-odd n <= {pe['n_max']}.",
        "- No GPU. No word-atlas recensus. No new Lean. No Paper A edit.",
        "",
        "## Fixtures",
        "",
        "- 9 -> 27: exact O, crumb 0, next letter O, isolated (27 is not a square).",
        "- Orbit of 3: isolated exact E at 36, image 6, word `OOOEE`.",
        "- 16 -> 4 -> 2 -> 1: even tower, start not isolated.",
        "",
        "## Identity",
        "",
        f"- mismatches: `{descent['n_mismatches']}`",
        f"- letter-force failures: `{descent['letter_fail']}`",
        f"- even-square walk increment failures: `{descent['walk_fail']}`",
        f"- exact events: `{descent['n_exact_events']}` "
        f"(isolated `{descent['n_isolated']}`, tower `{descent['n_tower']}`)",
        "",
        "## Density versus square baseline",
        "",
        "| bin | letter | visited | exact | observed | baseline | ratio | ok |",
        "|---|---|---|---|---|---|---|---|",
    ]
    for row in descent["density"]:
        if row["n_visited"] == 0:
            continue
        ratio = "n/a" if row["ratio"] is None else f"{row['ratio']:.3f}"
        observed = _fmt_pct(row["observed"])
        baseline = _fmt_pct(row["baseline"])
        lines.append(
            f"| [{row['lo']},{row['hi']}) | {row['letter']} | {row['n_visited']} | "
            f"{row['n_exact']} | {observed} | {baseline} | {ratio} | {row['ok']} |"
        )
    lines.extend(
        [
            "",
            "## First-descent impact",
            "",
            f"- E-certificates: `{descent['e_certs']}` with exact descending even "
            f"`{descent['e_certs_exact']}` (observed {_fmt_pct(descent['e_observed'])}, "
            f"baseline {_fmt_pct(descent['e_baseline'])}, ratio "
            f"{descent['e_ratio'] if descent['e_ratio'] is None else f'{descent['e_ratio']:.3f}'})",
            f"- class mix, start is a square: `{descent['class_start_square']}`",
            f"- class mix, mid-path isolated exact: `{descent['class_mid_isolated']}`",
            f"- class mix, no isolated exact: `{descent['class_none']}`",
            f"- mid-isolated rate by class: `{descent['rate_by_class']}`",
            f"- rates follow word length: `{descent['rates_follow_length']}`",
            f"- global TV (odd mid vs none): `{descent['tv_global']:.4f}`",
            "",
        ]
    )
    if descent["bin_tvs"]:
        lines.extend(
            [
                "| bin | n_mid | n_none | TV | ok |",
                "|---|---|---|---|---|",
            ]
        )
        for row in descent["bin_tvs"]:
            lines.append(
                f"| [{row['lo']},{row['hi']}) | {row['n_mid']} | {row['n_none']} | "
                f"{row['tv']:.4f} | {row['ok']} |"
            )
        lines.append("")
    lines.extend(
        [
            "## PE subsample",
            "",
            f"- PE starts: `{pe['n_pe_starts']}`",
            f"- exact hits on PE blocks: `{pe['n_exact_hits']}`",
            f"- not-square exact hits: `{pe['not_square']}`",
            f"- extra continuation (image ≠ cube / root): `{pe['extra_continuation']}`",
            "",
            "## Decision cue",
            "",
            "Local identity, square-density ratios, E-certificate exact share,",
            "size-matched mid-path class TV, and PE continuation all sit inside",
            "the known package if classification is `EXACT_FLOOR_IMPACT_KNOWN`.",
            "",
        ]
    )
    DOC_PATH.write_text("\n".join(lines) + "\n", encoding="utf-8")


def main(*, n_max: int = SCIENCE_N_MAX, pe_n_max: int = PE_N_MAX) -> dict[str, Any]:
    summary = build_summary(n_max=n_max, pe_n_max=pe_n_max)
    DATA_DIR.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(summary, indent=2) + "\n", encoding="utf-8")
    write_research_note(summary)
    print(summary["classification"])
    d = summary["descent"]
    print("identity_ok", d["identity_ok"], "density_ok", d["density_ok"], "e_ok", d["e_ok"], "tv_ok", d["tv_ok"])
    print("exact", d["n_exact_events"], "isolated", d["n_isolated"], "tower", d["n_tower"])
    print("e_certs", d["e_certs"], "e_exact", d["e_certs_exact"], "ratio", d["e_ratio"])
    print("tv_global", d["tv_global"], "bin_tvs", len(d["bin_tvs"]))
    pe = summary["pe"]
    print("pe", pe["n_pe_starts"], "exact", pe["n_exact_hits"], "ok", pe["continuation_ok"])
    return summary


if __name__ == "__main__":
    main()
