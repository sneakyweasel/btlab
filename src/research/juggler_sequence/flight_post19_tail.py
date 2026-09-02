"""Post-19 tails: walk-height overshoot versus descent.

Not a halt theorem, not a divergence exclusion, not a glue reopen,
not a CF census, and not a Paper A edit.

A length-19 AboveAnchor prefix has o >= hugOdds(19) = 12 (Lean
aboveAnchor_prefix_odds_ge_hug). The envelope gives
delta <= o log2(3) - 19 (follows_log_le_walkWeight). Hence o = 12
forces delta <= theta_19 < 0.05: a 19-near-return. Contrapositive:

    a length->=19 post-19 tail misses R_0.05 at t=19
    iff o >= 13 and delta > 0.05.

So a long miss is a walk-height overshoot, not a short descent.
Phase-0 checks that split on the existing fan-concat witnesses
(n <= 2000 and the seven high-flyers). No new n-window.
"""

from __future__ import annotations

import json
from typing import Any

from research.juggler_sequence.flight_divergent_structure import (
    HIGH_FLYERS,
    _hug_table,
    _log2_big,
    trajectory,
)
from research.juggler_sequence.flight_fan_concat import (
    FAN_LENGTHS,
    _delta,
    _segment_end,
    _word,
    classify_orbit,
    hug_letters,
)
from research.juggler_sequence.flight_return_quantization import (
    LOG2_3,
    NEAR_RETURN_EPS,
    WINDOW,
    return_set,
    theta_p,
)

REPO_ROOT = __import__("pathlib").Path(__file__).resolve().parents[3]
DATA_DIR = REPO_ROOT / "data" / "research" / "juggler" / "flight_post19_tail"
JSON_PATH = DATA_DIR / "summary.json"

FLOAT_TOL = 1e-12

CLASS_SPLIT_CONFIRMED = "POST19_TAIL_SPLIT_CONFIRMED"
CLASS_SPLIT_VIOLATED = "POST19_TAIL_SPLIT_VIOLATED"


def first_hug_split(word: str, hug: str) -> int | None:
    """1-based first letter where word leaves the hug prefix, or None."""

    for k, (a, b) in enumerate(zip(word, hug), start=1):
        if a != b:
            return k
    return None


def tail_scan(xs: list[int], end_idx: int, r05: list[int]) -> dict[str, Any]:
    """Walk-height profile of the AboveAnchor tail starting at end_idx."""

    logs = [_log2_big(x) if x > 0 else 0.0 for x in xs]
    par = [x % 2 for x in xs]
    last = _segment_end(xs, logs, end_idx)
    next_len = last - end_idx
    hug = _hug_table(max(next_len, 19))
    word = _word(xs, end_idx, next_len) if next_len else ""
    hug_pref = hug_letters(next_len) if next_len else ""
    at: list[dict[str, Any]] = []
    odds = 0
    for t in range(1, next_len + 1):
        odds += par[end_idx + t - 1]
        if t not in r05:
            continue
        delta = _delta(logs, end_idx, t)
        hug_o = hug[t]
        at.append(
            {
                "t": t,
                "o": odds,
                "hug_o": hug_o,
                "theta": round(odds * LOG2_3 - t, 9),
                "delta": round(delta, 9),
                "overshoot": odds > hug_o,
                "near_return": delta <= NEAR_RETURN_EPS + FLOAT_TOL,
            }
        )
    o19 = None
    d19 = None
    if next_len >= 19:
        o19 = sum(par[end_idx : end_idx + 19])
        d19 = round(_delta(logs, end_idx, 19), 9)
    if next_len == 0:
        kind = "dies_immediately"
    elif next_len < 19:
        kind = "dies_before_19"
    elif o19 is not None and o19 == 12:
        kind = "hug_minimal_19"
    else:
        kind = "overshoot"
    return {
        "next_len": next_len,
        "kind": kind,
        "o19": o19,
        "delta19": d19,
        "first_hug_split": first_hug_split(word, hug_pref) if word else None,
        "next_word19": word[:19],
        "at_r05": at,
    }


def _nineteen_events(xs: list[int], r05: frozenset[int]) -> list[dict[str, Any]]:
    return [e for e in classify_orbit(xs, r05)["events"] if e["p"] == 19]


def profile_starts(starts: list[int], r05_list: list[int]) -> list[dict[str, Any]]:
    r05 = frozenset(r05_list)
    rows: list[dict[str, Any]] = []
    for n in starts:
        xs = trajectory(n)
        for event in _nineteen_events(xs, r05):
            if event["p"] not in FAN_LENGTHS:
                continue
            scan = tail_scan(xs, event["i"] + event["p"], r05_list)
            rows.append(
                {
                    "n": n,
                    "i": event["i"],
                    "end_odd": event["end_odd"],
                    "end_is_tail_record": event["end_is_tail_record"],
                    **scan,
                }
            )
    return rows


def _tally(rows: list[dict[str, Any]]) -> dict[str, Any]:
    kinds: dict[str, int] = {}
    for row in rows:
        kinds[row["kind"]] = kinds.get(row["kind"], 0) + 1
    long_rows = [r for r in rows if r["next_len"] >= 19]
    ge3 = [r for r in rows if r["next_len"] >= 3]
    splits = sorted(
        {r["first_hug_split"] for r in long_rows if r["first_hug_split"] is not None}
    )
    split_ge3: dict[str, int] = {}
    for r in ge3:
        key = str(r["first_hug_split"])
        split_ge3[key] = split_ge3.get(key, 0) + 1
    o19s = sorted({r["o19"] for r in long_rows if r["o19"] is not None})
    lemma_ok = all(
        (r["o19"] or 0) >= 13
        and r["delta19"] is not None
        and r["delta19"] > NEAR_RETURN_EPS
        and not any(hit["near_return"] for hit in r["at_r05"])
        for r in long_rows
    )
    hug_minimal = sum(1 for r in long_rows if r["kind"] == "hug_minimal_19")
    return {
        "n19": len(rows),
        "kinds": kinds,
        "long": len(long_rows),
        "o19_on_long": o19s,
        "first_hug_split_on_long": splits,
        "n_ge3": len(ge3),
        "first_hug_split_ge3": split_ge3,
        "hug_minimal_19": hug_minimal,
        "lemma_holds_on_long": lemma_ok or len(long_rows) == 0,
        "long_witnesses": [
            {
                "n": r["n"],
                "next_len": r["next_len"],
                "kind": r["kind"],
                "o19": r["o19"],
                "delta19": r["delta19"],
                "first_hug_split": r["first_hug_split"],
                "next_word19": r["next_word19"],
                "at_r05": r["at_r05"],
            }
            for r in long_rows
        ],
    }


def classify(summary: dict[str, Any]) -> str:
    wt = summary["window"]["tally"]
    ft = summary["flyers"]["tally"]
    ok = (
        wt["lemma_holds_on_long"]
        and ft["lemma_holds_on_long"]
        and wt["hug_minimal_19"] == 0
        and ft["hug_minimal_19"] == 0
        and wt["long"] == 1
        and ft["long"] == 1
        and "overshoot" in wt["kinds"]
        and "overshoot" in ft["kinds"]
        and "dies_immediately" in wt["kinds"]
    )
    return CLASS_SPLIT_CONFIRMED if ok else CLASS_SPLIT_VIOLATED


def build_summary(n_max: int = WINDOW) -> dict[str, Any]:
    r05 = return_set(250, 0.05)
    window_rows = profile_starts(list(range(2, n_max + 1)), r05)
    flyer_rows = profile_starts(list(HIGH_FLYERS), r05)
    summary: dict[str, Any] = {
        "experiment": "juggler_flight_post19_tail",
        "anti_overclaim": {
            "halt_theorem": False,
            "divergence_excluded": False,
            "divergent_orbit_exists": False,
            "overshoot_forced": False,
            "glue_reopened": False,
            "n_window_raised": False,
            "paper_a_modified": False,
        },
        "theta_19": round(theta_p(19), 9),
        "hug19": hug_letters(19),
        "lemma": (
            "AboveAnchor length 19 implies o >= 12; o = 12 implies "
            "delta <= theta_19 < 0.05. A long post-19 miss is "
            "therefore o >= 13 and delta > 0.05 (overshoot), not "
            "a descent before length 19."
        ),
        "window": {"n_max": n_max, "tally": _tally(window_rows)},
        "flyers": {"starts": list(HIGH_FLYERS), "tally": _tally(flyer_rows)},
    }
    summary["classification"] = classify(summary)
    return summary


def main() -> dict[str, Any]:
    summary = build_summary()
    DATA_DIR.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(summary, indent=2) + "\n", encoding="utf-8")
    wt = summary["window"]["tally"]
    ft = summary["flyers"]["tally"]
    print(f"lemma: {summary['lemma']}")
    print(
        f"window kinds={wt['kinds']} ge3_splits={wt['first_hug_split_ge3']} "
        f"long={wt['long_witnesses']}"
    )
    print(
        f"flyers kinds={ft['kinds']} ge3_splits={ft['first_hug_split_ge3']} "
        f"long={ft['long_witnesses']}"
    )
    print(summary["classification"])
    return summary


if __name__ == "__main__":
    main()
