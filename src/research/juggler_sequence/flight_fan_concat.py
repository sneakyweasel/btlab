"""Fan-block concatenability: local glue of shortest positive-θ blocks.

Not a halt theorem, not a divergence exclusion, not a claim that any
divergent flight exists, not a CF fan census, and not a reopen of
record composition, mechanical lift, expanding-residual concat,
hug-cylinder C_L, or Paper A.

Phase-0 question: after a realized record segment of shortest fan
type (p, o) = (19, 12), can the terminal state launch another R_ε
fan block as a subsequent record segment — or is there a local
launch obstruction?

Windows only: the return-quantization census n <= 2000, plus the
seven canonical high-flyer ascent prefixes. No new n-window.
"""

from __future__ import annotations

import json
import math
from typing import Any

from research.juggler_sequence.flight_divergent_structure import (
    HIGH_FLYERS,
    _hug_table,
    _log2_big,
    trajectory,
)
from research.juggler_sequence.flight_return_quantization import (
    LOG2_3,
    MIN_ANCHOR,
    NEAR_RETURN_EPS,
    WINDOW,
    return_set,
    theta_p,
)

REPO_ROOT = __import__("pathlib").Path(__file__).resolve().parents[3]
DATA_DIR = REPO_ROOT / "data" / "research" / "juggler" / "flight_fan_concat"
JSON_PATH = DATA_DIR / "summary.json"

LN2 = math.log(2.0)
FLOAT_TOL = 1e-12
FAN_LENGTHS = (19, 38)
FLYER_WITNESS_CAP = 12

CLASS_GLUE_LIVE = "FAN_CONCAT_GLUE_LIVE"
CLASS_NO_GLUE = "FAN_CONCAT_NO_GLUE"
CLASS_EVEN_TERMINAL = "FAN_CONCAT_EVEN_TERMINAL"


def hug_letters(depth: int) -> str:
    """Hug word of length `depth` from the incremental hugOdds table."""

    hug = _hug_table(depth)
    return "".join("O" if hug[k + 1] > hug[k] else "E" for k in range(depth))


def _word(xs: list[int], start: int, length: int) -> str:
    return "".join("O" if xs[start + k] % 2 else "E" for k in range(length))


def _hamming(word: str, hug: str) -> int:
    return sum(a != b for a, b in zip(word, hug))


def _dip(xs: list[int], logs: list[float], i: int, j: int) -> bool:
    """True if xs[j] has left the AboveAnchor segment of xs[i]."""

    if logs[j] < logs[i] - 1e-12:
        return True
    if logs[j] < logs[i] + 1e-12 and xs[j] < xs[i]:
        return True
    return False


def _segment_end(xs: list[int], logs: list[float], i: int) -> int:
    """Last index of the AboveAnchor segment starting at i (inclusive)."""

    last = i
    for j in range(i, len(xs) - 1):
        if _dip(xs, logs, i, j + 1):
            break
        last = j + 1
    return last


def _delta(logs: list[float], i: int, t: int) -> float:
    if logs[i] <= 0.0 or logs[i + t] <= 0.0:
        return 0.0
    ratio = logs[i + t] / logs[i]
    if ratio <= 0.0:
        return 0.0
    return math.log2(ratio)


def _tail_record(xs: list[int], start: int, stop: int) -> bool:
    """xs[start] is a minimum on xs[start:stop+1]."""

    m = xs[start]
    for j in range(start, stop + 1):
        if xs[j] < m:
            return False
    return True


def _near_returns_from(
    xs: list[int],
    logs: list[float],
    par: list[int],
    i: int,
    last: int,
    lengths: frozenset[int],
) -> list[tuple[int, float, int]]:
    """Near-returns (t, delta, odds) from anchor i, t in `lengths`."""

    out: list[tuple[int, float, int]] = []
    odds = 0
    max_t = last - i
    for t in range(1, max_t + 1):
        odds += par[i + t - 1]
        if t not in lengths:
            continue
        delta = _delta(logs, i, t)
        if delta <= NEAR_RETURN_EPS + FLOAT_TOL:
            out.append((t, delta, odds))
    return out


def classify_orbit(xs: list[int], r05: frozenset[int]) -> dict[str, Any]:
    """Glue table for one trajectory. Same anchors as the quantization census."""

    logs = [_log2_big(x) if x > 0 else 0.0 for x in xs]
    par = [x % 2 for x in xs]
    hug19 = hug_letters(19)
    hug38 = hug_letters(38)
    hugs = {19: hug19, 38: hug38}
    events: list[dict[str, Any]] = []

    for i in range(len(xs) - 1):
        if xs[i] < MIN_ANCHOR:
            continue
        last = _segment_end(xs, logs, i)
        if last <= i:
            continue
        for t, delta, odds in _near_returns_from(
            xs, logs, par, i, last, frozenset(FAN_LENGTHS)
        ):
            end_idx = i + t
            end = xs[end_idx]
            word = _word(xs, i, t)
            hug = hugs[t]
            end_is_tail_record = _tail_record(xs, end_idx, last)
            next_last = _segment_end(xs, logs, end_idx) if end_idx < len(xs) - 1 else end_idx
            next_len = next_last - end_idx
            next_nrs = (
                _near_returns_from(xs, logs, par, end_idx, next_last, r05)
                if next_len > 0
                else []
            )
            next_near_p = next_nrs[0][0] if next_nrs else None
            next_near_theta = (
                round(next_nrs[0][2] * LOG2_3 - next_nrs[0][0], 9) if next_nrs else None
            )
            next_letter = "O" if end % 2 else "E"
            factors = None
            if t == 38:
                mid = i + 19
                d19 = _delta(logs, i, 19)
                d2 = _delta(logs, mid, 19) if mid + 19 <= last else math.inf
                mid_record = mid <= last and _tail_record(xs, mid, end_idx)
                o19 = sum(par[i : i + 19])
                first19_nr = d19 <= NEAR_RETURN_EPS + FLOAT_TOL and o19 >= 1
                second19_nr = d2 <= NEAR_RETURN_EPS + FLOAT_TOL
                factors = bool(first19_nr and mid_record and second19_nr)
            events.append(
                {
                    "i": i,
                    "anchor": xs[i],
                    "anchor_bits": xs[i].bit_length(),
                    "p": t,
                    "o": odds,
                    "theta": round(odds * LOG2_3 - t, 9),
                    "hug_theta": round(theta_p(t), 9),
                    "delta": round(delta, 9),
                    "word": word,
                    "is_hug": word == hug,
                    "hamming_hug": _hamming(word, hug),
                    "end": end,
                    "end_bits": end.bit_length(),
                    "end_odd": end % 2 == 1,
                    "end_is_tail_record": end_is_tail_record,
                    "formal_r05_launchable": end % 2 == 1,
                    "next_letter": next_letter,
                    "next_segment_len": next_len,
                    "next_near_p": next_near_p,
                    "next_near_theta": next_near_theta,
                    "glue_19_to_19": t == 19
                    and end_is_tail_record
                    and next_near_p == 19,
                    "glue_19_to_38": t == 19
                    and end_is_tail_record
                    and next_near_p == 38,
                    "glue_19_to_r05": t == 19
                    and end_is_tail_record
                    and next_near_p is not None,
                    "factors_19_19": factors,
                }
            )
    return {"events": events}


def _compact(event: dict[str, Any], n: int) -> dict[str, Any]:
    """Drop huge integer payloads; keep glue-relevant fields."""

    row = {
        "n": n,
        "i": event["i"],
        "anchor_bits": event["anchor_bits"],
        "p": event["p"],
        "o": event["o"],
        "theta": event["theta"],
        "delta": event["delta"],
        "word": event["word"],
        "is_hug": event["is_hug"],
        "hamming_hug": event["hamming_hug"],
        "end_bits": event["end_bits"],
        "end_odd": event["end_odd"],
        "end_is_tail_record": event["end_is_tail_record"],
        "formal_r05_launchable": event["formal_r05_launchable"],
        "next_letter": event["next_letter"],
        "next_segment_len": event["next_segment_len"],
        "next_near_p": event["next_near_p"],
        "next_near_theta": event["next_near_theta"],
        "glue_19_to_19": event["glue_19_to_19"],
        "glue_19_to_38": event["glue_19_to_38"],
        "glue_19_to_r05": event["glue_19_to_r05"],
        "factors_19_19": event["factors_19_19"],
    }
    if event["anchor_bits"] <= 53:
        row["anchor"] = event["anchor"]
        row["end"] = event["end"]
    return row


def _tally(events: list[dict[str, Any]]) -> dict[str, Any]:
    n19 = [e for e in events if e["p"] == 19]
    n38 = [e for e in events if e["p"] == 38]
    return {
        "n19": len(n19),
        "n38": len(n38),
        "hug19": sum(1 for e in n19 if e["is_hug"]),
        "hug38": sum(1 for e in n38 if e["is_hug"]),
        "end_odd_19": sum(1 for e in n19 if e["end_odd"]),
        "end_odd_38": sum(1 for e in n38 if e["end_odd"]),
        "tail_record_19": sum(1 for e in n19 if e["end_is_tail_record"]),
        "tail_record_38": sum(1 for e in n38 if e["end_is_tail_record"]),
        "formal_launchable_19": sum(1 for e in n19 if e["formal_r05_launchable"]),
        "glue_19_to_19": sum(1 for e in n19 if e["glue_19_to_19"]),
        "glue_19_to_38": sum(1 for e in n19 if e["glue_19_to_38"]),
        "glue_19_to_r05": sum(1 for e in n19 if e["glue_19_to_r05"]),
        "factors_19_19": sum(1 for e in n38 if e["factors_19_19"]),
        "odd_counts_19": sorted({e["o"] for e in n19}),
        "odd_counts_38": sorted({e["o"] for e in n38}),
        "next_near_p_19": sorted(
            {e["next_near_p"] for e in n19 if e["next_near_p"] is not None}
        ),
        "next_segment_lens_19": sorted({e["next_segment_len"] for e in n19}),
        "next_len_zero_19": sum(1 for e in n19 if e["next_segment_len"] == 0),
        "next_len_ge19_19": sum(1 for e in n19 if e["next_segment_len"] >= 19),
        "min_hamming_19": min((e["hamming_hug"] for e in n19), default=None),
        "long_tails_19": [
            {"n": e["n"], "next_segment_len": e["next_segment_len"]}
            for e in n19
            if e["next_segment_len"] >= 19 and e.get("n") is not None
        ],
    }


def window_census(n_max: int = WINDOW) -> dict[str, Any]:
    r05 = frozenset(return_set(250, 0.05))
    events: list[dict[str, Any]] = []
    for n in range(2, n_max + 1):
        row = classify_orbit(trajectory(n), r05)
        for event in row["events"]:
            events.append(_compact(event, n))
    return {
        "n_max": n_max,
        "tally": _tally(events),
        "events": events,
    }


def flyer_census() -> dict[str, Any]:
    r05 = frozenset(return_set(250, 0.05))
    rows = []
    all_events: list[dict[str, Any]] = []
    for n in HIGH_FLYERS:
        classified = classify_orbit(trajectory(n), r05)
        compact = [_compact(e, n) for e in classified["events"]]
        all_events.extend(compact)
        tally = _tally(compact)
        rows.append(
            {
                "n": n,
                "tally": tally,
                "witnesses": compact[:FLYER_WITNESS_CAP],
            }
        )
    return {
        "flyers": list(HIGH_FLYERS),
        "tally": _tally(all_events),
        "rows": rows,
    }


def classify(summary: dict[str, Any]) -> str:
    wt = summary["window"]["tally"]
    ft = summary["flyers"]["tally"]
    glue = (
        wt["glue_19_to_19"]
        + wt["glue_19_to_38"]
        + wt["factors_19_19"]
        + ft["glue_19_to_19"]
        + ft["glue_19_to_38"]
        + ft["factors_19_19"]
    )
    n19 = wt["n19"] + ft["n19"]
    end_odd = wt["end_odd_19"] + ft["end_odd_19"]
    if glue > 0:
        return CLASS_GLUE_LIVE
    if n19 > 0 and end_odd == 0:
        return CLASS_EVEN_TERMINAL
    return CLASS_NO_GLUE


def build_summary(n_max: int = WINDOW) -> dict[str, Any]:
    summary: dict[str, Any] = {
        "experiment": "juggler_flight_fan_concat",
        "anti_overclaim": {
            "halt_theorem": False,
            "divergence_excluded": False,
            "divergent_orbit_exists": False,
            "infinite_fan_sequence_constructed": False,
            "paper_a_modified": False,
            "record_composition_reopened": False,
            "mechanical_lift_reopened": False,
            "expanding_concat_reopened": False,
            "n_window_raised": False,
            "cf_fan_census": False,
        },
        "theta_19": round(theta_p(19), 9),
        "r05": return_set(250, 0.05),
        "hug19": hug_letters(19),
        "hug19_odds": hug_letters(19).count("O"),
        "window": window_census(n_max),
        "flyers": flyer_census(),
        "notes": {
            "target": (
                "local glue of (19, 12) record segments: does the "
                "endpoint launch another R_0.05 fan block?"
            ),
            "glue": (
                "19→19 / 19→38 requires the 19-endpoint to be a "
                "remaining-tail record and the next AboveAnchor "
                "segment to realize a 19- or 38-near-return; "
                "38=19|19 requires a mid-record at t=19 whose "
                "both halves are near-returns"
            ),
        },
    }
    summary["classification"] = classify(summary)
    return summary


def main() -> dict[str, Any]:
    summary = build_summary()
    DATA_DIR.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(summary, indent=2) + "\n", encoding="utf-8")
    wt = summary["window"]["tally"]
    ft = summary["flyers"]["tally"]
    print(f"hug19 = {summary['hug19']} (o={summary['hug19_odds']})")
    print(
        f"window: 19={wt['n19']} 38={wt['n38']} hug19={wt['hug19']} "
        f"end_odd_19={wt['end_odd_19']} tail_rec_19={wt['tail_record_19']} "
        f"glue19-19={wt['glue_19_to_19']} glue19-38={wt['glue_19_to_38']} "
        f"factors={wt['factors_19_19']} next_p={wt['next_near_p_19']}"
    )
    print(
        f"flyers: 19={ft['n19']} 38={ft['n38']} hug19={ft['hug19']} "
        f"end_odd_19={ft['end_odd_19']} tail_rec_19={ft['tail_record_19']} "
        f"glue19-19={ft['glue_19_to_19']} glue19-38={ft['glue_19_to_38']} "
        f"factors={ft['factors_19_19']}"
    )
    print(summary["classification"])
    return summary


if __name__ == "__main__":
    main()
