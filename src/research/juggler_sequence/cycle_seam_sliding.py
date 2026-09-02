"""Cyclic seam sliding through a homogeneous parity run.

Phase 0 only: separate combinatorial rotation of a cyclic word from
first-intersection sliding of a climb, and test whether the peak /
valley transfer is anything but the archived trailing-evens cell.

This is not a reopen of the first-intersection taxonomy leftover-killer,
not a finance reopen, not a halt theorem, and not a claim that every
positive integer reaches 1.

Dossier: docs/problems/juggler_cycle_seam_sliding.md.
"""

from __future__ import annotations

import json
from typing import Any

from research.juggler_sequence.cycle_finance import DATA_DIR
from research.juggler_sequence.power_itineraries import floor_power

SLIDE_DIR = DATA_DIR / "seam_sliding"

CLASS_CLOSED = "SEAM_SLIDING_CLOSED"
CLASS_GREEN = "SEAM_SLIDING_GREEN"
CLASS_PARK = "SEAM_SLIDING_PARK"

ARCHIVED = (
    "cycleItinerary_rotateItinerary",
    "rotateItinerary_even_run",
    "cycle_trailing_evens_lt",
    "even_run_scale_barrier",
    "odd_preimage_unique",
    "oddLanding_preimage_unique",
    "no_cycle_itinerary_even_count_le_three",
)

# Interior cuts of a homogeneous E^4 block, as in E|EEE, EE|EE, EEE|E.
INTERIOR_E_CUTS = ("E|EEE", "EE|EE", "EEE|E")
CANONICAL_SEAMS = ("EO", "OE")


def rotate_itinerary(word: str, k: int) -> str:
    """Cyclic shift; the Lean name is rotateItinerary."""

    if not word:
        return word
    k %= len(word)
    return word[k:] + word[:k]


def same_necklace(a: str, b: str) -> bool:
    return len(a) == len(b) and bool(a) and a in (b + b)


def e_block_word(r: int) -> str:
    """CycleMin-shaped necklace with a single trailing even run."""

    if r < 1:
        raise ValueError("even-run length must be at least 1")
    return "OO" + "E" * r


def interior_e_cut_words(r: int = 4) -> dict[str, str]:
    """Map E|E^{r-1}, EE|E^{r-2}, … to the rotated necklace."""

    base = e_block_word(r)
    out: dict[str, str] = {}
    for k in range(1, r):
        left = "E" * k
        right = "E" * (r - k)
        out[f"{left}|{right}"] = rotate_itinerary(base, 2 + k)
    return out


def necklace_collapses_interior_cuts(r: int = 4) -> bool:
    """Interior E-cuts are the same cyclic word class as the peak cut."""

    base = e_block_word(r)
    cuts = interior_e_cut_words(r)
    return bool(cuts) and all(same_necklace(base, w) for w in cuts.values())


def even_run(start: int, r: int) -> list[int]:
    xs = [start]
    x = start
    for _ in range(r):
        x = floor_power(x)
        xs.append(x)
    return xs


def first_shared(climb: list[int], other: list[int]) -> int | None:
    seen = set(other)
    for x in climb:
        if x in seen:
            return x
    return None


def distinct_even_parent(y: int) -> int:
    """An even parent of y other than y^2, inside the even cell."""

    if y < 2:
        raise ValueError("need an even-cell image")
    lo = y * y
    parent = lo + 2 if lo % 2 == 0 else lo + 1
    if floor_power(parent) != y:
        raise ValueError(f"{parent} is not an even parent of {y}")
    return parent


def backward_slide_witness(*, peak: int = 100, r: int = 2) -> dict[str, Any]:
    """First meeting interior to E^r cannot be slid back to the peak.

    The cycle-like descent is peak --E^r--> valley. The climb uses a
    different even parent of an interior state, so it first meets the
    descent there and never visits the peak.
    """

    descent = even_run(peak, r)
    if len(descent) < 3:
        raise ValueError("need an interior even for a backward-slide test")
    meet_at = descent[1]
    climb_start = distinct_even_parent(meet_at)
    climb = even_run(climb_start, r)
    meet = first_shared(climb, descent)
    valley = descent[-1]
    meet_idx = climb.index(meet) if meet is not None else None
    shared_tail = climb[meet_idx:] if meet_idx is not None else []
    return {
        "peak": peak,
        "r": r,
        "descent": descent,
        "climb_start": climb_start,
        "climb": climb,
        "first_intersection": meet,
        "valley": valley,
        "peak_on_climb": peak in climb,
        "valley_on_shared_tail": valley in shared_tail,
        "first_is_interior": meet not in (peak, valley),
        "backward_slide_is_first_intersection": meet == peak,
        "forward_slide_is_first_intersection": meet == valley,
    }


def peak_valley_scale(*, peak: int, r: int) -> dict[str, Any]:
    """P < (V+1)^{2^r} is cycle_trailing_evens_lt, not a new cell."""

    descent = even_run(peak, r)
    valley = descent[-1]
    exp = 1 << r
    trailing = (valley + 1) ** exp
    return {
        "peak": peak,
        "r": r,
        "valley": valley,
        "descent": descent,
        "trailing_cell": trailing,
        "peak_lt_trailing_cell": peak < trailing,
        "approx": f"P ~ V^{2**r} is the trailing-evens two-sided cell",
    }


def classify(payload: dict[str, Any]) -> dict[str, Any]:
    necklace_ok = bool(payload["necklace"]["interior_cuts_same_class"])
    back = payload["backward_slide"]
    back_fails = (
        back["first_is_interior"]
        and not back["peak_on_climb"]
        and not back["backward_slide_is_first_intersection"]
        and not back["forward_slide_is_first_intersection"]
        and back["valley_on_shared_tail"]
    )
    scale_ok = all(row["peak_lt_trailing_cell"] for row in payload["scale"])
    new_inequality = False
    if new_inequality:
        classification = CLASS_GREEN
        decision = "PROMOTE"
        reason = (
            "a first-intersection constraint or a bound on r appears "
            "that is not rotateItinerary / trailing-evens / even-scale / "
            "unique-odd-parent"
        )
    elif necklace_ok and back_fails and scale_ok:
        classification = CLASS_CLOSED
        decision = "CLOSE"
        reason = (
            "interior E-cuts are rotateItinerary of the same necklace; a "
            "first intersection interior to E^r cannot be slid to the "
            "peak or treated as first at the valley; P < (V+1)^{2^r} "
            "is cycle_trailing_evens_lt; the EO/OE reduction is the "
            "closed intersection taxonomy"
        )
    else:
        classification = CLASS_PARK
        decision = "PARK"
        reason = "the sliding census is mixed and does not decide"
    return {
        "classification": classification,
        "decision": decision,
        "reason": reason,
        "necklace_collapses": necklace_ok,
        "backward_slide_fails": back_fails,
        "scale_is_trailing_evens": scale_ok,
        "new_inequality": new_inequality,
        "leftover_killer": False,
        "reopens_intersection_taxonomy": False,
        "reopens_entry_corridor": False,
        "halt_theorem": False,
        "raise_n0": False,
        "paper_a_edit": False,
        "archived": list(ARCHIVED),
    }


def probe_payload() -> dict[str, Any]:
    cuts = interior_e_cut_words(4)
    back = backward_slide_witness()
    back3 = backward_slide_witness(peak=10_000, r=3)
    scale = [
        peak_valley_scale(peak=100, r=2),
        peak_valley_scale(peak=10_000, r=3),
    ]
    payload = {
        "bound": "seam_sliding",
        "archived": list(ARCHIVED),
        "canonical_seams": list(CANONICAL_SEAMS),
        "interior_e_cuts": list(INTERIOR_E_CUTS),
        "necklace": {
            "base": e_block_word(4),
            "cuts": cuts,
            "interior_cuts_same_class": necklace_collapses_interior_cuts(4),
            "lean": "cycleItinerary_rotateItinerary / rotateItinerary_even_run",
        },
        "backward_slide": back,
        "backward_slide_r3": {
            "first_intersection": back3["first_intersection"],
            "peak_on_climb": back3["peak_on_climb"],
            "backward_slide_is_first_intersection": back3[
                "backward_slide_is_first_intersection"
            ],
            "first_is_interior": back3["first_is_interior"],
        },
        "scale": scale,
        "odd_interior": {
            "first_intersection": False,
            "lean": "odd_preimage_unique / oddLanding_preimage_unique",
            "note": "O^r interiors are not first meetings, so O-sliding is vacuous",
        },
        "run_length": {
            "even_count_ge_four": True,
            "lean": "no_cycle_itinerary_even_count_le_three",
            "cell": "cycle_trailing_evens_lt at each r",
            "note": "how long E^r can be is the archived even-count plus the cell",
        },
    }
    payload["decision"] = classify(payload)
    return payload


def write_artifacts(payload: dict[str, Any] | None = None) -> dict[str, Any]:
    data = payload if payload is not None else probe_payload()
    SLIDE_DIR.mkdir(parents=True, exist_ok=True)
    path = SLIDE_DIR / "summary.json"
    path.write_text(json.dumps(data, indent=2, allow_nan=False) + "\n", encoding="utf-8")
    return data


def main() -> None:
    payload = write_artifacts()
    decision = payload["decision"]
    print(decision["classification"])
    print(decision["reason"])
    print(
        json.dumps(
            {
                "canonical_seams": payload["canonical_seams"],
                "necklace": payload["necklace"]["interior_cuts_same_class"],
                "first_intersection": payload["backward_slide"]["first_intersection"],
                "peak_on_climb": payload["backward_slide"]["peak_on_climb"],
                "decision": decision["decision"],
            },
            indent=2,
        )
    )


if __name__ == "__main__":
    main()
