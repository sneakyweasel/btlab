"""First-collision / ancestry of two realizing Juggler words.

Phase 0 only: characterize T_u(n)=T_v(m) with no earlier shared
state, starting from the four last-letter parent types EE, EO, OE,
OO. This is not a reopen of the cycle first-intersection stack,
not a leftover-killer, not twin-flight, not a predecessor BFS,
and not a halt theorem.

Dossier: docs/problems/juggler_first_collision.md.
"""

from __future__ import annotations

import json
from pathlib import Path
from typing import Any

from research.juggler_sequence.backward_geometry import pred_even, pred_odd
from research.juggler_sequence.compensated_contraction import follows_itinerary, image_after
from research.juggler_sequence.floor_preimages import even_preimage, odd_preimage_integers
from research.juggler_sequence.power_itineraries import floor_power, itinerary, word_of

REPO_ROOT = Path(__file__).resolve().parents[3]
DOSSIER_PATH = REPO_ROOT / "docs" / "problems" / "juggler_first_collision.md"
DATA_DIR = REPO_ROOT / "data" / "research" / "juggler" / "first_collision"

CLASS_CLOSED = "FIRST_COLLISION_CLOSED"
CLASS_GREEN = "FIRST_COLLISION_GREEN"
CLASS_PARK = "FIRST_COLLISION_PARK"

PARENT_TYPES = ("EE", "EO", "OE", "OO")
SINK = frozenset({1, 2})
X_MAX = 400
START_MAX = 400
WORD_LEN_MAX = 3

ARCHIVED = (
    "odd_preimage_unique",
    "oddLanding_preimage_unique",
    "even_preimage_iff",
    "odd_preimage_iff",
)

WITNESS_EE = {"n": 100, "u": "E", "m": 102, "v": "E", "x": 10}
WITNESS_OE = {"n": 5, "u": "O", "m": 122, "v": "E", "x": 11}
WITNESS_EO = {"n": 122, "u": "E", "m": 5, "v": "O", "x": 11}
SAME_PARENT_EE = {"n": 16, "u": "EE", "m": 18, "v": "EE", "x": 2}
SINK_OVERSHOOT = {"n": 4, "u": "EEO", "m": 2, "v": "E", "x": 1}


def orbit(n: int, word: str) -> list[int]:
    """States [n_0, ..., n_|u|] along a realizing word."""

    if not word:
        raise ValueError("orbit requires a nonempty word")
    if not follows_itinerary(n, word):
        raise ValueError(f"word {word!r} does not follow from {n}")
    current = n
    states = [current]
    for _letter in word:
        current = floor_power(current)
        states.append(current)
    return states


def last_parent(n: int, word: str) -> int:
    return orbit(n, word)[-2]


def parent_type(u: str, v: str) -> str:
    if not u or not v:
        raise ValueError("parent_type requires nonempty itinerarys")
    if u[-1] not in "EO" or v[-1] not in "EO":
        raise ValueError(f"invalid parent letters {(u[-1], v[-1])}")
    return u[-1] + v[-1]


def is_first_collision(
    n: int,
    u: str,
    m: int,
    v: str,
    *,
    exclude_sink: bool = True,
) -> bool:
    """True iff the orbits first meet at the common terminal image."""

    if n == m or not u or not v:
        return False
    if not follows_itinerary(n, u) or not follows_itinerary(m, v):
        return False
    left = orbit(n, u)
    right = orbit(m, v)
    if left[-1] != right[-1]:
        return False
    if exclude_sink and left[-1] in SINK:
        return False
    return set(left[:-1]).isdisjoint(right[:-1])


def even_preds_from_cell(x: int) -> list[int]:
    lo, hi = even_preimage(x)
    first = max(lo, 2)
    if first % 2:
        first += 1
    return [n for n in range(first, hi, 2) if floor_power(n) == x]


def odd_preds_from_cell(x: int) -> list[int]:
    return [n for n in odd_preimage_integers(x) if n >= 1 and n % 2 == 1 and floor_power(n) == x]


def one_step_row(x: int) -> dict[str, Any]:
    evens = pred_even(x)
    odds = pred_odd(x)
    cell_evens = even_preds_from_cell(x)
    cell_odds = odd_preds_from_cell(x)
    p, q = len(evens), len(odds)
    expected = {
        "EE": p * (p - 1),
        "EO": p * q,
        "OE": q * p,
        "OO": q * (q - 1),
    }
    counts = {typ: 0 for typ in PARENT_TYPES}
    parents = [("E", parent) for parent in evens] + [("O", parent) for parent in odds]
    for letter_u, parent_u in parents:
        for letter_v, parent_v in parents:
            if parent_u == parent_v:
                continue
            counts[letter_u + letter_v] += 1
    return {
        "x": x,
        "n_even": p,
        "n_odd": q,
        "counts": counts,
        "expected": expected,
        "fibre_matches_cell": evens == cell_evens and odds == cell_odds,
        "counts_match_expected": counts == expected,
        "oo_empty": expected["OO"] == 0 and counts["OO"] == 0,
        "in_sink": x in SINK,
    }


def one_step_census(x_max: int = X_MAX) -> dict[str, Any]:
    totals = {typ: 0 for typ in PARENT_TYPES}
    expected_totals = {typ: 0 for typ in PARENT_TYPES}
    occupied = {typ: False for typ in PARENT_TYPES}
    fibre_ok = True
    counts_ok = True
    oo_empty = True
    n_images = 0
    for x in range(1, x_max + 1):
        if x in SINK:
            continue
        row = one_step_row(x)
        n_images += 1
        fibre_ok = fibre_ok and row["fibre_matches_cell"]
        counts_ok = counts_ok and row["counts_match_expected"]
        oo_empty = oo_empty and row["oo_empty"]
        for typ in PARENT_TYPES:
            totals[typ] += row["counts"][typ]
            expected_totals[typ] += row["expected"][typ]
            if row["counts"][typ]:
                occupied[typ] = True
    return {
        "x_max": x_max,
        "sink_excluded": sorted(SINK),
        "n_images": n_images,
        "counts": totals,
        "expected": expected_totals,
        "occupied": occupied,
        "fibre_matches_cell": fibre_ok,
        "counts_match_expected": counts_ok,
        "oo_empty": oo_empty,
    }


def _meeting_record(
    n: int,
    path_n: tuple[int, ...],
    m: int,
    path_m: tuple[int, ...],
    *,
    exclude_sink: bool,
) -> dict[str, Any] | None:
    if path_n[-1] != path_m[-1]:
        return None
    x = path_n[-1]
    if exclude_sink and x in SINK:
        return None
    first = set(path_n[:-1]).isdisjoint(path_m[:-1])
    parent_n = path_n[-2]
    parent_m = path_m[-2]
    return {
        "n": n,
        "m": m,
        "u": word_of(path_n),
        "v": word_of(path_m),
        "x": x,
        "parent_n": parent_n,
        "parent_m": parent_m,
        "first": first,
        "distinct_parents": parent_n != parent_m,
        "type": word_of(path_n)[-1] + word_of(path_m)[-1],
    }


def determinism_check(
    *,
    start_max: int = START_MAX,
    word_len_max: int = WORD_LEN_MAX,
    exclude_sink: bool = True,
) -> dict[str, Any]:
    """Itinerary pairs: first collision iff last parents differ."""

    paths: dict[tuple[int, int], tuple[int, ...]] = {}
    for n in range(1, start_max + 1):
        for length in range(1, word_len_max + 1):
            paths[n, length] = itinerary(n, length)

    meetings = 0
    first = 0
    same_parent = 0
    mismatches: list[dict[str, Any]] = []
    type_first = {typ: 0 for typ in PARENT_TYPES}
    type_same_parent = {typ: 0 for typ in PARENT_TYPES}
    mixed_lengths = 0
    for n in range(1, start_max + 1):
        for m in range(n + 1, start_max + 1):
            for k in range(1, word_len_max + 1):
                for ell in range(1, word_len_max + 1):
                    rec = _meeting_record(
                        n,
                        paths[n, k],
                        m,
                        paths[m, ell],
                        exclude_sink=exclude_sink,
                    )
                    if rec is None:
                        continue
                    meetings += 1
                    if rec["first"]:
                        first += 1
                        type_first[rec["type"]] += 1
                    if not rec["distinct_parents"]:
                        same_parent += 1
                        type_same_parent[rec["type"]] += 1
                    if k != ell:
                        mixed_lengths += 1
                    if rec["first"] != rec["distinct_parents"]:
                        mismatches.append(rec)
                        if len(mismatches) >= 8:
                            return _determinism_payload(
                                start_max,
                                word_len_max,
                                exclude_sink,
                                meetings,
                                first,
                                same_parent,
                                mixed_lengths,
                                type_first,
                                type_same_parent,
                                mismatches,
                            )
    return _determinism_payload(
        start_max,
        word_len_max,
        exclude_sink,
        meetings,
        first,
        same_parent,
        mixed_lengths,
        type_first,
        type_same_parent,
        mismatches,
    )


def _determinism_payload(
    start_max: int,
    word_len_max: int,
    exclude_sink: bool,
    meetings: int,
    first: int,
    same_parent: int,
    mixed_lengths: int,
    type_first: dict[str, int],
    type_same_parent: dict[str, int],
    mismatches: list[dict[str, Any]],
) -> dict[str, Any]:
    return {
        "start_max": start_max,
        "word_len_max": word_len_max,
        "sink_excluded": sorted(SINK) if exclude_sink else [],
        "meetings": meetings,
        "first_collisions": first,
        "same_parent": same_parent,
        "mixed_lengths": mixed_lengths,
        "type_first": type_first,
        "type_same_parent": type_same_parent,
        "n_mismatch": len(mismatches),
        "mismatches": mismatches,
        "iff_holds": not mismatches,
    }


def witness_record(row: dict[str, Any], *, exclude_sink: bool = True) -> dict[str, Any]:
    n, u, m, v = row["n"], row["u"], row["m"], row["v"]
    left = orbit(n, u)
    right = orbit(m, v)
    return {
        **row,
        "image_n": left[-1],
        "image_m": right[-1],
        "parent_n": left[-2],
        "parent_m": right[-2],
        "type": parent_type(u, v),
        "first": is_first_collision(n, u, m, v, exclude_sink=exclude_sink),
        "distinct_parents": left[-2] != right[-2],
        "follows": follows_itinerary(n, u) and follows_itinerary(m, v),
        "same_image": left[-1] == right[-1] == row["x"],
    }


def witnesses() -> dict[str, Any]:
    ee = witness_record(WITNESS_EE)
    oe = witness_record(WITNESS_OE)
    eo = witness_record(WITNESS_EO)
    same = witness_record(SAME_PARENT_EE, exclude_sink=False)
    overshoot = witness_record(SINK_OVERSHOOT, exclude_sink=False)
    return {
        "EE": ee,
        "OE": oe,
        "EO": eo,
        "OO": None,
        "same_parent_EE": same,
        "sink_overshoot": overshoot,
        "occupied_ok": (
            ee["first"]
            and ee["type"] == "EE"
            and oe["first"]
            and oe["type"] == "OE"
            and eo["first"]
            and eo["type"] == "EO"
            and same["same_image"]
            and not same["first"]
            and not same["distinct_parents"]
            and overshoot["same_image"]
            and overshoot["distinct_parents"]
            and not overshoot["first"]
            and 1 in orbit(4, "EEO")[:-1]
        ),
    }


def classify(payload: dict[str, Any]) -> dict[str, Any]:
    census = payload["one_step"]
    det = payload["determinism"]
    wit = payload["witnesses"]
    cell_law = (
        census["oo_empty"]
        and census["fibre_matches_cell"]
        and census["counts_match_expected"]
        and census["occupied"]["EE"]
        and census["occupied"]["EO"]
        and census["occupied"]["OE"]
        and not census["occupied"]["OO"]
        and det["iff_holds"]
        and wit["occupied_ok"]
    )
    if cell_law:
        return {
            "classification": CLASS_CLOSED,
            "decision": "CLOSE",
            "reason": (
                "first collision iff distinct last parents; OO empty by "
                "odd_preimage_unique; OE/EO and EE are the one-step cells"
            ),
            "new_seam": False,
            "leftover_killer": False,
            "reopens_intersection_taxonomy": False,
            "halt_theorem": False,
            "raise_n0": False,
            "paper_a_edit": False,
            "archived": list(ARCHIVED),
        }
    return {
        "classification": CLASS_GREEN,
        "decision": "PARK",
        "reason": "a parent type left the cell law; inspect mismatches",
        "new_seam": True,
        "leftover_killer": False,
        "reopens_intersection_taxonomy": False,
        "halt_theorem": False,
        "raise_n0": False,
        "paper_a_edit": False,
        "archived": list(ARCHIVED),
    }


def probe_payload() -> dict[str, Any]:
    census = one_step_census()
    det = determinism_check()
    det_sink = determinism_check(exclude_sink=False)
    wit = witnesses()
    payload = {
        "bound": "first_collision",
        "archived": list(ARCHIVED),
        "sink": sorted(SINK),
        "parent_types": list(PARENT_TYPES),
        "one_step": census,
        "determinism": det,
        "determinism_including_sink": {
            "meetings": det_sink["meetings"],
            "first_collisions": det_sink["first_collisions"],
            "same_parent": det_sink["same_parent"],
            "n_mismatch": det_sink["n_mismatch"],
            "iff_holds": det_sink["iff_holds"],
        },
        "witnesses": wit,
        "image_after_check": image_after(5, "O") == 11 and image_after(122, "E") == 11,
    }
    payload["decision"] = classify(payload)
    return payload


def write_artifacts(payload: dict[str, Any] | None = None) -> dict[str, Any]:
    data = payload if payload is not None else probe_payload()
    DATA_DIR.mkdir(parents=True, exist_ok=True)
    path = DATA_DIR / "summary.json"
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
                "one_step": payload["one_step"]["counts"],
                "oo_empty": payload["one_step"]["oo_empty"],
                "iff": payload["determinism"]["iff_holds"],
                "iff_sink": payload["determinism_including_sink"]["iff_holds"],
                "meetings": payload["determinism"]["meetings"],
                "decision": decision["decision"],
            },
            indent=2,
        )
    )


if __name__ == "__main__":
    main()
