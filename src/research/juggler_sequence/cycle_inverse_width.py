"""Inverse-tube occupancy versus symbolic admissibility.

Phase 0 only: exact predecessor occupancy of short prescribed
prefixes, compared with the real/exponent hulls and with archived
floor cells. Not a halt theorem, not a finance reopen, not a floor
raise, and not a claim that one packed necklace is the obstruction.

Dossier: docs/problems/juggler_cycle_inverse_width.md.
"""

from __future__ import annotations

import json
from collections import Counter
from math import exp, log
from typing import Any

from research.juggler_sequence.cycle_almost_search import (
    PHASE1_L,
    compatible_oe_preimages,
    follow_depth,
    odd_preimage,
    packed_block_word,
)
from research.juggler_sequence.cycle_budget_opt import run_type_counts
from research.juggler_sequence.cycle_extremizer_discrepancy import (
    extra_even_word,
    extra_odd_word,
)
from research.juggler_sequence.cycle_finance import DATA_DIR, PUBLISHED_FLOOR, o_min_and_theta
from research.juggler_sequence.floor_preimages import even_preimage, even_preimage_width

INVERSE_DIR = DATA_DIR / "inverse_width"
PREFIX_LEN = 18
POINT_CAP = 4_000
INV_SCALE_CAP = 2_000_000
Y_GRID = (11, 101, 1001, 10_001, 100_001, 1_000_001)
FORWARD_SCALES = (100, 1_000, 10_000, 100_000, 1_000_000)
FORWARD_ODDS = 80
CALIBRATION = (365, 11681, 14237, 15343, 27623, 1_000_057)
ARCHIVED_DEATH = (
    "empty_odd_cell",
    "empty_oe",
    "empty_ooe",
    "two_block_243",
    "ooe_cell",
    "shared_ooe_prefix",
)

CLASS_CLOSED = "INVERSE_WIDTH_CLOSED"
CLASS_GREEN = "INVERSE_WIDTH_GREEN"
CLASS_PARK = "INVERSE_WIDTH_PARK"


def _odd_lo(n: int) -> int:
    return n + 1 if n % 2 == 0 else n


def hull_width(lo: float, hi: float) -> float:
    if hi <= lo:
        return 0.0
    return hi - lo


def exponent_hull_width(y: int, odd: int, length: int) -> float | None:
    """Order-blind real inverse width of n |-> n^{3^o / 2^L} at a singleton."""

    if y < 1 or length < 1 or odd < 0:
        return None
    alpha = (2.0**length) / (3.0**odd) if odd else float(2**length)
    log_hi = alpha * log(y + 1)
    log_lo = alpha * log(y)
    if log_hi > 700.0:
        return None
    return exp(log_hi) - exp(log_lo)


def real_letter_hull(lo: float, hi: float, letter: str) -> tuple[float, float]:
    """Real predecessor hull of an interval under one letter."""

    if letter == "E":
        return lo * lo, hi * hi
    if lo <= 0.0:
        return 0.0, hi ** (2.0 / 3.0)
    return lo ** (2.0 / 3.0), hi ** (2.0 / 3.0)


def _end_e_prefix(word: str, cap: int = PREFIX_LEN) -> str:
    """Longest start-O / end-E prefix of length at most ``cap``."""

    cut = min(len(word), cap)
    while cut > 0 and word[cut - 1] != "E":
        cut -= 1
    if cut < 1 or word[0] != "O":
        raise ValueError("no complete O...E prefix")
    return word[:cut]


def word_catalog() -> list[dict[str, Any]]:
    odd, _ = o_min_and_theta(PHASE1_L)
    n_ooe, n_oe = run_type_counts(odd, PHASE1_L - odd)
    packed = packed_block_word(PHASE1_L, odd)
    extra_odd = extra_odd_word(n_ooe, n_oe, 50, front=True)
    extra_even = extra_even_word(n_ooe, n_oe, 50, front=True)
    return [
        {
            "name": "packed_mechanical",
            "word": _end_e_prefix(packed),
            "family": "near",
            "source": "25781 Beatty packed prefix",
        },
        {
            "name": "bunched_ooe",
            "word": "OOE" * 6,
            "family": "near",
            "source": "bunched (OOE)^6 prefix",
        },
        {
            "name": "oe_then_ooe",
            "word": ("OE" + "OOE" * 5)[:PREFIX_LEN],
            "family": "near",
            "source": "OE inserted in front of OOE",
        },
        {
            "name": "interleave",
            "word": (("OOE" + "OE") * 4)[:PREFIX_LEN],
            "family": "near",
            "source": "alternating OOE/OE",
        },
        {
            "name": "oe_insert",
            "word": "OOEOOEOEOOEOOEOOE",
            "family": "near",
            "source": "packed with one early OE",
        },
        {
            "name": "extra_odd_front",
            "word": _end_e_prefix(extra_odd),
            "family": "near",
            "source": "25781 extra-odd front prefix",
        },
        {
            "name": "extra_even_front",
            "word": _end_e_prefix(extra_even),
            "family": "near",
            "source": "25781 extra-even front prefix",
        },
        {
            "name": "all_oe",
            "word": "OE" * 9,
            "family": "contracting",
            "source": "pure OE control",
        },
        {
            "name": "all_o",
            "word": "O" * 12,
            "family": "expanding",
            "source": "pure odd control",
        },
        {
            "name": "all_e",
            "word": "E" * 6,
            "family": "contracting",
            "source": "pure even control",
        },
    ]


def inverse_walk(word: str, y: int) -> dict[str, Any]:
    """Exact backward occupancy of ``word`` ending at singleton ``y``.

    Representation: ``points`` is a small exact set of images still to
    invert; ``even_cells`` stores the even-predecessor fibres of those
    points without enumerating width-``2q`` cells.
    """

    if y < 1 or not word:
        raise ValueError("inverse_walk requires a positive endpoint and an word")
    kind = "points"
    points = [y]
    hull_lo, hull_hi = float(y), float(y) + 1.0
    steps: list[dict[str, Any]] = []
    reverse_applied = ""
    death_tag = None
    occupied_thin = False
    empty_wide_exp = False
    empty_wide_real = False
    hulled = False

    for index, letter in enumerate(reversed(word)):
        prev_kind = kind
        prev_count = len(points)
        prev_scale = points[0] if points else y
        exp_width = exponent_hull_width(y, word[len(word) - index - 1 :].count("O"), index + 1)
        next_lo, next_hi = real_letter_hull(hull_lo, hull_hi, letter)
        real_width = hull_width(next_lo, next_hi)

        if letter == "E":
            if kind == "points":
                if not points:
                    nxt_kind, nxt_points = "points", []
                elif sum(even_preimage_width(q) for q in points) > POINT_CAP:
                    nxt_kind, nxt_points = "even_cells", list(points)
                else:
                    nxt_kind, nxt_points = "even_cells", list(points)
            else:
                hulled = True
                nxt_kind, nxt_points = "hulled", list(points)
        elif kind == "points":
            nxt_points = []
            for image in points:
                pred = odd_preimage(image)
                if pred is not None:
                    nxt_points.append(pred)
            nxt_kind = "points"
        elif kind == "even_cells":
            if any(image > INV_SCALE_CAP for image in points):
                hulled = True
                nxt_kind, nxt_points = "hulled", list(points)
            else:
                nxt_points = []
                for image in points:
                    nxt_points.extend(n for n, _ in compatible_oe_preimages(image))
                nxt_kind = "points"
        else:
            hulled = True
            nxt_kind, nxt_points = "hulled", list(points)

        exact_count: int | None
        if nxt_kind == "even_cells":
            exact_count = sum(max(q, 1) for q in nxt_points)
        elif nxt_kind == "hulled":
            exact_count = None
        else:
            exact_count = len(nxt_points)

        occupied = exact_count is None or exact_count > 0
        if occupied and real_width < 1.0 and nxt_kind == "points":
            occupied_thin = True
        if not occupied and exp_width is not None and exp_width >= 1.0:
            empty_wide_exp = True
        if not occupied and real_width >= 1.0:
            empty_wide_real = True

        reverse_applied += letter
        tag = None
        if not occupied and nxt_kind != "hulled":
            tag = _classify_death(reverse_applied, letter, prev_kind, prev_scale, y)
            death_tag = tag

        steps.append(
            {
                "k": index + 1,
                "letter": letter,
                "kind": nxt_kind,
                "exact_count": exact_count,
                "prev_count": prev_count,
                "real_width": real_width,
                "rel_width": real_width / next_lo if next_lo > 0 else None,
                "exp_width": exp_width,
                "occupied": occupied,
                "thin_occupied": occupied and real_width < 1.0 and nxt_kind == "points",
                "death_tag": tag,
            }
        )
        if not occupied and nxt_kind != "hulled":
            kind, points = nxt_kind, nxt_points
            hull_lo, hull_hi = next_lo, next_hi
            break
        kind, points = nxt_kind, nxt_points
        hull_lo, hull_hi = next_lo, next_hi
        if nxt_kind == "points" and nxt_points:
            hull_lo, hull_hi = float(min(nxt_points)), float(max(nxt_points)) + 1.0
        elif nxt_kind == "even_cells" and nxt_points:
            lo, _ = even_preimage(min(nxt_points))
            _, hi = even_preimage(max(nxt_points))
            hull_lo, hull_hi = float(lo), float(hi)

    survived = death_tag is None and not hulled
    return {
        "y": y,
        "word": word,
        "length": len(word),
        "steps": steps,
        "death_k": None if survived else (steps[-1]["k"] if steps else 0),
        "death_tag": death_tag,
        "survived": survived,
        "hulled": hulled,
        "occupied_thin": occupied_thin,
        "empty_wide_exp": empty_wide_exp,
        "empty_wide_real": empty_wide_real,
        "archived": death_tag in ARCHIVED_DEATH if death_tag else False,
        "final_count": steps[-1]["exact_count"] if steps else 1,
    }


def _classify_death(
    reverse_applied: str,
    letter: str,
    prev_kind: str,
    _prev_scale: int,
    _y: int,
) -> str:
    """Tag emptiness by the suffix inverted so far (forward order)."""

    if letter == "E":
        return "empty_even_cell"
    if reverse_applied.endswith("EOO"):
        return "empty_ooe"
    if prev_kind == "even_cells" or reverse_applied.endswith("EO"):
        return "empty_oe"
    return "empty_odd_cell"


def forward_lifespan(word: str, lo: int, n_odds: int = FORWARD_ODDS) -> dict[str, Any]:
    start = _odd_lo(lo)
    depths: list[int] = []
    for index in range(n_odds):
        n = start + 2 * index
        depths.append(follow_depth(n, word))
    if not depths:
        return {"n": 0}
    return {
        "lo": start,
        "n": len(depths),
        "min": min(depths),
        "max": max(depths),
        "mean": sum(depths) / len(depths),
        "hist": {str(k): v for k, v in sorted(Counter(depths).items())},
    }


def calibration_rows(words: list[dict[str, Any]]) -> list[dict[str, Any]]:
    rows = []
    for n in CALIBRATION:
        for spec in words:
            depth = follow_depth(n, spec["word"])
            rows.append(
                {
                    "n": n,
                    "name": spec["name"],
                    "R": depth,
                    "L": len(spec["word"]),
                    "complete": depth == len(spec["word"]),
                }
            )
    return rows


def inverse_grid(words: list[dict[str, Any]]) -> list[dict[str, Any]]:
    rows = []
    for spec in words:
        for y in Y_GRID:
            walk = inverse_walk(spec["word"], y)
            rows.append(
                {
                    "name": spec["name"],
                    "family": spec["family"],
                    "word": spec["word"],
                    "y": y,
                    "death_k": walk["death_k"],
                    "death_tag": walk["death_tag"],
                    "survived": walk["survived"],
                    "hulled": walk["hulled"],
                    "occupied_thin": walk["occupied_thin"],
                    "empty_wide_exp": walk["empty_wide_exp"],
                    "empty_wide_real": walk["empty_wide_real"],
                    "archived": walk["archived"],
                    "final_count": walk["final_count"],
                    "n_steps": len(walk["steps"]),
                }
            )
    return rows


def forward_grid(words: list[dict[str, Any]]) -> list[dict[str, Any]]:
    rows = []
    for spec in words:
        scale_max: list[int] = []
        for scale in FORWARD_SCALES:
            rec = forward_lifespan(spec["word"], scale + 1)
            scale_max.append(rec["max"])
            rows.append(
                {
                    "name": spec["name"],
                    "family": spec["family"],
                    "scale": scale,
                    **{k: rec[k] for k in ("lo", "n", "min", "max", "mean")},
                }
            )
        recs = [row for row in rows if row["name"] == spec["name"]]
        growing = recs[-1]["max"] > recs[0]["max"] + 2
        for row in recs:
            row["grows_with_scale"] = growing
            row["scale_maxima"] = scale_max
    return rows


def classify(payload: dict[str, Any]) -> dict[str, Any]:
    inverse = payload["inverse"]
    forward = payload["forward"]
    calib = payload["calibration"]
    deaths = [row for row in inverse if row["death_tag"]]
    tags = Counter(row["death_tag"] for row in deaths)
    occupied_thin = any(row["occupied_thin"] for row in inverse)
    empty_wide_real = any(
        row["empty_wide_real"] and row["y"] >= 1001 for row in inverse
    )
    empty_wide_exp = any(
        row["empty_wide_exp"] and row["y"] >= 1001 for row in inverse
    )
    unarchived = [row for row in deaths if not row["archived"]]
    near_deaths = [row for row in deaths if row["family"] == "near"]
    near_survived = [
        row for row in inverse if row["family"] == "near" and row["survived"]
    ]
    packed_cal = [row for row in calib if row["name"] in ("packed_mechanical", "bunched_ooe")]
    level1_false = any(row["R"] >= 20 for row in packed_cal)
    all_e = [row for row in inverse if row["name"] == "all_e"]
    all_e_explodes = all(row["survived"] or row["hulled"] for row in all_e)

    near_forward = [row for row in forward if row["family"] == "near"]
    packed_forward = [row for row in forward if row["name"] == "packed_mechanical"]
    scale_growth = bool(packed_forward) and packed_forward[-1]["max"] > packed_forward[0]["max"] + 2
    same_prefix_span = 0
    ooe_prefix = [
        row
        for row in near_deaths
        if row["word"].startswith("OOE") and row["y"] == 1_000_001
    ]
    if ooe_prefix:
        ks = {row["death_k"] for row in ooe_prefix}
        same_prefix_span = max(ks) - min(ks)

    leftover_killer = False
    new_mechanism = bool(unarchived) or (empty_wide_real and not occupied_thin)
    if unarchived or (empty_wide_real and not occupied_thin):
        classification = CLASS_GREEN
        reason = (
            "an inverse emptiness is not an archived cell, or a wide "
            "real hull emptied without a thin occupied witness"
        )
        decision = "PROMOTE"
    elif occupied_thin and not new_mechanism and all(row["archived"] for row in near_deaths):
        classification = CLASS_CLOSED
        reason = (
            "near-convergent inverse tubes empty only at archived cells; "
            "a real hull thinner than 1 remains occupied, so width is a "
            "relaxation of the floor cells"
        )
        decision = "CLOSE"
    else:
        classification = CLASS_PARK
        reason = "inverse occupancy is mixed and does not yield a uniform width law"
        decision = "PARK"

    return {
        "classification": classification,
        "decision": decision,
        "reason": reason,
        "death_tags": dict(tags),
        "occupied_thin": occupied_thin,
        "empty_wide_real": empty_wide_real,
        "empty_wide_exp": empty_wide_exp,
        "unarchived_deaths": len(unarchived),
        "near_survived": len(near_survived),
        "level1_k20_false": level1_false,
        "all_e_explodes": all_e_explodes,
        "scale_growth": scale_growth,
        "same_ooe_prefix_death_span": same_prefix_span,
        "leftover_killer": leftover_killer,
        "halt_theorem": False,
        "raise_n0": False,
        "open_55293": False,
        "new_mechanism": new_mechanism,
    }


def probe_payload() -> dict[str, Any]:
    words = word_catalog()
    inverse = inverse_grid(words)
    forward = forward_grid(words)
    calib = calibration_rows(words)
    payload = {
        "bound": "inverse_width",
        "L": PHASE1_L,
        "prefix_len": PREFIX_LEN,
        "y_grid": list(Y_GRID),
        "forward_scales": list(FORWARD_SCALES),
        "words": [
            {k: spec[k] for k in ("name", "word", "family", "source")}
            for spec in words
        ],
        "inverse": inverse,
        "forward": forward,
        "calibration": calib,
        "published_floor": PUBLISHED_FLOOR,
    }
    payload["decision"] = classify(payload)
    return payload


def write_artifacts(payload: dict[str, Any] | None = None) -> dict[str, Any]:
    data = payload if payload is not None else probe_payload()
    INVERSE_DIR.mkdir(parents=True, exist_ok=True)
    path = INVERSE_DIR / "summary.json"
    path.write_text(json.dumps(data, indent=2) + "\n", encoding="utf-8")
    return data


def main() -> None:
    payload = write_artifacts()
    decision = payload["decision"]
    print(decision["classification"])
    print(decision["reason"])
    print(decision["death_tags"])


if __name__ == "__main__":
    main()
