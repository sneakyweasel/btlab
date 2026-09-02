"""Finance-extremal word versus exact terminal cells.

The almost-cycle search closed: the L=25781 finance-optimal word
is unrealized past depth 11, and exact backward dies at an empty
OOE preimage after at most two blocks. This phase asks whether
that failure is an word-independent law

    finance extremality  =>  exact-cell incompatibility

or the existing F_2 / (2,1)-at-start envelope rewritten.

Not a halt theorem, not Phase 2 at L=55293, and not a floor raise.

Dossier: docs/problems/juggler_cycle_finance_cell_bridge.md.
"""

from __future__ import annotations

import json
from collections import Counter
from math import isqrt
from typing import Any

from research.juggler_sequence.cycle_almost_search import (
    PHASE1_L,
    circuits,
    distinguished_words,
    follow_depth,
    packed_block_word,
    run_preimages,
    run_stats,
    word_bundle,
)
from research.juggler_sequence.cycle_budget_opt import run_type_counts
from research.juggler_sequence.cycle_finance import (
    DATA_DIR,
    PUBLISHED_FLOOR,
    o_min_and_theta,
    sha256_int_list,
)
from research.juggler_sequence.cycle_ordered_excursion import excursion_map
from research.juggler_sequence.cycle_prefix_feasibility import (
    ceiling_christoffel_word,
    extremal_word,
)
BRIDGE_DIR = DATA_DIR / "finance_cell_bridge"
START = PUBLISHED_FLOOR + 1
WINDOW = 800
CENSUS_STRIDE = 20
COINCIDENCE_LENGTHS = (19, 84, 1054, 25781)
FOLLOW_HI = START + 2_000
FOLLOW_STRIDE = 34
A2_SCAN_HI = 20_000


def last_blocks(word: str, count: int = 4) -> list[tuple[int, int]]:
    pairs = circuits(word)
    return pairs[-count:]


def block_letters(pairs: list[tuple[int, int]]) -> str:
    return "".join("A" if a == 2 and b == 1 else "B" if a == 1 and b == 1 else "?" for a, b in pairs)


def isolated_minority(word: str) -> dict[str, Any]:
    """Sturmian isolation: majority OOE should separate every OE."""

    letters = block_letters(circuits(word))
    n_a = letters.count("A")
    n_b = letters.count("B")
    majority = "A" if n_a >= n_b else "B"
    minority = "B" if majority == "A" else "A"
    doubled = minority + minority
    return {
        "n_ooe": n_a,
        "n_oe": n_b,
        "majority": majority,
        "minority": minority,
        "isolated_minority": doubled not in letters,
        "bb_count": letters.count(doubled),
        "suffix": letters[-8:],
        "prefix": letters[:8],
    }


def expanding_last_ooe_hits(lo: int, hi: int) -> dict[str, Any]:
    """F_2(v)=n with v>=n: last circuit OOE landing at a CycleMin."""

    if lo % 2 == 0:
        lo += 1
    hits: list[dict[str, Any]] = []
    n_a2 = 0
    n_le = 0
    for v in range(lo, hi + 1, 2):
        rec = excursion_map(v, 2)
        if rec is None:
            continue
        n_a2 += 1
        landing = rec[1]
        if landing <= v:
            n_le += 1
            hits.append({"v": v, "w": landing, "peak": rec[0]})
            if len(hits) >= 8:
                break
    return {
        "lo": lo,
        "hi": hi,
        "n_a2": n_a2,
        "n_F2_le_v": n_le,
        "hits": hits,
        "expanding": n_le == 0,
    }


def first_pair(n: int, last_run: int, prev_run: int) -> tuple[int, int] | None:
    """One (u, v) with F_{prev}(u)=v and F_{last}(v)=n, if any."""

    for valley in run_preimages(n, last_run):
        preds = run_preimages(valley, prev_run)
        if preds:
            return preds[0], valley
    return None


def has_pair(n: int, last_run: int, prev_run: int) -> bool:
    return first_pair(n, last_run, prev_run) is not None


def triple221_into(n: int) -> tuple[int, int, int] | None:
    """u --OOE--> w --OOE--> v --OE--> n, if any."""

    pair = first_pair(n, 1, 2)
    if pair is None:
        return None
    u, v = pair
    preds = run_preimages(u, 2)
    if not preds:
        return None
    return preds[0], u, v


def terminal_census(lo: int, hi: int, *, stride: int = 2) -> dict[str, Any]:
    """How often n has OE, (2,1), (1,1), or (2,2,1) preimages."""

    if lo % 2 == 0:
        lo += 1
    n_seen = 0
    n_oe = 0
    n_21 = 0
    n_11 = 0
    n_221 = 0
    oe_counts: list[int] = []
    witnesses_21: list[dict[str, int]] = []
    witnesses_221: list[dict[str, int]] = []
    for n in range(lo, hi + 1, stride):
        if n % 2 == 0:
            continue
        n_seen += 1
        oe = run_preimages(n, 1)
        if not oe:
            continue
        n_oe += 1
        oe_counts.append(len(oe))
        pair_21 = first_pair(n, 1, 2)
        pair_11 = first_pair(n, 1, 1)
        if pair_21 is not None:
            n_21 += 1
            if len(witnesses_21) < 6:
                u, v = pair_21
                witnesses_21.append({"n": n, "u": u, "v": v})
            triple = triple221_into(n)
            if triple is not None:
                n_221 += 1
                if len(witnesses_221) < 6:
                    u0, u, v = triple
                    witnesses_221.append({"n": n, "u0": u0, "u": u, "v": v})
        if pair_11 is not None:
            n_11 += 1
    return {
        "lo": lo,
        "hi": hi,
        "n_seen": n_seen,
        "n_oe": n_oe,
        "n_21": n_21,
        "n_11": n_11,
        "n_221": n_221,
        "p_oe": n_oe / n_seen if n_seen else None,
        "p_21_given_oe": n_21 / n_oe if n_oe else None,
        "p_11_given_oe": n_11 / n_oe if n_oe else None,
        "p_221_given_21": n_221 / n_21 if n_21 else None,
        "mean_oe_preds": (sum(oe_counts) / len(oe_counts)) if oe_counts else None,
        "witnesses_21": witnesses_21,
        "witnesses_221": witnesses_221,
        "empty_21_as_law": n_21 == 0,
        "empty_221_as_law": n_221 == 0,
    }


def random_two_type(length: int, odd: int, *, seed: int = 1) -> str:
    """Deterministic two-type word with the same (OOE, OE) counts.

    Not mechanical: bunch the minority, then the majority. Used only
    as a non-extremal control of the same run-type packing.
    """

    n_ooe, n_oe = run_type_counts(odd, length - odd)
    if seed % 2 == 0:
        return "OE" * n_oe + "OOE" * n_ooe
    return "OOE" * n_ooe + "OE" * n_oe


def follow_report(word: str, lo: int, hi: int, *, stride: int = FOLLOW_STRIDE) -> dict[str, Any]:
    if lo % 2 == 0:
        lo += 1
    depths: list[int] = []
    fail_at: Counter[int] = Counter()
    for n in range(lo, hi + 1, stride):
        if n % 2 == 0:
            continue
        depth = follow_depth(n, word)
        depths.append(depth)
        fail_at[depth] += 1
    if not depths:
        return {"n": 0}
    return {
        "n": len(depths),
        "min": min(depths),
        "max": max(depths),
        "mean": sum(depths) / len(depths),
        "fail_at": {str(k): fail_at[k] for k in sorted(fail_at)},
    }


def coincidence_row(length: int) -> dict[str, Any]:
    odd, _ = o_min_and_theta(length)
    ext = extremal_word(length)
    chr_word = ceiling_christoffel_word(length, odd)
    packed = packed_block_word(length, odd)
    isol = isolated_minority(ext)
    last = last_blocks(ext, 4)
    return {
        "L": length,
        "o": odd,
        "extremal_eq_christoffel": ext == chr_word,
        "christoffel_eq_packed": chr_word == packed,
        "all_equal": ext == chr_word == packed,
        "last_blocks": last,
        "ends_oe": last[-1] == (1, 1),
        "ends_21": last[-2:] == [(2, 1), (1, 1)],
        "isolated_oe": isol["isolated_minority"],
        "suffix_blocks": isol["suffix"],
        "a0": run_stats(ext)["a0"],
    }


def composed_21_cell(n: int, u: int, v: int) -> dict[str, Any]:
    """Integer cells for u --OOE--> v --OE--> n."""

    return {
        "n": n,
        "u": u,
        "v": v,
        "oe_cell": n**4 <= v**3 < (n + 1) ** 4,
        "ooe_cell": v**8 <= u**9,
        "necessary_u27_ge_n32": u**27 >= n**32,
        "F2": excursion_map(u, 2),
        "F1": excursion_map(v, 1),
    }


def bridge_scan(*, start: int = START) -> dict[str, Any]:
    odd, theta = o_min_and_theta(PHASE1_L)
    words = distinguished_words(PHASE1_L, odd)
    canonical = words["christoffel"]
    bundle = word_bundle(PHASE1_L, odd)
    isol = isolated_minority(canonical)
    last = last_blocks(canonical, 6)
    coincidence = [coincidence_row(length) for length in COINCIDENCE_LENGTHS]
    expanding = expanding_last_ooe_hits(3, A2_SCAN_HI)
    census_floor = terminal_census(start, start + WINDOW, stride=CENSUS_STRIDE)
    census_mid = terminal_census(2_000_001, 2_000_001 + WINDOW, stride=CENSUS_STRIDE)
    bunched = random_two_type(PHASE1_L, odd, seed=1)
    bunched_rev = random_two_type(PHASE1_L, odd, seed=0)
    follow = {
        "canonical": follow_report(canonical, start, FOLLOW_HI),
        "bunched_ooe_then_oe": follow_report(bunched, start, FOLLOW_HI),
        "bunched_oe_then_ooe": follow_report(bunched_rev, start, FOLLOW_HI),
    }
    witnesses = census_floor["witnesses_21"] + census_mid["witnesses_21"]
    cells = [composed_21_cell(row["n"], row["u"], row["v"]) for row in witnesses[:4]]
    same_follow = follow["canonical"]["max"] <= follow["bunched_ooe_then_oe"]["max"] + 2
    ends_21 = last[-2:] == [(2, 1), (1, 1)]
    empty_21 = census_floor["empty_21_as_law"] and census_mid["empty_21_as_law"]
    empty_221 = census_floor["empty_221_as_law"] and census_mid["empty_221_as_law"]
    generic_two_type = same_follow
    reduces_to_known = (not empty_21) or generic_two_type
    return {
        "bound": "finance_cell_bridge",
        "L": PHASE1_L,
        "o": odd,
        "theta": theta,
        "n": start,
        "words": {
            "all_equal": bundle["extremal_eq_christoffel"] and bundle["christoffel_eq_packed"],
            "last_blocks": last,
            "ends_oe": last[-1] == (1, 1),
            "ends_21": ends_21,
            "isolation": isol,
        },
        "coincidence": coincidence,
        "expanding_last_ooe": expanding,
        "census_floor": census_floor,
        "census_mid": census_mid,
        "follow": follow,
        "composed_cells": cells,
        "terminal_21_forced": bool(
            ends_21 and isol["isolated_minority"] and expanding["expanding"]
        ),
        "terminal_21_empty_as_law": empty_21,
        "terminal_221_empty_as_law": empty_221,
        "generic_two_type_follow": generic_two_type,
        "reduces_to_known": reduces_to_known,
        "bridge_theorem": False,
        "leftover_killer": False,
        "halt_theorem": False,
        "no_cycle_all_lengths": False,
        "sha256_L": sha256_int_list([PHASE1_L, odd]),
    }


def write_bridge_artifacts(
    payload: dict[str, Any] | None = None,
    *,
    start: int = START,
) -> dict[str, Any]:
    data = payload if payload is not None else bridge_scan(start=start)
    BRIDGE_DIR.mkdir(parents=True, exist_ok=True)
    path = BRIDGE_DIR / "summary.json"
    path.write_text(json.dumps(data, indent=2, allow_nan=False) + "\n", encoding="utf-8")
    return data


if __name__ == "__main__":
    report = write_bridge_artifacts()
    print(
        json.dumps(
            {
                "all_equal": report["words"]["all_equal"],
                "ends_21": report["words"]["ends_21"],
                "isolated_oe": report["words"]["isolation"]["isolated_minority"],
                "suffix": report["words"]["isolation"]["suffix"],
                "coincidence": [
                    {
                        "L": row["L"],
                        "all_equal": row["all_equal"],
                        "ends_21": row["ends_21"],
                        "isolated_oe": row["isolated_oe"],
                    }
                    for row in report["coincidence"]
                ],
                "expanding": report["expanding_last_ooe"]["expanding"],
                "n_F2_le_v": report["expanding_last_ooe"]["n_F2_le_v"],
                "census_floor": {
                    "n_oe": report["census_floor"]["n_oe"],
                    "n_21": report["census_floor"]["n_21"],
                    "n_11": report["census_floor"]["n_11"],
                    "n_221": report["census_floor"]["n_221"],
                    "p_21": report["census_floor"]["p_21_given_oe"],
                    "p_11": report["census_floor"]["p_11_given_oe"],
                    "p_221": report["census_floor"]["p_221_given_21"],
                    "witnesses_21": report["census_floor"]["witnesses_21"],
                    "witnesses_221": report["census_floor"]["witnesses_221"],
                },
                "census_mid": {
                    "n_oe": report["census_mid"]["n_oe"],
                    "n_21": report["census_mid"]["n_21"],
                    "n_11": report["census_mid"]["n_11"],
                    "n_221": report["census_mid"]["n_221"],
                    "p_21": report["census_mid"]["p_21_given_oe"],
                    "p_221": report["census_mid"]["p_221_given_21"],
                },
                "follow": report["follow"],
                "terminal_21_forced": report["terminal_21_forced"],
                "empty_21": report["terminal_21_empty_as_law"],
                "empty_221": report["terminal_221_empty_as_law"],
                "generic_follow": report["generic_two_type_follow"],
                "reduces_to_known": report["reduces_to_known"],
                "bridge_theorem": report["bridge_theorem"],
            },
            indent=2,
        )
    )
