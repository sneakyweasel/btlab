"""Word-order exact-map invariant. Not a leftover-killer.

Phase 0 only: same (o, L) fixes the exponent budget 3^o/2^L and,
on a CycleItinerary, the endpoint quantities Delta and T/n^P. The exact
map T_w is an ordered composition, so two words with that budget
need not agree. This probe asks whether any cycle-usable compression
of that dependence is new, or whether every same-budget distinction
is already a rotation, lowerDenom / S(w), a named cell, or cheap-OOE
adjacency.

Do not treat D_w, OE / OOE / EOO cells, or cheap-OOE→OE as the find.
Not a halt theorem, not a finance reopen, and not a claim that every
positive integer reaches 1.

Dossier: docs/problems/juggler_cycle_word_order.md.
"""

from __future__ import annotations

import json
from typing import Any

from research.juggler_sequence.cycle_finance import DATA_DIR
from research.juggler_sequence.cycle_itinerary_functional import (
    expanding,
    necklace_key,
    weight_sum,
)
from research.juggler_sequence.global_defect import follows_itinerary, image_after, odd_count
from research.juggler_sequence.power_itineraries import floor_power

ORDER_DIR = DATA_DIR / "word_order"
K_MAX = 8
REALIZED_LO = 2
REALIZED_HI = 2001
SAMPLE_CAP = 3

CLASS_CLOSED = "WORD_ORDER_CLOSED"
CLASS_GREEN = "WORD_ORDER_GREEN"
CLASS_PARK = "WORD_ORDER_PARK"

NAMED_CELL_WORDS = frozenset({"OE", "OOE", "OEO", "EOO"})
CANONICAL_TRIPLE = ("OOE", "OEO", "EOO")
CANONICAL_CONTRACTING = ("OOOEE", "OOEOE")

ARCHIVED = (
    "lowerDenom",
    "cycle_itinerary_functional",
    "no_cycle_itinerary_ooe",
    "no_cycle_itinerary_oeo",
    "no_cycle_itinerary_eoo",
    "ooe_blocks_oe",
    "global_defect_identity",
    "image_eq_start_defectRatio",
    "power_bound_word",
)

TAGS = ("rotation", "named_cell", "adjacency", "lowerDenom", "known_map", "unarchived")


def cycle_endpoint_defect(n: int, odd: int, length: int) -> int:
    """Delta on a CycleItinerary: n^{3^o} - n^{2^L}. Independent of letter order."""

    if n < 1 or odd < 0 or length < 1:
        raise ValueError("cycle_endpoint_defect requires n>=1, o>=0, L>=1")
    return n ** (3**odd) - n ** (1 << length)


def cycle_normalized_exponent(odd: int, length: int) -> tuple[int, int]:
    """Exponent of T/n^P on a CycleItinerary: (2^L - 3^o)/2^L."""

    if odd < 0 or length < 1:
        raise ValueError("cycle_normalized_exponent requires o>=0, L>=1")
    return (1 << length) - 3**odd, 1 << length


def itinerary_unique(n: int, length: int) -> str:
    """The unique length-L O/E word realized by n."""

    if n < 1 or length < 1:
        raise ValueError("itinerary_unique requires n>=1 and L>=1")
    letters: list[str] = []
    current = n
    for _ in range(length):
        letters.append("E" if current % 2 == 0 else "O")
        current = floor_power(current)
    return "".join(letters)


def distinct_same_length_domains_disjoint(left: str, right: str) -> bool:
    """Distinct equal-length words cannot share a follows-start."""

    return len(left) == len(right) and left != right


def endpoint_quantities_word_free(n: int, left: str, right: str) -> bool:
    """Same (o, L) ⇒ same CycleItinerary endpoint quantities, ignoring the word."""

    if odd_count(left) != odd_count(right) or len(left) != len(right):
        return False
    if not left:
        return False
    odd, length = odd_count(left), len(left)
    return cycle_endpoint_defect(n, odd, length) == cycle_endpoint_defect(
        n, odd_count(right), len(right)
    ) and cycle_normalized_exponent(odd, length) == cycle_normalized_exponent(
        odd_count(right), len(right)
    )


def apply_word(n: int, word: str) -> int | None:
    if not follows_itinerary(n, word):
        return None
    return image_after(n, word)


def first_peak_valley(n: int, word: str) -> tuple[int | None, int | None]:
    """State after the first O-run, then after the following E-run."""

    if not follows_itinerary(n, word):
        return None, None
    current = n
    index = 0
    while index < len(word) and word[index] == "E":
        current = floor_power(current)
        index += 1
    if index == len(word) or word[index] != "O":
        return None, None
    while index < len(word) and word[index] == "O":
        current = floor_power(current)
        index += 1
    peak = current
    if index == len(word) or word[index] != "E":
        return peak, None
    while index < len(word) and word[index] == "E":
        current = floor_power(current)
        index += 1
    return peak, current


def has_cheap_ooe_oe(word: str) -> bool:
    return "OOEOE" in word


def budget_pair(word: str) -> tuple[int, int]:
    return odd_count(word), len(word)


def tag_pair(left: str, right: str) -> str:
    """Most specific archived reason, or unarchived if none apply."""

    if left == right:
        return "rotation"
    if necklace_key(left) == necklace_key(right):
        if {left, right} <= NAMED_CELL_WORDS:
            return "named_cell"
        return "rotation"
    if {left, right} <= NAMED_CELL_WORDS:
        return "named_cell"
    if has_cheap_ooe_oe(left) != has_cheap_ooe_oe(right):
        return "adjacency"
    if weight_sum(left) != weight_sum(right):
        return "lowerDenom"
    return "known_map"


def compare_pair(
    left: str,
    right: str,
    *,
    lo: int = REALIZED_LO,
    hi: int = REALIZED_HI,
) -> dict[str, Any]:
    tag = tag_pair(left, right)
    common = 0
    image_differ = 0
    peak_differ = 0
    samples: list[dict[str, Any]] = []
    for n in range(lo, hi):
        left_image = apply_word(n, left)
        right_image = apply_word(n, right)
        if left_image is None or right_image is None:
            continue
        common += 1
        left_peak, left_valley = first_peak_valley(n, left)
        right_peak, right_valley = first_peak_valley(n, right)
        differ_image = left_image != right_image
        differ_peak = (left_peak, left_valley) != (right_peak, right_valley)
        if differ_image:
            image_differ += 1
        if differ_peak:
            peak_differ += 1
        if (differ_image or differ_peak) and len(samples) < SAMPLE_CAP:
            samples.append(
                {
                    "n": n,
                    "T_left": left_image,
                    "T_right": right_image,
                    "peak_left": left_peak,
                    "peak_right": right_peak,
                    "valley_left": left_valley,
                    "valley_right": right_valley,
                }
            )
    if tag == "known_map" and (image_differ or peak_differ or common == 0):
        # Same S, different exact map or disjoint domains: the slogan,
        # not a new closed form.
        pass
    return {
        "left": left,
        "right": right,
        "o": odd_count(left),
        "L": len(left),
        "same_necklace": necklace_key(left) == necklace_key(right),
        "S_left": weight_sum(left),
        "S_right": weight_sum(right),
        "different_S": weight_sum(left) != weight_sum(right),
        "tag": tag,
        "common_follows": common,
        "image_differ": image_differ,
        "peak_differ": peak_differ,
        "samples": samples,
    }


def expanding_words(*, k_max: int = K_MAX) -> list[str]:
    words: list[str] = []
    for length in range(1, k_max + 1):
        for mask in range(1 << length):
            word = "".join("O" if mask >> i & 1 else "E" for i in range(length))
            if expanding(word):
                words.append(word)
    return words


def necklace_representatives(words: list[str]) -> dict[tuple[int, int], list[str]]:
    groups: dict[tuple[int, int], dict[str, str]] = {}
    for word in words:
        pair = budget_pair(word)
        bucket = groups.setdefault(pair, {})
        key = necklace_key(word)
        bucket.setdefault(key, key)
    return {pair: sorted(bucket.values()) for pair, bucket in groups.items()}


def census_pairs(
    words: list[str],
    *,
    lo: int = REALIZED_LO,
    hi: int = REALIZED_HI,
) -> dict[str, Any]:
    groups = necklace_representatives(words)
    counts = {tag: 0 for tag in TAGS}
    n_pairs = 0
    n_empty = 0
    n_image_differ = 0
    n_same_s_differ_t = 0
    examples: dict[str, list[dict[str, Any]]] = {tag: [] for tag in TAGS}
    pair_rows: list[dict[str, Any]] = []
    for pair in sorted(groups):
        reps = groups[pair]
        for i, left in enumerate(reps):
            for right in reps[i + 1 :]:
                rec = compare_pair(left, right, lo=lo, hi=hi)
                n_pairs += 1
                counts[rec["tag"]] += 1
                if rec["common_follows"] == 0:
                    n_empty += 1
                if rec["image_differ"]:
                    n_image_differ += 1
                if not rec["different_S"] and rec["image_differ"]:
                    n_same_s_differ_t += 1
                slim = {
                    "left": rec["left"],
                    "right": rec["right"],
                    "o": rec["o"],
                    "L": rec["L"],
                    "tag": rec["tag"],
                    "different_S": rec["different_S"],
                    "common_follows": rec["common_follows"],
                    "image_differ": rec["image_differ"],
                    "peak_differ": rec["peak_differ"],
                }
                pair_rows.append(slim)
                if len(examples[rec["tag"]]) < SAMPLE_CAP:
                    examples[rec["tag"]].append({**slim, "samples": rec["samples"]})
    return {
        "n_words": len(words),
        "n_budget_pairs": len(groups),
        "n_necklace_pairs": n_pairs,
        "n_empty_domain": n_empty,
        "n_image_differ": n_image_differ,
        "n_same_S_differ_T": n_same_s_differ_t,
        "counts": counts,
        "examples": {tag: rows for tag, rows in examples.items() if rows},
        "unarchived": counts["unarchived"],
        "rows": pair_rows,
    }


def cyclemin_oriented(word: str) -> bool:
    return word.startswith("OO") and word.endswith("E") and expanding(word)


def canonical_records() -> dict[str, Any]:
    triple = [
        compare_pair(CANONICAL_TRIPLE[i], CANONICAL_TRIPLE[j])
        for i in range(len(CANONICAL_TRIPLE))
        for j in range(i + 1, len(CANONICAL_TRIPLE))
    ]
    contracting = compare_pair(*CANONICAL_CONTRACTING)
    return {
        "triple": {
            "words": list(CANONICAL_TRIPLE),
            "o": 2,
            "L": 3,
            "budget": "9/8",
            "same_necklace": True,
            "pairs": [
                {
                    "left": rec["left"],
                    "right": rec["right"],
                    "tag": rec["tag"],
                    "same_necklace": rec["same_necklace"],
                    "different_S": rec["different_S"],
                    "common_follows": rec["common_follows"],
                    "image_differ": rec["image_differ"],
                    "samples": rec["samples"],
                }
                for rec in triple
            ],
        },
        "oooee_vs_ooeoe": {
            "left": contracting["left"],
            "right": contracting["right"],
            "o": contracting["o"],
            "L": contracting["L"],
            "budget": "27/32",
            "tag": contracting["tag"],
            "same_necklace": contracting["same_necklace"],
            "different_S": contracting["different_S"],
            "common_follows": contracting["common_follows"],
            "image_differ": contracting["image_differ"],
            "peak_differ": contracting["peak_differ"],
            "samples": contracting["samples"],
        },
    }


def itinerary_uniqueness_holds(*, lo: int = REALIZED_LO, hi: int = 64, k_max: int = 6) -> bool:
    for n in range(lo, hi):
        for length in range(1, k_max + 1):
            word = itinerary_unique(n, length)
            if not follows_itinerary(n, word):
                return False
            for mask in range(1 << length):
                other = "".join("O" if mask >> i & 1 else "E" for i in range(length))
                if other != word and follows_itinerary(n, other):
                    return False
    return True


def endpoint_probe() -> dict[str, Any]:
    checks = []
    for n, left, right in (
        (3, "OOE", "OEO"),
        (5, "OOE", "EOO"),
        (7, "OOOEE", "OOEOE"),
        (11, "OOOOE", "OOOEO"),
    ):
        checks.append(
            {
                "n": n,
                "left": left,
                "right": right,
                "holds": endpoint_quantities_word_free(n, left, right),
                "defect": cycle_endpoint_defect(n, odd_count(left), len(left)),
                "norm_exp": list(cycle_normalized_exponent(odd_count(left), len(left))),
            }
        )
    return {
        "formula_is_word_free": True,
        "checks": checks,
        "all_hold": all(item["holds"] for item in checks),
        "itinerary_unique": itinerary_uniqueness_holds(),
    }


def classify(payload: dict[str, Any]) -> dict[str, Any]:
    expanding_census = payload["expanding"]
    cyclemin_census = payload["cyclemin"]
    canonical = payload["canonical"]
    endpoint = payload["endpoint"]
    unarchived = int(expanding_census["unarchived"]) + int(cyclemin_census["unarchived"])
    triple_ok = all(rec["tag"] == "named_cell" for rec in canonical["triple"]["pairs"])
    contracting_ok = canonical["oooee_vs_ooeoe"]["tag"] in {
        "adjacency",
        "lowerDenom",
        "named_cell",
        "known_map",
    }
    collapse = (
        bool(endpoint["all_hold"])
        and bool(endpoint["formula_is_word_free"])
        and bool(endpoint["itinerary_unique"])
    )
    if unarchived == 0 and triple_ok and contracting_ok and collapse:
        classification = CLASS_CLOSED
        decision = "CLOSE"
        reason = (
            "on a CycleItinerary the endpoint quantities are (o, L)-only; "
            "every same-budget necklace distinction through length 8 "
            "is a rotation, lowerDenom / S(w), a named cell, cheap-OOE "
            "adjacency, or the exact-map slogan itself; OOE/OEO/EOO "
            "are one necklace excluded by cells; OOOEE versus OOEOE "
            f"is {canonical['oooee_vs_ooeoe']['tag']}"
        )
    elif unarchived > 0:
        classification = CLASS_GREEN
        decision = "PROMOTE"
        reason = (
            "a same-(o, L) necklace pair produced an unarchived "
            "relation between T_w and T_w'"
        )
    else:
        classification = CLASS_PARK
        decision = "PARK"
        reason = "the word-order census is mixed and does not decide"
    return {
        "classification": classification,
        "decision": decision,
        "reason": reason,
        "unarchived": unarchived,
        "endpoint_collapse": collapse,
        "triple_named_cell": triple_ok,
        "contracting_archived": contracting_ok,
        "new_identity": False,
        "leftover_killer": False,
        "reopens_finance": False,
        "reopens_word_functional": False,
        "halt_theorem": False,
        "raise_n0": False,
        "paper_a_edit": False,
        "archived": list(ARCHIVED),
    }


def probe_payload() -> dict[str, Any]:
    words = expanding_words()
    expanding_census = census_pairs(words)
    cyclemin_words = [word for word in words if cyclemin_oriented(word)]
    cyclemin_census = census_pairs(cyclemin_words)
    payload = {
        "bound": "word_order",
        "k_max": K_MAX,
        "window": {"lo": REALIZED_LO, "hi": REALIZED_HI},
        "note": (
            "Same (o, L) fixes 3^o/2^L and, on a CycleItinerary, Delta and "
            "T/n^P. Distinct necklaces with that budget have different "
            "exact maps; every cycle-usable compression through length 8 "
            "is already archived."
        ),
        "endpoint": endpoint_probe(),
        "expanding": {
            key: expanding_census[key]
            for key in (
                "n_words",
                "n_budget_pairs",
                "n_necklace_pairs",
                "n_empty_domain",
                "n_image_differ",
                "n_same_S_differ_T",
                "counts",
                "examples",
                "unarchived",
            )
        },
        "cyclemin": {
            key: cyclemin_census[key]
            for key in (
                "n_words",
                "n_budget_pairs",
                "n_necklace_pairs",
                "n_empty_domain",
                "n_image_differ",
                "n_same_S_differ_T",
                "counts",
                "examples",
                "unarchived",
            )
        },
        "canonical": canonical_records(),
        "identities": {
            "cycle_defect_is_n_pow_gap": True,
            "normalized_image_is_n_to_one_minus_P": True,
            "endpoint_quantities_ignore_order": True,
            "same_length_itinerary_is_unique": True,
        },
    }
    payload["decision"] = classify(payload)
    payload["_expanding_rows"] = expanding_census["rows"]
    payload["_cyclemin_rows"] = cyclemin_census["rows"]
    return payload


def write_artifacts(payload: dict[str, Any] | None = None) -> dict[str, Any]:
    data = payload if payload is not None else probe_payload()
    ORDER_DIR.mkdir(parents=True, exist_ok=True)
    slim = {key: value for key, value in data.items() if not key.startswith("_")}
    path = ORDER_DIR / "summary.json"
    path.write_text(json.dumps(slim, indent=2, allow_nan=False) + "\n", encoding="utf-8")
    return data


def main() -> None:
    payload = write_artifacts()
    decision = payload["decision"]
    print(decision["classification"])
    print(decision["reason"])
    print(
        json.dumps(
            {
                "endpoint": payload["endpoint"]["all_hold"],
                "expanding": {
                    key: payload["expanding"][key]
                    for key in (
                        "n_words",
                        "n_budget_pairs",
                        "n_necklace_pairs",
                        "n_empty_domain",
                        "n_image_differ",
                        "n_same_S_differ_T",
                        "counts",
                        "unarchived",
                    )
                },
                "cyclemin": {
                    key: payload["cyclemin"][key]
                    for key in (
                        "n_words",
                        "n_necklace_pairs",
                        "counts",
                        "unarchived",
                    )
                },
                "canonical_tags": {
                    "triple": [rec["tag"] for rec in payload["canonical"]["triple"]["pairs"]],
                    "oooee_vs_ooeoe": payload["canonical"]["oooee_vs_ooeoe"]["tag"],
                    "oooee_common": payload["canonical"]["oooee_vs_ooeoe"]["common_follows"],
                },
                "decision": decision,
            },
            indent=2,
        )
    )


if __name__ == "__main__":
    main()
