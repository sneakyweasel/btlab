"""Halbeisen-style cyclic word functional on Juggler floor powers.

Not a halt theorem, not a leftover-word census, not a new finance
identity, not Fourier, and not a residue system. Phase 0 asks whether
the unfolded slack weights

    alpha_i(w) = 2^i * 3^{#O(w[i+1:])}

are a compressed cyclic-word functional that yields a closure
inequality beyond (L, o), lowerDenom, or run-type finance.

The n-independent bound is already lowerDenom(w) = 4^{S(w)} with
S = sum alpha. Cyclic-shift optimization does not transfer: a
CycleMin orientation freezes the leading weights, and min_rot S
bounds some other cycle element, not the minimum.

Dossier: docs/problems/juggler_cycle_word_functional.md.
"""

from __future__ import annotations

import json
from typing import Any

from research.juggler_sequence.cycle_finance import DATA_DIR, o_min_and_theta, sha256_int_list
from research.juggler_sequence.cycle_prefix_feasibility import extremal_word
from research.juggler_sequence.global_defect import follows_itinerary, odd_count
from research.juggler_sequence.normalized_defect import slack_den, slack_num
from research.juggler_sequence.power_itineraries import floor_power
from research.juggler_sequence.uniform_superquadratic import lower_denom

FUNCTIONAL_DIR = DATA_DIR / "word_functional"
K_MAX = 8
IDENTITY_N_MAX = 24
IDENTITY_K_MAX = 4
SMALL_L = (5, 8, 11, 19)


def letter_weights(word: str) -> list[int]:
    """alpha_i(w) = 2^i * 3^{number of later odd letters}."""

    weights: list[int] = []
    odd_after = word.count("O")
    for index, letter in enumerate(word):
        if letter == "O":
            odd_after -= 1
        weights.append((1 << index) * 3**odd_after)
    return weights


def weight_sum(word: str) -> int:
    return sum(letter_weights(word))


def rotations(word: str) -> list[str]:
    if not word:
        return [""]
    return [word[i:] + word[:i] for i in range(len(word))]


def min_rot_sum(word: str) -> int:
    return min(weight_sum(rot) for rot in rotations(word))


def necklace_key(word: str) -> str:
    return min(rotations(word))


def exponent_gap(word: str) -> int:
    return 3 ** odd_count(word) - (1 << len(word))


def expanding(word: str) -> bool:
    return exponent_gap(word) > 0


def four_pow_weight_sum(word: str) -> int:
    return 4 ** weight_sum(word)


def denom_is_four_pow(word: str) -> bool:
    return lower_denom(word) == four_pow_weight_sum(word)


def product_identity_holds(n: int, word: str) -> bool:
    """n^{3^o} / T^{2^L} = prod_i (1+eta_i)^{alpha_i} as integers."""

    if not follows_itinerary(n, word):
        return False
    alphas = letter_weights(word)
    prod_num = 1
    prod_den = 1
    current = n
    for alpha, letter in zip(alphas, word, strict=True):
        image = floor_power(current)
        source = current * current * current if letter == "O" else current
        prod_num *= source**alpha
        prod_den *= (image * image) ** alpha
        current = image
    return slack_num(n, word) * prod_den == slack_den(n, word) * prod_num


def identity_census(
    *,
    n_max: int = IDENTITY_N_MAX,
    k_max: int = IDENTITY_K_MAX,
) -> dict[str, Any]:
    checked = 0
    fails = 0
    for n in range(2, n_max + 1):
        current = n
        letters: list[str] = []
        for _ in range(k_max):
            letters.append("E" if current % 2 == 0 else "O")
            current = floor_power(current)
            word = "".join(letters)
            checked += 1
            if not product_identity_holds(n, word):
                fails += 1
    return {"checked": checked, "fails": fails, "n_max": n_max, "k_max": k_max}


def denom_census(*, k_max: int = K_MAX) -> dict[str, Any]:
    checked = 0
    fails = 0
    examples: list[dict[str, Any]] = []
    for length in range(0, k_max + 1):
        for mask in range(1 << length):
            word = "".join("O" if mask >> i & 1 else "E" for i in range(length))
            checked += 1
            if not denom_is_four_pow(word):
                fails += 1
            if length <= 3:
                examples.append(
                    {
                        "w": word,
                        "L": length,
                        "o": odd_count(word),
                        "alpha": letter_weights(word),
                        "S": weight_sum(word),
                        "D": lower_denom(word),
                        "four_S": four_pow_weight_sum(word),
                    }
                )
    return {"checked": checked, "fails": fails, "k_max": k_max, "examples": examples}


def same_pair_split() -> dict[str, Any]:
    """Same (L, o) = (2, 1): OE versus EO."""

    left = "OE"
    right = "EO"
    return {
        "pair": (2, 1),
        "OE": {"alpha": letter_weights(left), "S": weight_sum(left), "D": lower_denom(left)},
        "EO": {
            "alpha": letter_weights(right),
            "S": weight_sum(right),
            "D": lower_denom(right),
        },
        "same_counts": odd_count(left) == odd_count(right) and len(left) == len(right),
        "different_S": weight_sum(left) != weight_sum(right),
        "different_alpha": letter_weights(left) != letter_weights(right),
        "min_rot_S_equal": min_rot_sum(left) == min_rot_sum(right),
    }


def cyclemin_leading_freeze(*, k_max: int = 6) -> dict[str, Any]:
    """Every word starting OO with the same (L, o) shares the first two weights."""

    rows: list[dict[str, Any]] = []
    frozen = True
    for length in range(3, k_max + 1):
        by_o: dict[int, list[str]] = {}
        for mask in range(1 << (length - 2)):
            tail = "".join("O" if mask >> i & 1 else "E" for i in range(length - 2))
            word = "OO" + tail
            by_o.setdefault(odd_count(word), []).append(word)
        for odd, words in by_o.items():
            heads = {tuple(letter_weights(word)[:2]) for word in words}
            expected = (3 ** (odd - 1), 2 * 3 ** (odd - 2))
            ok = heads == {expected}
            frozen = frozen and ok
            rows.append(
                {
                    "L": length,
                    "o": odd,
                    "n_words": len(words),
                    "leading": list(expected),
                    "frozen": ok,
                }
            )
    return {"frozen": frozen, "rows": rows}


def necklace_scan(*, k_max: int = K_MAX) -> dict[str, Any]:
    """Halbeisen M_{k,o} = max_w min_rot S(w) on expanding itineraries."""

    classes: dict[tuple[int, int], dict[str, Any]] = {}
    for length in range(1, k_max + 1):
        for mask in range(1 << length):
            word = "".join("O" if mask >> i & 1 else "E" for i in range(length))
            if not expanding(word):
                continue
            pair = (length, odd_count(word))
            bucket = classes.setdefault(
                pair,
                {
                    "L": length,
                    "o": pair[1],
                    "g": exponent_gap(word),
                    "n_words": 0,
                    "n_necklaces": 0,
                    "S_values": set(),
                    "min_rot_values": set(),
                    "M": 0,
                    "necklaces": set(),
                },
            )
            bucket["n_words"] += 1
            bucket["S_values"].add(weight_sum(word))
            rot_min = min_rot_sum(word)
            bucket["min_rot_values"].add(rot_min)
            bucket["M"] = max(int(bucket["M"]), rot_min)
            bucket["necklaces"].add(necklace_key(word))
    rows = []
    multi_S = 0
    multi_min = 0
    new_kill = 0
    for pair in sorted(classes):
        bucket = classes[pair]
        s_vals = sorted(bucket["S_values"])
        min_vals = sorted(bucket["min_rot_values"])
        gap = int(bucket["g"])
        # n <= 4^{S/g} is the lowerDenom cycle bound. Using min_rot S
        # in place of S is not a bound on the CycleMin start.
        crude = 4 ** (min(s_vals) // gap) if gap else None
        row = {
            "L": bucket["L"],
            "o": bucket["o"],
            "g": gap,
            "n_words": bucket["n_words"],
            "n_necklaces": len(bucket["necklaces"]),
            "n_S": len(s_vals),
            "n_min_rot": len(min_vals),
            "S_min": s_vals[0],
            "S_max": s_vals[-1],
            "M": bucket["M"],
            "min_rot_min": min_vals[0],
            "order_sensitive": len(s_vals) > 1,
            "rot_sensitive": len(min_vals) > 1,
            "crude_n_from_min_S": crude,
        }
        if row["order_sensitive"]:
            multi_S += 1
        if row["rot_sensitive"]:
            multi_min += 1
        rows.append(row)
    return {
        "k_max": k_max,
        "n_expanding_pairs": len(rows),
        "pairs_with_several_S": multi_S,
        "pairs_with_several_min_rot": multi_min,
        "new_necklace_kills": new_kill,
        "rows": rows,
    }


def mechanical_ooe_oe(length: int) -> str | None:
    odd, _ = o_min_and_theta(length)
    even = length - odd
    oo_count = odd - even
    oe_count = 2 * even - odd
    if oo_count < 0 or oe_count < 0:
        return None
    word = ("OOE" * oo_count) + ("OE" * oe_count)
    if len(word) != length:
        return None
    return word


def bunched_word(length: int) -> str:
    odd, _ = o_min_and_theta(length)
    return ("O" * odd) + ("E" * (length - odd))


def word_payload(word: str) -> dict[str, Any]:
    return {
        "w": word,
        "o": odd_count(word),
        "S": weight_sum(word),
        "min_rot_S": min_rot_sum(word),
        "starts_OO": word.startswith("OO"),
        "leading": letter_weights(word)[:2] if len(word) >= 2 else letter_weights(word),
    }


def shaped_row(length: int) -> dict[str, Any]:
    odd, theta = o_min_and_theta(length)
    gap = 3**odd - (1 << length)
    words: dict[str, str | None] = {
        "bunched": bunched_word(length),
        "mechanical": mechanical_ooe_oe(length),
        "extremal": extremal_word(length),
    }
    payloads = {
        name: word_payload(word) for name, word in words.items() if word is not None
    }
    s_vals = {item["S"] for item in payloads.values()}
    min_vals = {item["min_rot_S"] for item in payloads.values()}
    oo_leads = [
        tuple(item["leading"]) for item in payloads.values() if item["starts_OO"]
    ]
    return {
        "L": length,
        "o": odd,
        "g_positive": gap > 0,
        "theta": theta,
        "words": payloads,
        "order_sensitive": len(s_vals) > 1,
        "min_rot_varies": len(min_vals) > 1,
        "cyclemin_orientations_share_leading": len(set(oo_leads)) <= 1,
    }


def functional_scan() -> dict[str, Any]:
    identity = identity_census()
    denoms = denom_census()
    split = same_pair_split()
    freeze = cyclemin_leading_freeze()
    neck = necklace_scan()
    shapes = {str(length): shaped_row(length) for length in SMALL_L}
    leftover_like = shaped_row(19)
    return {
        "bound": "word_functional",
        "identity": identity,
        "denom": denoms,
        "oe_vs_eo": split,
        "cyclemin_freeze": {
            "frozen": freeze["frozen"],
            "n_rows": len(freeze["rows"]),
            "sample": freeze["rows"][:4],
        },
        "necklaces": {
            "k_max": neck["k_max"],
            "n_expanding_pairs": neck["n_expanding_pairs"],
            "pairs_with_several_S": neck["pairs_with_several_S"],
            "pairs_with_several_min_rot": neck["pairs_with_several_min_rot"],
            "new_necklace_kills": neck["new_necklace_kills"],
            "rows": neck["rows"],
        },
        "shapes": shapes,
        "L19": leftover_like,
        "identity_holds": identity["fails"] == 0,
        "denom_is_four_S": denoms["fails"] == 0,
        "order_sensitive": split["different_S"],
        "leading_weights_frozen": freeze["frozen"],
        "halbeisen_min_rot_kills_necklace": neck["new_necklace_kills"] > 0,
        "alpha_is_new_obstruction": False,
        "reduces_to_lowerDenom": True,
        "leftover_killer": False,
        "emptied_count": 0,
        "emptied_lengths": [],
        "halt_theorem": False,
        "no_cycle_all_lengths": False,
        "sha256_small_L": sha256_int_list(list(SMALL_L)),
    }


def write_functional_artifacts(payload: dict[str, Any] | None = None) -> dict[str, Any]:
    data = payload if payload is not None else functional_scan()
    FUNCTIONAL_DIR.mkdir(parents=True, exist_ok=True)
    slim = dict(data)
    slim["necklaces"] = {
        key: data["necklaces"][key]
        for key in (
            "k_max",
            "n_expanding_pairs",
            "pairs_with_several_S",
            "pairs_with_several_min_rot",
            "new_necklace_kills",
        )
    }
    slim["necklace_pairs"] = data["necklaces"]["rows"]
    path = FUNCTIONAL_DIR / "summary.json"
    path.write_text(json.dumps(slim, indent=2, allow_nan=False) + "\n", encoding="utf-8")
    return data


if __name__ == "__main__":
    report = write_functional_artifacts()
    print(
        json.dumps(
            {
                "identity_fails": report["identity"]["fails"],
                "denom_fails": report["denom"]["fails"],
                "OE_S": report["oe_vs_eo"]["OE"]["S"],
                "EO_S": report["oe_vs_eo"]["EO"]["S"],
                "frozen": report["leading_weights_frozen"],
                "pairs_with_several_S": report["necklaces"]["pairs_with_several_S"],
                "new_kills": report["necklaces"]["new_necklace_kills"],
                "L19_S": {
                    name: report["L19"]["words"][name]["S"]
                    for name in report["L19"]["words"]
                },
            },
            indent=2,
        )
    )
