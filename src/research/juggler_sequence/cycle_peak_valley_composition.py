"""Peak–valley interval composition around a necklace.

Phase 0 only: compose the exact cells

    P --E^r--> V --O^a--> P'

around a cyclic word and test whether the composite is forced off
the diagonal (P > P or P < P) for a reason that is not the
word-envelope exponent, the trailing-evens cell, or the closed
cycle-closure leftover-killer.

The exact cells determine a function, not a multi-valued interval
map. One-sided envelopes compose to power_bound_word. Leftover
words expand, so they do not give P' < P.

Not a reopen of seam sliding, the E^r block, cycle closure, or
extremal composition. Not a finance leftover-killer, not a halt
theorem, and not a claim that every positive integer reaches 1.

Dossier: docs/problems/juggler_cycle_peak_valley_composition.md.
"""

from __future__ import annotations

import json
from fractions import Fraction
from typing import Any

from research.juggler_sequence.cycle_almost_search import circuits
from research.juggler_sequence.cycle_e_block import even_tower_bounds, isqrt_iter
from research.juggler_sequence.cycle_finance import DATA_DIR
from research.juggler_sequence.power_itineraries import floor_power

COMPOSE_DIR = DATA_DIR / "peak_valley_composition"

CLASS_CLOSED = "PEAK_VALLEY_COMPOSITION_CLOSED"
CLASS_GREEN = "PEAK_VALLEY_COMPOSITION_GREEN"
CLASS_PARK = "PEAK_VALLEY_COMPOSITION_PARK"

ARCHIVED = (
    "power_bound_word",
    "power_bound_contracts",
    "cycle_trailing_evens_lt",
    "even_run_scale_barrier",
    "even_tower_bounds",
    "global_defect_identity",
    "cycle_itinerary_formally_expanding",
    "two_block_ooe_365",
)

# Reviewer necklace units: contracting, expanding, leftover-shaped.
WORD_OE = "OE"
WORD_OOE = "OOE"
WORD_OOOEE = "OOOEE"
WORD_TWO_OOE = "OOEOOE"
WORD_L11 = "OOEOOEOOEOE"

# cycle_closure mechanical meeting; do not recompute L=25781.
MECHANICAL_L25781 = {
    "L": 25781,
    "interval": [986891, 25482877],
    "meets_start": True,
    "source": "cycle_closure leftover-killer CLOSE",
}


def follow_word(n: int, word: str) -> int | None:
    current = n
    for letter in word:
        if letter == "O" and current % 2 == 0:
            return None
        if letter == "E" and current % 2 == 1:
            return None
        current = floor_power(current)
    return current


def first_realized(word: str, *, lo: int = 3, hi: int = 5001) -> int | None:
    start = lo if lo % 2 else lo + 1
    for n in range(start, hi, 2):
        if follow_word(n, word) is not None:
            return n
    return None


def peak_valley_blocks(word: str) -> list[tuple[int, int]]:
    """Blocks P --E^r--> V --O^a--> P' of a start-O / end-E necklace."""

    pairs = circuits(word)
    out: list[tuple[int, int]] = []
    for index, (_a, r) in enumerate(pairs):
        a_next = pairs[(index + 1) % len(pairs)][0]
        out.append((r, a_next))
    return out


def composite_exponent(word: str) -> Fraction:
    """Product of block maps P |-> P^{3^a / 2^{a+r}} = 3^o / 2^L."""

    odd = word.count("O")
    length = len(word)
    return Fraction(3**odd, 1 << length)


def blocks_exponent(blocks: list[tuple[int, int]]) -> Fraction:
    acc = Fraction(1, 1)
    for r, a in blocks:
        acc *= Fraction(3**a, 1 << (a + r))
    return acc


def apply_peak_block(peak: int, r: int, a: int) -> int | None:
    valley = isqrt_iter(peak, r)
    cell = even_tower_bounds(valley, r)
    if not (cell["p_lo"] <= peak < cell["p_hi"]):
        return None
    current = valley
    for _ in range(a):
        if current % 2 == 0:
            return None
        current = floor_power(current)
    return current


def exact_peak_composite(peak: int, word: str) -> int | None:
    current = peak
    for r, a in peak_valley_blocks(word):
        nxt = apply_peak_block(current, r, a)
        if nxt is None:
            return None
        current = nxt
    return current


def exact_valley_composite(start: int, word: str) -> int | None:
    """V --O^a--> P --E^r--> V' along circuits; equals follow_word."""

    current = start
    for a, r in circuits(word):
        for _ in range(a):
            if current % 2 == 0:
                return None
            current = floor_power(current)
        for _ in range(r):
            if current % 2 == 1:
                return None
            current = floor_power(current)
    return current


def rotate_to_first_peak(word: str) -> str:
    a0, _r0 = circuits(word)[0]
    return word[a0:] + word[:a0]


def first_peak(start: int, word: str) -> int | None:
    a0, _r0 = circuits(word)[0]
    current = start
    for _ in range(a0):
        if current % 2 == 0:
            return None
        current = floor_power(current)
    return current


def naive_odd_image(valley: int, a: int) -> int:
    """floor(V^{3^a / 2^a}): valley-to-peak envelope, not the nested climb."""

    if valley < 1 or a < 1:
        raise ValueError("naive_odd_image requires valley, a >= 1")
    return isqrt_iter(valley ** (3**a), a)


def naive_block_image(valley: int, a: int, r: int) -> int:
    """floor(V^{3^a / 2^{a+r}}): valley-to-valley envelope of one block."""

    if valley < 1 or a < 1 or r < 1:
        raise ValueError("naive_block_image requires valley, a, r >= 1")
    return isqrt_iter(valley ** (3**a), a + r)


def envelope_upper(peak: float, word: str) -> float:
    mu = float(composite_exponent(word))
    return peak**mu


def slack_lower(peak: float, word: str) -> float:
    """One-sided +1 slack: V > P^{1/2^r} - 1, then the real odd climb.

    This is the reviewer's interval widening, not the exact cell.
    Exact cells fix V = isqrt^r(P) uniquely.
    """

    current = float(peak)
    for r, a in peak_valley_blocks(word):
        valley = current ** (1.0 / (1 << r)) - 1.0
        if valley <= 1.0:
            return 0.0
        current = valley ** (3**a / float(1 << a))
    return current


def onesided_upper_is_power_bound(word: str) -> bool:
    return blocks_exponent(peak_valley_blocks(word)) == composite_exponent(word)


def functional_identity(start: int, word: str) -> dict[str, Any]:
    image = follow_word(start, word)
    valley = exact_valley_composite(start, word)
    peak = first_peak(start, word)
    rotated = rotate_to_first_peak(word)
    peak_image = None if peak is None else exact_peak_composite(peak, word)
    rotated_image = None if peak is None else follow_word(peak, rotated)
    return {
        "start": start,
        "word": word,
        "follow": image,
        "valley_composite": valley,
        "first_peak": peak,
        "peak_composite": peak_image,
        "rotated_follow": rotated_image,
        "valley_is_follow": image is not None and image == valley,
        # Wrap may be unrealized on a transient (both None). Equality
        # still says the block map is T on the rotated spelling.
        "peak_is_rotated_follow": peak_image == rotated_image,
    }


def exponent_row(word: str) -> dict[str, Any]:
    mu = composite_exponent(word)
    return {
        "word": word,
        "length": len(word),
        "odd": word.count("O"),
        "blocks": [list(pair) for pair in peak_valley_blocks(word)],
        "mu_num": mu.numerator,
        "mu_den": mu.denominator,
        "mu": float(mu),
        "blocks_match_word": onesided_upper_is_power_bound(word),
        "contracts": mu < 1,
        "expands": mu > 1,
    }


def slack_row(peak: float, word: str) -> dict[str, Any]:
    lo = slack_lower(peak, word)
    hi = envelope_upper(peak, word)
    return {
        "peak": peak,
        "word": word,
        "slack_lower": lo,
        "envelope_upper": hi,
        "contains_peak": lo <= peak <= hi,
        "upper_gt_peak": hi > peak,
        "lower_lt_peak": lo < peak,
        "entirely_above": lo > peak,
        "entirely_below": hi < peak,
    }


def classify(payload: dict[str, Any]) -> dict[str, Any]:
    identities = payload["identities"]
    exponents = payload["exponents"]
    functional = all(row["valley_is_follow"] and row["peak_is_rotated_follow"] for row in identities)
    power_bound = all(row["blocks_match_word"] for row in exponents)
    oooee = next(row for row in exponents if row["word"] == WORD_OOOEE)
    l11 = next(row for row in exponents if row["word"] == WORD_L11)
    expanding = payload["expanding_witness"]
    slack = payload["slack"]
    leftover_slack = [row for row in slack if row["word"] == WORD_L11]
    oooee_slack = next(row for row in slack if row["word"] == WORD_OOOEE)
    leftover_above = all(row["entirely_above"] for row in leftover_slack)
    contracting_below = bool(oooee_slack["entirely_below"])
    expanding_gt = expanding["image"] > expanding["start"]
    mechanical = payload["mechanical_l25781"]["meets_start"]
    new_inequality = False
    if new_inequality:
        classification = CLASS_GREEN
        decision = "PROMOTE"
        reason = (
            "the necklace composite forces P>P or P<P for a reason "
            "that is not the exponent gap or an archived cell"
        )
    elif (
        functional
        and power_bound
        and oooee["contracts"]
        and l11["expands"]
        and expanding_gt
        and leftover_above
        and contracting_below
        and mechanical
    ):
        classification = CLASS_CLOSED
        decision = "CLOSE"
        reason = (
            "exact peak–valley cells compose to T_w, so a cycle has "
            "P=P; one-sided composition is power_bound_word; leftover "
            "real intervals sit above P because 3^o>2^L, and "
            "contracting intervals sit below P because 3^o<2^L; that "
            "sign is the closed exponent budget; the mechanical "
            "meeting is the closed cycle-closure leftover-killer"
        )
    else:
        classification = CLASS_PARK
        decision = "PARK"
        reason = "the necklace census is mixed and does not decide"
    return {
        "classification": classification,
        "decision": decision,
        "reason": reason,
        "exact_cells_are_functional": functional,
        "onesided_is_power_bound": power_bound,
        "contracting_is_exponent_gap": bool(oooee["contracts"]),
        "leftover_expands": bool(l11["expands"]),
        "expanding_witness_gt": expanding_gt,
        "leftover_real_interval_above": leftover_above,
        "contracting_real_interval_below": contracting_below,
        "mechanical_meets": mechanical,
        "new_inequality": new_inequality,
        "leftover_killer": False,
        "reopens_cycle_closure": False,
        "reopens_seam_sliding": False,
        "reopens_exponent_budget": False,
        "halt_theorem": False,
        "raise_n0": False,
        "paper_a_edit": False,
        "archived": list(ARCHIVED),
    }


def probe_payload() -> dict[str, Any]:
    words = (WORD_OE, WORD_OOE, WORD_OOOEE, WORD_TWO_OOE, WORD_L11)
    realized = {word: first_realized(word) for word in words}
    identity_starts = {
        WORD_OE: 7,
        WORD_OOE: 365,
        WORD_OOOEE: 25,
        WORD_TWO_OOE: 365,
    }
    identities = [
        functional_identity(start, word) for word, start in identity_starts.items()
    ]
    two = follow_word(365, WORD_TWO_OOE)
    ooe_valley = 365
    ooe_exact = follow_word(ooe_valley, WORD_OOE)
    ooe_naive_peak = naive_odd_image(ooe_valley, 2) if ooe_exact is not None else None
    ooe_naive_valley = naive_block_image(ooe_valley, 2, 1) if ooe_exact is not None else None
    ooe_peak = first_peak(ooe_valley, WORD_OOE)
    oooee_peak = first_peak(25, WORD_OOOEE)
    slack = [
        slack_row(1_000.0, WORD_L11),
        slack_row(1_000_000.0, WORD_L11),
        slack_row(float(oooee_peak), WORD_OOOEE) if oooee_peak is not None else slack_row(1.0, WORD_OOOEE),
        slack_row(365.0, WORD_TWO_OOE),
    ]
    payload = {
        "bound": "peak_valley_composition",
        "archived": list(ARCHIVED),
        "words": list(words),
        "realized": realized,
        "exponents": [exponent_row(word) for word in words],
        "identities": identities,
        "expanding_witness": {
            "start": 365,
            "word": WORD_TWO_OOE,
            "image": two,
            "lean": "two_block_ooe_365",
            "note": "365 --OOE--> 763 --OOE--> 1749 is expansion, not P<P",
        },
        "naive_vs_exact_ooe": {
            "valley": ooe_valley,
            "exact_valley": ooe_exact,
            "exact_peak": ooe_peak,
            "naive_peak": ooe_naive_peak,
            "naive_valley": ooe_naive_valley,
            "naive_is_envelope": True,
            "note": (
                "floor(V^{9/4}) and floor(V^{9/8}) are envelopes; "
                "the exact climb is the nested floor-power"
            ),
        },
        "realized_l11": {
            "start": realized[WORD_L11],
            "word": WORD_L11,
            "image": follow_word(realized[WORD_L11], WORD_L11)
            if realized[WORD_L11] is not None
            else None,
        },
        "slack": slack,
        "mechanical_l25781": dict(MECHANICAL_L25781),
        "odd_fixed_point": {
            "n": 1,
            "word": "O",
            "is_peak_valley_necklace": False,
            "note": "the odd fixed point has no even letter, so it is not a P-V necklace",
        },
    }
    payload["decision"] = classify(payload)
    return payload


def write_artifacts(payload: dict[str, Any] | None = None) -> dict[str, Any]:
    data = payload if payload is not None else probe_payload()
    COMPOSE_DIR.mkdir(parents=True, exist_ok=True)
    path = COMPOSE_DIR / "summary.json"
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
                "exponents": [
                    {
                        "word": row["word"],
                        "mu": f"{row['mu_num']}/{row['mu_den']}",
                        "contracts": row["contracts"],
                    }
                    for row in payload["exponents"]
                ],
                "expanding": payload["expanding_witness"]["image"],
                "slack_l11_1e6_above": payload["slack"][1]["entirely_above"],
                "decision": decision["decision"],
            },
            indent=2,
        )
    )


if __name__ == "__main__":
    main()
