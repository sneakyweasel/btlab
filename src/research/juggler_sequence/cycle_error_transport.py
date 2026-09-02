"""Ordered floor-error transport, split at the O|E seam.

Phase 0 only: unroll accumulatedDefect into a per-letter vector.
Each local remainder is inserted as a powGap chunk and lifted
through the suffix with later remainders dropped (amplifyDefect).
The vector is split into a climb half E_O and a descent half E_E.
Cross terms X = Delta - sum e_i are the cubic mixings already
inside accumulateOdd.

Do not test Delta versus G as the obstruction. The question is
whether a seam half, a single position, or the ordered pair
(E_O, E_E) obstructs without passing through the scalar defect.

Not a reopen of first-defect Amplify, cluster Amplify, finance,
defect congruence, peak-valley composition, or cumulative floor
loss. Not a leftover-killer, not a halt theorem, and not a claim
that every positive integer reaches 1.

Dossier: docs/problems/juggler_cycle_error_transport.md.
"""

from __future__ import annotations

import json
from typing import Any

from research.juggler_sequence.cycle_almost_search import circuits
from research.juggler_sequence.cycle_finance import DATA_DIR
from research.juggler_sequence.defect_lower_bound import (
    amplify_defect,
    amplify_from_first,
    first_defect,
    formal_surplus,
)
from research.juggler_sequence.global_defect import (
    follows_itinerary,
    global_defect,
    image_after,
    local_defect,
    odd_count,
    pow_gap,
)
from research.juggler_sequence.power_itineraries import floor_power

TRANSPORT_DIR = DATA_DIR / "error_transport"

CLASS_CLOSED = "ERROR_TRANSPORT_CLOSED"
CLASS_GREEN = "ERROR_TRANSPORT_GREEN"
CLASS_PARK = "ERROR_TRANSPORT_PARK"

WORD_OE = "OE"
WORD_OOE = "OOE"
WORD_OOOEE = "OOOEE"
WORD_TWO_OOE = "OOEOOE"
WORD_L11 = "OOEOOEOOEOE"

CASES = (
    (13, WORD_OE),
    (25, WORD_OOOEE),
    (365, WORD_OOE),
    (1517, WORD_OOE),
    (1_000_057, WORD_OOE),
    (365, WORD_TWO_OOE),
    (429, WORD_L11),
)

ARCHIVED = (
    "global_defect_identity",
    "accumulatedDefect",
    "amplifyDefect",
    "firstDefect",
    "cycleMin_finance",
    "cycle_itinerary_formally_expanding",
    "power_bound_word",
    "power_bound_contracts",
)

COMPACT_BITS = 200


def first_realized(word: str, *, lo: int = 3, hi: int = 5001) -> int | None:
    start = lo if lo % 2 else lo + 1
    for n in range(start, hi, 2):
        if follows_itinerary(n, word):
            return n
    return None


def formal_weight(word: str, index: int) -> int:
    """State-free suffix factor: 3 to the remaining-odd count."""

    return 3 ** odd_count(word[index + 1 :])


def has_shared_later_odd(word: str) -> bool:
    """Two letters whose chunks are both cubed by a later odd."""

    odds = [i for i, letter in enumerate(word) if letter == "O"]
    return any(
        any(word[k] == "O" for k in range(right + 1, len(word)))
        for right in odds[1:]
    )


def letter_transport(n: int, word: str, index: int) -> dict[str, Any]:
    """Insert rho_i at letter i and amplify through the suffix."""

    if not follows_itinerary(n, word):
        raise ValueError(f"{n} does not follow {word}")
    current = n
    for _ in range(index):
        current = floor_power(current)
    rho = local_defect(current)
    image = floor_power(current)
    chunk = pow_gap(image * image, rho, 1 << index)
    transported = amplify_defect(image, chunk, index + 1, word[index + 1 :])
    return {
        "i": index,
        "letter": word[index],
        "x": current,
        "rho": rho,
        "chunk": chunk,
        "e": transported,
        "W": formal_weight(word, index),
    }


def seam_halves(rows: list[dict[str, Any]]) -> dict[str, int]:
    climb = sum(row["e"] for row in rows if row["letter"] == "O")
    descent = sum(row["e"] for row in rows if row["letter"] == "E")
    return {"E_O": climb, "E_E": descent, "sum": climb + descent}


def block_halves(word: str, rows: list[dict[str, Any]]) -> list[dict[str, Any]]:
    pairs = circuits(word)
    index = 0
    blocks: list[dict[str, Any]] = []
    for odd_run, even_run in pairs:
        odd_rows = rows[index : index + odd_run]
        even_rows = rows[index + odd_run : index + odd_run + even_run]
        blocks.append(
            {
                "a": odd_run,
                "r": even_run,
                "E_O": sum(row["e"] for row in odd_rows),
                "E_E": sum(row["e"] for row in even_rows),
            }
        )
        index += odd_run + even_run
    return blocks


def _compact_int(value: int) -> int | dict[str, int]:
    if value.bit_length() <= COMPACT_BITS:
        return value
    return {"bits": value.bit_length(), "sign": 1 if value >= 0 else -1}


def _compact_row(row: dict[str, Any]) -> dict[str, Any]:
    out = dict(row)
    for key in ("chunk", "e", "x", "rho"):
        if key in out and isinstance(out[key], int):
            out[key] = _compact_int(out[key])
    return out


def transport_record(n: int, word: str) -> dict[str, Any]:
    """Ordered transport of every local remainder, split at the seam."""

    if not follows_itinerary(n, word):
        raise ValueError(f"{n} does not follow {word}")
    rows = [letter_transport(n, word, index) for index in range(len(word))]
    halves = seam_halves(rows)
    delta = global_defect(n, word)
    surplus = formal_surplus(n, word)
    end = image_after(n, word)
    amp = amplify_from_first(n, word)
    first = first_defect(n, word)
    first_e = rows[first]["e"] if first < len(word) else 0
    transported_sum = halves["sum"]
    cross = delta - transported_sum
    max_e = max((row["e"] for row in rows), default=0)
    contracts = end < n
    expanding = end >= n
    formally_expanding = (1 << len(word)) < 3 ** odd_count(word)
    half_beats = surplus > 0 and (halves["E_O"] > surplus or halves["E_E"] > surplus)
    single_beats = surplus > 0 and max_e > surplus
    new_onesided = (half_beats or single_beats) and expanding
    suffix_weights = all(
        row["W"] == formal_weight(word, row["i"]) for row in rows
    )
    shared = has_shared_later_odd(word)
    return {
        "n": n,
        "word": word,
        "end": end,
        "o": odd_count(word),
        "L": len(word),
        "rows": rows,
        "halves": halves,
        "blocks": block_halves(word, rows),
        "delta": delta,
        "G": surplus,
        "X": cross,
        "identity": transported_sum + cross == delta,
        "X_nonneg": cross >= 0,
        "shared_later_odd": shared,
        "X_is_cubic_cross": (cross == 0 and not shared)
        or (cross >= 0 and shared),
        "amplify": amp,
        "first_defect": first,
        "first_e": first_e,
        "amp_eq_first_e": amp == first_e,
        "max_e": max_e,
        "contracts": contracts,
        "expanding": expanding,
        "formally_expanding": formally_expanding,
        "weights_are_suffix_exponents": suffix_weights,
        "half_beats_G": half_beats,
        "single_beats_G": single_beats,
        "new_onesided": new_onesided,
        "expanding_halves_below_G": expanding
        and surplus > 0
        and halves["E_O"] < surplus
        and halves["E_E"] < surplus
        and max_e < surplus
        and amp <= max_e,
    }


def compact_record(record: dict[str, Any]) -> dict[str, Any]:
    """JSON view: keep small integers exact, compact huge lifts."""

    out = dict(record)
    out["rows"] = [_compact_row(row) for row in record["rows"]]
    out["halves"] = {key: _compact_int(value) for key, value in record["halves"].items()}
    out["blocks"] = [
        {
            "a": block["a"],
            "r": block["r"],
            "E_O": _compact_int(block["E_O"]),
            "E_E": _compact_int(block["E_E"]),
        }
        for block in record["blocks"]
    ]
    for key in ("delta", "G", "X", "amplify", "first_e", "max_e", "end"):
        if isinstance(out.get(key), int):
            out[key] = _compact_int(out[key])
    return out


def classify(records: list[dict[str, Any]]) -> dict[str, Any]:
    identities = all(row["identity"] for row in records)
    x_cubic = all(row["X_is_cubic_cross"] for row in records)
    weights = all(row["weights_are_suffix_exponents"] for row in records)
    amp_first = all(row["amp_eq_first_e"] for row in records)
    expanding = [row for row in records if row["expanding"] and row["G"] > 0]
    expanding_ok = all(row["expanding_halves_below_G"] for row in expanding)
    new_onesided = any(row["new_onesided"] for row in records)
    contracting_may_beat = all(
        (not row["half_beats_G"] and not row["single_beats_G"]) or row["contracts"]
        for row in records
    )
    if (
        identities
        and x_cubic
        and weights
        and amp_first
        and expanding_ok
        and contracting_may_beat
        and not new_onesided
    ):
        classification = CLASS_CLOSED
        decision = "CLOSE"
        reason = (
            "attributed chunks plus cubic cross terms are Delta; "
            "no seam-half or single position beats G except on "
            "contracting itineraries where T_w < n; first-order weights "
            "are suffix 3^{o'}; first-defect Amplify is e_j"
        )
    elif new_onesided:
        classification = CLASS_GREEN
        decision = "PROMOTE"
        reason = (
            "a seam-half or single-position transport exceeds G "
            "while the orbit does not contract, and the reason is "
            "not T_w < n"
        )
    else:
        classification = CLASS_PARK
        decision = "PARK"
        reason = "the ordered-transport census is mixed and does not decide"
    return {
        "classification": classification,
        "decision": decision,
        "reason": reason,
        "identity": identities,
        "X_is_cubic_cross": x_cubic,
        "weights_are_suffix_exponents": weights,
        "amp_eq_first_e": amp_first,
        "expanding_halves_below_G": expanding_ok,
        "new_onesided": new_onesided,
        "leftover_killer": False,
        "reopens_finance": False,
        "reopens_amplify": False,
        "halt_theorem": False,
        "raise_n0": False,
        "paper_a_edit": False,
        "archived": list(ARCHIVED),
    }


def probe_payload() -> dict[str, Any]:
    records = [transport_record(n, word) for n, word in CASES]
    l11_start = first_realized(WORD_L11)
    payload = {
        "bound": "error_transport",
        "cases": [compact_record(record) for record in records],
        "l11_first_realized": l11_start,
        "note": (
            "ordered transport unrolls accumulatedDefect; "
            "seam halves and single positions do not beat G on "
            "expanding itineraries; X is the accumulateOdd cubic cross"
        ),
    }
    payload["decision"] = classify(records)
    return payload


def write_artifacts(payload: dict[str, Any] | None = None) -> dict[str, Any]:
    data = payload if payload is not None else probe_payload()
    TRANSPORT_DIR.mkdir(parents=True, exist_ok=True)
    path = TRANSPORT_DIR / "summary.json"
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
                "l11_first_realized": payload["l11_first_realized"],
                "decision": decision,
                "cases": [
                    {
                        "n": row["n"],
                        "word": row["word"],
                        "end": row["end"],
                        "contracts": row["contracts"],
                        "identity": row["identity"],
                        "X_is_cubic_cross": row["X_is_cubic_cross"],
                        "expanding_halves_below_G": row["expanding_halves_below_G"],
                        "new_onesided": row["new_onesided"],
                        "half_beats_G": row["half_beats_G"],
                        "shared_later_odd": row["shared_later_odd"],
                    }
                    for row in payload["cases"]
                ],
            },
            indent=2,
        )
    )


if __name__ == "__main__":
    main()
