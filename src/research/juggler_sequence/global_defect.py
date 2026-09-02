"""Exact accumulated Juggler defect. Not a termination theorem.

The recurrence is the binomial / cubic lift of local floor remainders.
It is not the naive path sum and not a definition of the envelope slack.
"""

from __future__ import annotations

from typing import Any

from research.juggler_sequence.lean_paths import has_named, juggler_text
from research.juggler_sequence.power_itineraries import floor_power

LEAN_THEOREMS = (
    "powGap",
    "accumulatedDefect",
    "globalDefect",
    "global_defect_nonneg",
    "global_defect_identity",
    "power_bound_of_global_defect",
    "global_defect_eq_zero_iff",
    "global_defect_eq_zero_iff_locals",
    "global_defect_append",
    "global_defect_pos_of_mixed",
    "residualStep_global_defect",
    "minimal_nonterm_global_defect_le_surplus",
)


def local_defect(x: int) -> int:
    y = floor_power(x)
    if x % 2 == 0:
        return x - y * y
    return x * x * x - y * y


def pow_gap(a: int, rho: int, e: int) -> int:
    return (a + rho) ** e - a**e


def accumulated_defect(current: int, d: int, k: int, word: str) -> int:
    if not word:
        return d
    rho = local_defect(current)
    y = floor_power(current)
    letter = word[0]
    if letter == "E":
        d_next = d + pow_gap(y * y, rho, 2**k)
    elif letter == "O":
        d_next = pow_gap(y * y, rho, 2**k) + pow_gap(current ** (2**k), d, 3)
    else:
        raise ValueError(f"unknown letter {letter!r}")
    return accumulated_defect(y, d_next, k + 1, word[1:])


def global_defect(n: int, word: str) -> int:
    return accumulated_defect(n, 0, 0, word)


def image_after(n: int, word: str) -> int:
    current = n
    for letter in word:
        if letter == "E" and current % 2 != 0:
            raise ValueError(f"{n} does not follow {word}")
        if letter == "O" and current % 2 != 1:
            raise ValueError(f"{n} does not follow {word}")
        current = floor_power(current)
    return current


def follows_itinerary(n: int, word: str) -> bool:
    current = n
    for letter in word:
        if letter == "E" and current % 2 != 0:
            return False
        if letter == "O" and current % 2 != 1:
            return False
        current = floor_power(current)
    return True


def odd_count(word: str) -> int:
    return word.count("O")


def envelope_slack(n: int, word: str) -> int:
    end = image_after(n, word)
    return n ** (3 ** odd_count(word)) - end ** (2 ** len(word))


def itinerary_word(n: int, k: int) -> str:
    letters: list[str] = []
    current = n
    for _ in range(k):
        letters.append("E" if current % 2 == 0 else "O")
        current = floor_power(current)
    return "".join(letters)


def is_monochrome(word: str) -> bool:
    return (not word) or set(word) <= {"E"} or set(word) <= {"O"}


def compose_formula(n: int, u: str, v: str) -> int:
    mid = image_after(n, u)
    end = image_after(mid, v)
    du = global_defect(n, u)
    dv = global_defect(mid, v)
    return pow_gap(mid ** (2 ** len(u)), du, 3 ** odd_count(v)) + pow_gap(
        end ** (2 ** len(v)), dv, 2 ** len(u)
    )


def first_positive_index(n: int, word: str) -> int | None:
    current = n
    for i, letter in enumerate(word):
        if letter == "E" and current % 2 != 0:
            return None
        if letter == "O" and current % 2 != 1:
            return None
        rho = local_defect(current)
        if rho > 0:
            return i
        current = floor_power(current)
    return None


def census(*, n_max: int = 80, k_max: int = 5) -> dict[str, Any]:
    rows: list[dict[str, Any]] = []
    mismatches = 0
    mixed_zero = 0
    first_defect_fail = 0
    compose_fail = 0
    for n in range(1, n_max + 1):
        for k in range(0, k_max + 1):
            word = itinerary_word(n, k)
            delta = global_defect(n, word)
            slack = envelope_slack(n, word)
            if delta != slack:
                mismatches += 1
            idx = first_positive_index(n, word)
            if idx is not None:
                current = n
                for _ in range(idx):
                    current = floor_power(current)
                rho = local_defect(current)
                if delta < rho ** (2**idx):
                    first_defect_fail += 1
            if word and not is_monochrome(word) and delta == 0:
                mixed_zero += 1
            for split in range(k + 1):
                u, v = word[:split], word[split:]
                if compose_formula(n, u, v) != delta:
                    compose_fail += 1
            if k <= 3 or n <= 20:
                rows.append(
                    {
                        "n": n,
                        "word": word,
                        "end": image_after(n, word),
                        "o": odd_count(word),
                        "k": k,
                        "delta": delta,
                        "slack": slack,
                    }
                )
    return {
        "n_max": n_max,
        "k_max": k_max,
        "mismatches": mismatches,
        "mixed_zero": mixed_zero,
        "first_defect_fail": first_defect_fail,
        "compose_fail": compose_fail,
        "sample_rows": rows[:40],
    }


def ce_prefix_scan(*, n_max: int = 400) -> dict[str, Any]:
    """On T_w(n) ≥ n, Δ ≤ formal surplus is equivalent to the image bound."""

    words = ("OOE", "OOEO", "OOOE")
    out: dict[str, Any] = {}
    for word in words:
        o = odd_count(word)
        k = len(word)
        surplus_beats = 0
        contracts = 0
        expands = 0
        checked = 0
        for n in range(12, n_max + 1):
            if n % 2 == 0:
                continue
            if not follows_itinerary(n, word):
                continue
            checked += 1
            end = image_after(n, word)
            delta = global_defect(n, word)
            surplus = n ** (3**o) - n ** (2**k)
            if end < n:
                contracts += 1
                if delta <= surplus:
                    # T < n can still have Δ ≤ surplus; only T^k < n^k is required
                    # for Δ > surplus. Count strict surplus violations.
                    pass
                if delta > surplus:
                    surplus_beats += 1
            else:
                expands += 1
                if delta > surplus:
                    surplus_beats += 1
        out[word] = {
            "checked": checked,
            "contracts": contracts,
            "expands_or_returns": expands,
            "delta_gt_surplus": surplus_beats,
            "formal_gap_exponents": f"3^{o} vs 2^{k}",
        }
    return out


def lean_api_present() -> dict[str, bool]:
    text = juggler_text()
    return {
        "sorry_free": "sorry" not in text and "admit" not in text,
        **{name: has_named(text, name) for name in LEAN_THEOREMS},
    }
