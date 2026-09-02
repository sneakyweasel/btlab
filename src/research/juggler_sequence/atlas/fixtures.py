"""Lean/Python certification fixtures. No Lean FFI."""

from __future__ import annotations

from research.juggler_sequence.atlas.packed import pack_word
from research.juggler_sequence.power_itineraries import floor_power

# Lean Dynamics / native_decide seeds.
FLOOR_POWER_SEEDS = (
    (1, 1),
    (2, 1),
    (4, 2),
    (6, 2),
    (7, 18),
    (8, 2),
)

# ooe_mem_expandingLanguage: n=5, OOE, image 6.
OOE_AT_FIVE = {
    "n": 5,
    "word": "OOE",
    "image": 6,
    "expanding": True,
}

# two_block_ooe_365 and expansion_run_365_len_three.
PE_CHAIN_365 = {
    "starts": (365, 763, 1749),
    "words": ("OOE", "OOE", "OOE"),
    "images": (763, 1749, 4447),
}

# four_block_pe_1999
PE_CHAIN_1999 = {
    "starts": (1999, 5169, 50093, 193753),
    "words": ("OOE", "OOOOEE", "OOE", "OOE"),
    "images": (5169, 50093, 193753, 887471),
}

# Realizable mixed word; not a forbidden factor.
EEOE_AT_2500 = {
    "n": 2500,
    "word": "EEOE",
}


def itinerary_symbols(n: int, steps: int) -> str:
    current = n
    letters: list[str] = []
    for _ in range(steps):
        letters.append("O" if current % 2 else "E")
        current = floor_power(current)
    return "".join(letters)


def image_after_steps(n: int, steps: int) -> int:
    current = n
    for _ in range(steps):
        current = floor_power(current)
    return current


def packed_fixture(word: str) -> tuple[int, int]:
    return pack_word(word)
