"""Consecutive expanding persistent residual runs. Not a termination theorem.

Asks whether expanding persistent residual blocks can occur with
arbitrarily high density, or whether a finite run bound exists that
is not the concatenated endpoint inequality.
"""

from __future__ import annotations

from collections import Counter
from typing import Any

from research.juggler_sequence.lean_registry import has_named, juggler_text
from research.juggler_sequence.progress_coverage import is_odd_odd
from research.juggler_sequence.residual_chain import residual_excursion
from research.juggler_sequence.two_block_residual import (
    classify_step,
    exponent_expanding,
    exponent_sign,
    odd_odd_starts,
)

N_MAX = 8000
CHAIN_CAP = 24
BIT_CAP = 4096

LEAN_THEOREMS = (
    "expansionSurplus",
    "expansionSurplus_oddEvenBlock",
    "expansionSurplus_pos_iff",
    "block_growth_identity",
    "expanding_oddEvenBlock_even_lt_odd",
    "logSlack_concat",
    "logSlack_concat_three",
    "PersistentExpansionChain",
    "expansion_run_365_len_three",
    "expansion_run_365_chain",
)

LONGEST_CERTIFIED_RUN = (365, 763, 1749, 4447)
LENGTH_SEVEN_START = 11681

KNOWN_TRIPLE = (365, 763, 1749, 4447)


def expansion_surplus(a: int, b: int) -> int:
    """Integer exponent surplus ``3^a - 2^{a+b}``."""
    return exponent_sign(a, b)


def even_lt_odd_needed(a: int, b: int) -> bool:
    """Integer shadow of ``#E < #O`` on an expanding residual."""
    return exponent_expanding(a, b) and b < a


def walk_pe_run(start: int, *, cap: int = CHAIN_CAP, bit_cap: int = BIT_CAP) -> dict[str, Any]:
    """Walk only while the residual step is persistent and expanding."""
    xs = [start]
    words: list[str] = []
    signs: list[int] = []
    pairs: list[tuple[int, int]] = []
    x = start
    stopped = "cap"
    for _ in range(cap):
        if x.bit_length() > bit_cap:
            stopped = "bit_cap"
            break
        raw = residual_excursion(x)
        if raw is None:
            stopped = "no_residual"
            break
        step = classify_step(x, raw)
        if not (step["persistent"] and step["expanding"]):
            stopped = "break"
            words.append(step["word"])
            signs.append(step["sign"])
            pairs.append((step["a"], step["b"]))
            xs.append(step["y"])
            break
        words.append(step["word"])
        signs.append(step["sign"])
        pairs.append((step["a"], step["b"]))
        xs.append(step["y"])
        x = step["y"]
    pe_len = 0
    y = start
    for i, (a, b) in enumerate(pairs):
        if i + 1 >= len(xs):
            break
        nxt = xs[i + 1]
        if exponent_expanding(a, b) and nxt > y and nxt >= 2 and is_odd_odd(nxt):
            pe_len += 1
            y = nxt
        else:
            break
    return {
        "start": start,
        "length": pe_len,
        "xs": xs[: pe_len + 1],
        "words": words[:pe_len],
        "pairs": pairs[:pe_len],
        "signs": signs[:pe_len],
        "stopped": stopped,
        "breaker": None
        if pe_len >= len(words)
        else {
            "word": words[pe_len],
            "sign": signs[pe_len],
            "pair": pairs[pe_len],
            "end": xs[pe_len + 1] if pe_len + 1 < len(xs) else None,
        },
    }


def run_census(*, n_max: int = N_MAX, chain_cap: int = CHAIN_CAP) -> dict[str, Any]:
    starts = odd_odd_starts(n_max)
    lengths = Counter()
    longest: list[dict[str, Any]] = []
    word_types = Counter()
    pair_types = Counter()
    max_len = 0
    skipped_bits = 0
    for n in starts:
        run = walk_pe_run(n, cap=chain_cap)
        L = run["length"]
        lengths[L] += 1
        if L > max_len:
            max_len = L
            longest = [run]
        elif L == max_len and L > 0 and len(longest) < 8:
            longest.append(run)
        for word, pair in zip(run["words"], run["pairs"]):
            word_types[word] += 1
            pair_types[pair] += 1
        if run["stopped"] == "bit_cap":
            skipped_bits += 1

    known = walk_pe_run(365, cap=chain_cap)
    return {
        "n_max": n_max,
        "starts": len(starts),
        "max_run": max_len,
        "length_hist": dict(sorted(lengths.items())),
        "runs_ge_3": sum(c for L, c in lengths.items() if L >= 3),
        "runs_ge_4": sum(c for L, c in lengths.items() if L >= 4),
        "runs_ge_5": sum(c for L, c in lengths.items() if L >= 5),
        "word_types": dict(word_types.most_common(12)),
        "pair_types": {f"O{a}E{b}": c for (a, b), c in pair_types.most_common(12)},
        "skipped_bits": skipped_bits,
        "known_365": {
            "length": known["length"],
            "xs": known["xs"],
            "words": known["words"],
            "breaker": known["breaker"],
        },
        "longest": [
            {
                "start": r["start"],
                "length": r["length"],
                "xs": r["xs"],
                "words": r["words"],
                "breaker": r["breaker"],
            }
            for r in longest
        ],
    }


def density_along_persistent(*, n_max: int = 2000, chain_cap: int = 16) -> dict[str, Any]:
    """Expanding fraction among persistent residual steps, not PE-only walks."""
    starts = odd_odd_starts(n_max)
    pers = 0
    exp_pers = 0
    max_density = 0.0
    best = None
    for n in starts:
        x = n
        p = 0
        e = 0
        for _ in range(chain_cap):
            raw = residual_excursion(x)
            if raw is None or x.bit_length() > BIT_CAP:
                break
            step = classify_step(x, raw)
            if not step["persistent"]:
                break
            p += 1
            if step["expanding"]:
                e += 1
            x = step["y"]
        pers += p
        exp_pers += e
        if p >= 3:
            d = e / p
            if d > max_density:
                max_density = d
                best = {"start": n, "persistent": p, "expanding": e, "density": d}
    return {
        "persistent_steps": pers,
        "expanding_persistent": exp_pers,
        "density": (exp_pers / pers) if pers else None,
        "max_prefix_density": best,
    }


def lean_api_present() -> dict[str, bool]:
    text = juggler_text()
    return {
        "sorry_free": "sorry" not in text and "admit" not in text,
        **{name: has_named(text, name) for name in LEAN_THEOREMS},
    }
