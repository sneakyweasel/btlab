"""Exact modular shadows of floor cells on E_run leftovers.

Not a halt theorem, not a leftover-word census, not a residue
automaton, not p-adic lifting, not Fourier, and not a new finance
bound. Phase 0 asks whether the modular shadow of the exact
square/cube cells refuses to close on a surviving (L,o) without
enumerating words.

R_nec is the algebraic necessary relation at CycleMin scale, where
defect windows 2Y+1 already exceed every listed modulus. R_wit is
witness-supported by exact floor_power. An empty diagonal is a
theorem only from R_nec. A nonempty R_wit diagonal kills the
modulus.

Dossier: docs/problems/juggler_cycle_mod_closure.md.
"""

from __future__ import annotations

import json
from math import gcd
from typing import Any

from research.juggler_sequence.cycle_budget_opt import run_type_counts
from research.juggler_sequence.cycle_closure import follows_block, oe_cell_holds
from research.juggler_sequence.cycle_finance import (
    DATA_DIR,
    PUBLISHED_FLOOR,
    o_min_and_theta,
    sha256_int_list,
)
from research.juggler_sequence.power_itineraries import floor_power

SPOTLIGHT = (25781, 55293)
BLOCK_WORDS = ("OE", "OOE", "OOOE", "OEE", "OOEE")
RUN_BLOCKS = ("OOE", "OE")
MOD_POW2 = (8, 16, 32, 64)
MOD_POW3 = (3, 9, 27, 81)
MOD_PROD = (72, 144, 216, 288, 432, 648, 864, 1296)
MODULI = MOD_POW2 + MOD_POW3 + MOD_PROD
START = PUBLISHED_FLOOR + 1
FILL_MOD_MAX = 81
FILL_PER_CLASS = 20
SCAN_HITS = 4000
SELF_LOOP_CAP = 8
MOD_DIR = DATA_DIR / "mod_closure"


def source_parity_ok(residue: int, modulus: int, odd: bool) -> bool:
    """Whether the class residue mod m has a lift of the given parity."""

    if modulus % 2 == 1:
        return True
    return (residue % 2 == 1) is odd


def first_letter_odd(word: str) -> bool:
    if not word or word[0] not in "OE":
        raise ValueError("word must start with O or E")
    return word[0] == "O"


def r_nec_source_count(modulus: int, odd: bool) -> int:
    if modulus % 2 == 1:
        return modulus
    return modulus // 2


def r_nec_pair_count(modulus: int, odd: bool) -> int:
    """Cycle-scale necessary pairs: first-letter parity times all targets.

    Once 2Y+1 > m the defects δ,η are free residues, so
    x^3 ≡ y^2 + δ and x ≡ y^2 + η impose no further restriction.
    """

    return r_nec_source_count(modulus, odd) * modulus


def defect_width_collapses(modulus: int, y_min: int = START) -> bool:
    return 2 * y_min + 1 <= modulus


def first_congruent(
    start: int,
    residue: int,
    modulus: int,
    want_odd: bool | None,
) -> int | None:
    residue %= modulus
    current = start + (residue - start) % modulus
    if want_odd is None:
        return current
    if (current % 2 == 1) == want_odd:
        return current
    if modulus % 2 == 0:
        return None
    return current + modulus


def stride_for(modulus: int, want_odd: bool | None) -> int:
    if want_odd is None or modulus % 2 == 0:
        return modulus
    return 2 * modulus


def even_cell_realizable(src: int, dst: int, modulus: int, y: int) -> bool:
    """Even cell at scale: Y ≡ dst, X = Y^2 + η ≡ src, 0 ≤ η < 2Y+1.

    For Y ≥ m the interval length exceeds m, so every even-compatible
    source is realized. This is the existence half of even_preimage_iff.
    """

    if y < 1 or y % modulus != dst % modulus:
        return False
    if not source_parity_ok(src, modulus, odd=False):
        return False
    eta = (src - (y * y) % modulus) % modulus
    return 0 <= eta < 2 * y + 1


def r_wit_step(
    modulus: int,
    *,
    odd: bool,
    start: int = START,
    per_class: int = FILL_PER_CLASS,
) -> set[tuple[int, int]]:
    pairs: set[tuple[int, int]] = set()
    want_odd = odd
    for residue in range(modulus):
        current = first_congruent(start, residue, modulus, want_odd)
        if current is None:
            continue
        stride = stride_for(modulus, want_odd)
        hits = 0
        while hits < per_class:
            image = floor_power(current)
            pairs.add((current % modulus, image % modulus))
            hits += 1
            if odd:
                current += stride
            else:
                nxt = (image + 1) * (image + 1)
                current = first_congruent(nxt, residue, modulus, want_odd)
                if current is None:
                    break
    return pairs


def r_wit_block(
    word: str,
    modulus: int,
    *,
    start: int = START,
    hit_budget: int = SCAN_HITS,
    per_class: int | None = None,
) -> set[tuple[int, int]]:
    """Witness pairs for an exact block. Skip starts that miss the word."""

    pairs: set[tuple[int, int]] = set()
    odd = first_letter_odd(word)
    if per_class is not None:
        for residue in range(modulus):
            current = first_congruent(start, residue, modulus, odd)
            if current is None:
                continue
            stride = stride_for(modulus, odd)
            hits = 0
            attempts = 0
            while hits < per_class and attempts < per_class * 16:
                image = follows_block(current, word)
                attempts += 1
                if image is not None:
                    pairs.add((current % modulus, image % modulus))
                    hits += 1
                current += stride
        return pairs

    current = start if (start % 2 == 1) == odd else start + 1
    hits = 0
    attempts = 0
    limit = hit_budget * 8
    while hits < hit_budget and attempts < limit:
        image = follows_block(current, word)
        attempts += 1
        if image is not None:
            pairs.add((current % modulus, image % modulus))
            hits += 1
        current += 2
    return pairs


def self_loop_residues(
    word: str,
    modulus: int,
    *,
    start: int = START,
    hit_budget: int = SCAN_HITS,
    cap: int = SELF_LOOP_CAP,
) -> set[int]:
    found: set[int] = set()
    odd = first_letter_odd(word)
    current = start if (start % 2 == 1) == odd else start + 1
    hits = 0
    attempts = 0
    limit = hit_budget * 8
    while hits < hit_budget and attempts < limit and len(found) < cap:
        image = follows_block(current, word)
        attempts += 1
        if image is not None:
            hits += 1
            if image % modulus == current % modulus:
                found.add(current % modulus)
        current += 2
    return found


def increment_set(pairs: set[tuple[int, int]], modulus: int) -> set[int]:
    return {(dst - src) % modulus for src, dst in pairs}


def increment_gcd(increments: set[int], modulus: int) -> int:
    acc = modulus
    for value in increments:
        acc = gcd(acc, value)
    return acc


def counts_return_possible(
    inc_ooe: set[int],
    inc_oe: set[int],
    n_ooe: int,
    n_oe: int,
    modulus: int,
) -> bool:
    if not inc_ooe or not inc_oe:
        return False
    for delta_ooe in inc_ooe:
        for delta_oe in inc_oe:
            if (n_ooe * delta_ooe + n_oe * delta_oe) % modulus == 0:
                return True
    return False


def odd_return_exists(pairs: set[tuple[int, int]], modulus: int) -> bool:
    """True if some odd-compatible residue returns to itself along the edges."""

    adj: list[list[int]] = [[] for _ in range(modulus)]
    for src, dst in pairs:
        adj[src].append(dst)
    for start in range(modulus):
        if not source_parity_ok(start, modulus, True):
            continue
        if start in adj[start]:
            return True
        seen: set[int] = set()
        stack = list(adj[start])
        while stack:
            node = stack.pop()
            if node == start:
                return True
            if node in seen:
                continue
            seen.add(node)
            stack.extend(adj[node])
    return False


def first_last_mod(n: int, modulus: int) -> dict[str, Any]:
    first = floor_power(n) % modulus
    last_len = 2 * n + 1
    return {
        "n": n,
        "first_odd_res": first,
        "last_even_covers_all": last_len >= modulus,
        "same_slot": False,
        "reduces_to_overshoot": True,
    }


def pair_meta(length: int) -> dict[str, Any]:
    odd_count, theta = o_min_and_theta(length)
    even_count = length - odd_count
    ooe_count, oe_count = run_type_counts(odd_count, even_count)
    return {
        "L": length,
        "o": odd_count,
        "e": even_count,
        "theta": theta,
        "ooe_count": ooe_count,
        "oe_count": oe_count,
    }


def local_step_report(
    modulus: int,
    *,
    start: int = START,
    fill: bool = False,
) -> dict[str, Any]:
    nec_odd = r_nec_pair_count(modulus, True)
    nec_even = r_nec_pair_count(modulus, False)
    even_full = not defect_width_collapses(modulus)
    wit_odd: set[tuple[int, int]] = set()
    wit_even: set[tuple[int, int]] = set()
    if fill:
        wit_odd = r_wit_step(modulus, odd=True, start=start)
        wit_even = r_wit_step(modulus, odd=False, start=start)
    return {
        "nec_odd_pairs": nec_odd,
        "nec_even_pairs": nec_even,
        "nec_is_first_letter_parity": True,
        "even_cell_full_at_scale": even_full,
        "wit_odd_pairs": len(wit_odd),
        "wit_even_pairs": len(wit_even),
        "wit_odd_fills_nec": fill and len(wit_odd) == nec_odd,
        "wit_even_fills_nec": fill and len(wit_even) == nec_even,
    }


def block_report(
    word: str,
    modulus: int,
    *,
    start: int = START,
    fill: bool = False,
) -> dict[str, Any]:
    nec = r_nec_pair_count(modulus, first_letter_odd(word))
    per_class = FILL_PER_CLASS if fill else None
    hits = SCAN_HITS if not fill else FILL_PER_CLASS * modulus
    pairs = r_wit_block(
        word,
        modulus,
        start=start,
        hit_budget=hits,
        per_class=per_class,
    )
    loops = {src for src, dst in pairs if src == dst}
    return {
        "word": word,
        "nec_pairs": nec,
        "nec_is_first_letter_parity": True,
        "wit_pairs": len(pairs),
        "self_loops": sorted(loops)[:SELF_LOOP_CAP],
        "self_loop_count": len(loops),
        "diagonal_wit": bool(loops),
        "increment_gcd": increment_gcd(increment_set(pairs, modulus), modulus),
    }


def _block_pairs(
    modulus: int,
    *,
    start: int = START,
    fill: bool = False,
) -> dict[str, set[tuple[int, int]]]:
    per_class = FILL_PER_CLASS if fill else None
    hits = SCAN_HITS if not fill else FILL_PER_CLASS * modulus
    return {
        word: r_wit_block(
            word,
            modulus,
            start=start,
            hit_budget=hits,
            per_class=per_class,
        )
        for word in BLOCK_WORDS
    }


def attach_counts(
    base: dict[str, Any],
    ooe_count: int,
    oe_count: int,
    inc_ooe: set[int],
    inc_oe: set[int],
) -> dict[str, Any]:
    row = dict(base)
    row["counts_return_possible"] = counts_return_possible(
        inc_ooe, inc_oe, ooe_count, oe_count, base["m"]
    )
    return row


def modulus_witness(
    modulus: int,
    *,
    start: int = START,
) -> tuple[dict[str, Any], set[int], set[int]]:
    fill = modulus <= FILL_MOD_MAX
    local = local_step_report(modulus, start=start, fill=fill)
    pair_map = _block_pairs(modulus, start=start, fill=fill)
    blocks = {}
    for word in BLOCK_WORDS:
        pairs = pair_map[word]
        loops = {src for src, dst in pairs if src == dst}
        blocks[word] = {
            "word": word,
            "nec_pairs": r_nec_pair_count(modulus, first_letter_odd(word)),
            "nec_is_first_letter_parity": True,
            "wit_pairs": len(pairs),
            "self_loops": sorted(loops)[:SELF_LOOP_CAP],
            "self_loop_count": len(loops),
            "diagonal_wit": bool(loops),
            "increment_gcd": increment_gcd(increment_set(pairs, modulus), modulus),
        }
    ooe_pairs = pair_map["OOE"]
    oe_pairs = pair_map["OE"]
    union_pairs = ooe_pairs | oe_pairs
    inc_ooe = increment_set(ooe_pairs, modulus)
    inc_oe = increment_set(oe_pairs, modulus)
    loops_ooe = {src for src, dst in ooe_pairs if src == dst}
    loops_oe = {src for src, dst in oe_pairs if src == dst}
    shared = loops_ooe & loops_oe
    odd_shared = {r for r in shared if source_parity_ok(r, modulus, True)}
    nec_diagonal = r_nec_source_count(modulus, True)
    wit_diagonal = odd_return_exists(union_pairs, modulus)
    reduces = (
        local["nec_is_first_letter_parity"]
        and local["even_cell_full_at_scale"]
        and nec_diagonal > 0
        and wit_diagonal
    )
    base = {
        "m": modulus,
        "defect_width_collapses": defect_width_collapses(modulus),
        "local": local,
        "blocks": blocks,
        "ooe_wit_pairs": len(ooe_pairs),
        "oe_wit_pairs": len(oe_pairs),
        "union_wit_pairs": len(union_pairs),
        "ooe_self_loops": len(loops_ooe),
        "oe_self_loops": len(loops_oe),
        "shared_self_loops": len(shared),
        "odd_shared_self_loops": len(odd_shared),
        "nec_diagonal_count": nec_diagonal,
        "nec_diagonal_nonempty": nec_diagonal > 0,
        "wit_union_odd_return": wit_diagonal,
        "increment_gcd_ooe": increment_gcd(inc_ooe, modulus),
        "increment_gcd_oe": increment_gcd(inc_oe, modulus),
        "reduces_to_parity": reduces,
        "level": "A",
        "diagonal_nonempty": wit_diagonal,
    }
    return base, inc_ooe, inc_oe


def modulus_report(
    modulus: int,
    *,
    start: int = START,
    ooe_count: int = 0,
    oe_count: int = 0,
) -> dict[str, Any]:
    base, inc_ooe, inc_oe = modulus_witness(modulus, start=start)
    return attach_counts(base, ooe_count, oe_count, inc_ooe, inc_oe)


def _summarize_moduli(rows: list[dict[str, Any]]) -> dict[str, bool]:
    return {
        "all_diagonal_nonempty": all(row["diagonal_nonempty"] for row in rows),
        "all_nec_diagonal_nonempty": all(
            row["nec_diagonal_nonempty"] for row in rows
        ),
        "all_reduces_to_parity": all(row["reduces_to_parity"] for row in rows),
        "all_counts_return": all(row["counts_return_possible"] for row in rows),
        "no_defect_width_collapse": not any(
            row["defect_width_collapses"] for row in rows
        ),
    }


def spotlight_from_witnesses(
    length: int,
    witnesses: list[tuple[dict[str, Any], set[int], set[int]]],
    *,
    start: int = START,
) -> dict[str, Any]:
    meta = pair_meta(length)
    first_last = first_last_mod(start if start % 2 == 1 else start + 1, 8)
    rows = [
        attach_counts(base, meta["ooe_count"], meta["oe_count"], inc_ooe, inc_oe)
        for base, inc_ooe, inc_oe in witnesses
    ]
    flags = _summarize_moduli(rows)
    return {
        **meta,
        "first_last_mod8": first_last,
        "moduli": rows,
        **flags,
        "requires_word_enumeration": not flags["all_diagonal_nonempty"],
        "level_c": False,
    }


def spotlight_row(length: int, *, start: int = START) -> dict[str, Any]:
    witnesses = [modulus_witness(modulus, start=start) for modulus in MODULI]
    return spotlight_from_witnesses(length, witnesses, start=start)


def mod_closure_scan(*, start: int = START) -> dict[str, Any]:
    witnesses = [modulus_witness(modulus, start=start) for modulus in MODULI]
    spots = {
        str(length): spotlight_from_witnesses(length, witnesses, start=start)
        for length in SPOTLIGHT
    }
    oe_ok = True
    x = 3
    hits = 0
    while hits < 40:
        image = follows_block(x, "OE")
        if image is not None:
            oe_ok = oe_ok and oe_cell_holds(x, image)
            hits += 1
        x += 2
    emptied = [
        length
        for length, row in spots.items()
        if not row["all_diagonal_nonempty"]
    ]
    return {
        "bound": "cycle_mod_closure",
        "floor": PUBLISHED_FLOOR,
        "start": start,
        "moduli": list(MODULI),
        "spotlights": spots,
        "oe_is_exponent_cell": oe_ok,
        "emptied_lengths": emptied,
        "emptied_count": len(emptied),
        "all_spotlights_diagonal": all(
            row["all_diagonal_nonempty"] for row in spots.values()
        ),
        "all_spotlights_nec_diagonal": all(
            row["all_nec_diagonal_nonempty"] for row in spots.values()
        ),
        "all_reduces_to_parity": all(
            row["all_reduces_to_parity"] for row in spots.values()
        ),
        "all_counts_return": all(
            row["all_counts_return"] for row in spots.values()
        ),
        "no_defect_width_collapse": all(
            row["no_defect_width_collapse"] for row in spots.values()
        ),
        "scanned_other_97": False,
        "level_c": False,
        "sha256_spotlights": sha256_int_list(list(SPOTLIGHT)),
        "halt_theorem": False,
        "no_cycle_all_lengths": False,
    }


def write_mod_closure_artifacts(
    payload: dict[str, Any] | None = None,
    *,
    start: int = START,
) -> dict[str, Any]:
    data = payload if payload is not None else mod_closure_scan(start=start)
    MOD_DIR.mkdir(parents=True, exist_ok=True)
    path = MOD_DIR / "summary.json"
    path.write_text(json.dumps(data, indent=2, allow_nan=False) + "\n", encoding="utf-8")
    return data


if __name__ == "__main__":
    report = write_mod_closure_artifacts()
    spots = report["spotlights"]
    print(
        json.dumps(
            {
                "emptied": report["emptied_count"],
                "all_diagonal": report["all_spotlights_diagonal"],
                "reduces_to_parity": report["all_reduces_to_parity"],
                "counts_return": report["all_counts_return"],
                "defect_collapse": not report["no_defect_width_collapse"],
                "25781": {
                    "o": spots["25781"]["o"],
                    "ooe": spots["25781"]["ooe_count"],
                    "oe": spots["25781"]["oe_count"],
                    "diagonal": spots["25781"]["all_diagonal_nonempty"],
                    "parity": spots["25781"]["all_reduces_to_parity"],
                },
                "55293": {
                    "o": spots["55293"]["o"],
                    "ooe": spots["55293"]["ooe_count"],
                    "oe": spots["55293"]["oe_count"],
                    "diagonal": spots["55293"]["all_diagonal_nonempty"],
                    "parity": spots["55293"]["all_reduces_to_parity"],
                },
            },
            indent=2,
        )
    )
