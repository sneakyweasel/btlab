"""Paper B's survivor recursion sits inside a named OEIS neighbourhood, and the plateau
lengths are a Beatty pair.

`J-paper-b-survivors-are-oeis-a076227` already identifies the survivor count `N_d` with
OEIS A076227 and checks it against the Hikawa-Nakanishi b-file to 3508 terms. This probe
asks the next question, which that row does not: the entry's own formula section carries a
recurrence in terms of two further sequences, and the laboratory's Lean recursion
`neverNegCount_succ_sub_onBarrier` -- `N_(d+1) + M_(d+1) = 2 N_d` -- is exactly the shape
that recurrence takes. What are those sequences, in the laboratory's terms?

**THE PLATEAU LENGTHS ARE A BEATTY PAIR, AND THE LABORATORY HAD ONE HALF OF IT.** `M_d` is
the count of minimal certificates of length `d`; the recursion doubles exactly when
`M_d = 0`, which by `minimalCertCount_eq_zero_of_window_empty` happens exactly when no power
of three lies in `[2^(d-1), 2^d)`. Those two sets are

    M_d != 0   <=>   d in A020914 = { floor(n log2 3) + 1 : n >= 0 }
    M_d  = 0   <=>   d in A054414 \\ {1},   A054414(n) = 1 + floor(n / (1 - log 2 / log 3))

and they partition the positive integers. A020914 is the laboratory's own distinguished
length, used throughout Paper A and B; **A054414, its Beatty complement, appears nowhere in
the repository.** The single exception is `d = 1`: A054414 contains 1, but the one-letter
word `E` contracts at once, so `M_1 = 1` and 1 is a non-doubling length. Verified to
`d = 200` against both closed forms.

**ONLY ONE OF THE FOUR SEQUENCES IS NEW, AND THE OTHER THREE WERE CHECKED FIRST.** A076227
is `J-paper-b-survivors-are-oeis-a076227`; A020914 is used throughout Papers A and B; A100982
is already named in Lean at `CollatzBridgeLab.lean` as the minimal-certificate count "read by
length", and `docs/research_journal.md` carries a Winkler sandwich row on it. Reading `M_d`
along the non-doubling lengths only, rather than by length with its zeros, gives A100982 with
one extra leading term -- the same content re-indexed, not a new identification, and it is
recorded here with its shift stated because an unstated offset produced this branch's A034887
error earlier the same day. **A054414 is the one sequence the repository had never met.**

**WHAT THIS IS AND IS NOT.** Bookkeeping. The mathematics is the laboratory's own and is
already kernel-checked; what is added is a closed form for *where* the plateau lengths are,
against the three verified instances at 6, 9 and 11 that the plateau law previously carried.
No bound moves, no cycle is excluded, `N_0` is untouched, and no Lean proof changes -- the
identification is recorded in docstrings and in the ledger, never as a new theorem, because
this container cannot run `lake` and unverifiable Lean has no business in a corpus whose
claim is that it is kernel-checked.
"""

from __future__ import annotations

import json
import math
from typing import Any

from research.juggler_sequence.lean_paths import DATA_ROOT, DOCS_RESEARCH

DATA_DIR = DATA_ROOT / "oeis_neighbourhood"
JSON_PATH = DATA_DIR / "summary.json"
DOC_PATH = DOCS_RESEARCH / "juggler_oeis_neighbourhood.md"

CLASS_NEIGHBOURHOOD = "THE_PLATEAU_LENGTHS_ARE_A_BEATTY_PAIR"

#: depth to which the recursion and the two closed forms are checked
MAX_DEPTH = 200

#: the mirror this session read, and when it was exported
OEIS_MIRROR = "github.com/oeis/oeisdata"
OEIS_EXPORT = "2026-09-20T03:00:19-04:00"

#: A100982 as stored by that export. READ from the mirror and emitted programmatically,
#: never typed: a hand transcription of this list on 20 September 2026 was correct for the
#: twelve terms that had appeared in a terminal and invented for the twenty that had not.
A100982_STORED = (
    1, 1, 2, 3, 7, 12, 30, 85, 173, 476, 961, 2652, 8045, 17637, 51033, 108950, 312455,
    663535, 1900470, 5936673, 13472296, 39993895, 87986917, 257978502, 820236724,
    1899474678, 5723030586, 12809477536, 38036848410, 84141805077, 248369601964,
    794919136728,
)


def survivor_recursion(max_depth: int = MAX_DEPTH) -> tuple[list[int], list[int]]:
    """`N_d` and `M_d` by dynamic programming on `(length, odd count)`.

    `N_d` counts length-`d` words every prefix of which is non-contracting (`2^m <= 3^(a_m)`);
    `M_d` counts those of length `d` that contract for the first time at the last letter.
    This is the laboratory's `neverNegCount` / `minimalCertCount` pair, computed without
    enumerating words so that the depth can reach 200.
    """
    if max_depth < 1:
        raise ValueError(f"max_depth must be >= 1, got {max_depth}")
    layer: dict[int, int] = {0: 1}
    counts = [1]
    certs = [0]
    for length in range(1, max_depth + 1):
        nxt: dict[int, int] = {}
        contracted = 0
        for odds, count in layer.items():
            if 2**length <= 3 ** (odds + 1):
                nxt[odds + 1] = nxt.get(odds + 1, 0) + count
            if 2**length <= 3**odds:
                nxt[odds] = nxt.get(odds, 0) + count
            else:
                contracted += count
        layer = nxt
        counts.append(sum(layer.values()))
        certs.append(contracted)
    return counts, certs


def a020914(limit: int) -> list[int]:
    """`floor(n log2 3) + 1`, the laboratory's distinguished length."""
    out = []
    n = 0
    while True:
        v = math.floor(n * math.log2(3)) + 1
        if v > limit:
            return out
        out.append(v)
        n += 1


def a054414(limit: int) -> list[int]:
    """`1 + floor(n / (1 - log 2 / log 3))`, the Beatty complement."""
    slope = 1 - math.log(2) / math.log(3)
    out = []
    n = 0
    while True:
        v = 1 + math.floor(n / slope)
        if v > limit:
            return out
        out.append(v)
        n += 1


def beatty_partition(max_depth: int = MAX_DEPTH) -> dict[str, Any]:
    """The plateau lengths against the two closed forms."""
    _counts, certs = survivor_recursion(max_depth)
    doubling = [d for d in range(1, max_depth + 1) if certs[d] == 0]
    stalling = [d for d in range(1, max_depth + 1) if certs[d] != 0]
    a14 = [v for v in a020914(max_depth)]
    a54 = [v for v in a054414(max_depth)]
    return {
        "max_depth": max_depth,
        "doubling_lengths": doubling[:24],
        "stalling_lengths": stalling[:24],
        "stalling_is_a020914": stalling == a14,
        "doubling_is_a054414_minus_one": doubling == [v for v in a54 if v != 1],
        "doubling_is_a054414_exactly": doubling == a54,
        "one_is_the_exception": certs[1] != 0 and 1 in a54,
        "partition_of_one_to_max": sorted(doubling + stalling) == list(range(1, max_depth + 1)),
        "a020914": "floor(n log2 3) + 1",
        "a054414": "1 + floor(n / (1 - log 2 / log 3))",
    }


def recursion_holds(max_depth: int = MAX_DEPTH) -> dict[str, Any]:
    """`N_(d+1) + M_(d+1) = 2 N_d`, the laboratory's kernel-checked recursion, by DP."""
    counts, certs = survivor_recursion(max_depth)
    bad = [d for d in range(max_depth) if counts[d + 1] + certs[d + 1] != 2 * counts[d]]
    return {
        "lean_theorem": "neverNegCount_succ_sub_onBarrier",
        "statement": "N_(d+1) + M_(d+1) = 2 N_d",
        "max_depth": max_depth,
        "violations": bad,
        "holds": not bad,
        "first_twenty_counts": counts[1:21],
    }


def deficit_is_a100982(max_depth: int = MAX_DEPTH) -> dict[str, Any]:
    """`M_d` along the non-doubling lengths is A100982 with one extra leading term."""
    _counts, certs = survivor_recursion(max_depth)
    deficits = [certs[d] for d in range(1, max_depth + 1) if certs[d] != 0]
    n = min(len(deficits) - 1, len(A100982_STORED))
    return {
        "deficits_head": deficits[:12],
        "a100982_head": list(A100982_STORED[:12]),
        "equal_without_shift": deficits[:n] == list(A100982_STORED[:n]),
        "equal_after_dropping_one": deficits[1 : n + 1] == list(A100982_STORED[:n]),
        "terms_compared": n,
        "shift": "drop the laboratory's first deficit; the rest is A100982 term for term",
    }


def probe_payload(max_depth: int = MAX_DEPTH) -> dict[str, Any]:
    partition = beatty_partition(max_depth)
    return {
        "decision": {
            "classification": CLASS_NEIGHBOURHOOD,
            "call": "CLOSE",
            "reason": "one new sequence (A054414) and a closed form for the plateau "
            "lengths; the other three names were already the laboratory's",
        },
        "recursion": recursion_holds(max_depth),
        "partition": partition,
        "deficit": deficit_is_a100982(max_depth),
        "sequences": {
            "A076227": "the survivor count N_d itself; already recorded as "
            "J-paper-b-survivors-are-oeis-a076227",
            "A020914": "the stalling lengths, M_d != 0; the laboratory's own distinguished "
            "length, used throughout Papers A and B",
            "A054414": "THE ONE NEW SEQUENCE: the plateau lengths, M_d = 0, apart from "
            "d = 1; the Beatty complement of A020914, absent from the repository before this",
            "A100982": "ALREADY THE LABORATORY'S, named in CollatzBridgeLab.lean as the "
            "minimal-certificate count read by length; the deficit read along the stalling "
            "lengths only is the same thing re-indexed, carrying one extra leading term",
        },
        "provenance": (
            f"identified 20 September 2026 against a local clone of {OEIS_MIRROR}, export "
            f"stamped {OEIS_EXPORT}; oeis.org itself is refused by this environment's egress "
            "policy. OEIS content is CC BY-SA 4.0, copyright the OEIS Foundation; nothing "
            "from it is vendored here, only A-numbers and the arithmetic they name."
        ),
        "anti_overclaim": (
            "Bookkeeping, not mathematics. No bound moves, no cycle is excluded, no floor is "
            "raised, N_0 = 350000000 is untouched, and no Lean statement changes: the "
            "identifications go in docstrings and the ledger, not into new theorems. The "
            "recursion checked here is the laboratory's own, already kernel-checked; the DP "
            "reproduces it to depth 200 as an independent arithmetic check, not as a proof."
        ),
    }


def render_markdown(data: dict[str, Any]) -> str:
    p = data["partition"]
    d = data["deficit"]
    lines = [
        "# Paper B's recursion in its OEIS neighbourhood",
        "",
        f"Status: **{data['decision']['classification']}**",
        "",
        "Generated by `python -m research.juggler_sequence.oeis_neighbourhood`.",
        "",
        "## The plateau lengths are a Beatty pair",
        "",
        "The survivor recursion doubles exactly when no minimal certificate has that length, "
        "which by `minimalCertCount_eq_zero_of_window_empty` is exactly when no power of three "
        "lies in `[2^(d-1), 2^d)`. Those lengths and their complement are:",
        "",
        f"- `M_d != 0` (no doubling) iff `d` in **A020914** = `{p['a020914']}` — "
        f"checked to `d = {p['max_depth']}`: `{p['stalling_is_a020914']}`",
        f"- `M_d = 0` (doubling) iff `d` in **A054414** `\\ {{1}}` = `{p['a054414']}` — "
        f"checked to `d = {p['max_depth']}`: `{p['doubling_is_a054414_minus_one']}`",
        f"- they partition `1..{p['max_depth']}`: `{p['partition_of_one_to_max']}`",
        "",
        f"The exception is `d = 1`: A054414 contains 1, but `E` contracts at once, so "
        f"`M_1 != 0` (`{p['one_is_the_exception']}`). Without that exclusion the identity is "
        f"`{p['doubling_is_a054414_exactly']}`.",
        "",
        f"- doubling lengths: `{p['doubling_lengths']}`",
        f"- stalling lengths: `{p['stalling_lengths']}`",
        "",
        "A020914 is the laboratory's own distinguished length. **A054414, its Beatty "
        "complement, appeared nowhere in the repository before this probe.**",
        "",
        "## The deficit is A100982, shifted by one",
        "",
        f"- `M_d` along the stalling lengths: `{d['deficits_head']}`",
        f"- A100982: `{d['a100982_head']}`",
        f"- equal without a shift: `{d['equal_without_shift']}`",
        f"- equal after dropping the first: `{d['equal_after_dropping_one']}` "
        f"(`{d['terms_compared']}` terms)",
        "",
        "The shift is stated rather than absorbed, because an unstated offset is what produced "
        "this branch's A034887 error earlier the same day.",
        "",
        "## The recursion, reproduced",
        "",
        f"`{data['recursion']['statement']}` (`{data['recursion']['lean_theorem']}`, "
        f"kernel-checked) holds to depth `{data['recursion']['max_depth']}` under an "
        f"independent dynamic program: `{data['recursion']['holds']}`.",
        "",
        "## Sequences",
        "",
    ]
    for aid, meaning in data["sequences"].items():
        lines.append(f"- **{aid}** — {meaning}")
    lines += [
        "",
        "## Provenance",
        "",
        data["provenance"],
        "",
        "## What this does not say",
        "",
        data["anti_overclaim"],
        "",
    ]
    return "\n".join(lines)


def write_artifacts(payload: dict[str, Any] | None = None) -> dict[str, Any]:
    data = payload if payload is not None else probe_payload()
    DATA_DIR.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(data, indent=2) + "\n", encoding="utf-8")
    DOC_PATH.write_text(render_markdown(data), encoding="utf-8")
    return data


def main() -> None:
    data = write_artifacts()
    print(data["decision"]["classification"])
    print("recursion holds to depth 200:", data["recursion"]["holds"])
    print("stalling == A020914:", data["partition"]["stalling_is_a020914"])
    print("doubling == A054414 minus {1}:", data["partition"]["doubling_is_a054414_minus_one"])
    print("deficit == A100982 after one shift:", data["deficit"]["equal_after_dropping_one"])


if __name__ == "__main__":
    main()
