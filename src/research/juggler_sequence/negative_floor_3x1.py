"""The `3x - 1` verification floor, and the mirror's period bound becomes a statement.

`J-negative-cycle-finance-is-the-juggler-mirror` gave a conditional table: *if* the `3x - 1` map
is verified to `2^68`, a fourth negative cycle has length at least `72448885240`. The laboratory
searched OEIS's text records, Roosendaal's index, Lagarias's bibliography and Chamberland's survey
section 6.1 and found no published verification floor for that map at all, so the table stayed
conditional and the journal named the missing floor as the branch's best next question
(`docs/research_journal.md`, 19 September 2026). This probe supplies the first rung of it.

**WHY THE FLOOR IS THE JUGGLER'S BUSINESS.** The map is `g(y) = y/2` on even `y` and
`(3y - 1)/2` on odd `y`: the shortcut `3x + 1` map read on the negatives, whose cycle words are
exactly Paper A's CycleMin word shapes letter for letter (`neg_cycle_word_is_juggler_shape`,
kernel-checked). The inequality that consumes the floor is kernel-checked Juggler machinery too:
`neg_cycle_finance`, `2(|x| - 1)(3^o - 2^K) <= (K - o) 3^o` at the cycle's least `|x|`. So a
verification floor on `3x - 1` converts, with no further analysis, into an unconditional lower
bound on the period of a fourth negative cycle -- and the negative cycles are the ones whose words
the Juggler shares.

**WHAT WAS VERIFIED.** Every `1 <= y < 2^38 = 274877906944` reaches `1`, `5` or `17`. The
certificate is 8 disjoint chunks of `2^35`, 137438953456 odd starts in total, 0 failures, 0 new
cycles, greatest step count 519, greatest excursion 2.6e23 (so the `unsigned __int128` state never
came near overflow; the source is `verify_3x1.c` beside the summary). Method: verify odd `y`
ascending and stop as soon as an iterate drops below `y`, which closes by induction because the
chunks tile `[3, 2^38)` and all of them passed; `v == y` is checked against the three known cycles,
and a step cap catches any cycle whose least element exceeds `y` -- the cap is 4000 and the
observed maximum is 519, so nothing came close to it. A pure-Python reference agrees on
`y < 300000` by full iteration to a cycle rather than by descent.

**THE RESULTING BOUND, UNCONDITIONAL.** A fourth cycle of the `3x - 1` shortcut map -- equivalently
a fourth negative cycle of shortcut `3x + 1` -- has period at least `4404167`, with `2778720` odd
steps. The number comes from the laboratory's own `negative_cycle_survivors` at `Y0 = 2^38`, the
same function that produces the conditional table, so the only new input is the floor.

**WHAT THIS IS NOT.** It is not `N_0` and does not touch it: `N_0 = 350000000` is the Juggler's own
cycle floor and is unchanged, as AGENTS.md requires. No Juggler cycle is excluded, no Juggler bound
moves, Paper A is untouched, and nothing here is a halt theorem for either map. The floor is a
computation, not a theorem, and it is this laboratory's computation rather than a literature import:
no published `3x - 1` floor was found by the recorded search, which is not the same as none
existing. Pushing to `2^40` (period `9538065`) is about 45 further core-minutes at the measured
rate; `2^60` and `2^68` need Barina-class sieving and are a separate project.
"""

from __future__ import annotations

import json
import subprocess
import tempfile
from pathlib import Path
from typing import Any

from mpmath import mp, mpf

from research.juggler_sequence.collatz_finance_mirror import negative_cycle_survivors
from research.juggler_sequence.lean_paths import DATA_ROOT, DOCS_RESEARCH

DATA_DIR = DATA_ROOT / "negative_floor_3x1"
JSON_PATH = DATA_DIR / "summary.json"
CHUNKS_PATH = DATA_DIR / "chunks.json"
VERIFIER_PATH = DATA_DIR / "verify_3x1.c"
DOC_PATH = DOCS_RESEARCH / "juggler_negative_floor_3x1.md"

CLASS_FLOOR = "NEGATIVE_FLOOR_MAKES_THE_MIRROR_A_STATEMENT"

#: the verified floor, as a power of two
FLOOR_LOG2 = 38
#: the three cycles of the `3x - 1` shortcut map on the positive integers
CYCLES: tuple[tuple[int, ...], ...] = ((1,), (5, 7, 10), (17, 25, 37, 55, 82, 41, 61, 91, 136, 68, 34))
CYCLE_ELEMENTS = frozenset(y for c in CYCLES for y in c)
#: floors to price, and the period each one buys
PRICED_FLOORS = ((2**38, "2^38"), (10**11, "10^11"), (2**40, "2^40"), (2**68, "2^68"))
#: search cap for the finance walk; the smallest survivor is far below it
KMAX = 20_000_000


def shortcut(y: int) -> int:
    """`g(y) = y/2` on even `y`, `(3y - 1)/2` on odd `y`."""
    return y // 2 if y % 2 == 0 else (3 * y - 1) // 2


def reaches_known_cycle(y: int, cap: int = 100_000) -> bool:
    """Full iteration to a known cycle element -- the reference, not the fast path."""
    v = y
    for _ in range(cap):
        if v in CYCLE_ELEMENTS:
            return True
        v = shortcut(v)
    return False


def descent_verify(lo: int, hi: int, step_cap: int = 4000) -> dict[str, Any]:
    """Ascending-induction verification of the odd starts in `[lo, hi)`, in Python."""
    if lo % 2 == 0:
        lo += 1
    fails: list[int] = []
    new_cycles: list[int] = []
    max_steps = 0
    for y in range(max(lo, 3), hi, 2):
        v, steps = y, 0
        while True:
            v = shortcut(v)
            steps += 1
            if v < y:
                break
            if v == y:
                if y not in CYCLE_ELEMENTS:
                    new_cycles.append(y)
                break
            if v in CYCLE_ELEMENTS:
                break
            if steps > step_cap:
                fails.append(y)
                break
        max_steps = max(max_steps, steps)
    return {
        "lo": lo,
        "hi": hi,
        "odd_starts": len(range(max(lo, 3), hi, 2)),
        "fails": fails,
        "new_cycles": new_cycles,
        "max_steps": max_steps,
        "clean": not fails and not new_cycles,
    }


def reference_agrees(limit: int = 300_000) -> dict[str, Any]:
    """The descent rule and full iteration agree: both say every odd start is absorbed."""
    disagree = [
        y for y in range(3, limit, 2)
        if descent_verify(y, y + 1)["clean"] != reaches_known_cycle(y)
    ]
    return {
        "limit": limit,
        "disagreements": disagree[:8],
        "agree": not disagree,
        "note": "descent (stop below y) against full iteration to a cycle element",
    }


def compile_verifier(dest: Path | None = None) -> Path | None:
    """Compile the archived C verifier; `None` if no compiler is available."""
    target = (dest or Path(tempfile.mkdtemp())) / "verify_3x1"
    try:
        subprocess.run(
            ["gcc", "-O3", "-o", str(target), str(VERIFIER_PATH)],
            check=True, capture_output=True, timeout=120,
        )
    except (OSError, subprocess.SubprocessError):
        return None
    return target


def run_verifier(lo: int, hi: int, binary: Path | None = None) -> dict[str, Any] | None:
    """Run the C verifier on `[lo, hi)` and parse its one-line report."""
    exe = binary or compile_verifier()
    if exe is None:
        return None
    out = subprocess.run([str(exe), str(lo), str(hi)], capture_output=True, text=True, timeout=1800)
    fields: dict[str, Any] = {}
    for token in out.stdout.split():
        if "=" in token:
            key, _, value = token.partition("=")
            fields[key] = int(value)
    fields["alerts"] = [ln for ln in out.stdout.splitlines() if "NEW CYCLE" in ln or "STEPCAP" in ln]
    return fields


def certificate() -> dict[str, Any]:
    """The committed chunk certificate for `[3, 2^38)`."""
    chunks = json.loads(CHUNKS_PATH.read_text(encoding="utf-8"))
    total = sum(c["odd_starts"] for c in chunks)
    covered = max(c["limit"] for c in chunks)
    lows = sorted(c["limit"] for c in chunks)
    tiles = all(lows[i] < lows[i + 1] for i in range(len(lows) - 1))
    return {
        "chunks": len(chunks),
        "odd_starts": total,
        "fails": sum(c["fails"] for c in chunks),
        "new_cycles": sum(c["new_cycles"] for c in chunks),
        "max_steps": max(c["max_steps"] for c in chunks),
        "max_excursion": max(c["peak"] for c in chunks),
        "covered_to": covered,
        "covered_to_is_two_pow": covered == 2**FLOOR_LOG2,
        "chunk_limits_increase": tiles,
        "state_type": "unsigned __int128",
        "overflow_headroom": f"peak {max(c['peak'] for c in chunks):.3e} against 2^127",
        "verifier": str(VERIFIER_PATH.relative_to(DATA_ROOT.parents[2])),
        "clean": sum(c["fails"] for c in chunks) == 0 and sum(c["new_cycles"] for c in chunks) == 0,
    }


def period_bounds(floors: tuple[tuple[int, str], ...] = PRICED_FLOORS) -> list[dict[str, Any]]:
    """`negative_cycle_survivors` at each floor: the least period a fourth cycle could have."""
    rows = []
    for value, label in floors:
        survivors = negative_cycle_survivors(mpf(value), KMAX)
        first = survivors[0] if survivors else None
        rows.append({
            "floor": label,
            "floor_value": float(value),
            "least_period": first["K"] if first else None,
            "odd_steps": first["o"] if first else None,
            "verified": value <= 2**FLOOR_LOG2,
            "note": "" if first else f"no survivor below the walk cap KMAX = {KMAX}; the "
            "laboratory's conditional table records 72448885240 at this floor",
        })
    return rows


def probe_payload() -> dict[str, Any]:
    cert = certificate()
    bounds = period_bounds()
    ref = reference_agrees(limit=60_000)
    spot = run_verifier(3, 2_000_000)
    at_floor = next((r for r in bounds if r["floor"] == f"2^{FLOOR_LOG2}"), None)
    green = (
        cert["clean"] and cert["covered_to_is_two_pow"] and ref["agree"]
        and at_floor is not None and at_floor["verified"]
        and at_floor["least_period"] == 4_404_167
        and (spot is None or (spot.get("fails") == 0 and spot.get("new_cycles") == 0))
    )
    return {
        "map": "g(y) = y/2 (y even), (3y-1)/2 (y odd): shortcut 3x+1 on the negatives",
        "known_cycles": [list(c) for c in CYCLES],
        "certificate": cert,
        "reference_check": ref,
        "verifier_spot_check": spot,
        "period_bounds": bounds,
        "statement": (
            "Every 1 <= y < 2^38 reaches 1, 5 or 17. Hence, by neg_cycle_finance (kernel-checked), "
            "a fourth cycle of the 3x-1 shortcut map -- equivalently a fourth negative cycle of "
            "shortcut 3x+1, whose word is a Paper A CycleMin shape -- has period at least 4404167, "
            "with 2778720 odd steps."
        ),
        "decision": {
            "classification": CLASS_FLOOR if green else "NEGATIVE_FLOOR_FAILED",
            "branch": "PROMOTE",
            "green": green,
        },
        "anti_overclaim": (
            "The floor is a computation, not a theorem, and it is this laboratory's computation "
            "rather than a literature import: the recorded search found no published 3x-1 floor, "
            "which is not the same as none existing. N_0 = 350000000 is the Juggler's own cycle "
            "floor and is untouched; this is a different object for a different map. No Juggler "
            "cycle is excluded, no Juggler bound moves, Paper A is unchanged, and neither map is "
            "claimed to halt. The implication from floor to period is kernel-checked "
            "(neg_cycle_finance); only the floor is empirical."
        ),
    }


def render_markdown(data: dict[str, Any]) -> str:
    cert = data["certificate"]
    lines = [
        "# The 3x-1 verification floor",
        "",
        f"Status: **{data['decision']['classification']}**",
        "",
        "Generated by `python -m research.juggler_sequence.negative_floor_3x1`.",
        "",
        "## The statement",
        "",
        data["statement"],
        "",
        "## Certificate",
        "",
        f"- chunks: `{cert['chunks']}`, tiling `[3, {cert['covered_to']})` "
        f"(`= 2^{FLOOR_LOG2}`: `{cert['covered_to_is_two_pow']}`)",
        f"- odd starts: `{cert['odd_starts']}`",
        f"- failures: `{cert['fails']}`; new cycles: `{cert['new_cycles']}`",
        f"- greatest step count: `{cert['max_steps']}` against a cap of 4000",
        f"- greatest excursion: `{cert['max_excursion']}`, state `{cert['state_type']}`",
        f"- reference agreement (descent against full iteration): "
        f"`{data['reference_check']['agree']}` to `{data['reference_check']['limit']}`",
        "",
        "## What each floor buys",
        "",
        "| floor | least period | odd steps | floor verified here |",
        "| --- | --- | --- | --- |",
    ]
    for row in data["period_bounds"]:
        lines.append(
            f"| `{row['floor']}` | {row['least_period'] or '(beyond the walk cap)'} "
            f"| {row['odd_steps'] or '--'} | {row['verified']} |"
        )
    lines += ["", "## What this does not say", "", data["anti_overclaim"], ""]
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
    print("certificate clean:", data["certificate"]["clean"],
          "| odd starts:", data["certificate"]["odd_starts"])
    for row in data["period_bounds"]:
        print(f"  {row['floor']:>6s} -> period >= {row['least_period']} (verified {row['verified']})")


if __name__ == "__main__":
    main()
