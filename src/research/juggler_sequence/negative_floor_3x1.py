"""The `3x - 1` verification floor, and the mirror's period bound becomes a statement.

`J-negative-cycle-finance-is-the-juggler-mirror` gave a conditional table: *if* the `3x - 1` map
is verified to `2^68`, a fourth negative cycle has length at least `72448885240`. The laboratory
searched OEIS's text records, Roosendaal's index, Lagarias's bibliography and Chamberland's survey
section 6.1 and found no published verification floor for that map at all, so the table stayed
conditional and the journal named the missing floor as the branch's best next question
(`docs/research_journal.md`, 19 September 2026). This probe supplies it: `2^38` on 19 September,
`2^40` on the morning of 20 September, `2^44` that evening on the laboratory's own machine.

**WHY THE FLOOR IS THE JUGGLER'S BUSINESS.** The map is `g(y) = y/2` on even `y` and
`(3y - 1)/2` on odd `y`: the shortcut `3x + 1` map read on the negatives, whose cycle words are
exactly Paper A's CycleMin word shapes letter for letter (`neg_cycle_word_is_juggler_shape`,
kernel-checked). The inequality that consumes the floor is kernel-checked Juggler machinery too:
`neg_cycle_finance`, `2(|x| - 1)(3^o - 2^K) <= (K - o) 3^o` at the cycle's least `|x|`. So a
verification floor on `3x - 1` converts, with no further analysis, into an unconditional lower
bound on the period of a fourth negative cycle -- and the negative cycles are the ones whose words
the Juggler shares.

**WHAT WAS VERIFIED.** Every `1 <= y < 2^44 = 17592186044416` reaches `1`, `5` or `17`. The
certificate is 112 chunks: sixteen with the plain descent walker `verify_3x1.c` to `2^40`
(greatest step count 544 against a cap of 4000), then 96 chunks of `5 * 2^35` numbers with the
sieve-plus-jump-table walker `verify_3x1_jump.c` -- 8246337208320 odd starts counted exactly, since
every odd start is either walked or sieved -- 0 failures, 0 new cycles, greatest step count
704 against a cap of 40000 (that walker counts sixteen steps per table jump and checks
the drop only at a landing, so its counts overshoot by up to fifteen). Method: verify odd `y`
ascending and stop as soon as an iterate drops below `y`, which closes by induction once the chunks
cover the interval and all of them passed; `v == y` is checked against the three known cycles, and
the step cap catches any cycle whose least element exceeds `y` -- with the jump table a jump can
carry past the return, so such a cycle surfaces as a `STEPCAP`, reported and never a silent pass.
The sieve is unconditional on this side (`neg_prefix_noncontracting`: a contracting prefix drops
every member of its residue class), and its class count at `K = 24` is `A076227(24) = 286581`.
The greatest landing value seen above `2^40`, `121443575752945981388885320`, exceeds the record
`261160802435320822179964` from below `2^40`; the `unsigned __int128` state never came near
overflow. A pure-Python reference agrees on `y < 300000` by full iteration to a cycle rather than
by descent. Sources, raw reports, driver and a run record with the source digest, compiler,
host and timings are archived beside the summary; `compile_verifier` builds either walker with
`gcc`, or inside WSL on a Windows checkout without one, and `run_verifier` re-runs it on any window.

**THE HOLE IN THE FIRST CERTIFICATE, FOUND FROM ITS OWN PRINTOUT.** The plain walker prints
`odd_starts = floor((limit - lo)/2)` with `lo` odd, which undercounts each chunk by one; the
committed total to `2^40` was short by 23, and the only launch value that reproduces the recorded
counts of chunks 1 to 7 is `k * 2^35 + 3`. So the seven odd starts `k * 2^35 + 1`, `k = 1..7`, lay
between the chunks of the `2^38` certificate and were walked by nothing. Each reaches a known cycle
by full iteration (118 to 232 steps to the first drop), as does every odd start within 64 of every
legacy boundary. `first_odd_start` recovers every chunk's launch value, `certificate` lists every
gap between chunks and verifies each, and the certificate is not clean otherwise. The floor
statements at `2^38` and `2^40` were true; the word "tiling" was not.

**THE RESULTING BOUND, UNCONDITIONAL.** A fourth cycle of the `3x - 1` shortcut map -- equivalently
a fourth negative cycle of shortcut `3x + 1` -- has period at least `16483927`, with `10400200` odd
steps; the uniform and hug-word constants give the same length at this floor. The number comes from
the laboratory's own `negative_cycle_survivors` at `Y0 = 2^44`, the same function that produces the
conditional table, so the only new input is the floor. At `2^40` it was `9538065` with `6017849`
odd steps; at `2^38`, `4404167`.

**WHAT THIS IS NOT.** It is not `N_0` and does not touch it: `N_0 = 350000000` is the Juggler's own
cycle floor and is unchanged, as AGENTS.md requires. No Juggler cycle is excluded, no Juggler bound
moves, Paper A is untouched (its Remark 5.20 quotes the `2^40` numbers; the `2^44` ones belong to
its next revision), and nothing here is a halt theorem for either map. The floor is a computation,
not a theorem, and it is this laboratory's computation rather than a literature import: no published
`3x - 1` floor was found by the recorded search, which is not the same as none existing.
`[2^40, 2^44)` took 27 minutes on 24 threads at about 393 million odd starts per second per
core; `2^48` is an overnight run here, and `2^60`, `2^68` need Barina-class sieving on a GPU.
"""

from __future__ import annotations

import json
import shutil
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
JUMP_VERIFIER_PATH = DATA_DIR / "verify_3x1_jump.c"
RUNS_PATH = DATA_DIR / "runs.json"
DOC_PATH = DOCS_RESEARCH / "juggler_negative_floor_3x1.md"

CLASS_FLOOR = "NEGATIVE_FLOOR_MAKES_THE_MIRROR_A_STATEMENT"

#: the verified floor, as a power of two
FLOOR_LOG2 = 44
#: step caps of the two archived verifiers; a start exceeding its cap is a reported failure,
#: never a silent pass. The jump verifier counts J = 16 steps per table jump and only checks
#: the drop at a landing, so its step counts overshoot the plain verifier's by up to 15.
STEP_CAP_PLAIN = 4000
STEP_CAP_JUMP = 40000
#: the three cycles of the `3x - 1` shortcut map on the positive integers
CYCLES: tuple[tuple[int, ...], ...] = ((1,), (5, 7, 10), (17, 25, 37, 55, 82, 41, 61, 91, 136, 68, 34))
CYCLE_ELEMENTS = frozenset(y for c in CYCLES for y in c)
#: floors to price, and the period each one buys
PRICED_FLOORS = (
    (2**38, "2^38"), (10**11, "10^11"), (2**40, "2^40"), (2**44, "2^44"), (2**51, "2^51"), (2**68, "2^68"),
)
#: search cap for the finance walk; the smallest survivor is far below it (85137581 at 2^51)
KMAX = 400_000_000
#: the GPU sweep record and its checks, written by negative_floor_gpu (sweep, spot)
GPU_RUNS_PATH = DATA_DIR / "gpu_runs.json"
GPU_SPOT_PATH = DATA_DIR / "gpu_calibration" / "spot_checks_2p44_2p51.json"
GPU_CALIBRATION_PATH = DATA_DIR / "gpu_calibration" / "summary.json"


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


def _wsl_path(path: Path) -> str:
    """`C:\\x\\y` as WSL sees it, `/mnt/c/x/y`; other paths unchanged."""
    text = str(path.resolve()).replace("\\", "/")
    if len(text) > 1 and text[1] == ":":
        return f"/mnt/{text[0].lower()}{text[2:]}"
    return text


def compile_verifier(
    dest: Path | None = None, source: Path = VERIFIER_PATH,
) -> list[str] | None:
    """Compile an archived C verifier; the command that runs it, or `None` without a compiler.

    Native `gcc` first. The sources need `unsigned __int128`, which MSVC lacks, so on a Windows
    checkout without gcc -- this laboratory's own machine -- the fallback builds and runs the
    verifier inside the default WSL distribution, which is where the `2^44` certificate was made.
    """
    target = (dest or Path(tempfile.mkdtemp())) / source.stem
    if shutil.which("gcc"):
        try:
            subprocess.run(
                ["gcc", "-O3", "-o", str(target), str(source)],
                check=True, capture_output=True, timeout=120,
            )
        except (OSError, subprocess.SubprocessError):
            return None
        return [str(target)]
    if shutil.which("wsl.exe"):
        wsl_target = f"/tmp/{source.stem}_{target.parent.name}"
        try:
            subprocess.run(
                ["wsl.exe", "gcc", "-O3", "-o", wsl_target, _wsl_path(source)],
                check=True, capture_output=True, timeout=300,
            )
        except (OSError, subprocess.SubprocessError):
            return None
        return ["wsl.exe", wsl_target]
    return None


def parse_report(text: str) -> dict[str, Any]:
    """A verifier's `key=value` report, with the 128-bit peak reassembled and the alerts kept."""
    fields: dict[str, Any] = {}
    for token in text.split():
        if "=" in token:
            key, _, value = token.partition("=")
            fields[key] = int(value)
    if "peak_hi" in fields and "peak_lo" in fields:
        fields["peak"] = (fields["peak_hi"] << 64) | fields["peak_lo"]
    fields["alerts"] = [ln for ln in text.splitlines() if "NEW CYCLE" in ln or "STEPCAP" in ln]
    return fields


def run_verifier(lo: int, hi: int, command: list[str] | None = None) -> dict[str, Any] | None:
    """Run a compiled verifier on `[lo, hi)` and parse its report; `None` without a compiler."""
    cmd = command or compile_verifier()
    if cmd is None:
        return None
    out = subprocess.run([*cmd, str(lo), str(hi)], capture_output=True, text=True, timeout=1800)
    return parse_report(out.stdout)


def certificate() -> dict[str, Any]:
    """The committed chunk certificate for `[3, 2^FLOOR_LOG2)`.

    Chunks are ordered by `limit`. A chunk that records its `lo` must start exactly where the
    previous chunk stopped, so the tiling is checked, not read off increasing limits; the first
    sixteen chunks, made before `lo` was recorded, are pinned by their limits alone. Each chunk
    names its verifier: the plain descent walker below `2^40`, the sieve-plus-jump-table walker
    above it, whose peak is a maximum over walked starts and jump landings only.
    """
    chunks = sorted(json.loads(CHUNKS_PATH.read_text(encoding="utf-8")), key=lambda c: c["limit"])
    plain = VERIFIER_PATH.name
    by_verifier: dict[str, int] = {}
    for c in chunks:
        name = c.get("verifier", plain)
        by_verifier[name] = by_verifier.get(name, 0) + 1
    steps_by_verifier = {
        name: max(c["max_steps"] for c in chunks if c.get("verifier", plain) == name)
        for name in by_verifier
    }
    covered = chunks[-1]["limit"]
    fails = sum(c["fails"] for c in chunks)
    new_cycles = sum(c["new_cycles"] for c in chunks)
    peak = max(c["peak"] for c in chunks)
    gaps = [
        y
        for a, b in zip(chunks, chunks[1:])
        for y in range(a["limit"] | 1, first_odd_start(b), 2)
    ]
    gap_checks = {y: reaches_known_cycle(y, cap=1_000_000) for y in gaps}
    return {
        "chunks": len(chunks),
        "chunks_by_verifier": by_verifier,
        "odd_starts": sum(c["odd_starts"] for c in chunks),
        "fails": fails,
        "new_cycles": new_cycles,
        "max_steps": max(c["max_steps"] for c in chunks),
        "max_steps_by_verifier": steps_by_verifier,
        "step_caps": {plain: STEP_CAP_PLAIN, JUMP_VERIFIER_PATH.name: STEP_CAP_JUMP},
        "max_excursion": peak,
        "covered_to": covered,
        "covered_to_is_two_pow": covered == 2**FLOOR_LOG2,
        "chunk_limits_increase": all(a["limit"] < b["limit"] for a, b in zip(chunks, chunks[1:])),
        "chunks_are_contiguous": not gaps,
        "gap_starts": gaps,
        "gap_starts_verified": all(gap_checks.values()),
        "state_type": "unsigned __int128",
        "overflow_headroom": f"peak {peak:.3e} against 2^127",
        "verifier": str(VERIFIER_PATH.relative_to(DATA_ROOT.parents[2])),
        "verifiers": sorted(
            str(p.relative_to(DATA_ROOT.parents[2])) for p in (VERIFIER_PATH, JUMP_VERIFIER_PATH)
        ),
        "runs": json.loads(RUNS_PATH.read_text(encoding="utf-8")) if RUNS_PATH.exists() else [],
        "clean": fails == 0 and new_cycles == 0 and all(gap_checks.values()),
    }


def first_odd_start(chunk: dict[str, Any]) -> int:
    """The first odd start a chunk walked.

    Its recorded `lo`, rounded up to odd as the verifiers do; for the sixteen plain-verifier
    chunks made before `lo` was recorded, the launch value recovered exactly from the printout,
    since the plain verifier prints `odd_starts = floor((limit - lo)/2)` with `lo` odd and
    `limit` even, hence `lo = limit - 2 odd_starts - 1`. That recovery is what showed chunks
    1 to 7 of the original `2^38` certificate were launched at `k 2^35 + 3`, leaving the seven
    odd starts `k 2^35 + 1` between chunks; `certificate` lists such gaps and verifies each by
    full iteration to a known cycle.
    """
    if "lo" in chunk:
        return chunk["lo"] | 1
    return chunk["limit"] - 2 * chunk["odd_starts"] - 1


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
            "verified": value <= 2**combined_floor_log2(),
            "note": "" if first else f"no survivor below the walk cap KMAX = {KMAX}; the "
            "laboratory's conditional table records 72448885240 at this floor",
        })
    return rows


def gpu_extension() -> dict[str, Any]:
    """The GPU sweep above the CPU certificate, if its record is clean and starts where the
    certificate stops, with its calibration and the spot checks against the CPU walker."""
    if not GPU_RUNS_PATH.is_file():
        return {"present": False}
    records = json.loads(GPU_RUNS_PATH.read_text(encoding="utf-8"))
    chain = sorted((r for r in records if r.get("clean")), key=lambda r: r["range"][0])
    covered = 2**FLOOR_LOG2
    used = []
    for r in chain:
        if r["range"][0] == covered:
            covered = r["range"][1]
            used.append(r)
    spot = json.loads(GPU_SPOT_PATH.read_text(encoding="utf-8")) if GPU_SPOT_PATH.is_file() else None
    cal = json.loads(GPU_CALIBRATION_PATH.read_text(encoding="utf-8")) if GPU_CALIBRATION_PATH.is_file() else None
    return {
        "present": bool(used),
        "covered_to": covered,
        "covered_to_log2": covered.bit_length() - 1 if covered & (covered - 1) == 0 else None,
        "records": [{k: v for k, v in r.items() if k not in ("chunk_reports", "overflow_rewalks")} for r in used],
        "overflow_rewalks": [w for r in used for w in r.get("overflow_rewalks", [])],
        "calibration_agrees": bool(cal and cal["comparison"]["all_agree"]),
        "spot_checks_agree": None if spot is None else bool(spot.get("all_agree")),
        "spot_checks": None if spot is None else spot.get("windows"),
        "verifier": "data/research/juggler/negative_floor_3x1/verify_3x1_gpu.cu",
    }


def combined_floor_log2() -> int:
    """The CPU certificate's floor, extended by a clean GPU sweep that starts at it."""
    ext = gpu_extension()
    if ext.get("present") and ext.get("covered_to_log2") and ext.get("calibration_agrees"):
        return ext["covered_to_log2"]
    return FLOOR_LOG2


def probe_payload() -> dict[str, Any]:
    cert = certificate()
    bounds = period_bounds()
    ref = reference_agrees(limit=60_000)
    spot = run_verifier(3, 2_000_000)
    ext = gpu_extension()
    floor_log2 = combined_floor_log2()
    at_floor = next((r for r in bounds if r["floor"] == f"2^{floor_log2}"), None)
    green = (
        cert["clean"] and cert["covered_to_is_two_pow"] and ref["agree"]
        and at_floor is not None and at_floor["verified"]
        and at_floor["least_period"] is not None
        and (spot is None or (spot.get("fails") == 0 and spot.get("new_cycles") == 0))
        and (not ext.get("present") or ext.get("spot_checks_agree") in (None, True))
    )
    return {
        "map": "g(y) = y/2 (y even), (3y-1)/2 (y odd): shortcut 3x+1 on the negatives",
        "known_cycles": [list(c) for c in CYCLES],
        "certificate": cert,
        "gpu_extension": ext,
        "floor_log2": floor_log2,
        "reference_check": ref,
        "verifier_spot_check": spot,
        "period_bounds": bounds,
        "statement": (
            f"Every 1 <= y < 2^{floor_log2} reaches 1, 5 or 17"
            + (f" (CPU certificate to 2^{FLOOR_LOG2}, GPU sweep to 2^{floor_log2})" if floor_log2 != FLOOR_LOG2 else "")
            + ". Hence, by neg_cycle_finance "
            "(kernel-checked), a fourth cycle of the 3x-1 shortcut map -- equivalently a fourth "
            "negative cycle of shortcut 3x+1, whose word is a Paper A CycleMin shape -- has period "
            f"at least {at_floor['least_period'] if at_floor else 'unknown'}, with "
            f"{at_floor['odd_steps'] if at_floor else 'unknown'} odd steps."
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
        f"- chunks: `{cert['chunks']}`, covering `[3, {cert['covered_to']})` "
        f"(`= 2^{FLOOR_LOG2}`: `{cert['covered_to_is_two_pow']}`; "
        f"contiguous: `{cert['chunks_are_contiguous']}`)",
        f"- odd starts between chunks, each verified by full iteration: `{cert['gap_starts']}` "
        f"(all reach a known cycle: `{cert['gap_starts_verified']}`)",
        f"- chunks by verifier: `{cert['chunks_by_verifier']}`",
        f"- odd starts: `{cert['odd_starts']}`",
        f"- failures: `{cert['fails']}`; new cycles: `{cert['new_cycles']}`",
        f"- greatest step count by verifier: `{cert['max_steps_by_verifier']}` "
        f"against caps `{cert['step_caps']}`",
        f"- greatest excursion: `{cert['max_excursion']}`, state `{cert['state_type']}` "
        "(above `2^40` a maximum over walked starts and jump landings only)",
        f"- reference agreement (descent against full iteration): "
        f"`{data['reference_check']['agree']}` to `{data['reference_check']['limit']}`",
        "",
    ]
    ext = data.get("gpu_extension", {})
    if ext.get("present"):
        lines += ["## GPU extension", ""]
        for r in ext["records"]:
            lines.append(
                f"- `[{r['range'][0]}, {r['range'][1]})` = `[2^{r['range_log2'][0]}, 2^{r['range_log2'][1]})` by "
                f"`{r['verifier']}` on {r['gpu']}: {r['chunks']} chunks, odd starts `{r['odd_starts']}` "
                f"(coverage exact: `{r['coverage_exact']}`), failures `{r['fails']}`, new cycles `{r['new_cycles']}`, "
                f"overflows `{r['overflows']}`, greatest step count `{r['max_steps']}`, peak `{r['peak']}` "
                f"(about 2^{r['peak_log2']:.1f}), {r['wall_seconds']} s wall"
            )
        lines += [
            f"- calibration on the CPU's range agrees: `{ext['calibration_agrees']}`; spot checks against the "
            f"CPU jump walker inside the new range agree: `{ext['spot_checks_agree']}`",
            f"- combined floor: `2^{data['floor_log2']}`",
            "",
        ]
    lines += [
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
