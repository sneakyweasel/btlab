"""N0 → L_finance(N0) sensitivity for the Juggler cycle-finance cutoff.

Not a halt theorem, not a leftover-word census, and not a new
inequality. This module evaluates the *implemented* Paper A
architecture

    exact cells → CycleMin → finance → n_max(L) → verified floor → period bound

at hypothetical verified floors, then (if justified) reruns the
existing exact first-passage verifier with a 100M+ bit cap.

Three numerical layers are kept separate:

1. exact theorem: cycleMin_finance (constant 1) and the 6/5
   length-only / run-packed human proofs;
2. numerical optimization: the padded Python comparisons already
   used by parity_scan / budget_scan;
3. heuristic extrapolation: recorded as such, never as a theorem.

Dossier: docs/problems/juggler_descent_floor.md.
"""

from __future__ import annotations

from research.juggler_sequence.lean_paths import (
    DOCS_RESEARCH,
)

import hashlib
import json
import math
import os
import sys
import time
from concurrent.futures import ProcessPoolExecutor, as_completed
from pathlib import Path
from typing import Any, Iterator

from research.juggler_sequence.cycle_budget_opt import (
    budget_excludes,
    budget_n_max,
    budget_survives_floor,
)
from research.juggler_sequence.cycle_finance import (
    BIT_CAP,
    DATA_DIR,
    EPS_CONST,
    MIN_STATE,
    PROGRESS_CHUNK,
    PUBLISHED_FLOOR,
    SCIENCE_L_MAX,
    STEP_CAP,
    _floor_workers,
    _format_hms,
    _odd_chunk_first_passage,
    _report_floor_progress,
    git_commit,
    n_max_from_bound,
    o_min_and_theta,
    parity_excludes,
    parity_n_max,
    parity_survives_floor,
    sha256_int_list,
    verify_floor,
)

SENS_DIR = DATA_DIR / "floor_sensitivity"
VERIFY_DIR = DATA_DIR / "floor_verify"

# Published architecture (Theorem 4.6) plus the two neighbouring
# numerical layers. 10^9 exhausts L <= 10^5 on the crude table, so
# the scan must go past the next principal leftover.
HYPOTHETICAL_FLOORS = (
    10**6,
    10**7,
    26_254_995,  # n_max^par(25781) at 6/5
    68_000_000,  # SCIENCE_FLOOR; just above crude n_max(25781)
    10**8,
    10**9,
)
SPOTLIGHT_LENGTHS = (1054, 25780, 25781, 50508, 76289, 99962)
L_MAX_SENSITIVITY = 200_000
BASELINE_PREFIX = 25780

# Cost model fitted to the existing 68M progress log
# (22_211 n/s at 23 workers, 82M-bit peak). Diagnostic only.
REF_RATE_N_PER_S = 22_211.0
REF_WORKERS = 23


def iter_o_min(l_max: int) -> Iterator[tuple[int, int, float]]:
    """Incremental (L, o_min, θ) with exact integer powers."""

    pow2 = 1
    pow3 = 1
    odd_count = 0
    for length in range(1, l_max + 1):
        pow2 <<= 1
        while pow3 <= pow2:
            pow3 *= 3
            odd_count += 1
        yield length, odd_count, (pow3 - pow2) / pow3


def crude_n_max(length: int, theta: float, *, const: float = EPS_CONST) -> int:
    """n_max from B(L) = const · L / θ. Conservative float lift."""

    if theta <= 0.0:
        return 10**18
    return n_max_from_bound(const * length / theta)


def layer_status(
    length: int,
    odd_count: int,
    theta: float,
    n0: int,
    *,
    layer: str,
    const: float = EPS_CONST,
) -> str:
    """certified_exclude | certified_survive | uncertain."""

    if layer == "parity":
        excluded = parity_excludes(length, odd_count, theta, n0, const=const)
        survives = parity_survives_floor(
            length, odd_count, theta, n0, const=const
        )
    elif layer == "runpack":
        excluded = budget_excludes(length, odd_count, theta, n0, const=const)
        survives = budget_survives_floor(
            length, odd_count, theta, n0, const=const
        )
    elif layer == "crude":
        start = max(n0 + 1, MIN_STATE)
        bound = const * length / theta
        # Conservative: exclude only when start * ln(start) is
        # strictly above the inflated bound used by n_max_from_bound.
        inflated = bound * (1.0 + 1e-9) + 1.0
        excluded = start * math.log(start) > inflated
        survives = start * math.log(start) <= bound
    else:
        raise ValueError(f"unknown layer {layer}")
    if excluded and not survives:
        return "certified_exclude"
    if survives and not excluded:
        return "certified_survive"
    return "uncertain"


def scan_layer(
    n0: int,
    *,
    l_max: int = L_MAX_SENSITIVITY,
    layer: str = "parity",
    const: float = EPS_CONST,
) -> dict[str, Any]:
    """Contiguous finance cutoff at a hypothetical floor."""

    survivors: list[int] = []
    uncertain: list[int] = []
    for length, odd_count, theta in iter_o_min(l_max):
        status = layer_status(
            length, odd_count, theta, n0, layer=layer, const=const
        )
        if status == "certified_survive":
            survivors.append(length)
        elif status == "uncertain":
            uncertain.append(length)
    first = survivors[0] if survivors else None
    prefix = (first - 1) if first is not None else l_max
    return {
        "layer": layer,
        "const": const,
        "floor": n0,
        "l_max": l_max,
        "first_exception": first,
        "contiguous_prefix": prefix,
        "table_exhausted": first is None,
        "survivor_count": len(survivors),
        "uncertain_count": len(uncertain),
        "uncertain": uncertain[:50],
        "sha256_lengths": sha256_int_list(survivors),
        "halt_theorem": False,
        "no_cycle_all_lengths": False,
    }


def spotlight_thresholds(
    lengths: tuple[int, ...] = SPOTLIGHT_LENGTHS,
) -> list[dict[str, Any]]:
    """Exact implemented n_max at named leftover / near-record lengths."""

    rows: list[dict[str, Any]] = []
    for length in lengths:
        odd_count, theta = o_min_and_theta(length)
        rows.append(
            {
                "L": length,
                "o": odd_count,
                "e": length - odd_count,
                "theta": theta,
                "n_max_parity_6_5": parity_n_max(
                    length, odd_count, theta, const=EPS_CONST
                ),
                "n_max_parity_1": parity_n_max(
                    length, odd_count, theta, const=1.0
                ),
                "n_max_runpack_6_5": budget_n_max(
                    length, odd_count, theta, const=EPS_CONST
                ),
                "n_max_crude_6_5": crude_n_max(
                    length, theta, const=EPS_CONST
                ),
                "n_max_crude_1": crude_n_max(length, theta, const=1.0),
            }
        )
    return rows


def estimate_verify_cost(n0: int) -> dict[str, Any]:
    """Diagnostic wall-time from the existing 68M progress log.

    Not a certification input. Linear in N0 at the measured rate;
    hard-seed million-bit isqrt can dominate and is not modelled.
    """

    seconds = n0 / REF_RATE_N_PER_S if REF_RATE_N_PER_S else math.inf
    return {
        "n0": n0,
        "ref_rate_n_per_s": REF_RATE_N_PER_S,
        "ref_workers": REF_WORKERS,
        "estimated_s": seconds,
        "estimated_hms": _format_hms(seconds),
        "heuristic": True,
    }


def sensitivity_table(
    floors: tuple[int, ...] = HYPOTHETICAL_FLOORS,
    *,
    l_max: int = L_MAX_SENSITIVITY,
) -> dict[str, Any]:
    """N0 ↦ L_max for the implemented layers.

    Primary architecture is parity 6/5 (Paper A Theorem 4.6).
    Run-packing is Theorem 4.7; crude is Corollary 4.5; constant 1
    is the Lean inequality with the same length-only packing.
    """

    layers = (
        ("parity_6/5", "parity", EPS_CONST),
        ("runpack_6/5", "runpack", EPS_CONST),
        ("parity_1", "parity", 1.0),
        ("crude_6/5", "crude", EPS_CONST),
    )
    rows: list[dict[str, Any]] = []
    for n0 in floors:
        entry: dict[str, Any] = {
            "floor": n0,
            "cost": estimate_verify_cost(n0),
        }
        for name, layer, const in layers:
            scan = scan_layer(n0, l_max=l_max, layer=layer, const=const)
            gain = scan["contiguous_prefix"] - BASELINE_PREFIX
            entry[name] = {
                "L_max": scan["contiguous_prefix"],
                "first_exception": scan["first_exception"],
                "gain_over_25780": gain,
                "survivor_count": scan["survivor_count"],
                "uncertain_count": scan["uncertain_count"],
                "table_exhausted": scan["table_exhausted"],
                "sha256_lengths": scan["sha256_lengths"],
            }
        rows.append(entry)

    # Cheapest floor among the list that raises the Theorem 4.6 cutoff.
    primary = [
        (row["floor"], row["parity_6/5"]["L_max"], row["parity_6/5"]["gain_over_25780"])
        for row in rows
    ]
    jumps = [item for item in primary if item[2] > 0]
    cheapest_gain = min(jumps, key=lambda item: item[0]) if jumps else None

    return {
        "architecture": "parity_6/5 Theorem 4.6",
        "baseline_prefix": BASELINE_PREFIX,
        "published_floor": PUBLISHED_FLOOR,
        "l_max": l_max,
        "layers": [name for name, _, _ in layers],
        "spotlight": spotlight_thresholds(),
        "rows": rows,
        "cheapest_floor_with_gain": (
            None
            if cheapest_gain is None
            else {
                "floor": cheapest_gain[0],
                "L_max": cheapest_gain[1],
                "gain_over_25780": cheapest_gain[2],
            }
        ),
        "bit_cap": BIT_CAP,
        "step_cap": STEP_CAP,
        "halt_theorem": False,
        "no_cycle_all_lengths": False,
    }


def _chunk_path(out_dir: Path, start: int, stop: int) -> Path:
    return out_dir / "chunks" / f"{start}_{stop}.json"


def _write_json(path: Path, payload: dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")


def _chunk_record(
    start: int,
    stop: int,
    step_cap: int,
    bit_cap: int,
) -> dict[str, Any]:
    (
        step_fail,
        bit_fail,
        other_fail,
        max_steps,
        hardest,
        max_bits,
        max_bits_seed,
        total_steps,
    ) = _odd_chunk_first_passage(start, stop, step_cap, bit_cap)
    lo = start + (start % 2 == 0)
    hi = stop - (stop % 2 == 0)
    odds = 0 if lo > hi else (hi - lo) // 2 + 1
    return {
        "start": start,
        "stop": stop,
        "odds_walked": max(0, odds),
        "step_failures": step_fail,
        "bit_failures": bit_fail,
        "other_failures": other_fail,
        "max_steps": max_steps,
        "hardest_seed": hardest,
        "max_bits": max_bits,
        "max_bits_seed": max_bits_seed,
        "total_steps": total_steps,
        "step_cap": step_cap,
        "bit_cap": bit_cap,
        "exact_integer": True,
        "floating_point_used": False,
    }


def _load_or_run_chunk(
    start: int,
    stop: int,
    step_cap: int,
    bit_cap: int,
    out_dir: Path | None,
    resume: bool,
) -> dict[str, Any]:
    if out_dir is not None and resume:
        path = _chunk_path(out_dir, start, stop)
        if path.is_file():
            return json.loads(path.read_text(encoding="utf-8"))
    record = _chunk_record(start, stop, step_cap, bit_cap)
    if out_dir is not None:
        _write_json(_chunk_path(out_dir, start, stop), record)
    return record


def verify_floor_certified(
    n_top: int,
    *,
    n_from: int = 2,
    step_cap: int = STEP_CAP,
    bit_cap: int = BIT_CAP,
    progress: bool | None = None,
    workers: int | None = None,
    resume: bool = True,
    out_dir: Path | None = None,
) -> dict[str, Any]:
    """Exact first-passage descent induction on 2 ≤ n ≤ n_top.

    Evens drop in one integer square-root. Odds are walked with
    exact integer isqrt until the iterate is strictly below the
    start. A periodic state never reaches 1, so a verified floor
    excludes every cycle that would have to sit at or below n_top.

    Floating point is not used for parity, the iterate, first
    passage, or success/failure. Optional chunk files make the run
    resumable and independently checksummable.
    """

    if n_top < 2:
        raise ValueError("n_top must be at least 2")
    if n_from < 2:
        raise ValueError("n_from must be at least 2")
    if progress is None:
        progress = n_top >= 100_000
    env_bits = os.environ.get("JUGGLER_FLOOR_BIT_CAP")
    if env_bits:
        bit_cap = max(bit_cap, int(env_bits))
    if out_dir is None:
        out_dir = VERIFY_DIR / f"N{n_top}"
    worker_count = _floor_workers(n_top, workers)
    walk_from = max(3, n_from if n_from % 2 == 1 else n_from + 1)
    chunks = [
        (start, min(start + PROGRESS_CHUNK - 1, n_top))
        for start in range(walk_from, n_top + 1, PROGRESS_CHUNK)
    ]
    started = time.perf_counter()
    records: list[dict[str, Any]] = []

    def absorb(record: dict[str, Any]) -> None:
        records.append(record)

    def emit(done: int) -> None:
        elapsed = time.perf_counter() - started
        chunks_total = len(chunks)
        n_done = min(n_top, walk_from - 1 + done * PROGRESS_CHUNK)
        walked = max(0, n_done - walk_from + 1)
        extension = max(1, n_top - walk_from + 1)
        rate = walked / elapsed if elapsed > 0 else 0.0
        remain = (extension - walked) / rate if rate > 0 else 0.0
        max_steps = max((row["max_steps"] for row in records), default=0)
        hardest = 0
        for row in records:
            if row["max_steps"] == max_steps:
                hardest = row["hardest_seed"]
        max_bits = max((row["max_bits"] for row in records), default=0)
        fails = sum(
            len(row["step_failures"])
            + len(row["bit_failures"])
            + len(row["other_failures"])
            for row in records
        )
        _report_floor_progress(
            {
                "n": n_done,
                "n_top": n_top,
                "n_from": n_from,
                "pct": 100.0 * walked / extension,
                "rate_n_per_s": rate,
                "elapsed_s": elapsed,
                "eta_s": remain,
                "elapsed": _format_hms(elapsed),
                "eta": _format_hms(remain),
                "hardest_seed": hardest,
                "max_steps": max_steps,
                "max_bits": max_bits,
                "failure_count": fails,
                "workers": worker_count,
                "bit_cap": bit_cap,
                "chunks_done": done,
                "chunks_total": chunks_total,
            }
        )

    if worker_count == 1 or len(chunks) <= 1:
        for index, (start, stop) in enumerate(chunks, start=1):
            absorb(
                _load_or_run_chunk(
                    start, stop, step_cap, bit_cap, out_dir, resume
                )
            )
            if progress:
                emit(index)
    else:
        if progress:
            print(
                f"verify_floor_certified n_top={n_top} workers={worker_count} "
                f"chunks={len(chunks)} bit_cap={bit_cap}",
                file=sys.stderr,
                flush=True,
            )
        with ProcessPoolExecutor(max_workers=worker_count) as pool:
            futures = {
                pool.submit(
                    _load_or_run_chunk,
                    start,
                    stop,
                    step_cap,
                    bit_cap,
                    out_dir,
                    resume,
                ): (start, stop)
                for start, stop in chunks
            }
            done = 0
            for future in as_completed(futures):
                absorb(future.result())
                done += 1
                if progress:
                    emit(done)

    records.sort(key=lambda row: row["start"])
    step_failures = [n for row in records for n in row["step_failures"]]
    bit_failures = [n for row in records for n in row["bit_failures"]]
    other_failures = [n for row in records for n in row["other_failures"]]
    failures = step_failures + bit_failures + other_failures
    max_steps = max((row["max_steps"] for row in records), default=0)
    hardest = 0
    for row in records:
        if row["max_steps"] == max_steps:
            hardest = row["hardest_seed"]
    max_bits = max((row["max_bits"] for row in records), default=0)
    max_bits_seed = 0
    for row in records:
        if row["max_bits"] == max_bits:
            max_bits_seed = row["max_bits_seed"]
    total_steps = sum(row["total_steps"] for row in records)
    odds_walked = sum(row["odds_walked"] for row in records)
    chunk_blob = json.dumps(records, separators=(",", ":")).encode("ascii")
    certificate = {
        "schema": "juggler-descent-floor-v1",
        "N0": n_top,
        "n_from": n_from,
        "starting_values": n_top,  # 1..N0, with n=1 trivial
        "odds_walked": odds_walked,
        "total_first_passage_steps": total_steps,
        "max_stopping_time": max_steps,
        "hardest_seed": hardest,
        "max_bits": max_bits,
        "max_bits_seed": max_bits_seed,
        "bit_cap": bit_cap,
        "step_cap": step_cap,
        "verified": not failures,
        "step_failures": step_failures,
        "bit_failures": bit_failures,
        "other_failures": other_failures,
        "exact_integer": True,
        "floating_point_used_for_certification": False,
        "implementation": "research.juggler_sequence.cycle_floor_sensitivity.verify_floor_certified",
        "git_commit": git_commit(),
        "sha256_chunks": hashlib.sha256(chunk_blob).hexdigest(),
        "chunk_count": len(records),
        "workers": worker_count,
        "elapsed_s": time.perf_counter() - started,
        "halt_theorem": False,
        "no_cycle_all_lengths": False,
    }
    _write_json(out_dir / "certificate.json", certificate)
    _write_json(out_dir / "chunks_index.json", {"chunks": records})
    return certificate


def recompute_period_bound(
    n0: int,
    *,
    l_max: int = L_MAX_SENSITIVITY,
    const: float = EPS_CONST,
) -> dict[str, Any]:
    """Theorem 4.6 instance at a verified floor: no new inequality."""

    parity = scan_layer(n0, l_max=l_max, layer="parity", const=const)
    packed = scan_layer(n0, l_max=l_max, layer="runpack", const=const)
    return {
        "floor": n0,
        "architecture": "parity_6/5 Theorem 4.6",
        "L_star": parity["contiguous_prefix"],
        "first_survivor": parity["first_exception"],
        "parity_survivors": parity["survivor_count"],
        "runpack_L_star": packed["contiguous_prefix"],
        "runpack_first_survivor": packed["first_exception"],
        "runpack_survivors": packed["survivor_count"],
        "statement": (
            f"No nontrivial Juggler cycle has length at most "
            f"{parity['contiguous_prefix']}"
            if parity["first_exception"] is not None
            else (
                f"No nontrivial Juggler cycle has length at most "
                f"{parity['contiguous_prefix']} "
                f"(table exhausted at L={l_max})"
            )
        ),
        "not_a_termination_proof": True,
        "not_a_search_for_cycles": True,
        "sha256_parity": parity["sha256_lengths"],
        "sha256_runpack": packed["sha256_lengths"],
    }


def bottleneck_note(certificate: dict[str, Any] | None = None) -> dict[str, Any]:
    """What limits the theorem after the current floor."""

    spots = {row["L"]: row for row in spotlight_thresholds()}
    need_25781 = spots[25781]["n_max_parity_6_5"]
    need_50508 = spots[50508]["n_max_parity_6_5"]
    current = PUBLISHED_FLOOR if certificate is None else certificate["N0"]
    if current < need_25781:
        kind = "computation"
        detail = (
            f"parity n_max(25781)={need_25781}; current floor {current} "
            "does not yet buy the first leftover"
        )
        next_floor = need_25781
    elif current < need_50508:
        kind = "computation"
        detail = (
            f"25781 is dead; next record leftover L=50508 needs "
            f"N0>={need_50508}"
        )
        next_floor = need_50508
    else:
        kind = "finance_or_next_convergent"
        detail = (
            "both 25781 and 50508 die at this floor; further "
            "verification only buys the next ln2/ln3 convergent"
        )
        next_floor = None
    return {
        "current_floor": current,
        "kind": kind,
        "detail": detail,
        "next_useful_floor": next_floor,
        "n_max_parity_25781": need_25781,
        "n_max_parity_50508": need_50508,
        "runpack_does_not_move_25781": (
            spots[25781]["n_max_runpack_6_5"] > PUBLISHED_FLOOR
        ),
    }


def render_markdown(payload: dict[str, Any]) -> str:
    table = payload["sensitivity"]
    lines = [
        "# Juggler verified-descent-floor sensitivity",
        "",
        "Status: **COMPUTATIONALLY VERIFIED** for the sensitivity "
        "table (implemented finance functions). The period bound is "
        "a Theorem 4.6 instance, not a new inequality and not a halt "
        "theorem.",
        "",
        "## Metadata",
        "",
        f"- architecture: `{table['architecture']}`",
        f"- baseline prefix: `{table['baseline_prefix']}`",
        f"- published floor: `{table['published_floor']}`",
        f"- L table: `1..{table['l_max']}`",
        f"- bit cap: `{table['bit_cap']}`",
        f"- classification: `{payload['decision']['classification']}`",
        "",
        payload["decision"]["reason"],
        "",
        "## Spotlight n_max (implemented, padded)",
        "",
    ]
    for row in table["spotlight"]:
        lines.append(
            f"- L=`{row['L']}` parity 6/5=`{row['n_max_parity_6_5']}` "
            f"parity 1=`{row['n_max_parity_1']}` "
            f"runpack 6/5=`{row['n_max_runpack_6_5']}` "
            f"crude 6/5=`{row['n_max_crude_6_5']}`"
        )
    lines.extend(["", "## Sensitivity table (parity 6/5 is the theorem layer)", ""])
    lines.append(
        "| N0 | L_max parity 6/5 | gain | survivors | "
        "L_max runpack | L_max parity 1 | est. time |"
    )
    lines.append("| ---: | ---: | ---: | ---: | ---: | ---: | ---: |")
    for row in table["rows"]:
        p = row["parity_6/5"]
        r = row["runpack_6/5"]
        one = row["parity_1"]
        lines.append(
            f"| {row['floor']} | {p['L_max']} | {p['gain_over_25780']} | "
            f"{p['survivor_count']} | {r['L_max']} | {one['L_max']} | "
            f"{row['cost']['estimated_hms']} |"
        )
    bound = payload.get("period_bound")
    if bound:
        lines.extend(
            [
                "",
                "## Recomputed period bound",
                "",
                f"- floor: `{bound['floor']}`",
                f"- statement: {bound['statement']}",
                f"- first survivor: `{bound['first_survivor']}`",
                f"- parity leftovers through L={table['l_max']}: "
                f"`{bound['parity_survivors']}`",
            ]
        )
    cert = payload.get("certificate")
    if cert:
        lines.extend(
            [
                "",
                "## Verification certificate",
                "",
                f"- N0: `{cert['N0']}`",
                f"- verified: `{cert['verified']}`",
                f"- odds walked: `{cert['odds_walked']}`",
                f"- total first-passage steps: `{cert['total_first_passage_steps']}`",
                f"- max stopping time: `{cert['max_stopping_time']}` "
                f"at `{cert['hardest_seed']}`",
                f"- max bits: `{cert['max_bits']}` at `{cert['max_bits_seed']}`",
                f"- bit cap: `{cert['bit_cap']}`",
                f"- git: `{cert['git_commit']}`",
                f"- sha256 chunks: `{cert['sha256_chunks']}`",
            ]
        )
    neck = payload.get("bottleneck")
    if neck:
        lines.extend(
            [
                "",
                "## Bottleneck",
                "",
                f"- kind: `{neck['kind']}`",
                f"- {neck['detail']}",
            ]
        )
    rec = payload["decision"].get("recommendation")
    if rec:
        lines.extend(["", "## Recommendation", "", rec, ""])
    return "\n".join(lines) + "\n"


def classify(
    table: dict[str, Any],
    certificate: dict[str, Any] | None,
) -> dict[str, Any]:
    cheapest = table.get("cheapest_floor_with_gain")
    if cheapest is None:
        return {
            "classification": "DESCENT_FLOOR_PARK",
            "reason": (
                "no hypothetical floor in range raises the Theorem 4.6 "
                "cutoff; further verification is not a leftover-killer"
            ),
            "recommendation": "STOP COMPUTING — IMPROVE THE MATHEMATICS",
        }
    if certificate is None or not certificate.get("verified"):
        return {
            "classification": "DESCENT_FLOOR_GREEN",
            "reason": (
                f"parity 6/5 jumps from {BASELINE_PREFIX} to "
                f"{cheapest['L_max']} at N0={cheapest['floor']}; "
                "the cheapest gain is computational, not a new inequality"
            ),
            "recommendation": "COMPUTE FURTHER",
        }
    neck = bottleneck_note(certificate)
    if neck["kind"] == "computation" and neck["next_useful_floor"]:
        ratio = neck["next_useful_floor"] / max(certificate["N0"], 1)
        if ratio >= 5.0:
            return {
                "classification": "DESCENT_FLOOR_PARK",
                "reason": (
                    f"verified N0={certificate['N0']} bought L*="
                    f"{cheapest['L_max']}; next useful floor "
                    f"{neck['next_useful_floor']} is "
                    f"{ratio:.1f}× larger, so the marginal theorem "
                    "gain is a later convergent, not more of this run"
                ),
                "recommendation": "STOP COMPUTING — IMPROVE THE MATHEMATICS",
            }
        return {
            "classification": "DESCENT_FLOOR_GREEN",
            "reason": (
                f"verified N0={certificate['N0']}; next useful floor "
                f"{neck['next_useful_floor']} is still cheap relative "
                "to the last jump"
            ),
            "recommendation": "COMPUTE FURTHER",
        }
    return {
        "classification": "DESCENT_FLOOR_PARK",
        "reason": neck["detail"],
        "recommendation": "STOP COMPUTING — IMPROVE THE MATHEMATICS",
    }


def probe_payload(
    *,
    floors: tuple[int, ...] = HYPOTHETICAL_FLOORS,
    l_max: int = L_MAX_SENSITIVITY,
    verify_n0: int | None = None,
    verify: bool = False,
) -> dict[str, Any]:
    table = sensitivity_table(floors, l_max=l_max)
    certificate = None
    if verify:
        target = verify_n0
        if target is None:
            cheapest = table["cheapest_floor_with_gain"]
            target = cheapest["floor"] if cheapest else None
        if target is not None:
            certificate = verify_floor_certified(target)
    period = None
    if certificate is not None and certificate["verified"]:
        period = recompute_period_bound(certificate["N0"], l_max=l_max)
    neck = bottleneck_note(certificate)
    decision = classify(table, certificate)
    return {
        "sensitivity": table,
        "certificate": certificate,
        "period_bound": period,
        "bottleneck": neck,
        "decision": decision,
        "smoke_floor": verify_floor(200, progress=False, workers=1),
        "git": git_commit(),
    }


def write_artifacts(payload: dict[str, Any] | None = None) -> dict[str, Any]:
    data = payload if payload is not None else probe_payload()
    SENS_DIR.mkdir(parents=True, exist_ok=True)
    (SENS_DIR / "summary.json").write_text(
        json.dumps(data, indent=2) + "\n", encoding="utf-8"
    )
    (SENS_DIR / "sensitivity.json").write_text(
        json.dumps(data["sensitivity"], indent=2) + "\n", encoding="utf-8"
    )
    md = render_markdown(data)
    (SENS_DIR / "summary.md").write_text(md, encoding="utf-8")
    doc = DOCS_RESEARCH / "juggler_descent_floor.md"
    js = doc.with_suffix(".json")
    doc.write_text(md, encoding="utf-8")
    js.write_text(json.dumps(data, indent=2) + "\n", encoding="utf-8")
    return data


def main() -> None:
    verify = os.environ.get("JUGGLER_VERIFY_FLOOR")
    target = os.environ.get("JUGGLER_VERIFY_N0")
    payload = probe_payload(
        verify=bool(verify),
        verify_n0=int(target) if target else None,
    )
    write_artifacts(payload)
    print(payload["decision"]["classification"])
    print(payload["decision"]["reason"])
    print(payload["decision"]["recommendation"])
    cheap = payload["sensitivity"]["cheapest_floor_with_gain"]
    if cheap:
        print(f"cheapest gain N0={cheap['floor']} L_max={cheap['L_max']}")


if __name__ == "__main__":
    main()
