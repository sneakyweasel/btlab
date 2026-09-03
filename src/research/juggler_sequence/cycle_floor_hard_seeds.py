"""Exact first-passage of bit-capped Juggler hard seeds.

Optional gmpy2 is used only as a faster exact mpz isqrt. The
iterate, parity, and success test remain integer. Not a halt
theorem.
"""

from __future__ import annotations

import json
import time
from math import isqrt
from pathlib import Path
from typing import Any

from research.juggler_sequence.cycle_finance import (
    BIT_CAP,
    STEP_CAP,
    git_commit,
    sha256_int_list,
)
from research.juggler_sequence.cycle_floor_sensitivity import VERIFY_DIR

try:
    import gmpy2

    def _walk_body(n: int, bit_cap: int, step_cap: int, progress_every: int):
        x = gmpy2.mpz(n)
        steps = 0
        max_bits = 0
        while x >= n:
            if x % 2 == 0:
                x = gmpy2.isqrt(x)
            else:
                x = gmpy2.isqrt(x * x * x)
            steps += 1
            bits = int(x.bit_length())
            if bits > max_bits:
                max_bits = bits
                if progress_every:
                    print(f"walk n={n} steps={steps} bits={bits}", flush=True)
            if steps > step_cap:
                return False, "step_cap", steps, max_bits, None
            if bits > bit_cap:
                return False, "bit_cap", steps, max_bits, None
        return True, "descended", steps, max_bits, int(x)

    ARITH = "gmpy2-mpz-isqrt"
except ImportError:  # pragma: no cover

    def _walk_body(n: int, bit_cap: int, step_cap: int, progress_every: int):
        x = n
        steps = 0
        max_bits = 0
        while x >= n:
            x = isqrt(x) if x % 2 == 0 else isqrt(x * x * x)
            steps += 1
            bits = x.bit_length()
            if bits > max_bits:
                max_bits = bits
                if progress_every:
                    print(f"walk n={n} steps={steps} bits={bits}", flush=True)
            if steps > step_cap:
                return False, "step_cap", steps, max_bits, None
            if bits > bit_cap:
                return False, "bit_cap", steps, max_bits, None
        return True, "descended", steps, max_bits, int(x)

    ARITH = "python-int-isqrt"


def walk_until_descent(
    n: int,
    *,
    bit_cap: int = BIT_CAP,
    step_cap: int = STEP_CAP,
    progress_every: int = 1,
) -> dict[str, Any]:
    """Exact first passage of n to a value strictly below n."""

    if n < 2:
        raise ValueError("n must be at least 2")
    started = time.perf_counter()
    ok, reason, steps, max_bits, landing = _walk_body(
        n, bit_cap, step_cap, progress_every
    )
    payload = {
        "n": n,
        "ok": ok,
        "reason": reason,
        "steps": steps,
        "max_bits": max_bits,
        "bit_cap": bit_cap,
        "arithmetic": ARITH,
        "exact_integer": True,
        "floating_point_used": False,
        "elapsed_s": time.perf_counter() - started,
    }
    if landing is not None:
        payload["landing"] = landing
    return payload


def patch_chunks_with_resolved_seeds(
    out_dir: Path,
    resolved: list[dict[str, Any]],
) -> dict[str, Any]:
    """Remove resolved seeds from chunk bit_failures and rebuild the cert."""

    by_n = {row["n"]: row for row in resolved}
    chunks_dir = out_dir / "chunks"
    records: list[dict[str, Any]] = []
    unresolved: list[int] = []
    for path in sorted(chunks_dir.glob("*.json")):
        row = json.loads(path.read_text(encoding="utf-8"))
        kept: list[int] = []
        for seed in row.get("bit_failures", []):
            hit = by_n.get(seed)
            if hit is None:
                kept.append(seed)
                unresolved.append(seed)
                continue
            if not hit["ok"]:
                kept.append(seed)
                unresolved.append(seed)
                continue
            if hit["max_bits"] > row.get("max_bits", 0):
                row["max_bits"] = hit["max_bits"]
                row["max_bits_seed"] = seed
            if hit["steps"] > row.get("max_steps", 0):
                row["max_steps"] = hit["steps"]
                row["hardest_seed"] = seed
            row["total_steps"] = row.get("total_steps", 0) + hit["steps"]
            row["bit_cap"] = max(row.get("bit_cap", 0), hit["bit_cap"])
        row["bit_failures"] = kept
        path.write_text(json.dumps(row, indent=2) + "\n", encoding="utf-8")
        records.append(row)
    records.sort(key=lambda row: row["start"])
    existing_cert = out_dir / "certificate.json"
    inherited_n_from = 2
    if existing_cert.is_file():
        inherited_n_from = int(
            json.loads(existing_cert.read_text(encoding="utf-8")).get("n_from", 2)
        )
    step_failures = [n for row in records for n in row.get("step_failures", [])]
    bit_failures = [n for row in records for n in row.get("bit_failures", [])]
    other_failures = [n for row in records for n in row.get("other_failures", [])]
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
    import hashlib

    chunk_blob = json.dumps(records, separators=(",", ":")).encode("ascii")
    n_top = max(row["stop"] for row in records)
    certificate = {
        "schema": "juggler-descent-floor-v1",
        "N0": n_top,
        "n_from": inherited_n_from,
        "starting_values": n_top,
        "odds_walked": sum(row.get("odds_walked", 0) for row in records),
        "total_first_passage_steps": sum(row.get("total_steps", 0) for row in records),
        "max_stopping_time": max_steps,
        "hardest_seed": hardest,
        "max_bits": max_bits,
        "max_bits_seed": max_bits_seed,
        "bit_cap": max(row.get("bit_cap", 0) for row in records),
        "step_cap": STEP_CAP,
        "verified": not failures,
        "step_failures": step_failures,
        "bit_failures": bit_failures,
        "other_failures": other_failures,
        "hard_seed_resolutions": resolved,
        "exact_integer": True,
        "floating_point_used_for_certification": False,
        "implementation": (
            "research.juggler_sequence.cycle_floor_sensitivity.verify_floor_certified"
            "+cycle_floor_hard_seeds.walk_until_descent"
        ),
        "git_commit": git_commit(),
        "sha256_chunks": hashlib.sha256(chunk_blob).hexdigest(),
        "sha256_resolved_seeds": sha256_int_list(sorted(by_n)),
        "chunk_count": len(records),
        "unresolved": unresolved,
        "halt_theorem": False,
        "no_cycle_all_lengths": False,
    }
    (out_dir / "certificate.json").write_text(
        json.dumps(certificate, indent=2) + "\n", encoding="utf-8"
    )
    return certificate


def resolve_listed_seeds(
    seeds: list[int],
    *,
    bit_cap: int = BIT_CAP,
    out_dir: Path | None = None,
) -> dict[str, Any]:
    resolved = [walk_until_descent(n, bit_cap=bit_cap) for n in seeds]
    if out_dir is not None:
        (out_dir / "hard_seeds.json").write_text(
            json.dumps(resolved, indent=2) + "\n", encoding="utf-8"
        )
        if all(row["ok"] for row in resolved):
            return patch_chunks_with_resolved_seeds(out_dir, resolved)
    return {
        "resolved": resolved,
        "all_ok": all(row["ok"] for row in resolved),
        "arithmetic": ARITH,
    }
