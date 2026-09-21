"""The 3x-1 descent floor on the GPU: build the CUDA verifier, calibrate it against the CPU
certificate, and sweep new ranges in chunks.

The kernel is ``data/research/juggler/negative_floor_3x1/verify_3x1_gpu.cu`` (built by
``build_gpu.bat`` beside it, with the CUDA toolkit on PATH and the MSVC Build Tools that built
the atlas). Its semantics are the C verifiers': every odd start ``y0 >= 3`` is iterated until
an iterate drops below ``y0``, returns to ``y0`` (a cycle), or lands on an element of the three
known cycles; the mod-``2^24`` prefix sieve skips the classes that a contracting prefix drops.
The iteration is Barina's domain switch, which on this side is the run identity
``g^a(y) - 1 = (3/2)^a (y - 1)``: one multiplication per odd run, one shift per even run.

Two things differ from the CPU walkers, both recorded: the peak is the exact trajectory peak
(the jump walker saw landings only), and ``max_steps`` is the plain walker's exact count (the
jump walker's is granular to sixteen). :func:`walk` is the same procedure in Python on big
integers, for the tests and for the rare start whose 128-bit state would overflow.

``python -m research.juggler_sequence.negative_floor_gpu calibrate`` reruns the calibration
set (the known-bad input, [3, 2000), [3, 2^35), [3, 2^40), [2^40, 2^44)), compares it with
``chunks.json`` and ``runs.json``, and writes ``gpu_calibration/summary.json`` and
``docs/research/juggler_negative_floor_gpu.md``. ``sweep LO_LOG2 HI_LOG2`` runs a new range
chunk by chunk into ``gpu_chunks/`` with a run record in ``gpu_runs.json``.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import math
import os
import subprocess
import sys
import time
from dataclasses import dataclass
from pathlib import Path
from typing import Any

from research.juggler_sequence.lean_paths import DATA_ROOT, DOCS_RESEARCH, REPO_ROOT

CERT_DIR = DATA_ROOT / "negative_floor_3x1"
CAL_DIR = CERT_DIR / "gpu_calibration"
CHUNK_DIR = CERT_DIR / "gpu_chunks"
SOURCE = CERT_DIR / "verify_3x1_gpu.cu"
BUILD_BAT = CERT_DIR / "build_gpu.bat"
BINARY = REPO_ROOT / ".build" / "negative_floor_gpu" / "verify_3x1_gpu.exe"
SUMMARY = CAL_DIR / "summary.json"
GPU_RUNS = CERT_DIR / "gpu_runs.json"
DOC = DOCS_RESEARCH / "juggler_negative_floor_gpu.md"
CHUNKS_JSON = CERT_DIR / "chunks.json"
RUNS_JSON = CERT_DIR / "runs.json"

CYCLE17 = (17, 25, 37, 55, 82, 41, 61, 91, 136, 68, 34)
KNOWN = (1, 5, 7, 10) + CYCLE17
SIEVE_K = 24
A076227_24 = 286581  #: prefix-noncontracting classes mod 2^24
STEP_CAP = 40000
LOG2, LOG3 = math.log(2), math.log(3)

#: the calibration set: name, lo, hi, options
CALIBRATION = (
    ("known_bad_3_2000", 3, 2000, {"forget_17": True}),
    ("3_2000", 3, 2000, {}),
    ("3_2p35", 3, 2 ** 35, {}),
    ("3_2p40", 3, 2 ** 40, {}),
    ("2p40_2p44", 2 ** 40, 2 ** 44, {}),
)


# ---------------------------------------------------------------- the map, in Python
def g(y: int) -> int:
    return y // 2 if y % 2 == 0 else (3 * y - 1) // 2


@dataclass(frozen=True)
class Walk:
    status: str  # drop | cycle | stepcap
    steps: int
    peak: int


def walk(y0: int, known: tuple[int, ...] = KNOWN, cap: int = STEP_CAP) -> Walk:
    """The kernel's procedure on big integers: odd runs by the run identity, even runs at
    once, the first halving below ``y0`` found exactly, the known-cycle test at the end of an
    even run. Exact for every size; used for the tests and for overflow starts."""
    if y0 < 3 or y0 % 2 == 0:
        raise ValueError("starts are odd and at least 3")
    y, steps, peak = y0, 0, y0
    while True:
        u = y - 1
        a = (u & -u).bit_length() - 1
        y = (u >> a) * 3 ** a + 1
        steps += a
        if y > peak:
            peak = y
        b = (y & -y).bit_length() - 1
        yb = y >> b
        if yb < y0:
            t = 1
            while t < b and not (y >> t) < y0:
                t += 1
            return Walk("drop", steps + t, peak)
        y = yb
        steps += b
        if y == y0:
            return Walk("cycle", steps, peak)
        if y <= 136 and y in known:
            return Walk("drop", steps, peak)
        if steps > cap:
            return Walk("stepcap", steps, peak)


def prefix_noncontracting(r: int, K: int = SIEVE_K) -> bool:
    """Does the K-step parity word of the class ``r mod 2^K`` keep ``3^a >= 2^j`` at every
    prefix? Only these classes need walking: a contracting prefix drops every member."""
    mask = (1 << K) - 1
    v, a, p3 = r, 0, 1
    for j in range(1, K + 1):
        if v & 1:
            v = ((3 * v - 1) >> 1) & mask
            a += 1
            p3 *= 3
        else:
            v >>= 1
        if p3 < (1 << j):
            return False
    return True


def survivors_below(limit: int, K: int = SIEVE_K) -> list[int]:
    """The odd starts in [3, limit) the sieve walks, for ``limit <= 2^K``."""
    if limit > (1 << K):
        raise ValueError("limit must be at most 2^K")
    return [y for y in range(3, limit, 2) if prefix_noncontracting(y, K)]


def odd_count(lo: int, hi: int) -> int:
    lo = max(lo, 3)
    first = lo | 1
    return 0 if first >= hi else (hi - first + 1) // 2


# ---------------------------------------------------------------- the binary
def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def binary_is_current() -> bool:
    return BINARY.is_file() and BINARY.stat().st_mtime >= SOURCE.stat().st_mtime


def build(force: bool = False) -> Path:
    """Build the verifier with ``build_gpu.bat`` unless the binary is newer than the source."""
    if binary_is_current() and not force:
        return BINARY
    if os.name != "nt":
        raise RuntimeError("build_gpu.bat drives nvcc through the MSVC Build Tools; build on Windows")
    run = subprocess.run(["cmd", "/c", str(BUILD_BAT)], capture_output=True, text=True, errors="replace")
    if run.returncode or not BINARY.is_file():
        raise RuntimeError(f"build failed (exit {run.returncode}):\n{run.stdout}\n{run.stderr}")
    return BINARY


def gpu_available() -> bool:
    """A built (or buildable) verifier and a visible GPU."""
    try:
        build()
    except Exception:
        return False
    try:
        return subprocess.run(["nvidia-smi", "-L"], capture_output=True, text=True, timeout=20).returncode == 0
    except Exception:
        return False


def gpu_name() -> str:
    try:
        out = subprocess.run(["nvidia-smi", "--query-gpu=name,driver_version", "--format=csv,noheader"],
                             capture_output=True, text=True, timeout=20).stdout.strip()
        return out.splitlines()[0] if out else "unknown"
    except Exception:
        return "unknown"


def nvcc_version() -> str:
    try:
        out = subprocess.run(["nvcc", "--version"], capture_output=True, text=True, timeout=20).stdout
        return next((ln.strip() for ln in out.splitlines() if "release" in ln), "unknown")
    except Exception:
        return "unknown"


def run(lo: int, hi: int, json_path: Path | None = None, *, sieve_K: int = SIEVE_K, cap: int = STEP_CAP,
        forget_17: bool = False, slabs: int = 1024) -> dict[str, Any]:
    """Run the verifier on [lo, hi) and return its JSON report (plus the printed lines)."""
    binary = build()
    target = json_path or (CAL_DIR / f"tmp_{lo}_{hi}.json")
    target.parent.mkdir(parents=True, exist_ok=True)
    cmd = [str(binary), str(lo), str(hi), "--sieve", str(sieve_K), "--cap", str(cap), "--slabs", str(slabs),
           "--json", str(target)]
    if forget_17:
        cmd.append("--forget-17")
    proc = subprocess.run(cmd, capture_output=True, text=True, errors="replace")
    if not target.is_file():
        raise RuntimeError(f"verifier wrote no report (exit {proc.returncode}):\n{proc.stdout}\n{proc.stderr}")
    report = json.loads(target.read_text(encoding="utf-8"))
    report["exit_code"] = proc.returncode
    report["printed"] = [ln for ln in proc.stdout.splitlines() if ln.startswith(("NEW CYCLE", "STEPCAP", "OVERFLOW", "WARNING"))]
    if json_path is None:
        target.unlink()
    else:
        target.write_text(json.dumps(report, indent=1) + "\n", encoding="utf-8")
    return report


def peak_of(report: dict[str, Any]) -> int:
    return (int(report["peak_hi"]) << 64) + int(report["peak_lo"])


# ---------------------------------------------------------------- calibration
def compare_with_certificate(reports: dict[str, dict[str, Any]]) -> dict[str, Any]:
    """The GPU reports against the CPU certificate, exactly where the semantics coincide."""
    chunks = json.loads(CHUNKS_JSON.read_text(encoding="utf-8"))
    runs = json.loads(RUNS_JSON.read_text(encoding="utf-8"))[0]
    low = [c for c in chunks if c["chunk"] <= 15]
    c0 = chunks[0]
    r35, r40, r44 = reports["3_2p35"], reports["3_2p40"], reports["2p40_2p44"]
    kb, r2000 = reports["known_bad_3_2000"], reports["3_2000"]
    out = {
        "sieve_classes_A076227_24": r44["classes"] == A076227_24,
        "known_bad_forgotten_17_reported": kb["new_cycles"] == 1 and kb["new_cycle_starts"] == [17] and kb["exit_code"] == 1,
        "3_2000_clean": r2000["fails"] == 0 and r2000["new_cycles"] == 0 and r2000["exit_code"] == 0,
        "3_2p35": {"max_steps": (r35["max_steps"], c0["max_steps"]), "peak": (peak_of(r35), c0["peak"]),
                   "odd_starts": (r35["odd_starts"], c0["odd_starts"]),
                   "agree": r35["max_steps"] == c0["max_steps"] and peak_of(r35) == c0["peak"] and r35["fails"] == 0},
        "3_2p40": {"max_steps": (r40["max_steps"], max(c["max_steps"] for c in low)),
                   "peak": (peak_of(r40), max(c["peak"] for c in low)),
                   "odd_starts": (r40["odd_starts"], sum(c["odd_starts"] for c in low)),
                   "agree": r40["max_steps"] == max(c["max_steps"] for c in low)
                   and peak_of(r40) == max(c["peak"] for c in low) and r40["fails"] == 0},
        "2p40_2p44": {"odd_starts": (r44["odd_starts"], runs["odd_starts"]),
                      "max_steps": (r44["max_steps"], runs["max_steps"]),
                      "peak": (peak_of(r44), runs["max_landing_peak"]),
                      "fails": (r44["fails"], runs["fails"]), "new_cycles": (r44["new_cycles"], runs["new_cycles"]),
                      "agree": r44["odd_starts"] == runs["odd_starts"] and r44["fails"] == 0 == runs["fails"]
                      and r44["new_cycles"] == 0 == runs["new_cycles"] and r44["overflows"] == 0
                      and r44["max_steps"] <= runs["max_steps"]},
        "peak_2p40_2p44_equal_to_landing_peak": peak_of(r44) == runs["max_landing_peak"],
        "odd_start_convention": "the CPU printed (limit - lo) // 2 per chunk, one below the count of odd "
                                "integers when lo is odd; the GPU counts them exactly, and the seven gap "
                                "starts the CPU verified separately are inside the GPU's ranges",
        "max_steps_convention": "the jump walker counts sixteen per jump and checks the drop at landings only, "
                                "so its count is at least the exact one and, when a trajectory dips below the "
                                "start inside a jump and recovers, can exceed it by more than a jump (72 steps in "
                                "one spot window); its 704 against the GPU's exact 703 on [2^40, 2^44). The peaks "
                                "have no forced relation for the same reason; they were equal wherever compared",
        "timing": {"gpu_seconds_2p40_2p44": r44["seconds"], "cpu_wall_seconds": runs["wall_seconds"],
                   "cpu_core_seconds": runs["sum_chunk_seconds"],
                   "speedup_vs_24_threads": runs["wall_seconds"] / r44["seconds"],
                   "speedup_vs_one_core": runs["sum_chunk_seconds"] / r44["seconds"]},
    }
    out["all_agree"] = bool(out["sieve_classes_A076227_24"] and out["known_bad_forgotten_17_reported"]
                            and out["3_2000_clean"] and out["3_2p35"]["agree"] and out["3_2p40"]["agree"]
                            and out["2p40_2p44"]["agree"])
    return out


def projections(rate: float, exponents: tuple[int, ...] = (48, 49, 50, 51, 52, 56, 58, 60)) -> list[dict[str, Any]]:
    """Hours from 2^44 to 2^e at the calibrated rate, odd starts per second; the rate is that
    of [2^40, 2^44) and trajectories lengthen slowly with size, so these are floors."""
    return [{"floor": f"2^{e}", "hours": ((2 ** e - 2 ** 44) / 2) / rate / 3600} for e in exponents]


def calibrate(write: bool = True) -> dict[str, Any]:
    CAL_DIR.mkdir(parents=True, exist_ok=True)
    reports = {}
    for name, lo, hi, opts in CALIBRATION:
        reports[name] = run(lo, hi, CAL_DIR / f"gpu_{name}.json", **opts)
    comparison = compare_with_certificate(reports)
    r44 = reports["2p40_2p44"]
    rate = r44["odd_starts"] / r44["seconds"]
    summary = {
        "verifier": SOURCE.name, "source_sha256": sha256(SOURCE), "binary_sha256": sha256(BINARY),
        "gpu": gpu_name(), "toolkit": nvcc_version(), "host": "laboratory machine, Windows 11",
        "date": time.strftime("%Y-%m-%d"),
        "sieve": {"K": SIEVE_K, "classes": r44["classes"]},
        "reports": {name: {k: v for k, v in rep.items() if k != "printed"} | {"printed": rep["printed"]}
                    for name, rep in reports.items()},
        "comparison": comparison,
        "rate_odd_starts_per_second": rate,
        "rate_walked_starts_per_second": r44["walked"] / r44["seconds"],
        "projections_hours_from_2p44": projections(rate),
    }
    if write:
        SUMMARY.write_text(json.dumps(summary, indent=1) + "\n", encoding="utf-8")
        DOC.write_text(render_markdown(summary), encoding="utf-8")
    return summary


def render_markdown(s: dict[str, Any]) -> str:
    c = s["comparison"]
    lines = [
        "# The 3x-1 descent floor on the GPU: calibration against the certificate",
        "",
        "Generated by `python -m research.juggler_sequence.negative_floor_gpu calibrate`; do not edit.",
        "",
        f"Verifier `{s['verifier']}` (sha256 `{s['source_sha256'][:16]}`), built with {s['toolkit']} for "
        f"{s['gpu']}; sieve mod 2^{s['sieve']['K']} with {s['sieve']['classes']} classes "
        f"(A076227(24) = {A076227_24}: {c['sieve_classes_A076227_24']}). Date {s['date']}.",
        "",
        "| range | GPU max_steps | CPU max_steps | GPU peak | CPU peak | GPU odd starts | CPU odd starts | agree |",
        "|---|---|---|---|---|---|---|---|",
    ]
    for key, label in (("3_2p35", "[3, 2^35) (chunk 0)"), ("3_2p40", "[3, 2^40) (chunks 0-15)"),
                       ("2p40_2p44", "[2^40, 2^44) (runs.json)")):
        r = c[key]
        lines.append(f"| {label} | {r['max_steps'][0]} | {r['max_steps'][1]} | {r['peak'][0]} | {r['peak'][1]} | "
                     f"{r['odd_starts'][0]} | {r['odd_starts'][1]} | {r['agree']} |")
    t = c["timing"]
    lines += [
        "",
        f"Known-bad input: with the 17-cycle forgotten the kernel reports `NEW CYCLE at 17` on [3, 2000): "
        f"{c['known_bad_forgotten_17_reported']}. Clean run on [3, 2000): {c['3_2000_clean']}. "
        f"Peak on [2^40, 2^44) equal to the CPU landing peak: {c['peak_2p40_2p44_equal_to_landing_peak']}.",
        "",
        f"Conventions: {c['odd_start_convention']}. {c['max_steps_convention']}.",
        "",
        f"Timing on [2^40, 2^44): GPU {t['gpu_seconds_2p40_2p44']:.1f} s against the CPU's {t['cpu_wall_seconds']} s "
        f"wall on 24 threads ({t['speedup_vs_24_threads']:.0f} times) and {t['cpu_core_seconds']} core-seconds "
        f"({t['speedup_vs_one_core']:.0f} times one core). Rate {s['rate_odd_starts_per_second']:.3e} odd starts per "
        f"second, {s['rate_walked_starts_per_second']:.3e} walked.",
        "",
        "| floor | hours from 2^44 at this rate |", "|---|---|",
    ]
    for p in s["projections_hours_from_2p44"]:
        lines.append(f"| {p['floor']} | {p['hours']:.2f} |")
    lines += ["", f"All calibration checks agree: **{c['all_agree']}**.", ""]
    return "\n".join(lines)


# ---------------------------------------------------------------- a sweep of a new range
def sweep(lo_log2: int, hi_log2: int, chunk_log2: int = 48, out_dir: Path = CHUNK_DIR,
          runs_path: Path = GPU_RUNS) -> dict[str, Any]:
    """Verify [2^lo_log2, 2^hi_log2) in chunks of 2^chunk_log2, one JSON report each, with the
    overflow starts re-walked wide in Python; append a run record with the coverage check."""
    lo, hi = 2 ** lo_log2, 2 ** hi_log2
    span = 2 ** min(chunk_log2, hi_log2)
    out_dir.mkdir(parents=True, exist_ok=True)
    binary = build()
    started = time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())
    t0 = time.time()
    chunks, total = [], {"odd_starts": 0, "walked": 0, "fails": 0, "new_cycles": 0, "overflows": 0, "max_steps": 0,
                         "peak": 0, "seconds": 0.0}
    wide: list[dict[str, Any]] = []
    i = 0
    a = lo
    while a < hi:
        b = min(a + span, hi)
        rep = run(a, b, out_dir / f"gpu_{lo_log2}_{hi_log2}_{i:04d}.json")
        for y0 in rep.get("overflow_starts", []):
            w = walk(y0)
            wide.append({"start": y0, "status": w.status, "steps": w.steps, "peak": str(w.peak)})
            if w.status != "drop":
                total["fails"] += 1
            total["max_steps"] = max(total["max_steps"], w.steps)
            total["peak"] = max(total["peak"], w.peak)
        for k in ("odd_starts", "walked", "fails", "new_cycles", "overflows"):
            total[k] += rep[k]
        total["max_steps"] = max(total["max_steps"], rep["max_steps"])
        total["peak"] = max(total["peak"], peak_of(rep))
        total["seconds"] += rep["seconds"]
        chunks.append({"chunk": i, "lo": a, "hi": b, "odd_starts": rep["odd_starts"], "fails": rep["fails"],
                       "new_cycles": rep["new_cycles"], "overflows": rep["overflows"], "max_steps": rep["max_steps"],
                       "peak": str(peak_of(rep)), "seconds": rep["seconds"], "exit_code": rep["exit_code"]})
        print(f"chunk {i} [{a},{b}) fails={rep['fails']} new_cycles={rep['new_cycles']} overflows={rep['overflows']} "
              f"max_steps={rep['max_steps']} secs={rep['seconds']:.1f}", flush=True)
        a, i = b, i + 1
    record = {
        "range": [lo, hi], "range_log2": [lo_log2, hi_log2], "chunk_log2": chunk_log2, "chunks": len(chunks),
        "verifier": SOURCE.name, "verifier_source_sha256": sha256(SOURCE), "binary_sha256": sha256(binary),
        "gpu": gpu_name(), "toolkit": nvcc_version(), "started_utc": started,
        "ended_utc": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()), "wall_seconds": round(time.time() - t0, 1),
        "sum_chunk_seconds": round(total["seconds"], 1), "odd_starts": total["odd_starts"],
        "odd_starts_expected": odd_count(lo, hi), "coverage_exact": total["odd_starts"] == odd_count(lo, hi),
        "walked": total["walked"], "fails": total["fails"], "new_cycles": total["new_cycles"],
        "overflows": total["overflows"], "overflow_rewalks": wide, "max_steps": total["max_steps"],
        "step_cap": STEP_CAP, "peak": str(total["peak"]), "peak_log2": math.log2(total["peak"]) if total["peak"] else 0,
        "clean": total["fails"] == 0 and total["new_cycles"] == 0 and total["odd_starts"] == odd_count(lo, hi)
        and all(w["status"] == "drop" for w in wide),
        "chunk_reports": chunks,
    }
    records = json.loads(runs_path.read_text(encoding="utf-8")) if runs_path.is_file() else []
    records = [r for r in records if r["range_log2"] != [lo_log2, hi_log2]] + [record]
    runs_path.write_text(json.dumps(records, indent=1) + "\n", encoding="utf-8")
    return record


# ---------------------------------------------------------------- spot checks against the CPU walker
SPOT_WINDOWS = ((2 ** 45, 2 ** 45 + 2 ** 37), (2 ** 48, 2 ** 48 + 2 ** 37), (2 ** 51 - 2 ** 37, 2 ** 51))
CPU_SPOT = CAL_DIR / "cpu_spot_2p44_2p51.json"
SPOT_OUT = CAL_DIR / "spot_checks_2p44_2p51.json"


def spot_check(cpu_json: Path = CPU_SPOT, out: Path = SPOT_OUT) -> dict[str, Any]:
    """The GPU against the archived CPU jump walker on the windows the CPU has already run
    (``cpu_json`` holds its reports; ``negative_floor_3x1.run_verifier`` produces them under
    WSL). Exact where the semantics coincide: walked and skipped counts (same sieve), failures
    and cycles; the CPU's step count is granular to sixteen and its peak is over landings."""
    cpu = json.loads(cpu_json.read_text(encoding="utf-8"))
    windows = []
    for c in cpu["windows"]:
        lo, hi = c["lo"], c["hi"]
        rep = run(lo, hi)
        cpu_odd = c["walked"] + c["skipped"]
        # Same sieve, so the walked and skipped counts must match exactly; no failure, cycle or
        # overflow on either side. The CPU's step count is at least the exact one (it checks the
        # drop at jump landings only, and a trajectory that dips below the start inside a jump and
        # recovers is walked on to a later landing), so it can exceed the GPU's by more than a
        # jump; the peaks have no forced relation for the same reason and are recorded, not
        # required (they were equal in every window and on [2^40, 2^44)).
        agree = (rep["walked"] == c["walked"] and rep["odd_starts"] == cpu_odd and rep["fails"] == 0 == c["fails"]
                 and rep["new_cycles"] == 0 == c["new_cycles"] and rep["overflows"] == 0
                 and rep["max_steps"] <= c["max_steps"])
        windows.append({"lo": lo, "hi": hi, "lo_log2": math.log2(lo), "width_log2": math.log2(hi - lo),
                        "peaks_equal": peak_of(rep) == c["peak"], "cpu_steps_minus_gpu": c["max_steps"] - rep["max_steps"],
                        "cpu": {k: c.get(k) for k in ("walked", "skipped", "fails", "new_cycles", "max_steps", "peak", "seconds")},
                        "gpu": {"walked": rep["walked"], "skipped": rep["skipped"], "odd_starts": rep["odd_starts"],
                                "fails": rep["fails"], "new_cycles": rep["new_cycles"], "overflows": rep["overflows"],
                                "max_steps": rep["max_steps"], "peak": peak_of(rep), "seconds": rep["seconds"]},
                        "agree": agree})
    result = {"cpu_verifier": cpu["verifier"], "cpu_command": cpu["command"], "gpu_verifier": SOURCE.name,
              "gpu_source_sha256": sha256(SOURCE), "date": time.strftime("%Y-%m-%d"), "windows": windows,
              "all_agree": all(w["agree"] for w in windows)}
    out.write_text(json.dumps(result, indent=1, default=str) + "\n", encoding="utf-8")
    return result


def main(argv: list[str] | None = None) -> None:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    sub = parser.add_subparsers(dest="command")
    sub.add_parser("build")
    sub.add_parser("calibrate")
    sw = sub.add_parser("sweep")
    sw.add_argument("lo_log2", type=int)
    sw.add_argument("hi_log2", type=int)
    sw.add_argument("--chunk-log2", type=int, default=48)
    sub.add_parser("spot")
    args = parser.parse_args(argv)
    if args.command == "build":
        print(build(force=True))
    elif args.command == "spot":
        res = spot_check()
        print(json.dumps({"all_agree": res["all_agree"], "windows": [(w["lo"], w["hi"], w["agree"]) for w in res["windows"]]}))
        if not res["all_agree"]:
            sys.exit(1)
    elif args.command == "sweep":
        rec = sweep(args.lo_log2, args.hi_log2, args.chunk_log2)
        print(json.dumps({k: v for k, v in rec.items() if k not in ("chunk_reports", "overflow_rewalks")}, indent=1))
    else:
        s = calibrate()
        c = s["comparison"]
        print(f"calibration {'agrees' if c['all_agree'] else 'DISAGREES'}: [2^40,2^44) in "
              f"{c['timing']['gpu_seconds_2p40_2p44']:.1f} s, {c['timing']['speedup_vs_24_threads']:.0f}x the CPU run; "
              f"wrote {SUMMARY} and {DOC}")
        if not c["all_agree"]:
            sys.exit(1)


if __name__ == "__main__":
    main()
