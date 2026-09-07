"""Optional native census binary. Python remains the exact reference."""

from __future__ import annotations

from research.juggler_sequence.lean_paths import (
    REPO_ROOT,
)

import os
import shutil
import subprocess
from pathlib import Path

BIN_NAMES = ("juggler-atlas-census.exe", "juggler-atlas-census")


def find_binary() -> Path | None:
    env = os.environ.get("JUGGLER_ATLAS_BIN")
    if env:
        path = Path(env)
        return path if path.is_file() else None
    for name in BIN_NAMES:
        found = shutil.which(name)
        if found:
            return Path(found)
    build = REPO_ROOT / "atlas" / "build"
    for name in BIN_NAMES:
        candidate = build / name
        if candidate.is_file():
            return candidate
        for nested in build.rglob(name):
            if nested.is_file():
                return nested
    return None


def run_census(
    *,
    k_max: int,
    n_max: int,
    n_begin: int = 1,
    backend: str = "cpu",
    output: Path,
    binary: Path | None = None,
) -> dict[str, str | int]:
    exe = binary or find_binary()
    if exe is None:
        raise FileNotFoundError("juggler-atlas-census is not built")
    output.parent.mkdir(parents=True, exist_ok=True)
    cmd = [
        str(exe),
        "--k-max",
        str(k_max),
        "--n-max",
        str(n_max),
        "--n-begin",
        str(n_begin),
        "--backend",
        backend,
        "--output",
        str(output),
    ]
    proc = subprocess.run(cmd, check=True, capture_output=True, text=True)
    return {
        "binary": str(exe),
        "backend": backend,
        "returncode": proc.returncode,
        "stdout": proc.stdout,
        "stderr": proc.stderr,
    }


def parse_census_tsv(path: Path) -> dict[str, object]:
    """Parse the native TSV dump into dense Python tables."""

    from research.juggler_sequence.atlas.packed import dense_index, dense_size

    k_max = 0
    n_max = 0
    n_begin = 1
    backend = "cpu"
    overflow = 0
    rows: list[tuple[int, int, int | None, int | None]] = []
    with path.open(encoding="utf-8") as fh:
        for raw in fh:
            line = raw.rstrip("\n\r")
            if not line.strip():
                continue
            if line.startswith("#"):
                body = line[1:].strip()
                if "=" in body:
                    key, val = body.split("=", 1)
                    if key == "k_max":
                        k_max = int(val)
                    elif key == "n_max":
                        n_max = int(val)
                    elif key == "n_begin":
                        n_begin = int(val)
                    elif key == "backend":
                        backend = val
                    elif key == "overflow_count":
                        overflow = int(val)
                continue
            if line.startswith("length"):
                continue
            parts = line.rstrip("\n\r").split("\t")
            if len(parts) < 2:
                continue
            length = int(parts[0])
            packed = int(parts[1])
            min_n = int(parts[2]) if len(parts) > 2 and parts[2] else None
            min_exp = int(parts[3]) if len(parts) > 3 and parts[3] else None
            rows.append((length, packed, min_n, min_exp))
    size = dense_size(k_max)
    min_n_tbl: list[int | None] = [None] * size
    min_exp_tbl: list[int | None] = [None] * size
    for length, packed, min_n, min_exp in rows:
        idx = dense_index(length, packed)
        min_n_tbl[idx] = min_n
        min_exp_tbl[idx] = min_exp
    overflow_path = path.with_name(path.name + ".overflow")
    overflow_n, truncated = parse_overflow_file(overflow_path)
    return {
        "k_max": k_max,
        "n_max": n_max,
        "n_begin": n_begin,
        "backend": backend,
        "overflow_count": overflow,
        "overflow_n": overflow_n,
        "overflow_truncated": truncated,
        "min_n": min_n_tbl,
        "min_exp": min_exp_tbl,
    }


def run_harvest(
    *,
    k_max: int,
    n_max: int,
    n_begin: int = 2,
    backend: str = "cpu",
    output: Path,
    list_cap: int = 10_000,
    binary: Path | None = None,
) -> dict[str, str | int]:
    exe = binary or find_binary()
    if exe is None:
        raise FileNotFoundError("juggler-atlas-census is not built")
    output.parent.mkdir(parents=True, exist_ok=True)
    cmd = [
        str(exe),
        "--mode",
        "harvest",
        "--k-max",
        str(k_max),
        "--n-max",
        str(n_max),
        "--n-begin",
        str(n_begin),
        "--backend",
        backend,
        "--list-cap",
        str(list_cap),
        "--output",
        str(output),
    ]
    proc = subprocess.run(cmd, check=True, capture_output=True, text=True)
    return {
        "binary": str(exe),
        "backend": backend,
        "returncode": proc.returncode,
        "stdout": proc.stdout,
        "stderr": proc.stderr,
    }


def parse_harvest_tsv(path: Path) -> dict[str, object]:
    """Parse a leftover-class harvest TSV."""

    from research.juggler_sequence.atlas.packed import dense_index, dense_size

    meta: dict[str, object] = {
        "k_max": 0,
        "n_max": 0,
        "n_begin": 2,
        "backend": "cpu",
        "count_skip": 0,
        "count_e": 0,
        "count_oe": 0,
        "count_ooee": 0,
        "count_leftover": 0,
        "count_uncapped": 0,
        "count_overflow": 0,
        "overflow_truncated": False,
        "uncapped_truncated": False,
    }
    rows: list[tuple[int, int, int, int | None]] = []
    with path.open(encoding="utf-8") as fh:
        for raw in fh:
            line = raw.rstrip("\n\r")
            if not line.strip():
                continue
            if line.startswith("#"):
                body = line[1:].strip()
                if "=" in body:
                    key, val = body.split("=", 1)
                    if key in {
                        "k_max",
                        "n_max",
                        "n_begin",
                        "count_skip",
                        "count_e",
                        "count_oe",
                        "count_ooee",
                        "count_leftover",
                        "count_uncapped",
                        "count_overflow",
                    }:
                        meta[key] = int(val)
                    elif key == "backend":
                        meta[key] = val
                    elif key in {"overflow_truncated", "uncapped_truncated"}:
                        meta[key] = val == "1"
                continue
            if line.startswith("length"):
                continue
            parts = line.split("\t")
            if len(parts) < 3:
                continue
            length = int(parts[0])
            packed = int(parts[1])
            count = int(parts[2])
            min_n = int(parts[3]) if len(parts) > 3 and parts[3] else None
            rows.append((length, packed, count, min_n))
    k_max = int(meta["k_max"])
    size = dense_size(k_max)
    hist = [0] * size
    min_n_tbl: list[int | None] = [None] * size
    for length, packed, count, min_n in rows:
        idx = dense_index(length, packed)
        hist[idx] = count
        min_n_tbl[idx] = min_n
    overflow_n, overflow_trunc = parse_overflow_file(
        path.with_name(path.name + ".overflow"),
        load_starts=int(meta["count_overflow"]) <= 10_000,
    )
    uncapped_n, uncapped_trunc = parse_overflow_file(
        path.with_name(path.name + ".uncapped"),
        load_starts=int(meta["count_uncapped"]) <= 10_000,
    )
    meta.update(
        {
            "hist": hist,
            "min_n": min_n_tbl,
            "overflow_n": overflow_n,
            "uncapped_n": uncapped_n,
            "overflow_truncated": bool(meta["overflow_truncated"]) or overflow_trunc,
            "uncapped_truncated": bool(meta["uncapped_truncated"]) or uncapped_trunc,
            "rows": rows,
        }
    )
    return meta


def parse_overflow_file(
    path: Path,
    *,
    load_starts: bool = True,
) -> tuple[list[int], bool]:
    if not path.is_file():
        return [], False
    starts: list[int] = []
    truncated = False
    with path.open(encoding="utf-8") as fh:
        for raw in fh:
            line = raw.strip()
            if not line:
                continue
            if line.startswith("#"):
                body = line[1:].strip()
                if body.startswith("overflow_truncated="):
                    truncated = body.split("=", 1)[1] == "1"
                continue
            if load_starts:
                starts.append(int(line))
            else:
                break
    return starts, truncated
