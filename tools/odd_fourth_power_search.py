"""Exact resumable search for odd non-square n with T(n) = a^4.

Standalone tool. Not a Research Engine control-layer experiment and not
a termination theorem. Iterates the output parameter a, not n. Every
comparison is an integer inequality. Empty finite ranges are evidence,
not theorems.

    a^8 <= n^3 < (a^4 + 1)^2

Per-a integer cube roots are used because m ~ a^{8/3} jumps by
~(8/3) a^{5/3} when a increases by 1, so incrementing m is not viable.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import platform
import sqlite3
import subprocess
import sys
import time
from concurrent.futures import ProcessPoolExecutor, as_completed
from dataclasses import dataclass
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Iterator

REPO_ROOT = Path(__file__).resolve().parents[1]
if str(REPO_ROOT / "src") not in sys.path:
    sys.path.insert(0, str(REPO_ROOT / "src"))

from research.juggler_sequence.odd_sharp_suffix import integer_cbrt
from research.juggler_sequence.power_algebra import is_square
from research.juggler_sequence.power_itineraries import floor_power

DEFAULT_DATA_DIR = REPO_ROOT / "data" / "research" / "juggler" / "odd_sharp_suffix"
SOFTWARE_VERSION = "0.2.2"
ALGORITHM_ALL = "odd-fourth-v1-cbrt"
ALGORITHM_ODD_A = "odd-fourth-v1-cbrt-odd-a"
PROBLEM_ID = "juggler_odd_sharp_suffix"
PARAMETER_S = 2
NEAR_MISS_CAP = 8
STALE_RUNNING_SECONDS = 3600

CLASS_EMPTY = "INTERVAL_EMPTY"
CLASS_EVEN = "EVEN_CUBE"
CLASS_ODD_SQUARE = "ODD_SQUARE"
CLASS_ODD_NON_SQUARE = "ODD_NON_SQUARE"

STATUS_PENDING = "PENDING"
STATUS_RUNNING = "RUNNING"
STATUS_COMPLETE = "COMPLETE"
STATUS_FAILED = "FAILED"
STATUS_INVALIDATED = "INVALIDATED"

MANIFEST_KEYS = (
    "search_id",
    "problem",
    "parameter_s",
    "a_start",
    "a_end",
    "status",
    "software_version",
    "git_commit",
    "machine_identifier",
    "started_at",
    "completed_at",
    "algorithm_version",
    "arithmetic_method",
    "worker_count",
    "checksum",
)

_GMPY2 = None
try:
    import gmpy2 as _gmpy2_mod

    _GMPY2 = _gmpy2_mod
except ImportError:
    pass


def arithmetic_method() -> str:
    return "gmpy2-iroot" if _GMPY2 is not None else "python-int"


def _cbrt(n: int) -> int:
    if _GMPY2 is not None:
        root, _exact = _GMPY2.iroot(n, 3)
        return int(root)
    return integer_cbrt(n)


def ceil_cbrt(n: int) -> int:
    root = _cbrt(n)
    if root * root * root < n:
        return root + 1
    return root


def utc_now() -> str:
    return datetime.now(timezone.utc).replace(microsecond=0).isoformat()


def git_commit() -> str:
    try:
        return subprocess.check_output(
            ["git", "rev-parse", "HEAD"],
            cwd=REPO_ROOT,
            stderr=subprocess.DEVNULL,
            text=True,
        ).strip()
    except (OSError, subprocess.CalledProcessError):
        return "unknown"


def machine_identifier() -> str:
    return platform.node() or "unknown"


def algorithm_version(*, odd_a_only: bool) -> str:
    return ALGORITHM_ODD_A if odd_a_only else ALGORITHM_ALL


def classify_preimage(n: int) -> str:
    if n % 2 == 0:
        return CLASS_EVEN
    if is_square(n):
        return CLASS_ODD_SQUARE
    return CLASS_ODD_NON_SQUARE


def residue_bundle(value: int) -> dict[str, int]:
    return {
        "mod_2": value % 2,
        "mod_4": value % 4,
        "mod_8": value % 8,
        "mod_16": value % 16,
    }


def verify_hit(a: int, n: int) -> None:
    """Exact interval check. floor_power only for odd n."""

    lower = a**8
    upper = (a**4 + 1) ** 2
    cube = n * n * n
    if not (lower <= cube < upper):
        raise ValueError(f"interval failed for a={a} n={n}")
    if n % 2 == 1 and floor_power(n) != a**4:
        raise ValueError(f"floor_power({n}) != {a**4}")


@dataclass(frozen=True)
class EvalRecord:
    s: int
    a: int
    n: int | None
    n_is_odd: bool | None
    n_is_square: bool | None
    exact_Tn: int
    interval_lower: int
    interval_upper: int
    cube_residual: int | None
    classification: str
    occupancy: int
    d_lower: int | None
    d_upper: int | None
    n_mod_2: int | None
    n_mod_4: int | None
    n_mod_8: int | None
    n_mod_16: int | None
    a_mod_2: int
    a_mod_4: int
    a_mod_8: int
    a_mod_16: int

    def as_hit_dict(self) -> dict[str, Any]:
        if self.n is None:
            raise ValueError("INTERVAL_EMPTY has no hit payload")
        return {
            "s": self.s,
            "a": self.a,
            "n": self.n,
            "n_is_odd": self.n_is_odd,
            "n_is_square": self.n_is_square,
            "exact_Tn": str(self.exact_Tn),
            "interval_lower": str(self.interval_lower),
            "interval_upper": str(self.interval_upper),
            "cube_residual": str(self.cube_residual),
            "classification": self.classification,
            "n_mod_2": self.n_mod_2,
            "n_mod_4": self.n_mod_4,
            "n_mod_8": self.n_mod_8,
            "n_mod_16": self.n_mod_16,
            "a_mod_2": self.a_mod_2,
            "a_mod_4": self.a_mod_4,
            "a_mod_8": self.a_mod_8,
            "a_mod_16": self.a_mod_16,
        }


def evaluate_a(a: int) -> EvalRecord:
    """Exact occupancy and classification of one a. No floats."""

    if a < 1:
        raise ValueError("evaluate_a requires a >= 1")
    pow4 = a * a * a * a
    lower = pow4 * pow4
    upper = (pow4 + 1) * (pow4 + 1)
    m = ceil_cbrt(lower)
    cube = m * m * m
    a_res = residue_bundle(a)
    if cube < upper:
        nxt = m + 1
        if nxt * nxt * nxt < upper:
            raise RuntimeError(f"two cubes in interval at a={a}")
        n_res = residue_bundle(m)
        classification = classify_preimage(m)
        verify_hit(a, m)
        return EvalRecord(
            s=PARAMETER_S,
            a=a,
            n=m,
            n_is_odd=m % 2 == 1,
            n_is_square=is_square(m),
            exact_Tn=pow4,
            interval_lower=lower,
            interval_upper=upper,
            cube_residual=cube - lower,
            classification=classification,
            occupancy=1,
            d_lower=cube - lower,
            d_upper=None,
            n_mod_2=n_res["mod_2"],
            n_mod_4=n_res["mod_4"],
            n_mod_8=n_res["mod_8"],
            n_mod_16=n_res["mod_16"],
            a_mod_2=a_res["mod_2"],
            a_mod_4=a_res["mod_4"],
            a_mod_8=a_res["mod_8"],
            a_mod_16=a_res["mod_16"],
        )
    prev = m - 1
    d_lower = lower - prev * prev * prev if prev >= 0 else lower
    return EvalRecord(
        s=PARAMETER_S,
        a=a,
        n=None,
        n_is_odd=None,
        n_is_square=None,
        exact_Tn=pow4,
        interval_lower=lower,
        interval_upper=upper,
        cube_residual=None,
        classification=CLASS_EMPTY,
        occupancy=0,
        d_lower=d_lower,
        d_upper=cube - upper,
        n_mod_2=None,
        n_mod_4=None,
        n_mod_8=None,
        n_mod_16=None,
        a_mod_2=a_res["mod_2"],
        a_mod_4=a_res["mod_4"],
        a_mod_8=a_res["mod_8"],
        a_mod_16=a_res["mod_16"],
    )


def _iter_a(a_start: int, a_end: int, odd_a_only: bool) -> Iterator[int]:
    a = a_start
    if odd_a_only and a % 2 == 0:
        a += 1
    step = 2 if odd_a_only else 1
    while a < a_end:
        yield a
        a += step


def scan_range(
    a_start: int,
    a_end: int,
    *,
    odd_a_only: bool = False,
    near_miss_cap: int = NEAR_MISS_CAP,
) -> dict[str, Any]:
    """Scan [a_start, a_end). Stores hits and compact near-misses only."""

    if a_start < 1 or a_end < a_start:
        raise ValueError("scan_range requires 1 <= a_start <= a_end")
    hits: list[dict[str, Any]] = []
    extra_misses: list[dict[str, Any]] = []
    best_lower: dict[str, Any] | None = None
    best_upper: dict[str, Any] | None = None
    n_empty = 0
    n_even = 0
    n_odd_square = 0
    n_odd_non_square = 0
    n_tested = 0
    min_gap: int | None = None
    max_gap: int | None = None
    stop = False

    for a in _iter_a(a_start, a_end, odd_a_only):
        rec = evaluate_a(a)
        n_tested += 1
        if rec.classification == CLASS_EMPTY:
            n_empty += 1
            assert rec.d_lower is not None and rec.d_upper is not None
            gap = rec.d_lower if rec.d_lower <= rec.d_upper else rec.d_upper
            if min_gap is None or gap < min_gap:
                min_gap = gap
            if max_gap is None or gap > max_gap:
                max_gap = gap
            if best_lower is None or rec.d_lower < int(best_lower["d"]):
                best_lower = {"a": a, "side": "lower", "d": rec.d_lower, "m": None}
            if best_upper is None or rec.d_upper < int(best_upper["d"]):
                best_upper = {"a": a, "side": "upper", "d": rec.d_upper, "m": None}
            width = rec.interval_upper - rec.interval_lower
            if gap * 4 < width and len(extra_misses) < near_miss_cap:
                extra_misses.append(
                    {
                        "a": a,
                        "side": "lower" if rec.d_lower <= rec.d_upper else "upper",
                        "d": gap,
                        "m": None,
                        "kind": "close",
                    }
                )
            continue
        payload = rec.as_hit_dict()
        hits.append(payload)
        if rec.classification == CLASS_EVEN:
            n_even += 1
        elif rec.classification == CLASS_ODD_SQUARE:
            n_odd_square += 1
        else:
            n_odd_non_square += 1
            stop = True
            break

    near_misses: list[dict[str, Any]] = []
    if best_lower is not None:
        near_misses.append({**best_lower, "kind": "best_lower"})
    if best_upper is not None:
        near_misses.append({**best_upper, "kind": "best_upper"})
    near_misses.extend(extra_misses)
    return {
        "a_start": a_start,
        "a_end": a_end,
        "n_tested": n_tested,
        "n_empty": n_empty,
        "n_even_cube": n_even,
        "n_odd_square": n_odd_square,
        "n_odd_non_square": n_odd_non_square,
        "min_gap": min_gap,
        "max_gap": max_gap,
        "hits": hits,
        "near_misses": near_misses,
        "stopped_on_odd_non_square": stop,
    }


def _worker(payload: dict[str, Any]) -> dict[str, Any]:
    result = scan_range(
        payload["a_start"],
        payload["a_end"],
        odd_a_only=payload["odd_a_only"],
        near_miss_cap=payload.get("near_miss_cap", NEAR_MISS_CAP),
    )
    result["chunk_id"] = payload["chunk_id"]
    result["worker_id"] = payload.get("worker_id", "worker")
    return result


def dataset_paths(data_dir: Path) -> dict[str, Path]:
    data_dir = Path(data_dir)
    return {
        "root": data_dir,
        "readme": data_dir / "README.md",
        "config": data_dir / "search_config.json",
        "manifest": data_dir / "manifest.json",
        "db": data_dir / "search.sqlite",
        "ranges": data_dir / "ranges",
        "hits": data_dir / "hits",
        "summaries": data_dir / "summaries",
        "analysis": data_dir / "analysis",
    }


def ensure_layout(data_dir: Path) -> dict[str, Path]:
    paths = dataset_paths(data_dir)
    for key in ("root", "ranges", "hits", "summaries", "analysis"):
        paths[key].mkdir(parents=True, exist_ok=True)
    return paths


SCHEMA = """
CREATE TABLE IF NOT EXISTS manifest (
    search_id TEXT PRIMARY KEY,
    problem TEXT NOT NULL,
    parameter_s INTEGER NOT NULL,
    a_start INTEGER NOT NULL,
    a_end INTEGER NOT NULL,
    status TEXT NOT NULL,
    software_version TEXT NOT NULL,
    git_commit TEXT NOT NULL,
    machine_identifier TEXT NOT NULL,
    started_at TEXT,
    completed_at TEXT,
    algorithm_version TEXT NOT NULL,
    arithmetic_method TEXT NOT NULL,
    worker_count INTEGER NOT NULL,
    checksum TEXT
);

CREATE TABLE IF NOT EXISTS chunks (
    chunk_id INTEGER PRIMARY KEY,
    search_id TEXT NOT NULL,
    algorithm_version TEXT NOT NULL,
    a_start INTEGER NOT NULL,
    a_end INTEGER NOT NULL,
    status TEXT NOT NULL,
    worker_id TEXT,
    started_at TEXT,
    completed_at TEXT,
    n_tested INTEGER,
    n_empty INTEGER,
    n_even_cube INTEGER,
    n_odd_square INTEGER,
    n_odd_non_square INTEGER,
    min_gap TEXT,
    max_gap TEXT,
    checksum TEXT,
    UNIQUE (search_id, a_start, a_end)
);

CREATE TABLE IF NOT EXISTS hits (
    hit_id INTEGER PRIMARY KEY,
    chunk_id INTEGER NOT NULL,
    s INTEGER NOT NULL,
    a INTEGER NOT NULL,
    n TEXT NOT NULL,
    n_is_odd INTEGER NOT NULL,
    n_is_square INTEGER NOT NULL,
    exact_Tn TEXT NOT NULL,
    interval_lower TEXT NOT NULL,
    interval_upper TEXT NOT NULL,
    cube_residual TEXT NOT NULL,
    classification TEXT NOT NULL,
    n_mod_2 INTEGER NOT NULL,
    n_mod_4 INTEGER NOT NULL,
    n_mod_8 INTEGER NOT NULL,
    n_mod_16 INTEGER NOT NULL,
    a_mod_2 INTEGER NOT NULL,
    a_mod_4 INTEGER NOT NULL,
    a_mod_8 INTEGER NOT NULL,
    a_mod_16 INTEGER NOT NULL
);

CREATE TABLE IF NOT EXISTS near_misses (
    miss_id INTEGER PRIMARY KEY,
    chunk_id INTEGER NOT NULL,
    a INTEGER NOT NULL,
    side TEXT NOT NULL,
    d TEXT NOT NULL,
    m TEXT,
    kind TEXT NOT NULL
);
"""


def connect_db(db_path: Path) -> sqlite3.Connection:
    conn = sqlite3.connect(str(db_path), timeout=60)
    conn.row_factory = sqlite3.Row
    conn.execute("PRAGMA journal_mode=WAL")
    conn.execute("PRAGMA synchronous=NORMAL")
    return conn


def chunk_checksum(result: dict[str, Any]) -> str:
    raw = json.dumps(
        {
            "a_start": result["a_start"],
            "a_end": result["a_end"],
            "n_tested": result["n_tested"],
            "n_empty": result["n_empty"],
            "n_even_cube": result["n_even_cube"],
            "n_odd_square": result["n_odd_square"],
            "n_odd_non_square": result["n_odd_non_square"],
            "hits": [(h["a"], h["n"], h["classification"]) for h in result["hits"]],
        },
        separators=(",", ":"),
        sort_keys=True,
    )
    return hashlib.sha256(raw.encode("utf-8")).hexdigest()


def manifest_checksum(conn: sqlite3.Connection, search_id: str) -> str:
    rows = conn.execute(
        "SELECT a_start, a_end, status, checksum FROM chunks "
        "WHERE search_id = ? ORDER BY a_start",
        (search_id,),
    ).fetchall()
    raw = json.dumps([tuple(row) for row in rows], separators=(",", ":"))
    return hashlib.sha256(raw.encode("utf-8")).hexdigest()


def write_json(path: Path, payload: dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")


def load_json(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8"))


def default_search_id(a_start: int, a_end: int, algo: str) -> str:
    return f"{PROBLEM_ID}-s{PARAMETER_S}-{algo}-{a_start}-{a_end}"


def init_search(
    data_dir: Path,
    *,
    a_start: int = 1,
    a_end: int = 1_000_000,
    chunk_size: int = 100_000,
    odd_a_only: bool = False,
    workers: int = 1,
    force: bool = False,
    extend: bool = False,
    search_id: str | None = None,
) -> dict[str, Any]:
    if a_start < 1 or a_end <= a_start or chunk_size < 1:
        raise ValueError("init requires 1 <= a_start < a_end and chunk_size >= 1")
    paths = ensure_layout(data_dir)
    algo = algorithm_version(odd_a_only=odd_a_only)
    method = arithmetic_method()
    sid = search_id or default_search_id(a_start, a_end, algo)
    db_path = paths["db"]

    if db_path.exists() and not force and not extend:
        raise FileExistsError(f"{db_path} already exists; use --force or --extend")

    if force and db_path.exists():
        db_path.unlink()
        for suffix in ("-wal", "-shm"):
            extra = Path(str(db_path) + suffix)
            if extra.exists():
                extra.unlink()

    conn = connect_db(db_path)
    try:
        conn.executescript(SCHEMA)
        existing = conn.execute("SELECT * FROM manifest").fetchone()
        if existing and extend:
            if existing["algorithm_version"] != algo or existing["arithmetic_method"] != method:
                conn.execute(
                    "UPDATE chunks SET status = ? WHERE search_id = ?",
                    (STATUS_INVALIDATED, existing["search_id"]),
                )
                raise ValueError("algorithm or arithmetic method changed; chunks invalidated")
            sid = existing["search_id"]
            old_end = int(existing["a_end"])
            if a_end <= old_end:
                raise ValueError("extend requires a larger a_end")
            a_start_new = old_end
            _insert_chunks(conn, sid, algo, a_start_new, a_end, chunk_size)
            conn.execute(
                "UPDATE manifest SET a_end = ?, status = ?, completed_at = NULL WHERE search_id = ?",
                (a_end, STATUS_PENDING, sid),
            )
            conn.commit()
        else:
            conn.execute("DELETE FROM manifest")
            conn.execute(
                """
                INSERT INTO manifest (
                    search_id, problem, parameter_s, a_start, a_end, status,
                    software_version, git_commit, machine_identifier,
                    started_at, completed_at, algorithm_version,
                    arithmetic_method, worker_count, checksum
                ) VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, NULL, NULL, ?, ?, ?, NULL)
                """,
                (
                    sid,
                    PROBLEM_ID,
                    PARAMETER_S,
                    a_start,
                    a_end,
                    STATUS_PENDING,
                    SOFTWARE_VERSION,
                    git_commit(),
                    machine_identifier(),
                    algo,
                    method,
                    workers,
                ),
            )
            _insert_chunks(conn, sid, algo, a_start, a_end, chunk_size)
            conn.commit()

        config = {
            "search_id": sid,
            "problem": PROBLEM_ID,
            "parameter_s": PARAMETER_S,
            "algorithm_version": algo,
            "arithmetic_method": method,
            "a_start": a_start if not existing else int(existing["a_start"]),
            "a_end": a_end,
            "chunk_size": chunk_size,
            "odd_a_only": odd_a_only,
            "near_miss_cap_per_chunk": NEAR_MISS_CAP,
            "software_version": SOFTWARE_VERSION,
        }
        write_json(paths["config"], config)
        snap = _manifest_snapshot(conn, sid)
        write_json(paths["manifest"], snap)
        return config
    finally:
        conn.close()


def _insert_chunks(
    conn: sqlite3.Connection,
    search_id: str,
    algo: str,
    a_start: int,
    a_end: int,
    chunk_size: int,
) -> None:
    start = a_start
    while start < a_end:
        end = start + chunk_size
        if end > a_end:
            end = a_end
        conn.execute(
            """
            INSERT OR IGNORE INTO chunks (
                search_id, algorithm_version, a_start, a_end, status
            ) VALUES (?, ?, ?, ?, ?)
            """,
            (search_id, algo, start, end, STATUS_PENDING),
        )
        start = end


def _manifest_snapshot(conn: sqlite3.Connection, search_id: str) -> dict[str, Any]:
    row = conn.execute("SELECT * FROM manifest WHERE search_id = ?", (search_id,)).fetchone()
    if row is None:
        raise ValueError(f"missing manifest {search_id}")
    data = {key: row[key] for key in MANIFEST_KEYS}
    counts = {
        status: conn.execute(
            "SELECT COUNT(*) FROM chunks WHERE search_id = ? AND status = ?",
            (search_id, status),
        ).fetchone()[0]
        for status in (
            STATUS_PENDING,
            STATUS_RUNNING,
            STATUS_COMPLETE,
            STATUS_FAILED,
            STATUS_INVALIDATED,
        )
    }
    data["chunk_status_counts"] = counts
    return data


def reset_stale_running(conn: sqlite3.Connection, search_id: str, *, max_age: int = STALE_RUNNING_SECONDS) -> int:
    rows = conn.execute(
        "SELECT chunk_id, started_at FROM chunks WHERE search_id = ? AND status = ?",
        (search_id, STATUS_RUNNING),
    ).fetchall()
    now = datetime.now(timezone.utc)
    reset = 0
    for row in rows:
        started = row["started_at"]
        stale = True
        if started:
            try:
                ts = datetime.fromisoformat(started)
                if ts.tzinfo is None:
                    ts = ts.replace(tzinfo=timezone.utc)
                stale = (now - ts).total_seconds() >= max_age
            except ValueError:
                stale = True
        if stale:
            conn.execute(
                "UPDATE chunks SET status = ?, worker_id = NULL WHERE chunk_id = ?",
                (STATUS_PENDING, row["chunk_id"]),
            )
            reset += 1
    if reset:
        conn.commit()
    return reset


def claim_chunks(
    conn: sqlite3.Connection,
    search_id: str,
    *,
    limit: int,
    worker_id: str,
    retry_failed: bool = False,
) -> list[sqlite3.Row]:
    statuses = [STATUS_PENDING]
    if retry_failed:
        statuses.append(STATUS_FAILED)
    placeholders = ",".join("?" for _ in statuses)
    rows = conn.execute(
        f"SELECT * FROM chunks WHERE search_id = ? AND status IN ({placeholders}) "
        "ORDER BY a_start LIMIT ?",
        (search_id, *statuses, limit),
    ).fetchall()
    claimed: list[sqlite3.Row] = []
    now = utc_now()
    for row in rows:
        cur = conn.execute(
            "UPDATE chunks SET status = ?, worker_id = ?, started_at = ?, completed_at = NULL "
            "WHERE chunk_id = ? AND status IN ({})".format(placeholders),
            (STATUS_RUNNING, worker_id, now, row["chunk_id"], *statuses),
        )
        if cur.rowcount == 1:
            claimed.append(row)
    conn.commit()
    return claimed


def persist_chunk(
    conn: sqlite3.Connection,
    search_id: str,
    result: dict[str, Any],
    paths: dict[str, Path],
) -> None:
    digest = chunk_checksum(result)
    chunk_id = result["chunk_id"]
    conn.execute(
        """
        UPDATE chunks SET
            status = ?, completed_at = ?, n_tested = ?, n_empty = ?,
            n_even_cube = ?, n_odd_square = ?, n_odd_non_square = ?,
            min_gap = ?, max_gap = ?, checksum = ?
        WHERE chunk_id = ?
        """,
        (
            STATUS_COMPLETE,
            utc_now(),
            result["n_tested"],
            result["n_empty"],
            result["n_even_cube"],
            result["n_odd_square"],
            result["n_odd_non_square"],
            None if result["min_gap"] is None else str(result["min_gap"]),
            None if result["max_gap"] is None else str(result["max_gap"]),
            digest,
            chunk_id,
        ),
    )
    for hit in result["hits"]:
        conn.execute(
            """
            INSERT INTO hits (
                chunk_id, s, a, n, n_is_odd, n_is_square, exact_Tn,
                interval_lower, interval_upper, cube_residual, classification,
                n_mod_2, n_mod_4, n_mod_8, n_mod_16,
                a_mod_2, a_mod_4, a_mod_8, a_mod_16
            ) VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
            """,
            (
                chunk_id,
                hit["s"],
                hit["a"],
                str(hit["n"]),
                int(hit["n_is_odd"]),
                int(hit["n_is_square"]),
                hit["exact_Tn"],
                hit["interval_lower"],
                hit["interval_upper"],
                hit["cube_residual"],
                hit["classification"],
                hit["n_mod_2"],
                hit["n_mod_4"],
                hit["n_mod_8"],
                hit["n_mod_16"],
                hit["a_mod_2"],
                hit["a_mod_4"],
                hit["a_mod_8"],
                hit["a_mod_16"],
            ),
        )
        write_json(paths["hits"] / f"a_{hit['a']}.json", hit)
        if hit["classification"] == CLASS_ODD_NON_SQUARE:
            write_json(paths["hits"] / "ODD_NON_SQUARE.json", hit)
    for miss in result["near_misses"]:
        conn.execute(
            """
            INSERT INTO near_misses (chunk_id, a, side, d, m, kind)
            VALUES (?, ?, ?, ?, ?, ?)
            """,
            (
                chunk_id,
                miss["a"],
                miss["side"],
                str(miss["d"]),
                None if miss.get("m") is None else str(miss["m"]),
                miss["kind"],
            ),
        )
    checksum = manifest_checksum(conn, search_id)
    conn.execute("UPDATE manifest SET checksum = ? WHERE search_id = ?", (checksum, search_id))
    conn.commit()


def mark_chunk_failed(conn: sqlite3.Connection, chunk_id: int, message: str) -> None:
    conn.execute(
        "UPDATE chunks SET status = ?, completed_at = ? WHERE chunk_id = ?",
        (STATUS_FAILED, utc_now(), chunk_id),
    )
    conn.commit()
    sys.stderr.write(f"chunk {chunk_id} FAILED: {message}\n")


def refresh_manifest_status(conn: sqlite3.Connection, search_id: str, *, workers: int | None = None) -> dict[str, Any]:
    counts = {
        status: conn.execute(
            "SELECT COUNT(*) FROM chunks WHERE search_id = ? AND status = ?",
            (search_id, status),
        ).fetchone()[0]
        for status in (
            STATUS_PENDING,
            STATUS_RUNNING,
            STATUS_COMPLETE,
            STATUS_FAILED,
            STATUS_INVALIDATED,
        )
    }
    if counts[STATUS_RUNNING] or counts[STATUS_PENDING]:
        status = STATUS_RUNNING if counts[STATUS_RUNNING] or counts[STATUS_COMPLETE] else STATUS_PENDING
        if counts[STATUS_RUNNING]:
            status = STATUS_RUNNING
        elif counts[STATUS_COMPLETE] and counts[STATUS_PENDING]:
            status = STATUS_RUNNING
        elif counts[STATUS_PENDING] and not counts[STATUS_COMPLETE]:
            status = STATUS_PENDING
    elif counts[STATUS_FAILED]:
        status = STATUS_FAILED
    elif counts[STATUS_COMPLETE]:
        status = STATUS_COMPLETE
    else:
        status = STATUS_PENDING
    completed_at = utc_now() if status == STATUS_COMPLETE else None
    started = conn.execute(
        "SELECT started_at FROM manifest WHERE search_id = ?", (search_id,)
    ).fetchone()["started_at"]
    if started is None and status != STATUS_PENDING:
        started = utc_now()
    if workers is not None:
        conn.execute(
            "UPDATE manifest SET status = ?, started_at = ?, completed_at = ?, worker_count = ?, "
            "checksum = ? WHERE search_id = ?",
            (status, started, completed_at, workers, manifest_checksum(conn, search_id), search_id),
        )
    else:
        conn.execute(
            "UPDATE manifest SET status = ?, started_at = ?, completed_at = ?, checksum = ? "
            "WHERE search_id = ?",
            (status, started, completed_at, manifest_checksum(conn, search_id), search_id),
        )
    conn.commit()
    return _manifest_snapshot(conn, search_id)


def run_search(
    data_dir: Path,
    *,
    workers: int = 1,
    retry_failed: bool = False,
    max_chunks: int | None = None,
    reset_stale: bool = True,
) -> dict[str, Any]:
    paths = dataset_paths(data_dir)
    config = load_json(paths["config"])
    odd_a_only = bool(config["odd_a_only"])
    sid = config["search_id"]
    conn = connect_db(paths["db"])
    odd_non_square = None
    processed = 0
    try:
        if reset_stale:
            reset_stale_running(conn, sid)
        method = arithmetic_method()
        row = conn.execute("SELECT * FROM manifest WHERE search_id = ?", (sid,)).fetchone()
        if row["arithmetic_method"] != method:
            conn.execute(
                "UPDATE chunks SET status = ? WHERE search_id = ? AND status != ?",
                (STATUS_INVALIDATED, sid, STATUS_COMPLETE),
            )
            conn.commit()
            raise ValueError(
                f"arithmetic method {method} != stored {row['arithmetic_method']}"
            )
        if row["algorithm_version"] != config["algorithm_version"]:
            raise ValueError("algorithm_version mismatch between config and manifest")
        refresh_manifest_status(conn, sid, workers=workers)
        write_json(paths["manifest"], _manifest_snapshot(conn, sid))

        while True:
            if max_chunks is not None and processed >= max_chunks:
                break
            remaining = None if max_chunks is None else max_chunks - processed
            batch = min(workers, remaining) if remaining is not None else max(workers, 1)
            claimed = claim_chunks(
                conn, sid, limit=batch, worker_id=f"pid{os.getpid()}", retry_failed=retry_failed
            )
            if not claimed:
                break
            payloads = [
                {
                    "chunk_id": row["chunk_id"],
                    "a_start": int(row["a_start"]),
                    "a_end": int(row["a_end"]),
                    "odd_a_only": odd_a_only,
                    "near_miss_cap": config.get("near_miss_cap_per_chunk", NEAR_MISS_CAP),
                    "worker_id": f"pid{os.getpid()}-{row['chunk_id']}",
                }
                for row in claimed
            ]
            if workers <= 1:
                results = [_worker(payload) for payload in payloads]
            else:
                results = []
                with ProcessPoolExecutor(max_workers=workers) as pool:
                    futures = {pool.submit(_worker, payload): payload for payload in payloads}
                    for fut in as_completed(futures):
                        payload = futures[fut]
                        try:
                            results.append(fut.result())
                        except Exception as exc:
                            mark_chunk_failed(conn, payload["chunk_id"], str(exc))
            for result in results:
                persist_chunk(conn, sid, result, paths)
                processed += 1
                if result["n_odd_non_square"]:
                    odd_non_square = result["hits"][-1]
                    print("ODD_FOURTH_POWER_COUNTEREXAMPLE", json.dumps(odd_non_square))
                    break
            if odd_non_square is not None:
                break

        snap = refresh_manifest_status(conn, sid, workers=workers)
        write_json(paths["manifest"], snap)
        return {"manifest": snap, "processed_chunks": processed, "odd_non_square": odd_non_square}
    finally:
        conn.close()


def status_report(data_dir: Path) -> dict[str, Any]:
    paths = dataset_paths(data_dir)
    conn = connect_db(paths["db"])
    try:
        config = load_json(paths["config"])
        sid = config["search_id"]
        snap = _manifest_snapshot(conn, sid)
        complete = conn.execute(
            "SELECT MIN(a_start), MAX(a_end), SUM(n_tested), SUM(n_even_cube), "
            "SUM(n_odd_square), SUM(n_odd_non_square) FROM chunks "
            "WHERE search_id = ? AND status = ?",
            (sid, STATUS_COMPLETE),
        ).fetchone()
        snap["complete_a_start"] = complete[0]
        snap["complete_a_end"] = complete[1]
        snap["complete_n_tested"] = complete[2]
        snap["complete_even_cubes"] = complete[3]
        snap["complete_odd_squares"] = complete[4]
        snap["complete_odd_non_squares"] = complete[5]
        return snap
    finally:
        conn.close()


def summarize(data_dir: Path) -> dict[str, Any]:
    paths = dataset_paths(data_dir)
    conn = connect_db(paths["db"])
    try:
        config = load_json(paths["config"])
        sid = config["search_id"]
        snap = refresh_manifest_status(conn, sid)
        write_json(paths["manifest"], snap)
        agg = conn.execute(
            "SELECT MIN(a_start), MAX(a_end), SUM(n_tested), SUM(n_empty), "
            "SUM(n_even_cube), SUM(n_odd_square), SUM(n_odd_non_square) "
            "FROM chunks WHERE search_id = ? AND status = ?",
            (sid, STATUS_COMPLETE),
        ).fetchone()
        hits = [dict(row) for row in conn.execute(
            "SELECT * FROM hits ORDER BY a"
        ).fetchall()]
        misses = [dict(row) for row in conn.execute(
            "SELECT * FROM near_misses ORDER BY a"
        ).fetchall()]
        gap_rows = conn.execute(
            "SELECT min_gap, max_gap FROM chunks "
            "WHERE search_id = ? AND status = ? AND min_gap IS NOT NULL",
            (sid, STATUS_COMPLETE),
        ).fetchall()
        min_gap = None
        max_gap = None
        for row in gap_rows:
            lo = int(row["min_gap"])
            hi = int(row["max_gap"]) if row["max_gap"] is not None else lo
            if min_gap is None or lo < min_gap:
                min_gap = lo
            if max_gap is None or hi > max_gap:
                max_gap = hi
        strongest_miss = None
        if misses:
            strongest_miss = min(misses, key=lambda row: int(row["d"]))
        smallest_witness = None
        odd_non_squares = [h for h in hits if h["classification"] == CLASS_ODD_NON_SQUARE]
        if odd_non_squares:
            smallest_witness = odd_non_squares[0]
        elif hits:
            smallest_witness = hits[0]
        summary = {
            "search_id": sid,
            "problem": PROBLEM_ID,
            "parameter_s": PARAMETER_S,
            "a_range_searched": [agg[0], agg[1]],
            "status": snap["status"],
            "algorithm_version": snap["algorithm_version"],
            "arithmetic_method": snap["arithmetic_method"],
            "git_commit": snap["git_commit"],
            "software_version": snap["software_version"],
            "total_candidates": agg[2] or 0,
            "interval_empty": agg[3] or 0,
            "interval_cubes": (agg[4] or 0) + (agg[5] or 0) + (agg[6] or 0),
            "even_cubes": agg[4] or 0,
            "odd_squares": agg[5] or 0,
            "odd_non_squares": agg[6] or 0,
            "min_gap": min_gap,
            "max_gap": None if max_gap is None else str(max_gap),
            "smallest_witness": smallest_witness,
            "strongest_near_miss": strongest_miss,
            "hits": hits,
            "checksum": snap["checksum"],
            "chunk_status_counts": snap["chunk_status_counts"],
            "completion_status": snap["status"],
        }
        write_json(paths["summaries"] / "summary.json", summary)
        (paths["summaries"] / "summary.md").write_text(render_summary_md(summary), encoding="utf-8")
        return summary
    finally:
        conn.close()


def render_summary_md(summary: dict[str, Any]) -> str:
    rng = summary["a_range_searched"]
    lines = [
        "# Odd fourth-power successor search",
        "",
        f"Status: **{summary['status']}**",
        "",
        "Exact integer search for `T(n) = a^4` on odd non-square `n`.",
        "A finite empty range is evidence, not a theorem.",
        "",
        "## Range",
        "",
        f"- search_id: `{summary['search_id']}`",
        f"- a-range: `[{rng[0]}, {rng[1]})`",
        f"- algorithm: `{summary['algorithm_version']}`",
        f"- arithmetic: `{summary['arithmetic_method']}`",
        f"- git: `{summary['git_commit']}`",
        f"- checksum: `{summary['checksum']}`",
        "",
        "## Counts",
        "",
        f"- candidates tested: `{summary['total_candidates']}`",
        f"- interval cubes: `{summary['interval_cubes']}`",
        f"- even cubes: `{summary['even_cubes']}`",
        f"- odd squares: `{summary['odd_squares']}`",
        f"- odd non-squares: `{summary['odd_non_squares']}`",
        f"- min gap: `{summary['min_gap']}`",
        f"- max gap: `{summary['max_gap']}`",
        "",
        "## Smallest recorded cube",
        "",
        f"`{summary['smallest_witness']}`",
        "",
        "## Strongest near miss",
        "",
        f"`{summary['strongest_near_miss']}`",
        "",
        "## Hits",
        "",
    ]
    for hit in summary["hits"]:
        lines.append(
            f"- a `{hit['a']}`: n `{hit['n']}` {hit['classification']} "
            f"n_mod_16=`{hit['n_mod_16']}` a_mod_16=`{hit['a_mod_16']}`"
        )
    if not summary["hits"]:
        lines.append("- none")
    lines.append("")
    return "\n".join(lines) + "\n"


def benchmark(a_end: int = 10_000, *, a_start: int = 1) -> dict[str, Any]:
    if a_end <= a_start:
        raise ValueError("benchmark requires a_start < a_end")
    sample = [1, 8, 27, 97, max(2, a_end // 2)]
    verify_start = time.perf_counter()
    verify_count = 0
    for a in sample:
        rec = evaluate_a(a)
        if rec.n is not None:
            verify_hit(a, rec.n)
            verify_count += 1
    verify_secs = time.perf_counter() - verify_start

    cbrt_start = time.perf_counter()
    for a in range(a_start, min(a_start + 200, a_end)):
        ceil_cbrt(a * a * a * a * a * a * a * a)
    cbrt_n = min(200, a_end - a_start)
    cbrt_secs = time.perf_counter() - cbrt_start

    walk_start = time.perf_counter()
    result = scan_range(a_start, a_end)
    walk_secs = time.perf_counter() - walk_start
    n = max(result["n_tested"], 1)
    payload = {
        "a_start": a_start,
        "a_end": a_end,
        "n_tested": result["n_tested"],
        "seconds": walk_secs,
        "candidates_per_sec": n / walk_secs if walk_secs else None,
        "cube_root_ops_per_sec": cbrt_n / cbrt_secs if cbrt_secs else None,
        "exact_verification_per_sec": verify_count / verify_secs if verify_secs else None,
        "hits": len(result["hits"]),
        "arithmetic_method": arithmetic_method(),
        "algorithm_version": ALGORITHM_ALL,
        "memory_bytes": _rss_bytes(),
        "storage_growth_bytes_per_chunk_estimate": 512 + 256 * len(result["hits"]),
    }
    return payload


def _rss_bytes() -> int | None:
    try:
        import psutil

        return int(psutil.Process(os.getpid()).memory_info().rss)
    except Exception:
        if sys.platform == "win32":
            return None
        try:
            import resource

            usage = resource.getrusage(resource.RUSAGE_SELF).ru_maxrss
            if sys.platform == "darwin":
                return int(usage)
            return int(usage) * 1024
        except Exception:
            return None


def _build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--data-dir", type=Path, default=DEFAULT_DATA_DIR)
    sub = parser.add_subparsers(dest="command", required=True)

    bench = sub.add_parser("benchmark")
    bench.add_argument("--a-start", type=int, default=1)
    bench.add_argument("--a-end", type=int, default=10_000)

    init = sub.add_parser("init")
    init.add_argument("--a-start", type=int, default=1)
    init.add_argument("--a-end", type=int, required=True)
    init.add_argument("--chunk-size", type=int, default=100_000)
    init.add_argument("--workers", type=int, default=1)
    init.add_argument("--odd-a", action="store_true")
    init.add_argument("--force", action="store_true")
    init.add_argument("--extend", action="store_true")
    init.add_argument("--search-id", type=str, default=None)

    run = sub.add_parser("run")
    run.add_argument("--workers", type=int, default=max(os.cpu_count() or 1, 1))
    run.add_argument("--retry-failed", action="store_true")
    run.add_argument("--max-chunks", type=int, default=None)

    resume = sub.add_parser("resume")
    resume.add_argument("--workers", type=int, default=max(os.cpu_count() or 1, 1))
    resume.add_argument("--retry-failed", action="store_true")
    resume.add_argument("--max-chunks", type=int, default=None)

    sub.add_parser("summarize")
    sub.add_parser("status")
    return parser


def main(argv: list[str] | None = None) -> int:
    parser = _build_parser()
    args = parser.parse_args(argv)
    data_dir = Path(args.data_dir)
    if args.command == "benchmark":
        payload = benchmark(args.a_end, a_start=args.a_start)
        print(json.dumps(payload, indent=2))
        return 0
    if args.command == "init":
        config = init_search(
            data_dir,
            a_start=args.a_start,
            a_end=args.a_end,
            chunk_size=args.chunk_size,
            odd_a_only=args.odd_a,
            workers=args.workers,
            force=args.force,
            extend=args.extend,
            search_id=args.search_id,
        )
        print(json.dumps(config, indent=2))
        return 0
    if args.command in {"run", "resume"}:
        result = run_search(
            data_dir,
            workers=args.workers,
            retry_failed=args.retry_failed,
            max_chunks=args.max_chunks,
            reset_stale=True,
        )
        print(json.dumps(result["manifest"], indent=2))
        if result["odd_non_square"] is not None:
            return 2
        return 0
    if args.command == "summarize":
        summary = summarize(data_dir)
        slim = {k: v for k, v in summary.items() if k != "hits"}
        print(json.dumps(slim, indent=2, default=str))
        return 0
    if args.command == "status":
        print(json.dumps(status_report(data_dir), indent=2, default=str))
        return 0
    parser.error(f"unknown command {args.command}")
    return 2


if __name__ == "__main__":
    raise SystemExit(main())
