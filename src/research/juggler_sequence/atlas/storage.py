"""SQLite / Parquet / SHA-256 experiment store. Never overwrite runs."""

from __future__ import annotations

import hashlib
import json
import sqlite3
import subprocess
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Iterable

from research.juggler_sequence.atlas.packed import (
    all_words,
    append_symbol,
    dense_index,
    pack_word,
    split_word_id,
    unpack_word,
    word_id,
    word_metadata,
)
from research.juggler_sequence.atlas.schema import (
    LANG_EXPANDING,
    LANG_PE_CERTIFIED,
    LANG_PE_RUN,
    LANG_PERSISTENT,
    LANG_REALIZABLE,
    SCHEMA_VERSION,
    SOURCE_CPU,
    STATUS_FOUND,
    STATUS_NOT_FOUND,
)

DEFAULT_DATA_DIR = (
    Path(__file__).resolve().parents[4] / "data" / "research" / "juggler" / "word_atlas"
)


def utc_now() -> str:
    return datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%SZ")


def _compact_int(value: int | None, *, bit_limit: int = 256) -> str | None:
    if value is None:
        return None
    if int(value).bit_length() > bit_limit:
        return f"bits:{int(value).bit_length()}"
    return str(value)


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as fh:
        for chunk in iter(lambda: fh.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def git_commit(repo: Path | None = None) -> str:
    root = repo or Path(__file__).resolve().parents[4]
    try:
        out = subprocess.check_output(
            ["git", "rev-parse", "HEAD"],
            cwd=root,
            text=True,
            stderr=subprocess.DEVNULL,
        )
        return out.strip()
    except (subprocess.CalledProcessError, FileNotFoundError):
        return "working-tree"


def experiment_id(backend: str, k_max: int, n_max: int) -> str:
    return f"wa-{utc_now()}-{backend}-k{k_max}-n{n_max}"


def sqlite_path(data_dir: Path) -> Path:
    return data_dir / "word_atlas.sqlite"


def connect(data_dir: Path) -> sqlite3.Connection:
    data_dir.mkdir(parents=True, exist_ok=True)
    con = sqlite3.connect(sqlite_path(data_dir))
    con.row_factory = sqlite3.Row
    con.execute("PRAGMA foreign_keys = ON")
    _init(con)
    return con


def _init(con: sqlite3.Connection) -> None:
    con.executescript(
        """
        CREATE TABLE IF NOT EXISTS experiments (
            experiment_id TEXT PRIMARY KEY,
            schema_version TEXT NOT NULL,
            git_commit TEXT,
            k_max INTEGER NOT NULL,
            n_max INTEGER NOT NULL,
            n_begin INTEGER NOT NULL,
            backend TEXT NOT NULL,
            realization_source TEXT NOT NULL,
            start_time TEXT,
            end_time TEXT,
            manifest_path TEXT,
            record_counts TEXT
        );
        CREATE TABLE IF NOT EXISTS words (
            word_id INTEGER PRIMARY KEY,
            length INTEGER NOT NULL,
            packed INTEGER NOT NULL,
            odd_count INTEGER NOT NULL,
            even_count INTEGER NOT NULL,
            run_signature TEXT NOT NULL,
            exponent_surplus INTEGER NOT NULL,
            exponent_deficit INTEGER NOT NULL,
            beta_num INTEGER NOT NULL,
            beta_den INTEGER NOT NULL,
            UNIQUE(length, packed)
        );
        CREATE TABLE IF NOT EXISTS realizers (
            experiment_id TEXT NOT NULL,
            word_id INTEGER NOT NULL,
            min_realizer INTEGER,
            realization_scan_limit INTEGER NOT NULL,
            realization_source TEXT NOT NULL,
            realization_status TEXT NOT NULL,
            trajectory_end TEXT,
            min_expanding_realizer INTEGER,
            expanding_status TEXT NOT NULL,
            PRIMARY KEY (experiment_id, word_id)
        );
        CREATE TABLE IF NOT EXISTS continuations (
            experiment_id TEXT NOT NULL,
            word_id INTEGER NOT NULL,
            language_id TEXT NOT NULL,
            successor_mask INTEGER NOT NULL,
            continuation_count INTEGER NOT NULL,
            PRIMARY KEY (experiment_id, word_id, language_id)
        );
        CREATE TABLE IF NOT EXISTS factors (
            experiment_id TEXT NOT NULL,
            language_id TEXT NOT NULL,
            r INTEGER NOT NULL,
            packed_factor INTEGER NOT NULL,
            PRIMARY KEY (experiment_id, language_id, r, packed_factor)
        );
        CREATE TABLE IF NOT EXISTS pe_records (
            experiment_id TEXT NOT NULL,
            word_id INTEGER NOT NULL,
            min_n INTEGER NOT NULL,
            end_state TEXT NOT NULL,
            scan_limit INTEGER NOT NULL,
            pe_definition TEXT NOT NULL,
            a INTEGER,
            b INTEGER,
            search_id TEXT,
            language_id TEXT NOT NULL,
            PRIMARY KEY (experiment_id, word_id, min_n, language_id)
        );
        CREATE TABLE IF NOT EXISTS checksums (
            experiment_id TEXT NOT NULL,
            relative_path TEXT NOT NULL,
            sha256 TEXT NOT NULL,
            PRIMARY KEY (experiment_id, relative_path)
        );
        """
    )
    con.commit()


def ensure_words(con: sqlite3.Connection, k_max: int) -> int:
    existing = con.execute("SELECT MAX(length) FROM words").fetchone()[0]
    if existing is not None and existing >= k_max:
        return int(con.execute("SELECT COUNT(*) FROM words").fetchone()[0])
    con.executemany(
        """
        INSERT OR IGNORE INTO words (
            word_id, length, packed, odd_count, even_count, run_signature,
            exponent_surplus, exponent_deficit, beta_num, beta_den
        ) VALUES (
            :word_id, :length, :packed, :odd_count, :even_count, :run_signature,
            :exponent_surplus, :exponent_deficit, :beta_num, :beta_den
        )
        """,
        all_words(k_max),
    )
    con.commit()
    return int(con.execute("SELECT COUNT(*) FROM words").fetchone()[0])


def write_realizers(
    con: sqlite3.Connection,
    experiment_id: str,
    k_max: int,
    n_max: int,
    source: str,
    min_n: list[int | None],
    min_exp: list[int | None],
    end_at_min: list[int | None],
) -> int:
    rows: list[dict[str, Any]] = []
    for length in range(1, k_max + 1):
        for packed in range(1 << length):
            idx = dense_index(length, packed)
            found = min_n[idx] is not None
            exp_found = min_exp[idx] is not None
            end = end_at_min[idx]
            rows.append(
                {
                    "experiment_id": experiment_id,
                    "word_id": word_id(length, packed),
                    "min_realizer": min_n[idx],
                    "realization_scan_limit": n_max,
                    "realization_source": source,
                    "realization_status": STATUS_FOUND if found else STATUS_NOT_FOUND,
                    "trajectory_end": _compact_int(end),
                    "min_expanding_realizer": min_exp[idx],
                    "expanding_status": STATUS_FOUND if exp_found else STATUS_NOT_FOUND,
                }
            )
    con.executemany(
        """
        INSERT INTO realizers (
            experiment_id, word_id, min_realizer, realization_scan_limit,
            realization_source, realization_status, trajectory_end,
            min_expanding_realizer, expanding_status
        ) VALUES (
            :experiment_id, :word_id, :min_realizer, :realization_scan_limit,
            :realization_source, :realization_status, :trajectory_end,
            :min_expanding_realizer, :expanding_status
        )
        """,
        rows,
    )
    con.commit()
    return len(rows)


def _language_words(
    con: sqlite3.Connection,
    experiment_id: str,
    language_id: str,
    k_max: int,
) -> dict[int, set[int]]:
    """Map length -> set of packed words observed in that language."""

    by_len: dict[int, set[int]] = {r: set() for r in range(1, k_max + 1)}
    if language_id == LANG_REALIZABLE:
        rows = con.execute(
            """
            SELECT word_id FROM realizers
            WHERE experiment_id = ? AND realization_status = ?
            """,
            (experiment_id, STATUS_FOUND),
        )
        for (wid,) in rows:
            length, packed = split_word_id(wid)
            if 1 <= length <= k_max:
                by_len[length].add(packed)
        return by_len
    if language_id == LANG_EXPANDING:
        rows = con.execute(
            """
            SELECT word_id FROM realizers
            WHERE experiment_id = ? AND expanding_status = ?
            """,
            (experiment_id, STATUS_FOUND),
        )
        for (wid,) in rows:
            length, packed = split_word_id(wid)
            if 1 <= length <= k_max:
                by_len[length].add(packed)
        return by_len
    rows = con.execute(
        """
        SELECT word_id FROM pe_records
        WHERE experiment_id = ? AND language_id = ?
        """,
        (experiment_id, language_id),
    )
    for (wid,) in rows:
        length, packed = split_word_id(wid)
        word = unpack_word(length, packed)
        for r in range(1, min(length, k_max) + 1):
            for i in range(0, length - r + 1):
                _, fp = pack_word(word[i : i + r])
                by_len[r].add(fp)
    return by_len


def write_continuations_and_factors(
    con: sqlite3.Connection,
    experiment_id: str,
    k_max: int,
    languages: Iterable[str] = (
        LANG_REALIZABLE,
        LANG_EXPANDING,
        LANG_PERSISTENT,
        LANG_PE_CERTIFIED,
        LANG_PE_RUN,
    ),
) -> tuple[int, int]:
    cont_rows: list[dict[str, Any]] = []
    fact_rows: list[dict[str, Any]] = []
    for language_id in languages:
        by_len = _language_words(con, experiment_id, language_id, k_max)
        for r, packed_set in by_len.items():
            for packed in packed_set:
                fact_rows.append(
                    {
                        "experiment_id": experiment_id,
                        "language_id": language_id,
                        "r": r,
                        "packed_factor": packed,
                    }
                )
        for length in range(1, k_max):
            for packed in by_len[length]:
                _, w_o = append_symbol(length, packed, 1)
                _, w_e = append_symbol(length, packed, 0)
                mask = 0
                if w_o in by_len[length + 1]:
                    mask |= 1
                if w_e in by_len[length + 1]:
                    mask |= 2
                cont_rows.append(
                    {
                        "experiment_id": experiment_id,
                        "word_id": word_id(length, packed),
                        "language_id": language_id,
                        "successor_mask": mask,
                        "continuation_count": mask.bit_count(),
                    }
                )
    if cont_rows:
        con.executemany(
            """
            INSERT INTO continuations (
                experiment_id, word_id, language_id,
                successor_mask, continuation_count
            ) VALUES (
                :experiment_id, :word_id, :language_id,
                :successor_mask, :continuation_count
            )
            """,
            cont_rows,
        )
    if fact_rows:
        con.executemany(
            """
            INSERT OR IGNORE INTO factors (
                experiment_id, language_id, r, packed_factor
            ) VALUES (
                :experiment_id, :language_id, :r, :packed_factor
            )
            """,
            fact_rows,
        )
    con.commit()
    return len(cont_rows), len(fact_rows)


def write_pe_records(
    con: sqlite3.Connection,
    experiment_id: str,
    records: list[dict[str, Any]],
) -> int:
    rows = []
    for rec in records:
        rows.append(
            {
                "experiment_id": experiment_id,
                "word_id": rec["word_id"],
                "min_n": rec["min_n"],
                "end_state": _compact_int(rec["end_state"]) or "0",
                "scan_limit": rec.get("scan_limit", 0),
                "pe_definition": rec["pe_definition"],
                "a": rec.get("a"),
                "b": rec.get("b"),
                "search_id": rec.get("search_id"),
                "language_id": rec["language_id"],
            }
        )
    if rows:
        con.executemany(
            """
            INSERT OR IGNORE INTO pe_records (
                experiment_id, word_id, min_n, end_state, scan_limit,
                pe_definition, a, b, search_id, language_id
            ) VALUES (
                :experiment_id, :word_id, :min_n, :end_state, :scan_limit,
                :pe_definition, :a, :b, :search_id, :language_id
            )
            """,
            rows,
        )
        con.commit()
    return len(rows)


def write_parquet_partitions(
    experiment_dir: Path,
    k_max: int,
    n_max: int,
    source: str,
    min_n: list[int | None],
    min_exp: list[int | None],
    end_at_min: list[int | None],
) -> list[Path]:
    paths: list[Path] = []
    try:
        import pyarrow as pa
        import pyarrow.parquet as pq
    except ImportError:
        return paths
    for length in range(1, k_max + 1):
        rows = []
        for packed in range(1 << length):
            idx = dense_index(length, packed)
            meta = word_metadata(length, packed)
            found = min_n[idx] is not None
            end = end_at_min[idx]
            rows.append(
                {
                    **meta,
                    "min_realizer": min_n[idx],
                    "realization_scan_limit": n_max,
                    "realization_source": source,
                    "realization_status": STATUS_FOUND if found else STATUS_NOT_FOUND,
                    "trajectory_end": _compact_int(end),
                    "min_expanding_realizer": min_exp[idx],
                    "expanding_status": (
                        STATUS_FOUND if min_exp[idx] is not None else STATUS_NOT_FOUND
                    ),
                }
            )
        table = pa.Table.from_pylist(rows)
        out_dir = experiment_dir / "observations" / f"itinerary_length={length}"
        out_dir.mkdir(parents=True, exist_ok=True)
        path = out_dir / "census.parquet"
        pq.write_table(table, path)
        paths.append(path)
    return paths


def write_manifest(
    experiment_dir: Path,
    payload: dict[str, Any],
    artifacts: list[Path],
) -> tuple[Path, dict[str, str]]:
    checksums: dict[str, str] = {}
    for path in artifacts:
        rel = path.relative_to(experiment_dir).as_posix()
        checksums[rel] = sha256_file(path)
    payload = dict(payload)
    payload["schema_version"] = SCHEMA_VERSION
    payload["checksums"] = checksums
    path = experiment_dir / "manifest.json"
    path.write_text(json.dumps(payload, indent=2, sort_keys=True), encoding="utf-8")
    checksums["manifest.json"] = sha256_file(path)
    path.write_text(json.dumps(payload | {"checksums": checksums}, indent=2, sort_keys=True), encoding="utf-8")
    return path, checksums


def register_experiment(
    con: sqlite3.Connection,
    payload: dict[str, Any],
    checksums: dict[str, str],
) -> None:
    eid = payload["experiment_id"]
    exists = con.execute(
        "SELECT 1 FROM experiments WHERE experiment_id = ?", (eid,)
    ).fetchone()
    if exists:
        raise ValueError(f"experiment {eid} already exists")
    con.execute(
        """
        INSERT INTO experiments (
            experiment_id, schema_version, git_commit, k_max, n_max, n_begin,
            backend, realization_source, start_time, end_time, manifest_path,
            record_counts
        ) VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
        """,
        (
            eid,
            payload["schema_version"],
            payload.get("git_commit"),
            payload["k_max"],
            payload["n_max"],
            payload["n_begin"],
            payload["backend"],
            payload.get("realization_source", SOURCE_CPU),
            payload.get("start_time"),
            payload.get("end_time"),
            payload.get("manifest_path"),
            json.dumps(payload.get("record_counts", {})),
        ),
    )
    con.executemany(
        """
        INSERT INTO checksums (experiment_id, relative_path, sha256)
        VALUES (?, ?, ?)
        """,
        [(eid, rel, digest) for rel, digest in checksums.items()],
    )
    con.commit()
