"""Factor and continuation queries. DuckDB when present, else SQLite."""

from __future__ import annotations

import sqlite3
from pathlib import Path
from typing import Any

from research.juggler_sequence.atlas.packed import unpack_word
from research.juggler_sequence.atlas.storage import connect, sqlite_path


def _latest_experiment(con: sqlite3.Connection) -> str:
    row = con.execute(
        "SELECT experiment_id FROM experiments ORDER BY start_time DESC LIMIT 1"
    ).fetchone()
    if row is None:
        raise ValueError("no experiments in the atlas store")
    return row[0]


def factor_complexity(
    language_id: str,
    r: int,
    *,
    experiment_id: str | None = None,
    data_dir: Path,
) -> int:
    return len(
        factor_set(
            language_id,
            r,
            experiment_id=experiment_id,
            data_dir=data_dir,
        )
    )


def factor_set(
    language_id: str,
    r: int,
    *,
    experiment_id: str | None = None,
    data_dir: Path,
) -> list[str]:
    parquet_hits = _duckdb_factors(
        language_id, r, experiment_id=experiment_id, data_dir=data_dir
    )
    if parquet_hits is not None:
        return parquet_hits
    con = connect(data_dir, read_only=True)
    try:
        eid = experiment_id or _latest_experiment(con)
        rows = con.execute(
            """
            SELECT packed_factor FROM factors
            WHERE experiment_id = ? AND language_id = ? AND r = ?
            ORDER BY packed_factor
            """,
            (eid, language_id, r),
        ).fetchall()
        return [unpack_word(r, packed) for (packed,) in rows]
    finally:
        con.close()


def continuation_mask(
    word: str,
    language_id: str,
    *,
    experiment_id: str | None = None,
    data_dir: Path,
) -> dict[str, Any]:
    from research.juggler_sequence.atlas.packed import pack_word, word_id

    length, packed = pack_word(word)
    con = connect(data_dir, read_only=True)
    try:
        eid = experiment_id or _latest_experiment(con)
        row = con.execute(
            """
            SELECT successor_mask, continuation_count
            FROM continuations
            WHERE experiment_id = ? AND word_id = ? AND language_id = ?
            """,
            (eid, word_id(length, packed), language_id),
        ).fetchone()
        if row is None:
            return {
                "word": word,
                "language_id": language_id,
                "successor_mask": None,
                "continuation_count": None,
                "experiment_id": eid,
            }
        return {
            "word": word,
            "language_id": language_id,
            "successor_mask": row[0],
            "continuation_count": row[1],
            "wO": bool(row[0] & 1),
            "wE": bool(row[0] & 2),
            "experiment_id": eid,
        }
    finally:
        con.close()


def continuation_histogram(
    language_id: str,
    *,
    experiment_id: str | None = None,
    data_dir: Path,
) -> list[dict[str, Any]]:
    con = connect(data_dir, read_only=True)
    try:
        eid = experiment_id or _latest_experiment(con)
        rows = con.execute(
            """
            SELECT
                (word_id >> 32) AS length,
                continuation_count,
                COUNT(*) AS n
            FROM continuations
            WHERE experiment_id = ? AND language_id = ?
            GROUP BY length, continuation_count
            ORDER BY length, continuation_count
            """,
            (eid, language_id),
        ).fetchall()
        return [
            {"length": r[0], "d": r[1], "count": r[2], "experiment_id": eid}
            for r in rows
        ]
    finally:
        con.close()


def _duckdb_factors(
    language_id: str,
    r: int,
    *,
    experiment_id: str | None,
    data_dir: Path,
) -> list[str] | None:
    if language_id != "REALIZABLE":
        return None
    try:
        import duckdb
    except ImportError:
        return None
    if experiment_id is None:
        con = connect(data_dir, read_only=True)
        try:
            experiment_id = _latest_experiment(con)
        finally:
            con.close()
    pattern = str(
        data_dir / "experiments" / experiment_id / "observations" / "**" / "*.parquet"
    )
    if not list((data_dir / "experiments" / experiment_id / "observations").glob("**/*.parquet")):
        return None
    try:
        con = duckdb.connect()
        rows = con.execute(
            """
            SELECT packed
            FROM read_parquet(?)
            WHERE length = ? AND realization_status = 'FOUND'
            ORDER BY packed
            """,
            [pattern, r],
        ).fetchall()
        return [unpack_word(r, packed) for (packed,) in rows]
    except Exception:
        return None
    finally:
        try:
            con.close()
        except Exception:
            pass


def word_record(
    word: str,
    *,
    experiment_id: str | None = None,
    data_dir: Path,
) -> dict[str, Any]:
    from research.juggler_sequence.atlas.packed import pack_word, word_id, word_metadata

    length, packed = pack_word(word)
    meta = word_metadata(length, packed)
    if not sqlite_path(data_dir).is_file():
        return {"word": word, **meta, "realization_status": None}
    con = connect(data_dir, read_only=True)
    try:
        eid = experiment_id or _latest_experiment(con)
        row = con.execute(
            """
            SELECT min_realizer, realization_scan_limit, realization_source,
                   realization_status, trajectory_end, min_expanding_realizer,
                   expanding_status
            FROM realizers
            WHERE experiment_id = ? AND word_id = ?
            """,
            (eid, word_id(length, packed)),
        ).fetchone()
        out = {"word": word, "experiment_id": eid, **meta}
        if row is None:
            out["realization_status"] = None
            return out
        out.update(
            {
                "min_realizer": row[0],
                "realization_scan_limit": row[1],
                "realization_source": row[2],
                "realization_status": row[3],
                "trajectory_end": row[4],
                "min_expanding_realizer": row[5],
                "expanding_status": row[6],
            }
        )
        return out
    finally:
        con.close()
