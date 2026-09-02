"""Public atlas API. Python is the research interface."""

from __future__ import annotations

import json
from pathlib import Path
from typing import Any

from research.juggler_sequence.atlas.cpu_census import (
    census,
    fill_end_states,
    merge_starts,
)
from research.juggler_sequence.atlas.native import find_binary, parse_census_tsv, run_census
from research.juggler_sequence.atlas.packed import pack_word
from research.juggler_sequence.atlas.pe_adapter import pe_certified_records
from research.juggler_sequence.atlas.query import (
    continuation_histogram,
    continuation_mask as query_continuation_mask,
    factor_complexity as query_factor_complexity,
    factor_set as query_factor_set,
    word_record as query_word_record,
)
from research.juggler_sequence.atlas.schema import (
    PE_CERTIFIED,
    SCHEMA_VERSION,
    SOURCE_CPU,
    SOURCE_KERNEL_A,
    STATUS_FOUND,
    STATUS_NOT_FOUND,
)
from research.juggler_sequence.atlas.storage import (
    DEFAULT_DATA_DIR,
    connect,
    ensure_words,
    experiment_id as make_experiment_id,
    git_commit,
    register_experiment,
    utc_now,
    write_continuations_and_factors,
    write_manifest,
    write_parquet_partitions,
    write_pe_records,
    write_realizers,
)
from research.juggler_sequence.atlas.validate import (
    stored_metadata_matches,
    validate_suite,
)


def add_experiment(
    payload: dict[str, Any],
    checksums: dict[str, str],
    *,
    data_dir: Path | None = None,
) -> str:
    root = Path(data_dir) if data_dir is not None else DEFAULT_DATA_DIR
    con = connect(root)
    try:
        register_experiment(con, payload, checksums)
    finally:
        con.close()
    return payload["experiment_id"]


def build(
    *,
    k_max: int = 12,
    n_max: int = 1_000_000,
    n_begin: int = 1,
    backend: str = "auto",
    pe_n_max: int | None = None,
    data_dir: Path | None = None,
) -> dict[str, Any]:
    root = Path(data_dir) if data_dir is not None else DEFAULT_DATA_DIR
    root.mkdir(parents=True, exist_ok=True)
    start = utc_now()
    print(f"atlas build: census k_max={k_max} n_max={n_max} backend={backend}", flush=True)
    chosen, native_info, min_n, min_exp, end_at = _run_backend(
        k_max=k_max,
        n_max=n_max,
        n_begin=n_begin,
        backend=backend,
        data_dir=root,
    )
    source = SOURCE_KERNEL_A if chosen == "cuda" else SOURCE_CPU
    eid = make_experiment_id(chosen, k_max, n_max)
    exp_dir = root / "experiments" / eid
    if exp_dir.exists():
        raise FileExistsError(f"refusing to overwrite {exp_dir}")
    exp_dir.mkdir(parents=True)

    pe_limit = n_max if pe_n_max is None else pe_n_max
    print(f"atlas build: PE_CERTIFIED post-pass pe_n_max={pe_limit}", flush=True)
    pe = pe_certified_records(n_max=pe_limit, search_id=eid, pe_definition=PE_CERTIFIED)
    print(
        f"atlas build: PE blocks={len(pe['pe_certified'])} runs={len(pe['pe_run'])}",
        flush=True,
    )
    con = connect(root)
    try:
        word_count = ensure_words(con, k_max)
        realizer_count = write_realizers(
            con, eid, k_max, n_max, source, min_n, min_exp, end_at
        )
        pe_count = write_pe_records(
            con,
            eid,
            pe["pe_certified"] + pe["persistent"] + pe["pe_run"],
        )
        cont_count, fact_count = write_continuations_and_factors(con, eid, k_max)
    finally:
        con.close()

    parquet_paths = write_parquet_partitions(
        exp_dir, k_max, n_max, source, min_n, min_exp, end_at
    )
    found = sum(1 for v in min_n if v is not None)
    end = utc_now()
    payload = {
        "experiment_id": eid,
        "schema_version": SCHEMA_VERSION,
        "git_commit": git_commit(),
        "k_max": k_max,
        "n_max": n_max,
        "pe_n_max": pe_limit,
        "n_begin": n_begin,
        "backend": chosen,
        "realization_source": source,
        "pe_definition": PE_CERTIFIED,
        "kernel_version": "A",
        "start_time": start,
        "end_time": end,
        "native": native_info,
        "record_counts": {
            "words": word_count,
            "realizers": realizer_count,
            "realized": found,
            "not_found": realizer_count - found,
            "continuations": cont_count,
            "factors": fact_count,
            "pe_certified": len(pe["pe_certified"]),
            "persistent": len(pe["persistent"]),
            "pe_run": len(pe["pe_run"]),
            "pe_records": pe_count,
        },
        "search_limits": {"k_max": k_max, "n_begin": n_begin, "n_max": n_max},
        "itinerary_lengths": list(range(1, k_max + 1)),
        "manifest_path": str(exp_dir / "manifest.json"),
    }
    manifest_path, checksums = write_manifest(exp_dir, payload, parquet_paths)
    payload["checksums"] = checksums
    payload["manifest_path"] = str(manifest_path)
    add_experiment(payload, checksums, data_dir=root)
    return payload


def _run_backend(
    *,
    k_max: int,
    n_max: int,
    n_begin: int,
    backend: str,
    data_dir: Path,
) -> tuple[str, dict[str, Any] | None, list[int | None], list[int | None], list[int | None]]:
    want = backend
    binary = find_binary()
    if backend == "auto":
        want = "cuda" if binary is not None else "cpu"
        if binary is None:
            want = "cpu"
    if want in {"cuda", "native-cpu"} and binary is not None:
        native_backend = "cuda" if want == "cuda" else "cpu"
        dump = data_dir / "_native_tmp" / f"census-{native_backend}.tsv"
        info = run_census(
            k_max=k_max,
            n_max=n_max,
            n_begin=n_begin,
            backend=native_backend,
            output=dump,
            binary=binary,
        )
        parsed = parse_census_tsv(dump)
        min_n = parsed["min_n"]
        min_exp = parsed["min_exp"]
        assert isinstance(min_n, list) and isinstance(min_exp, list)
        if parsed.get("overflow_truncated"):
            raise ValueError(
                "native overflow cap was exceeded; raise overflow_cap or lower n_max"
            )
        overflow_n = list(parsed.get("overflow_n") or [])
        if overflow_n:
            merge_starts(min_n, min_exp, overflow_n, k_max=k_max)
        end_at = fill_end_states(min_n, k_max=k_max)
        info["overflow_count"] = parsed.get("overflow_count", 0)
        info["overflow_merged"] = len(overflow_n)
        print(
            f"atlas build: native {native_backend} overflow={info['overflow_count']} "
            f"merged={len(overflow_n)}",
            flush=True,
        )
        from research.juggler_sequence.atlas.packed import dense_index, pack_word

        if n_max >= 5 and k_max >= 3:
            idx = dense_index(*pack_word("OOE"))
            if min_n[idx] != 5:
                raise ValueError(f"OOE min_realizer is {min_n[idx]}, expected 5")
        return native_backend if want == "cuda" else "cpu", info, min_n, min_exp, end_at
    min_n, min_exp, end_at = census(k_max=k_max, n_max=n_max, n_begin=n_begin)
    return "cpu", None, min_n, min_exp, end_at


def find_min_realizer(
    word: str,
    *,
    experiment_id: str | None = None,
    data_dir: Path | None = None,
) -> dict[str, Any]:
    root = Path(data_dir) if data_dir is not None else DEFAULT_DATA_DIR
    rec = query_word_record(word, experiment_id=experiment_id, data_dir=root)
    rec["claim"] = (
        STATUS_FOUND if rec.get("realization_status") == STATUS_FOUND else STATUS_NOT_FOUND
    )
    return rec


def word_record(
    word: str,
    *,
    experiment_id: str | None = None,
    data_dir: Path | None = None,
) -> dict[str, Any]:
    root = Path(data_dir) if data_dir is not None else DEFAULT_DATA_DIR
    return query_word_record(word, experiment_id=experiment_id, data_dir=root)


def factor_complexity(
    language: str,
    r: int,
    *,
    experiment_id: str | None = None,
    data_dir: Path | None = None,
) -> int:
    root = Path(data_dir) if data_dir is not None else DEFAULT_DATA_DIR
    return query_factor_complexity(
        language, r, experiment_id=experiment_id, data_dir=root
    )


def factor_set(
    language: str,
    r: int,
    *,
    experiment_id: str | None = None,
    data_dir: Path | None = None,
) -> list[str]:
    root = Path(data_dir) if data_dir is not None else DEFAULT_DATA_DIR
    return query_factor_set(language, r, experiment_id=experiment_id, data_dir=root)


def continuation_mask(
    word: str,
    language: str,
    *,
    experiment_id: str | None = None,
    data_dir: Path | None = None,
) -> dict[str, Any]:
    root = Path(data_dir) if data_dir is not None else DEFAULT_DATA_DIR
    return query_continuation_mask(
        word, language, experiment_id=experiment_id, data_dir=root
    )


def pe_records(
    *,
    experiment_id: str | None = None,
    data_dir: Path | None = None,
    language_id: str = PE_CERTIFIED,
) -> list[dict[str, Any]]:
    root = Path(data_dir) if data_dir is not None else DEFAULT_DATA_DIR
    con = connect(root)
    try:
        from research.juggler_sequence.atlas.query import _latest_experiment

        eid = experiment_id or _latest_experiment(con)
        rows = con.execute(
            """
            SELECT word_id, min_n, end_state, scan_limit, pe_definition, a, b,
                   search_id, language_id
            FROM pe_records
            WHERE experiment_id = ? AND language_id = ?
            ORDER BY min_n
            """,
            (eid, language_id),
        ).fetchall()
        return [dict(row) for row in rows]
    finally:
        con.close()


def experiment_manifest(
    experiment_id: str | None = None,
    *,
    data_dir: Path | None = None,
) -> dict[str, Any]:
    root = Path(data_dir) if data_dir is not None else DEFAULT_DATA_DIR
    con = connect(root)
    try:
        from research.juggler_sequence.atlas.query import _latest_experiment

        eid = experiment_id or _latest_experiment(con)
        row = con.execute(
            "SELECT manifest_path FROM experiments WHERE experiment_id = ?",
            (eid,),
        ).fetchone()
        if row is None or not row[0]:
            raise ValueError(f"unknown experiment {eid}")
        path = Path(row[0])
        return json.loads(path.read_text(encoding="utf-8"))
    finally:
        con.close()


def validate(
    *,
    experiment_id: str | None = None,
    data_dir: Path | None = None,
    native_tsv: Path | None = None,
) -> dict[str, Any]:
    root = Path(data_dir) if data_dir is not None else DEFAULT_DATA_DIR
    native_min = None
    label = "native"
    if native_tsv is not None:
        parsed = parse_census_tsv(Path(native_tsv))
        native_min = parsed["min_n"]
        label = str(parsed.get("backend", "native"))
    report = validate_suite(native_min_n=native_min, native_label=label)
    binary = find_binary()
    if binary is not None and native_tsv is None:
        dump = root / "_native_tmp" / "validate-k6-n1000.tsv"
        try:
            last_err = None
            parsed = None
            for native_backend in ("cuda", "cpu"):
                try:
                    run_census(
                        k_max=6,
                        n_max=1000,
                        n_begin=1,
                        backend=native_backend,
                        output=dump,
                        binary=binary,
                    )
                    parsed = parse_census_tsv(dump)
                    break
                except Exception as exc:
                    last_err = exc
            if parsed is None:
                raise last_err or RuntimeError("native census failed")
            py_min, _, _ = census(k_max=6, n_max=1000)
            native_tbl = parsed["min_n"]
            assert isinstance(native_tbl, list)
            mismatches = [
                i for i, (a, b) in enumerate(zip(py_min, native_tbl, strict=True)) if a != b
            ]
            report["gpu_eq_cpu"] = not mismatches and parsed.get("overflow_count", 0) == 0
            report["native_mismatches"] = mismatches[:12]
            report["native_overflow"] = parsed.get("overflow_count", 0)
            if mismatches:
                report["ok"] = False
                report["errors"] = list(report.get("errors") or []) + [
                    f"native census disagrees with Python at {len(mismatches)} slots"
                ]
            if report.get("gpu_eq_cpu"):
                report["claims"] = list(report.get("claims") or []) + ["GPU VERIFIED"]
        except Exception as exc:
            report["native_error"] = str(exc)
    if sqlite_path_exists(root):
        from research.juggler_sequence.atlas.query import _latest_experiment

        con = connect(root)
        try:
            eid = experiment_id or _latest_experiment(con)
        finally:
            con.close()
        report["stored_metadata"] = stored_metadata_matches(root, eid)
        report["ok"] = report["ok"] and not report["stored_metadata"]
        report["experiment_id"] = eid
    return report


def sqlite_path_exists(data_dir: Path) -> bool:
    from research.juggler_sequence.atlas.storage import sqlite_path

    return sqlite_path(data_dir).is_file()


def benchmark(
    *,
    k_max: int = 8,
    n_max: int = 10_000,
    backend: str = "cpu",
) -> dict[str, Any]:
    import time

    t0 = time.perf_counter()
    chosen, native_info, min_n, _, _ = _run_backend(
        k_max=k_max,
        n_max=n_max,
        n_begin=1,
        backend=backend,
        data_dir=DEFAULT_DATA_DIR,
    )
    elapsed = time.perf_counter() - t0
    found = sum(1 for v in min_n if v is not None)
    return {
        "backend": chosen,
        "k_max": k_max,
        "n_max": n_max,
        "seconds": elapsed,
        "realized": found,
        "native": native_info,
    }


def continuations(
    language: str,
    *,
    experiment_id: str | None = None,
    data_dir: Path | None = None,
) -> list[dict[str, Any]]:
    root = Path(data_dir) if data_dir is not None else DEFAULT_DATA_DIR
    return continuation_histogram(language, experiment_id=experiment_id, data_dir=root)
