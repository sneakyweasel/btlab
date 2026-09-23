"""Helpers to write experiment tables as JSONL, plus Parquet when available."""

from __future__ import annotations

import json
import re
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Sequence
from uuid import uuid4

from research.experiments.schema import ExperimentManifest
from research.experiments.provenance import write_manifest


def timestamp() -> str:
    return datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%S%fZ") + "_" + uuid4().hex[:8]


def _write_rows(
    rows: Sequence[dict[str, Any]],
    output_dir: Path | str,
    stem: str,
) -> dict[str, str]:
    """Write JSONL always. Write Parquet if pyarrow is installed."""
    if not re.fullmatch(r"[A-Za-z0-9][A-Za-z0-9_.-]*", stem):
        raise ValueError("stem must be a simple filename component")
    base = Path(output_dir)
    raw = base / "raw"
    raw.mkdir(parents=True, exist_ok=True)
    stamp = timestamp()
    jsonl_path = raw / f"{stem}_{stamp}.jsonl"
    with jsonl_path.open("w", encoding="utf-8", newline="\n") as fh:
        for row in rows:
            fh.write(json.dumps(row, separators=(",", ":")) + "\n")
    paths = {"jsonl": str(jsonl_path)}
    try:
        import pyarrow as pa
        import pyarrow.parquet as pq

        table = pa.Table.from_pylist(list(rows))
        parquet_path = raw / f"{stem}_{stamp}.parquet"
        pq.write_table(table, parquet_path)
        paths["parquet"] = str(parquet_path)
    except ImportError:
        paths["parquet"] = ""
    return paths


def write_rows(rows: Sequence[dict[str, Any]], output_dir: Path | str, stem: str,
               *, parameters: dict | None = None, scope: str | None = None,
               programme: str = "collatz", research_id: str | None = None) -> dict[str, str]:
    """Write table files and a portable provenance sidecar for this finite output."""
    paths = _write_rows(rows, output_dir, stem)
    path = Path(paths["jsonl"]).with_suffix(".research.json")
    write_manifest(path, programme=programme,
                   research_id=research_id or ("collatz/overview" if programme == "collatz" else None),
                   scope=scope or f"Finite exported table: {stem}, {len(rows)} rows; no global claim.",
                   parameters=parameters, outputs=[Path(p) for p in paths.values() if p])
    paths["provenance"] = str(path)
    return paths


def read_jsonl(path: Path | str) -> list[dict[str, Any]]:
    """Read rows written by ``write_rows``."""
    rows: list[dict[str, Any]] = []
    with Path(path).open("r", encoding="utf-8") as fh:
        for line in fh:
            if line.strip():
                rows.append(json.loads(line))
    return rows


def write_experiment(
    rows: Sequence[dict[str, Any]],
    output_dir: Path | str,
    stem: str,
    manifest: ExperimentManifest,
) -> dict[str, str]:
    """Write data artifacts plus a reproducibility manifest."""
    if manifest.row_count != len(rows):
        raise ValueError("manifest row_count does not match rows")
    paths = _write_rows(rows, output_dir, stem)
    jsonl_path = Path(paths["jsonl"])
    manifest_path = jsonl_path.with_name(
        jsonl_path.name.removesuffix(".jsonl") + "_manifest.json"
    )
    manifest_payload = manifest.as_dict()
    manifest_payload["created_utc"] = datetime.now(timezone.utc).isoformat()
    manifest_payload["artifacts"] = paths
    manifest_path.write_text(
        json.dumps(manifest_payload, indent=2, sort_keys=True),
        encoding="utf-8",
        newline="\n",
    )
    paths["manifest"] = str(manifest_path)
    provenance = jsonl_path.with_suffix(".research.json")
    write_manifest(provenance, programme="collatz", research_id="collatz/overview",
                   scope=f"{len(rows)} finite rows. {manifest.claim_status}",
                   parameters=manifest.parameters, outputs=[Path(p) for p in paths.values() if p])
    paths["provenance"] = str(provenance)
    return paths
