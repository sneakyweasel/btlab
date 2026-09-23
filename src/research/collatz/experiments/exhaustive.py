"""Reproducible exhaustive experiment A: odd n up to a configurable limit.

Stores JSON metadata and optional JSONL rows. No statistical claim is a
theorem. This experiment records exact feature transitions and verifies
the weight-parity bridge on the scanned range.
"""

from __future__ import annotations

import json
from dataclasses import dataclass, field
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from research.collatz.invariants import check_odd_weight, check_three_n_plus_one_even_weight
from research.collatz.transitions import ROW_COLUMNS, feature_transition
from research.experiments.provenance import write_manifest
from research.experiments.table_io import timestamp as output_timestamp


def code_version() -> str | None:
    try:
        from importlib.metadata import version

        return version("balanced-ternary")
    except Exception:
        return None


@dataclass
class ExhaustiveExperimentResult:
    experiment_name: str
    parameters: dict[str, Any]
    integer_range: str
    timestamp: str
    code_version: str | None
    checked: int
    weight_parity_failures: int
    ternary_shift_failures: int
    rows_written: int
    output_metadata: str | None = None
    output_rows: str | None = None
    sample_rows: list[dict[str, object]] = field(default_factory=list)

    def to_metadata(self) -> dict[str, Any]:
        return {
            "experiment_name": self.experiment_name,
            "parameters": self.parameters,
            "integer_range": self.integer_range,
            "timestamp": self.timestamp,
            "code_version": self.code_version,
            "checked": self.checked,
            "weight_parity_failures": self.weight_parity_failures,
            "ternary_shift_failures": self.ternary_shift_failures,
            "rows_written": self.rows_written,
            "schema": list(ROW_COLUMNS),
            "claim_status": {
                "weight_parity_on_this_range": (
                    "COMPUTATIONALLY VERIFIED"
                    if self.weight_parity_failures == 0
                    else "FAILED"
                ),
                "theorem_status": (
                    "The identity n mod 2 = weight(BT(n)) mod 2 is EXACT — HUMAN PROOF; "
                    "this experiment only re-checks it on a finite odd range."
                ),
            },
        }


def run_exhaustive_experiment(
    limit: int,
    output_dir: Path | str | None = None,
    sample_size: int = 5,
) -> ExhaustiveExperimentResult:
    """Scan every odd ``n`` with ``1 <= n <= limit``.

    If ``output_dir`` is given, write ``raw/*.jsonl`` and ``reports/*.json``.
    """
    if isinstance(limit, bool) or not isinstance(limit, int) or limit < 1:
        raise ValueError(f"limit must be an integer >= 1, got {limit!r}")

    timestamp = output_timestamp()
    result = ExhaustiveExperimentResult(
        experiment_name="exhaustive_feature_transitions",
        parameters={"limit": limit, "sample_size": sample_size},
        integer_range=f"odd n in [1, {limit}]",
        timestamp=datetime.now(timezone.utc).isoformat(),
        code_version=code_version(),
        checked=0,
        weight_parity_failures=0,
        ternary_shift_failures=0,
        rows_written=0,
    )

    rows_path: Path | None = None
    meta_path: Path | None = None
    rows_fh = None
    if output_dir is not None:
        base = Path(output_dir)
        raw = base / "raw"
        reports = base / "reports"
        raw.mkdir(parents=True, exist_ok=True)
        reports.mkdir(parents=True, exist_ok=True)
        (base / "derived").mkdir(parents=True, exist_ok=True)
        rows_path = raw / f"exhaustive_limit{limit}_{timestamp}.jsonl"
        meta_path = reports / f"exhaustive_limit{limit}_{timestamp}.json"
        rows_fh = rows_path.open("w", encoding="utf-8")

    try:
        for n in range(1, limit + 1, 2):
            trans = feature_transition(n)
            result.checked += 1
            if not check_odd_weight(n) or not check_three_n_plus_one_even_weight(n):
                result.weight_parity_failures += 1
            if not trans.ternary_shift_add_one_matches:
                result.ternary_shift_failures += 1
            row = trans.to_row()
            _jsonable = _to_jsonable(row)
            if len(result.sample_rows) < sample_size:
                result.sample_rows.append(_jsonable)
            if rows_fh is not None:
                rows_fh.write(json.dumps(_jsonable, separators=(",", ":")) + "\n")
                result.rows_written += 1
    finally:
        if rows_fh is not None:
            rows_fh.close()

    if meta_path is not None:
        payload = result.to_metadata()
        payload["sample_rows"] = result.sample_rows
        if rows_path is not None:
            payload["rows_path"] = str(rows_path)
        meta_path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")
        result.output_metadata = str(meta_path)
        result.output_rows = str(rows_path) if rows_path is not None else None
        write_manifest(meta_path.with_suffix(".research.json"), programme="collatz",
                       research_id="collatz/overview",
                       scope=f"Feature transitions for odd n in [1, {limit}]; finite computation only.",
                       parameters=result.parameters, outputs=[meta_path, rows_path],
                       artifact_root=Path(output_dir))

    return result


def _to_jsonable(row: dict[str, object]) -> dict[str, object]:
    out: dict[str, object] = {}
    for key, value in row.items():
        if isinstance(value, tuple):
            out[key] = list(value)
        else:
            out[key] = value
    return out
