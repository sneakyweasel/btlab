"""Persistent attack records for the Syracuse engine stress test."""

from __future__ import annotations

from collections.abc import Sequence
from pathlib import Path

from research.experiments.paths import collatz_data_dir
from research_engine.planner.hypothesis import PriorArtStatus
from research_engine.planner.orchestrator import PlannerReport
from research_engine.planner.records import write_records as write_engine_records
from research_engine.verification.targets import TheoremTarget

RECORD_DIR = collatz_data_dir() / "syracuse"


def write_records(
    report: PlannerReport,
    targets: Sequence[TheoremTarget],
    *,
    directory: Path | None = None,
    problem: str = "syracuse",
) -> tuple[Path, ...]:
    folder = directory if directory is not None else RECORD_DIR
    return write_engine_records(
        report,
        targets,
        directory=folder,
        problem=problem,
        prior_art_status=PriorArtStatus.KNOWN.value,
        novelty_note="engine diagnosis of accelerated odd-only map; not a Collatz proof",
        branch_status="PARK",
    )
