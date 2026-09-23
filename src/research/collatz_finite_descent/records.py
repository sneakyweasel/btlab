"""Persistent attack records. Not the named theorem ledger."""

from __future__ import annotations

from collections.abc import Sequence
from pathlib import Path

from research.experiments.paths import collatz_data_dir
from research.experiments.provenance import write_manifest
from research_engine.attacks.result import AttackResult, AttackStatus
from research_engine.core.semantics import SearchScope
from research_engine.planner.orchestrator import PlannerReport
from research_engine.verification.targets import TheoremTarget

RECORD_DIR = collatz_data_dir() / "finite_descent"


def record_status(result: AttackResult, *, lean_theorem: str = "") -> str:
    if result.status is AttackStatus.REFUTED:
        return "REFUTED"
    if result.status is AttackStatus.OBSERVATION:
        return "OBSERVED"
    if result.status is AttackStatus.INCONCLUSIVE:
        return "OBSERVED"
    if result.status is AttackStatus.INAPPLICABLE:
        return "OBSERVED"
    if lean_theorem:
        return "LEAN_VERIFIED"
    if result.status is AttackStatus.SUPPORTED and result.scope is SearchScope.EXACT:
        return "EXACT"
    if result.status is AttackStatus.SUPPORTED:
        return "SUPPORTED"
    return "OBSERVED"


def render_record(
    result: AttackResult,
    *,
    problem: str = "collatz_finite_descent",
    lean_theorem: str = "",
) -> str:
    evidence = "; ".join(
        f"{key}={result.evidence[key]}"
        for key in (
            "union_size",
            "complete",
            "horizon",
            "state_cap",
            "leak_count",
            "observed_bound",
        )
        if key in result.evidence
    )
    counters = repr(tuple(result.counterexamples[:4]))
    return (
        f"problem: {problem}\n"
        f"attack: {result.name}\n"
        f"claim: {result.claim}\n"
        f"status: {record_status(result, lean_theorem=lean_theorem)}\n"
        f"scope: {result.scope.value}\n"
        f"evidence: {evidence}\n"
        f"counterexamples: {counters}\n"
        f"lean_theorem: {lean_theorem}\n"
    )


def write_records(
    report: PlannerReport,
    targets: Sequence[TheoremTarget],
    *,
    directory: Path | None = None,
    problem: str = "collatz_finite_descent",
) -> tuple[Path, ...]:
    folder = directory if directory is not None else RECORD_DIR
    folder.mkdir(parents=True, exist_ok=True)
    linked = {target.attack: target for target in targets if target.linked}
    written: list[Path] = []
    for result in report.results:
        target = linked.get(result.name)
        lean = ""
        if target is not None:
            lean = f"{target.lean_module}.{target.lean_theorem}"
        path = folder / f"{result.name}.yaml"
        path.write_text(
            render_record(result, problem=problem, lean_theorem=lean),
            encoding="utf-8",
        )
        written.append(path)
    skipped_lines = [
        f"problem: {problem}",
        "attack: skipped",
        "claim: inapplicable or deferred",
        "status: OBSERVED",
        "scope: BOUNDED",
        "evidence: "
        + "; ".join(f"{item.attack}={item.reason}" for item in report.skipped),
        "counterexamples: ()",
        "lean_theorem: ",
    ]
    skip_path = folder / "skipped.yaml"
    skip_path.write_text("\n".join(skipped_lines) + "\n", encoding="utf-8")
    written.append(skip_path)
    write_manifest(folder / "records.research.json", programme="collatz",
                   research_id="collatz/finite_descent", outputs=written,
                   scope="Planner records; each YAML retains its own scope. No termination claim.",
                   parameters={"problem": problem}, sources=[Path(__file__)])
    return tuple(written)
