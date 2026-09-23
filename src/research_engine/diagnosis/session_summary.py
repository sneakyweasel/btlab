"""Extract campaign summaries from a ResearchSession. Not a second ledger."""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import Any

from research_engine.attacks.result import AttackResult
from research_engine.diagnosis.loop import ResearchSession
from research_engine.report import branch_status_for


def _by_name(session: ResearchSession) -> dict[str, AttackResult]:
    return {item.name: item for item in session.attack_report.results}


def _skipped_names(session: ResearchSession) -> tuple[str, ...]:
    return tuple(item.attack for item in session.attack_report.skipped)


@dataclass(frozen=True)
class SessionSummary:
    target: str
    decision: str
    decision_reason: str
    branch_status: str
    family_status: str
    family_id: str
    nearest_target: str
    delta_level: str
    semantic_class: str
    fingerprint: dict[str, str]
    exercised: tuple[str, ...]
    skipped: tuple[str, ...]
    census_kind: str
    family: dict[str, Any] | None
    domain_direction: str
    obstruction_scopes: tuple[str, ...]
    strongest_exact: str
    strongest_falsification: str
    extra: dict[str, Any] = field(default_factory=dict)

    def as_dict(self) -> dict[str, Any]:
        return {
            "target": self.target,
            "decision": self.decision,
            "decision_reason": self.decision_reason,
            "branch_status": self.branch_status,
            "family_status": self.family_status,
            "family_id": self.family_id,
            "nearest_target": self.nearest_target,
            "delta_level": self.delta_level,
            "semantic_class": self.semantic_class,
            "fingerprint": self.fingerprint,
            "exercised": self.exercised,
            "skipped": self.skipped,
            "census_kind": self.census_kind,
            "family": self.family,
            "domain_direction": self.domain_direction,
            "obstruction_scopes": self.obstruction_scopes,
            "strongest_exact": self.strongest_exact,
            "strongest_falsification": self.strongest_falsification,
            "extra": self.extra,
        }


def summarize_session(session: ResearchSession, extra: dict[str, Any] | None = None) -> SessionSummary:
    results = _by_name(session)
    census = results.get("piecewise_affine") or results.get("vector_affine")
    family = None
    census_kind = ""
    if census is not None:
        census_kind = str(census.evidence.get("census_kind") or "")
        raw = census.evidence.get("family")
        family = dict(raw) if isinstance(raw, dict) else None
    domain = results.get("parameter_domain")
    direction = ""
    if domain is not None:
        domains = domain.evidence.get("domains") or ()
        for item in domains:
            if isinstance(item, dict) and item.get("direction"):
                direction = str(item.get("direction"))
                break
    if not direction and results.get("vector_affine") is not None:
        for item in results["vector_affine"].evidence.get("domains") or ():
            if isinstance(item, dict) and item.get("direction"):
                direction = str(item.get("direction"))
                break
    obstructed = results.get("control_obstruction")
    scopes: list[str] = []
    if obstructed is not None:
        for cert in obstructed.evidence.get("certificates") or ():
            if isinstance(cert, dict) and cert.get("scope"):
                scopes.append(str(cert["scope"]))
    if not scopes and results.get("vector_affine") is not None:
        for cert in results["vector_affine"].evidence.get("certificates") or ():
            if isinstance(cert, dict) and cert.get("scope"):
                scopes.append(str(cert["scope"]))
    diagnosis = session.diagnosis
    delta = diagnosis.delta
    return SessionSummary(
        target=session.record.target,
        decision=session.decision.value,
        decision_reason=session.decision_reason,
        branch_status=branch_status_for(session.decision),
        family_status=diagnosis.family_status.value,
        family_id=diagnosis.family_id,
        nearest_target=diagnosis.nearest_target,
        delta_level="" if delta is None else delta.level.value,
        semantic_class=diagnosis.semantic_class,
        fingerprint=diagnosis.fingerprint.as_dict(),
        exercised=diagnosis.coverage.exercised(),
        skipped=_skipped_names(session),
        census_kind=census_kind,
        family=family,
        domain_direction=direction,
        obstruction_scopes=tuple(dict.fromkeys(scopes)),
        strongest_exact=session.record.strongest_exact,
        strongest_falsification=session.record.strongest_falsification,
        extra=extra or {},
    )
