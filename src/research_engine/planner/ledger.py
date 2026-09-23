"""In-memory experimental ledger. Not the named theorem ledger."""

from __future__ import annotations

from dataclasses import dataclass, field

from research_engine.attacks.result import AttackResult, AttackStatus
from research_engine.core.semantics import SearchScope
from research_engine.planner.hypothesis import DecisionKind, Hypothesis, HypothesisStatus, PriorArtStatus
from research_engine.planner.negative import NegativeKnowledge


class LedgerError(ValueError):
    """Illegal promote/refute across claim kinds or scopes."""


@dataclass
class ResearchLedger:
    """Hypotheses and attack outcomes for one experimental session.

    This does not write the canonical topic claims in ``docs/claims/``.
    Named theorem records belong there.
    """

    knowledge: NegativeKnowledge = field(default_factory=NegativeKnowledge)
    hypotheses: dict[str, Hypothesis] = field(default_factory=dict)
    attacks: list[AttackResult] = field(default_factory=list)
    decisions: list[tuple[str, DecisionKind, str]] = field(default_factory=list)

    def add_hypothesis(self, hypothesis: Hypothesis) -> None:
        self.hypotheses[hypothesis.id] = hypothesis

    def record_attack(self, result: AttackResult) -> None:
        self.attacks.append(result)

    def get(self, hyp_id: str) -> Hypothesis:
        try:
            return self.hypotheses[hyp_id]
        except KeyError as exc:
            raise LedgerError(f"unknown hypothesis {hyp_id!r}") from exc

    def decide(
        self,
        hyp_id: str,
        decision: DecisionKind,
        reason: str,
        *,
        from_result: AttackResult | None = None,
        superseded_by: str = "",
    ) -> Hypothesis:
        hyp = self.get(hyp_id)
        if from_result is not None:
            blocked = self.knowledge.forbids_kinds(from_result.kind, hyp.kind)
            if blocked is not None:
                raise LedgerError(blocked.statement)
            if from_result.kind is not hyp.kind:
                raise LedgerError(
                    f"{from_result.kind.value} evidence cannot decide {hyp.kind.value}"
                )
            if (
                decision is DecisionKind.PROMOTE
                and hyp.intended_scope is SearchScope.EXACT
                and from_result.scope is not SearchScope.EXACT
            ):
                raise LedgerError("BOUNDED evidence cannot PROMOTE an EXACT hypothesis")
            if decision is DecisionKind.PROMOTE and from_result.status is not AttackStatus.SUPPORTED:
                raise LedgerError("only SUPPORTED exact evidence can PROMOTE")
        if decision is DecisionKind.PROMOTE and hyp.prior_art_status is PriorArtStatus.UNKNOWN:
            raise LedgerError("PROMOTE requires a populated prior-art status")
        status = _status_for(decision, hyp.status)
        updated = Hypothesis(
            id=hyp.id,
            statement=hyp.statement,
            kind=hyp.kind,
            intended_scope=hyp.intended_scope,
            status=status,
            problem=hyp.problem,
            evidence=reason,
            superseded_by=superseded_by or hyp.superseded_by,
            prior_art_status=hyp.prior_art_status,
            novelty_note=hyp.novelty_note,
        )
        self.hypotheses[hyp.id] = updated
        self.decisions.append((hyp.id, decision, reason))
        return updated


def _status_for(decision: DecisionKind, current: HypothesisStatus) -> HypothesisStatus:
    if decision is DecisionKind.PROMOTE:
        if current is HypothesisStatus.SETTLED:
            return HypothesisStatus.SETTLED
        return HypothesisStatus.SUPPORTED
    if decision is DecisionKind.REFUTE:
        return HypothesisStatus.REFUTED
    if decision is DecisionKind.PARK:
        return HypothesisStatus.PARKED
    if decision is DecisionKind.CLOSE:
        return HypothesisStatus.CLOSED
    return HypothesisStatus.CLOSED
