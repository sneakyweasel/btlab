"""Persistent research memory with isolated lanes."""

from __future__ import annotations

import json
from collections.abc import Iterable
from pathlib import Path
from typing import TYPE_CHECKING, Any

from research_engine.memory.cluster import cluster_failures
from research_engine.memory.policy import backlog_item, candidates_from_clusters
from research_engine.memory.retrieval import query_loot
from research_engine.memory.types import (
    ENGINE_MEMORY_VERSION,
    BlindPacket,
    EngineeringBacklogItem,
    EngineeringCandidate,
    FailureClass,
    FailureCluster,
    FailureRecord,
    GreyLoot,
    GreyLootKind,
    LootEvidence,
    MemoryExperiment,
    MemoryLane,
    Reconciliation,
    ScoutDossier,
)

if TYPE_CHECKING:
    from research_engine.attacks.result import AttackContext
    from research_engine.core.problem_spec import ProblemSpec
    from research_engine.diagnosis.loop import ResearchSession



class FinalizedError(RuntimeError):
    """Raised when a finalized experiment is mutated except via reconciliation."""


class ResearchMemory:
    """Lane-isolated store. Grey loot never enters the attack lane."""

    def __init__(
        self,
        experiments: Iterable[MemoryExperiment] = (),
        hypotheses: Iterable[Any] = (),
    ) -> None:
        self._experiments: dict[str, MemoryExperiment] = {}
        self._hypotheses: dict[str, Any] = {}
        self._certified: list[str] = [
            "piecewise_affine",
            "parameter_domain",
            "control_word",
            "control_obstruction",
            "vector_affine",
            "matrix_word_invariant",
        ]
        for item in experiments:
            self._experiments[item.experiment_id] = item
        for item in hypotheses:
            self._hypotheses[item.id] = item

    @property
    def experiments(self) -> tuple[MemoryExperiment, ...]:
        return tuple(self._experiments.values())

    def get(self, experiment_id: str) -> MemoryExperiment:
        return self._experiments[experiment_id]

    def hypotheses(self) -> tuple[Any, ...]:
        return tuple(self._hypotheses.values())

    def add_hypothesis(self, hypothesis: Any) -> None:
        """Store a strategy hypothesis. Never copies it into a BlindPacket."""

        self._hypotheses[hypothesis.id] = hypothesis

    def add(self, experiment: MemoryExperiment) -> None:
        existing = self._experiments.get(experiment.experiment_id)
        if existing is not None and existing.finalized:
            raise FinalizedError(f"{experiment.experiment_id} is finalized")
        self._experiments[experiment.experiment_id] = experiment

    def finalize(self, experiment_id: str) -> MemoryExperiment:
        current = self._experiments[experiment_id]
        if current.finalized:
            return current
        done = current.finalize()
        self._experiments[experiment_id] = done
        return done

    def reconcile(self, experiment_id: str, overlay: Reconciliation) -> MemoryExperiment:
        current = self._experiments[experiment_id]
        updated = current.with_reconciliation(overlay)
        self._experiments[experiment_id] = updated
        return updated

    def ingest(
        self,
        session: ResearchSession,
        spec: ProblemSpec,
        context: AttackContext,
        **kwargs: Any,
    ) -> MemoryExperiment:
        from research_engine.memory.ingest import experiment_from_session

        experiment = experiment_from_session(session, spec, context, **kwargs)
        self.add(experiment)
        return self.finalize(experiment.experiment_id)

    def lane(self, name: MemoryLane):
        if name is MemoryLane.SCOUT:
            return tuple(item.scout for item in self.experiments if item.scout is not None)
        if name is MemoryLane.ATTACK:
            return tuple(item.blind_packet for item in self.experiments if item.blind_packet is not None)
        if name is MemoryLane.GREY_LOOT:
            return self.grey_loot()
        if name is MemoryLane.CERTIFIED:
            return tuple(self._certified)
        raise KeyError(name)

    def scout_for(self, target: str) -> ScoutDossier | None:
        for item in self.experiments:
            if item.scout is not None and (item.scout.target == target or item.target == target):
                return item.scout
        return None

    def blind_packet_for(self, experiment_id: str) -> BlindPacket:
        packet = self._experiments[experiment_id].blind_packet
        if packet is None:
            raise KeyError(experiment_id)
        return packet

    def failures(self) -> tuple[FailureRecord, ...]:
        items: list[FailureRecord] = []
        for experiment in self.experiments:
            items.extend(experiment.failures)
        return tuple(items)

    def grey_loot(self) -> tuple[GreyLoot, ...]:
        items: list[GreyLoot] = []
        for experiment in self.experiments:
            items.extend(experiment.grey_loot)
        return tuple(items)

    def query_loot(
        self,
        *,
        kind: GreyLootKind | None = None,
        failure_class: FailureClass | None = None,
        bottleneck: str | None = None,
        evidence: LootEvidence | None = None,
        target: str | None = None,
    ) -> tuple[GreyLoot, ...]:
        return query_loot(
            self.grey_loot(),
            kind=kind,
            failure_class=failure_class,
            bottleneck=bottleneck,
            evidence=evidence,
            target=target,
        )

    def clusters(self) -> tuple[FailureCluster, ...]:
        semantic = {
            item.experiment_id: item.diagnosis.semantic_class for item in self.experiments
        }
        semantic.update({item.target: item.diagnosis.semantic_class for item in self.experiments})
        return cluster_failures(self.failures(), semantic_class_of=semantic)

    def engineering_candidates(self) -> tuple[EngineeringCandidate, ...]:
        return candidates_from_clusters(self.clusters())

    def engineering_backlog(self) -> tuple[EngineeringBacklogItem, ...]:
        return tuple(backlog_item(item) for item in self.clusters())

    def named_clusters(self):
        from research_engine.memory.named_clusters import named_failure_clusters

        return named_failure_clusters(self)

    def yield_corpus(self):
        from research_engine.memory.board import yield_corpus

        return yield_corpus(self)

    def assemble_board(self, corpus=None):
        from research_engine.memory.board import assemble_board

        return assemble_board(self, corpus)

    def as_dict(self) -> dict[str, Any]:
        return {
            "engine_version": ENGINE_MEMORY_VERSION,
            "experiments": [item.as_dict() for item in self.experiments],
            "certified": list(self._certified),
            "hypotheses": [
                item.as_dict() if hasattr(item, "as_dict") else dict(item)
                for item in self.hypotheses()
            ],
        }

    def to_json(self, path: Path) -> None:
        path.write_text(json.dumps(self.as_dict(), indent=2) + "\n", encoding="utf-8")

    @classmethod
    def from_dict(cls, data: dict[str, Any]) -> ResearchMemory:
        experiments = tuple(MemoryExperiment.from_dict(item) for item in (data.get("experiments") or ()))
        raw_hyps = data.get("hypotheses") or ()
        hypotheses = []
        if raw_hyps:
            from research_engine.strategy.types import ResearchHypothesis

            hypotheses = [ResearchHypothesis.from_dict(item) for item in raw_hyps]
        memory = cls(experiments, hypotheses)
        certified = data.get("certified")
        if certified:
            memory._certified = list(certified)
        return memory

    @classmethod
    def from_json_path(cls, path: Path) -> ResearchMemory:
        data = json.loads(path.read_text(encoding="utf-8"))
        return cls.from_dict(data)
