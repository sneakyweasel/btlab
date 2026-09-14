"""Immutable v2.3 baseline. Normal v2.4 workflows never write these files."""

from __future__ import annotations

import hashlib
import json
from dataclasses import dataclass
from pathlib import Path
from typing import Any

from research_engine.control.types import (
    BASELINE_IDENTIFIER,
    ENGINE_CONTROL_VERSION,
    V2_3_CAMPAIGN_ORDER,
)
from research_engine.law import ENGINE_LAW_VERSION
from research_engine.memory.store import BOARD_PATH, SEED_PATH, ResearchMemory
from research_engine.memory.types import ENGINE_MEMORY_VERSION, MemoryExperiment, TargetBoard
from research_engine.planner.orchestrator import DEFAULT_ATTACK_ORDER, DEFERRED_ATTACKS
from research_engine.quantifiers import ENGINE_QUANTIFIER_VERSION
from research_engine.reasoning import ENGINE_REASONING_VERSION
from research_engine.strategy import ENGINE_STRATEGY_VERSION
from research_engine.strategy.capabilities import (
    GLOBAL_INDUCTIVE_CHAIN,
    LAW_DOMAIN_CHAIN,
    QUANTIFIER_PROBE_CHAIN,
)

MANIFEST_PATH = Path(__file__).resolve().parent / "manifest.json"


class BaselineImmutableError(RuntimeError):
    """Raised when a v2.4 workflow attempts to mutate the frozen baseline."""


def sha256_file(path: Path) -> str:
    """Digest the seed's *content*, not its line endings.

    The freeze protects what the v2.3 baseline says, and that is the same text
    on every platform. Hashing raw bytes made it platform-dependent instead:
    this repository is checked out with core.autocrlf on Windows, so the seed
    files are CRLF in a Windows working tree and LF in the stored blob, and the
    recorded digests -- computed on Windows -- were rejected everywhere else.
    CI failed 39 tests with BaselineImmutableError on 14 September 2026 for
    exactly that reason, the first time it ever got far enough to run them.

    Normalising first, the way tools/build_paper_a.py already digests text,
    makes the freeze mean what it claims. The recorded hashes in manifest.json
    move once, to the normalised digest of byte-identical content: parsing both
    encodings yields equal JSON, and the size difference is exactly the CRLF
    count.
    """

    digest = hashlib.sha256()
    digest.update(path.read_bytes().replace(b"\r\n", b"\n").replace(b"\r", b"\n"))
    return digest.hexdigest()


def expected_manifest() -> dict[str, Any]:
    return {
        "identifier": BASELINE_IDENTIFIER,
        "engine_control_version": ENGINE_CONTROL_VERSION,
        "files": {
            "historical.json": sha256_file(SEED_PATH),
            "target_board.json": sha256_file(BOARD_PATH),
        },
        "campaign_order": list(V2_3_CAMPAIGN_ORDER),
        "default_attack_order": list(DEFAULT_ATTACK_ORDER),
        "deferred_attacks": list(DEFERRED_ATTACKS),
        "engine_versions": {
            "memory": ENGINE_MEMORY_VERSION,
            "strategy": ENGINE_STRATEGY_VERSION,
            "reasoning": ENGINE_REASONING_VERSION,
            "law": ENGINE_LAW_VERSION,
            "quantifier": ENGINE_QUANTIFIER_VERSION,
        },
        "skip_decisions": {
            "global_inductive_chain_attacks": list(GLOBAL_INDUCTIVE_CHAIN.attacks),
            "law_domain_chain_attacks": list(LAW_DOMAIN_CHAIN.attacks),
            "quantifier_probe_chain_attacks": list(QUANTIFIER_PROBE_CHAIN.attacks),
        },
    }


def load_manifest() -> dict[str, Any]:
    return json.loads(MANIFEST_PATH.read_text(encoding="utf-8"))


def verify_manifest(manifest: dict[str, Any] | None = None) -> dict[str, Any]:
    recorded = manifest if manifest is not None else load_manifest()
    live = expected_manifest()
    if recorded["identifier"] != BASELINE_IDENTIFIER:
        raise BaselineImmutableError("baseline identifier mismatch")
    if recorded["files"] != live["files"]:
        raise BaselineImmutableError(
            "v2.3 seed hashes changed; freeze is immutable from normal v2.4 workflows"
        )
    if recorded["campaign_order"] != live["campaign_order"]:
        raise BaselineImmutableError("v2.3 campaign order changed")
    if recorded["default_attack_order"] != live["default_attack_order"]:
        raise BaselineImmutableError("DEFAULT_ATTACK_ORDER thawed")
    if recorded["deferred_attacks"] != live["deferred_attacks"]:
        raise BaselineImmutableError("DEFERRED_ATTACKS changed")
    if recorded["engine_versions"] != live["engine_versions"]:
        raise BaselineImmutableError("frozen engine versions changed")
    if recorded["skip_decisions"] != live["skip_decisions"]:
        raise BaselineImmutableError("frozen skip decisions changed")
    return recorded


class FrozenResearchMemory(ResearchMemory):
    """Load-only memory. add/ingest/to_json raise."""

    def add(self, experiment: MemoryExperiment) -> None:
        raise BaselineImmutableError("cannot add to RESEARCH_ENGINE_V2_3_BASELINE")

    def finalize(self, experiment_id: str) -> MemoryExperiment:
        raise BaselineImmutableError("cannot finalize RESEARCH_ENGINE_V2_3_BASELINE")

    def ingest(self, *args: Any, **kwargs: Any) -> MemoryExperiment:
        raise BaselineImmutableError("cannot ingest into RESEARCH_ENGINE_V2_3_BASELINE")

    def reconcile(self, experiment_id: str, overlay) -> MemoryExperiment:
        raise BaselineImmutableError("cannot reconcile RESEARCH_ENGINE_V2_3_BASELINE")

    def to_json(self, path: Path) -> None:
        raise BaselineImmutableError("cannot write RESEARCH_ENGINE_V2_3_BASELINE")


@dataclass(frozen=True)
class FrozenBaseline:
    identifier: str
    memory: FrozenResearchMemory
    board: TargetBoard
    attack_order: tuple[str, ...]
    deferred_attacks: tuple[str, ...]
    campaign_order: tuple[str, ...]
    manifest: dict[str, Any]

    def experiment(self, experiment_id: str) -> MemoryExperiment:
        return self.memory.get(experiment_id)

    def find_experiment(self, name: str) -> MemoryExperiment:
        try:
            return self.memory.get(name)
        except KeyError:
            for item in self.memory.experiments:
                if item.target == name or item.experiment_id == name:
                    return item
        raise KeyError(name)


def load_v2_3_baseline(*, verify: bool = True) -> FrozenBaseline:
    manifest = load_manifest()
    if verify:
        verify_manifest(manifest)
    memory = FrozenResearchMemory.from_json_path(SEED_PATH)
    board = TargetBoard.from_dict(json.loads(BOARD_PATH.read_text(encoding="utf-8")))
    return FrozenBaseline(
        identifier=BASELINE_IDENTIFIER,
        memory=memory,
        board=board,
        attack_order=tuple(DEFAULT_ATTACK_ORDER),
        deferred_attacks=tuple(DEFERRED_ATTACKS),
        campaign_order=V2_3_CAMPAIGN_ORDER,
        manifest=manifest,
    )


def write_manifest(path: Path | None = None) -> dict[str, Any]:
    """Explicit freeze helper. Not called by campaign runners."""

    payload = expected_manifest()
    target = path if path is not None else MANIFEST_PATH
    target.parent.mkdir(parents=True, exist_ok=True)
    target.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")
    return payload


__all__ = [
    "BASELINE_IDENTIFIER",
    "BaselineImmutableError",
    "FrozenBaseline",
    "FrozenResearchMemory",
    "MANIFEST_PATH",
    "expected_manifest",
    "load_manifest",
    "load_v2_3_baseline",
    "sha256_file",
    "verify_manifest",
    "write_manifest",
]
