"""Replay isolation and comparison. Historical records stay immutable."""

from __future__ import annotations

from dataclasses import replace

import pytest

from research_engine.control.baseline import BaselineImmutableError, load_v2_3_baseline
from research_engine.control.replay import (
    assert_already_run_unchanged,
    assert_blind_excludes_historical,
    recover_historical,
    replay_campaign_id,
    run_replay,
)
from research_engine.control.store import ControlStore
from research_engine.control.types import CampaignType, COMPARISON_DIMENSIONS, REPLAY_V22_TARGETS
from research_engine.memory.store import BOARD_PATH, SEED_PATH
from research_engine.memory.types import BlindPacket, MemoryExperiment


def _isolated_clone(historical: MemoryExperiment, source_target_id: str) -> MemoryExperiment:
    packet = historical.blind_packet or BlindPacket(spec_name=historical.target)
    payload = packet.attack_payload()
    blind = BlindPacket(
        spec_name=str(payload["spec_name"]),
        dimension=payload.get("dimension"),
        skip_attacks=tuple(payload.get("skip_attacks") or ()),
        max_states=payload.get("max_states"),
        max_steps=payload.get("max_steps"),
        allowed_definition=str(payload.get("allowed_definition") or ""),
        state_space=str(payload.get("state_space") or ""),
        observation=str(payload.get("observation") or ""),
        initial_conditions=tuple(payload.get("initial_conditions") or ()),
        explicit_controls=str(payload.get("explicit_controls") or ""),
        computational_budget=str(payload.get("computational_budget") or ""),
    )
    return replace(
        historical,
        experiment_id=replay_campaign_id(source_target_id),
        grey_loot=(),
        scout=None,
        prior_art=None,
        blind_packet=blind,
        engine_version="0.2.7",
    )


def test_replay_ids_are_distinct():
    assert replay_campaign_id("skolem_order2_known_zero") == "replay_v22_skolem_order2_known_zero"
    assert replay_campaign_id("skolem_order2_known_zero") != "skolem_order2_known_zero"


def test_historical_already_run_stays_true_under_replay_protocol():
    baseline = load_v2_3_baseline()
    for name in REPLAY_V22_TARGETS:
        assert_already_run_unchanged(baseline.board, name)
        historical = recover_historical(baseline, name)
        clone = _isolated_clone(historical, name)
        assert_blind_excludes_historical(clone.blind_packet, historical)
        store = ControlStore()
        record = run_replay(baseline, name, lambda source: _isolated_clone(historical, source), store=store)
        assert record.campaign_id == replay_campaign_id(name)
        assert record.campaign_type is CampaignType.REPLAY
        assert record.replay_metadata is not None
        assert record.replay_metadata.source_engine == "v2.2"
        assert record.replay_metadata.execution_engine == "v2.4_control_v2.3"
        assert record.replay_metadata.source_target_id == name
        assert record.comparison is not None
        assert set(record.comparison.dimensions) == set(COMPARISON_DIMENSIONS)
        assert record.comparison.v2_4_added_information
        assert baseline.board.by_name()[name].already_run is True
        assert baseline.memory.get(historical.experiment_id).experiment_id == historical.experiment_id


def test_replay_does_not_write_historical_seed(tmp_path):
    store = ControlStore()
    with pytest.raises(RuntimeError):
        store.to_json(SEED_PATH)
    with pytest.raises(RuntimeError):
        store.to_json(BOARD_PATH)
    path = tmp_path / "overlay.json"
    store.to_json(path)
    assert path.exists()


def test_baseline_cannot_ingest_a_replay():
    baseline = load_v2_3_baseline()
    historical = recover_historical(baseline, "skolem_order2_known_zero")
    clone = _isolated_clone(historical, "skolem_order2_known_zero")
    with pytest.raises(BaselineImmutableError):
        baseline.memory.add(clone)


def test_comparison_does_not_call_reproduction_a_discovery():
    baseline = load_v2_3_baseline()
    historical = recover_historical(baseline, "switching_affine_z2_origin")
    clone = _isolated_clone(historical, "switching_affine_z2_origin")
    record = run_replay(baseline, "switching_affine_z2_origin", lambda source: clone)
    yield_cell = record.comparison.dimensions["mathematical_yield"]
    assert yield_cell.classification.value != "NEW_THEOREM"
    assert "close_tag=" in " ".join(record.comparison.v2_4_added_information)
