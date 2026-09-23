"""Frozen-engine campaign on the even/odd floor-power map."""

from __future__ import annotations

from pathlib import Path

from research.juggler_sequence.discovery import evidence_state, falsify_claims
from research.juggler_sequence.lean_export import LEAN_MODULE, LEAN_PATH, THEOREMS
from research.juggler_sequence.planner import plan_strategy
from research.juggler_sequence.problem import PROBLEM
from research.juggler_sequence.runner import CURRENT, LIVE_ID, run_campaign
from research.juggler_sequence.spec import map_images, map_spec
from research.literature import get_reference
from research.open_problems import get_problem
from research_engine.memory.types import FailureClass
from research_engine.planner.orchestrator import DEFAULT_ATTACK_ORDER
from research_engine.strategy import ResearchGoal

ROOT = Path(__file__).resolve().parents[3]
SRC = ROOT / "src" / "research" / "juggler_sequence"
FORBIDDEN_SPEC = (
    "named conjectures",
    "open-problem",
    "Pickover",
    "every positive",
    "Collatz",
    "Catalan",
)


def _source_lines(name: str) -> str:
    return (SRC / name).read_text(encoding="utf-8")


def test_adapter_sources_are_blind_and_do_not_import_scout():
    for name in ("spec.py", "adapter.py", "planner.py"):
        text = _source_lines(name)
        for line in text.splitlines():
            stripped = line.strip()
            if "juggler_sequence.scout" in stripped:
                raise AssertionError(f"{name} imports scout")
        hits = [phrase for phrase in FORBIDDEN_SPEC if phrase.casefold() in text.casefold()]
        assert hits == [], f"{name} leaked {hits}"


def test_blind_packet_has_a_bounded_exact_seed_orbit():
    spec = map_spec()
    assert spec.name == LIVE_ID
    assert spec.dimension == 1
    assert spec.start == 13
    assert spec.start_remaining >= 4
    assert spec.state_cap >= 5
    assert map_images(13) == (46,)
    assert map_images(1) == (1,)
    assert spec.affine_system() is None


def test_problem_descriptor_and_prior_art():
    assert get_problem(CURRENT) is PROBLEM
    assert PROBLEM.docs == ("docs/problems/juggler_sequence.md",)
    assert get_reference("oeis-A007320")["year"] == 1996


def test_attack_architecture_remains_frozen():
    assert DEFAULT_ATTACK_ORDER[-1] == "symmetry"
    assert "piecewise_affine" in DEFAULT_ATTACK_ORDER
    assert "sqrt" not in DEFAULT_ATTACK_ORDER
    assert "radical" not in DEFAULT_ATTACK_ORDER


def test_post_run_seed_orbit_and_non_affine():
    spec = map_spec()
    report = evidence_state(spec)
    assert report["start_orbit"] == (13, 46, 6, 2, 1)
    assert report["steps_to_one"] == 4
    assert report["fixed_one"] is True
    assert report["first_growth"] == 3
    assert report["universal_reach_one"] is False
    flag = falsify_claims(spec)
    assert flag["residue_affine_cover"]["status"] == "REFUTED"
    assert flag["seed_halt_is_z_theorem"]["status"] == "REFUTED"
    assert flag["this_is_aliquot"]["status"] == "REFUTED"
    assert flag["this_is_floor_5x4"]["status"] == "REFUTED"
    assert flag["strict_descent"]["status"] == "REFUTED"
    assert flag["new_radical_attack"]["status"] == "REFUTED"


def test_blind_strategy_selects_termination_chain_without_memory():
    report = plan_strategy(goal=ResearchGoal.TERMINATION, memory=None)
    assert report.plan.chain.id == "global_inductive"
    assert [item.name for item in report.results] == []


def test_lean_identities_are_known_and_sorry_free():
    from research.juggler_sequence.lean_paths import juggler_text

    text = juggler_text()
    assert "sorry" not in text
    assert "admit" not in text
    assert LEAN_MODULE.replace(".", "/") in LEAN_PATH.replace("\\", "/")
    for name in THEOREMS:
        assert name in text


def test_campaign_runs_unmodified_loop():
    _, report = run_campaign()
    flagship = report.by_target("juggler")
    assert report.planner_unchanged_with_memory is True
    assert report.strategy_chain == "global_inductive"
    assert flagship.extra["piecewise_affine_status"] == "INCONCLUSIVE"
    assert flagship.extra["closure_status"] == "SUPPORTED"
    assert flagship.extra["closure_size"] == 5
    assert flagship.extra["yield"]["evidence"]["steps_to_one"] == 4
    assert flagship.extra["yield"]["engineering_changes"] == 0
    assert report.next_target_overridden is False
    if report.next_target_name:
        assert report.next_target_name != CURRENT
    classes = flagship.extra["failure_classes"]
    assert FailureClass.REPRESENTATION.value in classes
    assert FailureClass.GLOBAL_REASONING.value not in classes
    assert report.memory is not None
    stored = report.memory.get(LIVE_ID)
    assert stored.finalized
    assert stored.grey_loot
