"""Phase-3 restricted symbolic-composition experiment. Opt-in attack run."""

from __future__ import annotations

import json
from dataclasses import replace
from pathlib import Path
from typing import Any, Mapping

from research.cyclic_tag_bit.spec import map_spec as cyclic_spec
from research.home_prime_49.spec import map_spec as home_spec
from research.juggler_sequence.spec import map_spec as juggler_spec
from research.reverse_and_add_base3.spec import map_spec as reverse_spec
from research_engine.attacks.restricted_symbolic_composition import (
    APPLICABLE,
    FAMILY_NAME,
    GLOBAL_CONSEQUENCE_NONE,
    NOT_APPLICABLE,
    RULE_NAME,
    SymbolicCompositionResult,
    evaluate_odd_even_two_step,
)
from research_engine.attacks.result import AttackContext, AttackStatus
from research_engine.control.types import ENGINE_CONTROL_VERSION
from research_engine.planner.orchestrator import (
    DEFAULT_ATTACK_ORDER,
    DEFERRED_ATTACKS,
    EXPERIMENTAL_ATTACKS,
    run_named_attack,
)

REPO_ROOT = Path(__file__).resolve().parents[3]
JSON_PATH = REPO_ROOT / "docs" / "research" / "symbolic_composition_phase3.json"
DOC_PATH = REPO_ROOT / "docs" / "research" / "symbolic_composition_phase3.md"

TARGETS: tuple[tuple[str, Any], ...] = (
    ("juggler_sequence", juggler_spec),
    ("reverse_and_add_base3", reverse_spec),
    ("home_prime_49", home_spec),
    ("cyclic_tag_bit", cyclic_spec),
)


def opted_in_context(spec) -> AttackContext:
    builder = getattr(spec, "attack_context", None)
    if callable(builder):
        return builder(enable_restricted_symbolic_composition=True)
    return AttackContext(enable_restricted_symbolic_composition=True)


def run_target(target_id: str, spec) -> SymbolicCompositionResult:
    payload = evaluate_odd_even_two_step(spec)
    payload = replace(payload, target_id=target_id)
    result = run_named_attack(
        FAMILY_NAME,
        spec,
        opted_in_context(spec),
    )
    if payload.applicability == APPLICABLE:
        assert result.status is AttackStatus.SUPPORTED
        assert result.evidence.get("lean_status") == "PROVED"
        assert result.evidence.get("global_consequence") == GLOBAL_CONSEQUENCE_NONE
    else:
        assert result.status is AttackStatus.INAPPLICABLE
        assert result.evidence.get("failure_reason") == payload.failure_reason
    return payload


def run_phase3() -> tuple[SymbolicCompositionResult, ...]:
    return tuple(run_target(target_id, factory()) for target_id, factory in TARGETS)


def decide_phase3(reports: tuple[SymbolicCompositionResult, ...]) -> tuple[str, str]:
    by = {item.target_id: item for item in reports}
    juggler = by.get("juggler_sequence")
    negatives = [
        by[name]
        for name in ("reverse_and_add_base3", "home_prime_49", "cyclic_tag_bit")
        if name in by
    ]
    j_ok = (
        juggler is not None
        and juggler.applicability == APPLICABLE
        and juggler.lean_status == "PROVED"
        and juggler.candidate == "T^2(x) < x"
        and juggler.global_consequence == GLOBAL_CONSEQUENCE_NONE
    )
    neg_ok = all(item.applicability == NOT_APPLICABLE for item in negatives)
    if j_ok and neg_ok:
        return (
            "PROMOTE_RESTRICTED",
            "Juggler odd-even T^2 < x is recovered and Lean-certified; unrelated maps are rejected",
        )
    if j_ok:
        return (
            "REFINE_RESTRICTED",
            "Juggler works but a negative control was not a clean NOT_APPLICABLE",
        )
    return (
        "ABANDON_RESTRICTED",
        "the proved Juggler lemma could not be converted into a clean executable primitive",
    )


def grey_loot(reports: tuple[SymbolicCompositionResult, ...]) -> dict[str, Any]:
    by = {item.target_id: item for item in reports}
    return {
        "why_juggler": (
            "Phase-1 bounded T^2 ranking survived; Phase-2 explained it by the exact "
            "odd-even two-step inequality; Lean proved floorPower_odd_even_two_step_lt."
        ),
        "bounded_to_lean": (
            "finite survivor -> symbolic explanation -> Lean theorem -> gated executable rule"
        ),
        "reusable": [
            "fixed composition depth 2",
            "exact odd-to-even domain predicate",
            "map-identity probe against even/odd floor-power",
            "named candidate T^2(x) < x",
            "association with an existing Lean theorem",
        ],
        "not_covered": {
            name: by[name].failure_reason
            for name in ("reverse_and_add_base3", "home_prime_49", "cyclic_tag_bit")
            if name in by
        },
        "target_specific_vs_compositional": (
            "matching is by successor identity with the floor-power map, not by campaign name. "
            "The rule is compositional (odd-even T^2 decrease) and does not cover reverse-add "
            "or factor-concatenation."
        ),
        "hard_coded": [
            "finite map-identity probe",
            "single rule, depth frozen at 2",
            "two-candidate vocabulary T^2 < x and T^2 <= x-1",
            "Lean theorem name association (no proof search)",
        ],
        "global_consequence": GLOBAL_CONSEQUENCE_NONE,
        "not_a_termination_result": True,
    }


def phase3_payload(
    reports: tuple[SymbolicCompositionResult, ...],
    *,
    decision: str,
    decision_reason: str,
) -> dict[str, Any]:
    return {
        "engine_control_version": ENGINE_CONTROL_VERSION,
        "source_engine": "v2.3",
        "experimental_status": "PHASE_3_RESTRICTED_SYMBOLIC_ATTACK",
        "decision": decision,
        "decision_reason": decision_reason,
        "attack_name": RULE_NAME,
        "family": FAMILY_NAME,
        "depth": 2,
        "gated": True,
        "enable_flag": "enable_restricted_symbolic_composition",
        "candidate_attack": RULE_NAME,
        "default_attack_order_unchanged": True,
        "deferred_attacks_unchanged": list(DEFERRED_ATTACKS) == ["symbolic"],
        "experimental_attacks": sorted(EXPERIMENTAL_ATTACKS),
        "not_in_default_order": sorted(
            name for name in EXPERIMENTAL_ATTACKS if name not in DEFAULT_ATTACK_ORDER
        ),
        "targets": [item.as_dict() for item in reports],
        "grey_loot": grey_loot(reports),
    }


def render_phase3_markdown(payload: Mapping[str, Any]) -> str:
    lines = [
        "# Restricted symbolic-composition Phase-3 attack",
        "",
        "Status: **PHASE_3_RESTRICTED_SYMBOLIC_ATTACK**",
        "",
        "This is the first executable v2.4 mathematical attack. It is gated.",
        "It is not a general composition engine and not a halt theorem.",
        "",
        "## Branch budget",
        "",
        "```text",
        "Mathematical target     Can the proved odd-even T^2 < n lemma become a gated",
        "                        executable primitive that recovers Juggler and rejects",
        "                        unrelated maps, without a general composition engine?",
        "Novelty hypothesis      Map-identity matching plus a two-candidate vocabulary",
        "                        plus Lean association is enough; campaign names are not.",
        "Falsifier               Juggler not recovered, negatives accepted, flood-order",
        "                        thawed, or the attack only hard-codes the theorem.",
        "Existing machinery      FloorPowerSpec.successors; floorPower_odd_even_two_step_lt;",
        "                        Attack / run_named_attack.",
        "Maximum Phase-3 scope   One rule, depth 2, four targets, gated registration.",
        "Promotion criterion     Juggler APPLICABLE+PROVED; negatives NOT_APPLICABLE;",
        "                        freeze intact.",
        "Stop criterion          Arbitrary k, CAS/SMT, ranking synthesis, termination claim.",
        "```",
        "",
        "## Metadata",
        "",
        f"- engine_control_version: `{payload['engine_control_version']}`",
        f"- experimental_status: `{payload['experimental_status']}`",
        f"- family: `{payload['family']}`",
        f"- attack: `{payload['attack_name']}`",
        f"- depth: {payload['depth']}",
        f"- gated: `{payload['enable_flag']}`",
        f"- decision: **{payload['decision']}**",
        f"- decision reason: {payload['decision_reason']}",
        "",
        "`DEFAULT_ATTACK_ORDER` is unchanged. StrategyPlanner does not execute this attack.",
        "",
    ]
    for report in payload["targets"]:
        lines.extend(
            [
                f"## Target `{report['target']}`",
                "",
                f"- Applicability: **{report['applicability']}**",
                f"- Attack: `{report['attack_name']}`",
                f"- Depth: {report['depth']}",
                f"- Domain: {report.get('domain') or '—'}",
                f"- Candidate: {report.get('candidate_statement') or '—'}",
                f"- Bounded: {report.get('bounded_status') or '—'}",
                f"- Exact: {report.get('exact_status') or '—'}",
                f"- Lean: `{report.get('lean_status') or '—'}`",
                f"- Mathematical status: `{report.get('mathematical_status') or '—'}`",
                f"- Global consequence: `{report.get('global_consequence')}`",
                f"- Failure reason: `{report.get('failure_reason') or 'none'}`",
                "",
            ]
        )
        cex = report.get("counterexample")
        if cex:
            lines.append(f"- Counterexample: `{cex['source']} -> {cex['mid']} -> {cex['image']}`")
            lines.append("")
    loot = payload.get("grey_loot") or {}
    lines.extend(
        [
            "## Grey loot",
            "",
            f"- Why Juggler: {loot.get('why_juggler', '')}",
            f"- Path: {loot.get('bounded_to_lean', '')}",
            f"- Compositional vs target-specific: {loot.get('target_specific_vs_compositional', '')}",
            f"- Global consequence: `{loot.get('global_consequence')}`",
            "",
            "Reusable:",
            "",
        ]
    )
    for item in loot.get("reusable") or ():
        lines.append(f"- {item}")
    lines.extend(["", "Hard-coded before any later generalization:", ""])
    for item in loot.get("hard_coded") or ():
        lines.append(f"- {item}")
    lines.extend(
        [
            "",
            "## Decision",
            "",
            f"**{payload['decision']}**",
            "",
            payload["decision_reason"] + ".",
            "",
            "Ready for controlled research use. Not added to `DEFAULT_ATTACK_ORDER`.",
            "Not a universal symbolic-composition engine.",
            "",
            "## Best next question",
            "",
            "Does any other stored map have a natural depth-2 branch with an exact",
            "inequality that would justify a Phase-4 falsifier, rather than widening",
            "this primitive now?",
            "",
        ]
    )
    return "\n".join(lines)


def write_artifacts(reports=None) -> dict:
    items = reports if reports is not None else run_phase3()
    decision, reason = decide_phase3(items)
    payload = phase3_payload(items, decision=decision, decision_reason=reason)
    JSON_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")
    DOC_PATH.write_text(render_phase3_markdown(payload), encoding="utf-8")
    return payload


if __name__ == "__main__":
    result = write_artifacts()
    print(result["decision"], result["attack_name"])
    print(result["decision_reason"])
    for row in result["targets"]:
        print(row["target"], row["applicability"], row.get("failure_reason") or row.get("lean_status"))
