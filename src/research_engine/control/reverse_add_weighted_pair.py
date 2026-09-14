"""Phase-7 reverse-add weighted reverse-pair falsifier. Not an attack.

Positional summaries of raw pair sums s_i. Strictly coarser than
T(x)=sum s_i 3^i. Composition depth frozen at 1. No production registry.
"""

from __future__ import annotations

from dataclasses import dataclass
from enum import Enum
from typing import Any, Callable, Mapping

from research_engine.control.proposals import assert_not_executable
from research_engine.control.reverse_add_pair_interaction import pair_sums_lsd, sign_int
from research_engine.control.types import (
    ENGINE_CONTROL_VERSION,
    AttackProposal,
    AttackProposalDossier,
    Confidence,
    ImplementationScope,
    NoveltyRisk,
)

TARGET = "reverse_and_add_base3"
DEPTH = 1
EXPERIMENT_NAME = "reverse_pair_weighted_phase7"

FORBIDDEN_STATISTIC_KEYS = frozenset(
    {
        "weighted_sum",
        "full_sum",
        "reconstructed_T",
        "sum_s_3i",
    }
)


class WeightedPairClass(str, Enum):
    WEIGHTED_PAIR_GREEN_LOOT = "WEIGHTED_PAIR_GREEN_LOOT"
    WEIGHTED_PAIR_PROMISING = "WEIGHTED_PAIR_PROMISING"
    WEIGHTED_PAIR_NEEDS_RICHER_STRUCTURE = "WEIGHTED_PAIR_NEEDS_RICHER_STRUCTURE"
    WEIGHTED_PAIR_REFUTED = "WEIGHTED_PAIR_REFUTED"
    INSUFFICIENT_DATA = "INSUFFICIENT_DATA"


PAIR_CONVENTION = {
    "digit_index": "LSD-first: index i is the coefficient of 3^i",
    "alignment": (
        "LSD-align encode(x) with encode(W(x)); pad the shorter word with 0 "
        "on the MSD side"
    ),
    "s_i": "left_i + right_i, raw pair sum before rewrite_sum, in {-2,...,2}",
    "identity": "T(x)=sum_i s_i 3^i is definitional and is not a candidate",
    "coarser_than_T": True,
}

CANDIDATE_STATISTICS = {
    "h": "max {i : s_i != 0}, or None if every s_i = 0",
    "sign_h": "sign(s_h) when h is defined",
    "m_plus": "max {i : s_i > 0}, or None",
    "m_minus": "max {i : s_i < 0}, or None",
    "h2": "max {i : |s_i| = 2}, or None",
    "sign_h2": "sign(s_{h2}) when h2 is defined",
    "not_stored": "sum_i s_i 3^i",
}


def positional_profile(sums: tuple[int, ...]) -> dict[str, int | None]:
    """Index/sign summaries only. Does not return a weighted sum."""
    h: int | None = None
    m_plus: int | None = None
    m_minus: int | None = None
    h2: int | None = None
    for index, item in enumerate(sums):
        if item != 0:
            h = index
        if item > 0:
            m_plus = index
        if item < 0:
            m_minus = index
        if abs(item) == 2:
            h2 = index
    sign_h = None if h is None else sign_int(sums[h])
    sign_h2 = None if h2 is None else sign_int(sums[h2])
    return {
        "h": h,
        "sign_h": sign_h,
        "m_plus": m_plus,
        "m_minus": m_minus,
        "h2": h2,
        "sign_h2": sign_h2,
    }


def assert_not_reconstruction(payload: Mapping[str, Any]) -> None:
    keys = set(payload)
    overlap = keys & FORBIDDEN_STATISTIC_KEYS
    if overlap:
        raise ValueError(f"definitional reconstruction keys present: {sorted(overlap)}")


@dataclass(frozen=True)
class WeightedSample:
    source: int
    image: int
    w_source: int
    len_source: int
    len_image: int
    pair_sums: tuple[int, ...]
    h: int | None
    sign_h: int | None
    m_plus: int | None
    m_minus: int | None
    h2: int | None
    sign_h2: int | None
    note: str = ""

    @property
    def length_delta(self) -> int:
        return self.len_image - self.len_source

    def as_dict(self) -> dict[str, Any]:
        payload = {
            "source": self.source,
            "image": self.image,
            "w_source": self.w_source,
            "len_source": self.len_source,
            "len_image": self.len_image,
            "length_delta": self.length_delta,
            "pair_sums": list(self.pair_sums),
            "h": self.h,
            "sign_h": self.sign_h,
            "m_plus": self.m_plus,
            "m_minus": self.m_minus,
            "h2": self.h2,
            "sign_h2": self.sign_h2,
            "note": self.note,
        }
        assert_not_reconstruction(payload)
        return payload


@dataclass(frozen=True)
class RankedCandidate:
    rank: int
    name: str
    exact_statement: str
    motivation: str
    relevant_domain: str
    expected_yield: str
    cheapest_falsifier: str
    failure_class: str
    holds: Callable[[WeightedSample], bool]
    in_domain: Callable[[WeightedSample], bool]


@dataclass(frozen=True)
class CandidateOutcome:
    rank: int
    name: str
    exact_statement: str
    motivation: str
    relevant_domain: str
    expected_yield: str
    cheapest_falsifier: str
    survived: bool
    counterexample: WeightedSample | None
    failure_mechanism: str
    failure_class: str
    checked: int

    def as_dict(self) -> dict[str, Any]:
        return {
            "rank": self.rank,
            "name": self.name,
            "exact_statement": self.exact_statement,
            "motivation": self.motivation,
            "relevant_domain": self.relevant_domain,
            "expected_yield": self.expected_yield,
            "cheapest_falsifier": self.cheapest_falsifier,
            "survived": self.survived,
            "counterexample": None if self.counterexample is None else self.counterexample.as_dict(),
            "failure_mechanism": self.failure_mechanism,
            "failure_class": self.failure_class,
            "checked": self.checked,
        }


def _c2_holds(item: WeightedSample) -> bool:
    if item.m_minus is None:
        return item.image > 0
    if item.m_plus is None:
        return item.image < 0
    if item.m_plus > item.m_minus:
        return item.image > 0
    return item.image < 0


def ranked_candidates() -> tuple[RankedCandidate, ...]:
    """Exactly three candidates, ranked before execution. Do not extend after failure."""

    return (
        RankedCandidate(
            rank=1,
            name="highest_nonzero_pair_determines_sign",
            exact_statement=(
                "If some s_i != 0 and h=max{i:s_i!=0}, then sign(T(x))=sign(s_h). "
                "Equivalently s_h>0 implies T(x)>0 and s_h<0 implies T(x)<0"
            ),
            motivation=(
                "Phase-6 pair-sign majority failed because counts ignore 3^i. "
                "The minimal positional repair uses only the highest nonzero pair, "
                "not the full weighted sum."
            ),
            relevant_domain="one-step reverse-plus-add states with at least one nonzero pair",
            expected_yield="an exact sign(T) law from a single pair position",
            cheapest_falsifier="the first frozen seed whose highest nonzero pair has the opposite sign of T",
            failure_class="HIGH_POSITION_NOT_DOMINANT",
            in_domain=lambda item: item.h is not None,
            holds=lambda item: sign_int(item.image) == item.sign_h,
        ),
        RankedCandidate(
            rank=2,
            name="highest_positive_vs_highest_negative",
            exact_statement=(
                "If m+=max{i:s_i>0} and m-=max{i:s_i<0} are compared, then "
                "m+>m- implies T(x)>0 and m->m+ implies T(x)<0; a missing "
                "side is treated as strictly dominated"
            ),
            motivation=(
                "The Phase-6 count comparison P+>P- failed. The natural repair "
                "compares the most significant positive position with the most "
                "significant negative position, still without the full sum."
            ),
            relevant_domain="one-step reverse-plus-add states with at least one nonzero pair",
            expected_yield="an exact mixed-sign positional dominance law for sign(T)",
            cheapest_falsifier="the first frozen seed whose higher signed position disagrees with sign(T)",
            failure_class="SIGN_POSITION_MISMATCH",
            in_domain=lambda item: item.m_plus is not None or item.m_minus is not None,
            holds=_c2_holds,
        ),
        RankedCandidate(
            rank=3,
            name="highest_mag2_determines_sign",
            exact_statement=(
                "If h2=max{i:|s_i|=2} is defined, then sign(T(x))=sign(s_{h2}), "
                "even when a higher |s|=1 pair exists"
            ),
            motivation=(
                "Phase 5 showed internal |s|=2 activity without length change. "
                "This tests whether the highest constructive/destructive collision "
                "captures sign, or whether a higher |s|=1 pair can dominate it."
            ),
            relevant_domain="one-step reverse-plus-add states with some |s_i|=2",
            expected_yield="an exact collision-position law for sign(T)",
            cheapest_falsifier=(
                "the first frozen seed whose highest |s|=2 pair has the opposite sign of T"
            ),
            failure_class="MULTI_POSITION_INTERFERENCE",
            in_domain=lambda item: item.h2 is not None,
            holds=lambda item: sign_int(item.image) == item.sign_h2,
        ),
    )


def evaluate_candidate(
    candidate: RankedCandidate,
    samples: tuple[WeightedSample, ...],
) -> CandidateOutcome:
    checked = 0
    for item in samples:
        if not candidate.in_domain(item):
            continue
        checked += 1
        if candidate.holds(item):
            continue
        return CandidateOutcome(
            rank=candidate.rank,
            name=candidate.name,
            exact_statement=candidate.exact_statement,
            motivation=candidate.motivation,
            relevant_domain=candidate.relevant_domain,
            expected_yield=candidate.expected_yield,
            cheapest_falsifier=candidate.cheapest_falsifier,
            survived=False,
            counterexample=item,
            failure_mechanism=_mechanism(candidate, item),
            failure_class=candidate.failure_class,
            checked=checked,
        )
    if checked < 1:
        return CandidateOutcome(
            rank=candidate.rank,
            name=candidate.name,
            exact_statement=candidate.exact_statement,
            motivation=candidate.motivation,
            relevant_domain=candidate.relevant_domain,
            expected_yield=candidate.expected_yield,
            cheapest_falsifier=candidate.cheapest_falsifier,
            survived=False,
            counterexample=None,
            failure_mechanism="no frozen samples on the stated domain",
            failure_class="OTHER",
            checked=checked,
        )
    return CandidateOutcome(
        rank=candidate.rank,
        name=candidate.name,
        exact_statement=candidate.exact_statement,
        motivation=candidate.motivation,
        relevant_domain=candidate.relevant_domain,
        expected_yield=candidate.expected_yield,
        cheapest_falsifier=candidate.cheapest_falsifier,
        survived=True,
        counterexample=None,
        failure_mechanism="",
        failure_class="",
        checked=checked,
    )


def _mechanism(candidate: RankedCandidate, item: WeightedSample) -> str:
    if candidate.name == "highest_nonzero_pair_determines_sign":
        return (
            f"Highest nonzero pair does not dominate sign: h={item.h}, "
            f"s_h={item.sign_h}, T({item.source})={item.image}."
        )
    if candidate.name == "highest_positive_vs_highest_negative":
        return (
            f"Signed positional dominance disagrees with sign(T): m+={item.m_plus}, "
            f"m-={item.m_minus}, {item.source}->{item.image}."
        )
    return (
        f"Highest |s|=2 pair does not determine sign: h2={item.h2}, "
        f"sign(s_h2)={item.sign_h2}, h={item.h}, sign(s_h)={item.sign_h}, "
        f"{item.source}->{item.image}."
    )


def classify(outcomes: tuple[CandidateOutcome, ...]) -> tuple[WeightedPairClass, str]:
    if any(item.checked < 1 and not item.survived and item.counterexample is None for item in outcomes):
        if all(item.checked < 1 for item in outcomes):
            return (
                WeightedPairClass.INSUFFICIENT_DATA,
                "the frozen artifacts do not contain enough one-step samples",
            )
    survivors = [item for item in outcomes if item.survived]
    failed = [item for item in outcomes if not item.survived]
    by_name = {item.name: item for item in outcomes}
    top = by_name.get("highest_nonzero_pair_determines_sign")
    if all(item.survived for item in outcomes):
        return (
            WeightedPairClass.WEIGHTED_PAIR_PROMISING,
            "all three positional summaries survived the frozen sample",
        )
    if top is not None and top.survived and failed:
        return (
            WeightedPairClass.WEIGHTED_PAIR_PROMISING,
            "the highest-nonzero-pair sign law survived; a coarser collision "
            "summary is not sufficient on its own",
        )
    if len(failed) == 3:
        return (
            WeightedPairClass.WEIGHTED_PAIR_REFUTED,
            "the three natural low-information positional summaries all fail",
        )
    if survivors and failed:
        return (
            WeightedPairClass.WEIGHTED_PAIR_NEEDS_RICHER_STRUCTURE,
            "positional dominance matters but these summaries are not sufficient",
        )
    return (
        WeightedPairClass.WEIGHTED_PAIR_REFUTED,
        "low-information positional summaries are not a useful exact coordinate",
    )


def _proposal(
    rank: int,
    name: str,
    trigger: str,
    target: str,
    mechanism: str,
    capability: str,
    expected: str,
    falsifier: str,
    *,
    novelty: NoveltyRisk,
    scope: ImplementationScope,
    confidence: Confidence,
    reason: str,
) -> AttackProposal:
    assert_not_executable(name)
    return AttackProposal(
        rank=rank,
        attack_name=name,
        trigger=trigger,
        mathematical_target=target,
        mechanism=mechanism,
        required_capability=capability,
        expected_yield=expected,
        falsifier=falsifier,
        novelty_risk=novelty,
        implementation_scope=scope,
        confidence=confidence,
        novelty_risk_reason=reason,
    )


def _keep_composition_lead(*, pair_note: str) -> AttackProposalDossier:
    items = (
        _proposal(
            1,
            "symbolic_nonlinear_composition",
            "low-information positional summaries did not close reverse-add",
            "Keep the leading reverse-add proposal on nonlinear composition of W.",
            "Do not register weighted_reverse_pair_interaction as a production attack.",
            "symbolic nonlinear branch composition",
            "an exact reverse identity that is not a scalar positional summary",
            "A reverse-add sample whose named identity fails.",
            novelty=NoveltyRisk.HIGH,
            scope=ImplementationScope.LARGE,
            confidence=Confidence.MEDIUM,
            reason="Phase-7 showed positional dominance is supporting, not a flood attack",
        ),
        _proposal(
            2,
            "basin_preimage_grammar",
            "positional sign laws do not explain basins",
            "Characterize predecessors of 0 under reverse-plus-add.",
            "Bounded preimage with a residue/word quotient. Do not reopen reverse_gap.",
            "symbolic predecessor construction",
            "regular-preimage lemma or splitting pair",
            "Two predecessors indistinguishable by the quotient.",
            novelty=NoveltyRisk.MEDIUM,
            scope=ImplementationScope.MEDIUM,
            confidence=Confidence.MEDIUM,
            reason="basin language is independent of one-step pair-position sign",
        ),
        _proposal(
            3,
            "ranking_function_synthesis",
            "do not reopen reverse_gap or scalar ranking",
            "Revisit ranking only after a coordinate richer than positional pair sign is named.",
            "Keep ranking downstream. Do not enlarge the Phase-0 grid.",
            "ranking-function synthesis",
            "ranking certificate using a coordinate named after positional summaries were tested",
            "The new coordinate still fails to decrease on an exact transition.",
            novelty=NoveltyRisk.HIGH,
            scope=ImplementationScope.LARGE,
            confidence=Confidence.LOW,
            reason="Phase 0/1 already falsified scalar ranking and reverse_gap",
        ),
    )
    return AttackProposalDossier(
        proposals=items,
        campaign_id=TARGET,
        notes=(
            "updated from reverse-add weighted-pair Phase-7 falsifier; not executed",
            pair_note,
            "weighted_reverse_pair_interaction is not registered",
            "reverse_gap remains closed",
        ),
    )


def updated_proposals(classification: WeightedPairClass) -> AttackProposalDossier:
    if classification is WeightedPairClass.WEIGHTED_PAIR_GREEN_LOOT:
        items = (
            _proposal(
                1,
                "weighted_reverse_pair_interaction",
                "exact highest-pair sign law",
                "Package the survived positional sign lemma as a later Phase, not a flood attack.",
                "Keep k=1. Do not start a digit-language engine.",
                "positional reverse-pair dominance of x and W(x)",
                "Lean lemma on h, s_h, and sign(T)",
                "A domain element violating the lemma.",
                novelty=NoveltyRisk.LOW,
                scope=ImplementationScope.SMALL,
                confidence=Confidence.HIGH,
                reason="the statement is an exact positional identity, not a census",
            ),
            _proposal(
                2,
                "symbolic_nonlinear_composition",
                "positional dominance is a supporting coordinate",
                "Ask whether the survived sign law composes with W.",
                "Keep composition gated. Do not thaw DEFAULT_ATTACK_ORDER.",
                "symbolic nonlinear branch composition",
                "a composition identity that uses positional pair sign",
                "A reverse-add sample on which the sign law does not constrain T^2.",
                novelty=NoveltyRisk.MEDIUM,
                scope=ImplementationScope.MEDIUM,
                confidence=Confidence.MEDIUM,
                reason="sign loot is still one-step; composition remains open",
            ),
            _proposal(
                3,
                "proof_guided_hypothesis_refinement",
                "ReverseAdd Lean does not yet expose pair positions",
                "Formalize the survived identity only if encode/btReverseZ suffice.",
                "Do not add a word-algebra framework solely to force a proof.",
                "proof-guided hypothesis refinement",
                "Lean lemma covering the English statement",
                "A domain element whose one-step image violates the identity.",
                novelty=NoveltyRisk.MEDIUM,
                scope=ImplementationScope.MEDIUM,
                confidence=Confidence.MEDIUM,
                reason="Problems.Engine.ReverseAdd has no pair-position lemmas",
            ),
        )
        return AttackProposalDossier(
            proposals=items,
            campaign_id=TARGET,
            notes=(
                "updated from reverse-add weighted-pair Phase-7 falsifier; not executed",
                "weighted_reverse_pair_interaction is proposed, not registered",
            ),
        )
    if classification is WeightedPairClass.WEIGHTED_PAIR_PROMISING:
        return _keep_composition_lead(
            pair_note=(
                "positional dominance of reverse pairs determines sign(T) on the "
                "frozen sample; keep symbolic_nonlinear_composition as the leading "
                "proposal and treat highest-pair sign as a supporting coordinate"
            ),
        )
    if classification is WeightedPairClass.WEIGHTED_PAIR_REFUTED:
        return _keep_composition_lead(
            pair_note=(
                "low_information_positional_summary_insufficient; "
                "weighted_reverse_pair_interaction is not kept as a future attack"
            ),
        )
    return _keep_composition_lead(
        pair_note=(
            "positional dominance helps but is insufficient; keep "
            "symbolic_nonlinear_composition as the leading proposal"
        ),
    )


def lean_status_for(classification: WeightedPairClass) -> str:
    if classification is WeightedPairClass.INSUFFICIENT_DATA:
        return "NOT_YET_FORMALIZATION_READY"
    if classification in {
        WeightedPairClass.WEIGHTED_PAIR_PROMISING,
        WeightedPairClass.WEIGHTED_PAIR_GREEN_LOOT,
    }:
        return "FORMALIZATION_READY"
    return "FORMALIZATION_BLOCKED"


def tautology_checks() -> dict[str, Any]:
    return {
        "definitional_identity": "T(x)=sum_i s_i 3^i is not a candidate",
        "stored_statistics": sorted(CANDIDATE_STATISTICS.keys() - {"not_stored"}),
        "forbidden_keys": sorted(FORBIDDEN_STATISTIC_KEYS),
        "candidates_reconstruct_T": False,
        "coarser_than_full_sum": True,
        "oracle": "T(x) is taken from ReverseAddSpec, not reconstructed from the statistic",
    }


def phase7_payload(
    outcomes: tuple[CandidateOutcome, ...],
    *,
    classification: WeightedPairClass,
    decision_reason: str,
    transition_window: dict[str, Any],
    special_probes: list[dict[str, Any]],
    secondary_length_observation: str,
) -> dict[str, Any]:
    survivors = [item.as_dict() for item in outcomes if item.survived]
    first_counterexamples = [
        {
            "name": item.name,
            "rank": item.rank,
            "failure_class": item.failure_class,
            "counterexample": item.as_dict()["counterexample"],
        }
        for item in outcomes
        if item.counterexample is not None
    ]
    dossier = updated_proposals(classification)
    green = classification is WeightedPairClass.WEIGHTED_PAIR_GREEN_LOOT
    return {
        "engine_control_version": ENGINE_CONTROL_VERSION,
        "source_engine": "v2.3",
        "experimental_status": "PHASE_7_WEIGHTED_REVERSE_PAIR_FALSIFIER",
        "target": TARGET,
        "composition_depth": DEPTH,
        "experiment_name": EXPERIMENT_NAME,
        "gated": True,
        "pair_convention": PAIR_CONVENTION,
        "candidate_statistics": CANDIDATE_STATISTICS,
        "candidate_statements": [item.as_dict() for item in outcomes],
        "domains": [item.relevant_domain for item in outcomes],
        "special_probes": special_probes,
        "transition_window": transition_window,
        "survivors": survivors,
        "first_counterexamples": first_counterexamples,
        "failure_mechanisms": [
            {"name": item.name, "class": item.failure_class, "text": item.failure_mechanism}
            for item in outcomes
            if not item.survived
        ],
        "tautology_checks": tautology_checks(),
        "secondary_length_observation": secondary_length_observation,
        "lean_status": lean_status_for(classification),
        "mathematical_status": "none" if not green else "NEW_STRUCTURAL_LEMMA",
        "classification": classification.value,
        "top3_update": dossier.as_dict(),
        "decision": classification.value,
        "decision_reason": decision_reason,
        "green_loot": "WEIGHTED_PAIR_GREEN_LOOT" if green else "NO_NEW_LOOT",
        "global_consequence": "NONE",
        "laboratory_decision": "CLOSE" if classification is WeightedPairClass.WEIGHTED_PAIR_REFUTED else "PARK",
    }


def render_phase7_markdown(payload: Mapping[str, Any]) -> str:
    lines = [
        "# Reverse-add weighted reverse-pair Phase-7 falsifier",
        "",
        "Status: **PHASE_7_WEIGHTED_REVERSE_PAIR_FALSIFIER**",
        "",
        "This is not a reverse-and-add solver, not a ranking synthesizer, and not a",
        "digit-language engine. It tests whether a low-information positional",
        "summary of raw pair sums predicts successor sign without reconstructing",
        "`T(x)=sum_i s_i 3^i`.",
        "",
        "## Branch budget",
        "",
        "```text",
        "Mathematical target     Does highest-significance reverse-pair position",
        "                        determine sign(T) without the full weighted sum?",
        "Novelty hypothesis      Positional dominance, not pair counts, is the",
        "                        missing middle coordinate between counts and T.",
        "Falsifier               An exact one-step sample violating each candidate,",
        "                        or a survivor that reconstructs T.",
        "Existing machinery      ReverseAddSpec, encode, bt_reverse, pair_sums_lsd,",
        "                        WINDOW, seed-196 orbit, Phase-6 pair convention.",
        "Maximum Phase-7 scope   k=1; three pre-ranked positional summaries;",
        "                        frozen window+orbit.",
        "Promotion criterion     Exact coarser-than-T sign law, Lean path.",
        "Stop criterion          full-sum reconstruction, digit-language engine,",
        "                        k>1, census growth, ranking.",
        "```",
        "",
        "## Metadata",
        "",
        f"- engine_control_version: `{payload['engine_control_version']}`",
        f"- source_engine: `{payload['source_engine']}`",
        f"- experimental_status: `{payload['experimental_status']}`",
        f"- target: `{payload['target']}`",
        f"- composition depth: {payload['composition_depth']}",
        f"- classification: **{payload['classification']}**",
        f"- lean: `{payload['lean_status']}`",
        f"- green loot: `{payload['green_loot']}`",
        f"- decision reason: {payload['decision_reason']}",
        "",
        "Candidate list frozen at three. reverse_gap is not reopened.",
        "`DEFAULT_ATTACK_ORDER` is unchanged. No production weighted-pair attack.",
        "",
        "## Pair convention",
        "",
        f"- Digit index: {payload['pair_convention']['digit_index']}",
        f"- Alignment: {payload['pair_convention']['alignment']}",
        f"- Pair sum: {payload['pair_convention']['s_i']}",
        f"- Identity: {payload['pair_convention']['identity']}",
        "",
        "## Anti-tautology",
        "",
        f"- Definitional identity rejected as a candidate: `{payload['tautology_checks']['definitional_identity']}`",
        f"- Candidates reconstruct T: `{payload['tautology_checks']['candidates_reconstruct_T']}`",
        f"- Stored statistics coarser than the full sum: `{payload['tautology_checks']['coarser_than_full_sum']}`",
        "",
    ]
    for item in payload["candidate_statements"]:
        mark = "survived" if item["survived"] else "failed"
        lines.extend(
            [
                f"## Candidate {item['rank']}: `{item['name']}` ({mark})",
                "",
                f"- Statement: {item['exact_statement']}",
                f"- Motivation: {item['motivation']}",
                f"- Domain: {item['relevant_domain']}",
                f"- Expected yield: {item['expected_yield']}",
                f"- Cheapest falsifier: {item['cheapest_falsifier']}",
                f"- Checked: {item['checked']}",
                "",
            ]
        )
        if item.get("counterexample"):
            cex = item["counterexample"]
            lines.append(
                f"- Counterexample: `{cex['source']} -> {cex['image']}` "
                f"(h={cex['h']}, sign_h={cex['sign_h']}, m+={cex['m_plus']}, "
                f"m-={cex['m_minus']}, h2={cex['h2']}, sign_h2={cex['sign_h2']})"
            )
            lines.append(f"- Failure class: `{item['failure_class']}`")
            lines.append(f"- Mechanism: {item['failure_mechanism']}")
            lines.append("")
    lines.extend(
        [
            "## Special probes",
            "",
        ]
    )
    for probe in payload.get("special_probes") or []:
        lines.append(
            f"- `{probe.get('role', '')}`: x={probe.get('source')} -> "
            f"T={probe.get('image')}, s={probe.get('pair_sums')}, "
            f"h={probe.get('h')}, sign_h={probe.get('sign_h')}, "
            f"m+={probe.get('m_plus')}, m-={probe.get('m_minus')}, "
            f"h2={probe.get('h2')}, sign_h2={probe.get('sign_h2')}"
        )
    window = payload.get("transition_window") or {}
    lines.extend(
        [
            "",
            "## Secondary length observation",
            "",
            payload.get("secondary_length_observation") or "none",
            "",
            "## Transition window",
            "",
            f"- Frozen discovery window: {window.get('window', '—')}",
            f"- Packet orbit seed: {window.get('orbit_seed', '—')}",
            f"- One-step samples: {window.get('sample_count', '—')}",
            "",
            "## Decision",
            "",
            f"**{payload['decision']}**",
            "",
            payload["decision_reason"] + ".",
            "",
            f"Green loot: `{payload['green_loot']}`. Lean: `{payload['lean_status']}`.",
            "Not a halt theorem. Not a production attack.",
            "",
            "## Best next question",
            "",
            "If highest-pair sign is an exact but general place-value fact, does "
            "reverse-and-add still need a target-specific nonlinear identity, or "
            "is the remaining gap only formalization of that bound?",
            "",
        ]
    )
    return "\n".join(lines)
