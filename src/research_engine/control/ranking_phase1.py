"""Phase-1 enriched ranking falsifiers. Not a synthesizer and not an attack."""

from __future__ import annotations

from dataclasses import dataclass
from enum import Enum
from math import gcd
from typing import Any, Mapping

from research_engine.control.proposals import assert_not_executable
from research_engine.control.ranking import (
    COEFF_GRID,
    EXCEPTIONAL_K,
    FeatureVector,
    ObservedTransition,
    RankingCandidate,
    candidate_grid,
    canonicalize_coeffs,
    evaluate_candidate,
)
from research_engine.control.types import (
    ENGINE_CONTROL_VERSION,
    AttackProposal,
    AttackProposalDossier,
    Confidence,
    ImplementationScope,
    NoveltyRisk,
)

JUGGLER = "juggler_sequence"
REVERSE = "reverse_and_add_base3"
HOME = "home_prime_49"
REVERSE_SCALAR_BASES: tuple[tuple[int, int, int], ...] = (
    (0, 0, 0),
    (1, 0, 0),
    (0, 1, 0),
    (1, 1, 0),
    (0, 0, 1),
    (1, 0, 1),
    (1, 1, 1),
)


class Phase1Failure(str, Enum):
    COMPOSED_GROWTH = "COMPOSED_GROWTH"
    FLOOR_EFFECT = "FLOOR_EFFECT"
    PARITY_COORDINATE = "PARITY_COORDINATE"
    GAP_INCREASE = "GAP_INCREASE"
    PALINDROME_NOT_ATTRACTOR = "PALINDROME_NOT_ATTRACTOR"
    CONCAT_GROWTH = "CONCAT_GROWTH"
    FACTOR_NONDECREASE = "FACTOR_NONDECREASE"
    FEATURE_INSUFFICIENT = "FEATURE_INSUFFICIENT"
    OTHER = "OTHER"


class JugglerVerdict(str, Enum):
    COMPOSED_RANKING_PROMISING = "COMPOSED_RANKING_PROMISING"
    COMPOSED_RANKING_NEEDS_RICHER_STATE = "COMPOSED_RANKING_NEEDS_RICHER_STATE"
    COMPOSED_RANKING_IMPLAUSIBLE = "COMPOSED_RANKING_IMPLAUSIBLE"
    INSUFFICIENT_DATA = "INSUFFICIENT_DATA"


class ReverseVerdict(str, Enum):
    REVERSE_GAP_PROMISING = "REVERSE_GAP_PROMISING"
    REVERSE_GAP_NEEDS_RICHER_STATE = "REVERSE_GAP_NEEDS_RICHER_STATE"
    REVERSE_GAP_IMPLAUSIBLE = "REVERSE_GAP_IMPLAUSIBLE"
    REVERSE_GAP_NEEDS_DEFINITION = "REVERSE_GAP_NEEDS_DEFINITION"
    INSUFFICIENT_DATA = "INSUFFICIENT_DATA"


class HomeVerdict(str, Enum):
    PIECEWISE_RANKING_PROMISING = "PIECEWISE_RANKING_PROMISING"
    PIECEWISE_RANKING_NEEDS_RICHER_STATE = "PIECEWISE_RANKING_NEEDS_RICHER_STATE"
    PIECEWISE_RANKING_IMPLAUSIBLE = "PIECEWISE_RANKING_IMPLAUSIBLE"
    INSUFFICIENT_DATA = "INSUFFICIENT_DATA"


class Phase1Decision(str, Enum):
    PROMOTE_RANKING = "PROMOTE_RANKING"
    REFINE_RANKING = "REFINE_RANKING"
    ABANDON_RANKING = "ABANDON_RANKING"
    MIXED = "MIXED"


@dataclass(frozen=True)
class LinearCandidate:
    """Exact integer linear form on named FeatureVector coordinates."""

    coeffs: tuple[int, ...]
    keys: tuple[str, ...]
    form: str = ""

    def evaluate(self, features: FeatureVector) -> int:
        data = features.as_dict()
        total = 0
        for coeff, key in zip(self.coeffs, self.keys):
            total += coeff * int(data[key])
        return total

    def as_dict(self) -> dict[str, Any]:
        payload = {key: coeff for key, coeff in zip(self.keys, self.coeffs)}
        payload["q"] = 0
        payload["form"] = self.form or " + ".join(
            f"{coeff}*{key}" for coeff, key in zip(self.coeffs, self.keys)
        )
        return payload


@dataclass(frozen=True)
class LinearResult:
    candidate: LinearCandidate | RankingCandidate
    survived: bool
    counterexample: ObservedTransition | None
    v_source: int | None
    v_image: int | None
    failure_class: Phase1Failure | None
    failure_reason: str = ""
    source_features: dict[str, int] | None = None
    image_features: dict[str, int] | None = None

    def as_dict(self) -> dict[str, Any]:
        cex = None
        if self.counterexample is not None:
            cex = {
                "source": self.counterexample.source,
                "image": self.counterexample.image,
                "note": self.counterexample.note,
                "source_features": self.source_features,
                "image_features": self.image_features,
                "v_source": self.v_source,
                "v_image": self.v_image,
            }
        candidate = self.candidate.as_dict()
        return {
            "candidate": candidate,
            "survived": self.survived,
            "counterexample": cex,
            "v_source": self.v_source,
            "v_image": self.v_image,
            "failure_class": None if self.failure_class is None else self.failure_class.value,
            "failure_reason": self.failure_reason,
        }


@dataclass(frozen=True)
class Phase1TargetReport:
    target: str
    hypothesis: str
    available_features: tuple[str, ...]
    candidate_count: int
    transition_depth: int
    domain: str
    exceptional_set: tuple[str, ...]
    transitions_tested: int
    exactness: str
    survivors: tuple[LinearResult, ...]
    first_counterexamples: tuple[LinearResult, ...]
    strongest: LinearResult | None
    failure_mechanisms: tuple[str, ...]
    classification: str
    lean_status: str
    next_proposal: str
    notes: tuple[str, ...] = ()

    def as_dict(self) -> dict[str, Any]:
        return {
            "target": self.target,
            "hypothesis": self.hypothesis,
            "available_features": list(self.available_features),
            "candidate_count": self.candidate_count,
            "transition_depth": self.transition_depth,
            "domain": self.domain,
            "exceptional_set": list(self.exceptional_set),
            "transitions_tested": self.transitions_tested,
            "exactness": self.exactness,
            "survivor_count": len(self.survivors),
            "survivors": [item.as_dict() for item in self.survivors[:8]],
            "first_counterexamples": [item.as_dict() for item in self.first_counterexamples],
            "strongest": None if self.strongest is None else self.strongest.as_dict(),
            "failure_mechanisms": list(self.failure_mechanisms),
            "classification": self.classification,
            "lean_status": self.lean_status,
            "next_proposal": self.next_proposal,
            "notes": list(self.notes),
        }


def canonicalize_coeffs_n(values: tuple[int, ...]) -> tuple[int, ...] | None:
    if all(item == 0 for item in values):
        return None
    scale = 0
    for item in values:
        scale = abs(item) if scale == 0 else gcd(scale, abs(item))
    scaled = tuple(item // scale for item in values)
    for item in scaled:
        if item != 0:
            if item < 0:
                return tuple(-value for value in scaled)
            return scaled
    return None


def reverse_gap_grid() -> tuple[LinearCandidate, ...]:
    """Scalar bases from Phase 0, vary only the reverse_gap coefficient."""

    keys = ("log_bit", "digit", "residue", "reverse_gap")
    seen: set[tuple[int, ...]] = set()
    items: list[LinearCandidate] = []
    for base in REVERSE_SCALAR_BASES:
        if base != (0, 0, 0) and canonicalize_coeffs(*base) != base:
            continue
        for extra in COEFF_GRID:
            canon = canonicalize_coeffs_n(base + (extra,))
            if canon is None or canon in seen:
                continue
            seen.add(canon)
            items.append(
                LinearCandidate(
                    coeffs=canon,
                    keys=keys,
                    form="a*log_bit + b*digit + c*parity + d*reverse_gap",
                )
            )
    return tuple(items)


def piecewise_grid() -> tuple[LinearCandidate, ...]:
    keys = ("digit", "factor_count", "omega")
    seen: set[tuple[int, ...]] = set()
    items: list[LinearCandidate] = []
    for a in COEFF_GRID:
        for b in COEFF_GRID:
            for c in COEFF_GRID:
                canon = canonicalize_coeffs_n((a, b, c))
                if canon is None or canon in seen:
                    continue
                seen.add(canon)
                items.append(
                    LinearCandidate(
                        coeffs=canon,
                        keys=keys,
                        form="a*decimal_length + b*factor_count + c*omega",
                    )
                )
    return tuple(items)


def evaluate_linear(
    candidate: LinearCandidate,
    transitions: tuple[ObservedTransition, ...],
    exceptional: set[int | str],
    classify,
) -> LinearResult:
    for item in transitions:
        if item.source in exceptional:
            continue
        if item.source == item.image:
            continue
        v_src = candidate.evaluate(item.source_features)
        v_img = candidate.evaluate(item.image_features)
        if v_img < v_src:
            continue
        kind, reason = classify(item, candidate, v_src, v_img)
        return LinearResult(
            candidate=candidate,
            survived=False,
            counterexample=item,
            v_source=v_src,
            v_image=v_img,
            failure_class=kind,
            failure_reason=reason,
            source_features=item.source_features.as_dict(),
            image_features=item.image_features.as_dict(),
        )
    return LinearResult(
        candidate=candidate,
        survived=True,
        counterexample=None,
        v_source=None,
        v_image=None,
        failure_class=None,
    )


def _from_ranking_result(result) -> LinearResult:
    candidate = LinearCandidate(
        coeffs=result.candidate.coeffs,
        keys=("log_bit", "digit", "residue"),
        form="a*log_bit + b*digit + c*parity on T^2",
    )
    kind = None
    if result.failure_class is not None:
        kind = Phase1Failure.COMPOSED_GROWTH
        if result.counterexample is not None:
            src = result.counterexample.source_features
            img = result.counterexample.image_features
            if img.abs_value <= src.abs_value and src.residue != img.residue:
                kind = Phase1Failure.PARITY_COORDINATE
            elif img.abs_value <= src.abs_value:
                kind = Phase1Failure.FLOOR_EFFECT
    return LinearResult(
        candidate=candidate,
        survived=result.survived,
        counterexample=result.counterexample,
        v_source=result.v_source,
        v_image=result.v_image,
        failure_class=kind,
        failure_reason=result.failure_reason,
        source_features=None
        if result.counterexample is None
        else result.counterexample.source_features.as_dict(),
        image_features=None
        if result.counterexample is None
        else result.counterexample.image_features.as_dict(),
    )


def _coherent_size(candidate: LinearCandidate | RankingCandidate) -> bool:
    if isinstance(candidate, RankingCandidate):
        return candidate.a + candidate.b > 0
    data = dict(zip(candidate.keys, candidate.coeffs))
    return data.get("log_bit", 0) + data.get("digit", 0) > 0


def _coherent_gap(candidate: LinearCandidate) -> bool:
    data = dict(zip(candidate.keys, candidate.coeffs))
    return data.get("reverse_gap", 0) > 0


def _coherent_piecewise(candidate: LinearCandidate) -> bool:
    data = dict(zip(candidate.keys, candidate.coeffs))
    if data.get("digit", 0) < 0:
        return False
    return data.get("digit", 0) > 0 or data.get("factor_count", 0) > 0


def _quality(result: LinearResult) -> tuple:
    if isinstance(result.candidate, RankingCandidate):
        coeffs = result.candidate.coeffs
    else:
        coeffs = result.candidate.coeffs
    l0 = sum(1 for item in coeffs if item != 0)
    l1 = sum(abs(item) for item in coeffs)
    return (l0, l1, coeffs)


def _representative(failures: tuple[LinearResult, ...]) -> tuple[LinearResult, ...]:
    best: dict[Phase1Failure, LinearResult] = {}
    for item in failures:
        kind = item.failure_class
        if kind is None or item.counterexample is None:
            continue
        current = best.get(kind)
        if current is None or current.counterexample is None:
            best[kind] = item
            continue
        try:
            if abs(int(item.counterexample.source)) < abs(int(current.counterexample.source)):
                best[kind] = item
        except (TypeError, ValueError):
            pass
    return tuple(best[kind] for kind in Phase1Failure if kind in best)


def classify_composed(item: ObservedTransition, candidate, v_src: int, v_img: int):
    del candidate, v_src, v_img
    src = item.source_features
    img = item.image_features
    if img.abs_value > src.abs_value or img.digit > src.digit or img.log_bit > src.log_bit:
        return (
            Phase1Failure.COMPOSED_GROWTH,
            "odd floor-power growth overwhelms the following even square-root contraction",
        )
    if src.residue != img.residue:
        return (
            Phase1Failure.PARITY_COORDINATE,
            "two-step parity change defeats the ranking coordinate",
        )
    return (
        Phase1Failure.FLOOR_EFFECT,
        "integer floor on the even contraction does not restore a strict decrease",
    )


def classify_gap(item: ObservedTransition, candidate: LinearCandidate, v_src: int, v_img: int):
    del candidate, v_src, v_img
    src_gap = item.source_features.extra.get("reverse_gap", 0)
    img_gap = item.image_features.extra.get("reverse_gap", 0)
    if src_gap == 0 and img_gap > src_gap:
        return (
            Phase1Failure.PALINDROME_NOT_ATTRACTOR,
            "a palindrome (reverse_gap=0) maps to a non-palindrome; palindromes are not an attractor",
        )
    if img_gap > src_gap:
        return (
            Phase1Failure.GAP_INCREASE,
            "reverse-plus-add increases the canonical digit reverse-gap",
        )
    return (
        Phase1Failure.FEATURE_INSUFFICIENT,
        "reverse_gap and the frozen scalar features do not strictly decrease",
    )


def classify_piecewise(item: ObservedTransition, candidate: LinearCandidate, v_src: int, v_img: int):
    del candidate, v_src, v_img
    src = item.source_features
    img = item.image_features
    if img.digit > src.digit:
        return (
            Phase1Failure.CONCAT_GROWTH,
            "factor concatenation increases decimal length on a composite-to-composite step",
        )
    src_f = src.extra.get("factor_count", 0)
    img_f = img.extra.get("factor_count", 0)
    if img_f >= src_f:
        return (
            Phase1Failure.FACTOR_NONDECREASE,
            "factor_count does not decrease on this composite-to-composite concatenation",
        )
    return (Phase1Failure.OTHER, "piecewise V_C fails to decrease on this composite transition")


def _mechanisms(results: tuple[LinearResult, ...]) -> tuple[str, ...]:
    seen: list[str] = []
    for item in results:
        if item.survived or not item.failure_reason or item.failure_reason in seen:
            continue
        seen.append(item.failure_reason)
    return tuple(seen[:6])


def falsify_juggler_composed(
    transitions: tuple[ObservedTransition, ...],
    *,
    exceptional: tuple[int, ...] = (1,),
    odd_odd_count: int = 0,
) -> Phase1TargetReport:
    if len(exceptional) > EXCEPTIONAL_K:
        raise ValueError("exceptional set larger than K=8")
    exceptional_set = set(exceptional)
    tested = [item for item in transitions if item.source not in exceptional_set and item.source != item.image]
    notes = [
        "Domain: observed odd x with T(x) even and T(T(x)) defined. Depth k=2 only.",
        "Odd-to-odd one-step states such as 3->5 are outside this hypothesis.",
    ]
    if len(tested) < 3:
        return Phase1TargetReport(
            target=JUGGLER,
            hypothesis="odd_even_composed_ranking",
            available_features=("log_bit", "digit=bit_length", "parity"),
            candidate_count=len(candidate_grid()),
            transition_depth=2,
            domain="odd x with T(x) even and T^2(x) defined, on the frozen window/orbit",
            exceptional_set=tuple(str(item) for item in exceptional),
            transitions_tested=len(tested),
            exactness="exact integer V on T^2; same Phase-0 coefficient grid",
            survivors=(),
            first_counterexamples=(),
            strongest=None,
            failure_mechanisms=("fewer than three odd-to-even composed transitions",),
            classification=JugglerVerdict.INSUFFICIENT_DATA.value,
            lean_status="not_yet_formalization_ready",
            next_proposal="symbolic_nonlinear_composition",
            notes=tuple(notes),
        )
    raw = tuple(evaluate_candidate(item, transitions, exceptional_set) for item in candidate_grid())
    results = tuple(_from_ranking_result(item) for item in raw)
    survivors = tuple(
        sorted(
            (item for item in results if item.survived and _coherent_size(item.candidate)),
            key=_quality,
        )
    )
    failures = tuple(item for item in results if not item.survived)
    mechanisms = _mechanisms(results)
    if survivors:
        verdict = JugglerVerdict.COMPOSED_RANKING_PROMISING
        nxt = "odd_even_composed_ranking"
        if odd_odd_count:
            notes.append(
                f"{odd_odd_count} observed odd-to-odd one-step transitions remain outside the composed domain."
            )
            nxt = "odd_odd_branch_composition"
    else:
        classes = {item.failure_class for item in failures}
        if Phase1Failure.COMPOSED_GROWTH in classes or Phase1Failure.FLOOR_EFFECT in classes:
            verdict = JugglerVerdict.COMPOSED_RANKING_NEEDS_RICHER_STATE
            nxt = "odd_odd_branch_composition"
        else:
            verdict = JugglerVerdict.COMPOSED_RANKING_IMPLAUSIBLE
            nxt = "symbolic_nonlinear_composition"
    strongest = survivors[0] if survivors else None
    formal = (
        "formalization_ready"
        if verdict is JugglerVerdict.COMPOSED_RANKING_PROMISING and strongest is not None
        else "not_yet_formalization_ready"
    )
    return Phase1TargetReport(
        target=JUGGLER,
        hypothesis="odd_even_composed_ranking",
        available_features=("log_bit", "digit=bit_length", "parity"),
        candidate_count=len(candidate_grid()),
        transition_depth=2,
        domain="odd x with T(x) even and T^2(x) defined, on the frozen window/orbit",
        exceptional_set=tuple(str(item) for item in exceptional),
        transitions_tested=len(tested),
        exactness="exact integer V(T(T(x)))<V(x); Phase-0 7^3 grid, no enlargement",
        survivors=survivors,
        first_counterexamples=_representative(failures),
        strongest=strongest,
        failure_mechanisms=mechanisms,
        classification=verdict.value,
        lean_status=formal,
        next_proposal=nxt,
        notes=tuple(notes),
    )


def falsify_reverse_gap(
    transitions: tuple[ObservedTransition, ...],
    *,
    exceptional: tuple[int, ...] = (0,),
) -> Phase1TargetReport:
    if len(exceptional) > EXCEPTIONAL_K:
        raise ValueError("exceptional set larger than K=8")
    exceptional_set = set(exceptional)
    tested = [item for item in transitions if item.source not in exceptional_set and item.source != item.image]
    candidates = reverse_gap_grid()
    notes = [
        "reverse_gap is the L1 digit discrepancy between the canonical MSD word and its reverse.",
        "One-step V(T(x))<V(x) only. Scalar (a,b,c) held to a tiny Phase-0 basis; only d varies.",
    ]
    if len(tested) < 3:
        return Phase1TargetReport(
            target=REVERSE,
            hypothesis="reverse_gap_or_palindrome_ranking",
            available_features=("log_bit", "digit=bt_length", "parity", "reverse_gap"),
            candidate_count=len(candidates),
            transition_depth=1,
            domain="frozen reverse-add window/orbit; T(x)=x+bt_reverse(x)",
            exceptional_set=tuple(str(item) for item in exceptional),
            transitions_tested=len(tested),
            exactness="exact integer linear form including reverse_gap",
            survivors=(),
            first_counterexamples=(),
            strongest=None,
            failure_mechanisms=("fewer than three exact transitions",),
            classification=ReverseVerdict.INSUFFICIENT_DATA.value,
            lean_status="not_yet_formalization_ready",
            next_proposal="symbolic_nonlinear_composition",
            notes=tuple(notes),
        )
    results = tuple(
        evaluate_linear(item, transitions, exceptional_set, classify_gap) for item in candidates
    )
    survivors = tuple(
        sorted(
            (item for item in results if item.survived and _coherent_gap(item.candidate)),
            key=_quality,
        )
    )
    failures = tuple(item for item in results if not item.survived)
    mechanisms = _mechanisms(results)
    classes = {item.failure_class for item in failures}
    if survivors:
        verdict = ReverseVerdict.REVERSE_GAP_PROMISING
        nxt = "reverse_gap_or_palindrome_ranking"
    elif Phase1Failure.PALINDROME_NOT_ATTRACTOR in classes:
        verdict = ReverseVerdict.REVERSE_GAP_IMPLAUSIBLE
        nxt = "symbolic_nonlinear_composition"
        notes.append(
            "Palindrome defect ranks toward palindromes, but reverse-plus-add sends palindromes away."
        )
    elif Phase1Failure.GAP_INCREASE in classes:
        verdict = ReverseVerdict.REVERSE_GAP_NEEDS_RICHER_STATE
        nxt = "carry_or_3adic_reverse_gap"
    else:
        verdict = ReverseVerdict.REVERSE_GAP_IMPLAUSIBLE
        nxt = "symbolic_nonlinear_composition"
    strongest = survivors[0] if survivors else None
    formal = (
        "formalization_ready"
        if verdict is ReverseVerdict.REVERSE_GAP_PROMISING and strongest is not None
        else "not_yet_formalization_ready"
    )
    return Phase1TargetReport(
        target=REVERSE,
        hypothesis="reverse_gap_or_palindrome_ranking",
        available_features=("log_bit", "digit=bt_length", "parity", "reverse_gap"),
        candidate_count=len(candidates),
        transition_depth=1,
        domain="frozen reverse-add window/orbit; T(x)=x+bt_reverse(x)",
        exceptional_set=tuple(str(item) for item in exceptional),
        transitions_tested=len(tested),
        exactness="exact integer V; reverse_gap is L1 of canonical MSD digits vs reverse",
        survivors=survivors,
        first_counterexamples=_representative(failures),
        strongest=strongest,
        failure_mechanisms=mechanisms,
        classification=verdict.value,
        lean_status=formal,
        next_proposal=nxt,
        notes=tuple(notes),
    )


def falsify_home_piecewise(
    composite_transitions: tuple[ObservedTransition, ...],
    *,
    terminal_entries: tuple[ObservedTransition, ...] = (),
) -> Phase1TargetReport:
    candidates = piecewise_grid()
    tested = [item for item in composite_transitions if item.source != item.image]
    notes = [
        "V_C is tested only on composite x with composite T(x).",
        "Composite-to-prime steps are terminal-region entries, not required decreases.",
        f"Recorded terminal entries: {len(terminal_entries)}.",
    ]
    if len(tested) < 3:
        return Phase1TargetReport(
            target=HOME,
            hypothesis="composite_concat_piecewise_ranking",
            available_features=("decimal_length", "factor_count=Omega", "omega=distinct primes"),
            candidate_count=len(candidates),
            transition_depth=1,
            domain="composite x with composite T(x) on the frozen window/orbit",
            exceptional_set=(),
            transitions_tested=len(tested),
            exactness="exact integer V_C on composite-to-composite steps",
            survivors=(),
            first_counterexamples=(),
            strongest=None,
            failure_mechanisms=("fewer than three composite-to-composite transitions",),
            classification=HomeVerdict.INSUFFICIENT_DATA.value,
            lean_status="not_yet_formalization_ready",
            next_proposal="symbolic_nonlinear_composition",
            notes=tuple(notes),
        )
    results = tuple(evaluate_linear(item, tuple(tested), set(), classify_piecewise) for item in candidates)
    survivors = tuple(
        sorted(
            (item for item in results if item.survived and _coherent_piecewise(item.candidate)),
            key=_quality,
        )
    )
    failures = tuple(item for item in results if not item.survived)
    mechanisms = _mechanisms(results)
    classes = {item.failure_class for item in failures}
    if survivors:
        verdict = HomeVerdict.PIECEWISE_RANKING_PROMISING
        nxt = "composite_concat_piecewise_ranking"
    elif Phase1Failure.CONCAT_GROWTH in classes or Phase1Failure.FACTOR_NONDECREASE in classes:
        verdict = HomeVerdict.PIECEWISE_RANKING_NEEDS_RICHER_STATE
        nxt = "concat_word_composition"
    else:
        verdict = HomeVerdict.PIECEWISE_RANKING_IMPLAUSIBLE
        nxt = "symbolic_nonlinear_composition"
    strongest = survivors[0] if survivors else None
    formal = (
        "formalization_ready"
        if verdict is HomeVerdict.PIECEWISE_RANKING_PROMISING and strongest is not None
        else "not_yet_formalization_ready"
    )
    return Phase1TargetReport(
        target=HOME,
        hypothesis="composite_concat_piecewise_ranking",
        available_features=("decimal_length", "factor_count=Omega", "omega=distinct primes"),
        candidate_count=len(candidates),
        transition_depth=1,
        domain="composite x with composite T(x); primes are the terminal regime",
        exceptional_set=(),
        transitions_tested=len(tested),
        exactness="exact integer V_C; features from existing factor_trial, no new factorization engine",
        survivors=survivors,
        first_counterexamples=_representative(failures),
        strongest=strongest,
        failure_mechanisms=mechanisms,
        classification=verdict.value,
        lean_status=formal,
        next_proposal=nxt,
        notes=tuple(notes),
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


def updated_proposals(report: Phase1TargetReport) -> AttackProposalDossier:
    promising = report.classification.endswith("_PROMISING")
    if promising:
        items = (
            _proposal(
                1,
                report.hypothesis,
                "bounded exact survivor on the Phase-1 enriched domain",
                "Specify a ranking attack on this restricted transition relation only.",
                "Replay the recorded finite inequalities; do not enlarge the grid.",
                "ranking-function synthesis",
                "BOUNDED_SURVIVOR certificate, not a global termination theorem",
                "A transition in the recorded domain on which the surviving form fails.",
                novelty=NoveltyRisk.MEDIUM,
                scope=ImplementationScope.MEDIUM,
                confidence=Confidence.MEDIUM,
                reason="Phase-1 survivor is exact on a bounded sample only",
            ),
            _proposal(
                2,
                "proof_guided_hypothesis_refinement",
                "the surviving inequalities are finite and exact",
                "Package the finite decrease identities as Lean obligations.",
                "Replay V(T^k(x))<V(x) on the recorded pairs.",
                "proof-guided hypothesis refinement",
                "formalization-ready finite lemma",
                "A listed pair violates the recorded inequality.",
                novelty=NoveltyRisk.LOW,
                scope=ImplementationScope.SMALL,
                confidence=Confidence.MEDIUM,
                reason="finite identities may already be the definition",
            ),
            _proposal(
                3,
                "basin_preimage_grammar",
                "a ranking on one branch does not characterize the basin",
                "Couple the ranking sublevel sets with predecessor structure.",
                "Intersect sublevel sets with exact preimages of the declared core.",
                "symbolic predecessor construction",
                "quotient or splitting pair",
                "Two states with the same V-sublevel and different reachability.",
                novelty=NoveltyRisk.MEDIUM,
                scope=ImplementationScope.MEDIUM,
                confidence=Confidence.LOW,
                reason="basin language remains independent of a restricted ranking",
            ),
        )
    else:
        items = (
            _proposal(
                1,
                report.next_proposal,
                report.failure_mechanisms[0] if report.failure_mechanisms else "enriched ranking failed",
                "The Phase-1 enrichment does not repair the scalar obstruction.",
                "Move to the mapping-suggested competitor rather than enlarging the ranking grid.",
                "symbolic nonlinear branch composition"
                if "compos" in report.next_proposal
                else "symbolic predecessor construction"
                if "basin" in report.next_proposal
                else "symbolic nonlinear branch composition",
                "exact iterate identity, growth law, or a closed failing branch",
                "A cylinder whose composed expression disagrees with exact I/O.",
                novelty=NoveltyRisk.HIGH,
                scope=ImplementationScope.LARGE,
                confidence=Confidence.MEDIUM,
                reason="Phase-1 showed the named enrichment is not yet an attack",
            ),
            _proposal(
                2,
                "basin_preimage_grammar",
                "size and enriched scalar features do not see the attractor",
                "Characterize predecessor states of the declared core.",
                "Bounded preimage with a residue/word quotient.",
                "symbolic predecessor construction",
                "regular-preimage lemma or splitting pair",
                "Two predecessor states indistinguishable by the quotient.",
                novelty=NoveltyRisk.MEDIUM,
                scope=ImplementationScope.MEDIUM,
                confidence=Confidence.MEDIUM,
                reason="basin language is independent of ranking collapse",
            ),
            _proposal(
                3,
                report.hypothesis,
                "Phase-1 enrichment failed; ranking is demoted, not deleted",
                "Revisit only with a feature this phase marked unavailable.",
                "Do not enlarge the coefficient grid of the same coordinates.",
                "ranking-function synthesis",
                "ranking certificate using a genuinely new coordinate",
                "The new coordinate still fails to decrease on an exact transition.",
                novelty=NoveltyRisk.HIGH,
                scope=ImplementationScope.LARGE,
                confidence=Confidence.LOW,
                reason="Phase-1 showed the named enrichment is insufficient",
            ),
        )
    return AttackProposalDossier(
        proposals=items,
        campaign_id=report.target,
        notes=("updated from ranking Phase-1 falsifier; not executed",),
    )


def decide_phase1(reports: tuple[Phase1TargetReport, ...]) -> tuple[Phase1Decision, str]:
    classes = {item.target: item.classification for item in reports}
    promising = [item for item in reports if item.classification.endswith("_PROMISING")]
    insufficient = [item for item in reports if item.classification.endswith("INSUFFICIENT_DATA")]
    if insufficient and not promising:
        return (
            Phase1Decision.ABANDON_RANKING,
            "a Phase-1 hypothesis lacked enough exact transitions",
        )
    if len(promising) == len(reports) and reports:
        return (
            Phase1Decision.PROMOTE_RANKING,
            "every enriched hypothesis has a bounded exact survivor",
        )
    if promising:
        return (
            Phase1Decision.MIXED,
            "enriched ranking survives on a restricted domain but not as a uniform attack family",
        )
    richer = [
        item
        for item in reports
        if item.classification.endswith("_NEEDS_RICHER_STATE")
    ]
    if len(richer) >= 2:
        return (
            Phase1Decision.REFINE_RANKING,
            "enriched templates fail, but failures name one further small composition/feature gap",
        )
    del classes
    return (
        Phase1Decision.ABANDON_RANKING,
        "enriched hypotheses fail on exact transitions without a shared next ranking language",
    )


def phase1_payload(
    reports: tuple[Phase1TargetReport, ...],
    *,
    decision: Phase1Decision,
    decision_reason: str,
) -> dict[str, Any]:
    matrix = []
    for item in reports:
        survivors = len(item.survivors)
        if survivors:
            first = "none on the stated domain"
            lesson = next(
                (note for note in item.notes if "odd-to-odd" in note or "outside" in note),
                "bounded T^k decrease on the stated domain",
            )
        else:
            first = ""
            if item.first_counterexamples:
                cex = item.first_counterexamples[0].counterexample
                if cex is not None:
                    first = f"{cex.source} -> {cex.image}"
            lesson = item.failure_mechanisms[0] if item.failure_mechanisms else (
                item.notes[0] if item.notes else ""
            )
        matrix.append(
            {
                "target": item.target,
                "hypothesis": item.hypothesis,
                "survivors": survivors,
                "first_failure": first,
                "structural_lesson": lesson,
                "classification": item.classification,
            }
        )
    return {
        "engine_control_version": ENGINE_CONTROL_VERSION,
        "source_engine": "v2.3",
        "experimental_status": "PHASE_1_ENRICHED_RANKING_FALSIFIER",
        "ranking_phase1_decision": decision.value,
        "decision_reason": decision_reason,
        "formalization_ready": "not_yet_formalization_ready"
        if decision is not Phase1Decision.PROMOTE_RANKING
        else "formalization_ready",
        "target_matrix": matrix,
        "targets": [item.as_dict() for item in reports],
        "updated_proposals": {item.target: updated_proposals(item).as_dict() for item in reports},
    }


def render_phase1_markdown(payload: Mapping[str, Any]) -> str:
    lines = [
        "# Ranking-function Phase-1 enriched falsifier",
        "",
        "Status: **PHASE_1_ENRICHED_RANKING_FALSIFIER**",
        "",
        "This is not a ranking synthesizer and not a termination proof.",
        "Phase 0 parked scalar one-step ranking. Phase 1 tests the three",
        "named enrichments on the same frozen transition tables.",
        "",
        "## Branch budget",
        "",
        "```text",
        "Mathematical target     Do the three Phase-0 enrichments survive exact",
        "                        bounded falsification on their intended domains?",
        "Novelty hypothesis      k=2 odd-even composition, reverse_gap, or",
        "                        composite-versus-prime piecewise V_C might repair",
        "                        the scalar obstruction without a general synthesizer.",
        "Falsifier               Each named form fails on an exact transition in its",
        "                        stated domain, without a shared next ranking language.",
        "Existing machinery      Phase-0 grid; frozen windows/orbits; encode/bt_reverse;",
        "                        factor_trial / concat_from_factors.",
        "Maximum Phase-1 scope   k=2 only; reverse_gap L1 on canonical digits; V_C on",
        "                        composite-to-composite; no grid enlargement.",
        "Promotion criterion     A nontrivial bounded survivor on a stated domain,",
        "                        not a restatement of an existing halt.",
        "Stop criterion          k>2, 4D exhaustive search, new residual state,",
        "                        thawing DEFAULT_ATTACK_ORDER, or a global theorem claim.",
        "```",
        "",
        "## Metadata",
        "",
        f"- engine_control_version: `{payload['engine_control_version']}`",
        f"- source_engine: `{payload['source_engine']}`",
        f"- experimental_status: `{payload['experimental_status']}`",
        f"- family decision: **{payload['ranking_phase1_decision']}**",
        f"- decision reason: {payload['decision_reason']}",
        f"- formalization: `{payload['formalization_ready']}`",
        "",
    ]
    for report in payload["targets"]:
        lines.extend(_render_target(report))
    lines.extend(
        [
            "## Cross-hypothesis comparison",
            "",
            "| Target | Hypothesis | Survivors | First failure | Structural lesson | Classification |",
            "| --- | --- | ---: | --- | --- | --- |",
        ]
    )
    labels = {
        JUGGLER: "Juggler",
        REVERSE: "Reverse-add",
        HOME: "Home Prime",
    }
    for row in payload["target_matrix"]:
        target = labels.get(row["target"], row["target"])
        lesson = (row["structural_lesson"] or "—").replace("|", "/")
        first = (row["first_failure"] or "—").replace("|", "/")
        lines.append(
            f"| {target} | {row['hypothesis']} | {row['survivors']} | {first} | {lesson} | {row['classification']} |"
        )
    lines.extend(
        [
            "",
            "## Decision",
            "",
            f"**{payload['ranking_phase1_decision']}**",
            "",
            payload["decision_reason"] + ".",
            "",
            "A bounded survivor is `BOUNDED_SURVIVOR`, not `GLOBAL_RANKING`.",
            "Updated Top-3 proposals live in the machine-readable record and are not",
            "executed. Frozen v2.3 campaign files are unchanged.",
            "",
            "## Best next question",
            "",
        ]
    )
    decision = payload["ranking_phase1_decision"]
    if decision == "PROMOTE_RANKING":
        lines.append(
            "What is the smallest executable ranking attack that packages a Phase-1 "
            "bounded survivor without claiming a global termination theorem?"
        )
    elif decision == "MIXED":
        lines.append(
            "Should the surviving restricted ranking subfamily be specified as an "
            "attack, or should the failing targets move to symbolic composition first?"
        )
    elif decision == "REFINE_RANKING":
        lines.append(
            "What single additional composition rule or feature do the Phase-1 "
            "failures name, and can it be falsified without enlarging the grid?"
        )
    else:
        lines.append(
            "Should basin/preimage grammar or symbolic nonlinear composition be "
            "the next Phase-0-style falsifier instead of ranking?"
        )
    lines.append("")
    return "\n".join(lines)


def _render_target(report: Mapping[str, Any]) -> list[str]:
    survivors = report.get("survivors") or []
    strongest = report.get("strongest")
    cex = report.get("first_counterexamples") or []
    lines = [
        f"## Target `{report['target']}`",
        "",
        f"- Hypothesis: `{report['hypothesis']}`",
        f"- Available features: {', '.join(report['available_features'])}",
        f"- Candidate count: {report['candidate_count']}",
        f"- Survivor count: {report.get('survivor_count', len(report.get('survivors') or []))}",
        f"- Transition depth: {report['transition_depth']}",
        f"- Domain: {report['domain']}",
        f"- Exceptional set: {', '.join(report['exceptional_set']) or '(empty)'}",
        f"- Transitions tested: {report['transitions_tested']}",
        f"- Exactness: {report['exactness']}",
        f"- Classification: **{report['classification']}**",
        f"- Lean: `{report['lean_status']}`",
        f"- Next proposal: `{report['next_proposal']}`",
        "",
        "### Survivors",
        "",
    ]
    if survivors:
        for item in survivors[:12]:
            form = item["candidate"].get("form", "")
            coeffs = {k: item["candidate"][k] for k in item["candidate"] if k not in {"form", "q"}}
            lines.append(f"- `{form}` with {coeffs}")
    else:
        lines.append("None.")
    lines.extend(["", "### Strongest candidate", ""])
    if strongest:
        lines.append(f"`{strongest['candidate']}`")
    else:
        lines.append("None.")
    lines.extend(["", "### First counterexamples", ""])
    if cex:
        for item in cex:
            counter = item.get("counterexample") or {}
            lines.append(
                f"- `{item['candidate']}` fails at `{counter.get('source')} -> {counter.get('image')}` "
                f"({item.get('failure_class')}: {item.get('failure_reason')})"
            )
            if counter.get("source_features") is not None:
                lines.append(
                    f"  source features `{counter.get('source_features')}`; "
                    f"image features `{counter.get('image_features')}`; "
                    f"V {counter.get('v_source')} -> {counter.get('v_image')}"
                )
    else:
        lines.append("No failed candidates in the recorded prefix.")
    lines.extend(["", "### Failure mechanisms", ""])
    mechs = report.get("failure_mechanisms") or []
    if mechs:
        for item in mechs:
            lines.append(f"- {item}")
    else:
        lines.append("- none recorded")
    for note in report.get("notes") or ():
        lines.append(f"- {note}")
    lines.append("")
    return lines
