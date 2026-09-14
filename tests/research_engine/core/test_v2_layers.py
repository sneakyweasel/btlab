"""Engine v2 layers: observation, factorization, envelope, separation, quotient."""

from __future__ import annotations

from dataclasses import dataclass

from research_engine.attacks.envelope import (
    compare_envelope_to_reachable,
    envelope_from_interval,
    reachable_from_ints,
)
from research_engine.attacks.factorization import FactorizationAttack
from research_engine.attacks.result import AttackContext, AttackStatus
from research_engine.attacks.separation import separate_states
from research.linear_constraint_loops.spec import decrement_spec
from research_engine.behavior.mealy import minimize_mealy_count
from research_engine.behavior.profile import ComplexityProfile
from research_engine.behavior.quotient import quotient_from_states
from research_engine.core.contribution import (
    FactorizationStatus,
    check_control_factorization,
)
from research_engine.core.observation import has_output, observe
from research_engine.core.phase import IntPhase
from research_engine.core.semantics import CertificateKind, SearchScope
from tests.research_engine.core.test_attacks import CountdownSpec


@dataclass(frozen=True)
class ObservableCountdownSpec(CountdownSpec):
    def output(self, state: tuple[int, ...], control: int, phase: IntPhase | None = None) -> int:
        del phase
        return state[0] + control

    def raw_contribution(self, control: object) -> int:
        return int(control)


def test_observe_supports_two_and_three_argument_output():
    spec = ObservableCountdownSpec()
    phase = spec.initial_phase()
    assert has_output(spec) is True
    assert observe(spec, (0,), 1, phase) == 1
    assert has_output(CountdownSpec()) is False


def test_identity_raw_contribution_factors():
    spec = ObservableCountdownSpec()
    result = check_control_factorization(spec, states=((0,), (1,), (-1,)))
    assert result.status is FactorizationStatus.VERIFIED
    assert result.control_count == 3
    assert result.contribution_count == 3
    attack = FactorizationAttack().run(spec, AttackContext())
    assert attack.status is AttackStatus.SUPPORTED
    assert attack.certificate_kind is CertificateKind.EXACT_CLOSURE


def test_factorization_inapplicable_without_h():
    spec = CountdownSpec()
    result = check_control_factorization(spec)
    assert result.status is FactorizationStatus.INAPPLICABLE
    assert FactorizationAttack().applicable(spec, AttackContext()) is False


def test_envelope_holes_are_not_reachable_states():
    envelope = envelope_from_interval(-2, 2, as_states=True)
    reached = reachable_from_ints((-2, 0, 2), as_states=True)
    comparison = compare_envelope_to_reachable(envelope, reached)
    assert comparison.holes == frozenset({(-1,), (1,)})
    assert comparison.reachable_inside_envelope is True
    assert comparison.envelope_equals_reachable is False
    assert envelope.parameterization == "[-2,2]"
    assert reached.certificate_kind is CertificateKind.EXACT_CLOSURE


def test_separation_distinguishes_bound_from_equivalence():
    spec = ObservableCountdownSpec(start_remaining=3)
    separated = separate_states(spec, (0,), (1,))
    assert separated.separated is True
    assert separated.scope is SearchScope.EXACT
    assert separated.witness_length == 1
    same = separate_states(spec, (0,), (0,))
    assert same.separated is False
    assert same.scope is SearchScope.EXACT
    capped = separate_states(spec, (0,), (2,), max_depth=0)
    assert capped.separated is False
    assert capped.status is AttackStatus.INCONCLUSIVE
    assert capped.scope is SearchScope.BOUNDED


def test_quotient_count_matches_engine_mealy():

    def step(state, control):
        return (0,), int(control)

    class CollapseSpec(ObservableCountdownSpec):
        def transition(self, state, control, phase):
            del state, phase
            return (0,)

        def output(self, state, control, phase=None):
            del state, phase
            return int(control)

    collapse = CollapseSpec()
    states = ((0,),)
    result = quotient_from_states(collapse, states, complete=True)
    assert result.quotient_count == minimize_mealy_count(states, (-1, 0, 1), step)
    assert result.quotient_count == 1


def test_quotient_tolerates_empty_legal_controls():
    spec = decrement_spec(start=3)
    states = ((3,), (2,), (1,), (0,))
    result = quotient_from_states(spec, states, complete=True)
    assert result.reachable_state_count == 4
    assert result.quotient_count >= 4


def test_complexity_profile_omits_unset_fields():
    profile = ComplexityProfile(control_count=9, raw_contribution_count=3, reachable_state_count=1)
    text = profile.format_report()
    assert "raw controls: 9" in text
    assert "raw contribution values: 3" in text
    assert "symmetry count" not in text
    assert profile.populated_fields() == {
        "control_count": 9,
        "raw_contribution_count": 3,
        "reachable_state_count": 1,
    }
