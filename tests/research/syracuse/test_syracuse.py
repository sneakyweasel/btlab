"""v2 diagnosis of the accelerated odd-only map. Does not import research.collatz."""

from __future__ import annotations

from pathlib import Path

from research.literature import get_reference
from research.open_problems import get_problem
from research.syracuse.discovery import (
    idempotent_counterexample,
    interval_leak_witness,
    lyapunov_n_witness,
    magnitude_drop_counterexample,
    orbit_of,
    seed_complexity_profile,
)
from research.syracuse.lean_export import ONE_THEOREM, closure_is_inconclusive, export_syracuse_targets
from research.syracuse.planner import (
    CLOSURE_HYPOTHESIS,
    CONTRACTION_HYPOTHESIS,
    GLOBAL_RESIDUAL_HYPOTHESIS,
    IDEMPOTENT_HYPOTHESIS,
    INTERVAL_HYPOTHESIS,
    LYAPUNOV_HYPOTHESIS,
    plan_syracuse,
    plan_syracuse_session,
)
from research.syracuse.problem import PROBLEM
from research.syracuse.records import RECORD_DIR, write_records
from research.syracuse.spec import SyracuseSpec, syracuse_spec, syracuse_step
from research_engine.attacks.control_word import compose_affine_steps
from research_engine.attacks.result import AttackStatus
from research_engine.core.observation import observe
from research_engine.core.problem_spec import ProblemSpec
from research_engine.core.semantics import ClaimKind
from research_engine.diagnosis.compare import core_match
from research_engine.diagnosis.corpus import ResearchCorpus
from research_engine.diagnosis.loop import diagnose, record_from_session
from research_engine.diagnosis.types import DeltaLevel, ResearchDecision
from research_engine.planner.hypothesis import HypothesisStatus


def test_adapter_sources_do_not_import_collatz():
    root = Path(__file__).resolve().parents[3] / "src" / "research" / "syracuse"
    for path in root.glob("*.py"):
        for line in path.read_text(encoding="utf-8").splitlines():
            stripped = line.strip()
            if stripped.startswith("from research.collatz") or stripped.startswith("import research.collatz"):
                raise AssertionError(f"{path.name} imports research.collatz")
            if stripped.startswith("from bt.metrics") or stripped.startswith("import bt.metrics"):
                raise AssertionError(f"{path.name} imports bt.metrics")


def test_lean_specialization_applies_generic_lemma():
    path = Path(__file__).resolve().parents[3] / "formal" / "Problems" / "Collatz" / "Syracuse.lean"
    text = path.read_text(encoding="utf-8")
    assert "sorry" not in text
    assert "admit" not in text
    assert "syracuseS_parameter_iff" in text
    assert "syracuse_compose_two" in text
    assert "syracuse_len_one_cycle_dvd" in text
    assert "syracuse_last_step_remainder" in text
    assert "syracuse_cycle_abs_obstruction" in text
    assert "syracuse_dvd_constant_of_dvd_remainder" in text
    assert "mul_pow_eq_iff_padicValInt" in text
    engine = Path(__file__).resolve().parents[3] / "formal" / "Problems" / "Engine" / "ParameterDomain.lean"
    engine_text = engine.read_text(encoding="utf-8")
    assert "sorry" not in engine_text
    assert "admit" not in engine_text
    control = Path(__file__).resolve().parents[3] / "formal" / "Problems" / "Engine" / "ControlWord.lean"
    control_text = control.read_text(encoding="utf-8")
    assert "sorry" not in control_text
    assert "admit" not in control_text
    assert "compose_two_affine" in control_text


def test_problem_is_registered():
    assert get_problem("syracuse") is PROBLEM
    assert PROBLEM.status == "EXPLORATORY"


def test_prior_art_references_are_registered():
    assert get_reference("lagarias-2010-3x+1-survey")["year"] == 2010
    assert get_reference("terras-1976-stopping-time")["year"] == 1976
    assert get_reference("tao-2019-almost-all-collatz")["year"] == 2019
    assert get_reference("lebel-2026")["problem_area"] == "collatz cycles"


def test_step_is_ordinary_integer_arithmetic():
    assert syracuse_step(1) == 1
    assert syracuse_step(3) == 5
    assert syracuse_step(5) == 1
    assert syracuse_step(7) == 11
    assert syracuse_step(27) == 41


def test_falsifiers():
    assert lyapunov_n_witness() == 1
    leak = interval_leak_witness()
    assert leak is not None
    assert leak[0] == 11 and leak[1] == 17
    assert magnitude_drop_counterexample(min_n=3) == 3
    assert idempotent_counterexample() is not None
    assert 1 in orbit_of(5)


def test_identity_observation_and_no_hints():
    spec = syracuse_spec()
    phase = spec.initial_phase()
    assert observe(spec, (27,), 0, phase) == 27
    assert spec.affine_system() is None
    assert spec.attack_context().reverse_preimage is None
    assert spec.attack_context().candidate_region is None
    assert spec.legal_controls((27,), phase) == (0,)
    assert spec.legal_controls((26,), phase) == ()


def test_spec_planner_and_hypotheses():
    spec = syracuse_spec()
    assert isinstance(spec, ProblemSpec)
    assert isinstance(spec, SyracuseSpec)
    report = plan_syracuse()
    assert closure_is_inconclusive(report)
    skipped = {item.attack for item in report.skipped}
    assert "modular" in skipped
    assert "spectral" in skipped
    assert "reverse" in skipped
    assert "block" in skipped
    piecewise = next(item for item in report.results if item.name == "piecewise_affine")
    assert piecewise.status is AttackStatus.OBSERVATION
    assert piecewise.evidence.get("census_kind") == "PARAMETERIZED_CENSUS"
    family = piecewise.evidence.get("family")
    assert isinstance(family, dict)
    assert family.get("p") == 3 and family.get("r") == 1
    assert family.get("q_base") == 2
    domain = next(item for item in report.results if item.name == "parameter_domain")
    assert domain.status is AttackStatus.SUPPORTED
    assert domain.scope.value == "EXACT"
    domains = domain.evidence.get("domains") or ()
    assert domains
    assert all(item.get("direction") == "EXACT" for item in domains)
    kinds = {item.get("domain", {}).get("kind") for item in domains}
    assert kinds <= {"maximal_divisibility", "conjunction"}
    assert "maximal_divisibility" in kinds or any(
        part.get("kind") == "maximal_divisibility"
        for item in domains
        for part in item.get("domain", {}).get("parts", ())
    )
    assert any(
        "v_2" in str(item.get("domain", {}).get("presentation", ""))
        or "v_2" in str(item.get("domain", {}))
        for item in domains
    )
    checks = domain.evidence.get("divisibility_checks") or ()
    assert checks
    assert all(item.get("direction") == "NECESSARY_ONLY" for item in checks)
    composed = next(item for item in report.results if item.name == "control_word")
    assert composed.status in {AttackStatus.SUPPORTED, AttackStatus.OBSERVATION}
    assert composed.evidence.get("reconstructed_affine") is None
    relations = composed.evidence.get("relations") or ()
    assert relations
    base = int(family.get("base") or family.get("q_base") or 2)
    p = int(family["p"])
    r = int(family["r"])
    item = next(item for item in relations if item["word"]["length"] >= 1)
    word = tuple(item["word"]["parameters"])
    expected = compose_affine_steps(tuple((base ** k, p, r) for k in word))
    assert (item["a"], item["b"], item["c"]) == expected
    constraints = composed.evidence.get("constraints") or ()
    assert any(entry.get("kind") == "CYCLE_CONSTRAINT" for entry in constraints)
    obstructed = next(item for item in report.results if item.name == "control_obstruction")
    assert obstructed.status is AttackStatus.SUPPORTED
    assert obstructed.evidence.get("reconstructed_affine") is None
    class_certs = [
        item
        for item in obstructed.evidence.get("certificates") or ()
        if item.get("scope") == "CLASS"
        and item.get("status") in {"PROVED", "LEAN_CERTIFIED"}
    ]
    assert class_certs
    functional = next(item for item in report.results if item.name == "functional")
    assert functional.status is AttackStatus.REFUTED
    assert next(
        item for item in report.hypotheses if item.id == CLOSURE_HYPOTHESIS.id
    ).status is HypothesisStatus.PARKED
    assert next(
        item for item in report.hypotheses if item.id == INTERVAL_HYPOTHESIS.id
    ).status is HypothesisStatus.REFUTED
    assert next(
        item for item in report.hypotheses if item.id == LYAPUNOV_HYPOTHESIS.id
    ).status is HypothesisStatus.REFUTED
    assert next(
        item for item in report.hypotheses if item.id == GLOBAL_RESIDUAL_HYPOTHESIS.id
    ).status is HypothesisStatus.PARKED
    assert next(
        item for item in report.hypotheses if item.id == CONTRACTION_HYPOTHESIS.id
    ).status is HypothesisStatus.REFUTED
    assert next(
        item for item in report.hypotheses if item.id == IDEMPOTENT_HYPOTHESIS.id
    ).status is HypothesisStatus.REFUTED


def test_diagnosis_is_not_finite_contracting():
    from research.juggler_sequence.planner import plan_map_session
    corpus = ResearchCorpus((plan_map_session().record,))
    session = plan_syracuse_session(corpus=corpus)
    assert session.diagnosis.fingerprint.numerical_contraction != "FINITE_CONTRACTING"
    assert session.diagnosis.fingerprint.eventual_region == "UNBOUNDED_SAMPLE"
    assert session.diagnosis.fingerprint.control_structure == "SINGLETON"
    assert session.diagnosis.fingerprint.piecewise_affine_structure == "PARAMETERIZED"
    assert session.diagnosis.fingerprint.latent_control == "PARAMETERIZED"
    assert session.diagnosis.fingerprint.parameter_domain == "EXACT"
    assert session.diagnosis.fingerprint.latent_control_algebra == "EXPLOITABLE"
    assert session.diagnosis.fingerprint.latent_control_obstruction == "RECURSIVE_INVARIANT"
    assert session.diagnosis.delta is not None
    assert session.diagnosis.delta.level is DeltaLevel.HIGH
    assert not core_match(session.diagnosis.fingerprint, corpus.records[0].fingerprint)
    assert session.decision is ResearchDecision.CONTINUE
    assert "certified" in session.decision_reason or "domain" in session.decision_reason
    assert session.diagnosis.coverage.status("growth") == "EXERCISED"
    assert session.diagnosis.coverage.status("infinite_reachable_trajectories") == "EXERCISED"
    assert session.diagnosis.coverage.status("valuation_dynamics") == "EXERCISED"
    assert session.diagnosis.coverage.status("latent_piecewise_affine_control") == "EXERCISED"
    assert session.diagnosis.coverage.status("parameter_domain_certification") == "EXERCISED"
    assert session.diagnosis.coverage.status("control_word_composition") == "EXERCISED"
    assert session.diagnosis.coverage.status("cycle_obstruction") == "EXERCISED"
    assert session.diagnosis.coverage.status("control_obstruction_calculus") == "EXERCISED"
    assert session.diagnosis.coverage.status("symbolic_multi_step_obstruction") == "EXERCISED"
    assert session.diagnosis.coverage.status("recursive_remainder_invariant") == "EXERCISED"
    assert session.diagnosis.coverage.status("branching_controls") == "INAPPLICABLE"


def test_profile_and_export(tmp_path):
    profile = seed_complexity_profile()
    assert profile.control_count == 1
    assert profile.raw_contribution_count is None
    report = plan_syracuse()
    targets = export_syracuse_targets(report)
    one = next(item for item in targets if item.lean_theorem == ONE_THEOREM)
    assert one.exportable
    assert all(not (item.kind is ClaimKind.LIVE and item.exportable) for item in targets)
    written = write_records(report, targets, directory=tmp_path)
    assert "skipped.yaml" in {path.name for path in written}
    assert RECORD_DIR.name == "syracuse"
