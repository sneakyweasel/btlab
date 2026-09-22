"""``btlab research`` — inspect engine sessions. Not a prover."""

from __future__ import annotations

import argparse
from typing import cast

from research_engine.attacks.result import AttackStatus
from research_engine.benchmarks.pipeline import (
    load_benchmark,
    reproduce_checks,
    run_benchmark,
)
from research_engine.core.problem_spec import ProblemSpec
from research_engine.core.semantics import ClaimKind, SearchScope
from research_engine.planner.hypothesis import HypothesisStatus
from research_engine.diagnosis.loop import diagnose
from research_engine.planner.orchestrator import DEFERRED_ATTACKS, run_named_attack
from research_engine.report import (
    format_attack_result,
    format_diagnosis_report,
    format_planner_report,
    format_target_report,
)
from research_engine.verification.targets import targets_from_report


def add_research_subparser(subparsers: argparse._SubParsersAction) -> None:
    p = subparsers.add_parser(
        "research",
        help="experimental-dynamics planner and theorem targets",
    )
    c = p.add_subparsers(dest="research_cmd", required=True)
    p_an = c.add_parser("analyze", help="run the cheap-attack planner")
    p_an.add_argument(
        "problem",
        help="collatz, syracuse, or shared benchmark A-E; historical projects use --include-archive",
    )
    p_an.add_argument("--remaining", type=int, default=4)
    p_at = c.add_parser("attack", help="run one named cheap attack")
    p_at.add_argument("problem")
    p_at.add_argument("attack")
    p_at.add_argument("--remaining", type=int, default=4)
    p_re = c.add_parser("reproduce", help="check known fingerprints")
    p_re.add_argument("problem")
    p_re.add_argument("--remaining", type=int, default=4)
    p_rp = c.add_parser("report", help="print exportable theorem targets")
    p_rp.add_argument("problem")
    p_rp.add_argument("--remaining", type=int, default=4)


def run_research(args: argparse.Namespace) -> int:
    try:
        from research.scope import include_archive
        key = _normalize_problem(args.problem)
        if not include_archive() and key not in {'juggler_sequence', 'collatz_finite_descent', 'syracuse',
                                                'A', 'B', 'C', 'D', 'E'}:
            raise ValueError(f'{args.problem} is outside the active lab; use btlab --include-archive research ...')
        cmd = args.research_cmd
        if cmd == "analyze":
            return _analyze(args.problem, args.remaining)
        if cmd == "attack":
            return _attack(args.problem, args.attack, args.remaining)
        if cmd == "reproduce":
            return _reproduce(args.problem, args.remaining)
        if cmd == "report":
            return _report(args.problem, args.remaining)
    except ValueError as exc:
        print(exc)
        return 2
    raise ValueError(f"unknown research command {cmd!r}")


def _normalize_problem(name: str) -> str:
    key = name.strip()
    if key.lower() == "ostrowski":
        return "ostrowski"
    if key.lower() in {"balanced_ternary", "bt"}:
        return "balanced_ternary"
    if key.lower() in {"expanding_d", "expanding-d", "bt_expanding"}:
        return "expanding_d"
    if key.lower() in {"expanding_j2", "expanding-j2", "j2"}:
        return "expanding_j2"
    if key.lower() in {"expanding_j3", "expanding-j3", "j3"}:
        return "expanding_j3"
    if key.lower() in {"d_add", "d-add", "dadd"}:
        return "d_add"
    if key.lower() in {
        "signed_digit_residual",
        "signed-digit-residual",
        "sdr",
    }:
        return "signed_digit_residual"
    if key.lower() in {
        "signed_digit_residual_geometry",
        "signed-digit-residual-geometry",
        "sdrg",
        "sdr_geometry",
    }:
        return "signed_digit_residual_geometry"
    if key.lower() in {
        "signed_digit_residual_minimality",
        "signed-digit-residual-minimality",
        "sdrm",
        "sdr_minimality",
    }:
        return "signed_digit_residual_minimality"
    if key.lower() in {
        "signed_digit_constrained_controls",
        "signed-digit-constrained-controls",
        "sdcc",
        "sdr_constrained",
    }:
        return "signed_digit_constrained_controls"
    if key.lower() in {
        "signed_digit_short_horizon",
        "signed-digit-short-horizon",
        "sdsh",
        "sdr_horizon",
    }:
        return "signed_digit_short_horizon"
    if key.lower() in {
        "multiplicative_residual",
        "multiplicative-residual",
        "mul_residual",
        "mr",
    }:
        return "multiplicative_residual"
    if key.lower() in {
        "collatz",
        "collatz_finite_descent",
        "collatz-finite-descent",
        "cfd",
    }:
        return "collatz_finite_descent"
    if key.lower() in {
        "primes",
        "prime_residual",
        "prime-residual",
        "prime_residual_complexity",
        "prime-residual-complexity",
        "prc",
    }:
        return "prime_residual_complexity"
    if key.lower() in {
        "operator_dynamics",
        "operator-dynamics",
        "operator_dynamics_benchmark",
        "operator-dynamics-benchmark",
        "signed_p0",
        "signed-p0",
        "nsd",
    }:
        return "operator_dynamics_benchmark"
    if key.lower() in {
        "balanced_ternary_digit_sum_dynamics",
        "balanced-ternary-digit-sum-dynamics",
        "digit_sum",
        "digit-sum",
        "btds",
        "ds_dynamics",
    }:
        return "balanced_ternary_digit_sum_dynamics"
    if key.lower() in {
        "balanced_ternary_weight_dynamics",
        "balanced-ternary-weight-dynamics",
        "weight",
        "btw",
        "wd_dynamics",
    }:
        return "balanced_ternary_weight_dynamics"
    if key.lower() in {
        "balanced_ternary_weight_drift",
        "balanced-ternary-weight-drift",
        "weight_drift",
        "btdrift",
        "wdr",
    }:
        return "balanced_ternary_weight_drift"
    if key.lower() in {
        "syracuse",
        "accelerated_odd_map",
        "accelerated-odd-map",
    }:
        return "syracuse"
    letter = key.upper()
    if letter in {"A", "B", "C", "D", "E"}:
        return letter
    raise ValueError(
        f"unknown problem {name!r}; use ostrowski, balanced_ternary, expanding_d, expanding_j2, expanding_j3, d_add, signed_digit_residual, signed_digit_residual_geometry, signed_digit_residual_minimality, signed_digit_constrained_controls, signed_digit_short_horizon, multiplicative_residual, collatz, primes, operator_dynamics, balanced_ternary_digit_sum_dynamics, balanced_ternary_weight_dynamics, balanced_ternary_weight_drift, syracuse, or A-E"
    )


def _plan(problem: str, remaining: int):
    if problem == "ostrowski":
        from research.ostrowski.adapter import export_plan_targets, plan_np

        report = plan_np(remaining)
        targets = export_plan_targets(report)
        return report, targets
    if problem == "balanced_ternary":
        from research.balanced_ternary.adapter import export_plan_targets, plan_doubled_trit

        report = plan_doubled_trit(remaining)
        targets = export_plan_targets(report)
        return report, targets
    if problem == "expanding_d":
        from research.balanced_ternary.adapter import export_expanding_d_targets, plan_expanding_d

        report = plan_expanding_d(remaining)
        targets = export_expanding_d_targets(report)
        return report, targets
    if problem == "expanding_j2":
        from research.balanced_ternary.adapter import export_j2_targets, plan_expanding_j2

        report = plan_expanding_j2(remaining)
        targets = export_j2_targets(report)
        return report, targets
    if problem == "expanding_j3":
        from research.balanced_ternary.adapter import export_j3_targets, plan_expanding_j3

        report = plan_expanding_j3(remaining)
        targets = export_j3_targets(report)
        return report, targets
    if problem == "d_add":
        from research.balanced_ternary.adapter import export_d_add_targets, plan_d_add

        report = plan_d_add(remaining)
        targets = export_d_add_targets(report)
        return report, targets
    if problem == "signed_digit_residual":
        from research.signed_digit_residual.adapter import (
            export_signed_digit_targets,
            plan_signed_digit_residual,
        )

        report = plan_signed_digit_residual(remaining)
        targets = export_signed_digit_targets(report)
        return report, targets
    if problem == "signed_digit_residual_geometry":
        from research.signed_digit_residual_geometry.adapter import (
            export_geometry_targets,
            plan_signed_digit_residual_geometry,
        )

        report = plan_signed_digit_residual_geometry(remaining)
        targets = export_geometry_targets(report)
        return report, targets
    if problem == "signed_digit_residual_minimality":
        from research.signed_digit_residual_minimality.adapter import (
            export_minimality_targets,
            plan_signed_digit_residual_minimality,
        )

        report = plan_signed_digit_residual_minimality(remaining)
        targets = export_minimality_targets(report)
        return report, targets
    if problem == "signed_digit_constrained_controls":
        from research.signed_digit_constrained_controls.adapter import (
            export_constrained_targets,
            plan_signed_digit_constrained_controls,
        )

        report = plan_signed_digit_constrained_controls(remaining)
        targets = export_constrained_targets(report)
        return report, targets
    if problem == "signed_digit_short_horizon":
        from research.signed_digit_short_horizon.adapter import (
            export_short_horizon_targets,
            plan_signed_digit_short_horizon,
        )

        report = plan_signed_digit_short_horizon(remaining)
        targets = export_short_horizon_targets(report)
        return report, targets
    if problem == "multiplicative_residual":
        from research.multiplicative_residual.adapter import (
            export_multiplicative_targets,
            plan_multiplicative_residual,
        )

        report = plan_multiplicative_residual(remaining)
        targets = export_multiplicative_targets(report)
        return report, targets
    if problem == "collatz_finite_descent":
        from research.collatz_finite_descent.adapter import (
            export_collatz_finite_descent_targets,
            plan_collatz_finite_descent,
        )

        report = plan_collatz_finite_descent(remaining)
        targets = export_collatz_finite_descent_targets(report)
        return report, targets
    if problem == "prime_residual_complexity":
        from research.prime_residual_complexity.adapter import (
            export_prime_residual_targets,
            plan_prime_residual_complexity,
        )

        report = plan_prime_residual_complexity(remaining)
        targets = export_prime_residual_targets(report)
        return report, targets
    if problem == "operator_dynamics_benchmark":
        from research.operator_dynamics.signed_p0.adapter import (
            export_signed_p0_targets,
            plan_signed_p0,
        )

        report = plan_signed_p0(remaining)
        targets = export_signed_p0_targets(report)
        return report, targets
    if problem == "balanced_ternary_digit_sum_dynamics":
        from research.balanced_ternary_digit_sum_dynamics.adapter import (
            export_digit_sum_targets,
            plan_digit_sum_dynamics,
        )

        report = plan_digit_sum_dynamics(remaining)
        targets = export_digit_sum_targets(report)
        return report, targets
    if problem == "balanced_ternary_weight_dynamics":
        from research.balanced_ternary_weight_dynamics.adapter import (
            export_weight_targets,
            plan_weight_dynamics,
        )

        report = plan_weight_dynamics(remaining)
        targets = export_weight_targets(report)
        return report, targets
    if problem == "balanced_ternary_weight_drift":
        from research.balanced_ternary_weight_drift.adapter import (
            export_weight_drift_targets,
            plan_weight_drift,
        )

        report = plan_weight_drift(remaining)
        targets = export_weight_drift_targets(report)
        return report, targets
    if problem == "syracuse":
        from research.syracuse.adapter import export_syracuse_targets, plan_syracuse

        report = plan_syracuse(remaining)
        targets = export_syracuse_targets(report)
        return report, targets
    report = run_benchmark(problem)
    return report, targets_from_report(report, problem=f"benchmark_{problem}")


def _analyze(problem_name: str, remaining: int) -> int:
    problem = _normalize_problem(problem_name)
    report, _targets = _plan(problem, remaining)
    print(format_planner_report(report, problem=problem), end="")
    spec, context = _spec_and_context(problem, remaining)
    print(format_diagnosis_report(diagnose(spec, report, context)), end="")
    return 0


def _spec_and_context(problem: str, remaining: int):
    if problem == "ostrowski":
        from research.ostrowski.spec import ostrowski_spec
        from research.ostrowski.zero_value_kernel import SHORTEST_NONRESET
        from research_engine.algebra.linear_functionals import LinearFunctional

        spec = ostrowski_spec(remaining)
        return spec, spec.attack_context(
            functional=LinearFunctional((0, 0, 1)),
            word=SHORTEST_NONRESET,
        )
    if problem == "balanced_ternary":
        from research.balanced_ternary.spec import doubled_trit_spec

        spec = doubled_trit_spec(remaining)
        return spec, spec.attack_context()
    if problem == "expanding_d":
        from research.balanced_ternary.expanding_spec import expanding_d_spec

        spec = expanding_d_spec(remaining)
        return spec, spec.attack_context()
    if problem == "expanding_j2":
        from research.balanced_ternary.expanding_j2_spec import expanding_j2_spec

        spec = expanding_j2_spec(remaining)
        return spec, spec.attack_context()
    if problem == "expanding_j3":
        from research.balanced_ternary.expanding_j3_spec import expanding_j3_spec

        spec = expanding_j3_spec(remaining)
        return spec, spec.attack_context()
    if problem == "d_add":
        from research.balanced_ternary.d_add_spec import d_add_spec

        spec = d_add_spec(remaining)
        return spec, spec.attack_context()
    if problem == "signed_digit_residual":
        from research.signed_digit_residual.spec import signed_digit_spec

        spec = signed_digit_spec(remaining)
        return spec, spec.attack_context()
    if problem == "signed_digit_residual_geometry":
        from research.signed_digit_residual_geometry.spec import geometry_spec

        spec = geometry_spec(remaining)
        return spec, spec.attack_context()
    if problem == "signed_digit_residual_minimality":
        from research.signed_digit_residual_minimality.spec import minimality_spec

        spec = minimality_spec(remaining)
        return spec, spec.attack_context()
    if problem == "signed_digit_constrained_controls":
        from research.signed_digit_constrained_controls.spec import constrained_spec

        spec = constrained_spec(remaining)
        return spec, spec.attack_context()
    if problem == "signed_digit_short_horizon":
        from research.signed_digit_short_horizon.spec import short_horizon_spec

        spec = short_horizon_spec(remaining)
        return spec, spec.attack_context()
    if problem == "multiplicative_residual":
        from research.multiplicative_residual.spec import product_spec

        spec = product_spec(remaining)
        return spec, spec.attack_context()
    if problem == "collatz_finite_descent":
        from research.collatz_finite_descent.spec import shortcut_spec

        spec = shortcut_spec(remaining)
        return spec, spec.attack_context()
    if problem == "prime_residual_complexity":
        from research.prime_residual_complexity.spec import sieve_spec

        spec = sieve_spec(remaining)
        return spec, spec.attack_context()
    if problem == "operator_dynamics_benchmark":
        from research.operator_dynamics.signed_p0.spec import signed_p0_spec

        spec = signed_p0_spec(remaining)
        return spec, spec.attack_context()
    if problem == "balanced_ternary_digit_sum_dynamics":
        from research.balanced_ternary_digit_sum_dynamics.spec import digit_sum_spec

        spec = digit_sum_spec(remaining)
        return spec, spec.attack_context()
    if problem == "balanced_ternary_weight_dynamics":
        from research.balanced_ternary_weight_dynamics.spec import weight_dynamics_spec

        spec = weight_dynamics_spec(remaining)
        return spec, spec.attack_context()
    if problem == "balanced_ternary_weight_drift":
        from research.balanced_ternary_weight_drift.spec import weight_drift_spec

        spec = weight_drift_spec(remaining)
        return spec, spec.attack_context()
    if problem == "syracuse":
        from research.syracuse.spec import syracuse_spec

        spec = syracuse_spec(remaining)
        return spec, spec.attack_context()
    return load_benchmark(problem)


def _attack(problem_name: str, attack: str, remaining: int) -> int:
    problem = _normalize_problem(problem_name)
    spec, context = _spec_and_context(problem, remaining)
    try:
        result = run_named_attack(attack, cast(ProblemSpec, spec), context)
    except KeyError:
        print(f"unknown attack {attack!r}")
        return 2
    print(format_attack_result(result))
    if attack in DEFERRED_ATTACKS or result.status is AttackStatus.INAPPLICABLE:
        return 2
    return 0


def _reproduce(problem_name: str, remaining: int) -> int:
    problem = _normalize_problem(problem_name)
    report, targets = _plan(problem, remaining)
    print(format_planner_report(report, problem=problem), end="")
    if problem == "ostrowski":
        failures = _ostrowski_reproduce_failures(report, targets)
    elif problem == "balanced_ternary":
        failures = _balanced_ternary_reproduce_failures(report, targets)
    elif problem == "expanding_d":
        failures = _expanding_d_reproduce_failures(report, targets)
    elif problem == "expanding_j2":
        failures = _expanding_j2_reproduce_failures(report, targets)
    elif problem == "expanding_j3":
        failures = _expanding_j3_reproduce_failures(report, targets)
    elif problem == "d_add":
        failures = _d_add_reproduce_failures(report, targets)
    elif problem == "signed_digit_residual":
        failures = _signed_digit_residual_reproduce_failures(report, targets)
    elif problem == "signed_digit_residual_geometry":
        failures = _signed_digit_residual_geometry_reproduce_failures(report, targets)
    elif problem == "signed_digit_residual_minimality":
        failures = _signed_digit_residual_minimality_reproduce_failures(report, targets)
    elif problem == "signed_digit_constrained_controls":
        failures = _signed_digit_constrained_controls_reproduce_failures(report, targets)
    elif problem == "signed_digit_short_horizon":
        failures = _signed_digit_short_horizon_reproduce_failures(report, targets)
    elif problem == "multiplicative_residual":
        failures = _multiplicative_residual_reproduce_failures(report, targets)
    elif problem == "collatz_finite_descent":
        failures = _collatz_finite_descent_reproduce_failures(report, targets)
    elif problem == "prime_residual_complexity":
        failures = _prime_residual_reproduce_failures(report, targets)
    elif problem == "operator_dynamics_benchmark":
        failures = _operator_dynamics_reproduce_failures(report, targets)
    elif problem == "balanced_ternary_digit_sum_dynamics":
        failures = _digit_sum_dynamics_reproduce_failures(report, targets)
    elif problem == "balanced_ternary_weight_dynamics":
        failures = _weight_dynamics_reproduce_failures(report, targets)
    elif problem == "balanced_ternary_weight_drift":
        failures = _weight_drift_reproduce_failures(report, targets)
    elif problem == "syracuse":
        failures = _syracuse_reproduce_failures(report, targets)
    else:
        failures = reproduce_checks(problem, report)
    if failures:
        print("reproduce: FAIL")
        for item in failures:
            print(f"  {item}")
        return 1
    print("reproduce: ok")
    return 0


def _report(problem_name: str, remaining: int) -> int:
    problem = _normalize_problem(problem_name)
    report, targets = _plan(problem, remaining)
    print(format_planner_report(report, problem=problem), end="")
    print(format_target_report(targets), end="")
    return 0


def _ostrowski_reproduce_failures(report, targets) -> tuple[str, ...]:
    from research.ostrowski.lean_export import HUB_THEOREM, STEP_FST_THEOREM
    from research.ostrowski.negative_knowledge import L0_HYPOTHESIS

    failures: list[str] = []
    live = next(
        (item for item in report.hypotheses if item.id == L0_HYPOTHESIS.id),
        None,
    )
    if (
        live is None
        or live.status is not HypothesisStatus.PARKED
        or live.kind is not ClaimKind.LIVE
        or live.intended_scope is not SearchScope.EXACT
    ):
        failures.append("ostrowski: |L_0| is not PARKED EXACT LIVE")
    modular = next((item for item in targets if item.attack == "modular"), None)
    if (
        modular is None
        or not modular.exportable
        or modular.lean_theorem != STEP_FST_THEOREM
    ):
        failures.append("ostrowski: modular is not linked to step_fst_dvd_three")
    block = next((item for item in targets if item.attack == "block"), None)
    if block is None or block.lean_theorem != HUB_THEOREM:
        failures.append("ostrowski: hub block is not linked to hub_nonreset")
    if any(item.kind is ClaimKind.LIVE and item.exportable for item in targets):
        failures.append("ostrowski: exported a LIVE target")
    return tuple(failures)


def _balanced_ternary_reproduce_failures(report, targets) -> tuple[str, ...]:
    from research.balanced_ternary.lean_export import CLOSURE_THEOREM, closure_is_exact_three
    from research.balanced_ternary.planner import CLOSURE_HYPOTHESIS

    failures: list[str] = []
    if not closure_is_exact_three(report):
        failures.append("balanced_ternary: closure is not EXACT size 3")
    recon = next((item for item in report.results if item.name == "reconnaissance"), None)
    if (
        recon is None
        or recon.status is not AttackStatus.OBSERVATION
        or recon.scope is not SearchScope.BOUNDED
    ):
        failures.append("balanced_ternary: reconnaissance is not a bounded observation")
    skipped = {item.attack for item in report.skipped}
    if "modular" not in skipped or "spectral" not in skipped:
        failures.append("balanced_ternary: modular/spectral should stay inapplicable")
    hyp = next(
        (item for item in report.hypotheses if item.id == CLOSURE_HYPOTHESIS.id),
        None,
    )
    if hyp is None or hyp.status is not HypothesisStatus.SUPPORTED:
        failures.append("balanced_ternary: finite-closure hypothesis is not SUPPORTED")
    closure = next((item for item in targets if item.attack == "closure"), None)
    if closure is None or not closure.exportable or closure.lean_theorem != CLOSURE_THEOREM:
        failures.append("balanced_ternary: closure is not linked to doubledTrit_closure")
    if any(item.kind is ClaimKind.LIVE and item.exportable for item in targets):
        failures.append("balanced_ternary: exported a LIVE target")
    return tuple(failures)


def _expanding_d_reproduce_failures(report, targets) -> tuple[str, ...]:
    from research.balanced_ternary.lean_export import (
        EXPANDING_CLOSURE_THEOREM,
        closure_is_exact_three,
    )
    from research.balanced_ternary.planner import EXPANDING_CLOSURE_HYPOTHESIS

    failures: list[str] = []
    if not closure_is_exact_three(report):
        failures.append("expanding_d: closure is not EXACT size 3")
    recon = next((item for item in report.results if item.name == "reconnaissance"), None)
    if (
        recon is None
        or recon.status is not AttackStatus.OBSERVATION
        or recon.scope is not SearchScope.BOUNDED
    ):
        failures.append("expanding_d: reconnaissance is not a bounded observation")
    skipped = {item.attack for item in report.skipped}
    if "modular" not in skipped or "spectral" not in skipped:
        failures.append("expanding_d: modular/spectral should stay inapplicable")
    hyp = next(
        (item for item in report.hypotheses if item.id == EXPANDING_CLOSURE_HYPOTHESIS.id),
        None,
    )
    if hyp is None or hyp.status is not HypothesisStatus.SUPPORTED:
        failures.append("expanding_d: LSD-closure hypothesis is not SUPPORTED")
    closure = next((item for item in targets if item.attack == "closure"), None)
    if (
        closure is None
        or not closure.exportable
        or closure.lean_theorem != EXPANDING_CLOSURE_THEOREM
    ):
        failures.append("expanding_d: closure is not linked to expandingD_residue_closure")
    if any(item.kind is ClaimKind.LIVE and item.exportable for item in targets):
        failures.append("expanding_d: exported a LIVE target")
    return tuple(failures)


def _expanding_j2_reproduce_failures(report, targets) -> tuple[str, ...]:
    from research.balanced_ternary.lean_export import (
        J2_CLOSURE_THEOREM,
        closure_is_exact_size,
    )
    from research.balanced_ternary.planner import J2_CLOSURE_HYPOTHESIS

    failures: list[str] = []
    if not closure_is_exact_size(report, 9):
        failures.append("expanding_j2: closure is not EXACT size 9")
    recon = next((item for item in report.results if item.name == "reconnaissance"), None)
    if (
        recon is None
        or recon.status is not AttackStatus.OBSERVATION
        or recon.scope is not SearchScope.BOUNDED
    ):
        failures.append("expanding_j2: reconnaissance is not a bounded observation")
    skipped = {item.attack for item in report.skipped}
    if "modular" not in skipped or "spectral" not in skipped:
        failures.append("expanding_j2: modular/spectral should stay inapplicable")
    hyp = next(
        (item for item in report.hypotheses if item.id == J2_CLOSURE_HYPOTHESIS.id),
        None,
    )
    if hyp is None or hyp.status is not HypothesisStatus.SUPPORTED:
        failures.append("expanding_j2: J2-closure hypothesis is not SUPPORTED")
    closure = next((item for item in targets if item.attack == "closure"), None)
    if (
        closure is None
        or not closure.exportable
        or closure.lean_theorem != J2_CLOSURE_THEOREM
    ):
        failures.append("expanding_j2: closure is not linked to jet2_residue_closure")
    if any(item.kind is ClaimKind.LIVE and item.exportable for item in targets):
        failures.append("expanding_j2: exported a LIVE target")
    return tuple(failures)


def _expanding_j3_reproduce_failures(report, targets) -> tuple[str, ...]:
    from research.balanced_ternary.lean_export import (
        J3_CLOSURE_THEOREM,
        closure_is_exact_size,
    )
    from research.balanced_ternary.planner import J3_CLOSURE_HYPOTHESIS

    failures: list[str] = []
    if not closure_is_exact_size(report, 27):
        failures.append("expanding_j3: closure is not EXACT size 27")
    recon = next((item for item in report.results if item.name == "reconnaissance"), None)
    if (
        recon is None
        or recon.status is not AttackStatus.OBSERVATION
        or recon.scope is not SearchScope.BOUNDED
    ):
        failures.append("expanding_j3: reconnaissance is not a bounded observation")
    skipped = {item.attack for item in report.skipped}
    if "modular" not in skipped or "spectral" not in skipped:
        failures.append("expanding_j3: modular/spectral should stay inapplicable")
    hyp = next(
        (item for item in report.hypotheses if item.id == J3_CLOSURE_HYPOTHESIS.id),
        None,
    )
    if hyp is None or hyp.status is not HypothesisStatus.SUPPORTED:
        failures.append("expanding_j3: J3-closure hypothesis is not SUPPORTED")
    closure = next((item for item in targets if item.attack == "closure"), None)
    if (
        closure is None
        or not closure.exportable
        or closure.lean_theorem != J3_CLOSURE_THEOREM
    ):
        failures.append("expanding_j3: closure is not linked to jet3_residue_closure")
    if any(item.kind is ClaimKind.LIVE and item.exportable for item in targets):
        failures.append("expanding_j3: exported a LIVE target")
    return tuple(failures)


def _d_add_reproduce_failures(report, targets) -> tuple[str, ...]:
    from research.balanced_ternary.lean_export import (
        DADD_CLOSURE_THEOREM,
        closure_is_exact_size,
    )
    from research.balanced_ternary.planner import DADD_CLOSURE_HYPOTHESIS

    failures: list[str] = []
    if not closure_is_exact_size(report, 3):
        failures.append("d_add: closure is not EXACT size 3")
    recon = next((item for item in report.results if item.name == "reconnaissance"), None)
    if (
        recon is None
        or recon.status is not AttackStatus.OBSERVATION
        or recon.scope is not SearchScope.BOUNDED
    ):
        failures.append("d_add: reconnaissance is not a bounded observation")
    skipped = {item.attack for item in report.skipped}
    if "modular" not in skipped or "spectral" not in skipped:
        failures.append("d_add: modular/spectral should stay inapplicable")
    hyp = next(
        (item for item in report.hypotheses if item.id == DADD_CLOSURE_HYPOTHESIS.id),
        None,
    )
    if hyp is None or hyp.status is not HypothesisStatus.SUPPORTED:
        failures.append("d_add: residual-closure hypothesis is not SUPPORTED")
    closure = next((item for item in targets if item.attack == "closure"), None)
    if (
        closure is None
        or not closure.exportable
        or closure.lean_theorem != DADD_CLOSURE_THEOREM
    ):
        failures.append("d_add: closure is not linked to dAdd_residual_closure")
    if any(item.kind is ClaimKind.LIVE and item.exportable for item in targets):
        failures.append("d_add: exported a LIVE target")
    return tuple(failures)


def _signed_digit_residual_reproduce_failures(report, targets) -> tuple[str, ...]:
    from research.signed_digit_residual.lean_export import (
        CLOSURE_THEOREM,
        closure_is_exact_size,
    )
    from research.signed_digit_residual.planner import (
        CLOSURE_HYPOTHESIS,
        GEOMETRY_PHASE_HYPOTHESIS,
        MAXABS_MEALY_HYPOTHESIS,
        SCALAR_THRESHOLD_HYPOTHESIS,
    )

    failures: list[str] = []
    if not closure_is_exact_size(report, 3):
        failures.append("signed_digit_residual: closure is not EXACT size 3")
    recon = next((item for item in report.results if item.name == "reconnaissance"), None)
    if (
        recon is None
        or recon.status is not AttackStatus.OBSERVATION
        or recon.scope is not SearchScope.BOUNDED
    ):
        failures.append("signed_digit_residual: reconnaissance is not a bounded observation")
    skipped = {item.attack for item in report.skipped}
    if "modular" not in skipped or "spectral" not in skipped:
        failures.append("signed_digit_residual: modular/spectral should stay inapplicable")
    hyp = next(
        (item for item in report.hypotheses if item.id == CLOSURE_HYPOTHESIS.id),
        None,
    )
    if hyp is None or hyp.status is not HypothesisStatus.SUPPORTED:
        failures.append("signed_digit_residual: U_2-closure hypothesis is not SUPPORTED")
    scalar = next(
        (item for item in report.hypotheses if item.id == SCALAR_THRESHOLD_HYPOTHESIS.id),
        None,
    )
    if scalar is None or scalar.status is not HypothesisStatus.REFUTED:
        failures.append("signed_digit_residual: scalar λ=3 threshold is not REFUTED")
    geometry = next(
        (item for item in report.hypotheses if item.id == GEOMETRY_PHASE_HYPOTHESIS.id),
        None,
    )
    if geometry is None or geometry.status is not HypothesisStatus.REFUTED:
        failures.append("signed_digit_residual: geometry-controls-phase is not REFUTED")
    mealy = next(
        (item for item in report.hypotheses if item.id == MAXABS_MEALY_HYPOTHESIS.id),
        None,
    )
    if mealy is None or mealy.status is not HypothesisStatus.REFUTED:
        failures.append("signed_digit_residual: max-abs Mealy hypothesis is not REFUTED")
    closure = next((item for item in targets if item.attack == "closure"), None)
    if (
        closure is None
        or not closure.exportable
        or closure.lean_theorem != CLOSURE_THEOREM
    ):
        failures.append("signed_digit_residual: closure is not linked to lambda1_u2_residual_closure")
    if any(item.kind is ClaimKind.LIVE and item.exportable for item in targets):
        failures.append("signed_digit_residual: exported a LIVE target")
    return tuple(failures)


def _signed_digit_residual_geometry_reproduce_failures(report, targets) -> tuple[str, ...]:
    from research.signed_digit_residual_geometry.lean_export import (
        CLOSURE_THEOREM,
        closure_is_exact_size,
    )
    from research.signed_digit_residual_geometry.planner import (
        CLOSURE_HYPOTHESIS,
        LATTICE_ALL_U_HYPOTHESIS,
        SIGN_MEALY_HYPOTHESIS,
    )

    failures: list[str] = []
    if not closure_is_exact_size(report, 3):
        failures.append("signed_digit_residual_geometry: closure is not EXACT size 3")
    recon = next((item for item in report.results if item.name == "reconnaissance"), None)
    if (
        recon is None
        or recon.status is not AttackStatus.OBSERVATION
        or recon.scope is not SearchScope.BOUNDED
    ):
        failures.append("signed_digit_residual_geometry: reconnaissance is not a bounded observation")
    skipped = {item.attack for item in report.skipped}
    if "modular" not in skipped or "spectral" not in skipped:
        failures.append("signed_digit_residual_geometry: modular/spectral should stay inapplicable")
    hyp = next(
        (item for item in report.hypotheses if item.id == CLOSURE_HYPOTHESIS.id),
        None,
    )
    if hyp is None or hyp.status is not HypothesisStatus.SUPPORTED:
        failures.append("signed_digit_residual_geometry: U_2 interval hypothesis is not SUPPORTED")
    lattice = next(
        (item for item in report.hypotheses if item.id == LATTICE_ALL_U_HYPOTHESIS.id),
        None,
    )
    if lattice is None or lattice.status is not HypothesisStatus.REFUTED:
        failures.append("signed_digit_residual_geometry: lattice-all-U is not REFUTED")
    sign = next(
        (item for item in report.hypotheses if item.id == SIGN_MEALY_HYPOTHESIS.id),
        None,
    )
    if sign is None or sign.status is not HypothesisStatus.REFUTED:
        failures.append("signed_digit_residual_geometry: sign-Mealy hypothesis is not REFUTED")
    closure = next((item for item in targets if item.attack == "closure"), None)
    if (
        closure is None
        or not closure.exportable
        or closure.lean_theorem != CLOSURE_THEOREM
    ):
        failures.append(
            "signed_digit_residual_geometry: closure is not linked to lambda1_interval_reachable"
        )
    if any(item.kind is ClaimKind.LIVE and item.exportable for item in targets):
        failures.append("signed_digit_residual_geometry: exported a LIVE target")
    return tuple(failures)


def _signed_digit_residual_minimality_reproduce_failures(report, targets) -> tuple[str, ...]:
    from research.signed_digit_residual_minimality.lean_export import (
        CLOSURE_THEOREM,
        closure_is_exact_size,
    )
    from research.signed_digit_residual_minimality.planner import (
        CLOSURE_HYPOTHESIS,
        MERGE_HYPOTHESIS,
        MOD3_HYPOTHESIS,
    )

    failures: list[str] = []
    if not closure_is_exact_size(report, 3):
        failures.append("signed_digit_residual_minimality: closure is not EXACT size 3")
    recon = next((item for item in report.results if item.name == "reconnaissance"), None)
    if (
        recon is None
        or recon.status is not AttackStatus.OBSERVATION
        or recon.scope is not SearchScope.BOUNDED
    ):
        failures.append("signed_digit_residual_minimality: reconnaissance is not a bounded observation")
    skipped = {item.attack for item in report.skipped}
    if "modular" not in skipped or "spectral" not in skipped:
        failures.append("signed_digit_residual_minimality: modular/spectral should stay inapplicable")
    hyp = next(
        (item for item in report.hypotheses if item.id == CLOSURE_HYPOTHESIS.id),
        None,
    )
    if hyp is None or hyp.status is not HypothesisStatus.SUPPORTED:
        failures.append("signed_digit_residual_minimality: U_2 minimal hypothesis is not SUPPORTED")
    merge = next(
        (item for item in report.hypotheses if item.id == MERGE_HYPOTHESIS.id),
        None,
    )
    if merge is None or merge.status is not HypothesisStatus.REFUTED:
        failures.append("signed_digit_residual_minimality: merge-exists is not REFUTED")
    mod3 = next(
        (item for item in report.hypotheses if item.id == MOD3_HYPOTHESIS.id),
        None,
    )
    if mod3 is None or mod3.status is not HypothesisStatus.REFUTED:
        failures.append("signed_digit_residual_minimality: mod3-merge hypothesis is not REFUTED")
    closure = next((item for item in targets if item.attack == "closure"), None)
    if (
        closure is None
        or not closure.exportable
        or closure.lean_theorem != CLOSURE_THEOREM
    ):
        failures.append(
            "signed_digit_residual_minimality: closure is not linked to residual_separation"
        )
    if any(item.kind is ClaimKind.LIVE and item.exportable for item in targets):
        failures.append("signed_digit_residual_minimality: exported a LIVE target")
    return tuple(failures)


def _signed_digit_constrained_controls_reproduce_failures(report, targets) -> tuple[str, ...]:
    from research.signed_digit_constrained_controls.lean_export import (
        CLOSURE_THEOREM,
        closure_is_exact_size,
    )
    from research.signed_digit_constrained_controls.planner import (
        CLOSURE_HYPOTHESIS,
        CONSTANT_HYPOTHESIS,
        MERGE_HYPOTHESIS,
    )

    failures: list[str] = []
    if not closure_is_exact_size(report, 10):
        failures.append("signed_digit_constrained_controls: closure is not EXACT size 10")
    recon = next((item for item in report.results if item.name == "reconnaissance"), None)
    if (
        recon is None
        or recon.status is not AttackStatus.OBSERVATION
        or recon.scope is not SearchScope.BOUNDED
    ):
        failures.append("signed_digit_constrained_controls: reconnaissance is not a bounded observation")
    skipped = {item.attack for item in report.skipped}
    if "modular" not in skipped or "spectral" not in skipped:
        failures.append("signed_digit_constrained_controls: modular/spectral should stay inapplicable")
    hyp = next(
        (item for item in report.hypotheses if item.id == CLOSURE_HYPOTHESIS.id),
        None,
    )
    if hyp is None or hyp.status is not HypothesisStatus.SUPPORTED:
        failures.append("signed_digit_constrained_controls: no-repeat product hypothesis is not SUPPORTED")
    constant = next(
        (item for item in report.hypotheses if item.id == CONSTANT_HYPOTHESIS.id),
        None,
    )
    if constant is None or constant.status is not HypothesisStatus.REFUTED:
        failures.append("signed_digit_constrained_controls: constant-word hypothesis is not REFUTED")
    merge = next(
        (item for item in report.hypotheses if item.id == MERGE_HYPOTHESIS.id),
        None,
    )
    if merge is None or merge.status is not HypothesisStatus.REFUTED:
        failures.append("signed_digit_constrained_controls: residual-merge hypothesis is not REFUTED")
    closure = next((item for item in targets if item.attack == "closure"), None)
    if (
        closure is None
        or not closure.exportable
        or closure.lean_theorem != CLOSURE_THEOREM
    ):
        failures.append(
            "signed_digit_constrained_controls: closure is not linked to any_word_separation"
        )
    if any(item.kind is ClaimKind.LIVE and item.exportable for item in targets):
        failures.append("signed_digit_constrained_controls: exported a LIVE target")
    return tuple(failures)


def _signed_digit_short_horizon_reproduce_failures(report, targets) -> tuple[str, ...]:
    from research.signed_digit_short_horizon.lean_export import (
        CLOSURE_THEOREM,
        closure_is_exact_size,
    )
    from research.signed_digit_short_horizon.planner import (
        CLOSURE_HYPOTHESIS,
        DEADLOCK_HYPOTHESIS,
        MAXLEN_HYPOTHESIS,
        MERGE_HYPOTHESIS,
        SHORT_SEP_HYPOTHESIS,
        SUBSET_HYPOTHESIS,
    )

    failures: list[str] = []
    if not closure_is_exact_size(report, 7):
        failures.append("signed_digit_short_horizon: closure is not EXACT size 7")
    recon = next((item for item in report.results if item.name == "reconnaissance"), None)
    if (
        recon is None
        or recon.status is not AttackStatus.OBSERVATION
        or recon.scope is not SearchScope.BOUNDED
    ):
        failures.append("signed_digit_short_horizon: reconnaissance is not a bounded observation")
    skipped = {item.attack for item in report.skipped}
    if "modular" not in skipped or "spectral" not in skipped:
        failures.append("signed_digit_short_horizon: modular/spectral should stay inapplicable")
    hyp = next(
        (item for item in report.hypotheses if item.id == CLOSURE_HYPOTHESIS.id),
        None,
    )
    if hyp is None or hyp.status is not HypothesisStatus.SUPPORTED:
        failures.append("signed_digit_short_horizon: horizon product hypothesis is not SUPPORTED")
    merge = next(
        (item for item in report.hypotheses if item.id == MERGE_HYPOTHESIS.id),
        None,
    )
    if merge is None or merge.status is not HypothesisStatus.SUPPORTED:
        failures.append("signed_digit_short_horizon: genuine-merge hypothesis is not SUPPORTED")
    short_sep = next(
        (item for item in report.hypotheses if item.id == SHORT_SEP_HYPOTHESIS.id),
        None,
    )
    if short_sep is None or short_sep.status is not HypothesisStatus.REFUTED:
        failures.append("signed_digit_short_horizon: short-separator hypothesis is not REFUTED")
    deadlock = next(
        (item for item in report.hypotheses if item.id == DEADLOCK_HYPOTHESIS.id),
        None,
    )
    if deadlock is None or deadlock.status is not HypothesisStatus.REFUTED:
        failures.append("signed_digit_short_horizon: deadlock-only hypothesis is not REFUTED")
    subset = next(
        (item for item in report.hypotheses if item.id == SUBSET_HYPOTHESIS.id),
        None,
    )
    if subset is None or subset.status is not HypothesisStatus.REFUTED:
        failures.append("signed_digit_short_horizon: subset-merge hypothesis is not REFUTED")
    maxlen = next(
        (item for item in report.hypotheses if item.id == MAXLEN_HYPOTHESIS.id),
        None,
    )
    if maxlen is None or maxlen.status is not HypothesisStatus.SUPPORTED:
        failures.append("signed_digit_short_horizon: max-len criterion is not SUPPORTED")
    closure = next((item for item in targets if item.attack == "closure"), None)
    if (
        closure is None
        or not closure.exportable
        or closure.lean_theorem != CLOSURE_THEOREM
    ):
        failures.append(
            "signed_digit_short_horizon: closure is not linked to truncated_3adic_equiv"
        )
    if any(item.kind is ClaimKind.LIVE and item.exportable for item in targets):
        failures.append("signed_digit_short_horizon: exported a LIVE target")
    return tuple(failures)


def _multiplicative_residual_reproduce_failures(report, targets) -> tuple[str, ...]:
    from research.multiplicative_residual.lean_export import (
        CLOSURE_THEOREM,
        closure_is_exact_size,
    )
    from research.multiplicative_residual.planner import (
        CLOSURE_HYPOTHESIS,
        FACTOR_COUNT_HYPOTHESIS,
        THREE_STATE_HYPOTHESIS,
    )

    failures: list[str] = []
    if not closure_is_exact_size(report, 1):
        failures.append("multiplicative_residual: closure is not EXACT size 1")
    recon = next((item for item in report.results if item.name == "reconnaissance"), None)
    if (
        recon is None
        or recon.status is not AttackStatus.OBSERVATION
        or recon.scope is not SearchScope.BOUNDED
    ):
        failures.append("multiplicative_residual: reconnaissance is not a bounded observation")
    skipped = {item.attack for item in report.skipped}
    if "modular" not in skipped or "spectral" not in skipped:
        failures.append("multiplicative_residual: modular/spectral should stay inapplicable")
    hyp = next(
        (item for item in report.hypotheses if item.id == CLOSURE_HYPOTHESIS.id),
        None,
    )
    if hyp is None or hyp.status is not HypothesisStatus.SUPPORTED:
        failures.append("multiplicative_residual: U_1-closure hypothesis is not SUPPORTED")
    factor = next(
        (item for item in report.hypotheses if item.id == FACTOR_COUNT_HYPOTHESIS.id),
        None,
    )
    if factor is None or factor.status is not HypothesisStatus.REFUTED:
        failures.append("multiplicative_residual: factor-count hypothesis is not REFUTED")
    three = next(
        (item for item in report.hypotheses if item.id == THREE_STATE_HYPOTHESIS.id),
        None,
    )
    if three is None or three.status is not HypothesisStatus.REFUTED:
        failures.append("multiplicative_residual: 3-state residual hypothesis is not REFUTED")
    closure = next((item for item in targets if item.attack == "closure"), None)
    if (
        closure is None
        or not closure.exportable
        or closure.lean_theorem != CLOSURE_THEOREM
    ):
        failures.append("multiplicative_residual: closure is not linked to product_residual_closure")
    if any(item.kind is ClaimKind.LIVE and item.exportable for item in targets):
        failures.append("multiplicative_residual: exported a LIVE target")
    return tuple(failures)


def _collatz_finite_descent_reproduce_failures(report, targets) -> tuple[str, ...]:
    from research.collatz_finite_descent.lean_export import (
        DESCENT_THEOREM,
        closure_is_inconclusive,
    )
    from research.collatz_finite_descent.planner import (
        INTEGER_RESIDUAL_HYPOTHESIS,
        ONE_STEP_LYAPUNOV_HYPOTHESIS,
        UNIFORM_DESCENT_HYPOTHESIS,
    )

    failures: list[str] = []
    if not closure_is_inconclusive(report):
        failures.append("collatz: integer-state closure is not INCONCLUSIVE")
    recon = next((item for item in report.results if item.name == "reconnaissance"), None)
    if (
        recon is None
        or recon.status is not AttackStatus.OBSERVATION
        or recon.scope is not SearchScope.BOUNDED
    ):
        failures.append("collatz: reconnaissance is not a bounded observation")
    skipped = {item.attack for item in report.skipped}
    if "modular" not in skipped or "spectral" not in skipped:
        failures.append("collatz: modular/spectral should stay inapplicable")
    uniform = next(
        (item for item in report.hypotheses if item.id == UNIFORM_DESCENT_HYPOTHESIS.id),
        None,
    )
    if uniform is None or uniform.status is not HypothesisStatus.REFUTED:
        failures.append("collatz: uniform L-descent is not REFUTED")
    lyapunov = next(
        (item for item in report.hypotheses if item.id == ONE_STEP_LYAPUNOV_HYPOTHESIS.id),
        None,
    )
    if lyapunov is None or lyapunov.status is not HypothesisStatus.REFUTED:
        failures.append("collatz: one-step Lyapunov is not REFUTED")
    residual = next(
        (item for item in report.hypotheses if item.id == INTEGER_RESIDUAL_HYPOTHESIS.id),
        None,
    )
    if residual is None or residual.status is not HypothesisStatus.PARKED:
        failures.append("collatz: integer residual is not PARKED")
    obstruction = next(
        (item for item in targets if item.lean_theorem == DESCENT_THEOREM),
        None,
    )
    if obstruction is None or not obstruction.exportable:
        failures.append("collatz: obstruction is not linked to shortcutC_no_uniform_L_descent")
    if any(item.kind is ClaimKind.LIVE and item.exportable for item in targets):
        failures.append("collatz: exported a LIVE target")
    return tuple(failures)


def _prime_residual_reproduce_failures(report, targets) -> tuple[str, ...]:
    from research.prime_residual_complexity.lean_export import (
        SEPARATOR_THEOREM,
        sieve_closure_is_exact,
    )
    from research.prime_residual_complexity.planner import (
        INTEGER_PRIME_HYPOTHESIS,
        JET_EQUALS_PRIME_HYPOTHESIS,
        SIEVE_EQUALS_PRIME_HYPOTHESIS,
        SIEVE_RESIDUAL_HYPOTHESIS,
    )
    from research.prime_residual_complexity.spec import prime_spec
    from research_engine.core.problem_spec import ProblemSpec
    from research_engine.planner.orchestrator import run_named_attack

    failures: list[str] = []
    if not sieve_closure_is_exact(report):
        failures.append("primes: sieve closure is not EXACT")
    recon = next((item for item in report.results if item.name == "reconnaissance"), None)
    if (
        recon is None
        or recon.status is not AttackStatus.OBSERVATION
        or recon.scope is not SearchScope.BOUNDED
    ):
        failures.append("primes: reconnaissance is not a bounded observation")
    sieve_hyp = next(
        (item for item in report.hypotheses if item.id == SIEVE_RESIDUAL_HYPOTHESIS.id),
        None,
    )
    if sieve_hyp is None or sieve_hyp.status is not HypothesisStatus.SUPPORTED:
        failures.append("primes: sieve residual is not SUPPORTED")
    jet_hyp = next(
        (item for item in report.hypotheses if item.id == JET_EQUALS_PRIME_HYPOTHESIS.id),
        None,
    )
    if jet_hyp is None or jet_hyp.status is not HypothesisStatus.REFUTED:
        failures.append("primes: jet=prime is not REFUTED")
    sieve_eq = next(
        (item for item in report.hypotheses if item.id == SIEVE_EQUALS_PRIME_HYPOTHESIS.id),
        None,
    )
    if sieve_eq is None or sieve_eq.status is not HypothesisStatus.REFUTED:
        failures.append("primes: sieve=prime is not REFUTED")
    integer_hyp = next(
        (item for item in report.hypotheses if item.id == INTEGER_PRIME_HYPOTHESIS.id),
        None,
    )
    if integer_hyp is None or integer_hyp.status is not HypothesisStatus.PARKED:
        failures.append("primes: integer prime residual is not PARKED")
    spec = prime_spec(4)
    integer_closure = run_named_attack(
        "closure",
        cast(ProblemSpec, spec),
        spec.attack_context(),
    )
    if (
        integer_closure.status is not AttackStatus.INCONCLUSIVE
        or integer_closure.scope is not SearchScope.BOUNDED
    ):
        failures.append("primes: integer-state closure is not INCONCLUSIVE")
    separator = next(
        (item for item in targets if item.lean_theorem == SEPARATOR_THEOREM),
        None,
    )
    if separator is None or not separator.exportable:
        failures.append("primes: separator is not linked to sievePrime_I0_separator")
    if any(item.kind is ClaimKind.LIVE and item.exportable for item in targets):
        failures.append("primes: exported a LIVE target")
    return tuple(failures)


def _operator_dynamics_reproduce_failures(report, targets) -> tuple[str, ...]:
    from research.operator_dynamics.signed_p0.lean_export import (
        CLOSURE_THEOREM,
        closure_is_exact_size,
    )
    from research.operator_dynamics.signed_p0.planner import (
        CLOSURE_HYPOTHESIS,
        F2_HYPOTHESIS,
        GLOBAL_RESIDUAL_HYPOTHESIS,
        INTERVAL_HYPOTHESIS,
        LYAPUNOV_HYPOTHESIS,
        SIGN_MERGE_HYPOTHESIS,
    )

    failures: list[str] = []
    if not closure_is_exact_size(report, 3):
        failures.append("operator_dynamics: closure is not EXACT size 3")
    recon = next((item for item in report.results if item.name == "reconnaissance"), None)
    if (
        recon is None
        or recon.status is not AttackStatus.OBSERVATION
        or recon.scope is not SearchScope.BOUNDED
    ):
        failures.append("operator_dynamics: reconnaissance is not a bounded observation")
    skipped = {item.attack for item in report.skipped}
    if "modular" not in skipped or "spectral" not in skipped:
        failures.append("operator_dynamics: modular/spectral should stay inapplicable")
    if "factorization" not in skipped:
        failures.append("operator_dynamics: factorization should stay inapplicable")
    hyp = next(
        (item for item in report.hypotheses if item.id == CLOSURE_HYPOTHESIS.id),
        None,
    )
    if hyp is None or hyp.status is not HypothesisStatus.SUPPORTED:
        failures.append("operator_dynamics: seed-orbit hypothesis is not SUPPORTED")
    interval = next(
        (item for item in report.hypotheses if item.id == INTERVAL_HYPOTHESIS.id),
        None,
    )
    if interval is None or interval.status is not HypothesisStatus.REFUTED:
        failures.append("operator_dynamics: interval invariant is not REFUTED")
    lyap = next(
        (item for item in report.hypotheses if item.id == LYAPUNOV_HYPOTHESIS.id),
        None,
    )
    if lyap is None or lyap.status is not HypothesisStatus.REFUTED:
        failures.append("operator_dynamics: Lyapunov hypothesis is not REFUTED")
    global_res = next(
        (item for item in report.hypotheses if item.id == GLOBAL_RESIDUAL_HYPOTHESIS.id),
        None,
    )
    if global_res is None or global_res.status is not HypothesisStatus.REFUTED:
        failures.append("operator_dynamics: global finite residual is not REFUTED")
    f2 = next(
        (item for item in report.hypotheses if item.id == F2_HYPOTHESIS.id),
        None,
    )
    if f2 is None or f2.status is not HypothesisStatus.SUPPORTED:
        failures.append("operator_dynamics: F²=P_0 hypothesis is not SUPPORTED")
    merge = next(
        (item for item in report.hypotheses if item.id == SIGN_MERGE_HYPOTHESIS.id),
        None,
    )
    if merge is None or merge.status is not HypothesisStatus.SUPPORTED:
        failures.append("operator_dynamics: sign-merge hypothesis is not SUPPORTED")
    closure = next((item for item in targets if item.attack == "closure"), None)
    if (
        closure is None
        or not closure.exportable
        or closure.lean_theorem != CLOSURE_THEOREM
    ):
        failures.append("operator_dynamics: closure is not linked to signedP0_sq_eq_P0")
    if any(item.kind is ClaimKind.LIVE and item.exportable for item in targets):
        failures.append("operator_dynamics: exported a LIVE target")
    return tuple(failures)


def _digit_sum_dynamics_reproduce_failures(report, targets) -> tuple[str, ...]:
    from research.balanced_ternary_digit_sum_dynamics.lean_export import (
        CLOSURE_THEOREM,
        closure_is_exact_size,
    )
    from research.balanced_ternary_digit_sum_dynamics.planner import (
        CLOSURE_HYPOTHESIS,
        CONTRACTION_HYPOTHESIS,
        GLOBAL_RESIDUAL_HYPOTHESIS,
        IDENTITY_MERGE_HYPOTHESIS,
        IDEMPOTENT_HYPOTHESIS,
        INTERVAL_HYPOTHESIS,
        LYAPUNOV_HYPOTHESIS,
    )

    failures: list[str] = []
    if not closure_is_exact_size(report, 3):
        failures.append("digit_sum: closure is not EXACT size 3")
    recon = next((item for item in report.results if item.name == "reconnaissance"), None)
    if (
        recon is None
        or recon.status is not AttackStatus.OBSERVATION
        or recon.scope is not SearchScope.BOUNDED
    ):
        failures.append("digit_sum: reconnaissance is not a bounded observation")
    skipped = {item.attack for item in report.skipped}
    if "modular" not in skipped or "spectral" not in skipped:
        failures.append("digit_sum: modular/spectral should stay inapplicable")
    if "factorization" not in skipped:
        failures.append("digit_sum: factorization should stay inapplicable")
    if "reverse" not in skipped:
        failures.append("digit_sum: reverse should stay inapplicable")
    if "block" not in skipped:
        failures.append("digit_sum: block should stay inapplicable")
    if "symmetry" not in skipped:
        failures.append("digit_sum: symmetry should stay inapplicable")
    if "symbolic" not in skipped:
        failures.append("digit_sum: symbolic should stay skipped")
    hyp = next(
        (item for item in report.hypotheses if item.id == CLOSURE_HYPOTHESIS.id),
        None,
    )
    if hyp is None or hyp.status is not HypothesisStatus.SUPPORTED:
        failures.append("digit_sum: seed-orbit hypothesis is not SUPPORTED")
    interval = next(
        (item for item in report.hypotheses if item.id == INTERVAL_HYPOTHESIS.id),
        None,
    )
    if interval is None or interval.status is not HypothesisStatus.SUPPORTED:
        failures.append("digit_sum: interval invariant is not SUPPORTED")
    lyap = next(
        (item for item in report.hypotheses if item.id == LYAPUNOV_HYPOTHESIS.id),
        None,
    )
    if lyap is None or lyap.status is not HypothesisStatus.REFUTED:
        failures.append("digit_sum: Lyapunov hypothesis is not REFUTED")
    global_res = next(
        (item for item in report.hypotheses if item.id == GLOBAL_RESIDUAL_HYPOTHESIS.id),
        None,
    )
    if global_res is None or global_res.status is not HypothesisStatus.REFUTED:
        failures.append("digit_sum: global finite residual is not REFUTED")
    merge = next(
        (item for item in report.hypotheses if item.id == IDENTITY_MERGE_HYPOTHESIS.id),
        None,
    )
    if merge is None or merge.status is not HypothesisStatus.REFUTED:
        failures.append("digit_sum: identity-merge hypothesis is not REFUTED")
    idem = next(
        (item for item in report.hypotheses if item.id == IDEMPOTENT_HYPOTHESIS.id),
        None,
    )
    if idem is None or idem.status is not HypothesisStatus.REFUTED:
        failures.append("digit_sum: idempotent hypothesis is not REFUTED")
    contraction = next(
        (item for item in report.hypotheses if item.id == CONTRACTION_HYPOTHESIS.id),
        None,
    )
    if contraction is None or contraction.status is not HypothesisStatus.SUPPORTED:
        failures.append("digit_sum: contraction hypothesis is not SUPPORTED")
    closure = next((item for item in targets if item.attack == "closure"), None)
    if (
        closure is None
        or not closure.exportable
        or closure.lean_theorem != CLOSURE_THEOREM
    ):
        failures.append("digit_sum: closure is not linked to digitSumZ_natAbs_lt")
    if any(item.kind is ClaimKind.LIVE and item.exportable for item in targets):
        failures.append("digit_sum: exported a LIVE target")
    return tuple(failures)


def _weight_dynamics_reproduce_failures(report, targets) -> tuple[str, ...]:
    from research.balanced_ternary_weight_dynamics.lean_export import (
        CLOSURE_THEOREM,
        closure_is_exact_size,
    )
    from research.balanced_ternary_weight_dynamics.planner import (
        CLOSURE_HYPOTHESIS,
        CONTRACTION_GE2_HYPOTHESIS,
        CONTRACTION_GE3_HYPOTHESIS,
        EVEN_HYPOTHESIS,
        GLOBAL_RESIDUAL_HYPOTHESIS,
        IDENTITY_MERGE_HYPOTHESIS,
        IDEMPOTENT_HYPOTHESIS,
        INTERVAL_HYPOTHESIS,
        LYAPUNOV_HYPOTHESIS,
    )

    failures: list[str] = []
    if not closure_is_exact_size(report, 2):
        failures.append("weight: closure is not EXACT size 2")
    recon = next((item for item in report.results if item.name == "reconnaissance"), None)
    if (
        recon is None
        or recon.status is not AttackStatus.OBSERVATION
        or recon.scope is not SearchScope.BOUNDED
    ):
        failures.append("weight: reconnaissance is not a bounded observation")
    skipped = {item.attack for item in report.skipped}
    if "modular" not in skipped or "spectral" not in skipped:
        failures.append("weight: modular/spectral should stay inapplicable")
    if "factorization" not in skipped:
        failures.append("weight: factorization should stay inapplicable")
    if "reverse" not in skipped:
        failures.append("weight: reverse should stay inapplicable")
    if "block" not in skipped:
        failures.append("weight: block should stay inapplicable")
    if "symmetry" not in skipped:
        failures.append("weight: symmetry should stay inapplicable")
    if "symbolic" not in skipped:
        failures.append("weight: symbolic should stay skipped")
    hyp = next(
        (item for item in report.hypotheses if item.id == CLOSURE_HYPOTHESIS.id),
        None,
    )
    if hyp is None or hyp.status is not HypothesisStatus.SUPPORTED:
        failures.append("weight: seed-orbit hypothesis is not SUPPORTED")
    interval = next(
        (item for item in report.hypotheses if item.id == INTERVAL_HYPOTHESIS.id),
        None,
    )
    if interval is None or interval.status is not HypothesisStatus.SUPPORTED:
        failures.append("weight: interval invariant is not SUPPORTED")
    lyap = next(
        (item for item in report.hypotheses if item.id == LYAPUNOV_HYPOTHESIS.id),
        None,
    )
    if lyap is None or lyap.status is not HypothesisStatus.REFUTED:
        failures.append("weight: Lyapunov hypothesis is not REFUTED")
    global_res = next(
        (item for item in report.hypotheses if item.id == GLOBAL_RESIDUAL_HYPOTHESIS.id),
        None,
    )
    if global_res is None or global_res.status is not HypothesisStatus.REFUTED:
        failures.append("weight: global finite residual is not REFUTED")
    merge = next(
        (item for item in report.hypotheses if item.id == IDENTITY_MERGE_HYPOTHESIS.id),
        None,
    )
    if merge is None or merge.status is not HypothesisStatus.REFUTED:
        failures.append("weight: identity-merge hypothesis is not REFUTED")
    idem = next(
        (item for item in report.hypotheses if item.id == IDEMPOTENT_HYPOTHESIS.id),
        None,
    )
    if idem is None or idem.status is not HypothesisStatus.REFUTED:
        failures.append("weight: idempotent hypothesis is not REFUTED")
    ge2 = next(
        (item for item in report.hypotheses if item.id == CONTRACTION_GE2_HYPOTHESIS.id),
        None,
    )
    if ge2 is None or ge2.status is not HypothesisStatus.REFUTED:
        failures.append("weight: |n|≥2 contraction is not REFUTED")
    ge3 = next(
        (item for item in report.hypotheses if item.id == CONTRACTION_GE3_HYPOTHESIS.id),
        None,
    )
    if ge3 is None or ge3.status is not HypothesisStatus.SUPPORTED:
        failures.append("weight: |n|≥3 contraction is not SUPPORTED")
    even = next(
        (item for item in report.hypotheses if item.id == EVEN_HYPOTHESIS.id),
        None,
    )
    if even is None or even.status is not HypothesisStatus.SUPPORTED:
        failures.append("weight: evenness hypothesis is not SUPPORTED")
    closure = next((item for item in targets if item.attack == "closure"), None)
    if (
        closure is None
        or not closure.exportable
        or closure.lean_theorem != CLOSURE_THEOREM
    ):
        failures.append("weight: closure is not linked to weightZ_natAbs_lt")
    if any(item.kind is ClaimKind.LIVE and item.exportable for item in targets):
        failures.append("weight: exported a LIVE target")
    return tuple(failures)


def _weight_drift_reproduce_failures(report, targets) -> tuple[str, ...]:
    from research.balanced_ternary_weight_drift.lean_export import (
        DRIFT_THEOREM,
        closure_is_inconclusive,
    )
    from research.balanced_ternary_weight_drift.planner import (
        CLOSURE_HYPOTHESIS,
        CONTRACTION_HYPOTHESIS,
        DISJOINT_HYPOTHESIS,
        EVEN_HYPOTHESIS,
        GLOBAL_RESIDUAL_HYPOTHESIS,
        IDENTITY_MERGE_HYPOTHESIS,
        IDEMPOTENT_HYPOTHESIS,
        INCREASE_HYPOTHESIS,
        INTERVAL_HYPOTHESIS,
        LYAPUNOV_HYPOTHESIS,
        NONPOS_HYPOTHESIS,
    )

    failures: list[str] = []
    if not closure_is_inconclusive(report):
        failures.append("weight_drift: closure is not INCONCLUSIVE")
    recon = next((item for item in report.results if item.name == "reconnaissance"), None)
    if (
        recon is None
        or recon.status is not AttackStatus.OBSERVATION
        or recon.scope is not SearchScope.BOUNDED
    ):
        failures.append("weight_drift: reconnaissance is not a bounded observation")
    functional = next((item for item in report.results if item.name == "functional"), None)
    if functional is None or functional.status is not AttackStatus.REFUTED:
        failures.append("weight_drift: functional is not REFUTED")
    affine = next((item for item in report.results if item.name == "affine"), None)
    if affine is None or affine.status is not AttackStatus.REFUTED:
        failures.append("weight_drift: affine is not REFUTED")
    quotient = next((item for item in report.results if item.name == "quotient"), None)
    if quotient is None or quotient.status is not AttackStatus.INCONCLUSIVE:
        failures.append("weight_drift: quotient is not INCONCLUSIVE")
    skipped = {item.attack for item in report.skipped}
    if "modular" not in skipped or "spectral" not in skipped:
        failures.append("weight_drift: modular/spectral should stay inapplicable")
    if "factorization" not in skipped:
        failures.append("weight_drift: factorization should stay inapplicable")
    if "reverse" not in skipped:
        failures.append("weight_drift: reverse should stay inapplicable")
    if "block" not in skipped:
        failures.append("weight_drift: block should stay inapplicable")
    if "symmetry" not in skipped:
        failures.append("weight_drift: symmetry should stay inapplicable")
    if "symbolic" not in skipped:
        failures.append("weight_drift: symbolic should stay skipped")
    expected_refuted = (
        (CLOSURE_HYPOTHESIS.id, "seed-orbit finite"),
        (INTERVAL_HYPOTHESIS.id, "interval invariant"),
        (LYAPUNOV_HYPOTHESIS.id, "Lyapunov"),
        (GLOBAL_RESIDUAL_HYPOTHESIS.id, "global finite residual"),
        (IDENTITY_MERGE_HYPOTHESIS.id, "identity-merge"),
        (IDEMPOTENT_HYPOTHESIS.id, "idempotent"),
        (CONTRACTION_HYPOTHESIS.id, "contraction"),
        (EVEN_HYPOTHESIS.id, "evenness"),
        (DISJOINT_HYPOTHESIS.id, "disjoint orbits"),
    )
    for hyp_id, label in expected_refuted:
        hyp = next((item for item in report.hypotheses if item.id == hyp_id), None)
        if hyp is None or hyp.status is not HypothesisStatus.REFUTED:
            failures.append(f"weight_drift: {label} is not REFUTED")
    increase = next(
        (item for item in report.hypotheses if item.id == INCREASE_HYPOTHESIS.id),
        None,
    )
    if increase is None or increase.status is not HypothesisStatus.SUPPORTED:
        failures.append("weight_drift: strict-increase hypothesis is not SUPPORTED")
    nonpos = next(
        (item for item in report.hypotheses if item.id == NONPOS_HYPOTHESIS.id),
        None,
    )
    if nonpos is None or nonpos.status is not HypothesisStatus.SUPPORTED:
        failures.append("weight_drift: nonpositive-ray hypothesis is not SUPPORTED")
    drift = next((item for item in targets if item.lean_theorem == DRIFT_THEOREM), None)
    if drift is None or not drift.exportable:
        failures.append("weight_drift: increase is not linked to weightDriftZ_gt")
    if any(item.kind is ClaimKind.LIVE and item.exportable for item in targets):
        failures.append("weight_drift: exported a LIVE target")
    return tuple(failures)


def _syracuse_reproduce_failures(report, targets) -> tuple[str, ...]:
    from research.syracuse.lean_export import ONE_THEOREM, closure_is_inconclusive
    from research.syracuse.planner import (
        CLOSURE_HYPOTHESIS,
        CONTRACTION_HYPOTHESIS,
        GLOBAL_RESIDUAL_HYPOTHESIS,
        IDEMPOTENT_HYPOTHESIS,
        INTERVAL_HYPOTHESIS,
        LYAPUNOV_HYPOTHESIS,
    )

    failures: list[str] = []
    if not closure_is_inconclusive(report):
        failures.append("syracuse: integer-state closure is not INCONCLUSIVE")
    recon = next((item for item in report.results if item.name == "reconnaissance"), None)
    if (
        recon is None
        or recon.status is not AttackStatus.OBSERVATION
        or recon.scope is not SearchScope.BOUNDED
    ):
        failures.append("syracuse: reconnaissance is not a bounded observation")
    skipped = {item.attack for item in report.skipped}
    if "modular" not in skipped or "spectral" not in skipped:
        failures.append("syracuse: modular/spectral should stay inapplicable")
    if "reverse" not in skipped:
        failures.append("syracuse: reverse should stay inapplicable")
    functional = next((item for item in report.results if item.name == "functional"), None)
    if functional is None or functional.status is not AttackStatus.REFUTED:
        failures.append("syracuse: functional |n| bound is not REFUTED")
    expected_refuted = (
        (LYAPUNOV_HYPOTHESIS.id, "Lyapunov"),
        (INTERVAL_HYPOTHESIS.id, "interval"),
        (CONTRACTION_HYPOTHESIS.id, "contraction"),
        (IDEMPOTENT_HYPOTHESIS.id, "idempotent"),
    )
    for hyp_id, label in expected_refuted:
        hyp = next((item for item in report.hypotheses if item.id == hyp_id), None)
        if hyp is None or hyp.status is not HypothesisStatus.REFUTED:
            failures.append(f"syracuse: {label} is not REFUTED")
    residual = next(
        (item for item in report.hypotheses if item.id == GLOBAL_RESIDUAL_HYPOTHESIS.id),
        None,
    )
    if residual is None or residual.status is not HypothesisStatus.PARKED:
        failures.append("syracuse: integer residual is not PARKED")
    closure_hyp = next(
        (item for item in report.hypotheses if item.id == CLOSURE_HYPOTHESIS.id),
        None,
    )
    if closure_hyp is None or closure_hyp.status is not HypothesisStatus.PARKED:
        failures.append("syracuse: seed-orbit hypothesis is not PARKED")
    one = next((item for item in targets if item.lean_theorem == ONE_THEOREM), None)
    if one is None or not one.exportable:
        failures.append("syracuse: S(1)=1 is not linked to syracuseS_one")
    if any(item.kind is ClaimKind.LIVE and item.exportable for item in targets):
        failures.append("syracuse: exported a LIVE target")
    return tuple(failures)
