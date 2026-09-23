"""Itinerary, lift, and dual-code Collatz commands."""

from __future__ import annotations

from research.experiments.paths import collatz_data_dir


def _itinerary(ks: str) -> int:
    from research.collatz.itinerary import ValuationItinerary

    it = ValuationItinerary.from_ks(ks)
    print(it.format(), end="")
    return 0


def _realizer(ks: str) -> int:
    from research.collatz.compatibility import nested_cylinder_report
    from research.collatz.min_realizer import count_cylinder_up_to, itinerary_signature

    sig = itinerary_signature(ks)
    print(sig.format(), end="")
    print(nested_cylinder_report(ks).format(), end="")
    print(f"count in [1, 1000]: {count_cylinder_up_to(ks, 1000)}  [EXACT]")
    return 0


def _enumerate_itineraries(length: int, max_k: int, write: bool) -> int:
    from research.collatz.experiments.itinerary_enumeration import run_itinerary_enumeration

    out = collatz_data_dir() if write else None
    result = run_itinerary_enumeration(length, max_k, output_dir=out)
    print(result.format(), end="")
    if result.rows:
        sample = result.rows[0]
        print(
            f"sample ks={sample['ks']} C={sample['C']} R={sample['R']}  [EXACT]"
        )
    return 0


def _fixed_budget(length: int, sum_k: int, write: bool) -> int:
    from research.collatz.experiments.fixed_budget import run_fixed_budget

    out = collatz_data_dir() if write else None
    result = run_fixed_budget(length, sum_k, output_dir=out)
    print(result.format(), end="")
    return 0


def _permutations(ks: str, write: bool) -> int:
    from research.collatz.experiments.permutation_analysis import run_permutation_analysis

    out = collatz_data_dir() if write else None
    payload = run_permutation_analysis(ks, output_dir=out)
    summary = payload["summary"]
    print("Permutation analysis  [EXACT C; R compared computationally on this multiset]")
    print(f"C_min ks={summary['C_min']['ks']} C={summary['C_min']['C']}")
    print(f"C_max ks={summary['C_max']['ks']} C={summary['C_max']['C']}")
    print(f"R_min ks={summary['R_min']['ks']} R={summary['R_min']['R']}")
    print(f"R_max ks={summary['R_max']['ks']} R={summary['R_max']['R']}")
    print(f"C extremal are sorted: {summary['C_extremal_are_sorted']}")
    print(f"R extremal are sorted: {summary['R_extremal_are_sorted']}")
    print(f"status: {summary['status']}")
    if payload["paths"]:
        print(f"outputs: {payload['paths']}")
    return 0


def _exceptional_search(length: int, max_k: int, epsilon: float) -> int:
    from research.collatz.experiments.exceptional_paths import run_exceptional_search

    payload = run_exceptional_search(length, k_max=max_k, epsilon=epsilon)
    print("Exceptional / expansionary census  [COMPUTATIONAL]")
    print(
        f"length={payload['length']} k_max={payload['k_max']} "
        f"epsilon={payload['epsilon']} K_cut={payload['K_cut']}"
    )
    print(f"count={payload['count']} R_min={payload['R_min']} R_max={payload['R_max']}")
    print(payload["status"])
    for row in payload["sample"][:12]:
        print(f"  ks={row['ks']} K={row['K']} R={row['R']} C={row['C']}")
    return 0


def _zero_lift(
    ks: str,
    steps: int,
    candidate_k: int | None,
    precision: int,
) -> int:
    from research.collatz.zero_lift import (
        dichotomy_report,
        finite_lift_certificate,
        zero_lift_trace,
    )

    print(dichotomy_report(ks).format(), end="")
    if candidate_k is not None:
        cert = finite_lift_certificate(ks, candidate_k, precision)
        valuation = (
            str(cert.valuation)
            if cert.valuation is not None
            else f">={cert.valuation_at_least}"
        )
        print(
            f"finite lift certificate: candidate_k={candidate_k} "
            f"precision={precision} x_residue={cert.state_residue} "
            f"next valuation={valuation} result={cert.result}  [EXACT — HUMAN PROOF]"
        )
    print("Deterministic zero-lift successor trace  [EXACT]")
    for state in zero_lift_trace(ks, steps):
        print(
            f"  m={state.m} K={state.K} R={state.R} x={state.x} "
            f"next_k={state.successor_k()} prefix={state.prefix}"
        )
    print("The successor trace is the accelerated Collatz orbit of R. [EXACT — HUMAN PROOF]")
    return 0


def _periodic_itinerary(ks: str) -> int:
    from research.collatz.periodic_itineraries import periodic_candidate

    print(periodic_candidate(ks).format(), end="")
    print(
        "Classification uses n(2^K-3^p)=C and an exact cylinder check. "
        "[EXACT — HUMAN PROOF]"
    )
    return 0


def _zero_lift_census(max_length: int, max_k: int, precision: int) -> int:
    from research.collatz.experiments.zero_lift_census import (
        expanding_positive_lift_census,
        next_k_by_R_mod,
        uniqueness_census,
    )

    unique = uniqueness_census(max_length, max_k)
    expanding = expanding_positive_lift_census(max_length, max_k)
    abstraction = next_k_by_R_mod(max_length, max_k, precision)
    print("Zero-lift census")
    print(
        f"unique-zero regression: checked={unique['checked_prefixes']} "
        f"mismatches={unique['mismatches']} "
        f"k beyond range={unique['true_k_exceeds_k_max']}"
    )
    print(f"  {unique['status']}")
    print(
        f"expanding words={expanding['expanding_words']} "
        f"failures={len(expanding['failures'])}"
    )
    print(f"  {expanding['status']}")
    print(
        f"R mod 2^{precision} next-k collisions="
        f"{abstraction['collision_count']}"
    )
    print(f"  {abstraction['status']}")
    return 0


def _dual_code(ks: str) -> int:
    from research.collatz.dual_code import CollatzDualCode

    dual = CollatzDualCode.from_valuations(ks)
    print("Collatz dual code  [EXACT]")
    print(f"valuations={dual.valuations}")
    print(f"cumulative_K={dual.cumulative_K}")
    print(f"lift_digits={dual.lift_digits}")
    print(f"R_prefixes={dual.realizers}")
    print(f"R={dual.R}  modulus={dual.modulus}  BT(R)={dual.balanced_ternary_R}")
    print(f"reconstruction={dual.reconstruct_R()}  valid={dual.validates()}")
    for step in dual.steps:
        print(
            f"  i={step.index} k={step.valuation} t={step.lift_digit} "
            f"R:{step.R_before}->{step.R_after} "
            f"x:{step.endpoint_before}->{step.endpoint_after} "
            f"{step.edge_class}"
        )
    return 0


def _lift_tree(max_depth: int, max_k: int, max_nodes: int) -> int:
    from research.collatz.lift_tree import build_lift_tree

    tree = build_lift_tree(max_depth, max_k, max_nodes)
    print("Cylinder lift tree  [EXACT bounded tree]")
    print(
        f"depth={max_depth} k_max={max_k} nodes={len(tree.nodes)} "
        f"edges={len(tree.edges)} truncated={str(tree.truncated).lower()}"
    )
    print(
        f"zero_lift_edges={len(tree.zero_lift_edges())} "
        f"positive_lift_edges={len(tree.positive_lift_edges())}"
    )
    for edge in tree.edges[:20]:
        print(
            f"  {edge.parent} --k={edge.next_k},t={edge.lift_digit}--> "
            f"{edge.child} R={edge.child_R} {edge.edge_class.value}"
        )
    print("POSITIVE_LIFT edges are valid finite extensions, never forbidden.")
    return 0


def _periodic_dual(ks: str, repeats: int) -> int:
    from research.collatz.cylinders import parse_ks
    from research.collatz.experiments.periodic_dual import periodic_dual_trace

    trace = periodic_dual_trace(parse_ks(ks), repeats)
    print("Periodic dual-code trace  [EXACT finite rows]")
    print(
        f"period={tuple(trace['period'])} primitive={tuple(trace['primitive_period'])} "
        f"repeats={repeats}"
    )
    for row in trace["rows"]:
        print(
            f"  m={row['m']} K={row['K']} t={row['lift_digit']} "
            f"R={row['R']} BT(R)={row['BT(R)']} "
            f"budget={row['budget_comparison']}"
        )
    candidate = trace["periodic_candidate"]
    print(
        f"infinite compatibility={candidate['compatible']} "
        f"candidate_n={candidate['n']} reason={candidate['reason']}"
    )
    return 0


def _suffix_test(max_length: int, max_k: int, suffix_max: int) -> int:
    from research.collatz.experiments.suffix_determination import (
        suffix_determination_census,
    )

    result = suffix_determination_census(max_length, max_k, suffix_max)
    print("BT(R) suffix determination  [COMPUTATIONAL]")
    print(f"prefixes={result['prefix_count']}")
    for row in result["rows"]:
        print(
            f"  L={row['suffix_length']} next_determined="
            f"{row['next_value_determined']} lift_determined="
            f"{row['lift_digit_determined_given_k']} "
            f"ambiguous_next={row['ambiguous_next_suffixes']} "
            f"ambiguous_lift={row['ambiguous_lift_states']}"
        )
    print(result["exact_full_R_counterexample"])
    return 0


def _dual_dataset(length: int, max_k: int, write: bool) -> int:
    from itertools import product

    from research.collatz.dual_code import CollatzDualCode
    from research.experiments.schema import ExperimentManifest, validate_dual_row
    from research.experiments.table_io import write_experiment

    if length < 0 or max_k < 1:
        raise ValueError("length must be >= 0 and max_k >= 1")
    words = ((),) if length == 0 else product(range(1, max_k + 1), repeat=length)
    rows = [CollatzDualCode.from_valuations(tuple(ks)).as_dict() for ks in words]
    for row in rows:
        validate_dual_row(row)
    print(
        f"Dual-code dataset length={length} k_max={max_k} rows={len(rows)} "
        "[EXACT finite rows]"
    )
    if write:
        output = collatz_data_dir()
        manifest = ExperimentManifest(
            experiment_name="dual_code",
            parameters={"length": length, "max_k": max_k},
            row_count=len(rows),
            claim_status="EXACT finite rows",
        )
        paths = write_experiment(
            rows, output, f"dual_code_m{length}_k{max_k}", manifest
        )
        print(f"outputs: {paths}")
    else:
        print("no files written; pass --write to persist ignored artifacts")
    return 0
