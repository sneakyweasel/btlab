"""Compatibility, information, and affine-center Collatz commands."""

from __future__ import annotations

from bt.representation import encode
from research.experiments.paths import collatz_data_dir


def _compatibility(ks: str) -> int:
    from research.collatz.compatibility import ExponentCodeDiagnostic

    diagnostic = ExponentCodeDiagnostic.from_valuations(ks)
    print("Four-coordinate exponent-code diagnostic")
    print(f"valuations={diagnostic.valuations}  m={diagnostic.m}  K={diagnostic.K}")
    print(f"C={diagnostic.C}")
    print(
        f"refined R={diagnostic.R}  Kramer r={diagnostic.r}  "
        f"BT(R)={diagnostic.balanced_ternary_R}"
    )
    print(
        f"Kramer M={diagnostic.M}  endpoint={diagnostic.canonical_endpoint}  "
        f"modulus_3={diagnostic.three_power}"
    )
    print(f"lift_digits={diagnostic.lift_digits}")
    print(
        f"exact drift=3^{diagnostic.m}/2^{diagnostic.K}="
        f"{diagnostic.three_power}/{diagnostic.two_power}"
    )
    print(
        f"estimated d={diagnostic.d:.12g}  rho_r={diagnostic.rho_r:.12g}  "
        f"rho_M={diagnostic.rho_M:.12g}  [NATURAL-LOG ESTIMATES]"
    )
    print("R, r, M, endpoint, lifts, and drift powers: [EXACT]")
    return 0


def _compatibility_graph(max_depth: int, max_k: int, root: str) -> int:
    from research.collatz.compatibility import build_compatibility_graph

    graph = build_compatibility_graph(max_depth, max_k, root=root)
    print("Four-coordinate compatibility graph  [EXACT BOUNDED TREE]")
    print(
        f"root={graph.root.valuations} depth={graph.max_depth} k_max={graph.k_max} "
        f"nodes={len(graph.nodes)} edges={len(graph.edges)} valid={graph.validates()}"
    )
    for edge in graph.edges[:20]:
        print(
            f"  {edge.source} --k={edge.valuation},t={edge.lift_digit}--> "
            f"{edge.target}"
        )
    return 0


def _rational_base(n: int) -> int:
    from research.collatz.rational_base import RationalBaseThreeHalves

    representation = RationalBaseThreeHalves.from_int(n)
    display = representation.word or "epsilon"
    print("Rational-base 3/2 comparison  [EXACT]")
    print(f"n={n}")
    print(f"base_3/2={display}")
    print(f"BT(n)={encode(n).word()}")
    print(f"round_trip={representation.validates()}")
    if n % 2:
        child = representation.odd_step()
        print(
            f"odd (3n+1)/2 appends 1: {child.word == representation.word + '1'}  "
            f"child={child.value} word={child.word}"
        )
    else:
        print("odd append-1 identity not applicable; even division locality is open")
    return 0


def _information_test(
    max_length: int,
    max_k: int,
    precision_max: int,
    write: bool,
) -> int:
    from research.collatz.experiments.information_content import run_information_content

    if precision_max < 1:
        raise ValueError("precision_max must be >= 1")
    output = collatz_data_dir() if write else None
    result = run_information_content(
        max_length,
        max_k,
        precisions=tuple(range(1, precision_max + 1)),
        output_dir=output,
    )
    print("Balanced-ternary information-content test")
    print(f"rows={len(result.rows)} schema={result.schema_version}")
    bt_report = result.reports["BT(R)"]
    for state, report in bt_report["states"].items():
        print(
            f"  {state} determines BT(R)={report['determines_on_sample']}  "
            f"{report['status']}"
        )
    for observable, witness in result.balanced_ternary_collisions.items():
        if witness is None:
            print(f"  BT(R) collision for {observable}: none in bounded sample")
        else:
            print(
                f"  BT(R) does not determine {observable}: "
                f"{witness['row_a']['valuations']} vs "
                f"{witness['row_b']['valuations']}  [EXACT WITNESS]"
            )
    print(
        "H_BT strong independence: REFUTED EXACTLY because R determines BT(R); "
        "lossy-state results remain bounded observations."
    )
    if result.paths:
        print(f"outputs: {result.paths}")
    return 0


def _near_critical(
    max_length: int,
    max_k: int,
    random_length: int,
    random_count: int,
    seed: int,
    write: bool,
) -> int:
    from research.collatz.experiments.near_critical import run_near_critical

    output = collatz_data_dir() if write else None
    result = run_near_critical(
        exhaustive_max_length=max_length,
        exhaustive_max_k=max_k,
        random_length=random_length,
        random_count=random_count,
        seed=seed,
        output_dir=output,
    )
    families: dict[str, int] = {}
    for row in result.rows:
        family = str(row["family"])
        families[family] = families.get(family, 0) + 1
    print("Near-critical four-coordinate dataset  [EXACT SELECTION]")
    print(f"rows={len(result.rows)} seed={result.seed} schema={result.schema_version}")
    print(f"families={families}")
    print(f"Rozier-Terracol comparison fixtures={len(result.fixtures)}")
    print("Dataset patterns are OBSERVATIONS, not Collatz obstructions.")
    if result.paths:
        print(f"outputs: {result.paths}")
    return 0


def _format_fraction_pair(pair: tuple[int, int] | list[int]) -> str:
    return f"{pair[0]}/{pair[1]}"


def _affine_center(ks: str, critical_gap: int) -> int:
    from research.collatz.affine_center import AffineCenterState

    state = AffineCenterState.from_valuations(ks)
    print("Affine-center geometry  [EXACT]")
    print(f"valuations={state.valuations}  m={state.m}  K={state.K}")
    print(f"C={state.C}  R={state.R}  X={state.X}  M={state.M}")
    print(
        f"2^K-3^m={state.gap}  regime={state.regime.value}  "
        f"partition={state.partition(critical_gap)}"
    )
    print(
        f"n*={_format_fraction_pair((state.n_star.numerator, state.n_star.denominator))}"
    )
    print(
        f"R-n* raw={_format_fraction_pair(state.R_difference_raw)}  "
        f"reduced={_format_fraction_pair(state.R_difference_reduced)}"
    )
    print(
        f"X-n* raw={_format_fraction_pair(state.X_difference_raw)}  "
        f"reduced={_format_fraction_pair(state.X_difference_reduced)}"
    )
    print(
        f"center scaling=(3^{state.m}/2^{state.K})="
        f"{_format_fraction_pair([state.three_power, state.two_power])}"
    )
    print(
        f"X=M+q*3^m with q={state.endpoint_lift_quotient}; "
        f"all exact inequalities={all(state.exact_inequalities().values())}"
    )
    return 0


def _affine_center_census(
    max_length: int,
    max_k: int,
    critical_gap: int,
    closest_count: int,
    write: bool,
) -> int:
    from research.collatz.experiments.affine_center import run_affine_center_census

    output = collatz_data_dir() if write else None
    result = run_affine_center_census(
        max_length,
        max_k,
        critical_gap=critical_gap,
        closest_count=closest_count,
        output_dir=output,
    )
    print("Affine-center census  [EXACT ROWS; BOUNDED ORDER TESTS]")
    print(f"rows={len(result.rows)} schema={result.schema_version}")
    print(f"partitions={result.partition_counts}")
    failures = sum(
        int(record["failure_count"])
        for record in result.exact_inequalities.values()
    )
    print(f"theorem-backed inequality failures={failures}")
    for name, record in result.coordinate_orders.items():
        if record["smallest_true"] is not None and record["smallest_false"] is not None:
            print(f"  {name}: both directions witnessed; not universal")
    if result.closest_to_critical:
        nearest = result.closest_to_critical[0]
        print(
            f"closest gap={nearest['gap']} code={nearest['valuations']} "
            f"n*={_format_fraction_pair(nearest['n_star'])}"
        )
    if result.paths:
        print(f"outputs: {result.paths}")
    return 0
