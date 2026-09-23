"""Fixed-integer affine-geometry Collatz commands."""

from __future__ import annotations

from research.collatz.cylinders import parse_ks
from research.experiments.paths import collatz_data_dir


def _format_fraction(value) -> str:
    if value is None:
        return "undefined"
    return f"{value.numerator}/{value.denominator}"


def _fixed_integer(n: int, max_steps: int, critical_gap: int) -> int:
    from research.collatz.asymptotic import walk_integer_ledger
    from research.collatz.fixed_integer import InfiniteTrajectoryAffineState

    print(f"Fixed-integer affine geometry of n={n}  [EXACT]")
    rows = walk_integer_ledger(n, max_steps, critical_gap=critical_gap)
    final = InfiniteTrajectoryAffineState.prefix(n, len(rows) - 1)
    print(
        f"steps={final.m}  final x={final.x}  K={final.K}  C={final.C}  "
        f"G={final.G}  regime={final.regime}"
    )
    print(
        f"lambda={_format_fraction(final.lambda_m)}  "
        f"A={_format_fraction(final.A)}  "
        f"n*={_format_fraction(final.affine_center)}"
    )
    print(f"n*-le-n={final.n_star_le_n()}  start residue={final.start_residue} "
          f"mod {final.start_modulus}")
    print("m  k  x  K  C  G  regime  n*_le_n")
    for row in rows:
        k = row["k"]
        print(
            f"{row['m']}  {k}  {row['x']}  {row['K']}  {row['C']}  "
            f"{row['G']}  {row['regime']}  {row.get('n_star_le_n')}"
        )
    return 0


def _fixed_integer_census(
    limit: int,
    max_steps: int,
    critical_gap: int,
    write: bool,
) -> int:
    from research.collatz.asymptotic import run_fixed_integer_census

    output = collatz_data_dir() if write else None
    result = run_fixed_integer_census(
        limit,
        max_steps,
        critical_gap=critical_gap,
        output_dir=output,
    )
    print("Fixed-integer affine census  [EXACT IDENTITIES; BOUNDED n_* SEARCH]")
    print(
        f"limit={result.limit}  max_steps={result.max_steps}  "
        f"odd_count={result.odd_count}  schema={result.schema_version}"
    )
    print(
        f"prefixes contracting={result.contracting_prefixes}  "
        f"expanding={result.expanding_prefixes}  "
        f"critical-near={result.critical_near_prefixes}"
    )
    print(f"n_*<=n failure count={result.n_star_le_n_failure_count}")
    if result.n_star_le_n_failures:
        first = result.n_star_le_n_failures[0]
        print(f"  smallest recorded: n={first['n']} m={first['m']} x={first['x']}")
    else:
        print("  no contracting prefix with x>n in this bound")
    if result.min_G is not None:
        print(
            f"min G={result.min_G['G']} at n={result.min_G['n']} "
            f"m={result.min_G['m']} regime={result.min_G['regime']}"
        )
    if result.min_contracting_G is not None:
        print(
            f"min contracting G={result.min_contracting_G['G']} at "
            f"n={result.min_contracting_G['n']} m={result.min_contracting_G['m']}"
        )
    if result.paths:
        print(f"outputs: {result.paths}")
    return 0


def _affine_gap(n: int, max_steps: int) -> int:
    from research.collatz.affine_gap import addend_sign_law
    from research.collatz.asymptotic import walk_integer_ledger

    print(f"Integer affine gap G of n={n}  [EXACT]")
    print("G = n(2^K - 3^m) - C = 2^K (n - x)")
    rows = walk_integer_ledger(n, max_steps)
    for row in rows[1:]:
        k = row["k"]
        print(
            f"m={row['m']} k={k} x={row['x']} G={row['G']}  "
            f"addend_sign={addend_sign_law(n, k)}  regime={row['regime']}"
        )
    return 0


def _periodic_code(ks: str) -> int:
    from research.collatz.periodic_code import PeriodicFixedPointTheorem
    from research.collatz.periodic_itineraries import periodic_candidate

    valuations = tuple(parse_ks(ks))
    theorem = PeriodicFixedPointTheorem.from_valuations(valuations)
    candidate = periodic_candidate(valuations)
    print("Periodic-code fixed-point identity  [EXACT — HUMAN PROOF]")
    print(f"valuations={list(valuations)}  p={theorem.p}  K={theorem.K}  C={theorem.C}")
    print(f"identity: {theorem.identity}")
    print(f"2^K-3^p={theorem.gap}  expanding_excludes_positive={theorem.expanding_excludes_positive}")
    print(f"positive affine candidate={theorem.positive_candidate}")
    print(
        f"cylinder/orbit compatible={candidate.compatible}  "
        f"n={candidate.n}  {candidate.reason}"
    )
    print("Excluding a periodic code does not prove Collatz.")
    return 0
