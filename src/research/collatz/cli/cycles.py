"""Cycle-language Collatz commands."""

from __future__ import annotations

from research.collatz.cylinders import parse_ks
from research.experiments.paths import collatz_data_dir


def _cycle(ks: str) -> int:
    from research.collatz.cycles import candidate_cycle

    rec = candidate_cycle(parse_ks(ks))
    print("Periodic exponent code  [EXACT AFFINE; CYCLE ONLY IF VALUATIONS MATCH]")
    print(f"code={list(rec.code)}  primitive={rec.is_primitive}  p={rec.p} K={rec.K} C={rec.C}")
    print(f"D=2^K-3^p={rec.denominator}  candidate={rec.candidate_n}")
    print(
        f"integral={rec.is_integral}  exact_period={rec.is_exact_period}  "
        f"exact_cycle={rec.is_exact_cycle}"
    )
    print(f"states={rec.candidate_states}  lifts={list(rec.lift_digits)}")
    if rec.amplitude is not None:
        print(
            f"amplitude additive={rec.amplitude.additive}  "
            f"multiplicative={rec.amplitude.multiplicative}"
        )
    print(f"canonical={list(rec.canonical_code)}  reason={rec.reason}")
    print("A finite code check does not prove Collatz.")
    return 0


def _cycle_census(max_p: int, k_max: int, additive_bound: int | None, write: bool) -> int:
    from research.collatz.experiments.cycle_census import run_cycle_census

    output = collatz_data_dir() if write else None
    result = run_cycle_census(
        max_p,
        k_max,
        additive_bound=additive_bound,
        output_dir=output,
    )
    print("Cycle-language census  [EXACT PRUNING; BOUNDED SEARCH]")
    print(f"max_p={result.max_p} k_max={result.k_max} schema={result.schema_version}")
    print(f"counts={result.counts}")
    print(f"exact cycles={len(result.exact_cycles)}")
    for row in result.exact_cycles[:8]:
        print(f"  code={row['code']} n={row['candidate_n']} amp={row['amplitude']}")
    print(f"K>2p witnesses={result.K_gt_2p['witnesses']}")
    print(f"C mod 3: {result.C_mod_3['classification']}")
    if result.paths:
        print(f"outputs: {result.paths}")
    print("Absence of cycles in a finite search does not prove Collatz.")
    return 0


def _cycle_language(additive: int, max_p: int, k_max: int) -> int:
    from research.collatz.cycle_language import enumerate_cycle_language

    counts, cycles, language = enumerate_cycle_language(
        max_p, k_max, additive_bound=additive
    )
    print(f"L_A additive A={additive}  [BOUNDED LANGUAGE]")
    print(f"counts={counts.as_dict()}")
    print(f"language size={len(language)}  exact cycles={len(cycles)}")
    for rec in language:
        print(f"  {list(rec.code)} n={rec.candidate_n} add={rec.amplitude.additive}")
    return 0
