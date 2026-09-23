"""Finite checks of the Beatty phase transfer and its proposed jump series.

Integer survivor counts are exact. Logarithms, phases and profile comparisons
are floating-point diagnostics, not certified enclosures or a proof of a limit.
The analytic argument and its formalization boundary are recorded in
docs/theory/juggler_beatty_first_passage_note.md.
"""

from __future__ import annotations

import argparse
from bisect import bisect_left
from dataclasses import asdict, dataclass
import json
import math
from pathlib import Path

from research.experiments.provenance import write_manifest
from research.juggler_sequence.jump_spectrum import survivor_counts
from research.juggler_sequence.lean_paths import DATA_ROOT, REPO_ROOT

ALPHA = math.log2(3.0)
BETA = 1 / ALPHA
Q = 1 - BETA
S = ALPHA - 1
V = BETA ** (-BETA) * Q ** (-Q)
B = V**ALPHA


@dataclass(frozen=True)
class Atom:
    """An exact crossing count with its numerical phase and normalized weight."""

    order: int
    depth: int
    phase: float
    count: int
    ratio: float
    weight: float


def atoms(counts: list[int]) -> list[Atom]:
    """Use integer powers to locate each crossing; never round a logarithm."""
    out = []
    power = 3
    r = 1
    while True:
        m = power.bit_length() - 1
        if m + 1 >= len(counts):
            return out
        c = 2 * counts[m] - counts[m + 1]
        if c <= 0:
            raise ValueError(f"Nonpositive crossing count at order {r}")
        delta = r * ALPHA - m
        # w_r = c_r beta^r q^(m_r-r); this avoids real powers of huge bases.
        weight = math.exp(math.log(c) + r * math.log(BETA) + (m-r) * math.log(Q))
        out.append(Atom(r, m + 1, delta, c,
                        (r * c) / math.comb(m - 1, r - 1), weight))
        r += 1
        power *= 3


def endpoint_counts(depth: int) -> list[int]:
    """Count unrestricted words whose final exponent is positive, exactly."""
    result = [1]
    threshold = 0
    power = 1
    for n in range(1, depth + 1):
        while power <= 2**n:
            power *= 3
            threshold += 1
        result.append(sum(math.comb(n, k) for k in range(threshold, n + 1)))
    return result


def check_spitzer_coefficients(counts: list[int], depth: int) -> None:
    """Check n N_n = sum T_k N_(n-k), independently using binomial tails."""
    terminal = endpoint_counts(depth)
    for n in range(1, depth + 1):
        value = sum(terminal[k] * counts[n-k] for k in range(1, n+1))
        if value != n * counts[n]:
            raise AssertionError(f"Spitzer coefficient identity fails at {n}")


def cumulative_head(rows: list[Atom], phases: list[float]) -> list[float]:
    """Evaluate the left-continuous finite series; omit an atom at equality."""
    ordered = sorted((row.phase, row.weight) for row in rows)
    locations = [x for x, _ in ordered]
    cumulative = [0.0]
    for _, weight in ordered:
        cumulative.append(cumulative[-1] + weight)
    return [1 + cumulative[bisect_left(locations, x)] for x in phases]


def run(depth: int = 8000, coefficient_depth: int = 256) -> dict:
    """Reproduce the bounded integer and numerical comparisons in the note."""
    if depth < 16 or not 1 <= coefficient_depth <= depth:
        raise ValueError("Require depth >= 16 and 1 <= coefficient_depth <= depth")
    counts = survivor_counts(depth)
    check_spitzer_coefficients(counts, coefficient_depth)
    rows = atoms(counts)
    sample = rows[-min(500, len(rows)):]
    comparisons = []
    for cutoff in sorted({len(rows)//4, len(rows)//2, len(rows)}):
        head = rows[:cutoff]
        predicted = cumulative_head(head, [row.phase for row in sample])
        errors = [row.ratio - value for row, value in zip(sample, predicted)]
        comparisons.append({
            "head_orders": cutoff,
            "missing_mass_from_total_mass_identity": 1/S - sum(row.weight for row in head),
            "min_actual_ratio_minus_head": min(errors),
            "max_actual_ratio_minus_head": max(errors),
        })
    return {
        "scope": "Exact counts and finite coefficient identities; floating-point phase diagnostics.",
        "depth": depth,
        "max_order": len(rows),
        "coefficient_identity_checked_through": coefficient_depth,
        "constants": {"alpha": ALPHA, "beta": BETA, "q": Q, "v": V, "B": B},
        "first_atoms": [asdict(row) for row in rows[:12]],
        "sample_orders": [sample[0].order, sample[-1].order],
        "head_comparisons": comparisons,
        "total_atom_mass": 1/S,
        "total_mass_status": "Written centered-walk argument, not a finite computation.",
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--depth", type=int, default=8000)
    parser.add_argument("--coefficient-depth", type=int, default=256)
    parser.add_argument("--output", type=Path,
                        default=DATA_ROOT / "winkler_phase_collapse" / "phase_transfer.json")
    args = parser.parse_args()
    payload = run(args.depth, args.coefficient_depth)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8", newline="\n")
    write_manifest(
        args.output.with_suffix(".research.json"), programme="juggler",
        research_id="juggler/winkler_phase_collapse",
        scope=f"Exact survivor counts at depths 0..{args.depth}; exact binomial coefficient identity "
              f"through {args.coefficient_depth}; numerical jump diagnostics through order {payload['max_order']}.",
        parameters={"depth": args.depth, "coefficient_depth": args.coefficient_depth},
        outputs=[args.output], sources=[Path(__file__),
                 REPO_ROOT / "src/research/juggler_sequence/jump_spectrum.py"],
    )
    print(json.dumps(payload, indent=2))


if __name__ == "__main__":
    main()
