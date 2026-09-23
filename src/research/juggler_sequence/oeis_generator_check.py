"""Exact audit of the A325904 transform of Paper B's certificate counts.

Sources: OEIS A325904, A325913 and A100982, export 2026-09-20,
revision 9cee00061c60192aafbc74726ce4a83ca7040d81 (OEIS Foundation,
CC BY-SA 4.0). Implement the stated recurrence using integers, not the
floating-point factorial division in the entry's Python example.

The published A100982 upper limit fails at order 2. The repaired limit
is tested against the independent prefix dynamic program; agreement on
a finite range is not an all-orders proof or a Juggler density theorem.
"""

from __future__ import annotations

import argparse
import json
from math import comb

from research.juggler_sequence.certificate_increment import survivor_counts
from research.juggler_sequence.lean_paths import DATA_ROOT

DATA_DIR = DATA_ROOT / "oeis_generator_check"
OEIS_REVISION = "9cee00061c60192aafbc74726ce4a83ca7040d81"

# The 27 stored terms, kept as a dated comparison fixture, not as an oracle.
STORED_GENERATOR = (
    1, 0, -3, -8, 15, -91, -54, 2531, -17021, 43035, -66258,
    1958757, -24572453, 146991979, -287482322, -3148566077,
    35506973089, -198639977241, 1006345648929, -8250266425561,
    76832268802555, -517564939540551, 1890772860334557,
    3323588929061820, -104547561696315008, 907385094824827328,
    -6313246535826877248,
)


def carrying_length(order: int) -> int:
    """A020914(order), exactly: floor(log2(3**order)) + 1."""
    if order < 0:
        raise ValueError("order must be nonnegative")
    return (3**order).bit_length()


def generator_boundary(index: int) -> int:
    """A325913(index) = floor(index/(log2(3)-1)), using integer comparisons."""
    if index < 1:
        raise ValueError("index must be positive")
    low, high = 0, 2 * index
    # 3**m < 2**(m+index) iff m < index/(log2(3)-1).
    # The upper endpoint fails since 9**index > 8**index.
    while low < high:
        mid = (low + high + 1) // 2
        if 3**mid < 1 << (mid + index):
            low = mid
        else:
            high = mid - 1
    return low


def generator_coefficients(max_index: int) -> tuple[int, ...]:
    """Compute indices 0..max_index of the exact published A325904 recurrence."""
    if max_index < 0:
        raise ValueError("max_index must be nonnegative")
    values = [1, 0]
    for n in range(2, max_index + 1):
        c = generator_boundary(n)
        values.append(-sum(values[k] * comb(c + n - k - 2, c - 2)
                           for k in range(n)))
    return tuple(values[:max_index + 1])


def certificate_from_generator(
    order: int, coefficients: tuple[int, ...], *, published_upper_limit: bool = False,
) -> int:
    """Evaluate the published transform or its candidate repaired upper limit.

    Published: L(order-1)-order-2. Candidate: L(order-1)-order.
    The latter includes every term whose binomial coefficient can be nonzero.
    """
    if order < 1:
        raise ValueError("order must be positive")
    if order == 1:
        return 1
    length = carrying_length(order - 1)
    last = length - order - (2 if published_upper_limit else 0)
    if last >= len(coefficients):
        raise ValueError("not enough generator coefficients")
    return sum(coefficients[k] * comb(length - k - 2, order - 2)
               for k in range(last + 1))


def comparison_report(max_order: int = 256) -> dict:
    """Compare the transform with independent exact survivor/certificate counts."""
    if max_order < 2:
        raise ValueError("max_order must be at least 2")
    depth = carrying_length(max_order)
    coefficients = generator_coefficients(max(depth - max_order, 26))
    survivors, minimal = survivor_counts(depth)
    repaired = {n: certificate_from_generator(n, coefficients)
                for n in range(1, max_order + 1)}
    mismatches = [n for n, value in repaired.items()
                  if value != minimal[carrying_length(n)]]
    by_length = {carrying_length(n): value for n, value in repaired.items()}
    by_length[1] = 1  # The extra leading term in A186009, absent from A100982.
    reconstructed = 1
    survivor_mismatches = []
    for d in range(1, depth + 1):
        reconstructed = 2 * reconstructed - by_length.get(d, 0)
        if reconstructed != survivors[d]:
            survivor_mismatches.append(d)
    stored_transform_mismatches = []
    for n in range(2, max_order + 1):
        if carrying_length(n - 1) - n >= len(STORED_GENERATOR):
            break
        value = certificate_from_generator(n, STORED_GENERATOR)
        expected = minimal[carrying_length(n)]
        if value != expected:
            stored_transform_mismatches.append({"order": n, "stored_transform": value,
                                                 "dynamic_program": expected})
    return {
        "oeis_revision": OEIS_REVISION,
        "generator_table_mismatches": [
            {"index": k, "stored": stored, "exact_recurrence": coefficients[k]}
            for k, stored in enumerate(STORED_GENERATOR) if stored != coefficients[k]
        ],
        "published_formula_counterexample": {
            "order": 2,
            "published": certificate_from_generator(2, coefficients, published_upper_limit=True),
            "dynamic_program": minimal[carrying_length(2)],
        },
        "certificate_orders_checked": [1, max_order],
        "repaired_transform_mismatches": mismatches,
        "survivor_depths_checked": [0, depth],
        "reconstructed_survivor_mismatches": survivor_mismatches,
        "stored_generator_transform_first_mismatch": next(iter(stored_transform_mismatches), None),
        "scope": "finite exact comparison; repaired transform not proved for all orders",
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--max-order", type=int, default=256)
    parser.add_argument("--write", action="store_true", help="save the report in this checkout")
    args = parser.parse_args()
    report = comparison_report(args.max_order)
    rendered = json.dumps(report, indent=2) + "\n"
    if args.write:
        DATA_DIR.mkdir(parents=True, exist_ok=True)
        (DATA_DIR / "verification.json").write_text(rendered, encoding="utf-8")
    print(rendered, end="")


if __name__ == "__main__":
    main()
