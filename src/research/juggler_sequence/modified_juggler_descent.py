"""Two-step floor cancellation for the modified Juggler map A095396.

The odd branch is O(n)=floor(n**(3/2)), the even branch E(n)=floor(n**(2/3)).
Do not confuse E with the square-root branch of the original Juggler map.
The dossier proves E(O(n)) = n for squares and n-1 otherwise. Thus an
actual OE pair drops by exactly one. This is not a termination theorem.
"""

from __future__ import annotations

import argparse
import json
from math import isqrt

from research.juggler_sequence.cycle_ooo_scale import icbrt
from research.juggler_sequence.lean_paths import DATA_ROOT

DATA_DIR = DATA_ROOT / "modified_juggler_descent"


def odd_branch(n: int) -> int:
    """O(n), evaluated without enforcing odd parity, in exact integer arithmetic."""
    if n < 0:
        raise ValueError("n must be nonnegative")
    return isqrt(n**3)


def even_branch(n: int) -> int:
    """E(n), evaluated without enforcing even parity, in exact integer arithmetic."""
    if n < 0:
        raise ValueError("n must be nonnegative")
    return icbrt(n**2)


def modified_juggler(n: int) -> int:
    """A095396 on nonnegative integers (the OEIS entry starts at 1)."""
    if n < 0:
        raise ValueError("n must be nonnegative")
    return odd_branch(n) if n % 2 else even_branch(n)


def comparison_report(max_start: int = 10000) -> dict:
    """Check both equality characterizations and realized mixed pairs."""
    if max_start < 1:
        raise ValueError("max_start must be positive")
    failures = []
    pair_counts = {"OE": 0, "EO": 0}
    first_examples = {}
    for n in range(max_start + 1):
        o, e = odd_branch(n), even_branch(n)
        eo, oe = even_branch(o), odd_branch(e)
        square, cube = isqrt(n)**2 == n, icbrt(n)**3 == n
        if eo != n - int(not square):
            failures.append({"kind": "even_after_odd_identity", "start": n})
        if oe > n or ((oe == n) != cube):
            failures.append({"kind": "odd_after_even_equality", "start": n})
        if n % 2 and o % 2 == 0:
            pair_counts["OE"] += 1
            first_examples.setdefault("OE", [n, o, eo])
            if eo != n - 1:
                failures.append({"kind": "actual_OE_unit_descent", "start": n})
        if n > 0 and n % 2 == 0 and e % 2:
            pair_counts["EO"] += 1
            first_examples.setdefault("EO", [n, e, oe])
            if oe >= n:
                failures.append({"kind": "actual_EO_strict_descent", "start": n})
    return {
        "map": "A095396: even exponent 2/3, odd exponent 3/2",
        "starts_checked": [0, max_start],
        "failures": failures,
        "realized_pair_counts": pair_counts,
        "first_examples": first_examples,
        "formal_OE_equality_example_not_realized": [9, odd_branch(9), even_branch(odd_branch(9))],
        "formal_EO_equality_example_not_realized": [8, even_branch(8), odd_branch(even_branch(8))],
        "scope": "finite regression for a written proof; no termination or novelty claim",
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--max-start", type=int, default=10000)
    parser.add_argument("--write", action="store_true", help="save the report in this checkout")
    args = parser.parse_args()
    rendered = json.dumps(comparison_report(args.max_start), indent=2) + "\n"
    if args.write:
        DATA_DIR.mkdir(parents=True, exist_ok=True)
        (DATA_DIR / "verification.json").write_text(rendered, encoding="utf-8")
    print(rendered, end="")


if __name__ == "__main__":
    main()
