"""Permutation census for a valuation multiset."""

from __future__ import annotations

from pathlib import Path

from research.collatz.cylinders import parse_ks
from research.experiments.table_io import write_rows
from research.collatz.order_analysis import extremal_orders, permutation_table


def run_permutation_analysis(
    ks: tuple[int, ...] | str | list[int],
    output_dir: Path | str | None = None,
) -> dict[str, object]:
    ks = parse_ks(ks)
    rows = permutation_table(ks)
    summary = extremal_orders(ks)
    paths: dict[str, str] = {}
    if output_dir is not None:
        paths = write_rows(list(rows), output_dir, "permutations", parameters={"ks": list(ks)})
    return {
        "summary": summary,
        "rows": list(rows),
        "paths": paths,
        "status": summary["status"],
    }
