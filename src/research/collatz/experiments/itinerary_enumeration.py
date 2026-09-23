"""Enumerate valuation words and record exact itinerary signatures."""

from __future__ import annotations

from dataclasses import dataclass
from itertools import product
from pathlib import Path
from typing import Any

from research.collatz.experiments.exhaustive import code_version
from research.experiments.table_io import write_rows
from research.collatz.min_realizer import itinerary_signature


@dataclass
class EnumerationResult:
    m: int
    k_max: int
    rows: list[dict[str, Any]]
    paths: dict[str, str]
    status: str

    def format(self) -> str:
        return (
            f"Itinerary enumeration  m={self.m}  k_max={self.k_max}\n"
            f"words={len(self.rows)}  {self.status}\n"
            f"outputs: {self.paths}\n"
        )


def enumerate_itineraries(m: int, k_max: int) -> list[dict[str, Any]]:
    if isinstance(m, bool) or not isinstance(m, int) or m < 1:
        raise ValueError(f"m must be an integer >= 1, got {m!r}")
    if isinstance(k_max, bool) or not isinstance(k_max, int) or k_max < 1:
        raise ValueError(f"k_max must be an integer >= 1, got {k_max!r}")
    rows: list[dict[str, Any]] = []
    for ks in product(range(1, k_max + 1), repeat=m):
        sig = itinerary_signature(ks)
        row = sig.as_dict()
        row["code_version"] = code_version()
        rows.append(row)
    return rows


def run_itinerary_enumeration(
    m: int,
    k_max: int,
    output_dir: Path | str | None = None,
) -> EnumerationResult:
    rows = enumerate_itineraries(m, k_max)
    paths: dict[str, str] = {}
    if output_dir is not None:
        paths = write_rows(rows, output_dir, f"itineraries_m{m}_kmax{k_max}",
                           parameters={"m": m, "k_max": k_max})
    return EnumerationResult(
        m=m,
        k_max=k_max,
        rows=rows,
        paths=paths,
        status="EXACT signatures; finite enumeration is COMPUTATIONAL as a census",
    )
