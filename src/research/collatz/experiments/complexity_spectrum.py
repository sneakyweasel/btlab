"""Transducer / valuation-recognizer complexity spectrum.

For each ``k = 1..K_max`` record:

- ``N_k``: minimized state count of the LSD ``/2^k`` Mealy product
- ``A_k``: minimized DFA size of ``L_k = {w : v2(decode(w)) = k}``
- ``C_k``: the pair ``(A_k, N_k)`` and the product ``A_k * N_k`` as a
  crude bound on "recognize valuation k then divide by 2^k"

Naive bound ``3^k`` is **EXACT — HUMAN PROOF** as a product construction. Reachable and
minimized sizes are **COMPUTATIONALLY VERIFIED**. The pattern
``N_k = 2^k + 1`` is a **CONJECTURE** until a proof or counterexample.
"""

from __future__ import annotations

import json
from dataclasses import dataclass, field
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from research.collatz.experiments.exhaustive import code_version
from research.collatz.languages.cylinder_dfa import valuation_class_minimized_size
from bt.transducers.divide_by_two_power import DivideByTwoPowerTransducer
from research.experiments.provenance import write_manifest
from research.experiments.table_io import timestamp as output_timestamp


@dataclass
class ComplexitySpectrumResult:
    k_max: int
    rows: list[dict[str, Any]]
    n_k_equals_two_k_plus_one: bool
    timestamp: str
    code_version: str | None
    output_path: str | None = None
    sample_rows: list[dict[str, Any]] = field(default_factory=list)

    def format(self) -> str:
        lines = [
            f"Complexity spectrum  k=1..{self.k_max}",
            "N_k = minimized /2^k Mealy  "
            "A_k = minimized L_k DFA  "
            "C_k product bound = A_k * N_k",
            f"CONJECTURE N_k = 2^k+1 holds on this range: "
            f"{str(self.n_k_equals_two_k_plus_one).lower()}",
            "",
            f"{'k':>4}  {'naive':>8}  {'reach':>8}  {'N_k':>6}  "
            f"{'A_k':>6}  {'A_k*N_k':>10}  {'2^k+1':>6}",
        ]
        for row in self.rows:
            lines.append(
                f"{row['k']:>4}  {row['naive_bound']:>8}  {row['reachable']:>8}  "
                f"{row['N_k']:>6}  {row['A_k']:>6}  {row['C_k_product_bound']:>10}  "
                f"{row['two_k_plus_one']:>6}"
            )
        lines.append("")
        lines.append(
            "Naive 3^k is EXACT — HUMAN PROOF. N_k and A_k are COMPUTATIONALLY VERIFIED. "
            "N_k = 2^k+1 is a CONJECTURE on this finite range, not a theorem. "
            "Comparing N_k to Pr(k)~2^{-k} is an OBSERVATION only."
        )
        lines.append("")
        return "\n".join(lines)


def complexity_row(k: int) -> dict[str, Any]:
    if isinstance(k, bool) or not isinstance(k, int) or k < 1:
        raise ValueError(f"k must be an integer >= 1, got {k!r}")
    report = DivideByTwoPowerTransducer(k).complexity_report()
    a_k = valuation_class_minimized_size(k)
    n_k = report["minimized"]
    return {
        "k": k,
        "naive_bound": report["naive_bound"],
        "reachable": report["reachable"],
        "N_k": n_k,
        "A_k": a_k,
        "C_k": {"A_k": a_k, "N_k": n_k},
        "C_k_product_bound": a_k * n_k,
        "two_k_plus_one": (1 << k) + 1,
        "matches_two_k_plus_one": n_k == (1 << k) + 1,
        "reachable_two_k_plus_one_minus_one": report["reachable"] == (1 << (k + 1)) - 1,
    }


def run_complexity_spectrum(
    k_max: int,
    output_dir: Path | str | None = None,
) -> ComplexitySpectrumResult:
    if isinstance(k_max, bool) or not isinstance(k_max, int) or k_max < 1:
        raise ValueError(f"k_max must be an integer >= 1, got {k_max!r}")
    rows = [complexity_row(k) for k in range(1, k_max + 1)]
    holds = all(r["matches_two_k_plus_one"] for r in rows)
    timestamp = datetime.now(timezone.utc).isoformat()
    result = ComplexitySpectrumResult(
        k_max=k_max,
        rows=rows,
        n_k_equals_two_k_plus_one=holds,
        timestamp=timestamp,
        code_version=code_version(),
        sample_rows=rows,
    )
    if output_dir is not None:
        base = Path(output_dir)
        reports = base / "reports"
        reports.mkdir(parents=True, exist_ok=True)
        stamp = output_timestamp()
        path = reports / f"complexity_spectrum_kmax{k_max}_{stamp}.json"
        payload = {
            "experiment_name": "complexity_spectrum",
            "k_max": k_max,
            "timestamp": timestamp,
            "code_version": result.code_version,
            "claim_status": {
                "naive_bound": "EXACT — HUMAN PROOF (k-fold product of a 3-state machine)",
                "N_k_A_k": "COMPUTATIONALLY VERIFIED",
                "N_k_equals_2_k_plus_1": (
                    "CONJECTURE holds on this range"
                    if holds
                    else "CONJECTURE fails on this range (counterexample in rows)"
                ),
                "rare_branches_heavier": "OBSERVATION only; not a Collatz theorem",
            },
            "rows": rows,
        }
        path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")
        result.output_path = str(path)
        write_manifest(path.with_suffix(".research.json"), programme="collatz",
                       research_id="collatz/overview",
                       scope=f"Transducer complexity for k=1..{k_max}; finite computation only.",
                       parameters={"k_max": k_max}, outputs=[path])
    return result
