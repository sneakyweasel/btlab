"""Fixed-(m, K) census: homogeneous budget vs order-sensitive C and R."""

from __future__ import annotations

from dataclasses import dataclass
from math import log2
from pathlib import Path
from typing import Any

from research.experiments.table_io import write_rows
from research.collatz.itinerary import affine_constant
from research.collatz.min_realizer import itinerary_signature, min_realizer


def compositions_of(total: int, parts: int, k_max: int) -> tuple[tuple[int, ...], ...]:
    """Compositions of ``total`` into ``parts`` parts, each in ``1..k_max``."""
    if parts == 0:
        return ((),) if total == 0 else ()
    if parts == 1:
        return ((total,),) if 1 <= total <= k_max else ()
    out: list[tuple[int, ...]] = []
    lo = max(1, total - k_max * (parts - 1))
    hi = min(k_max, total - (parts - 1))
    for first in range(lo, hi + 1):
        for rest in compositions_of(total - first, parts - 1, k_max):
            out.append((first,) + rest)
    return tuple(out)


@dataclass
class FixedBudgetResult:
    m: int
    K: int
    rows: list[dict[str, Any]]
    summary: dict[str, Any]
    paths: dict[str, str]

    def format(self) -> str:
        s = self.summary
        return (
            f"Fixed (m,K)=({self.m},{self.K})  words={len(self.rows)}  [EXACT]\n"
            f"C min={s.get('C_min')} max={s.get('C_max')}\n"
            f"R min={s.get('R_min')} max={s.get('R_max')}\n"
            f"median log2 R (OBSERVATION)={s.get('median_log2_R')}\n"
            f"R varies across compositions: {s.get('R_varies_across_compositions')}\n"
            f"outputs: {self.paths}\n"
        )


def _median(values: list[float]) -> float | None:
    if not values:
        return None
    xs = sorted(values)
    n = len(xs)
    mid = n // 2
    if n % 2:
        return xs[mid]
    return 0.5 * (xs[mid - 1] + xs[mid])


def run_fixed_budget(
    m: int,
    sum_k: int,
    k_max: int | None = None,
    output_dir: Path | str | None = None,
) -> FixedBudgetResult:
    if isinstance(m, bool) or not isinstance(m, int) or m < 1:
        raise ValueError(f"m must be an integer >= 1, got {m!r}")
    if isinstance(sum_k, bool) or not isinstance(sum_k, int) or sum_k < m:
        raise ValueError(f"sum_k must be an integer >= m, got {sum_k!r}")
    if k_max is None:
        k_max = sum_k - (m - 1)
    words = compositions_of(sum_k, m, k_max)
    rows: list[dict[str, Any]] = []
    cs: list[int] = []
    rs: list[int] = []
    for ks in words:
        sig = itinerary_signature(ks)
        rows.append(sig.as_dict())
        cs.append(sig.C)
        rs.append(sig.R)
    logs = [log2(r) for r in rs if r > 0]
    summary = {
        "word_count": len(rows),
        "C_min": min(cs) if cs else None,
        "C_max": max(cs) if cs else None,
        "R_min": min(rs) if rs else None,
        "R_max": max(rs) if rs else None,
        "median_log2_R": _median(logs),
        "R_varies_across_compositions": len(set(rs)) > 1,
        "C_varies_across_compositions": len(set(cs)) > 1,
        "status": "EXACT C,R; median log2 R is OBSERVATION",
    }
    paths: dict[str, str] = {}
    if output_dir is not None:
        paths = write_rows(rows, output_dir, f"fixed_budget_m{m}_K{sum_k}",
                           parameters={"m": m, "sum_k": sum_k})
    return FixedBudgetResult(m=m, K=sum_k, rows=rows, summary=summary, paths=paths)


def compare_same_K_order(ks_a: tuple[int, ...], ks_b: tuple[int, ...]) -> dict[str, object]:
    if sum(ks_a) != sum(ks_b) or len(ks_a) != len(ks_b):
        raise ValueError("words must share (m, K)")
    return {
        "a": itinerary_signature(ks_a).as_dict(),
        "b": itinerary_signature(ks_b).as_dict(),
        "C_a": affine_constant(ks_a),
        "C_b": affine_constant(ks_b),
        "R_a": min_realizer(ks_a),
        "R_b": min_realizer(ks_b),
        "status": "EXACT",
    }
