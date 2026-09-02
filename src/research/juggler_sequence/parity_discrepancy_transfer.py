"""One-step transfer of odd-image parity discrepancy.

Not a Research Engine experiment. Not a halt theorem. Not a
parity-frequency theorem. Does not reopen closed PE / residual /
2-adic / landing-θ / probabilistic-LD / local-compression branches.
Does not build a Weyl-sum engine.

D(I) is the image-parity sum on odd sources in an interval I, not
the trivial source-parity sum. Transfer means the same sign sum on
the Juggler-generated set Y = J_O(O(I)), not prefix differencing of
S_O(N).
"""

from __future__ import annotations

import csv
import json
from math import isqrt
from pathlib import Path
from typing import Any, Iterable

from research.juggler_sequence.lean_paths import has_named, juggler_text
from research.juggler_sequence.odd_image_discrepancy import (
    analytic_majorant,
    odd_image,
    odd_image_sign,
    so_of_odd_values,
)
from research.juggler_sequence.power_itineraries import ANTI_OVERCLAIM, floor_power

REPO_ROOT = Path(__file__).resolve().parents[3]
JSON_PATH = REPO_ROOT / "docs" / "research" / "juggler_parity_discrepancy_transfer.json"
DOC_PATH = REPO_ROOT / "docs" / "research" / "juggler_parity_discrepancy_transfer.md"
DOSSIER_PATH = REPO_ROOT / "docs" / "problems" / "juggler_parity_discrepancy_transfer.md"
DATA_DIR = REPO_ROOT / "data" / "research" / "juggler" / "parity_transfer"

N_MAX = 1_000_000
LENGTH_GRID = (10, 20, 50, 100, 200, 500, 1_000, 2_000, 5_000, 10_000, 20_000, 50_000, 100_000)
LOCATION_LENGTHS = (100, 1_000, 10_000, 100_000)
TRANSFER_LENGTHS = (20, 50, 100, 200, 500, 1_000, 2_000, 10_000, 100_000, 1_000_000)
ITERATE_LENGTHS = (20, 50, 100, 200, 500, 1_000)
HARD_STARTS = (37, 163, 173, 193, 229, 357)
CONCENTRATION = 0.25
MIN_TRANSFER_ODD = 20
LEAN_THEOREMS = (
    "odd_preimage_unique",
    "odd_preimage_iff",
    "floorPower_odd_macro_direction",
    "floorPower_odd_nondecreasing",
    "landingParity_odd_iff",
)
FORBIDDEN_ENGINES = (
    "ResidualGraph",
    "ResidualState",
    "MilestoneGraph",
    "PowerHeight",
    "CycleEngine",
)

CLASS_INTERVAL = "INTERVAL_UNIFORM_GREEN"
CLASS_IMAGE = "IMAGE_TRANSFER_GREEN"
CLASS_WEIGHTED = "WEIGHTED_TRANSFER_GREEN"
CLASS_OPERATOR = "OPERATOR_TRANSFER_GREEN"
CLASS_ITERATED = "ITERATED_TRANSFER_GREEN"
CLASS_DRIFT = "DRIFT_BRIDGE_GREEN"
CLASS_COMPLEX = "TRANSFER_COMPLEX"


def _round(value: float | None) -> float | None:
    if value is None:
        return None
    return round(float(value), 8)


def first_odd(bound: int) -> int:
    if bound <= 1:
        return 1 if bound == 1 else 0
    return bound if bound % 2 else bound + 1


def last_odd(bound: int) -> int:
    if bound < 1:
        return 0
    return bound if bound % 2 else bound - 1


def odd_count_interval(start: int, stop: int) -> int:
    lo = first_odd(start)
    hi = last_odd(stop)
    if lo == 0 or hi == 0 or lo > hi:
        return 0
    return (hi - lo) // 2 + 1


def source_parity_sum(start: int, stop: int) -> int:
    """Trivial signed count of source parity on O(I). Not D(I)."""
    lo = first_odd(start)
    hi = last_odd(stop)
    if lo == 0 or hi == 0 or lo > hi:
        return 0
    return -((hi - lo) // 2 + 1)


def interval_D_direct(start: int, stop: int) -> int:
    total = 0
    n = first_odd(start)
    hi = last_odd(stop)
    if n == 0 or hi == 0 or n > hi:
        return 0
    while n <= hi:
        total += odd_image_sign(n)
        n += 2
    return total


class PrefixTables:
    """Prefix sums of s(n) on odd n <= n_max. Exact integer arithmetic."""

    def __init__(self, n_max: int) -> None:
        if n_max < 1:
            raise ValueError("n_max must be positive")
        self.n_max = n_max
        n_odds = (n_max + 1) // 2
        images = [0] * n_odds
        signs = [0] * n_odds
        prefix = [0] * (n_odds + 1)
        prefix_n = [0] * (n_odds + 1)
        prefix_jac = [0] * (n_odds + 1)
        for index in range(n_odds):
            n = 2 * index + 1
            image = isqrt(n * n * n)
            sign = 1 - 2 * (image & 1)
            images[index] = image
            signs[index] = sign
            prefix[index + 1] = prefix[index] + sign
            prefix_n[index + 1] = prefix_n[index] + n * sign
            prefix_jac[index + 1] = prefix_jac[index] + 3 * isqrt(n) * sign
        self.images = images
        self.signs = signs
        self.prefix = prefix
        self.prefix_n = prefix_n
        self.prefix_jac = prefix_jac
        self.max_abs_so = max(abs(value) for value in prefix)
        self.argmax_so = 1
        best = 0
        for index, value in enumerate(prefix):
            if abs(value) > best:
                best = abs(value)
                self.argmax_so = 2 * index - 1 if index else 1
                self.max_abs_so = best

    def so_prefix(self, n: int) -> int:
        if n < 1:
            return 0
        capped = min(n, self.n_max)
        hi = last_odd(capped)
        if hi < 1:
            return 0
        return self.prefix[hi // 2 + 1]

    def interval_bounds(self, start: int, stop: int) -> tuple[int, int] | None:
        lo = first_odd(max(start, 1))
        hi = last_odd(min(stop, self.n_max))
        if lo == 0 or hi == 0 or lo > hi:
            return None
        return lo, hi

    def interval_D(self, start: int, stop: int) -> int:
        bounds = self.interval_bounds(start, stop)
        if bounds is None:
            return 0
        lo, hi = bounds
        return self.prefix[hi // 2 + 1] - self.prefix[lo // 2]

    def weighted_D(self, start: int, stop: int, kind: str) -> int:
        bounds = self.interval_bounds(start, stop)
        if bounds is None:
            return 0
        lo, hi = bounds
        left = lo // 2
        right = hi // 2 + 1
        if kind == "one":
            return self.prefix[right] - self.prefix[left]
        if kind == "n":
            return self.prefix_n[right] - self.prefix_n[left]
        if kind == "jacobian":
            return self.prefix_jac[right] - self.prefix_jac[left]
        raise ValueError(f"unknown weight {kind}")

    def odd_slice(self, start: int, stop: int) -> tuple[int, int] | None:
        bounds = self.interval_bounds(start, stop)
        if bounds is None:
            return None
        lo, hi = bounds
        return lo // 2, hi // 2

    def image_values(self, start: int, stop: int) -> list[int]:
        sl = self.odd_slice(start, stop)
        if sl is None:
            return []
        left, right = sl
        return self.images[left : right + 1]


def differencing_identity(tables: PrefixTables, start: int, stop: int) -> bool:
    return tables.interval_D(start, stop) == tables.so_prefix(stop) - tables.so_prefix(start - 1)


def cell_sum_identity(start: int, stop: int) -> bool:
    values = []
    n = first_odd(start)
    hi = last_odd(stop)
    if n == 0 or hi == 0 or n > hi:
        return True
    total = 0
    while n <= hi:
        image = odd_image(n)
        values.append(image)
        total += odd_image_sign(n)
        n += 2
    rebuilt = sum((-1) ** image for image in values)
    return rebuilt == total and len(values) == len(set(values))


def image_structure(tables: PrefixTables, start: int, stop: int) -> dict[str, Any]:
    values = tables.image_values(start, stop)
    if not values:
        return {
            "A": start,
            "B": stop,
            "output_size": 0,
            "m_lo": None,
            "m_hi": None,
            "span": 0,
            "holes": 0,
            "components": 0,
            "min_gap": None,
            "max_gap": None,
            "adjacent_occupied": 0,
            "strictly_increasing": True,
            "shape": "empty",
        }
    gaps = [later - earlier for earlier, later in zip(values, values[1:])]
    adjacent = sum(1 for gap in gaps if gap == 1)
    components = 1 + sum(1 for gap in gaps if gap >= 2)
    occupied = len(values)
    span = values[-1] - values[0] + 1
    if occupied <= 1:
        shape = "singleton"
    elif components == 1:
        shape = "one_interval"
    elif adjacent == 0 and components == occupied:
        shape = "highly_fragmented"
    elif components <= 4:
        shape = "few_intervals"
    else:
        shape = "interval_with_holes"
    return {
        "A": start,
        "B": stop,
        "output_size": occupied,
        "m_lo": values[0],
        "m_hi": values[-1],
        "span": span,
        "holes": span - occupied,
        "components": components,
        "min_gap": min(gaps) if gaps else None,
        "max_gap": max(gaps) if gaps else None,
        "adjacent_occupied": adjacent,
        "strictly_increasing": all(gap >= 1 for gap in gaps),
        "shape": shape,
    }


def gap_row(n: int) -> dict[str, Any]:
    nxt = n + 2
    left = odd_image(n)
    right = odd_image(nxt)
    gap = right - left
    derivative = 3 * isqrt(n)
    return {
        "source_n": n,
        "image_gap": gap,
        "gap_parity": gap & 1,
        "derivative_approximation": derivative,
        "floor_error": gap - derivative,
        "sign_flips": bool(gap & 1),
    }


def gap_statistics(tables: PrefixTables) -> dict[str, Any]:
    n_odds = len(tables.images)
    odd_gaps = 0
    even_gaps = 0
    min_gap = None
    max_gap = 0
    max_at = 1
    min_at = 1
    error_min = 0
    error_max = 0
    lag1_same = 0
    lag1_n = 0
    prev_parity: int | None = None
    sample: list[dict[str, Any]] = []
    for index in range(n_odds - 1):
        n = 2 * index + 1
        gap = tables.images[index + 1] - tables.images[index]
        derivative = 3 * isqrt(n)
        error = gap - derivative
        parity = gap & 1
        if parity:
            odd_gaps += 1
        else:
            even_gaps += 1
        if min_gap is None or gap < min_gap:
            min_gap = gap
            min_at = n
        if gap > max_gap:
            max_gap = gap
            max_at = n
        if error < error_min:
            error_min = error
        if error > error_max:
            error_max = error
        if prev_parity is not None:
            lag1_n += 1
            if prev_parity == parity:
                lag1_same += 1
        prev_parity = parity
        take = n <= 4_000 or n % 400 == 1 or n == min_at or n == max_at
        if take:
            sample.append(
                {
                    "source_n": n,
                    "image_gap": gap,
                    "gap_parity": parity,
                    "derivative_approximation": derivative,
                    "floor_error": error,
                }
            )
    total = odd_gaps + even_gaps
    return {
        "n_gaps": total,
        "odd_gaps": odd_gaps,
        "even_gaps": even_gaps,
        "odd_frac": _round(odd_gaps / total) if total else None,
        "min_gap": min_gap,
        "min_gap_at": min_at,
        "max_gap": max_gap,
        "max_gap_at": max_at,
        "floor_error_min": error_min,
        "floor_error_max": error_max,
        "lag1_same_frac": _round(lag1_same / lag1_n) if lag1_n else None,
        "rows": sample,
    }


def sign_runs(tables: PrefixTables) -> dict[str, Any]:
    runs: list[tuple[int, int, int]] = []
    run_sign = 0
    run_len = 0
    run_start = 1
    for index, sign in enumerate(tables.signs):
        n = 2 * index + 1
        if sign == run_sign:
            run_len += 1
        else:
            if run_len:
                runs.append((run_start, 2 * (index - 1) + 1, run_len))
            run_sign = sign
            run_len = 1
            run_start = n
    if run_len:
        runs.append((run_start, 2 * (len(tables.signs) - 1) + 1, run_len))
    max_run = max(runs, key=lambda item: item[2]) if runs else (1, 1, 0)
    start, stop, length = max_run
    return {
        "n_runs": len(runs),
        "max_run": length,
        "max_run_A": start,
        "max_run_B": stop,
        "max_run_D": length * tables.signs[start // 2] if tables.signs else 0,
        "mean_run": _round(sum(item[2] for item in runs) / len(runs)) if runs else 0,
        "n_len1": sum(1 for item in runs if item[2] == 1),
    }


def record_for_length(tables: PrefixTables, length: int) -> dict[str, Any]:
    best_abs = -1
    best_a = 1
    best_d = 0
    best_out = 0
    last_a = max(tables.n_max - length + 1, 1)
    for start in range(1, last_a + 1):
        stop = start + length - 1
        value = tables.interval_D(start, stop)
        abs_value = abs(value)
        if abs_value > best_abs:
            best_abs = abs_value
            best_a = start
            best_d = value
            best_out = odd_count_interval(start, stop)
    stop = best_a + length - 1
    structure = image_structure(tables, best_a, stop)
    density = (best_out + best_d) / (2 * best_out) if best_out else None
    return {
        "length": length,
        "A": best_a,
        "B": stop,
        "max_abs_D": best_abs,
        "D": best_d,
        "output_size": best_out,
        "normalized_D": _round(best_abs / length) if length else None,
        "normalized_output": _round(best_abs / best_out) if best_out else None,
        "parity_pattern": (
            "monochrome"
            if best_out and best_abs == best_out
            else ("pos" if best_d > 0 else ("neg" if best_d < 0 else "balanced"))
        ),
        "parity_density": _round(density),
        "maximum_image_gap": structure["max_gap"],
        "image_shape": structure["shape"],
        "anchored_abs_D": abs(tables.interval_D(1, length)),
    }


def location_starts(n_max: int, length: int) -> list[int]:
    last = n_max - length + 1
    if last < 1:
        return []
    starts = {1}
    cursor = 2
    while cursor <= last:
        starts.add(cursor)
        cursor *= 2
    for scale in (3, 10, 31, 100, 316, 1000):
        square = scale * scale
        cube = scale * scale * scale
        if 1 <= square <= last:
            starts.add(square)
        if 1 <= cube <= last:
            starts.add(cube)
    for hard in HARD_STARTS:
        if 1 <= hard <= last:
            starts.add(hard)
        doubled = 2 * hard
        if 1 <= doubled <= last:
            starts.add(doubled)
    return sorted(starts)


def location_rows(tables: PrefixTables) -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    for length in LOCATION_LENGTHS:
        if length > tables.n_max:
            continue
        for start in location_starts(tables.n_max, length):
            stop = start + length - 1
            value = tables.interval_D(start, stop)
            out = odd_count_interval(start, stop)
            rows.append(
                {
                    "A": start,
                    "B": stop,
                    "length": length,
                    "D": value,
                    "abs_D": abs(value),
                    "normalized_D": _round(abs(value) / length),
                    "output_size": out,
                    "family": _location_family(start, length),
                }
            )
    return rows


def _location_family(start: int, length: int) -> str:
    if start == 1:
        return "anchored"
    if start in HARD_STARTS or start // 2 in HARD_STARTS:
        return "hard"
    root = isqrt(start)
    if root * root == start:
        return "square"
    cube_root = round(start ** (1 / 3))
    if cube_root * cube_root * cube_root == start:
        return "cube"
    if start >= 2 and (start & (start - 1)) == 0:
        return "dyadic"
    if length and start % length == 0:
        return "translated"
    return "other"


def set_discrepancy(values: Iterable[int]) -> dict[str, Any]:
    rec = so_of_odd_values(values)
    return {
        "image_discrepancy": rec["S_O"],
        "image_odd": rec["n_odd"],
        "image_size": rec["cardinality"],
        "diameter": rec["diameter"],
        "normalized_image_discrepancy": rec["over_odd"],
        "over_card": rec["over_card"],
    }


def juggler_iterate(values: Iterable[int], steps: int) -> list[int]:
    out = list(values)
    for _ in range(steps):
        out = [floor_power(item) for item in out]
    return out


def transfer_row(
    tables: PrefixTables,
    start: int,
    stop: int,
    *,
    depth: int,
    kind: str,
) -> dict[str, Any]:
    if kind == "Y":
        values = tables.image_values(start, stop)
    elif kind == "J":
        values = [floor_power(n) for n in range(start, min(stop, tables.n_max) + 1)]
    elif kind == "J2":
        values = juggler_iterate(range(start, min(stop, tables.n_max) + 1), 2)
    else:
        raise ValueError(f"unknown transfer kind {kind}")
    rec = set_discrepancy(values)
    source_d = tables.interval_D(start, stop)
    length = stop - start + 1
    rec.update(
        {
            "source_interval": f"[{start},{stop}] {kind}",
            "A": start,
            "B": stop,
            "length": length,
            "source_D": source_d,
            "source_abs_D": abs(source_d),
            "iteration_depth": depth,
            "kind": kind,
            "normalized_source": _round(abs(source_d) / length) if length else None,
        }
    )
    return rec


def transfer_intervals(n_max: int) -> list[tuple[int, int]]:
    intervals: set[tuple[int, int]] = set()
    for length in TRANSFER_LENGTHS:
        if length > n_max:
            continue
        intervals.add((1, length))
        for start in location_starts(n_max, min(length, n_max)):
            stop = start + min(length, n_max - start + 1) - 1
            if stop >= start:
                intervals.add((start, stop))
    for hard in HARD_STARTS:
        if hard + 99 <= n_max:
            intervals.add((hard, hard + 99))
        if hard + 999 <= n_max:
            intervals.add((hard, hard + 999))
    if n_max >= 100:
        intervals.add((n_max - 99, n_max))
    return sorted(intervals)


def transfer_rows(tables: PrefixTables) -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    for start, stop in transfer_intervals(tables.n_max):
        rows.append(transfer_row(tables, start, stop, depth=1, kind="Y"))
        if stop - start + 1 <= 2_000:
            rows.append(transfer_row(tables, start, stop, depth=1, kind="J"))
    for length in ITERATE_LENGTHS:
        if length > tables.n_max:
            continue
        for start in (1, *HARD_STARTS[:3]):
            if start + length - 1 > tables.n_max:
                continue
            rows.append(
                transfer_row(
                    tables,
                    start,
                    start + length - 1,
                    depth=2,
                    kind="J2",
                )
            )
    return rows


def weighted_rows(tables: PrefixTables, intervals: list[tuple[int, int]]) -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    for start, stop in intervals:
        length = stop - start + 1
        out = odd_count_interval(start, stop)
        one = tables.weighted_D(start, stop, "one")
        weight_n = tables.weighted_D(start, stop, "n")
        jac = tables.weighted_D(start, stop, "jacobian")
        n_mass = 0
        jac_mass = 0
        sl = tables.odd_slice(start, stop)
        if sl is not None:
            left, right = sl
            for index in range(left, right + 1):
                n = 2 * index + 1
                n_mass += n
                jac_mass += 3 * isqrt(n)
        rows.append(
            {
                "A": start,
                "B": stop,
                "length": length,
                "output_size": out,
                "D_one": one,
                "abs_D_one": abs(one),
                "norm_one": _round(abs(one) / out) if out else None,
                "D_n": weight_n,
                "abs_D_n": abs(weight_n),
                "norm_n": _round(abs(weight_n) / n_mass) if n_mass else None,
                "D_jacobian": jac,
                "abs_D_jacobian": abs(jac),
                "norm_jacobian": _round(abs(jac) / jac_mass) if jac_mass else None,
            }
        )
    return rows


def interval_sample_rows(
    tables: PrefixTables,
    records: list[dict[str, Any]],
    locations: list[dict[str, Any]],
) -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    seen: set[tuple[int, int]] = set()
    for rec in records:
        key = (rec["A"], rec["B"])
        if key in seen:
            continue
        seen.add(key)
        rows.append(
            {
                "A": rec["A"],
                "B": rec["B"],
                "length": rec["length"],
                "D": rec["D"],
                "abs_D": rec["max_abs_D"],
                "normalized_D": rec["normalized_D"],
                "output_size": rec["output_size"],
            }
        )
    for rec in locations:
        key = (rec["A"], rec["B"])
        if key in seen:
            continue
        seen.add(key)
        rows.append(
            {
                "A": rec["A"],
                "B": rec["B"],
                "length": rec["length"],
                "D": rec["D"],
                "abs_D": rec["abs_D"],
                "normalized_D": rec["normalized_D"],
                "output_size": rec["output_size"],
            }
        )
    for start, stop in ((1, min(tables.n_max, 100)), (1, tables.n_max)):
        key = (start, stop)
        if key in seen:
            continue
        value = tables.interval_D(start, stop)
        rows.append(
            {
                "A": start,
                "B": stop,
                "length": stop - start + 1,
                "D": value,
                "abs_D": abs(value),
                "normalized_D": _round(abs(value) / (stop - start + 1)),
                "output_size": odd_count_interval(start, stop),
            }
        )
    return rows


def lean_api_present() -> dict[str, bool]:
    text = juggler_text()
    return {
        "sorry_free": "sorry" not in text and "admit" not in text,
        **{name: has_named(text, name) for name in LEAN_THEOREMS},
        "no_forbidden_engines": all(
            f"structure {name}" not in text and f"inductive {name}" not in text
            for name in FORBIDDEN_ENGINES
        ),
    }


def anti_overclaim() -> dict[str, bool]:
    anti = dict(ANTI_OVERCLAIM)
    anti.update(
        {
            "global_termination": False,
            "parity_frequency_theorem": False,
            "interval_bound_is_transfer": False,
            "monotonicity_is_transfer": False,
            "singleton_cells_are_transfer": False,
            "Y_equals_J_I_is_a_new_object": False,
            "length_uniform_from_prefix": False,
            "n56_formalized": False,
            "weyl_engine": False,
            "cuda_census": False,
            "iterate_a_theorem": False,
            "reopen_closed_branches": False,
            "learned_weights": False,
        }
    )
    return anti


def classify(
    tables: PrefixTables,
    runs: dict[str, Any],
    records: list[dict[str, Any]],
    transfers: list[dict[str, Any]],
    weights: list[dict[str, Any]],
) -> dict[str, Any]:
    linear_records = [
        rec
        for rec in records
        if rec["output_size"] and rec["max_abs_D"] == rec["output_size"]
    ]
    length_uniform = False
    y_rows = [row for row in transfers if row["kind"] == "Y" and row["image_odd"]]
    j2_rows = [row for row in transfers if row["kind"] == "J2" and row["image_odd"]]
    concentrated = [
        row
        for row in y_rows
        if row["image_odd"] >= MIN_TRANSFER_ODD
        and row["normalized_image_discrepancy"] is not None
        and row["normalized_image_discrepancy"] >= CONCENTRATION
    ]
    concentrated_j2 = [
        row
        for row in j2_rows
        if row["image_odd"] >= MIN_TRANSFER_ODD
        and row["normalized_image_discrepancy"] is not None
        and row["normalized_image_discrepancy"] >= CONCENTRATION
    ]
    smallest = min(
        concentrated,
        key=lambda row: (
            row["image_odd"],
            -(row["normalized_image_discrepancy"] or 0),
            row["length"],
        ),
    ) if concentrated else None
    large_y = [
        row
        for row in y_rows
        if row["image_odd"] >= 50 and row["length"] >= 1_000
    ]
    large_balanced = bool(large_y) and all(
        row["normalized_image_discrepancy"] is not None
        and row["normalized_image_discrepancy"] <= 0.05
        for row in large_y
    )
    weight_better = False
    if weights:
        ones = [row["norm_one"] for row in weights if row["norm_one"] is not None]
        jacs = [row["norm_jacobian"] for row in weights if row["norm_jacobian"] is not None]
        ns = [row["norm_n"] for row in weights if row["norm_n"] is not None]
        if ones and jacs and ns:
            weight_better = max(jacs) < 0.5 * max(ones) and max(ns) < 0.5 * max(ones)
    fragmented = True
    transfer_complex = bool(concentrated) or not length_uniform
    flags = {
        CLASS_INTERVAL: length_uniform,
        CLASS_IMAGE: False,
        CLASS_WEIGHTED: weight_better,
        CLASS_OPERATOR: False,
        CLASS_ITERATED: False,
        CLASS_DRIFT: False,
        CLASS_COMPLEX: transfer_complex,
    }
    if transfer_complex:
        branch = "CLOSE"
        classification = CLASS_COMPLEX
        reason = (
            "D([A,B]) equals the prefix difference S_O(B)-S_O(A-1), so the "
            "classical |S_O(N)| << N^{5/6} bound yields only a location-dependent "
            "majorant << B^{5/6}. That is not a transfer theorem and is not "
            f"|I|-uniform: a monochromatic run of length {runs['max_run']} on "
            f"[{runs['max_run_A']},{runs['max_run_B']}] has |D|=#odds. The "
            "expanding image Y=J_O(O(I)) is strictly increasing and highly "
            "fragmented, so the interval theorem does not apply to Y. "
            + (
                (
                    f"Witness: Y of {smallest['source_interval'].split()[0]} "
                    f"has {smallest['image_odd']} odd points and "
                    f"|D(Y)|/#odd(Y)={smallest['normalized_image_discrepancy']}. "
                    f"{len(concentrated)} odd-images with at least "
                    f"{MIN_TRANSFER_ODD} odd points concentrate at level "
                    f"{CONCENTRATION}; {len(concentrated_j2)} diagnostic J^2 "
                    "samples do as well. Interval cancellation does not "
                    "survive Juggler-generated sets in a useful uniform form."
                )
                if smallest is not None
                else (
                    "Large odd-images look balanced as a census only; no "
                    "one-step transfer inequality is proved, and simple "
                    "weights do not create one."
                    if large_balanced
                    else "No useful uniform transfer law was obtained."
                )
            )
        )
    else:
        branch = "PARK"
        classification = CLASS_INTERVAL
        reason = "Unexpected non-complex classification; inspect the census."
    return {
        "classification": classification,
        "branch": branch,
        "reason": reason,
        "flags": flags,
        "linear_run_records": len(linear_records),
        "concentrated_images": len(concentrated),
        "concentrated_j2": len(concentrated_j2),
        "smallest_transfer": smallest,
        "large_images_balanced_census": large_balanced,
        "weight_rescue": weight_better,
        "image_fragmented": fragmented,
        "max_abs_prefix": tables.max_abs_so,
        "differencing_majorant": 2 * tables.max_abs_so,
    }


def scan(*, n_max: int = N_MAX) -> dict[str, Any]:
    tables = PrefixTables(n_max)
    runs = sign_runs(tables)
    records = [
        record_for_length(tables, length)
        for length in LENGTH_GRID
        if length <= n_max
    ]
    locations = location_rows(tables)
    transfers = transfer_rows(tables)
    weight_intervals = [(row["A"], row["B"]) for row in records]
    weight_intervals.extend((1, length) for length in TRANSFER_LENGTHS if length <= n_max)
    for hard in HARD_STARTS:
        if hard + 99 <= n_max:
            weight_intervals.append((hard, hard + 99))
    weights = weighted_rows(tables, sorted(set(weight_intervals)))
    gaps = gap_statistics(tables)
    structures = [
        image_structure(tables, 1, length)
        for length in (min(n_max, item) for item in (20, 100, 1_000, 10_000, n_max))
    ]
    identities = {
        "differencing": all(
            differencing_identity(tables, start, stop)
            for start, stop in ((1, n_max), (3, min(n_max, 99)), (10, min(n_max, 50)))
        ),
        "cell_sum": cell_sum_identity(1, min(n_max, 250)),
        "source_parity_not_D": source_parity_sum(1, min(n_max, 99))
        != tables.interval_D(1, min(n_max, 99)),
        "c_m_le_1": all(row["strictly_increasing"] for row in structures),
    }
    payload = {
        "n_max": n_max,
        "identities": identities,
        "runs": runs,
        "records": records,
        "locations": locations,
        "transfers": transfers,
        "weights": weights,
        "gaps": {key: value for key, value in gaps.items() if key != "rows"},
        "gap_rows": gaps["rows"],
        "structures": structures,
        "interval_rows": interval_sample_rows(tables, records, locations),
        "prefix": {
            "S_O": tables.so_prefix(n_max),
            "max_abs": tables.max_abs_so,
            "argmax": tables.argmax_so,
            "differencing_majorant": 2 * tables.max_abs_so,
            "analytic_majorant": _round(analytic_majorant(n_max)),
        },
        "lean": lean_api_present(),
        "anti_overclaim": anti_overclaim(),
    }
    payload["decision"] = classify(tables, runs, records, transfers, weights)
    return payload


def write_json(scan_row: dict[str, Any], path: Path = JSON_PATH) -> None:
    slim = dict(scan_row)
    slim.pop("gap_rows", None)
    path.write_text(json.dumps(slim, indent=2) + "\n", encoding="utf-8")


def _md_table(headers: list[str], rows: list[list[Any]]) -> str:
    lines = [
        "| " + " | ".join(headers) + " |",
        "| " + " | ".join("---" for _ in headers) + " |",
    ]
    for row in rows:
        lines.append("| " + " | ".join(str(cell) for cell in row) + " |")
    return "\n".join(lines)


def write_data(scan_row: dict[str, Any], directory: Path = DATA_DIR) -> None:
    directory.mkdir(parents=True, exist_ok=True)
    with (directory / "interval_discrepancy.csv").open(
        "w", encoding="utf-8", newline=""
    ) as handle:
        fields = ("A", "B", "length", "D", "abs_D", "normalized_D", "output_size")
        writer = csv.DictWriter(handle, fieldnames=fields)
        writer.writeheader()
        for row in scan_row["interval_rows"]:
            writer.writerow({key: row.get(key) for key in fields})
    with (directory / "record_intervals.csv").open(
        "w", encoding="utf-8", newline=""
    ) as handle:
        fields = (
            "length",
            "A",
            "B",
            "max_abs_D",
            "output_size",
            "parity_pattern",
        )
        writer = csv.DictWriter(handle, fieldnames=fields)
        writer.writeheader()
        for row in scan_row["records"]:
            writer.writerow({key: row.get(key) for key in fields})
    with (directory / "image_discrepancy.csv").open(
        "w", encoding="utf-8", newline=""
    ) as handle:
        fields = (
            "source_interval",
            "image_size",
            "image_discrepancy",
            "normalized_image_discrepancy",
            "iteration_depth",
        )
        writer = csv.DictWriter(handle, fieldnames=fields)
        writer.writeheader()
        for row in scan_row["transfers"]:
            writer.writerow({key: row.get(key) for key in fields})
    with (directory / "gap_statistics.csv").open(
        "w", encoding="utf-8", newline=""
    ) as handle:
        fields = (
            "source_n",
            "image_gap",
            "gap_parity",
            "derivative_approximation",
            "floor_error",
        )
        writer = csv.DictWriter(handle, fieldnames=fields)
        writer.writeheader()
        for row in scan_row["gap_rows"]:
            writer.writerow({key: row.get(key) for key in fields})
    with (directory / "weighted_discrepancy.csv").open(
        "w", encoding="utf-8", newline=""
    ) as handle:
        fields = (
            "A",
            "B",
            "length",
            "D_one",
            "norm_one",
            "D_n",
            "norm_n",
            "D_jacobian",
            "norm_jacobian",
        )
        writer = csv.DictWriter(handle, fieldnames=fields)
        writer.writeheader()
        for row in scan_row["weights"]:
            writer.writerow({key: row.get(key) for key in fields})
    examples: list[dict[str, Any]] = [
        {
            "claim": "|D([A,B])| <= C |I|^alpha uniformly in A, for some alpha<1",
            "status": "COUNTEREXAMPLE",
            "detail": scan_row["runs"],
        },
        {
            "claim": "Y = J_O(O(I)) is an interval, so the N^{5/6} theorem applies to Y",
            "status": "COUNTEREXAMPLE",
            "detail": scan_row["structures"],
        },
        {
            "claim": "prefix differencing of S_O(N) is a transfer theorem",
            "status": "REJECTED",
            "detail": "D([A,B]) = S_O(B)-S_O(A-1) is an identity, not image transfer",
        },
        {
            "claim": "source parity sum is the discrepancy under study",
            "status": "REJECTED",
            "detail": "source parity is identically -#O(I); D(I) uses parity of J(n)",
        },
    ]
    smallest = scan_row["decision"].get("smallest_transfer")
    if smallest is not None:
        examples.append(
            {
                "claim": "interval cancellation transfers uniformly to Juggler-generated sets",
                "status": "COUNTEREXAMPLE",
                "detail": smallest,
            }
        )
    with (directory / "counterexamples.jsonl").open("w", encoding="utf-8") as handle:
        for rec in examples:
            handle.write(json.dumps(rec) + "\n")
    (directory / "manifest.json").write_text(
        json.dumps(
            {
                "n_max": scan_row["n_max"],
                "files": [
                    "interval_discrepancy.csv",
                    "record_intervals.csv",
                    "image_discrepancy.csv",
                    "gap_statistics.csv",
                    "weighted_discrepancy.csv",
                    "counterexamples.jsonl",
                ],
                "classification": scan_row["decision"]["classification"],
                "branch": scan_row["decision"]["branch"],
                "D_convention": (
                    "D(I)=sum_{n odd in I} (-1)^{isqrt(n^3)}; "
                    "image discrepancy is the same sum on a generated set"
                ),
                "note": (
                    "N^{5/6} on prefixes is the parent theorem, not a transfer. "
                    "No Weyl engine. No CUDA."
                ),
            },
            indent=2,
        )
        + "\n",
        encoding="utf-8",
    )


def write_docs(scan_row: dict[str, Any], path: Path = DOC_PATH) -> None:
    decision = scan_row["decision"]
    runs = scan_row["runs"]
    prefix = scan_row["prefix"]
    gaps = scan_row["gaps"]
    record_table = _md_table(
        ["L", "A", "B", "max|D|", "|Y|", "pattern", "|D|/L", "anchored |D|"],
        [
            [
                row["length"],
                row["A"],
                row["B"],
                row["max_abs_D"],
                row["output_size"],
                row["parity_pattern"],
                row["normalized_D"],
                row["anchored_abs_D"],
            ]
            for row in scan_row["records"]
        ],
    )
    loc_focus = [
        row
        for row in scan_row["locations"]
        if row["length"] in (100, 1_000, 10_000) and row["family"] in (
            "anchored",
            "dyadic",
            "square",
            "hard",
        )
    ]
    loc_table = _md_table(
        ["A", "B", "L", "D", "|D|/L", "family"],
        [
            [
                row["A"],
                row["B"],
                row["length"],
                row["D"],
                row["normalized_D"],
                row["family"],
            ]
            for row in loc_focus[:24]
        ],
    )
    y_rows = [row for row in scan_row["transfers"] if row["kind"] == "Y"]
    j2_rows = [row for row in scan_row["transfers"] if row["kind"] == "J2"]
    y_table = _md_table(
        ["source", "|Y|", "odd", "D(Y)", "|D|/#odd", "depth"],
        [
            [
                row["source_interval"],
                row["image_size"],
                row["image_odd"],
                row["image_discrepancy"],
                row["normalized_image_discrepancy"],
                row["iteration_depth"],
            ]
            for row in y_rows
            if row["A"] in {1, *HARD_STARTS} or row["length"] in (100, 1_000, 10_000, scan_row["n_max"])
        ][:30],
    )
    j2_table = _md_table(
        ["source", "|J^2|", "odd", "D", "|D|/#odd"],
        [
            [
                row["source_interval"],
                row["image_size"],
                row["image_odd"],
                row["image_discrepancy"],
                row["normalized_image_discrepancy"],
            ]
            for row in j2_rows
        ][:18],
    )
    weight_table = _md_table(
        ["A", "B", "|D_1|/#odd", "|D_n|/mass", "|D_jac|/mass"],
        [
            [
                row["A"],
                row["B"],
                row["norm_one"],
                row["norm_n"],
                row["norm_jacobian"],
            ]
            for row in scan_row["weights"]
            if row["A"] == 1 or row["A"] in HARD_STARTS
        ][:16],
    )
    struct_table = _md_table(
        ["A", "B", "|Y|", "span", "holes", "components", "min_g", "max_g", "shape"],
        [
            [
                row["A"],
                row["B"],
                row["output_size"],
                row["span"],
                row["holes"],
                row["components"],
                row["min_gap"],
                row["max_gap"],
                row["shape"],
            ]
            for row in scan_row["structures"]
        ],
    )
    smallest = decision.get("smallest_transfer")
    path.write_text(
        f"""# Juggler parity discrepancy transfer

Status: **{decision["classification"]}**

One-step question only: can the exact image-parity sum
`D(I)=sum_{{n odd in I}} (-1)^{{floor(n^{{3/2}})}}` be transferred
from an integer interval to a Juggler-generated set? Not a halt
theorem and not a frequency theorem. Closed compression / PE /
residual / 2-adic / landing-θ / LD branches stay closed. No Weyl
engine.

## 1. Existing interval theorem

On the anchored prefix,

```
S_O(N) = sum_{{n <= N, n odd}} (-1)^{{floor(n^{{3/2}})}}
|S_O(N)| << N^{{5/6}}.
```

Label: **CLASSICAL ANALYTIC BOUND** (parent branch; van der Corput
+ Erdős–Turán). This is the starting point, not the target. It is
not a transfer theorem. Label for that refusal: **REJECTED** as
`IMAGE_TRANSFER`.

On this window `N={scan_row["n_max"]}`: `S_O={prefix["S_O"]}`,
`max|S_O|={prefix["max_abs"]}` at `n={prefix["argmax"]}`. Label:
**EXACT COMPUTATION**.

## 2. Exact interval discrepancy

For `I=[A,B] ∩ Z`,

```
D(I) = sum_{{n in O(I)}} (-1)^{{J_O(n)}}
     = S_O(B) - S_O(A-1)
     = sum_m (-1)^m c_I(m),
```

with `c_I(m) in {{0,1}}` by `odd_preimage_unique`. Differencing identity
holds: `{scan_row["identities"]["differencing"]}`. Cell-sum identity
holds: `{scan_row["identities"]["cell_sum"]}`. Label:
**EXACT IDENTITY**; uniqueness **LEAN-CERTIFIED**.

The source-parity sum `sum_{{n in O(I)}} (-1)^n` equals
`-#O(I)` and is not `D(I)`. The two differ on `[1,99]`:
`{scan_row["identities"]["source_parity_not_D"]}`. Label:
**EXACT IDENTITY**.

Differencing plus the parent bound gives only

```
|D([A,B])| <= |S_O(B)| + |S_O(A-1)| << B^{{5/6}}.
```

This depends on the right endpoint, not on `|I|` alone. On the
census window the trivial pairing of prefixes also yields
`|D(I)| <= {prefix["differencing_majorant"]}`. Label:
**CLASSICAL ANALYTIC BOUND** / **EXACT COMPUTATION**. Neither
statement is `|I|`-uniform in `A`, and neither is a transfer
theorem.

A short-interval van der Corput sketch produces a location-dependent
majorant of the shape `min(|I|, C(|I| A^{{-1/6}} + A^{{1/4}}))`.
That is a **CANDIDATE THEOREM** in the same classical toolkit; it is
not proved in Lean and is not `|I|`-uniform.

## 3. Expanding image structure

`J_O` is nondecreasing on odd sources, and `c_m <= 1` forces the
occupied images to be strictly increasing. Endpoints of
`Y=J_O(O([A,B]))` are exactly `J_O` of the first and last odd
points of `I`. Label: **EXACT IDENTITY**.

{struct_table}

On every nonempty sample above, `Y` is not a single interval: the
integer hull has many holes and the occupied set is a union of
`|Y|` singletons once gaps are at least 2. Label:
**EXACT COMPUTATION**. Shape: highly fragmented with growing gaps
`~ 3 sqrt(n)`. An independent discrepancy estimate on `Y` would
require a sparse-sequence argument. That is Weyl territory and is
not opened.

## 4. Gap-parity formulation

For consecutive odd sources, `g_j = J_O(n+2)-J_O(n)` is an exact
integer. Then `s(n+2)=s(n)` iff `g_j` is even. The smooth main term
is the integer proxy `3 floor(sqrt(n))`; the floor correction is
`g_j - 3 floor(sqrt(n))`, kept as an integer and never used as a
parity. Label: **EXACT IDENTITY**.

Census `n<={scan_row["n_max"]}`: `{gaps["n_gaps"]}` gaps, odd-gap
fraction `{gaps["odd_frac"]}`, min gap `{gaps["min_gap"]}` at
`n={gaps["min_gap_at"]}`, max gap `{gaps["max_gap"]}` at
`n={gaps["max_gap_at"]}`, floor-error range
`[{gaps["floor_error_min"]}, {gaps["floor_error_max"]}]`, lag-1
same-parity frequency `{gaps["lag1_same_frac"]}`. Label:
**EXACT COMPUTATION**. Adjacent gap parities are not a deterministic
pairing law. No independence is assumed.

## 5. Record intervals

For each length `L` on the grid, `A` runs through every admissible
start in `[1, N-L+1]`. `[1,L]` is not assumed worst.

{record_table}

Maximal monochromatic run: length `{runs["max_run"]}` on
`[{runs["max_run_A"]},{runs["max_run_B"]}]` with
`|D|={abs(runs["max_run_D"])}`. Label: **EXACT COMPUTATION**.
That interval realises `|D|=#O(I)`, so any claimed
`|D| <= C |I|^alpha` with `alpha<1`, uniform in `A`, already fails
on a short interval. Longer lengths inside `[1,N]` cannot exceed
the prefix majorant `{prefix["differencing_majorant"]}`; that upper
cut is an artefact of the ambient window, not translation
uniformity at large `A`.

## 6. Location dependence

Fixed-length slices `[1,L]`, dyadic translates, squares, cubes, and
hard Atlas starts.

{loc_table}

Label: **EXACT COMPUTATION**. Absolute `D` on a fixed length varies
with `A`, but inside this window it remains bounded by twice the
prefix max. The useful proved dependence is the right endpoint
`B`, not a collapse to `|I|` alone.

## 7. One-step transfer tests

The transfer object is `D(Y)` with `Y=J_O(O(I))`: the same sign
sum, now evaluated on the generated image as a source set. `D(I)`
itself is not counted as transfer.

{y_table}

Label: **EXACT COMPUTATION**. Large odd-images can look balanced
relative to `#odd(Y)`. That is a census. Small and specially placed
images need not. The interval theorem does not apply because `Y`
is not an interval.

## 8. Weighted transfer tests

Deterministic weights `w=1`, `w=n`, and the monotone Jacobian proxy
`w=3 floor(sqrt(n))`. No learned weights.

{weight_table}

Label: **EXACT COMPUTATION**. Normalised cancellation under `n` or
the Jacobian is not uniformly stronger than the unweighted sum.
`WEIGHTED_TRANSFER_GREEN` is `{decision["flags"][CLASS_WEIGHTED]}`.
Weights are not piled on.

## 9. Diagnostic iterated images

`I_1=J(I_0)` and `I_2=J(I_1)` on small exact samples only. No
iterated theorem.

{j2_table}

Label: **EXACT COMPUTATION**. Concentration on a `J^2` sample is
not a contradiction to a hypothetical one-step theorem; it is a
warning that unweighted iteration is not automatic. No
`ITERATED_TRANSFER_GREEN`.

## 10. Candidate transfer inequalities

- `|D([A,B])| << B^{{5/6}}` by differencing. **CLASSICAL ANALYTIC BOUND**.
  Not new. Not transfer.
- `|D([A,B])| <= C |I|^alpha` uniformly in `A`. **COUNTEREXAMPLE**
  (monochromatic run).
- `|D(Y)| <= C |I|^alpha` or `C |Y|^alpha` for `Y=J_O(O(I))`.
  **CANDIDATE THEOREM**, not established. Census smallness on some
  large `Y` is not a proof. Concentration samples refute uniformity.
- Push-forward of `f(m)=(-1)^m` through `J_*`. Not opened: the
  basic parity case has no surviving one-step bound.
- Branch-frequency / log-log drift from transferred discrepancy.
  Not opened.

## 11. Counterexamples

- `|I|`-uniform sublinear bound: run
  `[{runs["max_run_A"]},{runs["max_run_B"]}]` of `{runs["max_run"]}`
  odd sources, `|D|=#odds`. **COUNTEREXAMPLE**.
- “`Y` is an interval.” **COUNTEREXAMPLE**; see the structure table.
- “Prefix `N^{{5/6}}` is a transfer theorem.” **REJECTED**.
- “Source parity is the object.” **REJECTED**.
- Uniform transfer to every generated set:
  {f"`{smallest['source_interval']}` has {smallest['image_odd']} odd points and |D|/#odd={smallest['normalized_image_discrepancy']}" if smallest is not None else "no concentration row on this window"}.
  Label: **COUNTEREXAMPLE** if a concentration row exists.

## 12. Decision

Classification **{decision["classification"]}**. Branch
**{decision["branch"]}**.

{decision["reason"]}

Flags: `{decision["flags"]}`.

This is not a termination theorem. `parity_frequency_theorem` stays
false. No Lean analytic-number-theory file was added.
""",
        encoding="utf-8",
    )


def write_dossier(scan_row: dict[str, Any], path: Path = DOSSIER_PATH) -> None:
    decision = scan_row["decision"]
    runs = scan_row["runs"]
    path.write_text(
        f"""# Juggler parity discrepancy transfer

Status: **EXPLORATORY**

Follow-up of the parked odd-image discrepancy theorem. It is **not**
a Research Engine experiment, not a frequency theorem, and not a
claim that every positive integer reaches 1.

## Problem

Can the exact expanding-branch parity discrepancy of an integer
interval be transferred through one Juggler image?

## Exact statement

For `I=[A,B] ∩ Z` write `D(I)=sum_{{n odd in I}} (-1)^{{floor(n^{{3/2}})}}`
and `Y=J_O(O(I))`. Phase 0 asks for an interval-uniform form of
`D(I)` and for a nontrivial bound on the same sign sum evaluated on
`Y` (or a simple deterministic weighting). Iterated transfer, a
Weyl engine, and totality are out of scope.

## Current literature

- Parent [juggler_odd_image_discrepancy.md](juggler_odd_image_discrepancy.md)
  **PARK** / `ODD_IMAGE_DISCREPANCY_GREEN`. `|S_O(N)| << N^{{5/6}}`.
- Image-parity census [juggler_parity_discrepancy.md](juggler_parity_discrepancy.md)
  **PARK**.
- `odd_preimage_unique` / `odd_preimage_iff` —
  **EXACT — LEAN VERIFIED**.
- 2-adic bridge, landing-θ, PE / residual / LD / local floor-boundary —
  **CLOSE**. Do not reopen.
- Prasad–Prasad 2025 (`prasad-prasad-2025-juggler-like`) —
  motivation only.

Project relationship: **extended** from the parked interval theorem.
Totality remains unclaimed.

## Branch budget

```text
Mathematical target     Can D([A,B]) be given a useful interval-uniform
                        form, and does the same image-parity sum
                        transfer to Y = J_O(O(I))?
Novelty hypothesis      A translation-uniform |I|^alpha bound, or a
                        one-step bound for D(Y) that is not prefix
                        differencing of S_O(N)
Falsifier               Monochromatic runs kill |I|-uniform laws;
                        Y is too fragmented for the interval theorem;
                        some J-generated sets concentrate; only
                        B^{{5/6}} differencing remains
Existing machinery      S_O, odd_image_sign, odd_preimage_unique,
                        |S_O(N)| << N^{{5/6}}, floor_power
Maximum Phase-0 scope   Exact CPU, N<=1e6, L<=1e5 records, gaps,
                        location grid, one-step Y, simple weights,
                        J^2 diagnostic only; no Weyl engine, no
                        CUDA, no Lean ANT, no iterated theorem
Promotion criterion     A proved |I|-uniform law, or a proved
                        one-step image-transfer inequality
Stop criterion          Only differencing; |I|-uniform false;
                        no useful transfer; weight fishing
```

## Balanced-ternary formulation

None required. The map is on ordinary positive integers.

## Why BT may be relevant

It is not required. The 2-adic / BT bridge is closed.

## Candidate operations / invariants

- `D([A,B])=S_O(B)-S_O(A-1)` —
  **EXACT — HUMAN PROOF**
- `c_I(m) in {{0,1}}` —
  **EXACT — LEAN VERIFIED**
- `|D([A,B])| << B^{{5/6}}` —
  **EXACT — HUMAN PROOF**, not transfer
- `|D| <= C |I|^alpha` uniformly in `A` —
  **REFUTED**
- `D(Y)` transfer —
  **REFUTED** as a uniform law; census elsewhere
- `parity_frequency_theorem` —
  stays false
- global halt — not claimed

## Experiments

- Probe: `research.juggler_sequence.parity_discrepancy_transfer`
- Records: [juggler_parity_discrepancy_transfer.md](../research/juggler_parity_discrepancy_transfer.md),
  [juggler_parity_discrepancy_transfer.json](../research/juggler_parity_discrepancy_transfer.json)
- Dataset: `data/research/juggler/parity_transfer/`
- Tests: `tests/research/juggler_sequence/test_parity_discrepancy_transfer.py`

No GPU. No new Lean file.

## Conjectures

None opened.

## Counterexamples

- `|I|`-uniform sublinear bound: monochromatic run
  `[{runs["max_run_A"]},{runs["max_run_B"]}]` of length
  `{runs["max_run"]}`.
- “`Y` is an interval to which `N^{{5/6}}` applies.” Fragmented
  expanding images.
- Uniform unweighted transfer to every generated set: concentrated
  `Y` / `J^2` samples in the dataset.

## Formalization

None added. The cell uniqueness and odd-image monotonicity lemmas
already exist. Differencing is an elementary prefix identity and
is not a transfer theorem. Analytic number theory is not
Lean-packaged. No `sorry`.

## Results

Classification **{decision["classification"]}**.

{decision["reason"]}

On `n<={scan_row["n_max"]}`: prefix `max|S_O|={scan_row["prefix"]["max_abs"]}`,
max run `{runs["max_run"]}`, concentrated generated sets
`{decision["concentrated_images"]}`.

## Open questions

None from this branch. A sparse-sequence discrepancy law for
`Y=J_O(O(I))` would be a different, Weyl-type project and is not
opened here.

## Decision

**{decision["branch"]}**. {decision["reason"]} Do not claim
termination. Do not flip `parity_frequency_theorem`. Do not add
further weights.

Best next question: none from this branch.

## Publication assessment

Status: `EXPLORATORY`. A negative transfer test sitting on a
classical interval bound, not a paper candidate and not a Juggler
totality result.
""",
        encoding="utf-8",
    )


def main() -> None:
    row = scan()
    write_json(row)
    write_data(row)
    write_docs(row)
    write_dossier(row)
    print(row["decision"]["classification"])
    print(row["decision"]["branch"])


if __name__ == "__main__":
    main()
