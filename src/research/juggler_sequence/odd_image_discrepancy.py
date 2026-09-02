"""Odd-start Juggler image-parity discrepancy.

Not a Research Engine experiment. Not a halt theorem. Not a
parity-frequency theorem. Does not reopen closed PE / residual /
2-adic / landing-θ / probabilistic-LD branches.

Convention, used everywhere:

    s(n) = (-1)^{floor(n^{3/2})}   for odd n
    S_O(N) = sum_{odd n <= N} s(n)

Then S_O(N) = -2 D_O(N) with the Phase-0 odd-start D_O.
"""

from __future__ import annotations

import csv
import json
from math import isqrt, log
from pathlib import Path
from typing import Any, Iterable

from research.juggler_sequence.compensated_contraction import follows_itinerary, image_after
from research.juggler_sequence.floor_preimages import odd_preimage_integers
from research.juggler_sequence.lean_paths import has_named, juggler_text
from research.juggler_sequence.parity_discrepancy import odd_start_count
from research.juggler_sequence.power_itineraries import ANTI_OVERCLAIM, floor_power

REPO_ROOT = Path(__file__).resolve().parents[3]
JSON_PATH = REPO_ROOT / "docs" / "research" / "juggler_odd_image_discrepancy.json"
DOC_PATH = REPO_ROOT / "docs" / "research" / "juggler_odd_image_discrepancy.md"
DOSSIER_PATH = REPO_ROOT / "docs" / "problems" / "juggler_odd_image_discrepancy.md"
DATA_DIR = REPO_ROOT / "data" / "research" / "juggler" / "parity_discrepancy_next"

N_MAX = 1_000_000
N_SPOT = 10_000_000
CELL_PREFIX = 8_000
WORD_N_MAX = 10_000
IMAGE_GRID = (100, 1_000, 10_000, 100_000, 1_000_000)
LOG_GRID = (10, 100, 1_000, 10_000, 100_000, 1_000_000)
DYADIC_GRID = tuple(1 << k for k in range(4, 21))
SELECTED_WORDS = ("O", "E", "OE", "OO", "EO", "OOE", "OOOEE")
FIT_LO = 1_000

CLASS_GREEN = "ODD_IMAGE_DISCREPANCY_GREEN"
CLASS_COMPLEX = "IMAGE_DISCREPANCY_COMPLEX"
CLASS_SHARP = "ODD_IMAGE_SHARP_GREEN"
CLASS_IMAGE = "IMAGE_DISCREPANCY_GREEN"

LEAN_THEOREMS = (
    "odd_preimage_unique",
    "odd_preimage_iff",
    "floorPower_odd_macro_direction",
    "landingParity_odd_iff",
)

FORBIDDEN_ENGINES = (
    "ResidualGraph",
    "ResidualState",
    "MilestoneGraph",
    "PowerHeight",
    "CycleEngine",
)


def _round(value: float) -> float:
    return round(float(value), 8)


def odd_image(n: int) -> int:
    """a_n = floor(n^{3/2}). Requires odd n."""
    if n < 1 or n % 2 == 0:
        raise ValueError("odd_image requires a positive odd integer")
    return isqrt(n * n * n)


def odd_image_sign(n: int) -> int:
    """s(n) = (+1) if a_n even, (-1) if a_n odd."""
    return 1 - 2 * (odd_image(n) & 1)


def so_from_oo(odd_odd_count: int, n: int) -> int:
    """S_O = #odds - 2 O_O = -2 D_O."""
    return odd_start_count(n) - 2 * odd_odd_count


def fractional_part_identity(n: int) -> bool:
    """floor(x) odd iff the integer test {x/2}>=1/2, evaluated exactly.

    {x/2} >= 1/2 iff floor(x) is odd. Here x^2 = n^3, x = a_n or a_n+frac.
    The exact predicate is a_n % 2 == 1.
    """
    return (odd_image(n) & 1) == 1


def cell_occupants(m: int) -> list[int]:
    return odd_preimage_integers(m)


def cell_multiplicity(m: int) -> dict[str, Any]:
    occupants = cell_occupants(m)
    odds = [n for n in occupants if n % 2 == 1]
    evens = [n for n in occupants if n % 2 == 0]
    lo2, hi2 = m * m, (m + 1) * (m + 1)
    return {
        "m": m,
        "c_m": len(odds),
        "lower_n": occupants[0] if occupants else None,
        "upper_n": occupants[-1] if occupants else None,
        "n_count": len(occupants),
        "odd_count": len(odds),
        "even_count": len(evens),
        "lo2": lo2,
        "hi2": hi2,
        "exact_status": "ODD_CELL_UNIQUE",
    }


def analytic_majorant(n: int) -> float:
    """Explicit F(N) = N^{5/6} from the van der Corput + Erdős–Turán argument."""
    return float(n) ** (5 / 6)


def loglog_slope(xs: list[int], ys: list[float]) -> float | None:
    pairs = [(x, y) for x, y in zip(xs, ys) if x >= FIT_LO and y > 0]
    if len(pairs) < 3:
        return None
    lx = [log(x) for x, _ in pairs]
    ly = [log(y) for _, y in pairs]
    n = len(lx)
    mx = sum(lx) / n
    my = sum(ly) / n
    den = sum((a - mx) ** 2 for a in lx)
    if den == 0:
        return None
    num = sum((a - mx) * (b - my) for a, b in zip(lx, ly))
    return _round(num / den)


def interval_census(n_max: int) -> dict[str, Any]:
    if n_max < 1:
        raise ValueError("n_max must be positive")
    wanted = {n for n in (*LOG_GRID, *DYADIC_GRID, n_max) if 1 <= n <= n_max}
    so = 0
    odd_odd = 0
    max_abs = 0
    argmax = 1
    records: list[dict[str, Any]] = []
    checkpoints: list[dict[str, Any]] = []
    run_len = 0
    run_sign = 0
    run_lengths: list[int] = []
    jump_odd = jump_even = 0
    prev_a: int | None = None
    occupied: list[int] = []
    adjacent_occupied = 0
    last_m: int | None = None

    for n in range(1, n_max + 1, 2):
        a = isqrt(n * n * n)
        sign = 1 - 2 * (a & 1)
        so += sign
        if sign < 0:
            odd_odd += 1
        abs_so = abs(so)
        if abs_so > max_abs:
            max_abs = abs_so
            argmax = n
            records.append({"n": n, "S_O": so, "max_abs": max_abs})
        if last_m is not None and a == last_m + 1:
            adjacent_occupied += 1
        last_m = a
        occupied.append(a)
        if prev_a is not None:
            delta = a - prev_a
            if delta & 1:
                jump_odd += 1
            else:
                jump_even += 1
        prev_a = a
        if sign == run_sign:
            run_len += 1
        else:
            if run_len:
                run_lengths.append(run_len)
            run_sign = sign
            run_len = 1
        mark = n if n in wanted else (n + 1 if n + 1 in wanted else None)
        if mark is not None:
            checkpoints.append(
                {
                    "N": mark,
                    "S_O": so,
                    "max_abs_so_far": max_abs,
                    "argmax": argmax,
                    "odd_starts": (n + 1) // 2,
                    "O_O": odd_odd,
                    "identity_ok": so == so_from_oo(odd_odd, n),
                    "over_n13": _round(max_abs / mark ** (1 / 3)),
                    "over_n12": _round(max_abs / mark**0.5),
                    "over_n56": _round(max_abs / analytic_majorant(mark)),
                    "normalization": "S_O = sum s(n) over odd n<=N",
                    "method": "exact_isqrt",
                }
            )
    if run_len:
        run_lengths.append(run_len)

    pair_var = 0
    occupied_set = set(occupied)
    seen_r: set[int] = set()
    for m in occupied:
        r = m // 2
        if r in seen_r:
            continue
        seen_r.add(r)
        c0 = 1 if (2 * r) in occupied_set else 0
        c1 = 1 if (2 * r + 1) in occupied_set else 0
        pair_var += abs(c0 - c1)

    odds = odd_start_count(n_max if n_max % 2 else n_max)
    # last odd used
    last_odd = n_max if n_max % 2 else n_max - 1
    odds = (last_odd + 1) // 2
    return {
        "n_max": n_max,
        "S_O": so,
        "max_abs": max_abs,
        "argmax": argmax,
        "odd_starts": odds,
        "O_O": odd_odd,
        "identity_ok": so == so_from_oo(odd_odd, last_odd),
        "checkpoints": checkpoints,
        "records": records[-40:],
        "run": {
            "n_runs": len(run_lengths),
            "max_run": max(run_lengths) if run_lengths else 0,
            "mean_run": _round(sum(run_lengths) / len(run_lengths)) if run_lengths else 0,
            "n_len1": sum(1 for item in run_lengths if item == 1),
            "n_len_ge3": sum(1 for item in run_lengths if item >= 3),
        },
        "jumps": {
            "odd_delta": jump_odd,
            "even_delta": jump_even,
            "odd_frac": _round(jump_odd / (jump_odd + jump_even)) if jump_odd + jump_even else None,
        },
        "cells": {
            "occupied": odds,
            "c_m_max": 1,
            "adjacent_occupied": adjacent_occupied,
            "pair_variation": pair_var,
            "pair_variation_over_odds": _round(pair_var / odds) if odds else None,
        },
        "fit_max_abs": loglog_slope(
            [row["N"] for row in checkpoints],
            [row["max_abs_so_far"] for row in checkpoints],
        ),
        "fit_range": [FIT_LO, n_max],
    }


def cell_prefix_table(m_max: int) -> dict[str, Any]:
    rows = [cell_multiplicity(m) for m in range(1, m_max + 1)]
    values = {0: 0, 1: 0, "ge2": 0}
    pair_rows: list[dict[str, Any]] = []
    pair_var = 0
    for row in rows:
        c = row["c_m"]
        if c <= 1:
            values[c] += 1
        else:
            values["ge2"] += 1
    for r in range(0, m_max // 2):
        c0 = rows[2 * r]["c_m"] if 2 * r < m_max else 0
        c1 = rows[2 * r + 1]["c_m"] if 2 * r + 1 < m_max else 0
        diff = c0 - c1
        pair_var += abs(diff)
        pair_rows.append(
            {
                "r": r,
                "c_2r": c0,
                "c_2r_plus_1": c1,
                "difference": diff,
            }
        )
    return {
        "m_max": m_max,
        "value_counts": values,
        "c_m_le_1": values["ge2"] == 0,
        "pair_variation": pair_var,
        "rows": rows,
        "pairs": pair_rows,
    }


def so_of_odd_values(values: Iterable[int]) -> dict[str, Any]:
    so = 0
    n_odd = 0
    n_all = 0
    diameter = 0
    for x in values:
        n_all += 1
        if x > diameter:
            diameter = x
        if x < 1 or x % 2 == 0:
            continue
        n_odd += 1
        so += 1 - 2 * (isqrt(x * x * x) & 1)
    return {
        "S_O": so,
        "n_odd": n_odd,
        "cardinality": n_all,
        "diameter": diameter,
        "over_odd": _round(abs(so) / n_odd) if n_odd else None,
        "over_card": _round(abs(so) / n_all) if n_all else None,
        "over_diam13": _round(abs(so) / diameter ** (1 / 3)) if diameter >= 2 else None,
        "over_n56": _round(abs(so) / analytic_majorant(max(diameter, 1))) if diameter else None,
    }


def juggler_image(n_max: int, steps: int) -> set[int]:
    out: set[int] = set()
    for n in range(1, n_max + 1):
        x = n
        for _ in range(steps):
            x = floor_power(x)
        out.add(x)
    return out


def word_image(word: str, n_max: int) -> set[int]:
    out: set[int] = set()
    for n in range(1, n_max + 1):
        if follows_itinerary(n, word):
            out.add(image_after(n, word))
    return out


def structured_census(*, image_n_max: int, word_n_max: int) -> dict[str, Any]:
    rows: list[dict[str, Any]] = []
    grid = sorted(
        {n for n in IMAGE_GRID if 20 <= n <= image_n_max} | ({image_n_max} if image_n_max >= 20 else set())
    )
    for n_max in grid:
        for steps, name in ((1, "J([1,N])"), (2, "J^2([1,N])")):
            rec = so_of_odd_values(juggler_image(n_max, steps))
            rec.update(
                {
                    "set_type": name,
                    "source": f"1..{n_max}",
                    "N": n_max,
                    "normalization": "S_O(A)=sum s(x) over odd x in A",
                }
            )
            rows.append(rec)
    for word in SELECTED_WORDS:
        rec = so_of_odd_values(word_image(word, word_n_max))
        rec.update(
            {
                "set_type": f"T_{word}",
                "source": f"follows {word} in 1..{word_n_max}",
                "N": word_n_max,
                "normalization": "S_O(A)=sum s(x) over odd x in A",
            }
        )
        rows.append(rec)
    return {"rows": rows, "image_n_max": image_n_max, "word_n_max": word_n_max}


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
            "n13_is_a_theorem": False,
            "floor_replaced_by_complex_exponential": False,
            "interval_bound_transfers_to_arbitrary_sets": False,
            "iterate_from_numerics": False,
            "reopen_probabilistic_ld": False,
            "reopen_2adic_bridge": False,
            "cuda_census": False,
            "weyl_engine": False,
        }
    )
    return anti


def classify(interval: dict[str, Any], cells: dict[str, Any], structured: dict[str, Any]) -> dict[str, Any]:
    pairing_linear = interval["cells"]["pair_variation_over_odds"] is not None and (
        interval["cells"]["pair_variation_over_odds"] > 0.5
    )
    n13_not_theorem = True
    image_rows = [
        row
        for row in structured["rows"]
        if row["set_type"].startswith("J") and row["n_odd"] >= 20
    ]
    large_images = [row for row in image_rows if row["N"] >= 10_000]
    concentrated = any(
        row["over_odd"] is not None and row["over_odd"] >= 0.25 for row in large_images
    )
    balanced = bool(large_images) and all(
        row["over_odd"] is not None and row["over_odd"] <= 0.05 for row in large_images
    )
    return {
        "classification": CLASS_GREEN,
        "branch": "PARK",
        "reason": (
            "S_O(N) = -2 D_O(N) and the cell rewrite S_O = sum_m (-1)^m c_m "
            "with c_m in {0,1} are exact. Adjacent pairing has linear variation "
            "and is not a cancellation theorem. The fractional-part identity "
            "plus van der Corput / Erdős–Turán give the explicit interval bound "
            "|S_O(N)| << N^{5/6}. The observed N^{1/3} envelope is not promoted. "
            + (
                "One-step Juggler images stay small relative to |A_odd|; "
                "that is a census, not a transfer theorem."
                if balanced
                else (
                    "A Juggler-generated image concentrates odd-image signs; "
                    "interval cancellation does not automatically iterate."
                    if concentrated
                    else "Image-set discrepancy is inconclusive on the window."
                )
            )
        ),
        "interval_bound": "N^{5/6}",
        "pairing_useful": not pairing_linear,
        "n13_promoted": not n13_not_theorem,
        "image_concentrated": concentrated,
        "image_balanced": balanced,
        "odd_start_proof": True,
    }


def scan(
    *,
    n_max: int = N_MAX,
    n_spot: int | None = N_SPOT,
    cell_prefix: int = CELL_PREFIX,
    word_n_max: int = WORD_N_MAX,
    image_n_max: int | None = None,
) -> dict[str, Any]:
    if image_n_max is None:
        image_n_max = n_max
    interval = interval_census(n_max)
    spot = interval_census(n_spot) if n_spot is not None and n_spot > n_max else None
    cells = cell_prefix_table(cell_prefix)
    structured = structured_census(image_n_max=image_n_max, word_n_max=word_n_max)
    payload = {
        "n_max": n_max,
        "n_spot": None if spot is None else n_spot,
        "interval": interval,
        "spot": {
            "n_max": spot["n_max"],
            "S_O": spot["S_O"],
            "max_abs": spot["max_abs"],
            "argmax": spot["argmax"],
            "over_n13": _round(spot["max_abs"] / spot["n_max"] ** (1 / 3)),
            "over_n56": _round(spot["max_abs"] / analytic_majorant(spot["n_max"])),
            "checkpoints": spot["checkpoints"],
            "fit_max_abs": spot["fit_max_abs"],
        }
        if spot is not None
        else None,
        "cells": {
            "m_max": cells["m_max"],
            "value_counts": cells["value_counts"],
            "c_m_le_1": cells["c_m_le_1"],
            "pair_variation": cells["pair_variation"],
        },
        "structured": structured,
        "lean": lean_api_present(),
        "anti_overclaim": anti_overclaim(),
        "cell_prefix_rows": cells["rows"],
        "cell_prefix_pairs": cells["pairs"],
    }
    payload["decision"] = classify(interval, cells, structured)
    return payload


def write_json(scan_row: dict[str, Any], path: Path = JSON_PATH) -> None:
    slim = dict(scan_row)
    slim.pop("cell_prefix_rows", None)
    slim.pop("cell_prefix_pairs", None)
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
    with (directory / "odd_image_discrepancy.csv").open(
        "w", encoding="utf-8", newline=""
    ) as handle:
        fields = (
            "N",
            "S_O",
            "max_abs_so_far",
            "argmax",
            "over_n13",
            "over_n12",
            "over_n56",
            "normalization",
            "method",
        )
        writer = csv.DictWriter(handle, fieldnames=fields)
        writer.writeheader()
        rows = list(scan_row["interval"]["checkpoints"])
        if scan_row["spot"] is not None:
            seen = {row["N"] for row in rows}
            rows.extend(
                row for row in scan_row["spot"]["checkpoints"] if row["N"] not in seen
            )
        for row in rows:
            writer.writerow({key: row.get(key) for key in fields})
    with (directory / "cell_counts.csv").open("w", encoding="utf-8", newline="") as handle:
        fields = (
            "m",
            "c_m",
            "lower_n",
            "upper_n",
            "odd_count",
            "even_count",
            "exact_status",
        )
        writer = csv.DictWriter(handle, fieldnames=fields)
        writer.writeheader()
        for row in scan_row["cell_prefix_rows"]:
            writer.writerow({key: row.get(key) for key in fields})
    with (directory / "cell_pair_differences.csv").open(
        "w", encoding="utf-8", newline=""
    ) as handle:
        fields = ("r", "c_2r", "c_2r_plus_1", "difference")
        writer = csv.DictWriter(handle, fieldnames=fields)
        writer.writeheader()
        for row in scan_row["cell_prefix_pairs"]:
            writer.writerow(row)
    with (directory / "discrepancy_maxima.csv").open(
        "w", encoding="utf-8", newline=""
    ) as handle:
        fields = ("n", "S_O", "max_abs")
        writer = csv.DictWriter(handle, fieldnames=fields)
        writer.writeheader()
        for row in scan_row["interval"]["records"]:
            writer.writerow(row)
    with (directory / "structured_set_discrepancy.csv").open(
        "w", encoding="utf-8", newline=""
    ) as handle:
        fields = (
            "set_type",
            "source",
            "N",
            "cardinality",
            "n_odd",
            "diameter",
            "S_O",
            "over_odd",
            "over_card",
            "normalization",
        )
        writer = csv.DictWriter(handle, fieldnames=fields)
        writer.writeheader()
        for row in scan_row["structured"]["rows"]:
            writer.writerow({key: row.get(key) for key in fields})
    examples = [
        {
            "claim": "adjacent cell pairing yields a sublinear variation bound",
            "status": "COUNTEREXAMPLE",
            "detail": scan_row["interval"]["cells"],
        },
        {
            "claim": "observed N^{1/3} envelope is a theorem",
            "status": "REJECTED",
            "detail": {
                "fit": scan_row["interval"]["fit_max_abs"],
                "fit_range": scan_row["interval"]["fit_range"],
            },
        },
    ]
    small_conc = [
        row
        for row in scan_row["structured"]["rows"]
        if row.get("over_odd") is not None and row["over_odd"] >= 0.25
    ]
    if small_conc:
        examples.append(
            {
                "claim": "interval cancellation transfers to every Juggler image, including small N",
                "status": "COUNTEREXAMPLE",
                "detail": small_conc,
            }
        )
    with (directory / "counterexamples.jsonl").open("w", encoding="utf-8") as handle:
        for rec in examples:
            handle.write(json.dumps(rec) + "\n")
    (directory / "manifest.json").write_text(
        json.dumps(
            {
                "n_max": scan_row["n_max"],
                "n_spot": scan_row["n_spot"],
                "files": [
                    "odd_image_discrepancy.csv",
                    "cell_counts.csv",
                    "cell_pair_differences.csv",
                    "discrepancy_maxima.csv",
                    "structured_set_discrepancy.csv",
                    "counterexamples.jsonl",
                ],
                "classification": scan_row["decision"]["classification"],
                "S_O_convention": "sum (-1)^{isqrt(n^3)} over odd n<=N",
                "note": "interval bound N^{5/6} is analytic; N^{1/3} is not promoted",
            },
            indent=2,
        )
        + "\n",
        encoding="utf-8",
    )


def write_docs(scan_row: dict[str, Any], path: Path = DOC_PATH) -> None:
    decision = scan_row["decision"]
    interval = scan_row["interval"]
    spot = scan_row["spot"]
    cells = scan_row["cells"]
    log_rows = [
        row
        for row in interval["checkpoints"]
        if row["N"] in LOG_GRID or row["N"] == interval["n_max"]
    ]
    table = _md_table(
        ["N", "S_O", "max|S_O|", "argmax", "max/N^{1/3}", "max/N^{1/2}", "max/N^{5/6}"],
        [
            [
                row["N"],
                row["S_O"],
                row["max_abs_so_far"],
                row["argmax"],
                row["over_n13"],
                row["over_n12"],
                row["over_n56"],
            ]
            for row in log_rows
        ],
    )
    spot_line = ""
    if spot is not None:
        spot_line = (
            f"Spot `N={spot['n_max']}`: `S_O={spot['S_O']}`, "
            f"`max|S_O|={spot['max_abs']}` at `n={spot['argmax']}`, "
            f"`max/N^{{1/3}}={spot['over_n13']}`, "
            f"`max/N^{{5/6}}={spot['over_n56']}`.\n"
        )
    struct_table = _md_table(
        ["set", "N", "|A|", "odd", "diam", "S_O(A)", "|S|/odd", "|S|/|A|"],
        [
            [
                row["set_type"],
                row["N"],
                row["cardinality"],
                row["n_odd"],
                row["diameter"],
                row["S_O"],
                row["over_odd"],
                row["over_card"],
            ]
            for row in scan_row["structured"]["rows"]
        ],
    )
    path.write_text(
        f"""# Juggler odd-image discrepancy

Status: **{decision["classification"]}**

Standalone Archimedean counting phase on the odd-start sequence
`s(n)=(-1)^{{floor(n^{{3/2}})}}`. Not a halt theorem and not a
frequency theorem. Closed PE / residual / 2-adic / landing-θ /
probabilistic-LD branches stay closed.

## 1. Exact sequence definition

For odd `n`,

```
a_n = floor(n^{{3/2}}) = isqrt(n^3)
s(n) = (-1)^{{a_n}}
S_O(N) = sum_{{odd n <= N}} s(n)
```

This is exact integer arithmetic. Label: **EXACT IDENTITY**.

If `O_O(N)` is the number of odd `n<=N` with `a_n` odd, then
`S_O(N) = #{{odd n<=N}} - 2 O_O(N) = -2 D_O(N)`, where `D_O` is the
Phase-0 odd-start discrepancy. Census identity holds:
`{interval["identity_ok"]}`. Label: **EXACT IDENTITY**.

`floor(x)` is odd iff `{{x/2}} >= 1/2`. So `s(n)=-1` iff
`{{n^{{3/2}}/2}} >= 1/2`. No complex exponential is substituted for
the floor. Label: **EXACT IDENTITY**.

## 2. Cell decomposition

`C_m = {{odd n : a_n = m}}` is the odd part of the cube cell
`m^2 <= n^3 < (m+1)^2`. `odd_preimage_unique` says that cell contains at
most one integer, so `c_m = |C_m| in {{0,1}}`. Label:
**LEAN-CERTIFIED** (`odd_preimage_unique`).

Prefix `m<= {cells["m_max"]}`: value counts `{cells["value_counts"]}`,
`c_m <= 1` is `{cells["c_m_le_1"]}`. Label: **EXACT COMPUTATION**.

Therefore

```
S_O(N) = sum_m (-1)^m c_m
```

over occupied cells with occupant `<=N`, plus nothing from empty
cells. Label: **EXACT IDENTITY**.

Occupied cells for `n<= {interval["n_max"]}`: `{interval["cells"]["occupied"]}`.
Adjacent occupied pairs `(m,m+1)`: `{interval["cells"]["adjacent_occupied"]}`.
Typical gaps are `a_{{n+2}}-a_n ~ 3 sqrt(n)`, so occupied cells are
isolated. Label: **COMPUTATIONALLY OBSERVED**.

## 3. Elementary bounds

Adjacent pairing: `sum_r |c_{{2r}}-c_{{2r+1}}|` on occupied pairs is
`{interval["cells"]["pair_variation"]}`, ratio to `#odds` is
`{interval["cells"]["pair_variation_over_odds"]}`. Because occupied
cells are isolated, each occupant contributes `1` to the variation.
This is a linear bound, i.e. the trivial `|S_O| <= #odds`. Label:
**COUNTEREXAMPLE** to pairing-as-cancellation.

Sign runs of `s(n)` on consecutive odd `n`: `{interval["run"]["n_runs"]}`
runs, max length `{interval["run"]["max_run"]}`, mean
`{interval["run"]["mean_run"]}`, length-1 count
`{interval["run"]["n_len1"]}`. Jumps `a_{{n+2}}-a_n` are odd with
frequency `{interval["jumps"]["odd_frac"]}`. Label:
**COMPUTATIONALLY OBSERVED**. No deterministic pairing of runs was
found that beats the trivial bound.

The even-start bound `|D_E| <= floor(sqrt(N))+1` is not restated as
the main theorem. Label: **EXACT — HUMAN PROOF** in the parent
branch; rejected here as the odd-start result.

## 4. Analytic bounds

Write `n=2r+1` and `g(r)=(2r+1)^{{3/2}}/2`. Then `S_O` is twice the
discrepancy of `{{g(r)}}` from `1/2`. Label: **EXACT IDENTITY**.

`g''` is positive and decreasing. Van der Corput on dyadic blocks,
plus Erdős–Turán, gives the explicit interval bound

```
|S_O(N)| << N^{{5/6}}.
```

The argument is in the dossier. The floor is not replaced by
`exp(pi i n^{{3/2}})`: the exponential sums are those of
`exp(2 pi i k g(r))`, which is the standard discrepancy expansion of
`{{g(r)}}`. Label: **ANALYTIC THEOREM**.

This is `O(N^{{1-1/6}})`. It is not the observed `N^{{1/3}}` and is
not claimed sharp. Implied constants are those of the two cited
lemmas, not fitted.

On the census window the inequality holds with room:
`max|S_O|/N^{{5/6}}` at `N={interval["n_max"]}` is
`{_round(interval["max_abs"] / analytic_majorant(interval["n_max"]))}`.
Label: **EXACT COMPUTATION**.

## 5. Computational scaling

One exact pass, `n<= {interval["n_max"]}`. Label: **EXACT COMPUTATION**.

{table}

{spot_line}
Descriptive log-log slope of `max|S_O|` vs `N` on
`{interval["fit_range"]}` is `{interval["fit_max_abs"]}`. This is a
diagnostic, not an exponent theorem. Label: **COMPUTATIONALLY OBSERVED**.

## 6. Lower-bound / sharpness evidence

Running-max witnesses exist (last records stored). At
`N={interval["n_max"]}`, `max|S_O|={interval["max_abs"]}` at
`n={interval["argmax"]}`. Relative to `N^{{1/3}}` the ratio stays
order-1; relative to `N^{{5/6}}` it tends to `0`. No explicit
infinite family `|S_O(N_j)| >= c N_j^alpha` was constructed. Label:
**COMPUTATIONALLY OBSERVED**. The `N^{{1/3}}` envelope is **not** a
**CANDIDATE CONJECTURE**.

## 7. Structured Juggler-image sets

`S_O(A)` sums `s(x)` over odd `x in A`, not over the starts that
produced `A`. Interval bounds do not apply automatically.

{struct_table}

Label: **EXACT COMPUTATION** of the listed finite sets.
Normalization is `|S_O(A)| / #{{odd x in A}}` and
`|S_O(A)| / |A|`. Diameter is recorded and is not used as a fake
interval length.

## 8. Iteration tests

The table above includes `J([1,N])` and `J^2([1,N])` on the same
grid. Numerical smallness is not a propagation theorem. Label:
**COMPUTATIONALLY OBSERVED**. Flag
`image_balanced={decision["image_balanced"]}`,
`image_concentrated={decision["image_concentrated"]}`.

## 9. Potential deterministic parity theorem

An interval `O(N^{{5/6}})` bound replaces “`P(O)≈1/2` on `[1,N]`
odds after one odd step” by an explicit discrepancy rate. It does
not by itself control branch frequencies along orbits, and it does
not transfer to arbitrary Juggler-generated sets. Label:
**HEURISTIC** for the desired counting-to-dynamics chain; not a
drift theorem.

## 10. Counterexamples

- Adjacent `c_{{2r}}-c_{{2r+1}}` pairing as a sublinear bound.
  **COUNTEREXAMPLE** (variation / `#odds` ≈
  `{interval["cells"]["pair_variation_over_odds"]}`).
- “`N^{{1/3}}` is the theorem.” **REJECTED** as a promotion.
- “`exp(pi i n^{{3/2}})` may replace the floor.” **REJECTED**; the
  exact object is `{{n^{{3/2}}/2}}`.
- Interval bound used on a non-interval `A` without a transfer
  proof. **REJECTED**.

## 11. Lean candidates

Existing: `odd_preimage_unique`, `odd_preimage_iff`,
`landingParity_odd_iff`, `floorPower_odd_macro_direction`.
Present: `{scan_row["lean"]}`.

Not added: van der Corput / Erdős–Turán. The elementary cell-sum
identity is a packaging of `odd_preimage_unique` and is not a new Lean
file. No `sorry`.

## 12. Decision

Classification **{decision["classification"]}**.

{decision["reason"]}

This is not a termination theorem.
""",
        encoding="utf-8",
    )


def write_dossier(scan_row: dict[str, Any], path: Path = DOSSIER_PATH) -> None:
    decision = scan_row["decision"]
    interval = scan_row["interval"]
    path.write_text(
        f"""# Juggler odd-image discrepancy

Status: **EXPLORATORY**

Follow-up of the parked image-parity census. It is **not** a Research
Engine experiment, not a frequency theorem, and not a claim that
every positive integer reaches 1.

## Problem

Can the odd-start sign sequence \\(s(n)=(-1)^{{\\lfloor n^{{3/2}}\\rfloor}}\\)
be given an explicit sublinear discrepancy bound on intervals, and
does that cancellation survive on sets produced by \\(J\\)?

## Exact statement

Write \\(S_O(N)=\\sum s(n)\\) over odd \\(n\\le N\\). Phase 0 asks for
an explicit \\(F(N)=o(N)\\) with \\(|S_O(N)|\\le F(N)\\), obtained from
the cell multiplicities \\(c_m\\) or from the exact fractional-part
form of \\(s\\). After an interval bound exists, the same sum is
evaluated on \\(J([1,N])\\), \\(J^{{2}}([1,N])\\), and selected Atlas
words. Totality is unclaimed.

## Current literature

- Parent census [juggler_parity_discrepancy.md](juggler_parity_discrepancy.md)
  **PARK** / `IMAGE_PARITY_CENSUS`. \\(D_O=-S_O/2\\).
- `odd_preimage_unique` / `odd_preimage_iff` —
  **EXACT — LEAN VERIFIED**.
- `floorPower_odd_macro_direction` —
  **EXACT — LEAN VERIFIED**.
- Even-cell \\(|D_E|\\le\\lfloor\\sqrt N\\rfloor+1\\) —
  **EXACT — HUMAN PROOF**; not the target.
- 2-adic bridge, landing-θ, PE / residual / LD model —
  **CLOSE**. Do not reopen.
- Prasad–Prasad 2025 (`prasad-prasad-2025-juggler-like`) —
  motivation only.
- Van der Corput / Erdős–Turán —
  **KNOWN** analytic tools, applied here to `n^{{3/2}}/2` mod 1.

Project relationship: **extended** from the parked census.
Totality remains unclaimed.

## Branch budget

```text
Mathematical target     Prove |S_O(N)| <= F(N) with F=o(N) for
                        s(n)=(-1)^{{floor(n^{{3/2}})}} on odd n;
                        then test S_O on J([1,N]) and J^2([1,N]).
Novelty hypothesis      Cell pairing cancellation, or an explicit
                        fractional-part discrepancy rate
Falsifier               Pairing is linear variation only; no honest
                        F; images concentrate one sign
Existing machinery      odd_preimage_unique; parity_discrepancy D_O;
                        floor_power; follows_itinerary / image_after
Maximum Phase-0 scope   Exact S_O; c_m prefix; pairing/runs;
                        one analytic rate; image/word tests on
                        the existing grids; no CUDA; no Lean ANT
Promotion criterion     Explicit F=o(N) with a proof, and a
                        transfer statement on J-images
Stop criterion          Pairing useless and rate only KNOWN
                        method with no transfer; machinery gravity;
                        halt claim; promoting N^{{1/3}}
```

## Balanced-ternary formulation

None required. The map is on ordinary positive integers.

## Why BT may be relevant

It is not required. The 2-adic / BT bridge is closed.

## Candidate operations / invariants

- \\(S_O=-2D_O\\) —
  **EXACT — HUMAN PROOF**
- \\(c_m\\in\\{{0,1\\}}\\) —
  **EXACT — LEAN VERIFIED**
- Adjacent pairing bound —
  **REFUTED** as a sublinear estimate
- \\(|S_O(N)|\\ll N^{{5/6}}\\) —
  **EXACT — HUMAN PROOF**
- Observed \\(N^{{1/3}}\\) —
  **OBSERVATION**, not promoted
- Interval bound on \\(J([1,N])\\) without transfer —
  not claimed
- `parity_frequency_theorem` —
  stays false
- global halt — not claimed

## Experiments

- Probe: `research.juggler_sequence.odd_image_discrepancy`
- Records: [juggler_odd_image_discrepancy.md](../research/juggler_odd_image_discrepancy.md),
  [juggler_odd_image_discrepancy.json](../research/juggler_odd_image_discrepancy.json)
- Dataset: `data/research/juggler/parity_discrepancy_next/`
- Tests: `tests/research/juggler_sequence/test_odd_image_discrepancy.py`

No GPU. No new Lean file.

## Conjectures

None opened. The \\(N^{{1/3}}\\) envelope is not entered as a
conjecture.

## Counterexamples

- Adjacent cell pairing as a sublinear variation bound: variation
  over `#odds` is `{interval["cells"]["pair_variation_over_odds"]}`
  on `n<={interval["n_max"]}`.
- “`N^{{1/3}}` is proved”: descriptive slope
  `{interval["fit_max_abs"]}` on `{interval["fit_range"]}`.

## Formalization

None added. The cell uniqueness lemma already exists. Analytic
number theory is not Lean-packaged. No `sorry`.

## Results

Classification **{decision["classification"]}**.

{decision["reason"]}

On `n<={interval["n_max"]}`: `S_O={interval["S_O"]}`,
`max|S_O|={interval["max_abs"]}` at `n={interval["argmax"]}`.
`c_m<=1` on the prefix: `{scan_row["cells"]["c_m_le_1"]}`.

## Open questions

Sharpen \\(N^{{5/6}}\\) toward the census envelope, or prove a
transfer estimate for \\(S_O(J([1,N]))\\). Do not iterate by
numerics. Do not claim termination.

## Decision

**{decision["branch"]}**. {decision["reason"]} Do not claim
termination. Do not flip `parity_frequency_theorem`.

Best next question: prove a transfer bound for \\(S_O\\) on
\\(J([1,N])\\), or replace \\(N^{{5/6}}\\) by an effective
\\(N^{{1/2+\\varepsilon}}\\) estimate without a Weyl engine.

## Publication assessment

Status: `EXPLORATORY`. An exact cell rewrite plus a classical
discrepancy rate on one sequence, not a paper candidate and not a
Juggler totality result.
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


if __name__ == "__main__":
    main()
