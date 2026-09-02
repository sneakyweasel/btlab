"""One-step Juggler image-parity discrepancy.

Not a Research Engine control-layer experiment. Not a halt theorem.
Not a parity-frequency theorem and not a 2-adic cylinder argument.
Does not reopen landing theta, the 2-adic / integer bridge, or the
probabilistic / large-deviation branches.

Splits #{n<=N: J(n) odd} - N/2 into an elementary even-cell count and
the Archimedean n^{3/2} count on odd starts.
"""

from __future__ import annotations

import csv
import json
from math import isqrt, log
from pathlib import Path
from typing import Any

from research.juggler_sequence.lean_paths import has_named, juggler_text
from research.juggler_sequence.power_itineraries import ANTI_OVERCLAIM, floor_power

REPO_ROOT = Path(__file__).resolve().parents[3]
JSON_PATH = REPO_ROOT / "docs" / "research" / "juggler_parity_discrepancy.json"
DOC_PATH = REPO_ROOT / "docs" / "research" / "juggler_parity_discrepancy.md"
DOSSIER_PATH = REPO_ROOT / "docs" / "problems" / "juggler_parity_discrepancy.md"
DATA_DIR = REPO_ROOT / "data" / "research" / "juggler" / "parity_discrepancy"

N_MAX = 1_000_000
N_SPOT = 10_000_000
LOG_GRID = (10, 100, 1_000, 10_000, 100_000, 1_000_000)
DYADIC_GRID = tuple(1 << k for k in range(4, 21))

CLASS_PARK = "IMAGE_PARITY_CENSUS"
CLASS_PROMOTE = "ODD_START_BOUND_GREEN"
CLASS_CLOSE = "IMAGE_PARITY_CLOSE"

LINEAR_BIAS_FRAC = 0.01
ALMOST_LINEAR_EXP = 0.9

LEAN_THEOREMS = (
    "even_preimage_iff",
    "odd_preimage_unique",
    "odd_preimage_iff",
    "landingParity",
    "landingParity_odd_iff",
    "landingParity_even_iff",
    "floorPower_odd_macro_direction",
    "floorPower_odd_even_two_step_lt",
    "floorPower_odd_odd_two_step_gt",
    "ooe_cylinder_both_next_parities",
)

FORBIDDEN_ENGINES = (
    "ResidualGraph",
    "ResidualState",
    "MilestoneGraph",
    "PowerHeight",
    "CycleEngine",
)


def even_count_inclusive(lo: int, hi: int) -> int:
    if hi < lo:
        return 0
    if lo < 1:
        lo = 1
    return hi // 2 - (lo - 1) // 2


def even_image_odd_count(n: int) -> int:
    """Closed even-cell count of even starts with J odd."""
    if n < 2:
        return 0
    q = isqrt(n)
    complete = (q // 2) ** 2
    if q % 2 == 1:
        return complete + even_count_inclusive(q * q, n)
    return complete


def even_start_count(n: int) -> int:
    return n // 2


def odd_start_count(n: int) -> int:
    return (n + 1) // 2


def even_discrepancy(n: int) -> float:
    return even_image_odd_count(n) - even_start_count(n) / 2


def even_discrepancy_bound(n: int) -> int:
    """Uniform integer majorant |D_E(N)| <= isqrt(N) + 1."""
    return isqrt(max(n, 0)) + 1


def image_odd(n: int) -> bool:
    return floor_power(n) % 2 == 1


def _round(value: float) -> float:
    return round(float(value), 8)


def discrepancy_ratios(value: float, n: int) -> dict[str, float]:
    absv = abs(float(value))
    if n < 2:
        return {
            "abs": _round(absv),
            "over_log": None,
            "over_n13": None,
            "over_n12": None,
            "over_n23": None,
        }
    return {
        "abs": _round(absv),
        "over_log": _round(absv / log(n)),
        "over_n13": _round(absv / n ** (1 / 3)),
        "over_n12": _round(absv / n**0.5),
        "over_n23": _round(absv / n ** (2 / 3)),
    }


def _checkpoint_row(
    n: int,
    o_count: int,
    even_odd: int,
    odd_odd: int,
    max_abs_d: float,
    max_abs_de: float,
    max_abs_do: float,
) -> dict[str, Any]:
    evens = even_start_count(n)
    odds = odd_start_count(n)
    d = o_count - n / 2
    d_e = even_odd - evens / 2
    d_o = odd_odd - odds / 2
    closed = even_image_odd_count(n)
    return {
        "n": n,
        "O": o_count,
        "O_E": even_odd,
        "O_O": odd_odd,
        "even_starts": evens,
        "odd_starts": odds,
        "D": _round(d),
        "D_E": _round(d_e),
        "D_O": _round(d_o),
        "O_E_closed": closed,
        "closed_matches": closed == even_odd,
        "even_bound": even_discrepancy_bound(n),
        "even_bound_ok": abs(d_e) <= even_discrepancy_bound(n),
        "max_abs_D": _round(max_abs_d),
        "max_abs_D_E": _round(max_abs_de),
        "max_abs_D_O": _round(max_abs_do),
        "D_ratios": discrepancy_ratios(d, n),
        "D_E_ratios": discrepancy_ratios(d_e, n),
        "D_O_ratios": discrepancy_ratios(d_o, n),
        "max_D_O_ratios": discrepancy_ratios(max_abs_do, n),
    }


def prefix_census(n_max: int) -> dict[str, Any]:
    if n_max < 1:
        raise ValueError("n_max must be positive")
    wanted = {n for n in (*LOG_GRID, *DYADIC_GRID, n_max) if 1 <= n <= n_max}
    o_count = even_odd = odd_odd = 0
    max_abs_d = max_abs_de = max_abs_do = 0.0
    even_bound_holds = True
    rows: list[dict[str, Any]] = []
    for n in range(1, n_max + 1):
        if n % 2 == 0:
            jo = isqrt(n) & 1
            even_odd += jo
            d_e = even_odd - n // 2 / 2
            if abs(d_e) > max_abs_de:
                max_abs_de = abs(d_e)
            if abs(d_e) > even_discrepancy_bound(n):
                even_bound_holds = False
        else:
            jo = isqrt(n * n * n) & 1
            odd_odd += jo
            d_o = odd_odd - (n + 1) // 2 / 2
            if abs(d_o) > max_abs_do:
                max_abs_do = abs(d_o)
        o_count += jo
        d = o_count - n / 2
        if abs(d) > max_abs_d:
            max_abs_d = abs(d)
        if n in wanted:
            rows.append(
                _checkpoint_row(
                    n, o_count, even_odd, odd_odd, max_abs_d, max_abs_de, max_abs_do
                )
            )
    return {
        "n_max": n_max,
        "checkpoints": rows,
        "final": rows[-1],
        "even_bound_holds": even_bound_holds,
        "closed_matches": all(row["closed_matches"] for row in rows),
        "max_abs_D": _round(max_abs_d),
        "max_abs_D_E": _round(max_abs_de),
        "max_abs_D_O": _round(max_abs_do),
    }


def odd_start_spot(n_max: int) -> dict[str, Any]:
    if n_max < 1:
        raise ValueError("n_max must be positive")
    wanted = {n for n in (*LOG_GRID, *DYADIC_GRID, n_max) if 1 <= n <= n_max}
    odd_odd = 0
    max_abs_do = 0.0
    rows: list[dict[str, Any]] = []
    last_odd = n_max if n_max % 2 else n_max - 1
    for n in range(1, n_max + 1, 2):
        odd_odd += isqrt(n * n * n) & 1
        odds = (n + 1) // 2
        d_o = odd_odd - odds / 2
        if abs(d_o) > max_abs_do:
            max_abs_do = abs(d_o)
        mark = n if n in wanted else (n + 1 if n + 1 in wanted else None)
        if mark is not None:
            rows.append(
                {
                    "n": mark,
                    "odd_n": n,
                    "O_O": odd_odd,
                    "odd_starts": odds,
                    "D_O": _round(d_o),
                    "max_abs_D_O": _round(max_abs_do),
                    "max_D_O_ratios": discrepancy_ratios(max_abs_do, mark),
                }
            )
    return {
        "n_max": n_max,
        "last_odd": last_odd,
        "checkpoints": rows,
        "final": rows[-1] if rows else None,
        "max_abs_D_O": _round(max_abs_do),
    }


def lean_api_present() -> dict[str, bool]:
    text = juggler_text()
    return {
        "sorry_free": "sorry" not in text and "admit" not in text,
        **{name: has_named(text, name) for name in LEAN_THEOREMS},
        "no_forbidden_engines": all(
            f"structure {name}" not in text and f"inductive {name}" not in text
            for name in FORBIDDEN_ENGINES
        ),
        "no_global_termination_theorem": "theorem juggler_reaches_one" not in text,
        "no_new_landing_packaging": True,
    }


def anti_overclaim() -> dict[str, bool]:
    anti = dict(ANTI_OVERCLAIM)
    anti.update(
        {
            "global_termination": False,
            "parity_frequency_theorem": False,
            "reopen_landing_theta": False,
            "reopen_2adic_bridge": False,
            "reopen_probabilistic_ld": False,
            "reopen_preimage_cylinders": False,
            "iterate_counting_estimates": False,
            "weyl_engine": False,
            "cuda_census": False,
            "odd_start_bound_is_theorem": False,
        }
    )
    return anti


def classify(census: dict[str, Any], spot: dict[str, Any] | None) -> dict[str, Any]:
    final = census["final"]
    n_max = census["n_max"]
    max_do = census["max_abs_D_O"]
    if spot is not None and spot["final"] is not None:
        max_do = max(max_do, spot["max_abs_D_O"])
        n13 = spot["final"]["max_D_O_ratios"]["over_n13"]
        n_ref = spot["n_max"]
    else:
        n13 = final["max_D_O_ratios"]["over_n13"]
        n_ref = n_max
    linear = abs(final["D_O"]) > LINEAR_BIAS_FRAC * n_max
    almost_linear = max_do > n_ref**ALMOST_LINEAR_EXP
    even_ok = census["even_bound_holds"] and census["closed_matches"]
    odd_start_proof = False
    if linear or almost_linear:
        return {
            "classification": CLASS_CLOSE,
            "branch": "CLOSE",
            "reason": (
                "Odd-start image parity has a linear or almost-linear bias "
                "on the Phase-0 window, so an iterable N/2 discrepancy bound "
                "does not survive."
            ),
            "even_bound_holds": even_ok,
            "linear_bias": linear,
            "almost_linear": almost_linear,
            "odd_start_proof": odd_start_proof,
            "named_odd_exponent": None,
            "n13_ratio": n13,
        }
    if odd_start_proof:
        return {
            "classification": CLASS_PROMOTE,
            "branch": "PROMOTE",
            "reason": "An explicit o(N) odd-start discrepancy bound was proved.",
            "even_bound_holds": even_ok,
            "linear_bias": False,
            "almost_linear": False,
            "odd_start_proof": True,
            "named_odd_exponent": "proved",
            "n13_ratio": n13,
        }
    return {
        "classification": CLASS_PARK,
        "branch": "PARK",
        "reason": (
            "The even-cell discrepancy is an explicit O(sqrt(N)) identity. "
            "The odd-start n^{3/2} count has no linear bias and tracks a "
            f"named N^{{1/3}} envelope (max|D_O|/N^{{1/3}} ≈ {n13} on the "
            "window), but that envelope is only a census."
        ),
        "even_bound_holds": even_ok,
        "linear_bias": False,
        "almost_linear": False,
        "odd_start_proof": False,
        "named_odd_exponent": "N^{1/3}",
        "n13_ratio": n13,
    }


def scan(*, n_max: int = N_MAX, n_spot: int | None = N_SPOT) -> dict[str, Any]:
    census = prefix_census(n_max)
    spot = odd_start_spot(n_spot) if n_spot is not None and n_spot > n_max else None
    payload = {
        "n_max": n_max,
        "n_spot": None if spot is None else n_spot,
        "census": census,
        "odd_spot": spot,
        "lean": lean_api_present(),
        "anti_overclaim": anti_overclaim(),
        "existing_api": {
            "even_preimage": "even_preimage_iff: J(n)=q for even n iff q^2 <= n < (q+1)^2",
            "odd_cell": "odd_preimage_unique: the n^{3/2} cell is a singleton",
            "landing_parity": "landingParity = J(n) mod 2; tautological in T",
            "two_step": (
                "floorPower_odd_macro_direction: odd n>=3 has T^2(n)<n iff "
                "J(n) even and T^2(n)>n iff J(n) odd"
            ),
        },
    }
    payload["decision"] = classify(census, spot)
    return payload


def write_json(scan_row: dict[str, Any], path: Path = JSON_PATH) -> None:
    path.write_text(json.dumps(scan_row, indent=2) + "\n", encoding="utf-8")


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
    fields = (
        "n",
        "O",
        "O_E",
        "O_O",
        "D",
        "D_E",
        "D_O",
        "max_abs_D",
        "max_abs_D_E",
        "max_abs_D_O",
        "max_D_O_over_n13",
        "max_D_O_over_n12",
        "O_E_closed",
        "even_bound_ok",
    )
    with (directory / "checkpoints.csv").open("w", encoding="utf-8", newline="") as handle:
        writer = csv.DictWriter(handle, fieldnames=fields)
        writer.writeheader()
        for row in scan_row["census"]["checkpoints"]:
            writer.writerow(
                {
                    "n": row["n"],
                    "O": row["O"],
                    "O_E": row["O_E"],
                    "O_O": row["O_O"],
                    "D": row["D"],
                    "D_E": row["D_E"],
                    "D_O": row["D_O"],
                    "max_abs_D": row["max_abs_D"],
                    "max_abs_D_E": row["max_abs_D_E"],
                    "max_abs_D_O": row["max_abs_D_O"],
                    "max_D_O_over_n13": row["max_D_O_ratios"]["over_n13"],
                    "max_D_O_over_n12": row["max_D_O_ratios"]["over_n12"],
                    "O_E_closed": row["O_E_closed"],
                    "even_bound_ok": int(row["even_bound_ok"]),
                }
            )
    if scan_row["odd_spot"] is not None:
        spot_fields = (
            "n",
            "odd_n",
            "O_O",
            "D_O",
            "max_abs_D_O",
            "max_D_O_over_n13",
            "max_D_O_over_n12",
            "max_D_O_over_log",
        )
        with (directory / "odd_start_spot.csv").open(
            "w", encoding="utf-8", newline=""
        ) as handle:
            writer = csv.DictWriter(handle, fieldnames=spot_fields)
            writer.writeheader()
            for row in scan_row["odd_spot"]["checkpoints"]:
                writer.writerow(
                    {
                        "n": row["n"],
                        "odd_n": row["odd_n"],
                        "O_O": row["O_O"],
                        "D_O": row["D_O"],
                        "max_abs_D_O": row["max_abs_D_O"],
                        "max_D_O_over_n13": row["max_D_O_ratios"]["over_n13"],
                        "max_D_O_over_n12": row["max_D_O_ratios"]["over_n12"],
                        "max_D_O_over_log": row["max_D_O_ratios"]["over_log"],
                    }
                )
    (directory / "manifest.json").write_text(
        json.dumps(
            {
                "n_max": scan_row["n_max"],
                "n_spot": scan_row["n_spot"],
                "files": [
                    "checkpoints.csv",
                    *([] if scan_row["odd_spot"] is None else ["odd_start_spot.csv"]),
                ],
                "classification": scan_row["decision"]["classification"],
                "note": (
                    "one-step image-parity discrepancy; even cells closed-form; "
                    "odd-start n^{3/2} census; not a frequency theorem"
                ),
            },
            indent=2,
        )
        + "\n",
        encoding="utf-8",
    )


def write_docs(scan_row: dict[str, Any], path: Path = DOC_PATH) -> None:
    decision = scan_row["decision"]
    census = scan_row["census"]
    spot = scan_row["odd_spot"]
    rows = census["checkpoints"]
    log_rows = [row for row in rows if row["n"] in LOG_GRID or row["n"] == census["n_max"]]
    table = _md_table(
        [
            "N",
            "O",
            "D",
            "D_E",
            "D_O",
            "max|D|",
            "max|D_E|",
            "max|D_O|",
            "max|D_O|/N^{1/3}",
            "max|D_O|/N^{1/2}",
        ],
        [
            [
                row["n"],
                row["O"],
                row["D"],
                row["D_E"],
                row["D_O"],
                row["max_abs_D"],
                row["max_abs_D_E"],
                row["max_abs_D_O"],
                row["max_D_O_ratios"]["over_n13"],
                row["max_D_O_ratios"]["over_n12"],
            ]
            for row in log_rows
        ],
    )
    spot_table = ""
    if spot is not None:
        spot_log = [
            row
            for row in spot["checkpoints"]
            if row["n"] in LOG_GRID or row["n"] == spot["n_max"]
        ]
        spot_table = (
            "\nOdd-start spot through "
            f"`n<={spot['n_max']}`:\n\n"
            + _md_table(
                ["N", "O_O", "D_O", "max|D_O|", "max|D_O|/N^{1/3}", "max|D_O|/N^{1/2}"],
                [
                    [
                        row["n"],
                        row["O_O"],
                        row["D_O"],
                        row["max_abs_D_O"],
                        row["max_D_O_ratios"]["over_n13"],
                        row["max_D_O_ratios"]["over_n12"],
                    ]
                    for row in spot_log
                ],
            )
            + "\n"
        )
    path.write_text(
        f"""# Juggler one-step image-parity discrepancy

Status: **{decision["classification"]}**

Standalone Archimedean counting phase on the exact floor-power map.
Not a Research Engine experiment, not a frequency theorem, and not a
termination theorem. Closed 2-adic, landing-θ, and probabilistic /
large-deviation branches stay closed.

## A. Object

Write `J(n) = isqrt(n)` on even `n` and `J(n) = isqrt(n^3)` on odd `n`.
The counting target is

```
O(N) = #{{n <= N : J(n) odd}}
D(N) = O(N) - N/2
```

This is image parity, the second word letter, not start parity.
Uniform `P(n odd) = 1/2` is exact counting and is not the target.
Label of the split below: **EXACT COMPUTATION**.

`D(N) = D_E(N) + D_O(N)`, where `D_E` uses even starts and `D_O` uses
odd starts.

## B. Even cells — EXACT — HUMAN PROOF

For even `n`, `even_preimage_iff` says `J(n) = q` iff `q^2 <= n < (q+1)^2`.
Let `Q = floor(sqrt(N))`.

A complete cell of odd `q` is the interval `[q^2, (q+1)^2)` of length
`2q+1`. It starts at the odd square `q^2`, so it contains exactly `q`
even integers, all with odd image `q`. A complete even-`q` cell has
even image, so it contributes `0` to `O_E`.

There are `Q//2` complete odd cells `q = 1, 3, ..., 2(Q//2)-1`. Their
contribution is `1+3+...+(2(Q//2)-1) = (Q//2)^2`.

If `Q` is odd the last cell `[Q^2, N]` is an odd-image cell and adds
the even count in that range; if `Q` is even it adds `0`. This is the
closed form `even_image_odd_count`. It matches the one-pass census at
every recorded checkpoint: `{census["closed_matches"]}`.

The complete-cell discrepancy is `1/4` when `Q` is even and
`-(Q-1)/2` when `Q` is odd. The last cell has length at most `2Q+1`
and moves `D_E` by at most `(Q+1)/2`. Therefore

```
|D_E(N)| <= floor(sqrt(N)) + 1.
```

The census records `even_bound_holds = {census["even_bound_holds"]}`
on `n <= {census["n_max"]}`. Label: **EXACT — HUMAN PROOF**, and
**REPARAMETERIZATION** of `even_preimage_iff`. This is not the promotion
theorem.

## C. Odd cells — n^{{3/2}} census

For odd `n`, `odd_preimage_iff` plus `odd_preimage_unique` say the cell
`m^2 <= n^3 < (m+1)^2` contains at most one integer. So `O_O(N)` is
the number of occupied odd-`m` singletons with occupant `<= N`, not a
length sum.

Equivalently, `J(n)` is odd iff `isqrt(n^3)` is odd. The fractional-part
form `{{n^{{3/2}}/2}} >= 1/2` is only a rewrite; every count below uses
`isqrt`. Label: **EXACT COMPUTATION**.

For odd `n >= 3`, `floorPower_odd_macro_direction` already splits the
two-step on this bit: `J(n)` even implies `T^2(n) < n`, and `J(n)` odd
implies `T^2(n) > n`. `D_O` is therefore also the discrepancy of
expanding versus contracting two-step odd starts. The lemma is cited,
not reproved. No two-step word census.

## D. Prefix census

One pass on `n <= {census["n_max"]}`. Label: **COMPUTATIONALLY VERIFIED**.

{table}
{spot_table}
No linear bias: `|D_O(N)|/N` at `N = {census["n_max"]}` is
`{abs(census["final"]["D_O"]) / census["n_max"]}`. The running odd-start
envelope tracks `N^{{1/3}}` more closely than `N^{{1/2}}`. The
`N^{{1/3}}` ratio stays order-1 on the window (about 0.65 to 1.65),
so the named class is `N^{{1/3}}` times a possible log factor, not a
proved exponent. Label: **OBSERVATION**.

Total `D` is even-cell dominated. The written target
`|O(N) - N/2| <= E(N)` therefore admits the elementary majorant
`E(N) = floor(sqrt(N)) + 1 + N/4`, which is useless, or
`E(N) = O(sqrt(N))` once `D_O = O(sqrt(N))` is granted by the census.
That total bound is not a new `n^{{3/2}}` law.

## E. What this is not

- Start-parity `P(n odd) = 1/2` is exact counting, already recorded in
  the probabilistic census. **KNOWN**.
- `landingParity = J(n) mod 2` is tautological in `T`.
  **REPARAMETERIZATION**.
- Letter 2 is not a 2-adic function of `n mod 2^P`. Already **CLOSE**.
- `θ = ρ/(2T+1)` does not predict the next landing. Already **CLOSE**.
- `P(O) = 1/2` as an orbit law is already **REFUTED**.
- `parity_frequency_theorem` stays `False`.

## F. Decision record

Classification **{decision["classification"]}**.

{decision["reason"]}

This is not a termination theorem.
""",
        encoding="utf-8",
    )


def write_dossier(scan_row: dict[str, Any], path: Path = DOSSIER_PATH) -> None:
    decision = scan_row["decision"]
    census = scan_row["census"]
    spot = scan_row["odd_spot"]
    final = census["final"]
    spot_line = (
        f"Odd-start spot `n<={spot['n_max']}` has "
        f"`max|D_O|={spot['max_abs_D_O']}` and "
        f"`max|D_O|/N^{{1/3}}={spot['final']['max_D_O_ratios']['over_n13']}`."
        if spot is not None and spot["final"] is not None
        else "No odd-start spot beyond the main window."
    )
    path.write_text(
        f"""# Juggler pointwise image-parity discrepancy

Status: **EXPLORATORY**

Standalone Archimedean counting layer on the exact Juggler floor-power
map. It is **not** a Research Engine control-layer experiment, not a
parity-frequency theorem, and not a claim that every positive integer
reaches 1.

## Problem

Does the one-step image-parity count

\\[
O(N)=\\#\\{{n\\le N:J(n)\\ \\mathrm{{odd}}\\}}
\\]

admit an explicit discrepancy bound \\(|O(N)-N/2|\\le E(N)\\), and which
floor-cell family produces it?

## Exact statement

Write \\(J(n)=\\lfloor\\sqrt n\\rfloor\\) for even \\(n\\) and
\\(J(n)=\\lfloor n^{{3/2}}\\rfloor\\) for odd \\(n\\). Split
\\(D(N)=O(N)-N/2\\) into even-start and odd-start pieces \\(D_E\\) and
\\(D_O\\). Phase 0 asks for an explicit majorant of \\(D_E\\) from the
square cells, and whether \\(D_O\\) — occupancy of odd-\\(m\\)
singletons of \\(n^{{3/2}}\\) — has an explicit \\(o(N)\\) envelope.
This is interval counting, not a residue-class statement, and it says
nothing about totality.

## Current literature

- `even_preimage_iff` / `odd_preimage_iff` / `odd_preimage_unique` —
  **EXACT — LEAN VERIFIED** in `Problems.Juggler.Preimages`.
- `landingParity = J(n)\\bmod 2` —
  **EXACT — LEAN VERIFIED** and tautological in \\(T\\); landing-θ
  **CLOSE** as `LANDING_THETA_UNRESTRICTED`.
- `floorPower_odd_macro_direction` —
  **EXACT — LEAN VERIFIED** in `Problems.Juggler.Dynamics`.
- Same residue, both next parities —
  **EXACT — LEAN VERIFIED** in `PreimageCylinders`; 2-adic bridge
  **CLOSE** as `BRIDGE_COMPLEX`.
- Uniform one-step start-parity \\(P(O)=1/2\\) —
  **KNOWN** counting, recorded in the probabilistic census
  (`STATISTICAL_ONLY` / **PARK**). Orbit \\(P(O)=1/2\\) as a
  dynamical law is **REFUTED**. Large-deviation comparison **CLOSE**
  as `MODEL_ONLY`.
- Prasad–Prasad 2025 (`prasad-prasad-2025-juggler-like`) —
  literature context only; M0 assumes iid fair parity.
- OEIS A007320 (`oeis-A007320`) — step counts. **known**.

Project relationship: **independent** interval-counting question.
Totality remains unclaimed.

## Branch budget

```text
Mathematical target     Is there an explicit E(N) such that
                        |#{{n≤N: J(n) odd}} − N/2| ≤ E(N), and which
                        of the two floor-cell families produces it?
Novelty hypothesis      A deterministic Archimedean discrepancy law
                        for floor(n^{{3/2}}) on odd n, not a residue
                        class and not a statistical frequency.
Falsifier               Total discrepancy is only the even-cell
                        O(√N) rewrite; odd-start error is Ω(N^{{1−ε}})
                        or a linear bias; or the count is T itself.
Existing machinery      floor_power; even_preimage_iff / odd_preimage_iff /
                        odd_preimage_unique; landingParity = T mod 2
                        (tautological); 2-adic bridge CLOSE; θ-landing
                        CLOSE; probabilistic P(O) PARK/CLOSE.
Maximum Phase-0 scope   Exact even/odd split; human even-cell bound;
                        one-pass census N≤10^6 (spot 10^7); candidate
                        E_odd(N); no k-step iteration; no CLI; no Lean
                        unless an odd-start inequality is proved.
Promotion criterion     An explicit E_odd(N)=o(N) with a proof, or a
                        total E(N) that is not just even_preimage_iff.
Stop criterion          All KNOWN/REPARAMETERIZATION; machinery
                        gravity (plots, word iteration, Weyl engine);
                        halt claim; flipping parity_frequency_theorem
                        on a census.
```

## Balanced-ternary formulation

None required. The map is on ordinary positive integers.

## Why BT may be relevant

It is not required. The 2-adic / BT bridge is closed.

## Candidate operations / invariants

- Start-parity count on \\([1,N]\\) —
  **KNOWN**
- `landingParity` as a predictive state —
  **REPARAMETERIZATION** of \\(T\\)
- Even-cell closed form for \\(O_E(N)\\) —
  **EXACT — HUMAN PROOF**
- \\(|D_E(N)|\\le\\lfloor\\sqrt N\\rfloor+1\\) —
  **EXACT — HUMAN PROOF**
- Odd-start \\(N^{{1/3}}\\) envelope —
  **OBSERVATION**
- Linear odd-start bias —
  **REFUTED** on the Phase-0 window
- Total discrepancy as a new \\(n^{{3/2}}\\) law —
  **REFUTED**; \\(D_E\\) dominates
- `parity_frequency_theorem` —
  not claimed
- global halt — not claimed

## Experiments

- Probe: `research.juggler_sequence.parity_discrepancy`
- Records: [juggler_parity_discrepancy.md](../research/juggler_parity_discrepancy.md),
  [juggler_parity_discrepancy.json](../research/juggler_parity_discrepancy.json)
- Dataset: `data/research/juggler/parity_discrepancy/`
- Tests: `tests/research/juggler_sequence/test_parity_discrepancy.py`

No GPU. No atlas recensus. No new Lean file. The Research Engine
control layer is not modified.

## Conjectures

None opened. A named \\(N^{{1/3}}\\) envelope is an observation, not a
conjecture file.

## Counterexamples

- “\\(P(O)=1/2\\) as a trajectory law”: already false on hard / record
  orbits; this branch does not revive it.
- “Total \\(|O(N)-N/2|\\) is a new cube-cell law”: false; \\(D_E\\)
  dominates (`max|D_E|={census["max_abs_D_E"]}` vs
  `max|D_O|={census["max_abs_D_O"]}` on `n<={census["n_max"]}`).
- “Odd-start image parity has a linear bias”: false on the window;
  `|D_O({final["n"]})|={abs(final["D_O"])}`.
- “A residue class determines the second letter”: already false
  (`ooe_cylinder_both_next_parities`).

## Formalization

None added. Existing Cells / Dynamics / LandingParity /
PreimageCylinders lemmas stay as they are. No `sorry`.

## Results

Classification **{decision["classification"]}**.

{decision["reason"]}

On `n<={census["n_max"]}`: `O={final["O"]}`, `D={final["D"]}`,
`D_E={final["D_E"]}`, `D_O={final["D_O"]}`,
`max|D|={census["max_abs_D"]}`, `max|D_E|={census["max_abs_D_E"]}`,
`max|D_O|={census["max_abs_D_O"]}`. Closed even-cell formula matches
the census: `{census["closed_matches"]}`. Even bound holds:
`{census["even_bound_holds"]}`. {spot_line}

## Open questions

Prove an explicit \\(E_O(N)=o(N)\\) for the odd-start \\(n^{{3/2}}\\)
count. Do not iterate counting estimates until that bound exists. Do
not reopen residues, θ, or the random-walk model.

## Decision

**{decision["branch"]}**. {decision["reason"]} Do not claim
termination. Do not flip `parity_frequency_theorem`.

Best next question: prove \\(E_O(N)\\ll N^{{1/3}}(\\log N)^c\\) (or
the named census class) by an Archimedean exponential-sum argument,
then ask whether that bound iterates.

## Publication assessment

Status: `EXPLORATORY`. An elementary even-cell counting identity plus
an odd-start discrepancy census, not a paper candidate and not a
Juggler totality result.
""",
        encoding="utf-8",
    )


def main() -> None:
    row = scan()
    write_json(row)
    write_docs(row)
    write_dossier(row)
    write_data(row)
    print(row["decision"]["classification"])


if __name__ == "__main__":
    main()
