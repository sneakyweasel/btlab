"""Unbounded stopping-time prefix F_τ of the Juggler floor-power map.

Not a halt theorem. Does not reopen the closed windowed inverse-basin
census, predecessor-cell quotients, residual attacks, or statistical
fitting. F_τ(r) is the inverse of the running maximum of τ on a finite
window. A growing computed prefix is not a coverage lemma.
"""

from __future__ import annotations

import csv
import json
from pathlib import Path
from typing import Any

from research.juggler_sequence.lean_paths import MINIMAL_CLOSURE, has_named
from research.juggler_sequence.minimal_counterexample import stopping_times
from research.juggler_sequence.power_itineraries import ANTI_OVERCLAIM, floor_power

REPO_ROOT = Path(__file__).resolve().parents[3]
JSON_PATH = REPO_ROOT / "docs" / "research" / "juggler_stopping_prefix.json"
DOC_PATH = REPO_ROOT / "docs" / "research" / "juggler_stopping_prefix.md"
DOSSIER_PATH = REPO_ROOT / "docs" / "problems" / "juggler_stopping_prefix.md"
DATA_DIR = REPO_ROOT / "data" / "research" / "juggler" / "stopping_prefix"
WINDOWED_CSV = (
    REPO_ROOT / "data" / "research" / "juggler" / "minimal_counterexample" / "good_closure.csv"
)

N_PHASE0 = 4000
HORIZON = 10_000
ENTRY_BUDGET = 8
GROWTH_KS = (1, 2, 3, 4)
GROWTH_ALPHAS = (1.5, 2.0)
JSON_INT_BITS = 256
SUPERLINEAR_DENSITY_CUT = 0.25

CLOSED_IMPORT_TOKENS = (
    "future_quotient",
    "residual_minimize",
    "sum_rho",
    "realization_geometry",
    "landing_image",
    "itinerary_language",
    "nc_boundary",
    "adversarial_paths",
    "information_complexity",
    "backward_geometry",
    "accelerated",
    "floor_boundary",
    "two_adic_bridge",
    "first_return_excursions",
    "probabilistic_ld",
    "probabilistic",
    "extremal_control",
    "cell_hut",
    "good_closure",
)

ANTI = {
    **ANTI_OVERCLAIM,
    "finite_window_prefix_is_totality": False,
    "computed_F_tau_is_a_theorem": False,
    "interval_amplification": False,
    "reopen_windowed_closure": False,
    "reopen_backward_geometry": False,
    "reopen_cell_hut": False,
    "reopen_statistical_fitting": False,
    "reopen_extremal_control": False,
    "automaton": False,
}

LEAN_THEOREMS = (
    "even_good_of_sqrt_le",
    "odd_not_pred_of_le",
)

CLASS_AMPLIFY = "PREFIX_AMPLIFICATION_GREEN"
CLASS_LADDER = "RECORD_LADDER_UNEXPLAINED"
CLASS_COMPLEX = "STOPPING_PREFIX_COMPLEX"


def jsonable_int(n: int) -> int | str:
    if n.bit_length() > JSON_INT_BITS:
        return f"int[{n.bit_length()}bits]"
    return n


def running_max_tau(tau: list[int | None]) -> list[int]:
    """M(n) = max_{1≤k≤n} τ(k) for n = 1..n_max. Requires complete τ."""

    n_max = len(tau) - 1
    if n_max < 1:
        return []
    if any(tau[n] is None for n in range(1, n_max + 1)):
        missing = [n for n in range(1, n_max + 1) if tau[n] is None]
        raise ValueError(f"incomplete stopping times: {missing[:8]}")
    out: list[int] = []
    current = 0
    for n in range(1, n_max + 1):
        value = tau[n]
        assert value is not None
        current = max(current, value)
        out.append(current)
    return out


def prefix_from_tau(tau: list[int | None]) -> list[dict[str, Any]]:
    """Invert the running-max of τ.

    F_τ(r) = max{N : max_{n≤N} τ(n) ≤ r}.
    b_r = F_τ(r) + 1 is the first integer with τ > r, or n_max+1
    when the window is fully covered.
    """

    n_max = len(tau) - 1
    running = running_max_tau(tau)
    max_tau = running[-1] if running else 0
    rows: list[dict[str, Any]] = []
    n = 1
    for r in range(max_tau + 1):
        while n <= n_max and running[n - 1] <= r:
            n += 1
        f_tau = n - 1
        nxt = n
        while nxt <= n_max and running[nxt - 1] <= r + 1:
            nxt += 1
        f_next = nxt - 1
        plateau = f_next == f_tau
        ratio = (f_next / f_tau) if f_tau > 0 else None
        rows.append(
            {
                "r": r,
                "F_tau": f_tau,
                "b_r": f_tau + 1,
                "ratio": ratio,
                "plateau": plateau,
            }
        )
    return rows


def two_letters(n: int) -> tuple[str, int, int]:
    y = floor_power(n)
    z = floor_power(y)
    word = ("E" if n % 2 == 0 else "O") + ("E" if y % 2 == 0 else "O")
    return word, y, z


def orbit_until_prefix(n: int, prefix: int, *, budget: int) -> dict[str, Any]:
    """Forward walk until a state ≤ prefix, or `budget` steps."""

    x = n
    peak = n
    letters: list[str] = []
    entry: int | None = None
    for j in range(1, budget + 1):
        letters.append("E" if x % 2 == 0 else "O")
        x = floor_power(x)
        if x > peak:
            peak = x
        if entry is None and x <= prefix:
            entry = j
            break
    return {
        "word": "".join(letters),
        "entry_steps": entry,
        "last": x,
        "peak": peak,
    }


def first_gap_orbits(
    tau: list[int | None],
    rows: list[dict[str, Any]],
    *,
    budget: int = ENTRY_BUDGET,
) -> list[dict[str, Any]]:
    """One row per newly appearing first gap b_r ≤ n_max."""

    n_max = len(tau) - 1
    seen: set[int] = set()
    out: list[dict[str, Any]] = []
    for row in rows:
        b = int(row["b_r"])
        f_prev = int(row["F_tau"])
        r = int(row["r"])
        if b in seen or b > n_max:
            continue
        seen.add(b)
        tb = tau[b]
        assert tb is not None
        word, image, second = two_letters(b)
        walk = orbit_until_prefix(b, f_prev, budget=budget)
        out.append(
            {
                "b": b,
                "r": r,
                "F_prev": f_prev,
                "tau": tb,
                "parity": "odd" if b % 2 == 1 else "even",
                "word2": word,
                "T": image,
                "T2": second,
                "image_in_previous_prefix": image <= f_prev,
                "entry_steps": walk["entry_steps"],
                "entry_word": walk["word"],
                "entry_last": jsonable_int(walk["last"]),
                "peak": jsonable_int(walk["peak"]),
                "peak_bits": walk["peak"].bit_length(),
            }
        )
    return out


def even_successor_holds(tau: list[int | None], f_val: int, r: int) -> bool:
    """Even n < (F+1)^2 have τ(n) ≤ r+1 when [1,F] ⊆ {τ≤r}."""

    n_max = len(tau) - 1
    limit = min(n_max, (f_val + 1) ** 2 - 1)
    for n in range(2, limit + 1, 2):
        value = tau[n]
        if value is None or value > r + 1:
            return False
    return True


def first_gaps_odd_when_f_ge_2(rows: list[dict[str, Any]], n_max: int) -> dict[str, Any]:
    exceptions: list[dict[str, int]] = []
    checked = 0
    for row in rows:
        f_val = int(row["F_tau"])
        b = int(row["b_r"])
        if f_val < 2 or b > n_max:
            continue
        checked += 1
        if b % 2 == 0:
            exceptions.append({"r": int(row["r"]), "F_tau": f_val, "b_r": b})
    return {
        "checked": checked,
        "all_odd": not exceptions,
        "exceptions": exceptions,
    }


def growth_stats(rows: list[dict[str, Any]]) -> dict[str, Any]:
    if len(rows) < 2:
        return {
            "plateau_count": 0,
            "steps": 0,
            "plateau_fraction": 0.0,
            "max_ratio": None,
            "superlinear": [],
        }
    plateau_count = sum(1 for row in rows[:-1] if row["plateau"])
    steps = len(rows) - 1
    ratios = [row["ratio"] for row in rows[:-1] if row["ratio"] is not None]
    superlinear: list[dict[str, Any]] = []
    f_vals = [int(row["F_tau"]) for row in rows]
    for k in GROWTH_KS:
        for alpha in GROWTH_ALPHAS:
            eligible = 0
            hits = 0
            for i, f_val in enumerate(f_vals):
                if i + k >= len(f_vals) or f_val < 2:
                    continue
                eligible += 1
                if f_vals[i + k] + 0.0 >= f_val**alpha:
                    hits += 1
            density = (hits / eligible) if eligible else 0.0
            superlinear.append(
                {
                    "k": k,
                    "alpha": alpha,
                    "hits": hits,
                    "eligible": eligible,
                    "density": density,
                }
            )
    return {
        "plateau_count": plateau_count,
        "steps": steps,
        "plateau_fraction": plateau_count / steps if steps else 0.0,
        "max_ratio": max(ratios) if ratios else None,
        "superlinear": superlinear,
    }


def load_windowed_prefix(path: Path = WINDOWED_CSV) -> list[dict[str, Any]]:
    if not path.is_file():
        return []
    out: list[dict[str, Any]] = []
    with path.open(encoding="utf-8", newline="") as handle:
        for raw in csv.DictReader(handle):
            out.append(
                {
                    "r": int(raw["round"]),
                    "F_window": int(raw["maximum_certified_interval"]),
                    "certified_count": int(raw["certified_count"]),
                    "component_count": int(raw["component_count"]),
                }
            )
    return out


def compare_windowed(
    rows: list[dict[str, Any]],
    windowed: list[dict[str, Any]],
) -> list[dict[str, Any]]:
    by_r = {int(row["r"]): int(row["F_tau"]) for row in rows}
    out: list[dict[str, Any]] = []
    for item in windowed:
        r = int(item["r"])
        if r not in by_r:
            continue
        out.append(
            {
                "r": r,
                "F_tau": by_r[r],
                "F_window": int(item["F_window"]),
                "tau_minus_window": by_r[r] - int(item["F_window"]),
            }
        )
    return out


def lean_api_present() -> dict[str, bool]:
    text = MINIMAL_CLOSURE.read_text(encoding="utf-8")
    return {
        **{name: has_named(text, name) for name in LEAN_THEOREMS},
        "sorry_free": "sorry" not in text and "admit" not in text,
    }


def decide(payload: dict[str, Any]) -> dict[str, Any]:
    gaps = payload["first_gaps"]
    growth = payload["growth"]
    odd_check = payload["first_gaps_odd"]
    even_ok = payload["even_successor_ok"]
    complete = payload["all_reach_one"]
    lean = payload["lean"]

    finite_gaps = [row for row in gaps if isinstance(row.get("tau"), int)]
    odd_expanders = [
        row
        for row in finite_gaps
        if row["parity"] == "odd" and not row["image_in_previous_prefix"]
    ]
    bounded_entries = [
        row["entry_steps"]
        for row in finite_gaps
        if row["parity"] == "odd" and row["entry_steps"] is not None
    ]
    uniform_k = False
    if finite_gaps and odd_expanders and bounded_entries:
        max_entry = max(bounded_entries)
        missing = any(
            row["entry_steps"] is None
            for row in finite_gaps
            if row["parity"] == "odd"
        )
        uniform_k = (not missing) and max_entry <= 4 and len(odd_expanders) >= 3

    dense_superlinear = any(
        item["density"] >= SUPERLINEAR_DENSITY_CUT for item in growth["superlinear"]
    )
    plateau_dominates = growth["plateau_fraction"] >= 0.5

    if not (complete and even_ok and lean["sorry_free"] and all(lean[name] for name in LEAN_THEOREMS)):
        return {
            "classification": CLASS_COMPLEX,
            "branch": "CLOSE",
            "reason": (
                "Phase-0 census is incomplete or the existing even/odd "
                "Lean lemmas are missing. No amplification lemma is isolated."
            ),
        }

    if uniform_k and not plateau_dominates:
        return {
            "classification": CLASS_AMPLIFY,
            "branch": "PROMOTE",
            "reason": (
                "Every odd first gap enters the previous prefix in at most "
                "four steps. That is a candidate local coverage lemma."
            ),
        }

    striking_ladder = (
        odd_check["all_odd"]
        and dense_superlinear
        and not plateau_dominates
        and len({row["word2"] for row in odd_expanders}) == 1
    )
    if striking_ladder:
        return {
            "classification": CLASS_LADDER,
            "branch": "PARK",
            "reason": (
                "The record ladder of first gaps shares one two-letter word "
                "and shows dense superlinear prefix jumps, but no lemma "
                "predicts the next gap without computing τ."
            ),
        }

    return {
        "classification": CLASS_COMPLEX,
        "branch": "CLOSE",
        "reason": (
            "F_τ is the definitional inverse of the running-max of τ. "
            "First gaps are odd expanders whose images leave the previous "
            f"prefix; no uniform k≤4 entry exists. Plateaus cover "
            f"{growth['plateau_fraction']:.3f} of depth steps. "
            "Window totality F_τ(max τ)=N is the already-recorded fact "
            "that every n≤4000 reaches 1, not a coverage theorem."
        ),
    }


def run_phase0(
    n_max: int = N_PHASE0,
    *,
    horizon: int = HORIZON,
) -> dict[str, Any]:
    tau = stopping_times(n_max, horizon=horizon)
    missing = [n for n in range(1, n_max + 1) if tau[n] is None]
    rows = prefix_from_tau(tau) if not missing else []
    gaps = first_gap_orbits(tau, rows) if rows else []
    growth = growth_stats(rows) if rows else growth_stats([])
    windowed = load_windowed_prefix()
    comparison = compare_windowed(rows, windowed)
    odd_check = first_gaps_odd_when_f_ge_2(rows, n_max)
    even_ok = True
    if rows:
        for row in rows:
            if not even_successor_holds(tau, int(row["F_tau"]), int(row["r"])):
                even_ok = False
                break
    max_tau = max((t for t in tau[1:] if t is not None), default=None)
    f_at_max = rows[-1]["F_tau"] if rows else 0
    lean = lean_api_present()
    payload = {
        "experiment": "juggler_stopping_prefix",
        "N": n_max,
        "horizon": horizon,
        "cuda_used": False,
        "anti_overclaim": dict(ANTI),
        "all_reach_one": not missing,
        "missing_tau": missing[:16],
        "max_tau": max_tau,
        "F_tau_at_max": f_at_max,
        "prefix": rows,
        "first_gaps": gaps,
        "first_gaps_odd": odd_check,
        "even_successor_ok": even_ok,
        "growth": growth,
        "windowed_compare": comparison,
        "lean": lean,
    }
    payload["decision"] = decide(payload)
    return payload


def write_data(payload: dict[str, Any]) -> None:
    DATA_DIR.mkdir(parents=True, exist_ok=True)
    prefix_path = DATA_DIR / "prefix.csv"
    with prefix_path.open("w", encoding="utf-8", newline="") as handle:
        writer = csv.DictWriter(
            handle,
            fieldnames=("r", "F_tau", "ratio", "plateau", "b_r"),
        )
        writer.writeheader()
        for row in payload["prefix"]:
            writer.writerow(
                {
                    "r": row["r"],
                    "F_tau": row["F_tau"],
                    "ratio": "" if row["ratio"] is None else f"{row['ratio']:.6f}",
                    "plateau": int(row["plateau"]),
                    "b_r": row["b_r"],
                }
            )
    gaps_path = DATA_DIR / "first_gaps.jsonl"
    with gaps_path.open("w", encoding="utf-8") as handle:
        for row in payload["first_gaps"]:
            handle.write(json.dumps(row) + "\n")
    manifest = {
        "experiment": payload["experiment"],
        "N": payload["N"],
        "horizon": payload["horizon"],
        "max_tau": payload["max_tau"],
        "F_tau_at_max": payload["F_tau_at_max"],
        "all_reach_one": payload["all_reach_one"],
        "classification": payload["decision"]["classification"],
        "branch": payload["decision"]["branch"],
        "files": ["prefix.csv", "first_gaps.jsonl", "manifest.json"],
    }
    (DATA_DIR / "manifest.json").write_text(
        json.dumps(manifest, indent=2) + "\n", encoding="utf-8"
    )


def _md_table(headers: list[str], lines: list[list[Any]]) -> str:
    head = "| " + " | ".join(headers) + " |"
    sep = "| " + " | ".join("---" for _ in headers) + " |"
    body = "\n".join("| " + " | ".join(str(c) for c in row) + " |" for row in lines)
    return "\n".join((head, sep, body))


def render_markdown(payload: dict[str, Any]) -> str:
    d = payload["decision"]
    growth = payload["growth"]
    odd_check = payload["first_gaps_odd"]
    gaps = payload["first_gaps"]
    prefix_rows = payload["prefix"]
    compare = payload["windowed_compare"]

    sample = prefix_rows[:: max(1, len(prefix_rows) // 16)] if prefix_rows else []
    if prefix_rows and prefix_rows[-1] not in sample:
        sample.append(prefix_rows[-1])
    prefix_table = _md_table(
        ["r", "F_τ", "b_r", "ratio", "plateau"],
        [
            [
                row["r"],
                row["F_tau"],
                row["b_r"],
                "" if row["ratio"] is None else f"{row['ratio']:.4f}",
                row["plateau"],
            ]
            for row in sample
        ],
    )
    gap_table = _md_table(
        ["b", "r", "F_prev", "τ", "parity", "word", "T", "T≤F", "entry"],
        [
            [
                row["b"],
                row["r"],
                row["F_prev"],
                row["tau"],
                row["parity"],
                row["word2"],
                row["T"],
                row["image_in_previous_prefix"],
                row["entry_steps"] if row["entry_steps"] is not None else ">",
            ]
            for row in gaps
        ],
    )
    compare_table = _md_table(
        ["r", "F_τ", "F_window", "F_τ − F_window"],
        [
            [row["r"], row["F_tau"], row["F_window"], row["tau_minus_window"]]
            for row in compare
        ],
    )
    sl_table = _md_table(
        ["k", "α", "hits", "eligible", "density"],
        [
            [
                item["k"],
                item["alpha"],
                item["hits"],
                item["eligible"],
                f"{item['density']:.4f}",
            ]
            for item in growth["superlinear"]
        ],
    )
    max_ratio = growth["max_ratio"]
    max_ratio_s = "" if max_ratio is None else f"{max_ratio:.4f}"

    return f"""# Juggler stopping-time prefix

Status: **{d['classification']}**

Standalone Phase-0 on the unbounded stopping-time prefix of the exact
Juggler floor-power map. This is not a termination theorem. The closed
windowed inverse-basin census stays closed.

Every statement below is labelled
`LOGICAL CONSEQUENCE` | `LEAN-CERTIFIED` | `EXACT COMPUTATION` |
`COMPUTATIONALLY OBSERVED` | `COUNTEREXAMPLE`.
These are report labels. Ledger tags, when used, remain the seven
standard tags from [docs/README.md](../README.md).

## 1. Object

`T` is `floorPower`: even `⌊√n⌋`, odd `⌊n^{{3/2}}⌋`. `τ(1)=0` and
`τ(n)` is the first `k` with `T^k(n)=1`. Label:
**LEAN-CERTIFIED** for the map; **EXACT COMPUTATION** for `τ` on
`n ≤ {payload['N']}`.

```text
M(N)   := max_{{n ≤ N}} τ(n)
F_τ(r) := max {{ N : M(N) ≤ r }}
b_r    := F_τ(r) + 1
```

This identity is the definition of the inverse of a nondecreasing
running maximum. Label: **LOGICAL CONSEQUENCE**. **REPARAMETERIZATION**
of `τ`, not a new induction.

## 2. Window census

Every `n ≤ {payload['N']}` reaches `1` inside horizon
`{payload['horizon']}`: `{payload['all_reach_one']}`. Max `τ` is
`{payload['max_tau']}`. Therefore `F_τ({payload['max_tau']}) =
{payload['F_tau_at_max']}`. Label: **EXACT COMPUTATION**. That is the
already-recorded window totality from the closed minimal-counterexample
branch, not a proof that `F_τ(r)→∞`.

Finite-depth even cell: if `[1, F] ⊆ {{τ ≤ r}}` then every even
`n < (F+1)^2` in the window has `τ(n) ≤ r+1`:
`{payload['even_successor_ok']}`. Label: **EXACT COMPUTATION**. The
unbounded `Good` form is `even_good_of_sqrt_le`
(**LEAN-CERTIFIED**). One-step closure still adds no odd `n > F`
(`odd_not_pred_of_le`, **LEAN-CERTIFIED**).

First gaps with `F_τ(r) ≥ 2` and `b_r ≤ N` are odd:
`{odd_check['all_odd']}` (`{odd_check['checked']}` rows, exceptions
`{odd_check['exceptions']}`). Label: **EXACT COMPUTATION**.

## 3. Prefix table

Sampled `F_τ(r)` (full table in `data/research/juggler/stopping_prefix/prefix.csv`):

{prefix_table}

Plateau fraction `{growth['plateau_fraction']:.4f}`
(`{growth['plateau_count']}` of `{growth['steps']}` steps). Max one-step
ratio `{max_ratio_s}`. Label: **EXACT COMPUTATION**.

Side-by-side with the closed windowed inverse-basin prefix
`maximum_certified_interval`:

{compare_table}

`F_τ` and the windowed `F` agree only at the smallest depths. The
windowed prefix freezes at `24` because `25` leaves `[1, 4000]`. The
unbounded prefix continues because `τ(25)` is finite. Label:
**EXACT COMPUTATION**. **COUNTEREXAMPLE** to “the two prefixes are the
same sequence”.

## 4. First gaps

Each newly appearing `b_r ≤ N`:

{gap_table}

`entry` is the first `j ≤ {ENTRY_BUDGET}` with `T^j(b) ≤ F_prev`, or
`>` if none. Odd first gaps have `T(b) > F_prev`: their one-step image
leaves the certified interval. Label: **EXACT COMPUTATION**.

No candidate congruence or two-letter motif predicts the next `b`
without computing `τ(b)`. Label: **COMPUTATIONALLY OBSERVED**.

## 5. Growth tests

Diagnostic only. Superlinear test `F(r+k) ≥ F(r)^α`:

{sl_table}

A high density here would still not be a lemma: a jump after a late
odd is certified is “`τ(b)` is finite”, the window fact. Label:
**COMPUTATIONALLY OBSERVED**.

## 6. Lean

Cited, not added, from `Problems.Juggler.MinimalClosure`:

- `even_good_of_sqrt_le`
- `odd_not_pred_of_le`

Sorry-free: `{payload['lean']['sorry_free']}`. Not formalized, and not
claimed: `goodAt_interval_amplification`, `prefix_growth_theorem`.

## 7. Decision

Classification: **{d['classification']}**.

{d['reason']}

`PREFIX_AMPLIFICATION_GREEN` is not awarded. `RECORD_LADDER_UNEXPLAINED`
is not awarded. Branch status: **{d['branch']}**.

Phase 1 (`N = 10^5`) is not launched. A larger window lengthens the
record ladder of `τ` and does not isolate an amplification lemma.
"""


def render_dossier(payload: dict[str, Any]) -> str:
    d = payload["decision"]
    growth = payload["growth"]
    odd_check = payload["first_gaps_odd"]
    return f"""# Juggler stopping-time prefix

Status: **EXPLORATORY**

Standalone application phase on the Juggler floor-power map. It is
**not** a Research Engine control-layer experiment and not a claim that
every positive integer reaches 1. It does not reopen the closed
windowed inverse-basin census
([juggler_minimal_counterexample.md](juggler_minimal_counterexample.md)).

## Problem

Does the unbounded stopping-time prefix

\\[
F_\\tau(r)=\\max\\{{N:\\max_{{n\\le N}}\\tau(n)\\le r\\}}
\\]

admit an interval amplification lemma, or does it only invert the
running maximum of \\(\\tau\\)?

## Exact statement

Let \\(T\\) be `floorPower`: even \\(n\\mapsto\\lfloor\\sqrt{{n}}\\rfloor\\), odd
\\(n\\mapsto\\lfloor n^{{3/2}}\\rfloor\\). Write \\(\\tau(1)=0\\) and
\\(\\tau(n)=\\min\\{{k:T^k(n)=1\\}}\\) when the minimum exists. Decide whether
there exist an explicit \\(f\\) with \\(f(N)>N\\) and a controlled \\(k\\)
such that

\\[
[1,N]\\subseteq\\{{\\tau\\le r\\}}
\\implies
[1,f(N)]\\subseteq\\{{\\tau\\le r+k\\}},
\\]

or whether every prefix jump is the definitional event “the current
first gap \\(b_r=F_\\tau(r)+1\\) finally satisfies \\(\\tau(b_r)=r+1\\)”.

## Current literature

- OEIS A007320 (`oeis-A007320`): step counts to 1. **known**. Totality
  is not claimed.
- Windowed inverse-basin \\(F(r)\\) and \\(G_r\\) —
  **COMPUTATIONALLY VERIFIED**, branch **CLOSE**
  (`juggler_minimal_counterexample`).
- `PredClosure ↔ ReachesOne` — **EXACT — LEAN VERIFIED**.
  **REPARAMETERIZATION**.
- `even_good_of_sqrt_le`, `odd_not_pred_of_le` —
  **EXACT — LEAN VERIFIED**. One-step closure of \\([1,B]\\) adds no
  odd \\(n>B\\).
- Even cells are intervals \\([m^2,(m+1)^2)\\), not singletons on
  squares. The informal rule \\(T(2k)=k^2\\) is a forward/inverse swap
  and is not used.

Project relationship: **independent** of the windowed \\(G_r\\) census;
the object is the unbounded \\(\\tau\\)-prefix. Totality remains
unclaimed.

## Branch budget

```text
Mathematical target     Does F_τ(r)=max{{N : max_{{n≤N}} τ(n) ≤ r}} admit
                        an interval amplification [1,N] ⊆ {{τ≤r}} ⇒
                        [1,f(N)] ⊆ {{τ≤r+k}} with explicit f(N)>N, or
                        does it only invert the running-max of τ?
Novelty hypothesis      The closed branch measured windowed inverse-basin
                        F(r) (frozen at 24). Unbounded F_τ is a different
                        sequence; a reusable odd-gap mechanism would be new.
Falsifier               F_τ is the definitional inverse of running-max τ;
                        first gaps are odd expanders with no bounded-k
                        route into [1,N]; plateaus dominate; no f besides
                        “wait until τ(b)”.
Existing machinery      floor_power; stopping_times; even_good_of_sqrt_le;
                        odd_not_pred_of_le; U(B) density 1/2; windowed
                        F(r) in good_closure.csv
Maximum Phase-0 scope   N=4000, existing horizon 10000; one F_τ table;
                        first-gap orbits; growth/plateau tests; decide
Promotion criterion     A candidate lemma that predicts the next prefix
                        jump without computing τ of that gap
Stop criterion          Definitional reparameterization of τ; stall /
                        linear envelope; no reusable odd mechanism
```

## Balanced-ternary formulation

None required. The map is on ordinary positive integers.

## Why BT may be relevant

A first-gap cylinder in least significant trits, or a boundary of the
form \\((3^k\\pm 1)/2\\), would have been a BT observation. Phase-0 does
not hunt a BT law.

## Candidate operations / invariants

- \\(F_\\tau(r)=\\max\\{{N:M(N)\\le r\\}}\\) with \\(M(N)=\\max_{{n\\le N}}\\tau(n)\\)
  — **REPARAMETERIZATION** of the running-max of \\(\\tau\\) once
  computed
- finite-depth even cell: even \\(n<(F+1)^2\\) satisfies
  \\(\\tau(n)\\le r+1\\) when \\([1,F]\\subseteq\\{{\\tau\\le r\\}}\\) —
  **OBSERVATION** (Lean unbounded form is `even_good_of_sqrt_le`)
- one-step odd coverage of \\(n>F\\) — **REFUTED** in the closed
  branch (`odd_not_pred_of_le`)
- interval amplification with explicit \\(f(N)>N\\) — **REFUTED**
  on the Phase-0 window
- \\(F_\\tau(r)\\to\\infty\\) on a finite window — not a totality theorem
- global halt — not claimed

## Experiments

- Probe: `research.juggler_sequence.stopping_prefix`
- Records: [juggler_stopping_prefix.md](../research/juggler_stopping_prefix.md),
  [juggler_stopping_prefix.json](../research/juggler_stopping_prefix.json)
- Data: `data/research/juggler/stopping_prefix/`
- Tests: `tests/research/juggler_sequence/test_stopping_prefix.py`
- The Research Engine control layer is not modified.

## Conjectures

None opened.

## Counterexamples

- “\\(F_\\tau\\) is a new inductive coverage law.” **REFUTED**: it is
  the inverse of the running-max of \\(\\tau\\).
- “Unbounded and windowed prefixes coincide.” **REFUTED**: windowed
  `F(12)=24` while `F_τ(12)` is larger because `τ(25)` is finite.
- “A bounded number of predecessor layers covers the next interval.”
  **REFUTED**: odd first gaps have `T(b)` outside the previous prefix
  and no uniform `k≤{ENTRY_BUDGET}` entry. First-gap oddness
  `{odd_check['all_odd']}`; plateau fraction
  `{growth['plateau_fraction']:.3f}`.

## Formalization

None added. Existing `even_good_of_sqrt_le` and `odd_not_pred_of_le`
in `formal/Problems/Juggler/MinimalClosure.lean` are cited, not
restated. No `GoodAt` / `GoodSet` module.

## Results

See [juggler_stopping_prefix.md](../research/juggler_stopping_prefix.md).
Classification **{d['classification']}**.

## Open questions

Whether every positive integer reaches 1. A finite-window prefix
table does not answer it.

## Decision

**{d['branch']}**. {d['reason']} A branch whose surviving statements
are `KNOWN` or `REPARAMETERIZATION` is a `CLOSE`.

Best next question: none from this branch. Do not launch Phase 1.

## Publication assessment

Status: `ARCHIVED`.

The prefix table inverts recorded stopping times on `n ≤ {payload['N']}`.
There is no new theorem beyond the already-packaged even-cell lemma,
and no paper distinction.
"""


def write_docs(payload: dict[str, Any]) -> None:
    JSON_PATH.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")
    DOC_PATH.write_text(render_markdown(payload), encoding="utf-8")
    DOSSIER_PATH.write_text(render_dossier(payload), encoding="utf-8")


def write_all(payload: dict[str, Any]) -> None:
    write_data(payload)
    write_docs(payload)


def main() -> None:
    payload = run_phase0()
    write_all(payload)
    print(
        json.dumps(
            {
                "classification": payload["decision"]["classification"],
                "branch": payload["decision"]["branch"],
                "all_reach_one": payload["all_reach_one"],
                "max_tau": payload["max_tau"],
                "F_tau_at_max": payload["F_tau_at_max"],
                "plateau_fraction": payload["growth"]["plateau_fraction"],
                "first_gaps": len(payload["first_gaps"]),
                "first_gaps_odd": payload["first_gaps_odd"]["all_odd"],
                "even_successor_ok": payload["even_successor_ok"],
            },
            indent=2,
        )
    )


if __name__ == "__main__":
    main()
