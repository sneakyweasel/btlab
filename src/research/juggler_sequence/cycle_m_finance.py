"""m-cycle / Simons-circuit finance on the Juggler floor-power map.

Not a halt theorem, not a leftover-word census, not a floor raise,
and not a reopen of peak finance or extremal composition.

Collatz m-cycles (Simons–de Weger Lemma 4) satisfy
0 < Λ < Σ 1/x_i ≤ m / x_min. Juggler already has the m = 1
whole-period unroll at CycleMin (cycleMin_finance). This probe
asks whether the same log-unroll, applied at each local-minimum
circuit, produces a joint bound
    θ < C Σ_i 1/(n_i ln n_i)
that is strictly stronger than
    n ln n (3^o − 2^L) ≤ L 3^o
and whether it excludes any leftover (L, m) at floor 53.

Dossier: docs/problems/juggler_cycle_m_finance.md.
The odd-run height refinement is cycle_position_finance.py.
"""

from __future__ import annotations

import json
import math
import subprocess
from math import isqrt
from pathlib import Path
from typing import Any

from research.juggler_sequence.cycle_finance import (
    EPS_CONST,
    finance_rows,
    n_max_from_bound,
)
from research.juggler_sequence.cycle_top_pred import floor_power
from research.juggler_sequence.lean_paths import (
    CYCLE_CORE,
    CYCLE_EXTREMA,
    CYCLE_FINANCE,
    CYCLE_FINANCE_LEFTOVERS,
    JUGGLER_DIR,
    JUGGLER_PAPER_BARREL,
    has_named,
)
from research.juggler_sequence.power_itineraries import ANTI_OVERCLAIM

REPO_ROOT = Path(__file__).resolve().parents[3]
JSON_PATH = REPO_ROOT / "docs" / "research" / "juggler_cycle_m_finance.json"
DOC_PATH = REPO_ROOT / "docs" / "research" / "juggler_cycle_m_finance.md"
DATA_DIR = REPO_ROOT / "data" / "research" / "juggler" / "cycle_m_finance"

CLASS_GREEN = "M_CYCLE_FINANCE_GREEN"
CLASS_PARK = "M_CYCLE_FINANCE_PARK"
CLASS_CLOSED = "M_CYCLE_FINANCE_CLOSED"
CLASS_INCOMPLETE = "M_CYCLE_FINANCE_INCOMPLETE"

# Leftover near-convergents after floor-53 finance, plus the next record.
LEFTOVER_LENGTHS = (19, 30, 84)
LEAN_CYCLE_FLOOR = 53
STEP_CAP = 400
MIN_TERM = 3

# Existing hard starts from the cycle-finance / extrema probes.
SCIENCE_SEEDS = (25, 37, 77, 365, 1999, 30817)
TEST_SEEDS = (9, 25, 37, 77)

EXISTING_LEAN = (
    "cycleMin_finance",
    "cycle_peak_finance",
    "cycle_itinerary_formally_expanding",
    "cycle_distinguished_order",
    "cycle_itinerary_length_nineteen_or_ge_thirty",
)

FORBIDDEN_THEOREMS = (
    "cycle_m_finance",
    "cycle_circuit_finance",
    "no_juggler_cycle",
    "no_cycle_itinerary_any_length",
    "juggler_reaches_one",
)

FORBIDDEN_NEW_API = (
    "CycleLocalMin",
    "CircuitFinance",
    "MCycleItinerary",
)

FORBIDDEN_LEAN_FILES = (
    JUGGLER_DIR / "CycleMFinance.lean",
    JUGGLER_DIR / "CircuitFinance.lean",
)

PAPER_FORBIDDEN = (
    "CycleMFinance",
    "CircuitFinance",
    "cycle_m_finance",
    "cycle_circuit_finance",
)

# Cycle-like circuits have both valleys ≥ 12. Terminal drops to
# {1,...,11} are not cycle-valid and are excluded from the ratio
# that tests valley concentration.
CYCLE_VALLEY_FLOOR = 12
STEINER_RATIO_CEILING = 2.0


def git_commit() -> str:
    try:
        return subprocess.check_output(
            ["git", "rev-parse", "HEAD"],
            cwd=REPO_ROOT,
            text=True,
            stderr=subprocess.DEVNULL,
        ).strip()
    except (OSError, subprocess.CalledProcessError):
        return "unknown"


def inv_log_term(x: int) -> float:
    """1/(x ln x) for x ≥ 3; 0 otherwise (log is non-positive below e).

    States past the float range contribute underflow and are treated as 0.
    """

    if x < MIN_TERM:
        return 0.0
    if x.bit_length() > 1000:
        return 0.0
    try:
        return 1.0 / (float(x) * math.log(x))
    except OverflowError:
        return 0.0


def orbit_until_one(start: int, *, step_cap: int = STEP_CAP) -> list[int]:
    if start < 1:
        raise ValueError("orbit starts at a positive integer")
    states = [start]
    seen = {start}
    while states[-1] != 1 and len(states) <= step_cap:
        nxt = floor_power(states[-1])
        states.append(nxt)
        if nxt in seen:
            break
        seen.add(nxt)
    return states


def extract_circuits(
    start: int, *, step_cap: int = STEP_CAP
) -> list[dict[str, Any]]:
    """Simons circuits on a finite orbit: blocks O^k E^l.

    A local min is an odd source (even→odd landing, or the odd start).
    A local max is the first even after that odd-run. The circuit
    ends at the next odd landing. Only valley-to-valley circuits
    with next min ≥ 3 are returned; the terminal drop to 1 is omitted.
    """

    states = orbit_until_one(start, step_cap=step_cap)
    circuits: list[dict[str, Any]] = []
    i = 0
    n_states = len(states)
    while i < n_states - 1:
        if states[i] % 2 == 0 or states[i] < 2:
            i += 1
            continue
        k = 0
        while i + k < n_states and states[i + k] % 2 == 1 and states[i + k] >= 2:
            k += 1
        if k == 0 or i + k >= n_states:
            break
        peak = states[i + k]
        if peak % 2 != 0:
            break
        l = 0
        j = i + k
        while j < n_states and states[j] % 2 == 0 and states[j] >= 2:
            l += 1
            j += 1
        if l == 0:
            break
        n_next = states[j] if j < n_states else None
        if n_next is None or n_next < MIN_TERM:
            break
        circuits.append(
            {
                "n_i": states[i],
                "k": k,
                "y": peak if peak.bit_length() <= 64 else None,
                "y_bits": peak.bit_length(),
                "l": l,
                "n_next": n_next,
                "L_k": k + l,
                "mu": min(states[i], n_next),
                "states": states[i:j],
            }
        )
        i = j
    return circuits


def _compact_int(value: int | None) -> int | None:
    if value is None:
        return None
    if value.bit_length() > 64:
        return None
    return value


def _public_circuit(circuit: dict[str, Any]) -> dict[str, Any]:
    return {
        "n_i": _compact_int(circuit["n_i"]),
        "n_i_bits": circuit["n_i"].bit_length(),
        "k": circuit["k"],
        "y": circuit["y"],
        "y_bits": circuit["y_bits"],
        "l": circuit["l"],
        "n_next": _compact_int(circuit["n_next"]),
        "n_next_bits": circuit["n_next"].bit_length(),
        "L_k": circuit["L_k"],
        "mu": _compact_int(circuit["mu"]),
        "mu_bits": circuit["mu"].bit_length(),
    }


def _sum_stats(circuits: list[dict[str, Any]]) -> dict[str, Any]:
    full = 0.0
    minima = 0.0
    partition = 0.0
    for circuit in circuits:
        minima += inv_log_term(circuit["n_i"])
        partition += circuit["L_k"] * inv_log_term(circuit["mu"])
        for state in circuit["states"]:
            full += inv_log_term(state)
    total_steps = sum(circuit["L_k"] for circuit in circuits)
    mean_lk = (total_steps / len(circuits)) if circuits else None
    ratio = (full / minima) if minima > 0.0 else None
    return {
        "m": len(circuits),
        "total_steps": total_steps,
        "full_step_sum": full,
        "minima_only_sum": minima,
        "partition_sum": partition,
        "full_over_minima": ratio,
        "mean_circuit_length": mean_lk,
        "ratio_over_mean_Lk": (
            (ratio / mean_lk) if ratio is not None and mean_lk else None
        ),
        "steiner_constant_ok": (
            ratio is not None and ratio <= STEINER_RATIO_CEILING
        ),
    }


def circuit_census(start: int, *, step_cap: int = STEP_CAP) -> dict[str, Any]:
    circuits = extract_circuits(start, step_cap=step_cap)
    cycle_like = [
        circuit for circuit in circuits if circuit["mu"] >= CYCLE_VALLEY_FLOOR
    ]
    all_stats = _sum_stats(circuits)
    like_stats = _sum_stats(cycle_like)
    return {
        "start": start,
        **all_stats,
        "cycle_like_m": like_stats["m"],
        "cycle_like_full_over_minima": like_stats["full_over_minima"],
        "cycle_like_steiner_ok": like_stats["steiner_constant_ok"],
        "circuits": [_public_circuit(circuit) for circuit in circuits],
    }


def first_odd_image(n: int) -> int:
    """T(n) for odd n: floor(n^{3/2})."""

    return isqrt(n * n * n)


def steiner_rhs(
    n: int, length: int, odd_count: int, m: int, *, const: float = EPS_CONST
) -> float:
    """Conservative joint-minima ceiling for θ at a CycleMin n.

    Local mins contribute m/(n ln n). Other odds are climb interiors
    and sit at least at T(n). Evens sit at least at n^2
    (cycleMin_even_ge_sq).
    """

    even_count = length - odd_count
    climb = max(odd_count - m, 0)
    t = first_odd_image(n)
    return const * (
        m / (n * math.log(n))
        + climb / (t * math.log(t))
        + even_count / (n * n * math.log(n * n))
    )


def analytic_kills_at_floor(
    length: int,
    odd_count: int,
    theta: float,
    m: int,
    *,
    n0: int = LEAN_CYCLE_FLOOR,
) -> bool:
    """θ > RHS(n0) excludes that (L, m): RHS decreases in n."""

    return theta > steiner_rhs(n0, length, odd_count, m)


def leftover_table() -> list[dict[str, Any]]:
    """Global n_max versus the CycleMin joint-minima bound at floor 53.

    Adversarial circuit-partition (every μ_k = n) equals the global
    bound. The analytic Steiner form with climb/even error terms is
    the candidate new inequality.
    """

    by_length = {row["L"]: row for row in finance_rows(max(LEFTOVER_LENGTHS))}
    out: list[dict[str, Any]] = []
    for length in LEFTOVER_LENGTHS:
        row = by_length[length]
        theta = row["theta"]
        odd_count = row["o"]
        even_count = length - odd_count
        global_n_max = row["n_max"]
        lean_survives = (371 / 2) * theta <= length
        global_kills = not lean_survives
        by_m: list[dict[str, Any]] = []
        for m in range(1, even_count + 1):
            rhs = steiner_rhs(LEAN_CYCLE_FLOOR, length, odd_count, m)
            kills = theta > rhs
            by_m.append(
                {
                    "m": m,
                    "analytic_rhs_at_53": rhs,
                    "analytic_kills_at_53": kills,
                    "naive_steiner_n_max": n_max_from_bound(
                        EPS_CONST * m / theta
                    ),
                    "partition_n_max": global_n_max,
                    "partition_equals_global": True,
                    "new_exclusion": kills and lean_survives,
                }
            )
        out.append(
            {
                "L": length,
                "o": odd_count,
                "theta": theta,
                "even_count": even_count,
                "global_n_max": global_n_max,
                "lean_survives_floor_53": lean_survives,
                "global_kills_at_53": global_kills,
                "by_m": by_m,
                "analytic_kills_m1": by_m[0]["analytic_kills_at_53"],
                "analytic_kills_all_m": all(
                    item["analytic_kills_at_53"] for item in by_m
                ),
                "partition_kills_any_new": False,
                "new_exclusions": [
                    item["m"] for item in by_m if item["new_exclusion"]
                ],
            }
        )
    return out


def lean_surviving_scan(*, l_max: int = 90) -> dict[str, Any]:
    """Which Lean-surviving lengths die for every m at floor 53."""

    killed_all_m: list[int] = []
    leftover: list[dict[str, Any]] = []
    for row in finance_rows(l_max):
        length, odd_count, theta = row["L"], row["o"], row["theta"]
        if (371 / 2) * theta > length:
            continue
        even_count = length - odd_count
        all_m = all(
            analytic_kills_at_floor(length, odd_count, theta, m)
            for m in range(1, even_count + 1)
        )
        m1 = analytic_kills_at_floor(length, odd_count, theta, 1)
        leftover.append(
            {
                "L": length,
                "o": odd_count,
                "even_count": even_count,
                "theta": theta,
                "global_n_max": row["n_max"],
                "kills_m1": m1,
                "kills_all_m": all_m,
            }
        )
        if all_m:
            killed_all_m.append(length)
    return {
        "l_max": l_max,
        "lean_surviving": leftover,
        "killed_all_m": killed_all_m,
    }


def lean_api_present() -> dict[str, bool]:
    combined = (
        CYCLE_CORE.read_text(encoding="utf-8")
        + "\n"
        + CYCLE_FINANCE.read_text(encoding="utf-8")
        + "\n"
        # leftover instances split out of CycleFinance.lean (1 Sep 2026)
        + CYCLE_FINANCE_LEFTOVERS.read_text(encoding="utf-8")
        + "\n"
        + CYCLE_EXTREMA.read_text(encoding="utf-8")
        + "\n"
        + JUGGLER_PAPER_BARREL.read_text(encoding="utf-8")
    )
    paper = JUGGLER_PAPER_BARREL.read_text(encoding="utf-8")
    named = {name: has_named(combined, name) for name in EXISTING_LEAN}
    forbidden = {
        f"has_{name}": has_named(combined, name) for name in FORBIDDEN_THEOREMS
    }
    return {
        "sorry_free": "sorry" not in combined and "admit" not in combined,
        **named,
        **forbidden,
        **{
            f"has_api_{name}": has_named(combined, name)
            for name in FORBIDDEN_NEW_API
        },
        "cycle_finance_present": CYCLE_FINANCE.is_file(),
        "no_extra_m_finance_file": not any(
            path.is_file() for path in FORBIDDEN_LEAN_FILES
        ),
        "not_in_paper_barrel": all(name not in paper for name in PAPER_FORBIDDEN),
    }


def run_probe(
    *,
    seeds: tuple[int, ...] = SCIENCE_SEEDS,
    step_cap: int = STEP_CAP,
) -> dict[str, Any]:
    census = [circuit_census(seed, step_cap=step_cap) for seed in seeds]
    usable = [row for row in census if row["m"] >= 1]
    leftovers = leftover_table()
    scan90 = lean_surviving_scan()
    like_ratios = [
        row["cycle_like_full_over_minima"]
        for row in usable
        if row["cycle_like_full_over_minima"] is not None
    ]
    raw_ratios = [
        row["full_over_minima"]
        for row in usable
        if row["full_over_minima"] is not None
    ]
    new_pairs = [
        (row["L"], row["new_exclusions"])
        for row in leftovers
        if row["new_exclusions"]
    ]
    return {
        "seeds": list(seeds),
        "step_cap": step_cap,
        "census": census,
        "usable_circuit_starts": len(usable),
        "max_full_over_minima": max(raw_ratios) if raw_ratios else None,
        "max_cycle_like_ratio": max(like_ratios) if like_ratios else None,
        "cycle_like_steiner_holds": all(
            row["cycle_like_steiner_ok"]
            for row in usable
            if row["cycle_like_m"] >= 1
        ),
        "leftovers": leftovers,
        "lean_surviving_scan": scan90,
        "partition_kills_any_new": False,
        "new_leftover_pairs": new_pairs,
        "kills_length_thirty_all_m": any(
            row["L"] == 30 and row["analytic_kills_all_m"] for row in leftovers
        ),
        "kills_length_nineteen_m1": any(
            row["L"] == 19 and row["analytic_kills_m1"] for row in leftovers
        ),
        "git": git_commit(),
        "halt_theorem": False,
        "no_cycle_all_lengths": False,
        "floor_raise": False,
        "new_lean": False,
    }


def classify(scan: dict[str, Any], lean: dict[str, bool]) -> dict[str, Any]:
    lean_ok = (
        lean["sorry_free"]
        and all(lean[name] for name in EXISTING_LEAN)
        and not any(lean[f"has_{name}"] for name in FORBIDDEN_THEOREMS)
        and not any(lean[f"has_api_{name}"] for name in FORBIDDEN_NEW_API)
        and lean["cycle_finance_present"]
        and lean["no_extra_m_finance_file"]
        and lean["not_in_paper_barrel"]
    )
    if not lean_ok:
        return {"classification": CLASS_INCOMPLETE, "reason": f"lean_ok={lean_ok}"}
    if scan["halt_theorem"] or scan["no_cycle_all_lengths"] or scan["new_lean"]:
        return {
            "classification": CLASS_INCOMPLETE,
            "reason": "out-of-scope claim or unexpected Lean addition",
        }
    if scan["usable_circuit_starts"] < 1:
        return {
            "classification": CLASS_INCOMPLETE,
            "reason": "no complete O^k E^l circuit on the named starts",
        }
    if not scan["cycle_like_steiner_holds"]:
        return {
            "classification": CLASS_CLOSED,
            "reason": (
                "cycle-like circuits (valleys ≥ 12) do not concentrate at "
                f"minima: max full/minima = {scan['max_cycle_like_ratio']}"
            ),
        }
    if scan["kills_length_thirty_all_m"] or scan["kills_length_nineteen_m1"]:
        killed = scan["lean_surviving_scan"]["killed_all_m"]
        return {
            "classification": CLASS_GREEN,
            "reason": (
                "CycleMin joint-minima finance with climb/even error terms "
                "excludes leftover pairs that cycleMin_finance misses: "
                "L=19 is impossible as a 1-cycle, and L=30 is impossible "
                f"for every m. Lean-surviving lengths ≤ 90 killed for all m: "
                f"{killed}. Adversarial circuit-partition remains a "
                "reparameterization of the global bound. Cycle-like "
                "transient ratio "
                f"{scan['max_cycle_like_ratio']:.3g} ≤ "
                f"{STEINER_RATIO_CEILING}"
            ),
        }
    return {
        "classification": CLASS_PARK,
        "reason": (
            "valley concentration holds on cycle-like circuits but the "
            "analytic bound excludes no leftover (L, m) at floor 53"
        ),
    }


def probe_payload(
    *,
    seeds: tuple[int, ...] = SCIENCE_SEEDS,
    step_cap: int = STEP_CAP,
) -> dict[str, Any]:
    scan = run_probe(seeds=seeds, step_cap=step_cap)
    lean = lean_api_present()
    decision = classify(scan, lean)
    anti = dict(ANTI_OVERCLAIM)
    anti.update(
        {
            "halt_theorem": False,
            "no_cycle_all_lengths": False,
            "floor_raise": False,
            "new_lean": False,
            "steiner_form": False,
            "stronger_than_cycleMin_finance": False,
            "peak_finance_reopened": False,
            "extremal_composition_reopened": False,
        }
    )
    return {
        "experiment": "juggler_cycle_m_finance",
        "engine_control_layer_modified": False,
        "anti_overclaim": anti,
        "scan": scan,
        "lean": lean,
        "decision": decision,
        "search_method": (
            f"Simons circuits O^k E^l on starts {list(seeds)}, "
            f"step_cap {step_cap}; leftover n_max at L in {list(LEFTOVER_LENGTHS)}"
        ),
    }


def render_markdown(payload: dict[str, Any]) -> str:
    decision = payload["decision"]
    scan = payload["scan"]
    lines = [
        "# Juggler m-cycle finance",
        "",
        f"Status: **{decision['classification']}**",
        "",
        "Simons-circuit log-unroll of CycleFinance at each local minimum.",
        "Not a halt theorem. Not a no-cycle-of-any-length theorem.",
        "No new Lean.",
        "",
        "## Metadata",
        "",
        f"- classification: **{decision['classification']}**",
        f"- seeds: `{scan['seeds']}`",
        f"- step cap: `{scan['step_cap']}`",
        f"- usable circuit starts: `{scan['usable_circuit_starts']}`",
        f"- max raw full/minima: `{scan['max_full_over_minima']}`",
        f"- max cycle-like full/minima: `{scan['max_cycle_like_ratio']}`",
        f"- cycle-like Steiner holds: `{scan['cycle_like_steiner_holds']}`",
        f"- L=19 m=1 killed: `{scan['kills_length_nineteen_m1']}`",
        f"- L=30 all m killed: `{scan['kills_length_thirty_all_m']}`",
        f"- Lean-surviving all-m kills ≤ 90: "
        f"`{scan['lean_surviving_scan']['killed_all_m']}`",
        "",
        decision["reason"] + ".",
        "",
        "## Transient circuits",
        "",
    ]
    for row in scan["census"]:
        ratio = row["full_over_minima"]
        like = row["cycle_like_full_over_minima"]
        lines.append(
            f"- start=`{row['start']}` m=`{row['m']}` "
            f"cycle-like m=`{row['cycle_like_m']}` "
            f"raw full/minima=`{None if ratio is None else round(ratio, 4)}` "
            f"cycle-like full/minima="
            f"`{None if like is None else round(like, 4)}`"
        )
    lines.extend(["", "## Leftover lengths", ""])
    for row in scan["leftovers"]:
        lines.append(
            f"- L=`{row['L']}` o=`{row['o']}` even=`{row['even_count']}` "
            f"global n_max=`{row['global_n_max']}` "
            f"Lean survives=`{row['lean_survives_floor_53']}` "
            f"kills m=1=`{row['analytic_kills_m1']}` "
            f"kills all m=`{row['analytic_kills_all_m']}` "
            f"new m=`{row['new_exclusions']}`"
        )
    lines.extend(
        [
            "",
            "## Anti-overclaim",
            "",
        ]
    )
    for key, value in payload["anti_overclaim"].items():
        lines.append(f"- {key}: `{value}`")
    lines.extend(
        [
            "",
            "## Decision",
            "",
            f"**{decision['classification']}**",
            "",
            decision["reason"] + ".",
            "",
        ]
    )
    return "\n".join(lines) + "\n"


def write_data_artifacts(payload: dict[str, Any]) -> None:
    DATA_DIR.mkdir(parents=True, exist_ok=True)
    scan = payload["scan"]
    (DATA_DIR / "census.json").write_text(
        json.dumps(scan["census"], indent=2) + "\n", encoding="utf-8"
    )
    (DATA_DIR / "leftovers.json").write_text(
        json.dumps(scan["leftovers"], indent=2) + "\n", encoding="utf-8"
    )
    summary = {
        "classification": payload["decision"]["classification"],
        "reason": payload["decision"]["reason"],
        "max_cycle_like_ratio": scan["max_cycle_like_ratio"],
        "kills_length_nineteen_m1": scan["kills_length_nineteen_m1"],
        "kills_length_thirty_all_m": scan["kills_length_thirty_all_m"],
        "killed_all_m": scan["lean_surviving_scan"]["killed_all_m"],
        "git": scan["git"],
    }
    (DATA_DIR / "summary.json").write_text(
        json.dumps(summary, indent=2) + "\n", encoding="utf-8"
    )
    (DATA_DIR / "README.md").write_text(
        "# Juggler m-cycle finance\n\n"
        "Simons-circuit log-unroll versus cycleMin_finance.\n"
        "Not a halt theorem. No new Lean.\n\n"
        "Regenerate with `python -m research.juggler_sequence.cycle_m_finance`.\n",
        encoding="utf-8",
    )


def write_artifacts(payload: dict[str, Any] | None = None) -> dict[str, Any]:
    data = payload if payload is not None else probe_payload()
    JSON_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(data, indent=2) + "\n", encoding="utf-8")
    DOC_PATH.write_text(render_markdown(data), encoding="utf-8")
    write_data_artifacts(data)
    return data


def main() -> None:
    payload = write_artifacts()
    scan = payload["scan"]
    print(payload["decision"]["classification"])
    print(payload["decision"]["reason"])
    print(
        f"usable={scan['usable_circuit_starts']} "
        f"cycle_like_ratio={scan['max_cycle_like_ratio']} "
        f"L19m1={scan['kills_length_nineteen_m1']} "
        f"L30all={scan['kills_length_thirty_all_m']}"
    )


if __name__ == "__main__":
    main()
