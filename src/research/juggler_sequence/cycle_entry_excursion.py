"""CycleMin entry excursion versus valley-only finance.

Phase 0 only: enumerate exact O^a E landings at the CycleMin n,
measure the finance cost of those predecessor valleys against the
relaxed OE / OOE classes, and test whether the entry cut forces a
global tax or a closing-edge conflict at L=25781.

Not a halt theorem, not a last-even reopen, not an inverse-width
reopen, and not a claim that every valley must itself land at n.

Dossier: docs/problems/juggler_cycle_entry_excursion.md.
"""

from __future__ import annotations

import json
from typing import Any

from research.juggler_sequence.cycle_almost_search import (
    PHASE1_L,
    circuits,
    compatible_oe_preimages,
    packed_block_word,
    run_preimages,
)
from research.juggler_sequence.cycle_budget_opt import (
    budget_excludes,
    inv_log,
    oe_start_min,
    run_type_counts,
)
from research.juggler_sequence.cycle_conditioned_closure import deficit_row
from research.juggler_sequence.cycle_finance import (
    DATA_DIR,
    MIN_STATE,
    PUBLISHED_FLOOR,
    o_min_and_theta,
    parity_excludes,
)
from research.juggler_sequence.cycle_ordered_excursion import excursion_map, first_a2
from research.juggler_sequence.floor_preimages import even_preimage
from research.juggler_sequence.power_itineraries import floor_power

ENTRY_DIR = DATA_DIR / "entry_excursion"
START = PUBLISHED_FLOOR + 1
A_MAX = 4
WINDOW_HI = START + 2_000
WINDOW_STRIDE = 400
TAX_EPS = 1e-18
REL_SCALE_EPS = 1e-9

CLASS_CLOSED = "ENTRY_EXCURSION_CLOSED"
CLASS_GREEN = "ENTRY_EXCURSION_GREEN"
CLASS_PARK = "ENTRY_EXCURSION_PARK"

ARCHIVED = (
    "last_even_ne_odd_sq",
    "F2_gt_v",
    "oe_start_min",
    "terminal_21_realized",
    "odd_preimage_unique",
)


def envelope_valley_scale(n: int, a: int) -> float:
    """Real envelope v ~ n^{2^{a+1}/3^a} for peak ~ n^2 after a odds."""

    if n < 2 or a < 1:
        return 0.0
    return float(n) ** ((2 ** (a + 1)) / (3**a))


def entry_even_cell(n: int) -> dict[str, Any]:
    """Last-even predecessors of odd n: n^2 < x < (n+1)^2, x even."""

    if n < 1 or n % 2 == 0:
        raise ValueError("entry_even_cell requires a positive odd n")
    lo, hi = even_preimage(n)
    start = lo if lo % 2 == 0 else lo + 1
    count = 0
    if start < hi:
        count = (hi - 1 - start) // 2 + 1
    return {
        "n": n,
        "lo": lo,
        "hi": hi,
        "first_even": start if start < hi else None,
        "count": count,
        "width": hi - lo,
        "rel_width": (hi - lo) / (n * n),
        "contains_n2": False,
        "n2_odd": True,
    }


def excursion_states(v: int, a: int) -> list[int] | None:
    rec = excursion_map(v, a)
    if rec is None:
        return None
    peak, landing = rec
    states = [v]
    current = v
    for _ in range(a):
        current = floor_power(current)
        states.append(current)
    current = floor_power(current)
    states.append(current)
    if states[-2] != peak or states[-1] != landing:
        return None
    return states


def tube_ok(states: list[int], n: int) -> bool:
    return bool(states) and all(state >= n for state in states)


def entry_row(v: int, a: int, n: int) -> dict[str, Any] | None:
    states = excursion_states(v, a)
    if states is None:
        return None
    peak = states[-2]
    landing = states[-1]
    if landing != n:
        return None
    oe = oe_start_min(n)
    cost = inv_log(v)
    cheap_oe = inv_log(oe)
    cheap_n = inv_log(n)
    return {
        "v": v,
        "a": a,
        "peak": peak,
        "x": peak,
        "landing": landing,
        "states": states,
        "tube_min": min(states),
        "tube_ge_n": tube_ok(states, n),
        "v_over_n": v / n,
        "v_over_oe": v / oe,
        "finance_cost": cost,
        "tax_vs_oe": cheap_oe - cost,
        "tax_vs_n": cheap_n - cost,
        "run_type": "O" * a + "E",
    }


def entries_of_run(n: int, a: int) -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    if a == 1:
        pairs = compatible_oe_preimages(n)
        valleys = [v for v, _peak in pairs]
    else:
        valleys = run_preimages(n, a)
    for v in valleys:
        row = entry_row(v, a, n)
        if row is not None:
            rows.append(row)
    rows.sort(key=lambda rec: rec["v"])
    return rows


def run_layer(n: int, a: int) -> dict[str, Any]:
    all_rows = entries_of_run(n, a)
    ge_n = [row for row in all_rows if row["tube_ge_n"]]
    env = envelope_valley_scale(n, a)
    return {
        "a": a,
        "run_type": "O" * a + "E",
        "envelope_v": env,
        "envelope_below_n": env < n,
        "n_total": len(all_rows),
        "n_ge_n": len(ge_n),
        "min_v": ge_n[0]["v"] if ge_n else (all_rows[0]["v"] if all_rows else None),
        "max_v": ge_n[-1]["v"] if ge_n else (all_rows[-1]["v"] if all_rows else None),
        "min_v_below_n": min((row["v"] for row in all_rows), default=None),
        "any_below_n": any(row["v"] < n for row in all_rows),
        "rows": ge_n,
    }


def finance_summary(n: int, ge_n_rows: list[dict[str, Any]]) -> dict[str, Any]:
    oe = oe_start_min(n)
    cheap = inv_log(oe)
    if not ge_n_rows:
        return {
            "oe_start": oe,
            "n_entry": 0,
            "min_v": None,
            "max_v": None,
            "min_v_over_oe": None,
            "max_tax_vs_oe": None,
            "min_tax_vs_oe": None,
            "tax_zero": True,
            "at_oe_scale": False,
        }
    taxes = [row["tax_vs_oe"] for row in ge_n_rows]
    min_v = min(row["v"] for row in ge_n_rows)
    max_v = max(row["v"] for row in ge_n_rows)
    return {
        "oe_start": oe,
        "oe_cost": cheap,
        "n_entry": len(ge_n_rows),
        "min_v": min_v,
        "max_v": max_v,
        "min_v_over_oe": min_v / oe,
        "max_v_over_oe": max_v / oe,
        "min_tax_vs_oe": min(taxes),
        "max_tax_vs_oe": max(taxes),
        "tax_zero": all(abs(tax) < TAX_EPS or tax <= 0.0 for tax in taxes)
        or abs(min_v / oe - 1.0) < REL_SCALE_EPS,
        "at_oe_scale": abs(min_v / oe - 1.0) < 1e-3 or min_v == oe,
    }


def valley_class_row(n: int, name: str, v: int) -> dict[str, Any]:
    hits: list[dict[str, Any]] = []
    if v % 2 == 1 and v >= 1:
        for a in range(1, A_MAX + 1):
            rec = excursion_map(v, a)
            if rec is None:
                continue
            peak, landing = rec
            states = excursion_states(v, a)
            if landing == n and states is not None:
                hits.append(
                    {
                        "a": a,
                        "peak": peak,
                        "tube_ge_n": tube_ok(states, n),
                    }
                )
    return {
        "name": name,
        "v": v,
        "enters_n": any(hit["tube_ge_n"] for hit in hits),
        "hits": hits,
    }


def finance_classes(n: int) -> list[dict[str, Any]]:
    return [
        valley_class_row(n, "cyclemin", n),
        valley_class_row(n, "unique_visit_next", n + 2),
        valley_class_row(n, "oe_start", oe_start_min(n)),
    ]


def packed_closing() -> dict[str, Any]:
    odd, _theta = o_min_and_theta(PHASE1_L)
    word = packed_block_word(PHASE1_L, odd)
    pairs = circuits(word)
    n_ooe, n_oe = run_type_counts(odd, PHASE1_L - odd)
    last = pairs[-1]
    prev = pairs[-2] if len(pairs) >= 2 else None
    return {
        "L": PHASE1_L,
        "o": odd,
        "n_ooe": n_ooe,
        "n_oe": n_oe,
        "last_circuit": list(last),
        "prev_circuit": list(prev) if prev else None,
        "ends_oe": last == (1, 1),
        "ends_21": prev == (2, 1) and last == (1, 1),
        "suffix": word[-16:],
        "prefix": word[:16],
    }


def forward_ooe_overshoot(n: int) -> dict[str, Any]:
    """First a=2 start at or above n: peak vs the return cell of n."""

    v = first_a2(n)
    rec = None if v is None else excursion_map(v, 2)
    cell_hi = (n + 1) * (n + 1)
    out: dict[str, Any] = {
        "n": n,
        "first_a2": v,
        "F2": None if rec is None else {"v": v, "peak": rec[0], "landing": rec[1]},
        "return_hi": cell_hi,
    }
    if rec is not None:
        out["peak_overshoots_return"] = rec[0] >= cell_hi
        out["landing_gt_n"] = rec[1] > n
        out["landing_eq_n"] = rec[1] == n
    return out


def window_census(lo: int, hi: int, *, stride: int) -> dict[str, Any]:
    if lo % 2 == 0:
        lo += 1
    n_seen = 0
    n_oe = 0
    n_deep_ge_n = 0
    min_over: list[float] = []
    for n in range(lo, hi + 1, stride):
        if n % 2 == 0:
            continue
        n_seen += 1
        layer1 = run_layer(n, 1)
        if layer1["n_ge_n"]:
            n_oe += 1
            oe = oe_start_min(n)
            min_over.append(layer1["min_v"] / oe)
        deep = 0
        for a in range(2, A_MAX + 1):
            deep += run_layer(n, a)["n_ge_n"]
        if deep:
            n_deep_ge_n += 1
    return {
        "lo": lo,
        "hi": hi,
        "stride": stride,
        "n_seen": n_seen,
        "n_oe_entry": n_oe,
        "n_deep_ge_n": n_deep_ge_n,
        "mean_min_v_over_oe": (sum(min_over) / len(min_over)) if min_over else None,
        "max_min_v_over_oe": max(min_over) if min_over else None,
    }


def slack_compare(n: int, finance: dict[str, Any]) -> dict[str, Any]:
    slack = deficit_row(PHASE1_L, floor=PUBLISHED_FLOOR)
    one_tax = max(finance.get("max_tax_vs_oe") or 0.0, 0.0)
    false_all = slack["oe_count"] * one_tax
    return {
        "theta": slack["theta"],
        "packed": slack["packed"],
        "margin": slack["margin"],
        "oe_count": slack["oe_count"],
        "oo_count": slack["oo_count"],
        "one_entry_tax": one_tax,
        "one_entry_inside_slack": one_tax < slack["margin"],
        "false_all_oe_tax": false_all,
        "false_all_inside_slack": false_all < slack["margin"],
        "false_all_would_kill": false_all >= slack["margin"] and false_all > 0.0,
    }


def classify(payload: dict[str, Any]) -> dict[str, Any]:
    layers = payload["layers"]
    finance = payload["finance"]
    classes = payload["valley_classes"]
    closing = payload["packed_closing"]
    slack = payload["slack"]
    deep_ge_n = sum(layer["n_ge_n"] for layer in layers if layer["a"] >= 2)
    only_oe = layers[0]["n_ge_n"] > 0 and deep_ge_n == 0
    all_valleys = all(row["enters_n"] for row in classes)
    cheap_ooe_enter = any(
        row["name"] in {"cyclemin", "unique_visit_next"} and row["enters_n"]
        for row in classes
    )
    tax_zero = finance["tax_zero"] or finance["at_oe_scale"]
    no_closing_conflict = closing["ends_oe"]
    leftover_killer = (
        (not slack["one_entry_inside_slack"])
        and only_oe
        and (not tax_zero)
    )
    archived_only = only_oe and tax_zero and no_closing_conflict and not all_valleys
    if leftover_killer:
        classification = CLASS_GREEN
        decision = "PROMOTE"
        reason = (
            "the CycleMin entry forces a finance tax larger than "
            "packed-to-theta slack"
        )
    elif archived_only:
        classification = CLASS_CLOSED
        decision = "CLOSE"
        reason = (
            "entry into n is the archived OE cell at oe_start_min; "
            "a>=2 with v>=n is empty (F2(v)>v); the packed word "
            "already ends OE; every-valley compatibility is false; "
            "no extra leftover-killing delta"
        )
    else:
        classification = CLASS_PARK
        decision = "PARK"
        reason = "entry census is mixed and does not yield a uniform tax"
    return {
        "classification": classification,
        "decision": decision,
        "reason": reason,
        "only_oe_entry": only_oe,
        "deep_ge_n": deep_ge_n,
        "tax_zero": tax_zero,
        "at_oe_scale": finance["at_oe_scale"],
        "all_valleys_compatible": all_valleys,
        "cheap_ooe_enters_n": cheap_ooe_enter,
        "packed_ends_oe": closing["ends_oe"],
        "closing_conflict": not no_closing_conflict,
        "one_entry_inside_slack": slack["one_entry_inside_slack"],
        "false_all_would_kill": slack["false_all_would_kill"],
        "leftover_killer": leftover_killer,
        "halt_theorem": False,
        "raise_n0": False,
        "open_55293": False,
        "archived_tags": list(ARCHIVED),
    }


def _compact_row(row: dict[str, Any]) -> dict[str, Any]:
    return {
        "v": row["v"],
        "a": row["a"],
        "peak": row["peak"],
        "tube_min": row["tube_min"],
        "tube_ge_n": row["tube_ge_n"],
        "v_over_n": row["v_over_n"],
        "v_over_oe": row["v_over_oe"],
        "finance_cost": row["finance_cost"],
        "tax_vs_oe": row["tax_vs_oe"],
        "run_type": row["run_type"],
    }


def probe_payload(*, n: int = START) -> dict[str, Any]:
    cell = entry_even_cell(n)
    layers = [run_layer(n, a) for a in range(1, A_MAX + 1)]
    ge_n_rows = [row for layer in layers for row in layer["rows"]]
    finance = finance_summary(n, ge_n_rows)
    classes = finance_classes(n)
    closing = packed_closing()
    overshoot = forward_ooe_overshoot(n)
    window = window_census(START, WINDOW_HI, stride=WINDOW_STRIDE)
    slack = slack_compare(n, finance)
    odd, theta = o_min_and_theta(PHASE1_L)
    start = max(n, MIN_STATE)
    payload = {
        "bound": "entry_excursion",
        "L": PHASE1_L,
        "o": odd,
        "theta": theta,
        "n": n,
        "entry_cell": cell,
        "layers": [
            {k: v for k, v in layer.items() if k != "rows"}
            | {"witnesses": [_compact_row(row) for row in layer["rows"][:8]]}
            for layer in layers
        ],
        "finance": finance,
        "valley_classes": classes,
        "packed_closing": closing,
        "ooe_overshoot": overshoot,
        "window": window,
        "slack": slack,
        "published_floor": PUBLISHED_FLOOR,
        "start": start,
        "charged_excludes": {
            "parity_excludes": parity_excludes(PHASE1_L, odd, theta, PUBLISHED_FLOOR),
            "budget_excludes": budget_excludes(PHASE1_L, odd, theta, PUBLISHED_FLOOR),
        },
    }
    payload["decision"] = classify(payload)
    return payload


def write_artifacts(payload: dict[str, Any] | None = None) -> dict[str, Any]:
    data = payload if payload is not None else probe_payload()
    ENTRY_DIR.mkdir(parents=True, exist_ok=True)
    path = ENTRY_DIR / "summary.json"
    path.write_text(json.dumps(data, indent=2, allow_nan=False) + "\n", encoding="utf-8")
    return data


def main() -> None:
    payload = write_artifacts()
    decision = payload["decision"]
    print(decision["classification"])
    print(decision["reason"])
    print(
        json.dumps(
            {
                "n": payload["n"],
                "entry_count": payload["finance"]["n_entry"],
                "min_v": payload["finance"]["min_v"],
                "oe_start": payload["finance"]["oe_start"],
                "min_v_over_oe": payload["finance"]["min_v_over_oe"],
                "max_tax": payload["finance"]["max_tax_vs_oe"],
                "layers": [
                    {
                        "a": layer["a"],
                        "n_total": layer["n_total"],
                        "n_ge_n": layer["n_ge_n"],
                        "envelope_below_n": layer["envelope_below_n"],
                    }
                    for layer in payload["layers"]
                ],
                "classes": payload["valley_classes"],
                "closing": payload["packed_closing"],
                "window": payload["window"],
                "slack": payload["slack"],
                "decision": decision,
            },
            indent=2,
        )
    )


if __name__ == "__main__":
    main()
