"""CycleMin local seam types on both sides of n.

Phase 0 only: classify the letters touching a CycleMin cut, record
the cell inequality of each legal type, and test whether any type
empties for a reason that is not an archived first/last-letter lemma.

This is not the closed OE-corridor leftover-killer, not a finance
reopen, not a halt theorem, and not a claim that every positive
integer reaches 1.

Dossier: docs/problems/juggler_cycle_cyclic_seam.md.
"""

from __future__ import annotations

import json
from typing import Any

from research.juggler_sequence.cycle_almost_search import odd_preimage
from research.juggler_sequence.cycle_entry_corridor import ee_entry_count
from research.juggler_sequence.cycle_entry_excursion import (
    entry_even_cell,
    run_layer,
)
from research.juggler_sequence.cycle_finance import DATA_DIR, PUBLISHED_FLOOR
from research.juggler_sequence.floor_preimages import even_preimage
from research.juggler_sequence.power_itineraries import floor_power

SEAM_DIR = DATA_DIR / "cyclic_seam"
START = PUBLISHED_FLOOR + 1

CLASS_CLOSED = "CYCLIC_SEAM_CLOSED"
CLASS_GREEN = "CYCLIC_SEAM_GREEN"
CLASS_PARK = "CYCLIC_SEAM_PARK"

LAUNCH_LO = 13
LAUNCH_HI = 2001
OEE_P_CAP = 40
OEE_Q_CAP = 40

ARCHIVED = (
    "cycleMin_starts_two_odds",
    "cycleMin_not_end_odd",
    "cycleMin_not_odd_even",
    "cycleMin_getLast_even",
    "exists_cycleMin_last_odd_run",
    "cycle_last_even_interval",
    "cycle_trailing_evens_lt",
    "oo_suffix_threshold",
)

# 2+2 window: last two letters | first two letters.
LEGAL_22 = ("EE|OO", "OE|OO")
FORBIDDEN_22 = (
    "EE|OE",
    "EE|EO",
    "EE|EE",
    "OE|OE",
    "OE|EO",
    "OE|EE",
    "EO|OO",
    "OO|OO",
)

# 3+3 window after forcing last E and first OO.
LEGAL_33 = (
    "EOE|OOE",
    "EOE|OOO",
    "OEE|OOE",
    "OEE|OOO",
    "EEE|OOE",
    "EEE|OOO",
)


def even_predecessor_start(n: int) -> tuple[int, int]:
    """First even in (n^2, (n+1)^2) and the exclusive top."""

    lo, hi = even_preimage(n)
    start = lo + 1 if lo % 2 else lo + 2
    return start, hi


def even_predecessors(n: int, *, cap: int | None = None) -> list[int]:
    """Even last-even-cell occupants of odd n, optionally capped."""

    start, hi = even_predecessor_start(n)
    if cap is None:
        return list(range(start, hi, 2))
    out: list[int] = []
    p = start
    while p < hi and len(out) < cap:
        out.append(p)
        p += 2
    return out


def odd_return_ge_n(n: int) -> int | None:
    """Odd predecessor of n that stays ≥ n, or None.

    The odd cell sits at scale n^{2/3} < n, so CycleMin forbids it.
    """

    pred = odd_preimage(n)
    if pred is None or pred < n:
        return None
    if floor_power(pred) != n:
        return None
    return pred


def launch_word(n: int) -> str | None:
    """First two or three letters realized by odd n, or None."""

    if n < 1 or n % 2 == 0:
        return None
    t1 = floor_power(n)
    if t1 % 2 == 0:
        return "OE"
    t2 = floor_power(t1)
    if t2 % 2 == 0:
        return "OOE"
    return "OOO"


def launch_split(*, lo: int = LAUNCH_LO, hi: int = LAUNCH_HI) -> dict[str, Any]:
    """OOE vs OOO among odd starts that realize OO."""

    n_oe = 0
    n_ooe = 0
    n_ooo = 0
    first_ooe: int | None = None
    first_ooo: int | None = None
    for n in range(lo if lo % 2 else lo + 1, hi, 2):
        word = launch_word(n)
        if word == "OE":
            n_oe += 1
        elif word == "OOE":
            n_ooe += 1
            if first_ooe is None:
                first_ooe = n
        elif word == "OOO":
            n_ooo += 1
            if first_ooo is None:
                first_ooo = n
    return {
        "lo": lo,
        "hi": hi,
        "n_oe": n_oe,
        "n_ooe": n_ooe,
        "n_ooo": n_ooo,
        "n_oo": n_ooe + n_ooo,
        "both_launch_subtypes": n_ooe > 0 and n_ooo > 0,
        "first_ooe": first_ooe,
        "first_ooo": first_ooo,
    }


def oee_search(
    n: int,
    *,
    p_cap: int = OEE_P_CAP,
    q_cap: int = OEE_Q_CAP,
) -> dict[str, Any]:
    """Search for one CycleMin-legal OEE into n (last odd then EE)."""

    scanned = 0
    for p in even_predecessors(n, cap=p_cap):
        q_lo = p * p
        q_hi = (p + 1) * (p + 1)
        q = q_lo if q_lo % 2 == 0 else q_lo + 1
        seen = 0
        while q < q_hi and seen < q_cap:
            scanned += 1
            valley = odd_preimage(q)
            if (
                valley is not None
                and valley % 2 == 1
                and valley >= n
                and floor_power(valley) == q
                and floor_power(q) == p
                and floor_power(p) == n
            ):
                return {
                    "found": True,
                    "v": valley,
                    "q": q,
                    "p": p,
                    "n": n,
                    "scanned": scanned,
                    "scale_note": "last odd at ~ n^{8/3}, not n^{4/3}",
                }
            q += 2
            seen += 1
    return {
        "found": False,
        "v": None,
        "q": None,
        "p": None,
        "n": n,
        "scanned": scanned,
        "scale_note": "last odd at ~ n^{8/3}, not n^{4/3}",
    }


def eee_witness(n: int) -> dict[str, Any]:
    """One trailing-EEE chain: r --E--> q --E--> p --E--> n."""

    preds = even_predecessors(n, cap=1)
    p = preds[0]
    q = p * p if (p * p) % 2 == 0 else p * p + 1
    r = q * q if (q * q) % 2 == 0 else q * q + 1
    ok = (
        r % 2 == 0
        and q % 2 == 0
        and p % 2 == 0
        and r >= n
        and floor_power(r) == q
        and floor_power(q) == p
        and floor_power(p) == n
    )
    return {"found": ok, "r": r, "q": q, "p": p, "n": n}


def type_inequalities() -> dict[str, str]:
    return {
        "OE|OO": (
            "last peak in (n^2,(n+1)^2); last valley in n^4<v^3<(n+1)^4; "
            "T^2(n) >= (n+1)^2"
        ),
        "EE|OO": (
            "last peak in (n^2,(n+1)^2); previous even in [p^2,(p+1)^2); "
            "cycle_trailing_evens_lt at r>=2; T^2(n) >= (n+1)^2"
        ),
        "return-O": "odd cell n^2 <= x^3 < (n+1)^2 forces x < n (cycleMin_not_end_odd)",
        "launch-OE": "first even < n^2 (cycleMin_not_odd_even)",
        "left-OOE": "oo_suffix_threshold vs last-even (exists_cycleMin_last_odd_run)",
    }


def classify(payload: dict[str, Any]) -> dict[str, Any]:
    window22 = payload["window_22"]
    occ = payload["occupancy"]
    launch = payload["launch_split"]
    legal = tuple(window22["legal"])
    finite = legal == LEGAL_22
    both_occ = bool(occ["oe_ge_n"] > 0 and occ["ee_count"] > 0)
    return_o_empty = occ["odd_return_ge_n"] is None
    left_ooe_empty = occ["left_ooe_ge_n"] == 0
    launch_both = bool(launch["both_launch_subtypes"])
    oee_open = bool(payload["oee"]["found"])
    eee_open = bool(payload["eee"]["found"])
    new_emptiness = (not both_occ) or (not return_o_empty) or (not left_ooe_empty)
    new_inequality = False
    if new_emptiness or new_inequality:
        classification = CLASS_GREEN
        decision = "PROMOTE"
        reason = (
            "a seam type empties, or a cell bound appears, that is "
            "not start-OO / no-end-O / last-even / trailing-evens / "
            "oo_suffix"
        )
    elif finite and both_occ and return_o_empty and left_ooe_empty and launch_both:
        classification = CLASS_CLOSED
        decision = "CLOSE"
        reason = (
            "the 2+2 window is exactly {OE|OO, EE|OO}; return-O and "
            "launch-OE are the archived Lean lemmas; both legal types "
            "are occupied by the archived OE cell and the EE count "
            "n(n^2+n+1); 3+3 only lengthens E^r or splits T^2 parity"
        )
    else:
        classification = CLASS_PARK
        decision = "PARK"
        reason = "the seam census is mixed and does not decide"
    return {
        "classification": classification,
        "decision": decision,
        "reason": reason,
        "finite_22": finite,
        "both_legal_occupied": both_occ,
        "return_o_empty": return_o_empty,
        "left_ooe_empty": left_ooe_empty,
        "launch_both_subtypes": launch_both,
        "oee_open": oee_open,
        "eee_open": eee_open,
        "new_emptiness": new_emptiness,
        "new_inequality": new_inequality,
        "leftover_killer": False,
        "reopens_entry_corridor": False,
        "halt_theorem": False,
        "raise_n0": False,
        "paper_a_edit": False,
        "archived": list(ARCHIVED),
    }


def probe_payload(*, n: int = START) -> dict[str, Any]:
    oe = run_layer(n, 1)
    deep_ge_n = sum(run_layer(n, a)["n_ge_n"] for a in (2, 3, 4))
    launch = launch_split()
    oee = oee_search(n)
    eee = eee_witness(n)
    payload = {
        "bound": "cyclic_seam",
        "n": n,
        "published_floor": PUBLISHED_FLOOR,
        "n_is_cyclemin_launch": launch_word(n) in {"OOE", "OOO"},
        "forced": {
            "start_odd": True,
            "start_oo": True,
            "end_even": True,
            "end_odd_forbidden": True,
            "last_odd_run_le_one": True,
            "lean": list(ARCHIVED[:5]),
        },
        "window_22": {
            "legal": list(LEGAL_22),
            "forbidden": list(FORBIDDEN_22),
            "note": "right OO and last E are Lean; left letter is O or E",
        },
        "window_33": {
            "legal": list(LEGAL_33),
            "note": (
                "left OOE is the forbidden last odd-run >= 2; "
                "right third letter is T^2(n) parity"
            ),
        },
        "inequalities": type_inequalities(),
        "occupancy": {
            "oe_ge_n": oe["n_ge_n"],
            "oe_min_v": oe["min_v"],
            "left_ooe_ge_n": deep_ge_n,
            "ee_count": ee_entry_count(n),
            "odd_return": odd_preimage(n),
            "odd_return_ge_n": odd_return_ge_n(n),
            "entry_cell": entry_even_cell(n),
        },
        "launch_split": launch,
        "oee": oee,
        "eee": eee,
    }
    payload["decision"] = classify(payload)
    return payload


def write_artifacts(payload: dict[str, Any] | None = None) -> dict[str, Any]:
    data = payload if payload is not None else probe_payload()
    SEAM_DIR.mkdir(parents=True, exist_ok=True)
    path = SEAM_DIR / "summary.json"
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
                "legal_22": payload["window_22"]["legal"],
                "oe_ge_n": payload["occupancy"]["oe_ge_n"],
                "ee_count": payload["occupancy"]["ee_count"],
                "odd_return_ge_n": payload["occupancy"]["odd_return_ge_n"],
                "left_ooe_ge_n": payload["occupancy"]["left_ooe_ge_n"],
                "launch_split": payload["launch_split"],
                "oee_found": payload["oee"]["found"],
                "eee_found": payload["eee"]["found"],
                "decision": decision,
            },
            indent=2,
        )
    )


if __name__ == "__main__":
    main()
