"""Extend the shipped Theorem 4.6 snapshot with the finance survivors.

The browser never recomputes n_max. This script evaluates the certified
parity table (Paper A, Corollary 4.5 / Theorem 4.6) with the laboratory
code and writes the 141 survivors at the floor 10^6, each with its exact
o_min, its padded parity n_max, and its Proposition 4.9 lattice
coordinates (L, o) = a·v* + b·v_1054. The 42 run-packing deaths of
Theorem 4.8 are flagged. A survivor is a length the inequality did not
kill; it is not a candidate cycle.

Run from the repository root with the laboratory package installed:

    python web/juggler-companion/scripts/export_finance_snapshot.py
"""

from __future__ import annotations

import json
import sys
from pathlib import Path

from research.juggler_sequence.cycle_finance import parity_finance_rows

sys.path.insert(0, str(Path(__file__).resolve().parent))
from export_finance_ledgers import attach_ledgers

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / "src" / "data" / "finance.json"
REPO = ROOT.parents[1]
BUDGET_OPT = REPO / "data" / "research" / "juggler" / "cycle_finance" / "budget_opt.json"

FLOOR = 1_000_000
L_CAP = 100_000
V_STAR = (25781, 16266)
V_1054 = (1054, 665)
PACKING_DEATH_START = 56347
PACKING_DEATH_COUNT = 42


def lattice_coordinates(length: int, odd_count: int) -> tuple[int, int]:
    """Solve (L, o) = a·v* + b·v_1054 with the unimodular inverse."""

    det = V_STAR[0] * V_1054[1] - V_1054[0] * V_STAR[1]
    if det != 1:
        raise RuntimeError(f"lattice basis is not unimodular: det = {det}")
    a = V_1054[1] * length - V_1054[0] * odd_count
    b = -V_STAR[1] * length + V_STAR[0] * odd_count
    if a * V_STAR[0] + b * V_1054[0] != length or a * V_STAR[1] + b * V_1054[1] != odd_count:
        raise RuntimeError(f"lattice inversion failed at L={length}")
    return a, b


def packing_deaths() -> set[int]:
    """Theorem 4.8: the 42 lengths 56347 + 1054k, cross-checked against the lab artifact."""

    progression = {PACKING_DEATH_START + V_1054[0] * k for k in range(PACKING_DEATH_COUNT)}
    if BUDGET_OPT.exists():
        payload = json.loads(BUDGET_OPT.read_text(encoding="utf-8"))
        killed = payload.get("killed_by_budget")
        if isinstance(killed, list) and killed and isinstance(killed[0], int):
            if set(killed) != progression:
                raise RuntimeError("budget_opt.json killed_by_budget disagrees with 56347 + 1054k")
    return progression


def main() -> None:
    if not OUT.exists():
        raise SystemExit(f"missing {OUT}; the base Theorem 4.6 snapshot must exist")
    snapshot = json.loads(OUT.read_text(encoding="utf-8"))
    if snapshot["floor"] != FLOOR or snapshot["lCap"] != L_CAP:
        raise SystemExit("finance.json floor or cap does not match this exporter")

    rows = parity_finance_rows(L_CAP)
    survivors = [row for row in rows if row["n_max"] > FLOOR]
    lengths = [row["L"] for row in survivors]
    if lengths != snapshot["exceptionLengths"]:
        raise SystemExit("recomputed survivor set differs from the shipped exceptionLengths")

    deaths = packing_deaths()
    slices: dict[int, int] = {}
    payload_rows = []
    for row in survivors:
        a, b = lattice_coordinates(row["L"], row["o"])
        death = row["L"] in deaths
        if not death:
            slices[a] = slices.get(a, 0) + 1
        payload_rows.append(
            {
                "L": row["L"],
                "o": row["o"],
                "nMax": row["n_max"],
                "a": a,
                "b": b,
                "packingDeath": death,
            }
        )
    if sum(1 for row in payload_rows if row["packingDeath"]) != PACKING_DEATH_COUNT:
        raise SystemExit("packing deaths are not all inside the survivor set")

    slice_counts = [slices.get(1, 0), slices.get(2, 0), slices.get(3, 0)]
    if slice_counts != [29, 47, 23]:
        raise SystemExit(f"lattice slices {slice_counts} differ from Proposition 4.9")

    snapshot["survivors"] = payload_rows
    attach_ledgers(snapshot)
    snapshot["lattice"] = {
        "vStar": list(V_STAR),
        "v1054": list(V_1054),
        "determinant": 1,
        "sliceCounts": slice_counts,
        "packingDeaths": PACKING_DEATH_COUNT,
        "runSurvivors": len(payload_rows) - PACKING_DEATH_COUNT,
        "note": "Proposition 4.9: a change of coordinates for (L, o_min), not a relation between hypothetical cycles.",
    }
    OUT.write_text(json.dumps(snapshot, indent=1) + "\n", encoding="utf-8")
    print(
        f"wrote {OUT}: {len(payload_rows)} survivors, "
        f"{PACKING_DEATH_COUNT} packing deaths, slices {slice_counts}"
    )


if __name__ == "__main__":
    sys.exit(main())
