"""Ship θ(L) and the constant-1 crossing. The browser only looks them up.

Exact θ = 1 − 2^L / 3^{o_min} is an integer ratio. The crossing is the
largest real n with n ln n ≤ L/θ. Both are written next to the shipped
o_min so the React chart never builds 3^o.

    python web/juggler-companion/scripts/export_finance_ledgers.py
"""

from __future__ import annotations

import json
import math
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / "src" / "data" / "finance.json"
DIGITS = 12


def theta_decimal(length: int, odd_count: int) -> str:
    den = 3**odd_count
    num = den - (1 << length)
    if num <= 0:
        raise RuntimeError(f"non-positive surplus at L={length}, o={odd_count}")
    scaled = (num * 10**DIGITS) // den
    text = str(scaled).zfill(DIGITS + 1)
    return f"{text[:-DIGITS]}.{text[len(text) - DIGITS :]}"


def theta_approx(length: int, odd_count: int) -> float:
    return -math.expm1(length * math.log(2) - odd_count * math.log(3))


def constant_one_crossing(length: int, theta: float) -> float:
    if theta <= 0:
        raise RuntimeError(f"non-positive theta at L={length}")
    target = length / theta
    lo = 2.0
    hi = 2.0
    while hi * math.log(hi) < target:
        hi *= 2.0
    for _ in range(200):
        mid = (lo + hi) / 2.0
        if mid * math.log(mid) < target:
            lo = mid
        else:
            hi = mid
    return lo


def ledger_row(length: int, odd_count: int) -> dict[str, float | int | str]:
    approx = theta_approx(length, odd_count)
    return {
        "L": length,
        "o": odd_count,
        "theta": approx,
        "thetaDecimal": theta_decimal(length, odd_count),
        "crossing": constant_one_crossing(length, approx),
    }


def attach_ledgers(snapshot: dict) -> list[dict]:
    seen: dict[int, int] = {}
    for row in snapshot.get("records", []):
        seen[int(row["L"])] = int(row["o"])
    for row in snapshot.get("survivors", []):
        seen[int(row["L"])] = int(row["o"])
    ledgers = [ledger_row(length, odd_count) for length, odd_count in sorted(seen.items())]
    snapshot["ledgers"] = ledgers
    return ledgers


def main() -> int:
    snapshot = json.loads(OUT.read_text(encoding="utf-8"))
    ledgers = attach_ledgers(snapshot)
    OUT.write_text(json.dumps(snapshot, indent=1) + "\n", encoding="utf-8")
    print(f"wrote {OUT}: {len(ledgers)} ledgers")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
