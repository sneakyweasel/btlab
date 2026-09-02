"""Export shipped monster orbits for the reviewer companion.

Live exploration walks in the browser up to 256 bits. These records
exceed that cap, so the site loads them from JSON and never recomputes
n_max-scale arithmetic. Not a halt theorem: each row is one orbit.
"""

from __future__ import annotations

import json
import sys
from pathlib import Path

sys.set_int_max_str_digits(20_000)

from research.juggler_sequence.power_words import floor_power

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / "src" / "data" / "monster_orbits.json"

# Peaks exceed DISPLAY_BITS_MAX = 256. Skip million-bit flyers.
MONSTERS = (
    {
        "n": 173,
        "label": "173 peak",
        "blurb": "Classical high peak. Exceeds the live 256-bit walker.",
    },
    {
        "n": 193,
        "label": "193 delay",
        "blurb": "Laboratory delay record. Long stay above the start.",
    },
    {
        "n": 761,
        "label": "761 adversary",
        "blurb": "Fan climb and collapse on one prefix. Display only.",
    },
    {
        "n": 2183,
        "label": "2183 five-block",
        "blurb": "Five persistent-expanding blocks. Peak is far above 256 bits.",
    },
    {
        "n": 3889,
        "label": "3889 hard",
        "blurb": "Hard canonical start. Peak exceeds the live walker.",
    },
)

STEP_CAP = 200
BIT_REJECT = 25_000


def walk(n: int) -> dict:
    states = [n]
    letters: list[str] = []
    current = n
    peak = n
    for _ in range(STEP_CAP):
        if current.bit_length() > BIT_REJECT:
            raise RuntimeError(f"{n} exceeded {BIT_REJECT} bits")
        letter = "O" if current % 2 else "E"
        letters.append(letter)
        current = floor_power(current)
        states.append(current)
        if current > peak:
            peak = current
        if current == 1:
            break
    else:
        raise RuntimeError(f"{n} did not reach 1 in {STEP_CAP} steps")
    return {
        "n": str(n),
        "word": "".join(letters),
        "states": [str(state) for state in states],
        "peak": str(peak),
        "peakBits": peak.bit_length(),
        "reachedOne": states[-1] == 1,
        "steps": len(states) - 1,
    }


def main() -> None:
    rows = []
    for spec in MONSTERS:
        row = walk(int(spec["n"]))
        row["label"] = spec["label"]
        row["blurb"] = spec["blurb"]
        rows.append(row)
        print(
            f"{spec['n']}: steps={row['steps']} peak_bits={row['peakBits']} "
            f"digits={len(row['peak'])}"
        )
    payload = {
        "bitCapLive": 256,
        "note": "Shipped orbits whose peak exceeds the live 256-bit walker. One orbit each, not a theorem.",
        "orbits": rows,
    }
    OUT.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")
    print(f"wrote {OUT} ({OUT.stat().st_size} bytes)")


if __name__ == "__main__":
    main()
