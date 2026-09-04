"""Ship Movement-1 necklace walks. The browser looks them up.

    python web/juggler-companion/scripts/export_necklace_presets.py
"""

from __future__ import annotations

import json
import sys
from pathlib import Path

sys.set_int_max_str_digits(0)

from research.juggler_sequence.power_itineraries import floor_power

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / "src" / "data" / "necklace_presets.json"

PRESETS = (
    {
        "id": "365",
        "n": 365,
        "word": "OOEOOEOOEOOEOEEEOOEEE",
        "label": "365 · six excursions",
        "hint": "The finance-leftover shape: four OOE climbs, then the wave falls through n. Not a cycle minimum.",
    },
    {
        "id": "1999",
        "n": 1999,
        "word": "OOEOOOOEEOOE",
        "label": "1999 · rising valleys",
        "hint": "Valleys 1999 → 5169 → 50093 → 193753: the four consecutive expanding blocks of §6. The first peak overshoots; nothing lands.",
    },
    {
        "id": "o7eeee-5",
        "n": 5,
        "word": "OOOOOOOEEEE",
        "label": "O⁷EEEE at 5",
        "hint": "The CycleMin-shaped survivor tried on a real start: the walk leaves the word at the third letter.",
    },
    {
        "id": "37",
        "n": 37,
        "word": "OOOOEOOOEEOOEEEEE",
        "label": "37 · the note peak",
        "hint": "Three blocks, then a tower of evens. The second peak is the printed 24,906,114,455,136, far above (n+1)².",
    },
    {
        "id": "173",
        "n": 173,
        "word": "OOEOOOOOOOOEOOEOOEEOEEOEEEOEOEEE",
        "label": "173 · peak",
        "hint": "Classical high peak: 272 bits, then it falls to 1. One trajectory, not a theorem.",
    },
    {
        "id": "2183",
        "n": 2183,
        "word": "OOEOOOOEOOOOOOOOEOOOEOOOOOOOEOOOEEEOOOEEEEEEOEEOEEOOEEOOOOEEOEEOEEOOOEEE",
        "label": "2183 · peak bits",
        "hint": "Five expanding blocks. Peak 19,694 bits — the largest peak that still ships. Not a cycle.",
    },
    {
        "id": "3889",
        "n": 3889,
        "word": "OOOOOEOEOOOEOOEOEOEOOOOOOEOOOEOEOOOEOOOOOEEOEOEEOEOEEOOOEEOEOOEEOOEEOOOOOEEEEEEE",
        "label": "3889 · delay",
        "hint": "Longest shipped drop to 1: 80 steps. The n≤4000 delay record. Not a cycle.",
    },
)


def walk(n: int, word: str) -> list[str]:
    states = [n]
    current = n
    for _ in word:
        current = floor_power(current)
        states.append(current)
    return [str(state) for state in states]


def main() -> int:
    rows = []
    for spec in PRESETS:
        states = walk(int(spec["n"]), spec["word"])
        rows.append(
            {
                "id": spec["id"],
                "n": str(spec["n"]),
                "word": spec["word"],
                "states": states,
                "label": spec["label"],
                "hint": spec["hint"],
            }
        )
        peak = max(int(state) for state in states)
        print(f"{spec['id']}: {len(states)} states, peak bits {peak.bit_length()}")
    payload = {
        "note": "Shipped Movement-1 necklace walks. The browser does not recompute these.",
        "presets": rows,
    }
    OUT.write_text(json.dumps(payload, indent=1) + "\n", encoding="utf-8")
    print(f"wrote {OUT} ({OUT.stat().st_size} bytes)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
