"""Insert rate-free Lean ledger rows. Temporary helper."""

from __future__ import annotations

import json
from pathlib import Path

JSON_PATH = Path("docs/theory/theorem_ledger.json")

rows = json.loads(JSON_PATH.read_text(encoding="utf-8"))
ids = [row["id"] for row in rows]
assert "J-rate-free-density-one" in ids
assert "J-rate-free-prop-j-finite" not in ids
assert "J-rate-free-floor-certificates" not in ids

for row in rows:
    if row["id"] == "J-rate-free-density-one":
        row["lean"] = "Problems/Juggler/RateFreeDensity.lean"

propj = {
    "id": "J-rate-free-prop-j-finite",
    "tag": "EXACT — LEAN VERIFIED",
    "statement": (
        "Finite Proposition J. If every length-d parity class w satisfies "
        "classCount w N * 2^d <= N + E * 2^d, then the number of starts in "
        "1..N whose length-d itinerary is prefix-noncontracting obeys "
        "uncertifiedCount d N * 2^d <= neverNegCount d * (N + E * 2^d). "
        "Any finite set of starts in 1..N with no coefficient stop sits "
        "inside that uncertified set. Lean theorem propJ_count. Not a "
        "density-one claim and not a halt theorem."
    ),
    "source": "docs/problems/juggler_k3_rate_free.md",
    "lean": "Problems/Juggler/RateFreeDensity.lean",
    "decl": "propJ_count",
    "lean_trust": "kernel",
    "tests": [
        "tests/research/juggler_sequence/test_k3_rate_free.py",
        "tests/research/juggler_sequence/test_layer_architecture.py",
    ],
    "related_conjectures": ["juggler_tower_rate_free_equidistribution"],
}

floor = {
    "id": "J-rate-free-floor-certificates",
    "tag": "EXACT — LEAN VERIFIED",
    "statement": (
        "If every positive m <= N0 reaches 1 and every n > N0 has "
        "FiniteProgress, then every positive n reaches 1. Lean theorem "
        "reachesOne_of_floor_and_certificates. The certificate hypothesis "
        "is universal, not a density statement. Not a halt theorem."
    ),
    "source": "docs/problems/juggler_k3_rate_free.md",
    "lean": "Problems/Juggler/RateFreeDensity.lean",
    "decl": "reachesOne_of_floor_and_certificates",
    "lean_trust": "kernel",
    "tests": [
        "tests/research/juggler_sequence/test_k3_rate_free.py",
        "tests/research/juggler_sequence/test_layer_architecture.py",
    ],
    "related_conjectures": [],
}

idx = ids.index("J-rate-free-density-one")
rows[idx + 1 : idx + 1] = [propj, floor]

JSON_PATH.write_text(
    json.dumps(rows, indent=1, ensure_ascii=False) + "\n",
    encoding="utf-8",
)
print("inserted", propj["id"], floor["id"])
