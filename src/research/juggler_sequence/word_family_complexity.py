"""Best contagion root over admissible word families, by nested-floor complexity.

Question (depth-five dossier, Result 27): the Juggler/3n-1 bridge shares the word
combinatorics and Paper C's ideal coefficients ``3^(-#O)``. Does some family of
parity words other than the first-descent words reach a higher contagion root
for the same analytic difficulty?

A word is admissible as a production when every nonempty suffix has multiplier
``rho < 1``. Only then does every target's fibre form a window of many sources;
a word ending in ``O`` gives empty fibres for most targets. Difficulty is
measured by the *nested growing factors*. Let ``R_i`` be the real whose floor is
``J^i n``, with exponent ``e_i``, for ``1 <= i < |w|``. A floor taken at ``R_j``
with ``j >= 2`` reaches ``R_i`` with coefficient about ``n^(e_i - e_j)``, and
the factor is growing when that exponent is positive. First-level carries of
``floor(X)`` are excluded, since Lemma 4.4 handles them. The optimum over
prefix-free families is computed by a tree recursion for each ``lambda``. The
root uses ideal coefficients, and ``E`` at coefficient ``1``. This is pricing
only; it proves no production.
"""

from __future__ import annotations

import json
from fractions import Fraction
from functools import lru_cache
from pathlib import Path

from research.experiments.outputs import artifact_path
from research.experiments.provenance import write_manifest
from research.juggler_sequence.depth_five_production import rho
from research.juggler_sequence.lean_paths import DATA_ROOT

DATA_DIR = DATA_ROOT / "depth_five_production" / "word_families"
MAX_LEN = 14

CLASSES = {
    "no nested growing factor": lambda g: not g,
    "one factor <= 9/16": lambda g: len(g) <= 1 and (not g or g[0] <= Fraction(9, 16)),
    "one factor <= 9/8": lambda g: len(g) <= 1 and (not g or g[0] <= Fraction(9, 8)),
    "factors <= 9/8": lambda g: not g or g[0] <= Fraction(9, 8),
    "factors <= 27/16": lambda g: not g or g[0] <= Fraction(27, 16),
    "factors <= 45/16": lambda g: not g or g[0] <= Fraction(45, 16),
    "unrestricted": lambda g: True,
}


def admissible(word: str) -> bool:
    """Every nonempty suffix contracts, so every target's fibre is a window."""
    return bool(word) and all(rho(word[i:]) < 1 for i in range(len(word)))


def growing_factors(word: str) -> list[Fraction]:
    """Positive exponents ``e_i - e_j`` over nested pairs ``2 <= j < i``, descending."""
    e, x = [], Fraction(1)
    for ch in word[:-1]:
        x *= Fraction(3, 2) if ch == "O" else Fraction(1, 2)
        e.append(x)
    return sorted((e[i] - e[j] for i in range(len(e)) for j in range(1, i) if e[i] > e[j]),
                  reverse=True)


def best_family(lam: float, allowed) -> tuple[float, tuple[str, ...]]:
    """Largest ``sum c_w rho_w^lam`` over prefix-free admissible allowed families."""
    @lru_cache(maxsize=None)
    def value(word: str) -> tuple[float, tuple[str, ...]]:
        stop = 0.0
        if admissible(word) and allowed(growing_factors(word)):
            stop = 3.0 ** -word.count("O") * float(rho(word)) ** lam
        if len(word) >= MAX_LEN:
            return stop, (word,) if stop else ()
        a, la = value(word + "O")
        b, lb = value(word + "E")
        return (stop, (word,) if stop else ()) if stop >= a + b else (a + b, la + lb)

    total, leaves = value("O")
    return 0.5 ** lam + total, leaves


def class_root(allowed) -> tuple[float, tuple[str, ...]]:
    lo, hi = 0.0, 1.0
    for _ in range(40):
        mid = (lo + hi) / 2
        if best_family(mid, allowed)[0] > 1:
            lo = mid
        else:
            hi = mid
    return lo, best_family(lo, allowed)[1]


def table() -> dict:
    rows = []
    for name, allowed in CLASSES.items():
        lam, leaves = class_root(allowed)
        ordered = sorted(leaves, key=lambda w: (len(w), w))
        rows.append({"class": name, "root": lam, "word_count": len(ordered),
                     "max_length": max(map(len, ordered)), "first_words": ordered[:12]})
    depth_seven = {w: [str(g) for g in growing_factors(w)]
                   for w in ("OOEOOEE", "OOOEOEE", "OOOOEEE")}
    return {"max_length": MAX_LEN, "classes": rows, "depth_seven_factors": depth_seven}


def run(output_root: Path | None = None) -> Path:
    out_dir = artifact_path(DATA_DIR, output_root)
    out_dir.mkdir(parents=True, exist_ok=True)
    out = out_dir / "classes.json"
    out.write_text(json.dumps(table(), indent=1) + "\n", encoding="utf-8", newline="\n")
    return write_manifest(
        out_dir / "run.research.json", programme="juggler",
        research_id="juggler/depth_five_production",
        scope=f"prefix-free families of admissible words of length <= {MAX_LEN}",
        parameters={"max_length": MAX_LEN, "classes": list(CLASSES)},
        outputs=[out], sources=[Path(__file__)],
    )


if __name__ == "__main__":
    print(run())
