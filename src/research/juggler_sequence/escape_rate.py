"""Phase-0 probe for ``escape_rate``.

Question: does counting escaping starts give a premise for excluding divergent
orbits that is weaker, and more reachable, than the failure rate? The Lean
corollary ``no_escape_of_escape_rate`` turns an escape rate above ``3/8`` into the
absence of divergent orbits. This probe checks the fair-coin model behind the
natural route to such a rate, Ville's maximal inequality. It proves nothing about
actual orbits and is not a halt theorem.

In the fair model a word's multiplier ``rho_k = (3/2)^a (1/2)^b`` after ``k`` letters
is a martingale (each letter multiplies it by ``3/2`` or ``1/2`` with mean one), and
``log x_k = rho_k log x_0``. Ville's inequality gives
``P(max_{k <= d} rho_k >= R) <= 1/R`` for every depth ``d``. The probe counts the
words exactly, so a height ``H = x_0^R`` is ever reached with fair frequency at
most ``1/R = log x_0 / log H``. Transferring this to actual starts needs fair
parity counts at every depth, which is the all-depth equidistribution program.
"""

from __future__ import annotations

import json
from fractions import Fraction
from pathlib import Path

from research.experiments.outputs import artifact_path
from research.experiments.provenance import write_manifest
from research.juggler_sequence.lean_paths import DATA_ROOT

DATA_DIR = DATA_ROOT / "escape_rate"
MAX_DEPTH = 60
THRESHOLDS = (2, 4, 16, 256)


def rho(odd: int, even: int) -> Fraction:
    """Multiplier of a word with ``odd`` odd and ``even`` even letters."""
    return Fraction(3, 2) ** odd * Fraction(1, 2) ** even


def hitting_fraction(depth: int, threshold: int) -> Fraction:
    """Exact fair-word frequency of ``max_{k <= depth} rho_k >= threshold``.

    Dynamic programming over the odd count of unabsorbed prefixes; a prefix is
    absorbed the first time its multiplier reaches the threshold.
    """
    live = {0: Fraction(1)}
    hit = Fraction(0)
    for k in range(depth):
        nxt: dict[int, Fraction] = {}
        for odd, weight in live.items():
            for step_odd in (1, 0):
                a = odd + step_odd
                half = weight / 2
                if rho(a, k + 1 - a) >= threshold:
                    hit += half
                else:
                    nxt[a] = nxt.get(a, Fraction(0)) + half
        live = nxt
    return hit


def ville_table(max_depth: int = MAX_DEPTH) -> list[dict]:
    """Hitting frequency against the Ville bound ``1/R`` at several depths."""
    rows = []
    for threshold in THRESHOLDS:
        for depth in (10, 20, 40, max_depth):
            frac = hitting_fraction(depth, threshold)
            rows.append({
                "threshold": threshold,
                "depth": depth,
                "hitting_fraction": float(frac),
                "ville_bound": 1 / threshold,
                "within_bound": frac <= Fraction(1, threshold),
            })
    return rows


def run(output_root: Path | None = None) -> Path:
    """Write the Ville table and its manifest."""
    out_dir = artifact_path(DATA_DIR, output_root)
    out_dir.mkdir(parents=True, exist_ok=True)
    table = out_dir / "ville.json"
    table.write_text(json.dumps(ville_table(), indent=1) + "\n", encoding="utf-8", newline="\n")
    return record_outputs([table], scope=f"fair binary words of length <= {MAX_DEPTH}",
                          parameters={"max_depth": MAX_DEPTH, "thresholds": list(THRESHOLDS)},
                          output_root=output_root)


def record_outputs(
    outputs: list[Path], *, scope: str, parameters: dict, output_root: Path | None = None
) -> Path:
    """Call after generating outputs; supply the actual finite scope and parameters."""
    return write_manifest(
        artifact_path(DATA_DIR, output_root) / "run.research.json", programme="juggler",
        research_id="juggler/escape_rate", scope=scope, parameters=parameters,
        outputs=outputs, sources=[Path(__file__)],
    )


if __name__ == "__main__":
    print(run())
