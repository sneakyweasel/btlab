"""Phase-0 probe for ``depth_five_production``.

Question: what contagion exponent could actual productions along the depth-five
first-descent words OOOEE and OOEOE buy, and what fibre geometry would those
productions have to control? This prices the step; it proves no production and
is not a halt theorem.

A word ``w`` with ``a`` odd and ``b`` even letters has multiplier
``rho_w = (3/2)^a (1/2)^b``. Paper C's ideal coefficient (5.7) is
``2^{-|w|} / rho_w``, the log-mass coefficient of a fibre carrying its fair share.
The first-descent words (``rho < 1`` for the first time at the last letter) form a
prefix-free family; the ideal contagion exponent of the depth-``d`` family is the
root in ``(0, 1]`` of ``sum_w 2^{-|w|} rho_w^(lambda - 1) = 1``. A fibre of target
``m`` has sources near ``P = m^(1/rho)`` and spans a window of length about
``P^(1 - rho)``, which is what any per-fibre parity estimate must control.
"""

from __future__ import annotations

import json
from fractions import Fraction
from pathlib import Path

from research.experiments.outputs import artifact_path
from research.experiments.provenance import write_manifest
from research.juggler_sequence.lean_paths import DATA_ROOT

DATA_DIR = DATA_ROOT / "depth_five_production"
MAX_DEPTH = 12

#: Coefficients of the kernel-checked depth-four assembly (FateOOEEAssembly).
CERTIFIED_DEPTH_FOUR = {"E": Fraction(1), "OE": Fraction(33, 100), "OOEE": Fraction(11, 100)}


def rho(word: str) -> Fraction:
    """Multiplier ``(3/2)^a (1/2)^b`` of a word with ``a`` odd and ``b`` even letters."""
    return Fraction(3, 2) ** word.count("O") * Fraction(1, 2) ** word.count("E")


def ideal_coefficient(word: str) -> Fraction:
    """Paper C (5.7): ``2^{-|w|} / rho_w``; equal to ``3^{-a}``."""
    return Fraction(1, 2 ** len(word)) / rho(word)


def first_descent_words(max_len: int) -> list[str]:
    """Words whose multiplier drops below one for the first time at the last letter."""
    out: list[str] = []

    def grow(word: str) -> None:
        if len(word) > max_len:
            return
        if word and rho(word) < 1:
            out.append(word)
            return
        grow(word + "O")
        grow(word + "E")

    grow("")
    return sorted(out, key=lambda w: (len(w), w))


def root(coefficients: dict[str, Fraction], tol: float = 1e-12) -> float:
    """Largest ``lambda`` in ``[0, 1]`` with ``sum c_w rho_w^lambda >= 1`` (bisection)."""
    def excess(lam: float) -> float:
        return sum(float(c) * float(rho(w)) ** lam for w, c in coefficients.items()) - 1.0

    if excess(1.0) >= 0:
        return 1.0
    lo, hi = 0.0, 1.0
    while hi - lo > tol:
        mid = (lo + hi) / 2
        lo, hi = (mid, hi) if excess(mid) > 0 else (lo, mid)
    return lo


def price(max_depth: int = MAX_DEPTH) -> dict:
    """Ideal roots by depth and the fibre window exponent of every first-descent word."""
    words = first_descent_words(max_depth)
    depths = []
    for d in range(1, max_depth + 1):
        family = {w: ideal_coefficient(w) for w in words if len(w) <= d}
        lam = root(family)
        depths.append({
            "depth": d,
            "words": len(family),
            "new_words": [w for w in words if len(w) == d],
            "kraft": str(sum(Fraction(1, 2 ** len(w)) for w in family)),
            "ideal_root": lam,
            "required_rate": 1 - lam,
        })
    per_word = [{
        "word": w,
        "rho": str(rho(w)),
        "ideal_coefficient": str(ideal_coefficient(w)),
        "window_exponent_in_P": str(1 - rho(w)),
        "window_exponent_in_m": str(1 / rho(w) - 1),
    } for w in words if len(w) <= 5]
    return {
        "depths": depths,
        "words": per_word,
        "certified_depth_four_root": root(CERTIFIED_DEPTH_FOUR),
    }


def run(output_root: Path | None = None) -> Path:
    """Write the pricing table and its manifest."""
    out_dir = artifact_path(DATA_DIR, output_root)
    out_dir.mkdir(parents=True, exist_ok=True)
    table = out_dir / "pricing.json"
    table.write_text(json.dumps(price(), indent=1) + "\n", encoding="utf-8", newline="\n")
    return record_outputs([table], scope=f"first-descent words of length <= {MAX_DEPTH}",
                          parameters={"max_depth": MAX_DEPTH}, output_root=output_root)


def record_outputs(
    outputs: list[Path], *, scope: str, parameters: dict, output_root: Path | None = None
) -> Path:
    """Call after generating outputs; supply the actual finite scope and parameters."""
    return write_manifest(
        artifact_path(DATA_DIR, output_root) / "run.research.json", programme="juggler",
        research_id="juggler/depth_five_production", scope=scope, parameters=parameters,
        outputs=outputs, sources=[Path(__file__)],
    )


if __name__ == "__main__":
    print(run())
