"""Structural check of Lemma E7's ``U``-carry decomposition for ``OOEOE``.

Lemma E7 (``docs/problems/juggler_depth_five_production.md``, Result 19) writes the
differenced phase ``phi(n+2d) - phi(n)``, with ``phi = (iX + lU + kW)/2`` and
Paper B's Section 4.3 coordinates, as a smooth phase ``F_{G,kappa}`` on cells of
``G = floor(S)``, ``S = (x+2d)^(9/8) - x^(9/8)``, where ``kappa`` is the carry of
``floor(U)``. It charges the difference to four sources:

- replacing ``B(n+2d)`` by ``B(n)``, about ``k d P^(-7/16)`` per point;
- the theta cancellation residual, ``k d P^(-13/16)``;
- the Taylor remainder, ``k P^(-9/16)``;
- the ``l``-noise, ``l P^(-3/8)``.

On actual odd ``n`` near ``P``, with integer square roots for every floor and
50-digit arithmetic, this module measures the pointwise distance to the nearest
integer between the exact phase difference and the model, both before and after
restoring the ``B`` replacement. It also counts the carry mismatches directly.
The model covers ``j = 0``, the case that carries E7's new cancellation. This is
a finite check of an identity and its error orders; it proves nothing
asymptotic.
"""

from __future__ import annotations

import json
from math import isqrt
from pathlib import Path

from mpmath import mp, mpf, sqrt, floor, frac

from research.experiments.outputs import artifact_path
from research.experiments.provenance import write_manifest
from research.juggler_sequence.lean_paths import DATA_ROOT

DATA_DIR = DATA_ROOT / "depth_five_production" / "e7_structural"
SCALES = (10 ** 8, 10 ** 10)
SHIFTS = (1, 30, 300)
FREQUENCIES = ((0, 0, 1), (0, 1, 2), (3, -2, -1))
POINTS = 2000
MISMATCH_POINTS = 20000


def coordinates(n: int) -> tuple:
    """``X, U, W, floor(U)`` for Paper B's Section 4.3 chain at ``n``."""
    m = isqrt(n ** 3)
    v = isqrt(m ** 3)
    w = isqrt(v)
    return mpf(n) ** 1.5, sqrt(mpf(v)), mpf(w) ** 1.5, w


def _dist(t) -> float:
    f = frac(t)
    return float(min(f, 1 - f))


def residuals(P: int, d: int, i: int, l: int, k: int, points: int) -> dict:
    """Pointwise model errors and carry mismatches on ``points`` odd inputs from ``P``."""
    mp.dps = 50
    n = P + 1 if P % 2 == 0 else P
    raw, corrected, mismatches = [], [], 0
    for _ in range(points):
        X0, U0, W0, w0 = coordinates(n)
        X1, U1, W1, w1 = coordinates(n + 2 * d)
        exact = (i * (X1 - X0) + l * (U1 - U0) + k * (W1 - W0)) / 2
        x = mpf(n)
        S = (x + 2 * d) ** (mpf(9) / 8) - x ** (mpf(9) / 8)
        G = floor(S)
        kappa = 1 if frac(U0) >= 1 - (S - G) else 0
        mismatches += int(w1 - w0 != int(G) + kappa)
        B0 = mpf(3) * k / 4 * x ** (mpf(9) / 16)
        B1 = mpf(3) * k / 4 * (x + 2 * d) ** (mpf(9) / 16)
        model = (mpf(k) / 2 * ((x + 2 * d) ** (mpf(27) / 16) - x ** (mpf(27) / 16))
                 - B0 * (S - G - kappa) + mpf(i) / 2 * (X1 - X0) + mpf(l) / 2 * S)
        raw.append(_dist(exact - model))
        corrected.append(_dist(exact - model + (B1 - B0) * frac(U1)))
        n += 2
    raw.sort()
    corrected.sort()
    q = int(0.99 * points)
    return {
        "P": P, "d": d, "frequency": [i, 0, l, k], "points": points,
        "raw_median": raw[points // 2], "raw_p99": raw[q], "raw_max": raw[-1],
        "corrected_median": corrected[points // 2], "corrected_p99": corrected[q],
        "corrected_max": corrected[-1], "carry_mismatches": mismatches,
    }


def carry_mismatches(P: int, d: int, points: int) -> int:
    """Count odd ``n`` from ``P`` where ``floor(U)``'s gap differs from ``G + kappa``."""
    mp.dps = 50
    n = P + 1 if P % 2 == 0 else P
    count = 0
    for _ in range(points):
        v0, v1 = isqrt(isqrt(n ** 3) ** 3), isqrt(isqrt((n + 2 * d) ** 3) ** 3)
        x = mpf(n)
        S = (x + 2 * d) ** (mpf(9) / 8) - x ** (mpf(9) / 8)
        G = floor(S)
        kappa = 1 if frac(sqrt(mpf(v0))) >= 1 - (S - G) else 0
        count += int(isqrt(v1) - isqrt(v0) != int(G) + kappa)
        n += 2
    return count


def run(output_root: Path | None = None) -> Path:
    """Write the residual table and its manifest."""
    out_dir = artifact_path(DATA_DIR, output_root)
    out_dir.mkdir(parents=True, exist_ok=True)
    rows = [residuals(P, d, i, l, k, POINTS)
            for P in SCALES for d in SHIFTS for (i, l, k) in FREQUENCIES]
    table = out_dir / "residuals.json"
    counts = [{"P": SCALES[0], "d": d, "points": MISMATCH_POINTS,
               "carry_mismatches": carry_mismatches(SCALES[0], d, MISMATCH_POINTS)}
              for d in SHIFTS]
    table.write_text(json.dumps({"rows": rows, "mismatch_counts": counts}, indent=1) + "\n", encoding="utf-8", newline="\n")
    return write_manifest(
        out_dir / "run.research.json", programme="juggler",
        research_id="juggler/depth_five_production",
        scope=f"{POINTS} consecutive odd n from each P in {list(SCALES)}; d in {list(SHIFTS)}; "
              f"(i, j, l, k) in {[[i, 0, l, k] for (i, l, k) in FREQUENCIES]}",
        parameters={"scales": list(SCALES), "shifts": list(SHIFTS),
                    "frequencies": [list(f) for f in FREQUENCIES], "points": POINTS,
                    "mismatch_points": MISMATCH_POINTS, "mp_dps": 50},
        outputs=[table], sources=[Path(__file__)],
    )


if __name__ == "__main__":
    print(run())
