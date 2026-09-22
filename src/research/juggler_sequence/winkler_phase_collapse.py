"""Winkler's normalised first-passage count is a function of the phase alone.

Question. Winkler's public Corollary 12 (arXiv:2609.22303) normalises A100982 by its
lower cycle bound,

    R+_r = r c_r / C_r,   c_r = A100982(r),   C_r = binom(m_r - 1, r - 1),
    m_r = floor(r alpha),   alpha = log2 3,

and proves liminf R+_r = 1 and limsup R+_r = alpha / (alpha - 1), both on the record
orders of {r alpha}. That is a statement about two sparse sets of orders. The question
here is what happens at every other order: does R+_r depend on r only through the phase
delta_r = {r alpha}?

Method. c_r comes from this laboratory's own survivor counts, through
M_d = 2 N_(d-1) - N_d and c_r = M_(m_r + 1) (J-winkler-sandwich-holds-on-the-laboratory-
counts), with N_d from ``jump_spectrum.survivor_counts``, the height program behind
Paper B's jump spectrum. Binning R+_r by delta_r measures the collapse in three disjoint
windows of r; shuffling delta_r among the orders is the control that must destroy it.
One-sided means across the orbit points {n alpha} measure the jumps, against control
points at the midpoints of the widest gaps between the first forty orbit points.

Relation. This is the delta-side counterpart of Paper B's prefactor psi, whose jumps sit
on the orbit {n beta}, beta = log 2 / log 3 (J-paper-b-meander-prefactor-is-almost-
periodic, J-paper-b-jump-spectrum-is-the-survivor-sequence).

Status. Computationally verified, not proved: the existence of the limit profile is the
same missing local limit theorem as for psi (J-paper-b-tilt-reduction-and-the-phase-
factor). Not a halt theorem.
"""

from __future__ import annotations

import math
import random
from dataclasses import dataclass

from research.juggler_sequence.jump_spectrum import survivor_counts

ALPHA = math.log2(3.0)
#: Winkler's Corollary 12 upper envelope, printed there as 2.7095112914.
UPPER = ALPHA / (ALPHA - 1.0)
DEPTH = 5000
BINS = 20
JUMP_WINDOW = 0.006


@dataclass(frozen=True)
class Order:
    r: int
    delta: float
    ratio: float
    count: int


def orders(depth: int = DEPTH) -> list[Order]:
    """Every order r with m_r + 1 <= depth: its phase, R+_r and c_r = M_(m_r + 1)."""
    n = survivor_counts(depth)
    out: list[Order] = []
    r = 1
    while True:
        m = (3**r).bit_length() - 1  # floor(r log2 3), exact
        if m + 1 > depth:
            break
        c = 2 * n[m] - n[m + 1]
        out.append(Order(r, r * ALPHA - m, (r * c) / math.comb(m - 1, r - 1), c))
        r += 1
    return out


def binned(rows: list[Order], bins: int = BINS) -> dict[str, object]:
    """Bin R+ by phase: bin means, across-bin range, count-weighted within-bin sd."""
    groups: list[list[float]] = [[] for _ in range(bins)]
    for row in rows:
        groups[min(int(row.delta * bins), bins - 1)].append(row.ratio)
    means = [sum(g) / len(g) for g in groups]
    sds = [math.sqrt(sum((x - mu) ** 2 for x in g) / len(g)) for g, mu in zip(groups, means)]
    weight = sum(len(g) for g in groups)
    spread = sum(sd * len(g) for sd, g in zip(sds, groups)) / weight
    span = max(means) - min(means)
    return {"means": means, "range": span, "spread": spread, "signal": span / spread}


def windows(rows: list[Order]) -> list[tuple[int, int]]:
    """Three disjoint, doubling windows of order indices: [n/8, n/4), [n/4, n/2), [n/2, n)."""
    n = len(rows)
    return [(n // 8, n // 4), (n // 4, n // 2), (n // 2, n)]


def shape_drift(rows: list[Order]) -> list[float]:
    """Standard deviation of the per-bin differences between successive windows."""
    shapes = [binned(rows[lo:hi])["means"] for lo, hi in windows(rows)]
    out = []
    for a, b in zip(shapes, shapes[1:]):
        diff = [x - y for x, y in zip(a, b)]
        mu = sum(diff) / len(diff)
        out.append(math.sqrt(sum((d - mu) ** 2 for d in diff) / len(diff)))
    return out


def shuffled(rows: list[Order], seed: int = 1) -> list[Order]:
    """The control: the same ratios with the phases permuted among the orders."""
    phases = [row.delta for row in rows]
    random.Random(seed).shuffle(phases)
    return [Order(row.r, d, row.ratio, row.count) for row, d in zip(rows, phases)]


def jump_at(rows: list[Order], x: float, eps: float = JUMP_WINDOW) -> float:
    """Right one-sided mean minus left one-sided mean of R+ across the phase x."""
    left = [row.ratio for row in rows if x - eps < row.delta < x]
    right = [row.ratio for row in rows if x < row.delta < x + eps]
    return sum(right) / len(right) - sum(left) / len(left)


def orbit_point(n: int) -> float:
    return (n * ALPHA) % 1.0


def control_points(first: int = 40, count: int = 6) -> list[float]:
    """Midpoints of the widest gaps between the first orbit points: off the orbit by rule."""
    pts = sorted([0.0] + [orbit_point(n) for n in range(1, first + 1)] + [1.0])
    gaps = sorted(((b - a, (a + b) / 2) for a, b in zip(pts, pts[1:])), reverse=True)
    return [mid for _, mid in gaps[:count]]


def probe_payload(depth: int = DEPTH) -> dict[str, object]:
    rows = orders(depth)
    late = rows[len(rows) // 3:]
    return {
        "depth": depth,
        "orders": len(rows),
        "head": [row.count for row in rows[:21]],
        "ratio_min": min(row.ratio for row in rows),
        "ratio_max": max(row.ratio for row in rows),
        "windows": [
            {"r": (rows[lo].r, rows[hi - 1].r), **binned(rows[lo:hi])} for lo, hi in windows(rows)
        ],
        "shape_drift": shape_drift(rows),
        "control_signal": binned(shuffled(rows[len(rows) // 2:]))["signal"],
        "orbit_jumps": {n: jump_at(late, orbit_point(n)) for n in range(1, 9)},
        "control_jumps": {round(x, 5): jump_at(late, x) for x in control_points()},
    }


def main() -> None:
    p = probe_payload()
    print("orders r = 1..%d from depth %d" % (p["orders"], p["depth"]))
    print("R+ in [%.6f, %.6f], Winkler's envelope [1, %.10f]" % (p["ratio_min"], p["ratio_max"], UPPER))
    for w in p["windows"]:
        print("  r in %s: range %.4f, spread %.4f, signal x%.1f" % (w["r"], w["range"], w["spread"], w["signal"]))
    print("  shape drift between windows: %s" % ", ".join("%.4f" % s for s in p["shape_drift"]))
    print("  shuffled-phase control: signal x%.2f" % p["control_signal"])
    print("  orbit jumps: " + ", ".join("n=%d %+.4f" % kv for kv in p["orbit_jumps"].items()))
    print("  control jumps: " + ", ".join("%.4f %+.4f" % kv for kv in p["control_jumps"].items()))


if __name__ == "__main__":
    main()
