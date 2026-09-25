"""Exponent-level comparison of the two Hausdorff-dimension methods for K_alpha.

A slope is modelled by its convergent log-scales Lambda_k = log Q_k, as a periodic
pattern of elements:

* ``('g', t)``: a jump level, Lambda -> t Lambda with t > 1 (a large partial quotient);
* ``('d', rho)``: a dense stretch of bounded partial quotients, Lambda -> rho Lambda,
  taken in its t -> 1 limit.

Upper bound (the cell-cover recursion of the paper's Section 6.3 and Theorem 6.18a).
With W the logarithm of the inverse cover cost at a level and w = W / Lambda,

    jump:  w = max(3s/2 - 1, t w', max_{1<=y<=t} min(s + s y/2 - 1, t w' + t - y))
    dense: w = max(3s/2 - 1, rho w')

and H^s(K_alpha) = 0 when the periodic solution has w > 0.

Lower bound (the grid-window Cantor measure of Section 6.8). A window exponent
gamma in [1, t] at each jump level gives the mass deficit
A_n = Lambda_n - sum_{k<n} (gamma_k - 1) Lambda_k, and the Frostman inequality needs

    jump:  A_n >= s (Lambda_{n+1}/2 + (3 - gamma_n) Lambda_n / 2)
    dense: A >= (3s/2) Lambda throughout the stretch.

At a jump level the condition says that a window's mass is at most the s-th power
of the atom mass it carries, (d q_{n+1})^(-1/2) q_n^(-3/2).

Both recursions are floating-point exponent calculations. They drop constants and
lower-order terms and prove nothing; they locate where the two proof methods meet.
"""

from __future__ import annotations

import argparse
import json
import math
import random
from pathlib import Path

from research.experiments.provenance import write_manifest
from research.juggler_sequence.lean_paths import DATA_ROOT

Pattern = list[tuple[str, float]]


def upper_positive(pattern: Pattern, s: float, periods: int = 3000) -> bool:
    """Whether the cover recursion certifies H^s = 0 (the periodic solution has w > 0)."""
    floor = 1.5 * s - 1.0
    w = floor
    for _ in range(periods):
        for kind, t in reversed(pattern):
            if kind == 'd':
                w = max(floor, t * w)
                continue
            y = min(max((t * w + t - s + 1.0) / (1.0 + s / 2.0), 1.0), t)
            w = max(floor, t * w, min(s + s * y / 2.0 - 1.0, t * w + t - y))
            if w > 1e3:
                return True
    return w > 1e-12


def upper_dim(pattern: Pattern, periods: int = 3000, steps: int = 50) -> float:
    """Upper-bound threshold by bisection on s in [0, 2/3]."""
    lo, hi = 0.0, 2.0 / 3.0 + 1e-12
    for _ in range(steps):
        mid = (lo + hi) / 2
        if upper_positive(pattern, mid, periods):
            hi = mid
        else:
            lo = mid
    return hi


def lower_s(pattern: Pattern, gammas: list[float]) -> float:
    """Largest s the window measure with these exponents supports, in the periodic regime."""
    c, d = 1.0, 0.0
    it = iter(gammas)
    for kind, t in pattern:
        g = next(it) if kind == 'g' else 1.0
        c, d = c / t, (d + t - g) / t
    a = d / (1.0 - c)
    best = math.inf
    it = iter(gammas)
    for kind, t in pattern:
        if kind == 'g':
            g = next(it)
            best = min(best, a / (t / 2 + 1.5 - g / 2))
            a = (a + t - g) / t
        else:
            end = (a + t - 1.0) / t
            best = min(best, min(a, end) / 1.5)
            a = end
    return max(best, 0.0)


def _nelder_mead(f, x0: list[float], step: float = 1.0, iters: int = 6000,
                 tol: float = 1e-15) -> tuple[list[float], float]:
    """Minimise f by the Nelder-Mead simplex method (standard coefficients)."""
    n = len(x0)
    simplex = [x0[:]] + [[x0[j] + (step if j == i else 0.0) for j in range(n)] for i in range(n)]
    values = [f(x) for x in simplex]
    for _ in range(iters):
        order = sorted(range(n + 1), key=values.__getitem__)
        simplex = [simplex[i] for i in order]
        values = [values[i] for i in order]
        if values[-1] - values[0] < tol and iters > 50:
            spread = max(abs(simplex[i][j] - simplex[0][j]) for i in range(n + 1) for j in range(n))
            if spread < 1e-12:
                break
        centroid = [sum(simplex[i][j] for i in range(n)) / n for j in range(n)]
        worst = simplex[-1]
        reflect = [c + (c - w) for c, w in zip(centroid, worst)]
        fr = f(reflect)
        if values[0] <= fr < values[-2]:
            simplex[-1], values[-1] = reflect, fr
            continue
        if fr < values[0]:
            expand = [c + 2 * (c - w) for c, w in zip(centroid, worst)]
            fe = f(expand)
            simplex[-1], values[-1] = (expand, fe) if fe < fr else (reflect, fr)
            continue
        contract = [c + 0.5 * (w - c) for c, w in zip(centroid, worst)]
        fc = f(contract)
        if fc < values[-1]:
            simplex[-1], values[-1] = contract, fc
            continue
        best = simplex[0]
        simplex = [best] + [[b + 0.5 * (x - b) for b, x in zip(best, p)] for p in simplex[1:]]
        values = [values[0]] + [f(p) for p in simplex[1:]]
    i = min(range(n + 1), key=values.__getitem__)
    return simplex[i], values[i]


def lower_dim(pattern: Pattern, restarts: int = 25, seed: int = 0) -> tuple[float, list[float]]:
    """Maximise ``lower_s`` over window exponents gamma_i in [1, t_i] (restarted Nelder-Mead
    on a logistic parametrisation, then a second simplex from the best point)."""
    rng = random.Random(seed)
    tops = [t for kind, t in pattern if kind == 'g']
    if not tops:
        return lower_s(pattern, []), []

    def gammas(x):
        return [1.0 + (t - 1.0) / (1.0 + math.exp(-max(min(v, 60.0), -60.0)))
                for t, v in zip(tops, x)]

    def loss(x):
        return -lower_s(pattern, gammas(x))

    best_val, best_g = lower_s(pattern, [1.0] * len(tops)), [1.0] * len(tops)
    for r in range(restarts):
        x0 = [rng.gauss(0.0, 3.0) if r else 0.0 for _ in tops]
        x, _ = _nelder_mead(loss, x0)
        x, v = _nelder_mead(loss, x, step=0.1)
        if -v > best_val:
            best_val, best_g = -v, gammas(x)
    return best_val, best_g


def star_dim(nu: float) -> float:
    """s*(nu) = 2(sqrt(1+3nu)-1)/(3nu)."""
    return 2 * (math.sqrt(1 + 3 * nu) - 1) / (3 * nu)


def two_scale_dim(nu: float, rho: float) -> tuple[float, float]:
    """Closed form for one jump nu followed by a dense stretch rho: (dimension, gamma)."""
    if rho <= 1 + 3 / nu:
        return 2 / (2 + nu), 1.0
    r = rho * nu
    g = nu + 2 - (2 + math.sqrt((rho - 1) * (3 * nu * rho + rho - 4))) / rho
    return 2 * (r - g) / ((r - 1) * (nu + 3 - g)), g


FAMILIES: list[tuple[str, Pattern]] = [
    ('regular nu=2', [('g', 2.0)]),
    ('regular nu=3', [('g', 3.0)]),
    ('regular nu=5', [('g', 5.0)]),
    ('two-scale nu=2 rho=5', [('g', 2.0), ('d', 5.0)]),
    ('two-scale nu=3 rho=10', [('g', 3.0), ('d', 10.0)]),
    ('two-scale nu=2 rho=1e9', [('g', 2.0), ('d', 1e9)]),
    ('alternating 2,4', [('g', 2.0), ('g', 4.0)]),
    ('alternating 1.5,6', [('g', 1.5), ('g', 6.0)]),
    ('pair then dense', [('g', 3.0), ('g', 3.0), ('d', 10.0)]),
    ('two blocks', [('g', 2.0), ('d', 3.0), ('g', 4.0), ('d', 1.5)]),
    ('jump, small jump, dense', [('g', 4.0), ('g', 1.3), ('d', 5.0)]),
    ('three jumps', [('g', 3.288), ('g', 4.063), ('g', 2.453)]),
    ('mixed A', [('d', 2.492), ('g', 4.927), ('d', 9.042), ('g', 2.252)]),
    ('mixed B', [('d', 10.833), ('g', 4.249), ('g', 1.51), ('d', 13.433)]),
    ('mixed C', [('g', 2.241), ('g', 3.654), ('d', 12.468), ('g', 2.018)]),
]


def run(periods: int = 30000) -> dict:
    rows = []
    for name, pattern in FAMILIES:
        up = upper_dim(pattern, periods)
        low, gammas = lower_dim(pattern)
        row = {'family': name, 'pattern': [list(e) for e in pattern], 'upper': up,
               'lower': low, 'gap': up - low, 'gammas': gammas}
        if len(pattern) == 2 and pattern[0][0] == 'g' and pattern[1][0] == 'd':
            row['closed_form'] = two_scale_dim(pattern[0][1], pattern[1][1])[0]
        rows.append(row)
    return {'periods': periods, 'families': rows,
            'max_gap': max(r['gap'] for r in rows),
            'note': 'Exponent-level floating-point model; constants dropped. Not a proof.'}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--periods', type=int, default=30000)
    parser.add_argument('--output', type=Path,
                        default=DATA_ROOT / 'winkler_phase_collapse' / 'dimension_game.json')
    args = parser.parse_args()
    payload = run(args.periods)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(payload, indent=2) + '\n', encoding='utf-8', newline='\n')
    write_manifest(
        args.output.with_suffix('.research.json'), programme='juggler',
        research_id='juggler/winkler_phase_collapse',
        scope=f"Exponent-level upper (cover recursion) and lower (window measure) dimension "
              f"bounds for {len(FAMILIES)} periodic growth patterns; backward iteration over "
              f"{args.periods} periods; floating point, constants dropped.",
        parameters={'periods': args.periods, 'families': len(FAMILIES)},
        outputs=[args.output], sources=[Path(__file__)],
    )
    print(json.dumps({'max_gap': payload['max_gap']}, indent=2))


if __name__ == '__main__':
    main()
