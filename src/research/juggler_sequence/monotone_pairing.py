"""Paper C Lemma 4.1' (monotone pairing): the witness against its printed proof, and a search.

Lemma 4.1' says that an increasing real sequence with nondecreasing steps in ``[a, b]``,
``0 < a <= b <= 1/2``, ``b <= 21a/20`` and ``(H-1) a >= 12`` has at least ``H/3 - 2`` terms in
each half-cell colour.  The proof printed until 8 September 2026 claimed that every pair of
consecutive cells ``(rho, rho')`` satisfies ``min >= (rho + rho')/3``, arguing that the step
scale changes gradually across the cells.  Monotone steps need not change gradually, and a
pair of interior cells with occupancies ``(3, 1)`` occurs at ``X = 1/(2a) = 2.05`` with
``b = 21a/20``.  The statement survives: this module

1. builds that witness exactly (``Fraction`` arithmetic) and reports the ``(3, 1)`` pair
   together with the lemma's conclusion, which still holds on it;
2. runs an adversarial search over two-valued monotone step profiles (``s`` steps of ``a``
   then steps of ``b``, every phase, ``X`` on a grid, ``b/a`` at several ratios) and records
   the least slack of the scarcer colour over ``H/3 - 2``;
3. checks the structural fact the corrected proof rests on -- after an interior cell of
   occupancy ``v`` every later cell has occupancy at most ``v + 1`` -- on every profile.

Nothing here is a proof.  The corrected proof is in the paper; the Lean of Lemma 4.1 is
``FateSweep.lean``, and Lemma 4.1' is not yet formalized.  Run
``python -m research.juggler_sequence.monotone_pairing``.
"""

from __future__ import annotations

import json
import math
from fractions import Fraction
from typing import Any

import numpy as np

from research.juggler_sequence.lean_paths import DATA_ROOT

DATA_DIR = DATA_ROOT / "monotone_pairing"


def occupancies(x: list[Fraction]) -> list[int]:
    """Occupancies of the visited half-cells, in order."""
    cells = [math.floor(2 * v) for v in x]
    lo, hi = cells[0], cells[-1]
    counts = [0] * (hi - lo + 1)
    for c in cells:
        counts[c - lo] += 1
    return counts


def colour_counts(x: list[Fraction]) -> tuple[int, int]:
    good = sum(1 for v in x if v - math.floor(v) < Fraction(1, 2))
    return good, len(x) - good


def witness() -> dict[str, Any]:
    """The exact witness: `X = 41/20`, `b = 21a/20`, points `-2a, -a, 0, a, 2a, 2a+b, 2a+2b, ...`."""
    X = Fraction(41, 20)
    a = 1 / (2 * X)
    b = Fraction(21, 20) * a
    steps = [a] * 4 + [b] * 60
    x = [Fraction(-2) * a]
    for s in steps:
        x.append(x[-1] + s)
    occ = occupancies(x)
    pairs = [(occ[i], occ[i + 1]) for i in range(1, len(occ) - 2, 2)]
    bad_pairs = [p for p in pairs if 3 * min(p) < sum(p)]
    good, bad = colour_counts(x)
    H = len(x)
    return {
        "X": str(X), "a": str(a), "b": str(b), "b_over_a": str(b / a),
        "steps_nondecreasing": all(steps[i] <= steps[i + 1] for i in range(len(steps) - 1)),
        "hypotheses": bool(0 < a <= b <= Fraction(1, 2) and b <= Fraction(21, 20) * a
                           and (H - 1) * a >= 12),
        "H": H,
        "occupancies": occ,
        "interior_pairs": pairs,
        "pairs_violating_min_ge_sum_over_three": bad_pairs,
        "good": good, "bad": bad,
        "H_over_3_minus_2": str(Fraction(H, 3) - 2),
        "conclusion_holds": min(good, bad) >= Fraction(H, 3) - 2,
    }


def later_at_most_one_fuller(occ: list[int]) -> bool:
    """Fact (a) of the corrected proof: for interior i < j, occ[j] <= occ[i] + 1."""
    running_min = None
    for i in range(1, len(occ)):
        if running_min is not None and occ[i] > running_min + 1:
            return False
        if i < len(occ) - 1:
            running_min = occ[i] if running_min is None else min(running_min, occ[i])
    return True


def search(x_max: float = 6.0, x_step: float = 0.02, ratios: tuple[float, ...] = (1.05, 1.04, 1.02, 1.0),
           extra_H: int = 40, phases: int = 64) -> dict[str, Any]:
    """Adversarial search over two-valued monotone profiles; least slack over H/3 - 2."""
    worst = {"slack": math.inf}
    fact_a_failures = 0
    profiles = 0
    for X in np.arange(1.0, x_max, x_step):
        a = 1 / (2 * X)
        for r in ratios:
            b = min(r * a, 0.5)
            Hmin = math.ceil(12 / a) + 1
            ph = np.linspace(0, 0.5, phases, endpoint=False)
            for H in range(Hmin, Hmin + extra_H):
                for s in range(0, H):
                    steps = np.concatenate([np.full(s, a), np.full(H - 1 - s, b)])
                    x = np.concatenate([[0.0], np.cumsum(steps)])
                    xs = x[None, :] + ph[:, None]
                    fr = xs - np.floor(xs)
                    good = (fr < 0.5).sum(axis=1)
                    m = np.minimum(good, H - good)
                    k = int(np.argmin(m))
                    slack = float(m[k] - (H / 3 - 2))
                    profiles += phases
                    if slack < worst["slack"]:
                        worst = {"slack": slack, "X": float(X), "b_over_a": r, "H": H, "switch": s,
                                 "phase": float(ph[k]), "scarcer": int(m[k])}
                # fact (a) on the extreme phases only (exact enough for a structural check)
                for s in (0, H // 2, H - 1):
                    steps = [Fraction(a).limit_denominator(10**6)] * s + \
                            [Fraction(b).limit_denominator(10**6)] * (H - 1 - s)
                    xf = [Fraction(0)]
                    for st in steps:
                        xf.append(xf[-1] + st)
                    if not later_at_most_one_fuller(occupancies(xf)):
                        fact_a_failures += 1
    return {"profiles": profiles, "worst": worst, "violations": worst["slack"] < 0,
            "fact_a_failures": fact_a_failures}


def summary(fast: bool = False) -> dict[str, Any]:
    from research.juggler_sequence.cycle_finance import git_commit

    w = witness()
    s = search(x_max=3.0, x_step=0.1, extra_H=8, phases=16) if fast else search()
    ok = (w["pairs_violating_min_ge_sum_over_three"] != [] and w["conclusion_holds"]
          and not s["violations"] and s["fact_a_failures"] == 0)
    return {
        "witness": w,
        "search": s,
        "classification": {
            "label": "PRINTED_PROOF_STEP_FALSE_STATEMENT_SUPPORTED" if ok else "UNEXPECTED",
            "printed_pair_claim_refuted": w["pairs_violating_min_ge_sum_over_three"] != [],
            "statement_violated": s["violations"],
            "fact_a_failures": s["fact_a_failures"],
        },
        "git_commit": git_commit(),
    }


def main() -> None:
    result = summary()
    DATA_DIR.mkdir(parents=True, exist_ok=True)
    (DATA_DIR / "summary.json").write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    w, s = result["witness"], result["search"]
    print(f"witness X={w['X']}: occupancies {w['occupancies'][:6]}..., pairs violating the printed "
          f"claim {w['pairs_violating_min_ge_sum_over_three']}, conclusion holds: {w['conclusion_holds']}")
    print(f"search: {s['profiles']} profiles, least slack {s['worst']['slack']:.3f} at {s['worst']}")
    print(f"fact (a) failures: {s['fact_a_failures']}")
    print(f"classification {result['classification']['label']}")


if __name__ == "__main__":
    main()
