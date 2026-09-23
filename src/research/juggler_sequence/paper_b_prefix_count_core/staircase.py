"""Paper B prefix counts: staircase."""
from __future__ import annotations
import math
from typing import Any




def least_peak_staircase(kmax: int) -> "Any":
    """Least achievable peak of a non-contracting walk, by length ``1..kmax``, vectorised.

    The state ``(t, a)`` -- length and odd letters -- fixes the level ``u = a log2(3) - t``, and
    that level depends on the NEW state alone, not on which predecessor reached it.  So the
    dynamic program collapses to one array recurrence,

        new[a] = max( min(prev[a], prev[a-1]), a log2(3) - t )   where that level is >= 0,

    which runs to ``kmax = 26000`` in seconds where the dict form reached 1200.  Reproduces the
    dict form exactly (difference 0.0 over ``k <= 1200``).
    """
    import numpy as np

    log2_3 = math.log2(3.0)
    prev = np.full(kmax + 2, np.inf)
    prev[0] = 0.0
    index = np.arange(kmax + 2)
    out = np.empty(kmax)
    for t in range(1, kmax + 1):
        shifted = np.empty_like(prev)
        shifted[0] = np.inf
        shifted[1:] = prev[:-1]
        best = np.minimum(prev, shifted)
        level = index * log2_3 - t
        prev = np.where((level >= -1e-12) & np.isfinite(best), np.maximum(best, level), np.inf)
        out[t - 1] = prev.min()
    return out


def staircase_jumps(kmax: int) -> list[int]:
    """The lengths at which ``least_peak_staircase`` rises: BETA's one-sided semiconvergents.

    THE CHARACTERISATION IS EXACT, not a containment.  ``J-least-peak-staircase-is-beta-ostrowski``
    records the jumps to length 1200 -- 2, 5, 8, 27, 46, 65, 149, 233, 317, 401, 485 -- observes
    every one is a semiconvergent denominator of BETA, and notes that the converse fails because
    3, 19, 84 and 1054 are semiconvergents that are not jumps.  The converse does not fail; it
    needs the sign.  Writing ``gap(d) = o log2(3) - d`` at the nearest ``o``, the jump set to
    ``kmax = 26000`` is EXACTLY the set of semiconvergents with ``gap < 0``: 34 elements each way,
    no exception in either direction.

    THE PREDICTION THAT TESTED IT.  Semiconvergents come in families ``q_(k-1) + j q_k``,
    ``j = 1..a_(k+1)``, and the families alternate sides.  The family after 485 is
    ``485 + j * 1054`` with ``j = 1..23``, landing on ``23 * 1054 + 485 = 24727``, the next
    convergent.  Length 1200 stops just short of its first member, 1539.  Run to 26000 and all
    twenty-three appear -- 1539, 2593, 3647, ... , 24727 -- with nothing between 485 and 1539 and
    nothing after 24727.

    AND THE OTHER SIDE IS THE CYCLE MODULE'S.  The semiconvergents with ``gap > 0`` up to 50508 are
    3, 11, 19, 84, 569, 1054, 25781, 50508, which is exactly ``cycle_gap_baker.RECORD_LENGTHS``
    apart from the trivial 1.  So Paper B's walk geometry and the cycle side's Diophantine record
    lengths are the two halves of one semiconvergent split, and ``25781`` was predicted from the
    staircase side before being found in the cycle module.

    WHAT IS AND IS NOT PROVED.  That one-sided approximation records are exactly the one-sided
    semiconvergents is classical.  That the staircase steps exactly at those records follows from
    the mechanism in ``J-noncontracting-peak-supremum-log2-three`` -- the least peak is set by how
    closely a reachable level creeps below ``1 - c`` -- but is verified here rather than proved.
    """
    peaks = least_peak_staircase(kmax)
    out = [1] if peaks[0] > 1e-12 else []
    out.extend(t + 1 for t in range(1, len(peaks)) if peaks[t] > peaks[t - 1] + 1e-12)
    return out
