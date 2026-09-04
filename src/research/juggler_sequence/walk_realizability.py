"""How much does the exponent-walk relaxation cost?

Theorem 5.3's charge is evaluated by a lattice dynamic program whose own contract says

    Any binary word with o odds, e evens, and u_k >= 0 is admitted
    (a relaxation of realizability).

Both quantities in the paper's envelope-vs-DP cross-check (margins 1.1204 and 1.1196 at
L = 50508) live on that relaxed class, so the 0.07% agreement bounds the *envelope* against the
relaxed optimum and says nothing about how far the relaxed optimum sits above the true maximum
over realizable itineraries.  This module measures that gap where it is computable.

Two quantities per length ``L`` at odd count ``o``:

* ``admissible`` -- every binary word with ``o`` odds and ``u_k >= 0`` throughout, and the largest
  walk charge over them.  This is exactly what the DP maximises.
* ``realized``   -- the subset actually occurring as ``word_L(m)`` for some odd ``m`` in a scanned
  range, and the largest walk charge over *those*.

The ratio of the two charges is the relaxation slack.  It is a lower bound on the realizable
optimum and hence an upper bound on the slack: a word absent from the scan may still be realizable
further out, which can only raise the realized maximum.  The scan range needed grows like ``2^L``,
so the honest reading is "slack at most this, at the scanned depth".
"""

from __future__ import annotations

import math
from typing import Any

import numpy as np

from .cycle_walk_charge import MU, U_TOL, charge_row


def juggler_step(n: int) -> int:
    return math.isqrt(n) if n % 2 == 0 else math.isqrt(n**3)


def word_of(n: int, L: int) -> int:
    """The length-``L`` parity word of the orbit of ``n``, as a bitmask (bit k = step k odd)."""
    x, w = n, 0
    for k in range(L):
        if x % 2:
            w |= 1 << k
        x = juggler_step(x)
    return w


def admissible_words(L: int, o: int) -> list[tuple[int, list[float]]]:
    """Every mask with ``o`` odds whose exponent walk stays nonnegative, with that walk."""
    out = []
    for mask in range(1 << L):
        if bin(mask).count("1") != o:
            continue
        u, ok, us = 0.0, True, []
        for k in range(L):
            u += MU if (mask >> k) & 1 else -1.0
            if u < -U_TOL:
                ok = False
                break
            us.append(max(u, 0.0))
        if ok:
            out.append((mask, us))
    return out


def walk_charge(us: list[float], n: int) -> float:
    """The Theorem 5.3 charge of one walk: the base state plus every intermediate state."""
    total = float(charge_row(np.zeros(1), n, 0.0)[0])
    if len(us) > 1:
        total += float(charge_row(np.array(us[:-1]), n, 0.0).sum())
    return total


def realized_words(L: int, hi: int, lo: int = 3) -> set[int]:
    """Masks occurring as ``word_L(m)`` for odd ``m`` in ``[lo, hi)``."""
    return {word_of(m, L) for m in range(lo | 1, hi, 2)}


def slack(L: int, o: int, n: int, hi: int) -> dict[str, Any]:
    """Relaxation slack at one ``(L, o)``: relaxed optimum against the realized optimum."""
    adm = admissible_words(L, o)
    if not adm:
        return {"L": L, "o": o, "admissible": 0}
    seen = realized_words(L, hi)
    best_all = max(walk_charge(us, n) for _m, us in adm)
    real = [(m, us) for m, us in adm if m in seen]
    best_real = max((walk_charge(us, n) for _m, us in real), default=0.0)
    argmax = max(adm, key=lambda mu: walk_charge(mu[1], n))[0]
    return {
        "L": L, "o": o, "n": n, "scan_hi": hi,
        "admissible": len(adm), "realized": len(real),
        "realized_fraction": len(real) / len(adm),
        "charge_relaxed": best_all, "charge_realized": best_real,
        "slack_ratio": (best_all / best_real) if best_real > 0 else math.inf,
        "argmax_realized": argmax in seen,
    }


def word_to_letters(mask: int, L: int) -> str:
    return "".join("O" if (mask >> k) & 1 else "E" for k in range(L))
