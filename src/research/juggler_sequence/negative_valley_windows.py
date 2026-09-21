"""Hercher's Lemma 26 averaging and Corollary 29's residue drop, transposed to 3n-1 and
measured against what Paper D's open values actually need.

Support machinery for the ``juggler_negative_m_cycles`` branch; it writes no artifact and is
not an input of Paper D's release manifest.

**The negative-side statement of Lemma 26.** Let ``y`` be an odd local minimum of
``g(y) = y/2`` (even), ``(3y-1)/2`` (odd), ``u = y - 1``, ``a = v_2(u)``.  The note's Lemma 1
gives ``g^k(y) = 1 + (3/2)^k u`` for ``k <= a``, so the run's contribution to ``Lambda`` is

    T(y) = sum_{k<a} 1/(3 g^k(y) - 1) < (1/(3u)) sum_{k<a} (2/3)^k = (1 - (2/3)^a) / u .

The note's Lemma 2 discards the factor ``kappa(a) = 1 - (2/3)^a`` and keeps ``T(y) < 1/u``.
Hercher's Remark 7 is the same bound on his side with ``n_i`` in place of ``u``, and his
Lemma 26 is the case analysis that averages ``kappa`` over one, two or three consecutive
runs; the relation between consecutive minima is ``u_i = (2/3)^{a_i}(2^{r_i}(u_{i+1}+1)-1)``
here against his ``n_i = (2/3)^{k_i}(2^{l_i} n_{i+1}+1) - 1``, the same shape with the sign
flipped, so the case analysis does transpose and its constants are the same rationals.

**What is measured.** Write, for a local minimum above the floor ``X0``,

    rho(y) := T(y) * (X0 - 1)  <=  kappa(a) * (X0 - 1) / u   in [0, 1],

the valley's contribution in units of Lemma 2's own one-per-valley.  Lemma 6 bounds
``Lambda`` by ``r`` valleys at the floor plus ``m - r`` above a threshold, and the only way
an averaging argument can improve it is to bound the sum of ``rho`` over that block of ``r``
below ``r``.  So the quantity that decides the transposition is

    A_r := sup over r consecutive local minima, all >= X0, of their average rho,

and ``window_ceiling`` computes rigorous upper bounds on the related

    gamma_D := sup over D consecutive local minima, all >= X0, of
               min_{1 <= d <= D} (average of the first d),          gamma_D <= A_D,

by a branch-and-bound over residue classes of ``y`` modulo powers of two.  That tree is
Corollary 29's mechanism: the note's Lemma 5 makes each case word a residue class, and a
branch dies when the least member of its class above the floor is large enough to make the
trivial bound suffice.  ``witness`` runs the other way and returns concrete integers, which
are lower bounds on ``A_r`` and so are what can refute the transposition rather than
support it.

The windows here are orbit segments, not segments of a cycle -- none is known above the
floor -- so a witness refutes a *method* and not the conclusion.  That is the right target
for these two refinements, which use the floor and the local step relations along a few
consecutive runs and never the cycle's closure; a witness satisfying those local constraints
is exactly what such a bound cannot improve past.

Not a theorem of Paper D: nothing here enters the manuscript, and the tree's output is an
upper bound on a supremum, not an exclusion.
"""
from __future__ import annotations

import sys
from fractions import Fraction
from typing import Any

from mpmath import log, mp, mpf

from research.juggler_sequence.negative_m_cycles import _valley_thresholds, delta

#: the verified floor of the 3x-1 map, as Paper D 1.1.0 uses it
FLOOR_LOG2 = 51
#: the tree walks the 2-adic expansion of the start; no branch has ever needed this many bits
MAX_BITS = 600

_KAPPA: dict[int, Fraction] = {}


def kappa(a: int) -> Fraction:
    """``1 - (2/3)^a``: the run-length factor the note's Lemma 2 discards."""
    k = _KAPPA.get(a)
    if k is None:
        k = _KAPPA[a] = 1 - Fraction(2, 3) ** a
    return k


class _Survivor(Exception):
    """A window survived the threshold: the tree does not close there."""


def window_values(y: int, D: int, X0: int) -> dict[str, Any] | None:
    """Walk the real orbit of the odd ``y`` through ``D`` local minima.

    Returns the minima, their run lengths, their ``rho`` and the running averages, or
    ``None`` if a minimum falls below ``X0`` (such a window is not one an m-cycle above the
    floor can show)."""
    cur, out = y, []
    Xm1 = Fraction(X0 - 1)
    for _ in range(D):
        if cur % 2 == 0 or cur < X0:
            return None
        u = cur - 1
        a = (u & -u).bit_length() - 1
        out.append({"y": cur, "a": a, "rho": kappa(a) * Xm1 / u})
        cur = 1 + 3 ** a * (u >> a)                 # the local maximum, by Lemma 1
        while cur % 2 == 0:
            cur //= 2
    total, avgs = Fraction(0), []
    for d, v in enumerate(out, start=1):
        total += v["rho"]
        avgs.append(total / d)
    return {"valleys": out, "averages": avgs, "average": avgs[-1], "min_prefix": min(avgs)}


def close_window_tree(X0: int, D: int, theta: Fraction, max_bits: int = MAX_BITS) -> dict:
    """Try to certify ``gamma_D <= theta`` at the floor ``X0``.

    The state is ``y = rho (mod 2^j)`` together with ``2^t g^t(y) = 3^c y - Dw`` (Lemma 5);
    the class splits whenever the next parity is not yet determined by the known bits.  Each
    completed local minimum imposes ``>= X0``, which is an increasing affine condition on
    ``y`` and so raises the lower bound for the whole window, and that bound is lifted into
    the residue class: this is Corollary 29's drop, in the sharper form the floor allows.
    A branch is cut as soon as a completed prefix already averages at or below ``theta``."""
    stats = {"nodes": 0, "splits": 0, "max_j": 0}
    Xm1 = Fraction(X0 - 1)
    witness: dict = {}

    def cut(j, rho, valleys, pending, ylo) -> bool:
        y_eff = ylo + ((rho - ylo) % (1 << j))
        total = Fraction(0)
        for d, (a_i, c_i, Dw_i, t_i) in enumerate(valleys, start=1):
            total += kappa(a_i) * Xm1 / (Fraction(3 ** c_i * y_eff - Dw_i, 1 << t_i) - 1)
            if total / d <= theta:
                return True
        if pending is not None and len(valleys) < D:
            c_p, Dw_p, t_p = pending
            u_lo = Fraction(3 ** c_p * y_eff - Dw_p, 1 << t_p) - 1
            if (total + Xm1 / u_lo) / (len(valleys) + 1) <= theta:      # kappa <= 1
                return True
        return False

    def parity(rho, t, c, Dw) -> int:
        mod = 1 << (t + 1)
        return (((pow(3, c, mod) * rho - Dw) % mod) >> t) & 1

    def walk(j, rho, t, c, Dw, valleys, pending, a, ylo):
        stats["nodes"] += 1
        stats["max_j"] = max(stats["max_j"], j)
        if j > max_bits:
            raise RuntimeError(f"window tree ran past {max_bits} bits at theta = {theta}")
        if cut(j, rho, valleys, pending, ylo):
            return
        if j < t + 1:                                       # next parity not yet determined
            stats["splits"] += 1
            walk(j + 1, rho, t, c, Dw, valleys, pending, a, ylo)
            walk(j + 1, rho + (1 << j), t, c, Dw, valleys, pending, a, ylo)
            return
        odd = parity(rho, t, c, Dw)
        if pending is None:                                 # descending to the next minimum
            if not odd:
                walk(j, rho, t + 1, c, Dw, valleys, None, 0, ylo)
                return
            need = -(-((X0 << t) + Dw) // 3 ** c)           # this minimum is above the floor
            walk(j, rho, t, c, Dw, valleys, (c, Dw, t), 0, max(ylo, need))
            return
        if odd:                                             # the run continues
            walk(j, rho, t + 1, c + 1, 3 * Dw + (1 << t), valleys, pending, a + 1, ylo)
            return
        nv = valleys + [(a, *pending)]                      # the run ended with a odd steps
        if cut(j, rho, nv, None, ylo):
            return
        if len(nv) >= D:
            witness.update(rho=rho, j=j, y=ylo + ((rho - ylo) % (1 << j)),
                           runs=[v[0] for v in nv])
            raise _Survivor
        walk(j, rho, t + 1, c, Dw, nv, None, 0, ylo)

    depth = sys.getrecursionlimit()
    sys.setrecursionlimit(max(depth, 20000))
    try:
        walk(1, 1, 0, 0, 0, [], (0, 0, 0), 0, X0)
    except _Survivor:
        return {"closed": False, "theta": theta, "D": D, "X0": X0, "witness": witness, **stats}
    finally:
        sys.setrecursionlimit(depth)
    return {"closed": True, "theta": theta, "D": D, "X0": X0, "witness": {}, **stats}


def single_valley_sup(X0: int, max_run: int | None = None) -> dict[str, Any]:
    """``A_1`` exactly, without the tree: one local minimum above the floor.

    ``u`` is a multiple of ``2^a`` with ``u/2^a`` odd, so the least ``u >= X0 - 1`` with
    ``v_2(u) = a`` is ``2^a`` times the least odd integer at or above ``(X0-1)/2^a``.  The
    supremum over ``a`` is attained at a run long enough that ``kappa(a)`` is spent and short
    enough that the rounding of ``u`` up to its residue class costs little; at ``2^51`` it is
    within ``10^-5`` of one, which is why no single-valley argument can do anything here."""
    Xm1 = X0 - 1
    best = {"rho": Fraction(0), "a": None, "u": None}
    for a in range(1, (max_run or X0.bit_length() + 2) + 1):
        w = -(-Xm1 >> a) | 1                                # least odd w with 2^a w >= X0-1
        u = w << a
        if u < Xm1:
            u += 1 << (a + 1)
        r = kappa(a) * Fraction(Xm1, u)
        if r > best["rho"]:
            best = {"rho": r, "a": a, "u": u}
    return {"average": best["rho"], "min_prefix": best["rho"], "start": best["u"] + 1,
            "valleys": [{"y": best["u"] + 1, "a": best["a"], "rho": best["rho"]}]}


def window_ceiling(X0: int, D: int, steps: int = 11) -> tuple[Fraction, dict]:
    """Bisect for the least ``theta`` at which the tree closes: a certified ``gamma_D``.

    ``D = 1`` is not walked: the tree would have to resolve the whole floor bit by bit to
    close it, and ``single_valley_sup`` gives the answer in closed form."""
    if D == 1:
        return single_valley_sup(X0)["average"], {"closed": True, "by": "single_valley_sup"}
    lo, hi, last = Fraction(0), Fraction(1), {}
    for _ in range(steps):
        mid = (lo + hi) / 2
        res = close_window_tree(X0, D, mid)
        if res["closed"]:
            hi, last = mid, res
        else:
            lo = mid
    return hi, last


def witness(X0: int, D: int, steps: int = 11) -> dict[str, Any] | None:
    """A concrete start whose first ``D`` minima are all above ``X0`` and average high.

    Bisects as ``window_ceiling`` does but keeps, from each threshold the tree fails to
    close, the least member of the surviving class above the floor, and evaluates it on the
    real orbit.  The value returned is a *lower* bound on ``A_D``, so it is what stops an
    averaging argument rather than what supports one."""
    if D == 1:
        return single_valley_sup(X0)
    lo, hi, best = Fraction(0), Fraction(1), None
    for _ in range(steps):
        mid = (lo + hi) / 2
        res = close_window_tree(X0, D, mid)
        if res["closed"]:
            hi = mid
            continue
        lo = mid
        w = res.get("witness") or {}
        if not w:
            continue
        ex = window_values(w["y"], D, X0)
        if ex is not None and (best is None or ex["min_prefix"] > best["min_prefix"]):
            best = {**ex, "start": w["y"], "bits_of_class": w["j"]}
    return best


# ---------------------------------------------------------------------------------------------
# What the open values need: Lemma 6's cap read as a demand on the block at the floor
# ---------------------------------------------------------------------------------------------

def block_demand(m: int, o: int, X0: int, lam) -> list[dict[str, Any]]:
    """For each block size ``r`` Lemma 6 can use, the constant an averaging argument would
    have to beat to close this row.

    Lemma 6 bounds ``Lambda`` by ``r 2^{-L0} + (m - r) 2^{-T}`` on the piece where exactly
    ``r`` minima lie at or below ``T``; that piece is ``[T_r, T_{r+1})`` and the bound falls
    with ``T``, so the pair the cap uses is ``(r, T_{r+1})``, exactly as the probe's
    ``_valley_cap_from`` reads it off the breakpoints.  An averaging argument replaces the
    first ``r`` by ``c r``, and the row closes at block size ``r`` exactly when
    ``c r 2^{-L0} + (m - r) 2^{-T_{r+1}} <= Lambda``, so ``c <= demand(r)``."""
    with mp.workdps(60):
        L0 = log(mpf(X0) - 1) / log(2)
        T = _valley_thresholds(m, o, delta(), mpf)
        out = []
        for r in range(1, m + 1):
            tail = mpf(0) if r == m else (m - r) * mpf(2) ** (-T[r + 1])
            if r < m and T[r + 1] <= L0:
                continue                                # fewer than r + 1 minima can be low
            out.append({"r": r, "T": float(L0 if r == m else T[r + 1]),
                        "cap_bits_at_r": float(log((r * mpf(2) ** (-L0) + tail) / lam) / log(2)),
                        "demand": float((lam - tail) / (r * mpf(2) ** (-L0)))})
        return out


def reach_report(rows: dict[int, dict], X0: int, ms: tuple[int, ...] = (62, 63, 64),
                 max_block: int = 7, starts: dict[int, int] | None = None) -> dict[str, Any]:
    """The verdict: for each open ``m``, what the block at the floor would have to average
    and what consecutive minima above the floor actually do average.

    ``rows`` maps ``m`` to the probe's row at this floor (``survivors`` carrying ``K`` and
    ``o``).  ``starts`` supplies known window starts by block size; they are re-walked on the
    map here, so passing them only saves the search, not the check.  Without them every block
    size is searched from scratch, which takes minutes rather than seconds."""
    from research.juggler_sequence.negative_m_cycles import lambda_juggler

    measured = {}
    for r in range(1, max_block + 1):
        w = window_values(starts[r], r, X0) if starts and r in starts else witness(X0, r)
        measured[r] = {"attained": None if w is None else float(w["average"]),
                       "start": None if w is None else (starts or {}).get(r, w.get("start")),
                       "runs": None if w is None else [v["a"] for v in w["valleys"]]}
    out: dict[str, Any] = {"floor_log2": X0.bit_length() - 1, "windows": measured, "rows": {}}
    with mp.workdps(60):
        for m in ms:
            for s in rows[m]["survivors"]:
                lam = lambda_juggler(s["K"])[1]
                demands = [d for d in block_demand(m, s["o"], X0, lam) if d["r"] <= max_block]
                best = None
                for d in demands:
                    att = measured[d["r"]]["attained"]
                    if att is None:
                        continue
                    gain = -float(log(mpf(att)) / log(2))
                    need = -float(log(mpf(d["demand"])) / log(2))
                    cand = {"r": d["r"], "demand": d["demand"], "attained": att,
                            "gain_bits": gain, "needed_bits": need,
                            "closes": att <= d["demand"]}
                    if best is None or cand["needed_bits"] - cand["gain_bits"] < \
                            best["needed_bits"] - best["gain_bits"]:
                        best = cand
                out["rows"].setdefault(str(m), []).append(
                    {"K": s["K"], "o": s["o"], "best_block": best,
                     "shortfall_bits": None if best is None
                     else best["needed_bits"] - best["gain_bits"]})
    return out


#: Window starts found by the residue tree at the floor 2^51 and re-walked on the map by
#: every caller.  They are lower bounds on what an averaging argument can give, and they are
#: what the verdict rests on; the tests keep their own copy rather than importing these.
WITNESSES_AT_2_51: dict[int, int] = {
    1: 2251799813685249, 2: 2251935393968129, 3: 2263959154913281, 4: 2255557997555713,
    5: 2266848965985921, 6: 2343202629650049, 7: 2258052872963713,
}


def main() -> None:
    """Print the verdict at the floor the probe's tables carry.  Writes nothing: the data
    directory beside it holds pinned inputs of Paper D's release manifest, and this
    measurement changes no number in the manuscript."""
    import json

    from research.juggler_sequence.negative_m_cycles import FLOOR_LOG2, JSON_PATH

    data = json.loads(JSON_PATH.read_text(encoding="utf-8"))
    X0 = 2 ** FLOOR_LOG2
    rows = {r["m"]: r for r in data["tables"][f"2^{FLOOR_LOG2}"]["rows"]}
    first_open = data["classification"]["first_open_m"]
    ms = tuple(m for m in (first_open, first_open + 1, first_open + 2) if m in rows)
    rep = reach_report(rows, X0, ms=ms, starts=WITNESSES_AT_2_51)
    print(f"floor 2^{FLOOR_LOG2}, first open m = {first_open}")
    print("  block  attained  start")
    for r, w in rep["windows"].items():
        print(f"  {r:5d}  {w['attained']:.6f}  {w['start']}  runs {w['runs']}")
    print("  m    K                block  demanded  attained  needed  delivered  verdict")
    for m, entries in rep["rows"].items():
        for e in entries:
            b = e["best_block"]
            if b is None:
                print(f"  {m:<4s} {e['K']:<16d} no block within the measured range")
                continue
            verdict = ("reaches" if b["closes"]
                       else f"short by {e['shortfall_bits']:.4f} bits")
            print(f"  {m:<4s} {e['K']:<16d} {b['r']:5d}  {b['demand']:8.4f}  "
                  f"{b['attained']:8.4f}  {b['needed_bits']:6.4f}  {b['gain_bits']:9.4f}  "
                  f"{verdict}")


if __name__ == "__main__":
    main()
