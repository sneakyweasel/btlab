"""m-cycles of the 3n-1 map above the verified floor: the Simons-de Weger template, mirrored.

The map is ``g(y) = y/2`` (``y`` even), ``(3y-1)/2`` (``y`` odd) on the positive integers, the
shortcut 3n+1 map read on the negative integers. Its known cycles are ``1``, ``(5, 7, 10)`` and
the eleven-element cycle at ``17``; every start below ``2^44`` reaches one of them
(``negative_floor_3x1``). An m-cycle is a cycle with ``m`` odd runs, equivalently ``m`` local
minima (the first element of each odd run). This probe runs the five-step template of
Simons-de Weger 2005 / Simons 2008 on this side, with the negative-side constants derived
in ``docs/theory/collatz_3n_minus_1_m_cycles_note.md``:

* **Run identity.** For odd ``y ≠ 1`` with ``a = v_2(y - 1)``: ``g^k(y) - 1 = (3/2)^k (y - 1)``
  for ``k ≤ a``, the first ``a`` iterates are odd and ``g^a(y)`` is even. Hence a run of ``a``
  odd steps starts at ``y ≥ 2^a + 1`` (the negative Lemma 8 of Hercher 2023).
* **Cycle equation.** On a cycle with ``K`` steps and ``o`` odd steps,
  ``Lambda := o log 3 - K log 2 = -sum over odd elements y of log(1 - 1/(3y)) > 0``, and a run
  from the local minimum ``y`` contributes at most ``1/(y - 1)``. So ``Lambda ≤ m/(x_min - 1)``
  for an m-cycle whose least element is ``x_min``.
* **Chaining.** With ``u = y - 1`` at successive local minima, ``u_{i+1} < u_i^delta / 2``,
  ``delta = log_2 3``, because the local maximum is at most ``u^delta + 1`` and at least one
  halving follows. Summing the run lengths ``a_i = v_2(u_i) ≤ log_2 u_i`` around the cycle,
  ``o ≤ B(m) log_2 u_1 - (B(m) - m)/(delta - 1)`` with ``B(m) = (delta^m - 1)/(delta - 1)``, and
  ``K < delta o``.
* **Crandall.** ``Lambda ≤ m/(x_min - 1)`` makes ``o/K`` a best approximation of
  ``log 2 / log 3`` from above, so ``K`` is at least the first admissible length ``K0(m)``,
  found exactly by the three-gap walk.
* **Rhin.** ``|u_0 + u_1 log 2 + u_2 log 3| >= H^{-13.3}`` for ``H = max(|u_1|, |u_2|) >= 2``
  (Rhin 1987, Proposition p. 160, (7), as printed); with ``(u_0, u_1, u_2) = (0, -K, o)`` and
  ``H = K`` the length, ``x_min - 1 < m / Lambda <= m K^{13.3}``; against the chaining this
  bounds ``K`` above by ``K3(m)``. (The form ``exp(-13.3 (0.46057 + log K))`` carried since
  Paper A is Simons-de Weger 2005 Lemma 12, the same bound at ``H = K + L`` in the odd count;
  ``RHIN_OFFSET`` restores it for comparison.)

For each ``m`` the admissible lengths ``K < K3(m)`` with ``Lambda(K) < m/(X0 - 1)`` are
enumerated exactly, and each is tested against the chaining: an m-cycle of length ``K`` needs
``2^{L_min(K, m)} < m / Lambda(K)``. No survivor means no m-cycle above the floor. The
statement is conditional on Rhin's effective measure, an external theorem, and on nothing
else; the finite parts are 80-digit arithmetic with the margins recorded.

Not a halt theorem: it excludes cycles of a given number of odd runs above a floor, on a map
this laboratory did not invent, and says nothing about the Juggler's own cycles.
"""

from __future__ import annotations

import json
from fractions import Fraction
from typing import Any

from mpmath import mp, mpf, exp, floor, log

from research.juggler_sequence.collatz_finance_mirror import (
    _x,
    continued_fraction,
    frac,
    lambda_juggler,
    negative_cycle_survivors,
)
from research.juggler_sequence.lean_paths import DATA_ROOT, DOCS_RESEARCH

DATA_DIR = DATA_ROOT / "negative_m_cycles"
JSON_PATH = DATA_DIR / "summary.json"
DOC_PATH = DOCS_RESEARCH / "juggler_negative_m_cycles.md"

CLASS_EXCLUDED = "NEGATIVE_M_CYCLES_EXCLUDED_BELOW_M"

_DPS = 80
#: the verified floor of the 3x-1 map
FLOOR_LOG2 = 44
#: the three cycles of the 3x-1 shortcut map on the positive integers
CYCLES: tuple[tuple[int, ...], ...] = ((1,), (5, 7, 10), (17, 25, 37, 55, 82, 41, 61, 91, 136, 68, 34))
#: Rhin 1987, Proposition p. 160, (7): |u0 + u1 log 2 + u2 log 3| >= H^(-13.3) for every
#: H = max(|u1|, |u2|) >= 2, with no further constant. Here u1 = -K, u2 = o, H = K. The form
#: the laboratory carried since Paper A, exp(-13.3 (0.46057 + log K_odd)), is the same bound
#: read at H = delta * K_odd, since 0.46057 = log delta; ``RHIN_OFFSET`` is kept at zero so
#: that H is the cycle length itself.
RHIN_EXPONENT = mpf("13.3")
RHIN_OFFSET = mpf("0")


def rhin_form() -> str:
    """The bound in force, spelled out for the summary and the rendered table."""
    if RHIN_OFFSET == 0:
        return (f"Lambda >= K^(-{RHIN_EXPONENT}), K the cycle length "
                "(Rhin 1987, Proposition (7), H = max(|u_1|, |u_2|) = K)")
    return (f"Lambda > exp(-{RHIN_EXPONENT} ({RHIN_OFFSET} + log K)), K the cycle length "
            "(Simons-de Weger 2005 Lemma 12 form)")
#: floors to table, with the label each is reported under; 301 * 2^50 is the floor of
#: Simons-de Weger 2005 (Roosendaal, November 2004), for a like-for-like comparison
FLOORS: tuple[tuple[int, str], ...] = (
    (2**40, "2^40"), (2**44, "2^44"), (2**48, "2^48"), (301 * 2**50, "301*2^50"),
    (2**60, "2^60"), (2**68, "2^68"),
)
#: the largest m tabled; beyond the excluded range the window is reported, not enumerated
M_MAX = 120
#: more admissible lengths than this in a window and the window is reported, not walked
WALK_CAP = 200_000


def shortcut(y: int) -> int:
    return y // 2 if y % 2 == 0 else (3 * y - 1) // 2


# ---------------------------------------------------------------------------------------------
# The exact identities, as Fractions, for the tests and the known cycles
# ---------------------------------------------------------------------------------------------

def v2(n: int) -> int:
    a = 0
    while n % 2 == 0:
        n //= 2
        a += 1
    return a


def run_length(y: int) -> int:
    """``v_2(y - 1)``: the number of consecutive odd steps from odd ``y ≠ 1``."""
    assert y % 2 == 1 and y != 1
    return v2(y - 1)


def odd_run(y: int) -> list[int]:
    """The odd run from ``y``: ``y, g(y), ...`` while odd, then the even landing value."""
    out = [y]
    while out[-1] % 2 == 1:
        out.append(shortcut(out[-1]))
    return out


def cycle_data(cycle: tuple[int, ...]) -> dict[str, Any]:
    """``K``, ``o``, the local minima with their runs, and the exact cycle equation."""
    K = len(cycle)
    odds = [y for y in cycle if y % 2 == 1]
    o = len(odds)
    minima = [cycle[i] for i in range(K) if cycle[i] % 2 == 1 and cycle[i - 1] % 2 == 0]
    if o == K:
        minima = [min(cycle)]
    product = Fraction(3) ** o
    for y in odds:
        product *= Fraction(3 * y - 1, 3 * y)
    return {
        "K": K, "o": o, "m": len(minima), "minima": minima,
        "runs": {y: run_length(y) for y in minima if y != 1},
        "cycle_equation_holds": product == Fraction(2) ** K,
    }


# ---------------------------------------------------------------------------------------------
# The template's constants
# ---------------------------------------------------------------------------------------------

def delta() -> mpf:
    return log(3) / log(2)


def tower_B(m: int) -> mpf:
    """``B(m) = (delta^m - 1)/(delta - 1)``: the sum of the run-length bounds around the cycle."""
    d = delta()
    return (d ** m - 1) / (d - 1)


def log2_xmin_lower(K: int, m: int) -> mpf:
    """``L_min(K, m)``: the chaining lower bound on ``log_2(x_min - 1)`` for an m-cycle of
    length ``K``, from ``o ≤ B log_2 u_1 - (B - m)/(delta - 1)`` and ``K < delta o``."""
    d = delta()
    B = tower_B(m)
    return (mpf(K) / d + (B - m) / (d - 1)) / B


def rhin_lower(K: int) -> mpf:
    """Rhin's lower bound on ``Lambda`` at height ``K``."""
    return exp(-RHIN_EXPONENT * (RHIN_OFFSET + log(mpf(K))))


def lambda_bound(m: int, X0: int) -> mpf:
    """The cycle-equation bound ``Lambda ≤ m/(X0 - 1)`` for an m-cycle above the floor."""
    return mpf(m) / (mpf(X0) - 1)


def K3(m: int) -> int:
    """The least integer ``K*`` such that ``2^{L_min(K, m)} ≥ 2 e^{13.3 RHIN_OFFSET} m K^{13.3}``
    for every ``K ≥ K*`` (the factor is ``2m`` with ``RHIN_OFFSET = 0``), which covers
    ``m/Lambda(K) + 1``; every m-cycle has length ``K < K*``. The function
    ``g(K) = L_min(K, m) - 13.3 log_2 K - log_2(2 e^{13.3 RHIN_OFFSET} m)`` is convex, has its
    minimum at ``K = 13.3 delta B(m) / log 2`` and is negative there, so it has one root beyond
    the minimum; ``K*`` is that root rounded up, confirmed at the integers ``K* - 1`` (negative)
    and ``K*`` (non-negative). Earlier versions evaluated ``L_min`` at ``int(K)`` inside a real
    bisection and returned one more than this."""
    with mp.workdps(40):
        c = log(2 * exp(RHIN_EXPONENT * RHIN_OFFSET) * m) / log(2)
        d = delta()
        B = tower_B(m)

        def g(K: mpf) -> mpf:
            return (K / d + (B - m) / (d - 1)) / B - RHIN_EXPONENT * log(K) / log(2) - c

        kmin = RHIN_EXPONENT * d * B / log(2)
        if not g(kmin) < 0:
            raise RuntimeError(f"the ceiling function is not negative at its minimum for m = {m}")
        lo, hi = kmin, 2 * kmin
        while g(hi) < 0:
            hi *= 2
            if hi > mpf(10) ** 60:
                raise RuntimeError("no Rhin ceiling below 1e60")
        for _ in range(300):
            mid = (lo + hi) / 2
            if g(mid) < 0:
                lo = mid
            else:
                hi = mid
        Kstar = int(mp.ceil(hi))
        while Kstar - 1 > kmin and g(mpf(Kstar - 1)) >= 0:
            Kstar -= 1
        while g(mpf(Kstar)) < 0:
            Kstar += 1
        if not (g(mpf(Kstar)) >= 0 > g(mpf(Kstar - 1)) and mpf(Kstar - 1) >= kmin):
            raise RuntimeError(f"ceiling bracket failed for m = {m}")
        return Kstar


# ---------------------------------------------------------------------------------------------
# The admissible lengths: the three-gap walk on the expanding side, with a deep convergent list
# ---------------------------------------------------------------------------------------------

def _returns(eps: mpf, terms: int = 70) -> tuple[int, int, mpf, mpf]:
    """Least ``q`` with ``frac(q x) < eps`` and least ``q`` with ``1 - frac(q x) < eps``."""
    a = continued_fraction(terms)
    p0, q0, p1, q1 = 0, 1, 1, 0
    conv = []
    for ai in a:
        p0, p1 = p1, ai * p1 + p0
        q0, q1 = q1, ai * q1 + q0
        conv.append((p1, q1))
    x = _x()
    best: dict[int, int | None] = {+1: None, -1: None}
    for i in range(1, len(conv)):
        (_, qp), (_, q) = conv[i - 1], conv[i]
        ai1 = a[i + 1] if i + 1 < len(a) else 1
        for j in range(0, ai1 + 1):
            Q = qp + j * q
            if Q <= 0:
                continue
            f = frac(Q * x)
            for side, val in ((+1, f), (-1, 1 - f)):
                if val < eps and (best[side] is None or Q < best[side]):
                    best[side] = Q
        if best[+1] is not None and best[-1] is not None and q > max(best[+1], best[-1]):
            break
    if best[+1] is None or best[-1] is None:
        raise RuntimeError("convergent list too short for this eps")
    return best[+1], best[-1], frac(best[+1] * x), 1 - frac(best[-1] * x)


def admissible_lengths(eps_frac: mpf, kmax: int, cap: int = WALK_CAP) -> list[int] | None:
    """All ``K ≤ kmax`` with ``1 - frac(K x) < eps_frac`` (the expanding side), in order, by
    the three-gap walk; ``None`` if more than ``cap`` would be produced."""
    with mp.workdps(_DPS):
        q1, q2, d1, d2 = _returns(eps_frac)
        up, dn, du, dd = q2, q1, d2, d1
        K, g, out = up, du, []
        while K <= kmax:
            out.append(K)
            if len(out) > cap:
                return None
            if g + du < eps_frac:
                K += up
                g += du
            elif g >= dd:
                K += dn
                g -= dd
            else:
                K += up + dn
                g += du - dd
        return out


# ---------------------------------------------------------------------------------------------
# One row of the table
# ---------------------------------------------------------------------------------------------

def row(m: int, X0: int) -> dict[str, Any]:
    """The template at ``(m, X0)``: the Rhin ceiling, the admissible lengths below it, and
    which of them survive the chaining."""
    with mp.workdps(_DPS):
        eps = lambda_bound(m, X0)
        eps_frac = eps / log(3)
        ceiling = K3(m)
        expected = float(eps_frac * ceiling)
        lengths = admissible_lengths(eps_frac, ceiling - 1) if expected < WALK_CAP / 2 else None
        survivors = []
        K0 = None
        margin = None
        if lengths is not None:
            K0 = lengths[0] if lengths else None
            for K in lengths:
                o, lam = lambda_juggler(K)
                finance = mpf(m) / lam                      # x_min - 1 ≤ this
                tower = 2 ** log2_xmin_lower(K, m)          # x_min - 1 > this
                slack = float(log(finance / tower) / log(2))
                if margin is None or slack > margin:
                    margin = slack
                if tower < finance:
                    survivors.append({
                        "K": K, "o": o, "Lambda": float(lam),
                        "xmin_minus_one_le": float(finance),
                        "xmin_minus_one_gt": float(tower),
                        "log2_slack": float(log(finance / tower) / log(2)),
                    })
        return {
            "m": m,
            "floor": X0,
            "lambda_bound": float(eps),
            "K3_rhin_ceiling": ceiling,
            "expected_admissible": expected,
            "walked": lengths is not None,
            "admissible_count": None if lengths is None else len(lengths),
            "K0_least_admissible": K0,
            "closest_slack_bits": margin,
            "rhin_free_window": lengths is not None and not lengths,
            "survivors": survivors,
            "excluded": lengths is not None and not survivors,
        }


def table(X0: int, m_max: int = M_MAX, stop_after_failures: int = 6) -> list[dict[str, Any]]:
    """Rows ``m = 1, 2, ...`` at the floor ``X0``, stopping a few rows past the first ``m``
    that is not excluded."""
    rows, failures = [], 0
    for m in range(1, m_max + 1):
        r = row(m, X0)
        rows.append(r)
        if not r["excluded"]:
            failures += 1
            if failures >= stop_after_failures:
                break
    return rows


def excluded_through(rows: list[dict[str, Any]]) -> int:
    """The largest ``M`` with every ``m ≤ M`` excluded."""
    M = 0
    for r in rows:
        if r["excluded"] and r["m"] == M + 1:
            M = r["m"]
        else:
            break
    return M


# ---------------------------------------------------------------------------------------------
# Sanity: the template must not exclude the cycles that exist
# ---------------------------------------------------------------------------------------------

def known_cycles_survive() -> list[dict[str, Any]]:
    """With the floor set at each known cycle's least element, that cycle's ``(m, K)`` must
    pass the chaining test: the real cycles are witnesses that the inequalities are sound."""
    out = []
    for cycle in CYCLES[1:]:
        d = cycle_data(cycle)
        xmin = min(cycle)
        with mp.workdps(_DPS):
            o, lam = lambda_juggler(d["K"])
            finance = mpf(d["m"]) / lam
            tower = 2 ** log2_xmin_lower(d["K"], d["m"])
            out.append({
                "cycle_min": xmin, "K": d["K"], "o": d["o"], "m": d["m"],
                "o_matches_ceil": o == d["o"],
                "cycle_equation_holds": d["cycle_equation_holds"],
                "finance_holds": float(finance) >= xmin - 1,
                "tower_holds": float(tower) < xmin - 1 or xmin - 1 <= 1,
                "xmin_minus_one": xmin - 1,
                "finance_bound": float(finance),
                "tower_bound": float(tower),
            })
    return out


def run_identity_checks(limit: int = 4000) -> dict[str, Any]:
    """The run identity ``g^k(y) - 1 = (3/2)^k (y - 1)`` and ``a = v_2(y - 1)`` on every odd
    ``3 ≤ y < limit``, and the run reciprocal bound ``sum 1/(3 y_k - 1) ≤ 1/(y - 1)``."""
    worst_ratio = Fraction(0)
    checked = 0
    for y in range(3, limit, 2):
        a = run_length(y)
        run = odd_run(y)
        assert len(run) == a + 1, (y, a, run)
        u = Fraction(y - 1)
        for k, v in enumerate(run):
            assert Fraction(v - 1) == u * Fraction(3, 2) ** k, (y, k)
        recip = sum(Fraction(1, 3 * v - 1) for v in run[:-1])
        ratio = recip * (y - 1)
        worst_ratio = max(worst_ratio, ratio)
        checked += 1
    return {"checked": checked, "worst_recip_times_u": float(worst_ratio),
            "bound_holds": worst_ratio <= 1}


# ---------------------------------------------------------------------------------------------
# Payload, markdown, main
# ---------------------------------------------------------------------------------------------

def probe_payload() -> dict[str, Any]:
    tables = {}
    for X0, label in FLOORS:
        rows = table(X0)
        tables[label] = {
            "floor": X0,
            "excluded_through": excluded_through(rows),
            "rows": rows,
        }
    at_floor = tables[f"2^{FLOOR_LOG2}"]
    M = at_floor["excluded_through"]
    first_open = next((r for r in at_floor["rows"] if not r["excluded"]), None)
    mfree = negative_cycle_survivors(mpf(2 ** FLOOR_LOG2), 20_000_000)
    return {
        "map": "g(y) = y/2 (even), (3y-1)/2 (odd) on the positive integers; the shortcut 3n+1 map on the negatives",
        "known_cycles": [list(c) for c in CYCLES],
        "known_cycle_data": [{k: (v if k != "runs" else {str(a): b for a, b in v.items()})
                              for k, v in cycle_data(c).items()} for c in CYCLES],
        "floor_log2": FLOOR_LOG2,
        "rhin": {"exponent": float(RHIN_EXPONENT), "offset": float(RHIN_OFFSET),
                 "form": rhin_form()},
        "identity_checks": run_identity_checks(),
        "known_cycles_survive": known_cycles_survive(),
        "tables": tables,
        "m_free_survivors_at_floor": mfree[:12],
        "classification": {
            "label": CLASS_EXCLUDED if M >= 1 else "NEGATIVE_M_CYCLES_TABLES_INCONCLUSIVE",
            "excluded_through_at_floor": M,
            "first_open_m": None if first_open is None else first_open["m"],
            "first_open_survivors": None if first_open is None else first_open["survivors"],
            "conditional_on": "Rhin 1987 (external theorem); the floor 2^44 (laboratory certificate)",
        },
    }


def render_markdown(data: dict[str, Any]) -> str:
    lines = [
        "# m-cycles of the 3x-1 map above the floor",
        "",
        "Generated by `python -m research.juggler_sequence.negative_m_cycles`; do not edit.",
        "",
        f"Map: {data['map']}. Known cycles: {data['known_cycles']}. Verified floor `2^{data['floor_log2']}`.",
        "",
        f"Rhin's bound used: `{data['rhin']['form']}`.",
        "",
        "| floor | m excluded through | first open m | survivors at the first open m (K, o, log2 slack) |",
        "|---|---|---|---|",
    ]
    for label, t in data["tables"].items():
        first_open = next((r for r in t["rows"] if not r["excluded"]), None)
        if first_open is None:
            desc = "none in the tabled range"
            fm = "—"
        else:
            fm = str(first_open["m"])
            if not first_open["walked"]:
                desc = f"window not walked ({first_open['expected_admissible']:.0f} expected lengths)"
            else:
                desc = "; ".join(f"({s['K']}, {s['o']}, {s['log2_slack']:.1f})" for s in first_open["survivors"][:6])
        lines.append(f"| {label} | {t['excluded_through']} | {fm} | {desc} |")
    lines += ["", "## Rows at the verified floor", "",
              "| m | Lambda bound | K3 (Rhin ceiling) | admissible K below K3 | least admissible K | survivors |",
              "|---|---|---|---|---|---|"]
    for r in data["tables"][f"2^{data['floor_log2']}"]["rows"]:
        adm = "not walked" if not r["walked"] else str(r["admissible_count"])
        k0 = "—" if r["K0_least_admissible"] is None else str(r["K0_least_admissible"])
        surv = "none" if r["excluded"] else ("?" if not r["walked"] else str([s["K"] for s in r["survivors"]]))
        lines.append(f"| {r['m']} | {r['lambda_bound']:.3e} | {r['K3_rhin_ceiling']} | {adm} | {k0} | {surv} |")
    lines += ["", "## The cycles that exist pass the same test", ""]
    for c in data["known_cycles_survive"]:
        lines.append(f"- least element {c['cycle_min']}: K = {c['K']}, o = {c['o']}, m = {c['m']}; "
                     f"cycle equation exact: {c['cycle_equation_holds']}; finance bound {c['finance_bound']:.2f} "
                     f"≥ x_min - 1 = {c['xmin_minus_one']}: {c['finance_holds']}; tower bound "
                     f"{c['tower_bound']:.2f} < x_min - 1: {c['tower_holds']}")
    lines += ["", f"Classification: `{data['classification']['label']}`, excluded through m = "
              f"{data['classification']['excluded_through_at_floor']} at `2^{data['floor_log2']}`, "
              f"conditional on {data['classification']['conditional_on']}.", ""]
    return "\n".join(lines)


def write_artifacts(payload: dict[str, Any] | None = None) -> dict[str, Any]:
    data = payload or probe_payload()
    DATA_DIR.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(data, indent=2, default=str) + "\n", encoding="utf-8")
    DOC_PATH.write_text(render_markdown(data), encoding="utf-8")
    return data


def main() -> None:
    data = write_artifacts()
    c = data["classification"]
    print(f"{c['label']}: m-cycles excluded through m = {c['excluded_through_at_floor']} at 2^{FLOOR_LOG2}; "
          f"first open m = {c['first_open_m']}")
    for label, t in data["tables"].items():
        print(f"  floor {label}: excluded through m = {t['excluded_through']}")
    print(f"wrote {JSON_PATH} and {DOC_PATH}")


if __name__ == "__main__":
    main()
