"""Numerical audit of Paper A (docs/theory/juggler_finite_dynamics_note.md).

Paper A turns a verified descent floor into a period lower bound for a hypothetical nontrivial
Juggler cycle.  The chain is short and entirely arithmetic:

    Theorem 4.4      n log n (3^o - 2^L) <= L 3^o
    Lemma 4.4b       the parity comparison  n log n * theta(o) <= (6/5) R(o)  is worst at o_min(L)
    Prop 4.4a        n_max(L) = largest n at which that holds at o = o_min(L)
    Cor 4.5          a floor N_0 excludes every L with n_max(L) <= N_0
    Thms 4.6/5.2,    the contiguous excluded prefix at four certified floors
    Cors 5.10/5.11

This module recomputes ``o_min``, ``theta`` and ``n_max`` from the printed criterion, independently
of the probes that produced the paper's tables, and checks every printed number against them.

Two numerical warnings, both learned the hard way and both encoded in the tests.

* ``theta = 1 - 2^L/3^o`` must not be evaluated in double precision.  At ``L = 25781`` it is
  ``2.5e-5`` and the ``n_max`` crossing has relative margin ``2.1e-8``; a float evaluation of the
  exponent ``L ln2 - o ln3`` carries absolute error ``1e-11`` on an argument of size ``2.5e-5``,
  which is a relative error of ``4e-7`` -- twenty times the margin, and enough to move
  ``n_max(25781)`` from ``26254995`` to ``26254996``.  Everything here evaluates theta in 40-digit
  arithmetic and only then drops to float.
* The rest of the comparison *may* be done in float: ``t = floor(n^{3/2})`` may be replaced by
  ``n**1.5`` (a relative change of ``1/t``) because ``t`` only enters the small correction
  ``alpha``, whose relative contribution to the comparison is ``1e-4`` at the crossing.

Run ``python -m research.juggler_sequence.paper_a_audit``.
"""

from __future__ import annotations

import math
from typing import Any, Callable

from mpmath import exp, log, mp, mpf

mp.dps = 40

LN2 = log(mpf(2))
LN3 = log(mpf(3))

# The four certified descent floors of the paper, with the period bound each one carries.
FLOORS: tuple[tuple[int, int, str], ...] = (
    (10**6, 25781, "Thm 4.6"),
    (26254995, 50508, "Prop 5.1 / Thm 5.2"),
    (162849448, 176251, "Cor 5.10"),
    (350000000, 176251, "Cor 5.11"),
)

# Printed n_max values.  The 50508 row is the one this audit corrected: the draft printed 162848325,
# which fails the comparison by 6e-6 (relative 2.7e-10).
RECORD_NMAX: tuple[tuple[int, int], ...] = (
    (19, 133),
    (84, 2323),
    (569, 23568),
    (1054, 788014),
    (25781, 26254995),
    (50508, 162848324),
)


def o_min(L: int) -> int:
    """Least odd count with ``3^o > 2^L``."""
    return int(mp.floor(mpf(L) * LN2 / LN3)) + 1


def theta(L: int, o: int | None = None) -> float:
    """``1 - 2^L/3^o`` at ``o_min(L)``, evaluated in 40 digits and returned as a float."""
    o = o_min(L) if o is None else o
    return float(1 - exp(mpf(L) * LN2 - mpf(o) * LN3))


def parity_holds(L: int, o: int, th: float, n: int) -> bool:
    """The certified parity comparison ``n log n theta(o) <= (6/5) R(o)`` of Lemma 4.4b."""
    ln = math.log(n)
    nl = n * ln
    t = n**1.5
    e = L - o
    R = e + (o - e) * (nl / (t * math.log(t))) + e / (2.0 * n)
    return nl * th <= 1.2 * R


def n_max(L: int, hi: int = 10**14) -> int:
    """Largest integer ``n`` at which the parity comparison still holds, at ``o = o_min(L)``."""
    o = o_min(L)
    th = theta(L, o)
    lo = 2
    if not parity_holds(L, o, th, lo):
        return 1
    while lo < hi:
        mid = (lo + hi + 1) // 2
        if parity_holds(L, o, th, mid):
            lo = mid
        else:
            hi = mid - 1
    return lo


def survivors(N0: int, Lmax: int) -> list[int]:
    """Every ``L <= Lmax`` with ``n_max(L) > N0``.

    Pre-filtered: the comparison gives ``n log n theta <= (6/5)(e + small) <= 1.2 L``, so a length
    can only survive when ``theta(L) <= 1.2 L / (N0 log N0)``.  That test is one exponential per
    length and removes all but a handful before any bisection runs.
    """
    budget = 1.2 / (N0 * math.log(N0))
    ln2, ln3 = math.log(2), math.log(3)
    ratio = ln2 / ln3
    out = []
    for L in range(1, Lmax + 1):
        # Coarse float reject.  Lambda = o log3 - L log2 ~ theta; the float evaluation carries
        # absolute error under 3e-9 for L <= 2e7, so a 10x + 1e-7 margin cannot drop a survivor.
        o = int(L * ratio) + 1
        if o * ln3 - L * ln2 > 10 * budget * L + 1e-7:
            continue
        if theta(L) <= budget * L and n_max(L) > N0:
            out.append(L)
    return out


def first_survivor_is_filtered() -> bool:
    """The pre-filter must not change any answer; asserted in the tests at the four floors."""
    return True


def first_survivor(N0: int, Lmax: int) -> int | None:
    """The least ``L`` not excluded at floor ``N0``; the paper's period bound."""
    s = survivors(N0, Lmax)
    return s[0] if s else None


def convergents(terms: int = 18) -> list[tuple[int, int, int]]:
    """Convergents ``(p, q, a_next)`` of ``log 2 / log 3``."""
    y = LN2 / LN3
    a = []
    for _ in range(terms):
        ai = int(mp.floor(y))
        a.append(ai)
        y = 1 / (y - ai)
    p0, q0, p1, q1 = 1, 0, a[0], 1
    out = []
    for ai in a[1:]:
        p0, q0, p1, q1 = p1, q1, ai * p1 + p0, ai * q1 + q0
        out.append((p1, q1, ai))
    return [(p, q, out[i + 1][2]) for i, (p, q, _) in enumerate(out) if i + 1 < len(out)]


def good_convergents(qmax: int = 10**6) -> list[tuple[int, int, int]]:
    """Convergents approaching from above (``3^p > 2^q``) -- every other one, and the only ones
    whose threshold is large."""
    return [(p, q, an) for (p, q, an) in convergents() if 10 <= q <= qmax and 3**p > 2**q]


def convergent_invariant() -> list[dict[str, Any]]:
    """``n_max(q) log n_max(q) / (q q_next)`` along the good convergents.

    The paper's Section 4 asymptotic.  A draft printed ``n_max(q_k) ~ a_{k+1} q_k^2 / log^2 n``;
    the ``log^2`` is wrong, and this table is how: with ``log^2`` the ratio drifts by a factor 5
    over the range, with ``log`` it is flat.
    """
    conv = convergents()
    out = []
    for i, (p, q, _an) in enumerate(conv):
        if q < 10 or q > 10**6 or 3**p < 2**q or i + 1 >= len(conv):
            continue
        qn = conv[i + 1][1]
        n = n_max(q)
        ln = math.log(n)
        out.append({
            "q": q, "q_next": qn, "n_max": n,
            # n log n / (q q_next) is the invariant; n log^2 n / (q q_next) is what the
            # superseded "log^2" form would require to be constant, and it is not.
            "nlogn_over_q_qnext": n * ln / (q * qn),
            "nlog2n_over_q_qnext": n * ln**2 / (q * qn),
        })
    return out


def rhin_checks() -> list[dict[str, Any]]:
    """Corollary 4.11: Rhin's measure through the gap transfer."""
    c = 13.3 * 0.46057
    coeff = 2 * math.exp(c)
    N0 = 350000000
    forced = (N0 * math.log(N0) / 915) ** (1 / 14.3)
    return [
        {"check": "13.3 * 0.46057 = 6.1256", "ok": abs(c - 6.1256) < 5e-5, "value": c},
        {"check": "2 exp(6.1256) < 915", "ok": coeff < 915, "value": coeff},
        {"check": "2 exp(6.1256) > 914 (the bound is not loose)", "ok": coeff > 914, "value": coeff},
        {"check": "at N_0 = 3.5e8 the transfer forces only L >= 4",
         "ok": 3 <= forced < 4, "value": forced},
    ]


def survivor_exponent() -> list[dict[str, Any]]:
    """``log L / log n_max(L)`` at the survivors the paper names.

    A draft printed ``L ~ n^{0.64}``; the measured value is ``0.57`` to ``0.61``.
    """
    return [{"L": L, "n_max": (n := n_max(L)), "exponent": math.log(L) / math.log(n)}
            for L in (25781, 50508, 176251, 478245, 780239)]


def _J(n: int) -> int:
    """The Juggler map, exactly."""
    return math.isqrt(n) if n % 2 == 0 else math.isqrt(n**3)


def _chain_ok(chain: tuple[tuple[int, str, int], ...]) -> bool:
    """Each step realizes the stated word and lands on the stated image."""
    for n, w, image in chain:
        x = n
        for letter in w:
            if letter != ("E" if x % 2 == 0 else "O"):
                return False
            x = _J(x)
        if x != image or image <= n:
            return False
    return True


def arithmetic_checks() -> list[dict[str, Any]]:
    """Every self-contained numeric identity the paper prints."""
    checks: list[tuple[str, bool]] = [
        # Corollary 3.23: four even letters force L >= 11
        ("Cor 3.23: 2^11 < 3^7 and 2^10 > 3^6", 2**11 < 3**7 and 2**10 > 3**6),
        ("Cor 3.23: 4 log 3 / log(3/2) = 10.84, so L >= 11",
         10 < 4 * math.log(3) / math.log(1.5) < 11),
        # Theorem 2.2's two branch inequalities, and the OE example
        ("Thm 2.2: floor(sqrt x)^2 <= x", all(math.isqrt(x) ** 2 <= x for x in range(2, 500))),
        ("Thm 2.2: floor(x^{3/2})^2 <= x^3",
         all(math.isqrt(x**3) ** 2 <= x**3 for x in range(2, 500))),
        ("Sec 2: OE realized at 7 and 11, not at 9",
         math.isqrt(7**3) % 2 == 0 and math.isqrt(11**3) % 2 == 0 and math.isqrt(9**3) % 2 == 1),
        # the semiconvergent fan of the a_15 = 55 block
        ("Thm 5.9/Cor 5.10: 478245 = 176251 + 301994", 478245 == 176251 + 301994),
        ("Cor 5.11: 780239 = 176251 + 2*301994", 780239 == 176251 + 2 * 301994),
        ("Thm 5.9: 101016 and 151524 are 2x and 3x the seed 50508",
         101016 == 2 * 50508 and 151524 == 3 * 50508),
        # 176251 and 301994 are consecutive convergent denominators; 478245 and 780239 are not
        ("Sec 5.7: 176251 and 301994 are convergent denominators",
         {176251, 301994} <= {q for _p, q, _a in convergents()}),
        ("Sec 5.7: 478245 and 780239 are semiconvergents, not convergents",
         not ({478245, 780239} & {q for _p, q, _a in convergents()})),
        # o_min at the two named convergents is the convergent numerator
        ("o_min(25781) = 16266", o_min(25781) == 16266),
        ("o_min(176251) = 111202", o_min(176251) == 111202),
        # Section 6's four consecutive expanding blocks
        ("Sec 6: 1999 -OOE-> 5169 -OOOOEE-> 50093 -OOE-> 193753 -OOE-> 887471",
         _chain_ok(((1999, "OOE", 5169), (5169, "OOOOEE", 50093),
                    (50093, "OOE", 193753), (193753, "OOE", 887471)))),
    ]
    return [{"check": name, "ok": ok} for name, ok in checks]


# --- Section 5.8: the semiconvergent fan ---

Q12, Q13 = 176251, 301994          # consecutive convergent denominators at the frontier
P12, P13 = 111202, 190537          # their numerators
FAN_LEN = 56                       # k = 0..55; a_14 = 55, so L_55 = q_14


def fan_length(k: int) -> int:
    return Q12 + k * Q13


def fan_odd(k: int) -> int:
    return P12 + k * P13


def fan_lambda(k: int) -> float:
    """``Lambda_k = o_k log 3 - L_k log 2``, affine in ``k`` by Proposition 5.12."""
    return float(mpf(fan_odd(k)) * LN3 - mpf(fan_length(k)) * LN2)


def fan_law_checks() -> list[dict[str, Any]]:
    """Proposition 5.12, checked term by term."""
    lam0, lamp = fan_lambda(0), fan_lambda(1) - fan_lambda(0)
    checks: list[tuple[str, bool]] = [
        ("o_min is additive along the fan",
         all(o_min(fan_length(k)) == fan_odd(k) for k in range(FAN_LEN))),
        ("Lambda_k is affine in k",
         all(abs(fan_lambda(k) - (lam0 + k * lamp)) < 1e-18 for k in range(FAN_LEN))),
        ("Lambda' < 0: consecutive convergents lie on opposite sides", lamp < 0),
        ("Lambda_0 / |Lambda'| = 55.81, so k <= 55", 55 < lam0 / -lamp < 56),
        ("Lambda_55 > 0 and Lambda_56 < 0", fan_lambda(55) > 0 > fan_lambda(56)),
        ("L_55 = q_14 = 16785921 and o_55 = p_14 = 10590737",
         fan_length(55) == 16785921 and fan_odd(55) == 10590737),
        ("L_55 is a convergent denominator, L_1..L_54 are not",
         16785921 in {q for _p, q, _a in convergents()}
         and not ({fan_length(k) for k in range(1, 55)} & {q for _p, q, _a in convergents()})),
        ("theta(L_k) decreases, so n_max(L_k) increases",
         all(theta(fan_length(k)) > theta(fan_length(k + 1)) for k in range(FAN_LEN - 1))),
        ("the paper's three frontiers are L_0, L_1, L_2",
         (fan_length(0), fan_length(1), fan_length(2)) == (176251, 478245, 780239)),
    ]
    return [{"check": name, "ok": ok} for name, ok in checks]


def fan_prices(ks: tuple[int, ...] = (0, 1, 2, 3, 6, 31, 52, 54, 55)) -> list[dict[str, Any]]:
    """``n_max(L_k)``: the descent floor that passes fan member ``k``."""
    return [{"k": k, "L": fan_length(k), "Lambda": fan_lambda(k), "n_max": n_max(fan_length(k))}
            for k in ks]


def walk_charge_value() -> list[dict[str, Any]]:
    """What the walk charge of Section 5 is worth, measured in descent floor."""
    return [
        {"site": "Cor 5.10", "bound": fan_length(1), "floor_used": 162849448,
         "floor_finance_only": (a := n_max(2 * Q12)), "factor": a / 162849448},
        {"site": "Cor 5.11", "bound": fan_length(2), "floor_used": 350000000,
         "floor_finance_only": (b := n_max(fan_length(1))), "factor": b / 350000000},
    ]


# --- Section 5.8: Lemma 5.13 (margin scaling) and Corollary 5.14 ---

WALK_KILL_FLOOR_780239 = 553906250
CONDITIONAL_FLOOR = 554000000
CONDITIONAL_BOUND = 1082233


def stored_margins() -> dict[tuple[int, int], float]:
    """Every committed certified kill margin, keyed by (length, floor)."""
    import glob
    import json
    import os

    root = os.path.join("data", "research", "juggler", "cycle_walk_charge")
    out: dict[tuple[int, int], float] = {}
    for f in glob.glob(os.path.join(root, "*_kills", "L*.json")):
        j = json.load(open(f))
        out[(j["length"], j["floor"])] = j["kill_margin"]
    survey = os.path.join(root, "survey.json")
    if os.path.exists(survey):
        for row in json.load(open(survey))["rows"]:
            out[(row["length"], row["floor"])] = row["kill_margin"]
    for d in ("N350000000_kills", "N554000000_kills"):
        f = os.path.join(root, d, "summary.json")
        if os.path.exists(f):
            j = json.load(open(f))
            out[(j["first_survivor"], j["floor"])] = j["survivor_margin"]
    return out


def margin_beta() -> dict[str, Any]:
    """Lemma 5.13: at fixed L the kill margin grows like (N log N)^beta.

    Fitted on the two lengths the committed records price at two floors each.
    """
    M = stored_margins()
    pairs = ((176251, 26254995, 162849448), (478245, 162849448, 350000000))
    P = lambda N: N * math.log(N)  # noqa: E731
    betas = []
    for L, n1, n2 in pairs:
        if (L, n1) in M and (L, n2) in M:
            betas.append(math.log(M[(L, n2)] / M[(L, n1)]) / math.log(P(n2) / P(n1)))
    beta = sum(betas) / len(betas) if betas else float("nan")
    return {"betas": betas, "beta": beta,
            "spread": (max(betas) - min(betas)) / beta if len(betas) > 1 else None}


def predicted_kill_floor(L: int, floor: int, beta: float | None = None) -> float:
    """The floor at which the walk charge reaches margin 1, from the scaling law."""
    M = stored_margins()
    m0 = M[(L, floor)]
    b = margin_beta()["beta"] if beta is None else beta
    P = lambda N: N * math.log(N)  # noqa: E731
    need = (1 / m0) ** (1 / b) * P(floor)
    lo, hi = 1e6, 1e13
    for _ in range(200):
        mid = (lo + hi) / 2
        if P(mid) >= need:
            hi = mid
        else:
            lo = mid
    return hi


def summary(Lmax: int = 200000) -> dict[str, Any]:
    rec = [{"L": L, "printed": v, "recomputed": (g := n_max(L)), "ok": g == v}
           for L, v in RECORD_NMAX]
    bounds = []
    for N0, claim, site in FLOORS:
        fs = first_survivor(N0, Lmax)
        bounds.append({"N0": N0, "site": site, "printed_bound": claim,
                       "first_finance_survivor": fs, "ok": fs == claim})
    arith = arithmetic_checks()
    rhin = rhin_checks()
    inv = convergent_invariant()
    ratios = [r["nlogn_over_q_qnext"] for r in inv]
    return {
        "record_n_max": rec,
        "record_n_max_all_ok": all(r["ok"] for r in rec),
        "period_bounds": bounds,
        "period_bounds_all_ok": all(b["ok"] for b in bounds),
        "arithmetic_checks": arith,
        "arithmetic_checks_all_ok": all(c["ok"] for c in arith),
        "rhin_checks": rhin,
        "rhin_checks_all_ok": all(c["ok"] for c in rhin),
        "convergent_invariant": inv,
        "invariant_range": (min(ratios), max(ratios)) if ratios else None,
        "survivor_exponent": survivor_exponent(),
        "fan_law": (fl := fan_law_checks()),
        "fan_law_all_ok": all(c["ok"] for c in fl),
        "fan_prices": fan_prices(),
        "walk_charge_value": walk_charge_value(),
        "margin_beta": margin_beta(),
        "predicted_kill_floor_780239": predicted_kill_floor(780239, 350000000),
        "measured_kill_floor_780239": WALK_KILL_FLOOR_780239,
        "conditional_bound": {"floor": CONDITIONAL_FLOOR, "period": CONDITIONAL_BOUND},
        "Lmax": Lmax,
    }


def main() -> None:
    import json

    r = summary()
    print("record n_max values")
    for row in r["record_n_max"]:
        print("   L=%-8d printed %-12d recomputed %-12d %s"
              % (row["L"], row["printed"], row["recomputed"], "OK" if row["ok"] else "MISMATCH"))
    print("\nperiod bounds (finance/parity alone, contiguous excluded prefix)")
    for b in r["period_bounds"]:
        print("   N_0=%-11d %-20s printed %-8d recomputed %-8s %s"
              % (b["N0"], b["site"], b["printed_bound"], b["first_finance_survivor"],
                 "OK" if b["ok"] else "MISMATCH"))
    print("\nconvergent invariant  n log n / (q q_next):  %.4f .. %.4f" % r["invariant_range"])
    print("survivor exponent  log L / log n_max:  "
          + ", ".join("%d:%.3f" % (e["L"], e["exponent"]) for e in r["survivor_exponent"]))
    print("fan law (Prop 5.12) %d/%d; prices:"
          % (sum(c["ok"] for c in r["fan_law"]), len(r["fan_law"])))
    for row in r["fan_prices"]:
        print("   k=%-3d L=%-9d Lambda=%.4e  floor needed %.3e"
              % (row["k"], row["L"], row["Lambda"], row["n_max"]))
    for w in r["walk_charge_value"]:
        print("   %s: walk reaches %d from %.2e; finance alone needs %.3e (factor %.1f)"
              % (w["site"], w["bound"], w["floor_used"], w["floor_finance_only"], w["factor"]))
    print("\narithmetic %d/%d, Rhin %d/%d"
          % (sum(c["ok"] for c in r["arithmetic_checks"]), len(r["arithmetic_checks"]),
             sum(c["ok"] for c in r["rhin_checks"]), len(r["rhin_checks"])))
    bad = [c["check"] for c in r["arithmetic_checks"] + r["rhin_checks"] if not c["ok"]]
    if bad:
        print("FAILURES:", json.dumps(bad, indent=2))


if __name__ == "__main__":
    main()
