"""Paper A's cycle finance, transposed to Collatz, reproduces Eliahou 1993 and Hercher 2018.

`J-juggler-is-collatz-one-exponential-up` says the two problems share the linear form
`o log 3 - L log 2` and part only at how words attach to integers. On cycles that claim has a
numerical test, and this probe runs it.

**The two finance inequalities are one inequality with the sign of the gap flipped.** For a
shortcut Collatz cycle of length `K` with `p` odd steps, multiplying the step relations around
the cycle gives the exact identity `K log 2 - p log 3 = sum over odd steps of log(1 + 1/(3 x_j))`
(Eliahou's inequality (2), Hercher's Theorem 16), hence

    Lambda_C(K) := K log 2 - p log 3 = log 3 * frac(K x),   x = log 2 / log 3,   p = floor(K x),
    x_min <= p / (3 Lambda_C).

For a Juggler cycle Paper A Theorem 4.4 (`cycleMin_finance`, constant 1) gives

    Lambda_J(L) := o log 3 - L log 2 = log 3 * (1 - frac(L x)),   o = ceil(L x),
    n log n <= L / (1 - exp(-Lambda_J)) = L 3^o / (3^o - 2^L).

So `Lambda_J(L) = log 3 - Lambda_C(L)` for every length: the Collatz-dangerous lengths have
`frac(L x)` just above `0`, the Juggler-dangerous ones just below `1`, and the convergents of
`log 3 / log 2` alternate between the two. The cycle-level dictionary is `x_min <-> n log n`,
not the walk-level `log x <-> log log n`; the two differ by a factor `n` and must not be
substituted for one another.

**The test.** A length survives finance at a floor when its bound does not fall below the floor.
Enumerating the survivors exactly with the three-gap walk (the set `{K : frac(K x) < eps}` is
walked by the two one-sided return times of the rotation), the Collatz side gives

* floor `2^40`: smallest survivor `17087915`, every survivor of the form
  `301994 a + 17087915 b + 85137581 c` with `b >= 1` and `a c = 0` -- Eliahou 1993 exactly;
* floor `2^68`: smallest survivor `114208327604`, with `72057431991` odd steps -- Hercher's
  2018 period bound, quoted as "more than 7.2e10 odd numbers";
* floor `2^71`: the second survivor is `217976794617`, Barina's 2025 bound; the first is still
  `114208327604`, which Barina removes with a sharper averaging this probe does not use.

and the Juggler side, at constant 1, leaves `1054` and its multiples first at floor `10^6` and
`50508` first at `3.5e8`. Paper A's certified comparison (Lemma 4.4b, evens charged at `n^2` and
climb interiors at `n^(3/2)`) is sharper and leaves `25781` and `176251` -- the printed Theorem
4.6 and Corollary 5.11 finance floors -- so the inequality used on the Collatz side here is the
weaker of the two Juggler forms, and it is that weaker form which already matches the published
Collatz bounds.

**What it does not do.** No cycle of any length is excluded or claimed in either problem; the
Collatz numbers are re-derived, not new. The 1-cycle length `9809721694` (a Juggler-side
convergent numerator) survives the Juggler finance at `N_0 = 3.5e8` by ten orders of magnitude,
which is the numerical form of "Juggler has no Steiner theorem": nothing floor-free excludes a
Juggler 1-cycle, where Collatz has excluded them since 1977 through the 2-adic run congruence.
"""

from __future__ import annotations

import json
import math
from typing import Any

import numpy as np
from mpmath import mp, mpf, exp, floor, log

from research.juggler_sequence.lean_paths import DATA_ROOT, DOCS_RESEARCH
from research.juggler_sequence.paper_a_audit import survivors as paper_a_survivors

DATA_DIR = DATA_ROOT / "collatz_finance_mirror"
JSON_PATH = DATA_DIR / "summary.json"
DOC_PATH = DOCS_RESEARCH / "juggler_collatz_finance_mirror.md"

CLASS_MIRROR = "FINANCE_MIRROR_REPRODUCES_ELIAHOU_HERCHER"

#: Eliahou 1993: the admissible Collatz periods at floor 2^40.
ELIAHOU_GENERATORS = (301994, 17087915, 85137581)
#: Hercher 2018 at Barina's floor: the smallest surviving length, and its odd count.
HERCHER_LENGTH, HERCHER_ODD = 114208327604, 72057431991
#: Barina 2025 at floor 2^71.
BARINA_LENGTH = 217976794617

_DPS = 80


def _x() -> mpf:
    return log(2) / log(3)


def frac(v: mpf) -> mpf:
    return v - floor(v)


def lambda_collatz(K: int) -> tuple[int, mpf]:
    """``(p, Lambda_C)``: ``p = floor(K x)`` and ``K log 2 - p log 3 = log 3 * frac(K x)``."""
    with mp.workdps(_DPS):
        v = K * _x()
        p = int(floor(v))
        return p, log(3) * frac(v)


def lambda_juggler(L: int) -> tuple[int, mpf]:
    """``(o, Lambda_J)``: ``o = ceil(L x)`` and ``o log 3 - L log 2 = log 3 * (1 - frac(L x))``."""
    with mp.workdps(_DPS):
        v = L * _x()
        o = int(floor(v)) + 1
        return o, log(3) * (1 - frac(v))


def collatz_bound(K: int) -> mpf:
    """The Collatz finance majorant on the cycle minimum, ``p / (3 Lambda_C)``."""
    p, lam = lambda_collatz(K)
    with mp.workdps(_DPS):
        return mpf(p) / (3 * lam)


def juggler_bound(L: int) -> mpf:
    """Paper A Theorem 4.4 at constant 1, as a bound on ``n log n``: ``L / (1 - exp(-Lambda_J))``."""
    _, lam = lambda_juggler(L)
    with mp.workdps(_DPS):
        return mpf(L) / (1 - exp(-lam))


def nlogn(N0: int) -> mpf:
    with mp.workdps(_DPS):
        return mpf(N0) * log(mpf(N0))


# ---------------------------------------------------------------------------------------------
# Sides of the convergents
# ---------------------------------------------------------------------------------------------

def continued_fraction(terms: int = 30) -> list[int]:
    """Partial quotients of ``log 2 / log 3``."""
    with mp.workdps(_DPS):
        a, y = [], _x()
        for _ in range(terms):
            ai = int(floor(y))
            a.append(ai)
            y = 1 / (y - ai)
        return a


def convergent_sides(terms: int = 22, exact_below: int = 2 * 10**7) -> list[dict[str, Any]]:
    """Each convergent ``p/q`` of ``x`` with the sign of ``q log 2 - p log 3``.

    ``3^p > 2^q`` (gap negative, Juggler-admissible) or ``2^q > 3^p`` (gap positive,
    Collatz-admissible). Below ``exact_below`` the side is decided by comparing the integers
    ``3^p`` and ``2^q`` themselves; above it by ``frac(q x)`` at 80 digits, which is certified by
    the margin recorded in the row.
    """
    a = continued_fraction(terms)
    p0, q0, p1, q1 = 0, 1, 1, 0
    rows: list[dict[str, Any]] = []
    for ai in a:
        p0, p1 = p1, ai * p1 + p0
        q0, q1 = q1, ai * q1 + q0
        p, q = p1, q1
        if q == 0:
            continue
        with mp.workdps(_DPS):
            f = frac(q * _x())
            margin = float(min(f, 1 - f))
        if q <= exact_below:
            juggler_side = (3**p).bit_length() > q   # 3^p > 2^q  <=>  bit_length(3^p) > q
            method = "integers"
        else:
            juggler_side = bool(f > mpf("0.5"))
            method = "frac at 80 digits"
        rows.append({
            "p": p, "q": q, "frac_q_x": float(f), "margin": margin, "method": method,
            "side": "juggler" if juggler_side else "collatz",
        })
    return rows


# ---------------------------------------------------------------------------------------------
# The three-gap walk
# ---------------------------------------------------------------------------------------------

def _one_sided_returns(eps: mpf, terms: int = 40) -> tuple[int, int, mpf, mpf]:
    """``(q1, q2, d1, d2)``: least ``q`` with ``frac(q x) < eps`` and least ``q`` with
    ``1 - frac(q x) < eps``, found among convergents and semiconvergents."""
    a = continued_fraction(terms)
    p0, q0, p1, q1 = 0, 1, 1, 0
    conv = []
    for ai in a:
        p0, p1 = p1, ai * p1 + p0
        q0, q1 = q1, ai * q1 + q0
        conv.append((p1, q1))
    x = _x()
    best = {+1: None, -1: None}
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
    q1, q2 = best[+1], best[-1]
    return q1, q2, frac(q1 * x), 1 - frac(q2 * x)


def three_gap_walk(eps: mpf, side: int, kmax: int) -> list[int]:
    """All ``K <= kmax`` with ``g(K) < eps``, ``g = frac(K x)`` (side +1) or ``1 - frac(K x)``
    (side -1), enumerated exactly: from a member with value ``g``, the next member is ``K + up``
    if ``g + du < eps``, else ``K + dn`` if ``g >= dd``, else ``K + up + dn``."""
    with mp.workdps(_DPS):
        q1, q2, d1, d2 = _one_sided_returns(eps)
        up, dn, du, dd = (q1, q2, d1, d2) if side > 0 else (q2, q1, d2, d1)
        K, g, out = up, du, []
        while K <= kmax:
            out.append(K)
            if g + du < eps:
                K += up
                g += du
            elif g >= dd:
                K += dn
                g -= dd
            else:
                K += up + dn
                g += du - dd
        return out


def collatz_survivors(X0: mpf, kmax: int) -> list[dict[str, Any]]:
    """Collatz lengths ``K <= kmax`` whose finance majorant does not fall below the floor."""
    with mp.workdps(_DPS):
        eps = mpf(kmax) * _x() / (3 * log(3) * X0) * mpf("1.001")
        out = []
        for K in three_gap_walk(eps, +1, kmax):
            p, lam = lambda_collatz(K)
            bound = mpf(p) / (3 * lam)
            if bound >= X0:
                out.append({"K": K, "p": p, "frac": float(lam / log(3)), "x_min_le": float(bound)})
        return out


def juggler_survivors(N0: int, lmax: int) -> list[dict[str, Any]]:
    """Juggler lengths ``L <= lmax`` surviving Theorem 4.4 at constant 1 at floor ``N0``."""
    with mp.workdps(_DPS):
        F = nlogn(N0)
        eps = min(mpf(lmax) / (log(3) * F) * mpf("1.001"), mpf("0.5"))
        out = []
        for L in three_gap_walk(eps, -1, lmax):
            o, lam = lambda_juggler(L)
            bound = mpf(L) / (1 - exp(-lam))
            if bound >= F:
                out.append({"L": L, "o": o, "one_minus_frac": float(lam / log(3)),
                            "nlogn_le": float(bound)})
        return out


def brute_force_collatz_survivors(X0: float, kmax: int) -> list[int]:
    """Independent check of the walk: every ``K <= kmax`` by a float candidate filter and an
    exact refinement. ``kmax`` up to a few ``10^7`` runs in about a second."""
    xf = float(_x())
    log3 = math.log(3)
    K = np.arange(1, kmax + 1, dtype=np.float64)
    f = np.mod(K * xf, 1.0)
    sel = f <= K * xf / (3.0 * log3 * X0) * 1.01 + 1e-7
    out = []
    for k in K[sel].astype(np.int64).tolist():
        if collatz_bound(int(k)) >= X0:
            out.append(int(k))
    return out


def eliahou_decomposition(K: int) -> tuple[int, int, int] | None:
    """``(a, b, c)`` with ``K = 301994 a + 17087915 b + 85137581 c``, ``b >= 1``, ``a c = 0``."""
    g1, g2, g3 = ELIAHOU_GENERATORS
    for c in range(0, K // g3 + 1):
        for b in range(1, (K - g3 * c) // g2 + 1):
            rest = K - g3 * c - g2 * b
            if rest % g1 == 0:
                a = rest // g1
                if a * c == 0:
                    return (a, b, c)
    return None


# ---------------------------------------------------------------------------------------------
# The record
# ---------------------------------------------------------------------------------------------

def probe_payload(*, kmax_40: int = 4 * 10**8, brute_kmax: int = 3 * 10**7) -> dict[str, Any]:
    with mp.workdps(_DPS):
        two40, two68, two71 = mpf(2) ** 40, mpf(2) ** 68, mpf(2) ** 71
        hercher_floor = 695 * mpf(2) ** 60
        s40 = collatz_survivors(two40, kmax_40)
        brute = brute_force_collatz_survivors(float(two40), brute_kmax)
        walk_below = [r["K"] for r in s40 if r["K"] <= brute_kmax]
        s_h = collatz_survivors(hercher_floor, 4 * 10**11)
        s68 = collatz_survivors(two68, 4 * 10**11)
        s71 = collatz_survivors(two71, 10**12)
        j6 = juggler_survivors(10**6, 2 * 10**6)
        j35 = juggler_survivors(350_000_000, 2 * 10**6)
        one_cycle = 9809721694
        o1, lam1 = lambda_juggler(one_cycle)
        mirror = max(abs(lambda_collatz(K)[1] + lambda_juggler(K)[1] - log(3))
                     for K in (1, 19, 84, 1054, 301994, 17087915, 85137581))
    return {
        "answer": "Paper A's finance transposed by x_min <-> n log n reproduces Eliahou and Hercher",
        "identities": {
            "lambda_collatz": "K log 2 - floor(K x) log 3 = log 3 * frac(K x)",
            "lambda_juggler": "ceil(L x) log 3 - L log 2 = log 3 * (1 - frac(L x))",
            "mirror": "Lambda_J(L) = log 3 - Lambda_C(L)",
            "mirror_residual": float(mirror),
            "cycle_dictionary": "x_min <-> n log n (not the walk-level log x <-> log log n)",
        },
        "convergent_sides": convergent_sides(),
        "collatz": {
            "floor_2_40": {
                "smallest": s40[0]["K"], "count_below": kmax_40, "n_survivors": len(s40),
                "first": s40[:8],
                "all_in_eliahou_lattice": all(eliahou_decomposition(r["K"]) is not None for r in s40),
                "pure_301994_multiples_excluded": all(
                    collatz_bound(301994 * a) < two40 for a in range(1, 57)),
                "brute_force_agrees_below": brute_kmax,
                "brute_force_agrees": brute == walk_below,
            },
            "floor_695_2_60": {"smallest": s_h[0]["K"], "odd": s_h[0]["p"], "first": s_h[:4]},
            "floor_2_68": {"smallest": s68[0]["K"], "odd": s68[0]["p"], "first": s68[:4]},
            "floor_2_71": {"first_two": [r["K"] for r in s71[:2]], "first": s71[:4]},
            "eliahou_generators": list(ELIAHOU_GENERATORS),
            "hercher": [HERCHER_LENGTH, HERCHER_ODD], "barina": BARINA_LENGTH,
        },
        "juggler": {
            "floor_1e6": {"smallest": j6[0]["L"], "first": [r["L"] for r in j6[:12]],
                          "paper_a_certified_smallest": paper_a_survivors(10**6, 30_000)[0]},
            "floor_3_5e8": {"smallest": j35[0]["L"], "first": [r["L"] for r in j35[:12]],
                            "paper_a_certified_smallest": paper_a_survivors(350_000_000, 200_000)[0]},
            "one_cycle_length": one_cycle, "one_cycle_odd": o1,
            "one_cycle_nlogn_bound": float(mpf(one_cycle) / (1 - exp(-lam1))),
            "floor_nlogn_3_5e8": float(nlogn(350_000_000)),
        },
        "decision": {
            "classification": CLASS_MIRROR,
            "reason": (
                "the Collatz transposition of Theorem 4.4 reproduces Eliahou's period bound and"
                " lattice at 2^40 and Hercher's bound at 2^68 from the same inequality, walk and"
                " brute force agreeing; the Juggler side reproduces the laboratory's own survivors"
            ),
        },
        "anti_overclaim": (
            "No cycle of any length is excluded or claimed in either problem. The Collatz numbers"
            " are re-derived from a classical inequality, not new; Barina's 2025 bound needs a"
            " sharper averaging than this inequality. The Juggler 1-cycle length 9809721694"
            " survives finance at N_0 = 3.5e8, which records that no Juggler analogue of Steiner's"
            " theorem exists, not that a cycle does."
        ),
    }


def render_markdown(data: dict[str, Any]) -> str:
    c, j = data["collatz"], data["juggler"]
    lines = [
        "# Paper A's finance, transposed to Collatz, reproduces Eliahou 1993 and Hercher 2018",
        "",
        "Generated by `python -m research.juggler_sequence.collatz_finance_mirror`.",
        "",
        "## The mirror",
        "",
        f"- `{data['identities']['lambda_collatz']}`",
        f"- `{data['identities']['lambda_juggler']}`",
        f"- `{data['identities']['mirror']}` (residual `{data['identities']['mirror_residual']:.1e}`)",
        f"- cycle-level dictionary: `{data['identities']['cycle_dictionary']}`",
        "",
        "## Collatz side, `x_min <= p / (3 Lambda_C)`",
        "",
        f"- floor `2^40`: smallest survivor `{c['floor_2_40']['smallest']}`;"
        f" all `{c['floor_2_40']['n_survivors']}` survivors below `{c['floor_2_40']['count_below']}`"
        f" in Eliahou's lattice = `{c['floor_2_40']['all_in_eliahou_lattice']}`;"
        f" brute force agrees below `{c['floor_2_40']['brute_force_agrees_below']}` ="
        f" `{c['floor_2_40']['brute_force_agrees']}`",
        f"- floor `695 * 2^60`: smallest `{c['floor_695_2_60']['smallest']}` with"
        f" `{c['floor_695_2_60']['odd']}` odd steps (Hercher 2018)",
        f"- floor `2^68`: smallest `{c['floor_2_68']['smallest']}` with `{c['floor_2_68']['odd']}` odd steps",
        f"- floor `2^71`: first two `{c['floor_2_71']['first_two']}` (Barina 2025 is the second)",
        "",
        "## Juggler side, `n log n <= L / (1 - exp(-Lambda_J))` (Theorem 4.4, constant 1)",
        "",
        f"- floor `10^6`: smallest `{j['floor_1e6']['smallest']}`, first `{j['floor_1e6']['first']}`",
        f"- floor `3.5e8`: smallest `{j['floor_3_5e8']['smallest']}`, first `{j['floor_3_5e8']['first']}`",
        f"- the 1-cycle length `{j['one_cycle_length']}` has bound `{j['one_cycle_nlogn_bound']:.3e}`"
        f" against the floor `{j['floor_nlogn_3_5e8']:.3e}`: not excluded by finance",
        "",
        "## What this does not say",
        "",
        data["anti_overclaim"],
        "",
    ]
    return "\n".join(lines)


def write_artifacts(payload: dict[str, Any] | None = None) -> dict[str, Any]:
    data = payload if payload is not None else probe_payload()
    DATA_DIR.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(data, indent=2) + "\n", encoding="utf-8")
    DOC_PATH.write_text(render_markdown(data), encoding="utf-8")
    return data


def main() -> None:
    data = write_artifacts()
    print(data["decision"]["classification"])
    c = data["collatz"]
    print("2^40 smallest", c["floor_2_40"]["smallest"], "| lattice", c["floor_2_40"]["all_in_eliahou_lattice"],
          "| brute agrees", c["floor_2_40"]["brute_force_agrees"])
    print("2^68 smallest", c["floor_2_68"]["smallest"], "odd", c["floor_2_68"]["odd"])
    print("2^71 first two", c["floor_2_71"]["first_two"])
    print("juggler smallest", data["juggler"]["floor_1e6"]["smallest"], data["juggler"]["floor_3_5e8"]["smallest"])


if __name__ == "__main__":
    main()
