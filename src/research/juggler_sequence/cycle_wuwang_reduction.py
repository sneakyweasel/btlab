"""The Wu-Wang instance of Paper A's floor-free gap transfer.

Not a halt theorem, not a floor raise, not a kill, and not a Baker reopen.
Paper A Corollary 4.11 feeds Rhin's effective measure through the gap
transfer `n log n * min(Lambda, 1) <= 2 L` and reports

    n log n <= 915 * L^14.3,   so   L > (n log n / 915)^(1/14.3).

The laboratory already imports a sharper measure for a different purpose.
`docs/problems/juggler_cycle_walk_fan_growth.md` cites Wu-Wang (2014),

    |a + b log 2 + c log 3| >= H^(-4.1163051-eps),    H = max(|b|, |c|),

and uses it only to cap fan widths. Corollary 4.11's own substitution is
`(a, b, c) = (0, -L, o)` with `H = max(L, o) = L`, which is exactly the
shape Wu-Wang bounds. Carrying it back gives

    n log n <<_eps L^5.1163051,   so   L >>_eps n^0.1954,

against `n^0.0699` from Rhin. Three consequences are measured here.

**The reduction.** The short-cycle regime Corollary 4.11 excludes widens
from `L^14.3 <= n log n / 915` to `L^5.1163051 <= C n log n / 2`. Nothing
new is killed: at every certified floor the finance table is far stronger
(the Corollary forces `L >= 4` at `N_0 = 3.5e8` where the table forces
`780239`), which is the recorded reason the floor-level Baker transfer is
REFUTED and the floor-free transfer is its complement.

**The period lower bound.** Read the same inequality the other way and it
is the only proved statement in which a cycle's *period* grows with its
*minimum*, with no descent floor anywhere. That is a different claim from
the fan-width cap and from the refuted floor-level transfer.

**The closure threshold.** The standing reopen condition of
`docs/problems/juggler_cycle_method_ceilings.md` is "a lower bound on the
cycle minimum in terms of the period", stated without a number. The
transfer supplies the number: a lower bound `n >> L^(p+1)` closes the
no-cycle problem, where `p` is any Diophantine exponent valid for
`o log 3 - L log 2`. Wu-Wang puts that target at `L^5.1163051` instead of
Rhin's `L^14.3`, and `p >= 1` for every irrational, so `L^2` is a hard
floor no improvement of the measure can go below.

**What it does not do.** `n_max(q_k) log n_max ~ 0.45 q_k q_(k+1)`, so the
minimum a survivor is allowed is governed by the *next* partial quotient,
not by a power of `L` alone. The measured survivor exponent `0.59` is
`n_max ~ L^2 / log n_max` at the tested scale, not a genuine exponent
below two; `survivor_band` prints both readings. Wu-Wang caps
`q_(k+1) = O_eps(q_k^4.1163051)` but does not give `a_(k+1) = O(1)`, so the
family leftover of Paper D is untouched, and the kill criterion here is a
period bound in `n`, not a function of the surplus `theta` -- which is what
the standing prohibition in `juggler_cycle_method_ceilings` forbids.

Lean: `formal/Problems/Juggler/GapTransferWW.lean`
(`cycleMin_length_of_gap_power`, `cycleMin_period_ge`,
`no_cycleMin_of_gap_and_minimum`). The transcendence input is a
hypothesis there, as Rhin is in `GapTransfer.lean`.
"""

from __future__ import annotations

import json
import math
from typing import Any

from research.juggler_sequence.cycle_finance import DATA_DIR
from research.juggler_sequence.paper_a_audit import (
    convergents,
    n_max,
    survivor_exponent,
)

#: Rhin, as Paper A prints it: `Lambda > e^(-6.1256) L^(-13.3)`.
RHIN_P = 13.3
RHIN_C = math.exp(-6.1256)

#: Wu-Wang 2014, `|a + b log2 + c log3| >= H^(-4.1163051-eps)`.
#: `eps`-asymptotic with an implied constant, unlike Rhin.
WUWANG_P = 4.1163051

#: Bondareva-Luchin-Salikhov 2018 sharpen the same shape.
BLS_P = 4.116201

#: Dirichlet: no irrational has an exponent below one, so `p + 1 >= 2`
#: is a hard floor on every instance of the scheme.
DIRICHLET_P = 1.0

#: The certified descent floor. Not raised here.
N0 = 350_000_000


def transfer_exponent(p: float) -> float:
    """Exponent on `L` in `n log n <= (2/C) L^(p+1)`."""
    return p + 1.0


def period_exponent(p: float) -> float:
    """Exponent on `n` in the floor-free period lower bound `L >> n^(1/(p+1))`."""
    return 1.0 / transfer_exponent(p)


def forced_period(n: int, p: float, const: float) -> float:
    """The period the transfer forces at minimum `n`, from `L >= (C n log n / 2)^(1/(p+1))`.

    `const` is the `C` of the budget `C L^(-p)`; for Rhin it is the printed
    `e^(-6.1256)`, for Wu-Wang it is the implied `C_eps` and the value is a
    diagnostic at `C = 1`, not a certified number.
    """
    return (const / 2.0 * n * math.log(n)) ** period_exponent(p)


def exponent_table() -> list[dict[str, Any]]:
    """Rhin against Wu-Wang, on the three readings of the same inequality."""
    rows = [
        ("rhin-1987 (printed, effective)", RHIN_P, RHIN_C, True),
        ("wu-wang-2014 (asymptotic)", WUWANG_P, 1.0, False),
        ("bondareva-luchin-salikhov-2018", BLS_P, 1.0, False),
        ("Dirichlet floor (no measure beats it)", DIRICHLET_P, 1.0, False),
    ]
    out = []
    for label, p, const, effective in rows:
        out.append(
            {
                "source": label,
                "diophantine_exponent_p": p,
                "length_exponent": transfer_exponent(p),
                "period_exponent_in_n": period_exponent(p),
                "minimum_lower_bound_needed": transfer_exponent(p),
                "constant_effective": effective,
                "forced_period_at_N0": forced_period(N0, p, const),
            }
        )
    return out


def wuwang_checks() -> list[dict[str, Any]]:
    """The arithmetic of the swap, as `rhin_checks` does for Corollary 4.11."""
    rhin_forced = (N0 * math.log(N0) / 915) ** (1 / 14.3)
    ww_forced = forced_period(N0, WUWANG_P, 1.0)
    ratio = transfer_exponent(RHIN_P) / transfer_exponent(WUWANG_P)
    return [
        {
            "check": "Wu-Wang length exponent is 4.1163051 + 1",
            "ok": abs(transfer_exponent(WUWANG_P) - 5.1163051) < 1e-12,
            "value": transfer_exponent(WUWANG_P),
        },
        {
            "check": "period exponent in n rises from 1/14.3 to 1/5.1163051",
            "ok": abs(period_exponent(WUWANG_P) - 0.19545355) < 1e-7,
            "value": period_exponent(WUWANG_P),
        },
        {
            "check": "the swap is worth a factor 2.8 in the exponent",
            "ok": 2.79 < ratio < 2.80,
            "value": ratio,
        },
        {
            "check": "still toothless at the certified floor: forced period below 780239",
            "ok": ww_forced < 780239,
            "value": ww_forced,
        },
        {
            "check": "but stronger than Rhin at that floor",
            "ok": ww_forced > rhin_forced,
            "value": ww_forced / rhin_forced,
        },
        {
            "check": "Dirichlet floor: no measure takes the target below L^2",
            "ok": abs(transfer_exponent(DIRICHLET_P) - 2.0) < 1e-12,
            "value": transfer_exponent(DIRICHLET_P),
        },
    ]


def survivor_band() -> list[dict[str, Any]]:
    """Where the finance survivors sit, in both readings.

    `exponent` is Paper A's `log L / log n_max` (the `0.59` of Section 6.2);
    `n_max_over_L2_over_log` is `n_max log n_max / L^2`, which is the honest
    variable: it is `q_next / q` up to the flat `0.45`, not a power of `L`.
    The last column checks that every survivor stays far inside the Wu-Wang
    allowance, i.e. that this sharpening kills nothing.
    """
    out = []
    for row in survivor_exponent():
        L, n = row["L"], row["n_max"]
        ln = math.log(n)
        out.append(
            {
                "L": L,
                "n_max": n,
                "paper_a_exponent": row["exponent"],
                "n_max_logn_over_L2": n * ln / L**2,
                "wuwang_allowance": L ** transfer_exponent(WUWANG_P),
                "inside_wuwang_allowance": n * ln < L ** transfer_exponent(WUWANG_P),
            }
        )
    return out


def quotient_cap_consistency(qmax: int = 10**6) -> list[dict[str, Any]]:
    """Certified convergents against the Wu-Wang cap `q_next <= C q^4.1163051`.

    Diagnostic at `C = 1`. A ratio far below one means the observed
    continued fraction is nowhere near the worst case the measure allows,
    which is why the cap cannot close the family leftover of Paper D.
    """
    conv = convergents()
    out = []
    for i, (p, q, _a) in enumerate(conv):
        if q < 10 or q > qmax or i + 1 >= len(conv):
            continue
        q_next = conv[i + 1][1]
        cap = float(q) ** transfer_exponent(WUWANG_P)
        out.append(
            {
                "q": q,
                "q_next": q_next,
                "cap": cap,
                "ratio": q_next / cap,
                "inside": q_next <= cap,
            }
        )
    return out


def closure_threshold() -> dict[str, Any]:
    """The reopen condition of `juggler_cycle_method_ceilings`, with its number."""
    return {
        "statement": (
            "a lower bound n log n > (2/C) L^(p+1) on cycle minima excludes "
            "every nontrivial cycle"
        ),
        "unconditional_exponent": transfer_exponent(WUWANG_P),
        "previous_exponent_rhin": transfer_exponent(RHIN_P),
        "hard_floor_exponent": transfer_exponent(DIRICHLET_P),
        "lean": "Problems.Juggler.no_cycleMin_of_gap_and_minimum",
        "proved_here": False,
        "no_cycle_of_any_length": False,
    }


def report() -> dict[str, Any]:
    band = survivor_band()
    caps = quotient_cap_consistency()
    return {
        "exponents": exponent_table(),
        "checks": wuwang_checks(),
        "survivor_band": band,
        "quotient_cap": caps,
        "closure_threshold": closure_threshold(),
        "all_checks_ok": all(row["ok"] for row in wuwang_checks()),
        "every_survivor_inside_allowance": all(r["inside_wuwang_allowance"] for r in band),
        "every_quotient_inside_cap": all(r["inside"] for r in caps),
        "max_quotient_cap_ratio": max(r["ratio"] for r in caps),
        "kills_nothing_new": True,
        "is_halt_theorem": False,
        "raises_descent_floor": False,
    }


def write_artifacts(payload: dict[str, Any] | None = None) -> dict[str, Any]:
    data = payload if payload is not None else report()
    DATA_DIR.mkdir(parents=True, exist_ok=True)
    (DATA_DIR / "wuwang_reduction.json").write_text(
        json.dumps(data, indent=2) + "\n", encoding="utf-8"
    )
    return data


def main() -> None:
    data = write_artifacts()
    print(
        "gap transfer: length exponent "
        f"{transfer_exponent(RHIN_P):.4f} (Rhin) -> "
        f"{transfer_exponent(WUWANG_P):.7f} (Wu-Wang); "
        f"period exponent in n {period_exponent(RHIN_P):.4f} -> "
        f"{period_exponent(WUWANG_P):.4f}"
    )
    print(
        "closure threshold: a minimum lower bound n >> L^"
        f"{transfer_exponent(WUWANG_P):.7f} excludes every nontrivial cycle "
        f"(hard floor L^{transfer_exponent(DIRICHLET_P):.0f}, Dirichlet)"
    )
    print(
        "kills nothing: every survivor inside the allowance "
        f"({data['every_survivor_inside_allowance']}), "
        f"max quotient/cap ratio {data['max_quotient_cap_ratio']:.3e}"
    )


if __name__ == "__main__":
    main()
