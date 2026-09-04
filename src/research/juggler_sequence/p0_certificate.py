"""Effective threshold certificate for Paper B (docs/theory/juggler_parity_discrepancy_note.md).

Every numerical margin in Sections 4-6 is claimed for ``P >= P_0``.  This module transcribes each
such printed inequality as a predicate in ``P``, solves it for the least ``P`` beyond which it holds
(bisection on ``log10 P``; each predicate is monotone in ``P`` over the stated search range), and
reports the maximum.  That maximum is ``P_0``.

Two things the certificate is *not*.  It is not a proof: it certifies that the inequalities the
paper prints are true beyond the stated threshold, not that they are the right inequalities.  And it
is not a statement about ``epsilon``: no divisor sum, gcd sum or large-sieve average occurs anywhere
in Sections 3-6, so every ``<<_epsilon`` there is a power of ``log P``, and the threshold at which
``log^A P`` is absorbed into ``P^epsilon`` is a fact about ``epsilon`` rather than about the proof.
``log_absorption_thresholds`` computes those separately and they are excluded from ``P_0``.

Run ``python -m research.juggler_sequence.p0_certificate``.
"""

from __future__ import annotations

import math
from typing import Any, Callable

# Lemma 3.9 curvature constant: 1 / ||M^{-1}||_inf for the Vandermonde-type matrix at the Step 5b
# exponent triple.  Exact value proved in formal/Problems/Juggler/MonomialSplitting.lean
# (`step5b_curvature_norm`); 1/288 is the value printed in an earlier draft.
C7 = 1.0 / 232.0
C7_SUPERSEDED = 1.0 / 288.0
RHO0 = C7 / 8.0

# Normalisation of the balanced sublevel parameter V = KAPPA * S^(1/2) * P^(-11/24).
KAPPA = 1.0 / 3.0
KAPPA_SUPERSEDED = 3.0

# Lemma 5.2b interpolant majorant |f'' - Lambda| <= 219 P^(-25/24) + 0.11 P^(-5/6).
def interpolant_error(P: float) -> float:
    return 219.0 * P ** (-25 / 24) + 0.11 * P ** (-5 / 6)


def least_P(pred: Callable[[float], bool], lo: float = 0.0, hi: float = 300.0, iters: int = 400) -> float | None:
    """Least ``log10 P`` in ``[lo, hi]`` beyond which ``pred`` holds, or ``None`` if never.

    Deterministic bisection rather than a root solve: the predicates are booleans built from the
    printed inequalities, several of which compare sums of powers and have no closed-form crossing.
    """
    if pred(10.0**lo):
        return lo
    if not pred(10.0**hi):
        return None
    a, b = lo, hi
    for _ in range(iters):
        mid = (a + b) / 2
        if pred(10.0**mid):
            b = mid
        else:
            a = mid
    return b


def _V(S: float, P: float, kappa: float = KAPPA) -> float:
    return kappa * S**0.5 * P ** (-11 / 24)


def thresholds(kappa: float = KAPPA, c7: float = C7) -> list[dict[str, Any]]:
    """Every printed threshold inequality of Sections 4-6, with its least admissible P."""
    rho0 = c7 / 8.0
    S5b = lambda P: 0.35 * P**-0.625  # noqa: E731  middle band, worst standing cell k h1 h2 = 1
    S5a = lambda P: 0.60 * P**-0.625  # noqa: E731  offset composite

    rows: list[tuple[str, str, str, Callable[[float], bool]]] = [
        # --- Theorem 4.1, the theta-sawtooth and the collision band ---
        ("s3s1-window", "Thm 4.1 St.3(s1)", "P^(1/2) >= 8(1+|B|) with |B| < 1/2",
         lambda P: P**0.5 >= 12),
        ("s3s1-Bsmall", "Thm 4.1 St.3(s1)", "2.25 P^(-1/16) < 1/2",
         lambda P: 2.25 * P ** (-1 / 16) < 0.5),
        ("s3s2-window", "Thm 4.1 St.3(s2)", "P^(1/2) >= 8(1 + 2.25 P^(1/4))",
         lambda P: P**0.5 >= 8 * (1 + 2.25 * P**0.25)),
        ("s3s2-flat", "Thm 4.1 St.3(s2)", "8(1+2.25P^(1/4))P^(1/2) <= 19 P^(3/4)",
         lambda P: 8 * (1 + 2.25 * P**0.25) * P**0.5 <= 19 * P**0.75),
        ("s3s2-wincount", "Thm 4.1 St.3(s2)", "0.6 P^(1/4) + 1 <= 0.65 P^(1/4)",
         lambda P: 0.6 * P**0.25 + 1 <= 0.65 * P**0.25),
        ("s3s2-bdry", "Thm 4.1 St.3(s2)", "window boundaries <= 1.1 P^(17/32) <= P^(5/8)",
         lambda P: (0.6 * P**0.25 + 1) * (0.35 * P ** (3 / 16)) ** -0.5 * P**0.375
         <= 1.1 * P ** (17 / 32) and 1.1 * P ** (17 / 32) <= P**0.625),
        ("stage2-modecurv", "Thm 4.1 St.2", "mode/cell curvature ratio 0.39 P^(1/8) >= 4",
         lambda P: 0.39 * P**0.125 >= 4),
        ("stage5-band", "Thm 4.1 St.5", "4.5 - 1.5/(h P^(1/2)) >= 4.4 at h = 1",
         lambda P: 4.5 - 1.5 / P**0.5 >= 4.4),
        # --- Theorem 4.4, Claims C and G ---
        ("claimC-1", "Claim C", "P^(7/72) >= 3",
         lambda P: P ** (7 / 72) >= 3),
        ("claimC-2", "Claim C", "41 P^(5/36) <= P^(1/2)",
         lambda P: 41 * P ** (5 / 36) <= P**0.5),
        ("claimG-pref", "Claim G", "96 P^(-5/24) <= 1",
         lambda P: 96 * P ** (-5 / 24) <= 1),
        ("claimG-P36", "Claim G", "P^(1/72-1/24) <= 1",
         lambda P: P ** (-1 / 36) <= 1),
        # --- Theorem 5.3, window hypotheses ---
        ("st3a-window", "Thm 5.3 St.3(a)", "P^(1/2)/(2h1) >= 8(1+|B|): 0.5 P^(23/48) >= 15 P^(10/48)",
         lambda P: 0.5 * P ** (23 / 48) >= 15 * P ** (10 / 48)),
        ("st3b-window", "Thm 5.3 St.3(b)", "P^(1/2)/(2h2) >= 8(1+|B|): 0.5 P^(22/48) >= 15 P^(9/48)",
         lambda P: 0.5 * P ** (22 / 48) >= 15 * P ** (9 / 48)),
        ("st3a-flat", "Thm 5.3 St.3(a)", "16 h1 P^(1/2) + 30 k h1 h2 P^(5/8) <= 46 P^(3/4)",
         lambda P: 16 * P ** (1 / 48 + 0.5) + 30 * P**0.75 <= 46 * P**0.75),
        ("st6D1-window", "Thm 5.3 St.6(D1)", "P^(1/2) >= 8(1 + 7 P^(1/4))",
         lambda P: P**0.5 >= 8 * (1 + 7 * P**0.25)),
        ("st6D1-good", "Thm 5.3 St.6(D1)", "72 t^(-1) P^(-1/2) <= 1/4 at t = 1",
         lambda P: 72 * P**-0.5 <= 0.25),
        ("5b-j0-window", "Thm 5.3 St.5b (j=0)", "P^(1/2) >= 8(1+6) = 56",
         lambda P: P**0.5 >= 56),
        # --- Theorem 5.3, Step 5b geometry ---
        ("5b-Npieces", "Thm 5.3 St.5b", "cells + anchor runs + windows <= 3.5 P^(13/24)",
         lambda P: 3 * P ** (1 / 24 + 0.5) + 2 + 22 * P ** (1 / 16 + 0.25) + 5 * P ** (1 / 3)
         <= 3.5 * P ** (13 / 24)),
        ("5b-lam0-range", "Lemma 5.2b", "[0.38,2.44] with its corrections inside [0.35,2.6]",
         lambda P: 2.44 * (1 + P**-0.25) * (1 + 1 / (3 * P**0.5)) ** 2 <= 2.6
         and 0.38 * (1 - P**-0.25) * (1 - 1 / (3 * P**0.5)) ** 2 >= 0.35),
        # --- Theorem 5.3, Lemma 3.9 perturbation hypothesis rho <= rho_0 ---
        ("39-c2", "Thm 5.3 St.5b", "|c''/2|/S <= rho_0: (0.053/0.35) P^(-1/4)",
         lambda P: (0.053 / 0.35) * P**-0.25 <= rho0),
        ("39-c3", "Thm 5.3 St.5b", "P|c'''/2|/S <= rho_0: (0.047/0.35) P^(-1/4)",
         lambda P: (0.047 / 0.35) * P**-0.25 <= rho0),
        ("39-c4", "Thm 5.3 St.5b", "P^2|c''''/2|/S <= rho_0: (0.044/0.35) P^(-1/4)",
         lambda P: (0.044 / 0.35) * P**-0.25 <= rho0),
        ("39-beta", "Thm 5.3 St.5b", "beta-substitution error 2.31 P^(-1/2) <= rho_0",
         lambda P: (1.187 * 0.68 / 0.35) * P**-0.5 <= rho0),
        ("39-wave", "Thm 5.3 St.5b", "wave remainder 200 P^(-35/24) vs S: 571 P^(-5/6) <= rho_0",
         lambda P: (200 / 0.35) * P ** (-5 / 6) <= rho0),
        # --- Theorem 5.3, the two Lemma 3.9 balance comparisons ---
        ("5a-competitors", "Thm 5.3 St.5a", "every competitor ratio <= 1/4 (margin 4)",
         lambda P: max(1.3 * P**-0.125, 13 * P ** (-9 / 16), 9 * P ** (-13 / 12), 3 * P**-0.125) <= 0.25),
        ("5a-V>=10err", "Thm 5.3 St.5a", "V >= 10 |f'' - Lambda|",
         lambda P: _V(S5a(P), P, kappa) >= 10 * interpolant_error(P)),
        ("5a-V<=c7S", "Thm 5.3 St.5a", "V <= c_7 S/2 at S >= 0.60 P^(-5/8)",
         lambda P: _V(S5a(P), P, kappa) <= c7 * S5a(P) / 2),
        ("5b-V>=10err", "Thm 5.3 St.5b", "V >= 10 |f'' - Lambda|",
         lambda P: _V(S5b(P), P, kappa) >= 10 * interpolant_error(P)),
        ("5b-V<=c7S", "Thm 5.3 St.5b", "V <= c_7 S/2 at S >= 0.35 P^(-5/8)",
         lambda P: _V(S5b(P), P, kappa) <= c7 * S5b(P) / 2),
        # --- Section 6 ---
        ("thm63-rem", "Thm 6.3", "linearization remainder P^(43/96) <= P^(1-1/96)",
         lambda P: P ** (43 / 96) <= P ** (1 - 1 / 96)),
    ]
    out = []
    for tag, site, claim, pred in rows:
        lg = least_P(pred)
        out.append({"tag": tag, "site": site, "claim": claim, "log10_P_min": lg,
                    "P_min": None if lg is None else 10.0**lg})
    return out


def kappa_tradeoff(kappa: float, c7: float = C7, S_lo: float = 0.35, N: float = 3.5) -> dict[str, Any]:
    """Threshold and P^(89/96) coefficient as functions of the normalisation of V.

    The transition cost carries ``kappa^(1/2)`` and the piece-boundary cost ``kappa^(-1/2)``, so the
    coefficient is minimised near ``kappa = 3.69`` while the threshold falls monotonically as
    ``kappa`` decreases until the two Lemma 3.9 comparisons collide.
    """
    S = lambda P: S_lo * P**-0.625  # noqa: E731
    lg = least_P(lambda P: _V(S(P), P, kappa) <= c7 * S(P) / 2
                 and _V(S(P), P, kappa) >= 10 * interpolant_error(P))
    transition = (kappa * S_lo**-0.5) ** 0.5
    boundaries = N * (0.9 * kappa * S_lo**0.5) ** -0.5
    return {"kappa": kappa, "log10_P_min": lg, "P_min": None if lg is None else 10.0**lg,
            "coeff_transition": transition, "coeff_boundaries": boundaries,
            "coeff_total": transition + boundaries}


def log_absorption_thresholds() -> list[dict[str, Any]]:
    """When ``C (log P)^A <= P^delta`` first holds.  Diagnostic: NOT part of ``P_0``.

    These are the thresholds one would need if the epsilon in ``P^(...+epsilon)`` were to be spent
    on the log powers rather than carried.  Sections 4-6 carry it, so none of these is required.
    """
    out = []
    for name, A, delta, C in (("Step 5b: C log P <= P^(1/96)", 1.0, 1 / 96, 1.0),
                              ("Thm 5.3: log^(3/4) P <= P^(1/96)", 0.75, 1 / 96, 1.0),
                              ("Thm 6.3: log^(15/4) P <= P^(1/96)", 3.75, 1 / 96, 1.0)):
        lg = least_P(lambda P, A=A, d=delta, C=C: C * math.log(P) ** A <= P**d, lo=1.0)
        out.append({"comparison": name, "log_power": A, "delta": delta,
                    "log10_P_min": lg, "P_min": None if lg is None else 10.0**lg})
    return out


def certificate() -> dict[str, Any]:
    rows = thresholds()
    solved = [r for r in rows if r["log10_P_min"] is not None]
    binding = max(solved, key=lambda r: r["log10_P_min"])
    balance = {"5a-V<=c7S", "5b-V<=c7S", "5a-V>=10err", "5b-V>=10err"}
    others = [r for r in solved if r["tag"] not in balance]
    without_balance = max(others, key=lambda r: r["log10_P_min"])
    superseded = thresholds(kappa=KAPPA_SUPERSEDED, c7=C7_SUPERSEDED)
    sup_binding = max((r for r in superseded if r["log10_P_min"] is not None),
                      key=lambda r: r["log10_P_min"])
    return {
        "kappa": KAPPA,
        "c7": C7,
        "thresholds": rows,
        "all_solved": len(solved) == len(rows),
        "n_thresholds": len(rows),
        "P0": binding["P_min"],
        "log10_P0": binding["log10_P_min"],
        "binding": binding,
        "P0_excluding_lemma_3_9_balance": without_balance["P_min"],
        "binding_excluding_balance": without_balance,
        "P0_at_superseded_kappa3_c7_288": sup_binding["P_min"],
        "kappa_tradeoff": [kappa_tradeoff(k) for k in (3.69, 3.0, 1.0, 0.5, 1 / 3, 0.312, 0.25)],
        "log_absorption_not_required": log_absorption_thresholds(),
    }


def markdown_table(rows: list[dict[str, Any]]) -> str:
    """The Appendix A table, generated so that the paper and the probe cannot drift apart."""
    lines = ["| threshold | site | least $P$ |", "|---|---|---|"]
    for r in sorted(rows, key=lambda r: (1e9 if r["log10_P_min"] is None else r["log10_P_min"])):
        p = r["P_min"]
        val = "always" if p is not None and p <= 1.0 else ("--" if p is None else "$%s$" % _sci(p))
        lines.append("| %s | %s | %s |" % (r["claim"].replace("|", "\\|"), r["site"], val))
    return "\n".join(lines)


def _sci(x: float) -> str:
    e = int(math.floor(math.log10(x)))
    m = x / 10.0**e
    return ("%.1f\\cdot10^{%d}" % (m, e)) if e >= 3 else ("%.0f" % x)


def main() -> None:
    c = certificate()
    print("Paper B effective threshold certificate")
    print("  kappa = %.4f   c_7 = 1/%.0f   %d thresholds, all solved: %s"
          % (c["kappa"], 1 / c["c7"], c["n_thresholds"], c["all_solved"]))
    print()
    for r in sorted(c["thresholds"], key=lambda r: (1e9 if r["log10_P_min"] is None else r["log10_P_min"])):
        print("  %-16s %-22s %10s  %s"
              % (r["tag"], r["site"],
                 "%.2f" % r["log10_P_min"] if r["log10_P_min"] is not None else "none",
                 r["claim"]))
    print()
    print("  P_0 = %.3e  (log10 = %.4f)" % (c["P0"], c["log10_P0"]))
    print("  binding: %s -- %s" % (c["binding"]["tag"], c["binding"]["claim"]))
    print("  excluding the Lemma 3.9 balance comparisons: %.3e (%s)"
          % (c["P0_excluding_lemma_3_9_balance"], c["binding_excluding_balance"]["tag"]))
    print("  at the superseded kappa=3, c_7=1/288:        %.3e" % c["P0_at_superseded_kappa3_c7_288"])
    print()
    print("  kappa trade-off (threshold against the P^(89/96) coefficient):")
    for t in c["kappa_tradeoff"]:
        print("    kappa=%.3f  P_min=%9s  coeff = %.2f + %.2f = %.2f"
              % (t["kappa"], "%.2e" % t["P_min"] if t["P_min"] else "-",
                 t["coeff_transition"], t["coeff_boundaries"], t["coeff_total"]))
    print()
    print("  log absorption (NOT part of P_0):")
    for t in c["log_absorption_not_required"]:
        print("    %-36s %s" % (t["comparison"], "%.2e" % t["P_min"] if t["P_min"] else "> 1e300"))


if __name__ == "__main__":
    main()
