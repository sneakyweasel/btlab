"""Exact-fraction exponent ledger for the depth-five critical path (0.74 route).

Each lemma on the path claims a bound ``|T_d| << P^c`` or a tail exponent. Its
proof lists costs ``P^(e_j)``. This ledger records every listed cost as an exact
``Fraction`` at the worst admissible shift, ``d = P^(1/48)``, and checks
mechanically that ``max_j e_j <= c`` and ``c < 1``. It also recomputes the
derived exponents (tail exponents, coefficient margins) from their inputs. It
checks bookkeeping, not analysis: an omitted cost stays omitted. Sources are the
depth-five dossier's Results 14 (E5), 16 and 23 (E6', E9), 19-21 (E7) and 20
(E8'), and Paper B's printed Appendix C.9 and C.2. Logarithmic factors are
ignored.
"""

from __future__ import annotations

import json
from fractions import Fraction as F
from pathlib import Path

from research.experiments.outputs import artifact_path
from research.experiments.provenance import write_manifest
from research.juggler_sequence.lean_paths import DATA_ROOT

DATA_DIR = DATA_ROOT / "depth_five_production" / "critical_path_ledger"
DELTA = F(1, 48)          # sub-block exponent: shifts d < P^DELTA
T_CUT = F(1, 8)           # Fourier cutoff exponents used by E5 and E7

#: (claim, claimed exponent, [(cost label, exponent)]) with d = P^DELTA.
BOUNDS = [
    ("OOOEE k != 0: Paper B C.9 T_1(h_1)", F(63, 64), [
        ("P^2/H_2 inside the square root", (2 - F(1, 24)) / 2),
        ("double correlation P^(31/32) inside the square root", (1 + F(31, 32)) / 2)]),
    ("OOOEE k = 0, j != 0: Paper B C.2 at h = d", F(7, 8) + DELTA / 2, [
        ("P^(7/8)(1 + sqrt h)", F(7, 8) + DELTA / 2)]),
    ("OOOEE k = 0, j = 0, l != 0: E5", F(7, 8), [
        ("positive Fourier errors P log T / T", 1 - T_CUT),
        ("off-diagonal T^(1/2) P^(3/4)", T_CUT / 2 + F(3, 4)),
        ("off-diagonal endpoints P^(3/16) P^(1/4)", F(3, 16) + F(1, 4)),
        ("diagonal lengths d^(1/2) P^(11/32)", DELTA / 2 + F(11, 32)),
        ("diagonal endpoints P^(3/16) d^(-1/2) P^(21/32)", F(3, 16) + F(21, 32)),
        ("(C.6) replacement |l| P^(7/16)", F(7, 16))]),
    ("OOOEE k = 0, j = 0, l != 0: E5 with cutoff P^(1/16) (Result 34)", F(15, 16), [
        ("positive Fourier errors P log T / T", 1 - F(1, 16)),
        ("off-diagonal T^(1/2) P^(3/4)", F(1, 32) + F(3, 4)),
        ("off-diagonal endpoints P^(3/16) P^(1/4)", F(3, 16) + F(1, 4)),
        ("diagonal lengths d^(1/2) P^(11/32)", DELTA / 2 + F(11, 32)),
        ("diagonal endpoints P^(3/16) d^(-1/2) P^(21/32)", F(3, 16) + F(21, 32)),
        ("(C.6) replacement |l| P^(7/16)", F(7, 16))]),
    ("OOOEE k = l = j = 0: Kusmin-Landau", F(1, 2), [("P^(1/2)/d", F(1, 2))]),
    ("OOEOE j = 0, k != 0: E7", F(7, 8), [
        ("zero-mode lengths P^(11/32) d^(1/2)", F(11, 32) + DELTA / 2),
        ("zero-mode endpoints d^(1/2) P^(25/32)", DELTA / 2 + F(25, 32)),
        ("carry modes R_U^(1/2) P^(9/16)", T_CUT / 2 + F(9, 16)),
        ("carry-mode endpoints d P^(1/8) P^(7/16)", DELTA + F(1, 8) + F(7, 16)),
        ("U truncation P log R_U / R_U + P^(7/8)", F(7, 8)),
        ("carry mismatches P^(7/8)", F(7, 8)),
        ("theta-noise in U-modes", F(3, 4)),
        ("B(n+2d) -> B(n) replacement d P^(9/16)", DELTA + F(9, 16)),
        ("Taylor step (4.18) k P^(7/16), incl. B times the nu remainder", F(7, 16)),
        ("l-noise P^(5/8)", F(5, 8)),
        ("theta-cancellation residual d P^(3/16)", DELTA + F(3, 16))]),
    ("OOEOE j != 0: E7 (Lemma 4.4 rerun, U-cutoff P^(1/16))", F(15, 16), [
        ("P^(7/8) d^(1/2)", F(7, 8) + DELTA / 2),
        ("d P^(3/4)", DELTA + F(3, 4)),
        ("P^(5/6)", F(5, 6)),
        ("U truncation at P^(1/16)", 1 - F(1, 16))]),
    ("OOEOE k = 0: E7 (E1 at small shift, or Kusmin-Landau)", F(7, 8) + DELTA / 2, [
        ("Lemma 4.4 P^(7/8) d^(1/2)", F(7, 8) + DELTA / 2),
        ("Kusmin-Landau P^(7/8)/d", F(7, 8)),
        ("l-noise P^(5/8)", F(5, 8))]),
]


def check_bounds() -> list[dict]:
    rows = []
    for claim, c, costs in BOUNDS:
        worst = max(e for _, e in costs)
        rows.append({"claim": claim, "claimed": str(c), "worst_cost": str(worst),
                     "worst_label": max(costs, key=lambda t: t[1])[0],
                     "ok": worst <= c < 1, "saving": str(1 - c)})
    return rows


def derived() -> dict:
    """Recompute the tail exponents and the coefficient margin from their inputs."""
    sigma = {name: 1 - F(c) for name, c in
             ((r["claim"], r["claimed"]) for r in check_bounds())}
    ooee = min(v for k, v in sigma.items() if k.startswith("OOOEE"))
    ooeoe = min(v for k, v in sigma.items() if k.startswith("OOEOE"))
    rho_inv = F(32, 27)
    eta = F(1, 1000)  # FateDepthFiveWeighted.eta, the kernel-checked choice
    return {
        "sigma_OOOEE": str(ooee), "sigma_OOEOE": str(ooeoe),
        "poor_fraction_OOOEE": str(min(DELTA, ooee)),
        "poor_fraction_OOEOE": str(min(DELTA, ooeoe)),
        "tail_exponent_OOOEE": str(rho_inv * min(DELTA, ooee)),
        "tail_exponent_OOEOE": str(rho_inv * min(DELTA, ooeoe)),
        "tail_claims_ok": rho_inv * min(DELTA, ooee) > F(1, 55)
                          and rho_inv * min(DELTA, ooeoe) > F(1, 41),
        "coefficient_margin": str((1 - 16 * eta) * F(28, 27)),
        "coefficient_ok": (1 - 16 * eta) * F(28, 27) > 1,
        "assembly_loss_margin": str(8 * (F(33, 100) + F(11, 100) + F(1, 14))),
        "assembly_loss_ok": 8 * (F(33, 100) + F(11, 100) + F(1, 14)) >= 4,
    }


def table() -> dict:
    return {"delta": str(DELTA), "bounds": check_bounds(), "derived": derived()}


def run(output_root: Path | None = None) -> Path:
    out_dir = artifact_path(DATA_DIR, output_root)
    out_dir.mkdir(parents=True, exist_ok=True)
    out = out_dir / "ledger.json"
    out.write_text(json.dumps(table(), indent=1) + "\n", encoding="utf-8", newline="\n")
    return write_manifest(
        out_dir / "run.research.json", programme="juggler",
        research_id="juggler/depth_five_production",
        scope="exponent bookkeeping of the depth-five 0.74 critical path at d = P^(1/48)",
        parameters={"delta": str(DELTA), "cutoff": str(T_CUT)},
        outputs=[out], sources=[Path(__file__)],
    )


if __name__ == "__main__":
    print(run())
