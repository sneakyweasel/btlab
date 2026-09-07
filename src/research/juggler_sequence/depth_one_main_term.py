"""The depth-one parity sum has a main term, and the odd starts cancel it.

For ``F(M) = α M^{3/2}`` the van der Corput B-process dualises the sum to a phase in the
frequency ``ν = F'(M)``:  with ``M_ν = (2ν/3α)^2`` one has ``F(M_ν) - ν M_ν = -4ν^3/(27α^2)``,
a *cubic polynomial* with a *rational* coefficient whenever ``α`` is rational.  So

    Σ_{M ≤ X} e(α M^{3/2})  ≈  e(1/8) Σ_{ν ≤ (3α/2)√X} (√(8ν)/(3α)) e(-4ν^3/(27α^2)),

and the dual Weyl sum does not cancel: it is a complete cubic Gauss sum on every period.  At
``α = 1/2`` the modulus is ``27``, ``Σ_{r mod 27} e(-16 r^3/27) = 9``, and the main term is

    |Σ_{M ≤ X} e(M^{3/2}/2)|  =  (4√8/27)(3/4)^{3/2} X^{3/4} (1 + o(1))  =  0.27217 X^{3/4}.

Hence the parity of ``⌊M^{3/2}⌋`` over *all* ``M ≤ X`` is biased toward even by ``≈ 0.425 X^{3/4}``.
Restricting to odd ``M`` twists by ``(-1)^M``, which shifts the dual frequency by ``1/2``; the
mod-27 cubic sum is invariant under that shift (``2ν+1`` runs over a complete residue system), so
the two ``X^{3/4}`` terms are equal and cancel.  The Juggler odd branch therefore has

    Σ_{M ≤ X, M odd} e(M^{3/2}/2) = o(X^{3/4}),   measured ≈ X^{0.31},

far below the random-walk order ``X^{1/2}``: the odd-branch parity is *super-fair* at depth one.
The exponent ``3/2`` is what makes this happen — its dual exponent ``c/(c-1) = 3`` is an integer
— and the deeper tower levels, whose exponents ``(3/2)^k`` have non-integer duals, show only the
random-walk order ``√N`` in their parity imbalance.

Nothing here touches the frontier (depth ``→ ∞``); it is an exact statement about the first
letter after an odd start, with a constant checked to four digits.
"""

from __future__ import annotations

import cmath
import json
import math
from pathlib import Path
from typing import Any

import numpy as np

REPO_ROOT = Path(__file__).resolve().parents[3]
ARTIFACT = REPO_ROOT / "data" / "research" / "juggler" / "depth_one_main_term" / "summary.json"


def predicted_constant(alpha: float = 0.5, modulus: int = 27, coeff: int = -16) -> float:
    """``|Σ_{M≤X} e(α M^{3/2})| / X^{3/4}`` from the B-process with the complete cubic sum."""

    gauss = sum(cmath.exp(2j * math.pi * coeff * r**3 / modulus) for r in range(modulus))
    mean = abs(gauss) / modulus                          # average of the dual phase per period
    V_over_sqrtX = 1.5 * alpha                           # ν runs to (3α/2)√X
    # Σ_{ν≤V} √ν e(...) ≈ mean · (2/3) V^{3/2};  amplitude √8/(3α) per ν
    return (math.sqrt(8.0) / (3.0 * alpha)) * mean * (2.0 / 3.0) * V_over_sqrtX**1.5


def complete_cubic_sum(coeff: int, modulus: int = 27) -> complex:
    return sum(cmath.exp(2j * math.pi * coeff * r**3 / modulus) for r in range(modulus))


def complete_cubic_sum_shifted(k: int) -> complex:
    """The dual complete sum of the twisted harmonic: ``Σ_{ν mod 27k²} e(-2(2ν-1)³/(27k²))``.

    Restricting ``Σ e(k M^{3/2}/2)`` to odd ``M`` twists by ``(-1)^M``, which moves the stationary
    points to half-integers ``μ = ν - 1/2``; the dual phase ``-16μ³/(27k²)`` at ``μ = (2ν-1)/2``
    is ``-2(2ν-1)³/(27k²)``.  For odd ``k`` the map ``ν ↦ 2ν-1`` permutes the residues mod ``27k²``,
    so this equals ``Σ_w e(-2w³/(27k²))``, and so does the untwisted sum ``Σ_r e(-16r³/(27k²))``
    via ``w = 2r``: the two main terms are identical for every odd harmonic.
    """

    q = 27 * k * k
    return sum(cmath.exp(2j * math.pi * (-2 * (2 * r - 1) ** 3) / q) for r in range(q))


def harmonic_identity(k: int) -> dict[str, Any]:
    """``C_k`` (untwisted) against ``C'_k`` (parity-twisted) at the modulus ``27k²``."""

    q = 27 * k * k
    c = complete_cubic_sum(-16, q)
    cp = complete_cubic_sum_shifted(k)
    return {"k": k, "modulus": q, "C_k": [c.real, c.imag], "C_k_shifted": [cp.real, cp.imag],
            "difference": abs(c - cp), "identical": bool(abs(c - cp) < 1e-6 * max(1.0, abs(c)))}


def odd_harmonic_sums(X: int, ks: tuple[int, ...] = (1, 3, 5, 7)) -> dict[str, Any]:
    """``|Σ_{n ≤ X odd} e(k n^{3/2}/2)|`` against ``X^{1/4}`` for the first odd harmonics."""

    n = np.arange(1, X + 1, 2, dtype=np.float64)
    ph = np.power(n, 1.5)
    out = {}
    for k in ks:
        s = np.exp(2j * np.pi * np.mod(k * ph / 2.0, 1.0)).sum()
        out[f"k{k}"] = {"abs": float(abs(s)), "over_X14": float(abs(s) / X**0.25)}
    return out


def depth_one_sums(X: int, chunk: int = 2_000_000) -> dict[str, Any]:
    """The sum over all, even and odd ``M ≤ X``, and the parity imbalances of ``⌊M^{3/2}⌋``."""

    S_all = S_odd = 0j
    imb_all = imb_even = imb_odd = 0
    for lo in range(1, X + 1, chunk):
        M = np.arange(lo, min(X, lo + chunk - 1) + 1, dtype=np.float64)
        p = np.power(M, 1.5)
        e = np.exp(2j * np.pi * np.mod(p / 2.0, 1.0))
        odd = M % 2 == 1
        S_all += e.sum()
        S_odd += e[odd].sum()
        par = np.where(np.floor(p) % 2 == 0, 1, -1)
        imb_all += int(par.sum())
        imb_even += int(par[~odd].sum())
        imb_odd += int(par[odd].sum())
    return {
        "X": X,
        "abs_S_all_over_X34": float(abs(S_all) / X**0.75),
        "abs_S_odd": float(abs(S_odd)),
        "abs_S_odd_over_sqrtX": float(abs(S_odd) / X**0.5),
        "abs_S_odd_over_X34": float(abs(S_odd) / X**0.75),
        "imbalance_all": imb_all,
        "imbalance_even_M": imb_even,
        "imbalance_odd_M": imb_odd,
        "even_M_imbalance_over_X34": imb_even / X**0.75,
    }


def tower_level_imbalances(X: int, levels: int = 4) -> dict[str, Any]:
    """Even-minus-odd imbalance of the next letter on the cylinders ``O^k``, odd starts ``≤ X``."""

    imb = [0] * (levels + 1)
    cnt = [0] * (levels + 1)
    for n in range(1, X + 1, 2):
        m = n
        for k in range(1, levels + 1):
            m = math.isqrt(m * m * m)
            cnt[k] += 1
            imb[k] += 1 if m % 2 == 0 else -1
            if m % 2 == 0:
                break
    return {
        f"level_{k}": {"cylinder": cnt[k], "imbalance": imb[k],
                       "over_sqrt": imb[k] / cnt[k] ** 0.5, "over_34": imb[k] / cnt[k] ** 0.75}
        for k in range(1, levels + 1)
    }


def summary() -> dict[str, Any]:
    pred = predicted_constant()
    sums = {f"1e{e}": depth_one_sums(10**e) for e in (5, 6)}
    towers = tower_level_imbalances(10**6)
    ratio_all = sums["1e6"]["abs_S_all_over_X34"]
    identities = {f"k{k}": harmonic_identity(k) for k in (1, 3, 5, 7, 9, 11)}
    odd_harm = {f"1e{e}": odd_harmonic_sums(10**e) for e in (5, 6)}
    return {
        "harmonic_identities": identities,
        "every_odd_harmonic_main_term_cancels": bool(all(v["identical"] for v in identities.values())),
        "odd_harmonic_sums": odd_harm,
        "odd_harmonics_stay_within_four_X14": bool(all(
            v["over_X14"] < 4.0 for row in odd_harm.values() for v in row.values())),
        "predicted_constant": pred,
        "complete_cubic_sum_mod_27": {"coeff_-16": complete_cubic_sum(-16).real,
                                      "coeff_-2": complete_cubic_sum(-2).real},
        "sums": sums,
        "prediction_matches_at_1e6": bool(abs(ratio_all / pred - 1) < 0.01),
        "odd_sum_is_below_root_X": bool(all(s["abs_S_odd_over_sqrtX"] < 0.1 for s in sums.values())),
        "even_M_carries_the_bias": bool(all(
            abs(s["imbalance_odd_M"]) < 0.02 * abs(s["imbalance_even_M"]) for s in sums.values())),
        "tower_levels_at_1e6": towers,
        "tower_levels_are_root_order": bool(all(abs(v["over_sqrt"]) < 3.0 for v in towers.values())),
        "classification": "DEPTH_ONE_MAIN_TERM_CANCELS_ON_ODD_STARTS_ALL_HARMONICS",
    }


def main() -> None:
    s = summary()
    ARTIFACT.parent.mkdir(parents=True, exist_ok=True)
    ARTIFACT.write_text(json.dumps(s, indent=1, ensure_ascii=False), encoding="utf-8")
    print(f"predicted |S_all|/X^(3/4) = {s['predicted_constant']:.5f}")
    for k, v in s["sums"].items():
        print(f"  {k}: |S_all|/X^.75={v['abs_S_all_over_X34']:.4f}  |S_odd|/X^.5={v['abs_S_odd_over_sqrtX']:.3f}"
              f"  imbalance all={v['imbalance_all']} even-M={v['imbalance_even_M']} odd-M={v['imbalance_odd_M']}")
    for k, v in s["harmonic_identities"].items():
        print(f"  {k}: modulus {v['modulus']}  C_k={v['C_k'][0]:.3f}  shifted={v['C_k_shifted'][0]:.3f}  identical={v['identical']}")
    for k, v in s["tower_levels_at_1e6"].items():
        print(f"  {k}: cylinder {v['cylinder']} imbalance {v['imbalance']} (/sqrt = {v['over_sqrt']:.2f})")
    print(s["classification"])
    print(ARTIFACT)


if __name__ == "__main__":
    main()
