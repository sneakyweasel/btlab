"""Phase-0 direct estimates of ``M_{θ,q}`` / ``P_θ`` (Tao note §10, Paper C §9).

Not a third formulation of the frontier and not a new orbit census.  The
module records two identities already implicit in the note and one fair-coin
walk DP: the tilted walk-live mass of a long odd suffix.  Nothing here is a
proof of the hypotheses; the classification is whether either laboratory
route bounds them without becoming ``H(C,A)``, a killed Paper B sum, or a
bounded-depth statement (Tao note §10.4(e)).
"""

from __future__ import annotations

import json
import math
from pathlib import Path
from typing import Any

from research.juggler_sequence.cycle_finance import git_commit
from research.juggler_sequence.tao_reduction import (
    LOG2_3,
    N0_CERTIFIED,
    REQUIRED_RATE_STAR3,
    chernoff_biased_exponent,
    fair_tilted_live,
    fair_tilted_live_suffix_odd_mass,
    least_C_pressure,
    p_of_C,
    scale_L,
    theta_of_C,
)

DATA_DIR = Path(__file__).resolve().parents[3] / "data" / "research" / "juggler" / "pressure_direct"

Q_CRIT = 1.0 / LOG2_3  # log 2 / log 3
THETA_19 = theta_of_C(19)
RHO_19 = math.tanh(THETA_19 / 2.0)


def reset_worst_case_q(mu_k: float) -> float:
    """``s_θ ≤ 1/2 + μ_k/2`` if complementary cylinders split at 1/2 and the
    suffix-``O^{≥k}`` complement is allowed to split at 1."""

    return 0.5 + 0.5 * mu_k


def room_against_p_C(mu_k: float, C: int) -> dict[str, float | bool]:
    """Numerical room for the reset split at this ``C``: need ``q_star < p_C``."""

    q_star = reset_worst_case_q(mu_k)
    p = p_of_C(C)
    return {
        "mu_k": mu_k,
        "q_star": q_star,
        "p_C": p,
        "q_crit": Q_CRIT,
        "mu_k_budget_for_p_C": 2.0 * p - 1.0,
        "room_below_p_C": q_star < p,
        "room_below_q_crit": q_star < Q_CRIT,
    }


def iterate_word(n: int, length: int) -> tuple[list[int], int]:
    """Parity word of ``n, J(n), …, J^{length-1}(n)`` and the image ``J^{length}(n)``."""

    letters: list[int] = []
    x = n
    for _ in range(length):
        letters.append(x % 2)
        if x % 2 == 0:
            x = math.isqrt(x)
        else:
            x = math.isqrt(x * x * x)
    return letters, x


def cylinder_image_stats(y: int, word: tuple[int, ...]) -> dict[str, Any]:
    """Exact image of the start-cylinder ``[w] ∩ (y, 2y]``.

    Density is ``|#image| / (max − min + 1)``.  A filled interval has density 1;
    a high-walk word ending in ``E`` is sparse in its landing range.  Walk
    ``u = o log2 3 − t`` is a function of the word only.
    """

    images: list[int] = []
    for n in range(y + 1, 2 * y + 1):
        if n % 2 != word[0]:
            continue
        letters, xt = iterate_word(n, len(word))
        if tuple(letters) == word:
            images.append(xt)
    o = sum(word)
    t = len(word)
    row: dict[str, Any] = {
        "y": y,
        "word": "".join("O" if b else "E" for b in word),
        "ends_E": word[-1] == 0,
        "o": o,
        "t": t,
        "u": o * LOG2_3 - t,
        "members": len(images),
    }
    if not images:
        row.update(image_card=0, span=0, density=None, high_walk=row["u"] > 0)
        return row
    lo, hi = min(images), max(images)
    span = hi - lo + 1
    card = len(set(images))
    row.update(
        image_card=card,
        image_min=lo,
        image_max=hi,
        span=span,
        density=card / span,
        high_walk=row["u"] > 0,
    )
    return row


def walsh_generating_function_budget(d: int, theta: float, k0: int = 4) -> dict[str, float]:
    """Crude Walsh product at depth ``d``: ``ρ = tanh(θ/2)``.

    Fixed-order characters with ``|W_T| ≤ N`` cost ``e^{O(log d)} = e^{o(d)}``.
    The full generating function is ``(1+ρ)^d = e^{Θ(d)}`` unless the tail
    after order ``k0`` is cancelled — that tail is high-depth information.
    """

    rho = math.tanh(theta / 2.0)
    partial = 0.0
    binom = 1.0
    for k in range(k0 + 1):
        partial += binom * rho**k
        binom *= (d - k) / (k + 1)
    full = (1.0 + rho) ** d
    return {
        "d": float(d),
        "theta": theta,
        "rho": rho,
        "k0": float(k0),
        "partial_k0": partial,
        "full_1_plus_rho_pow_d": full,
        "log_partial": math.log(partial) if partial > 0 else float("-inf"),
        "log_full": d * math.log(1.0 + rho),
        "log_full_over_d": math.log(1.0 + rho),
        "tail_is_theta_d": True,
    }


def suffix_table(L: float, d: int, theta: float, C: int) -> dict[str, Any]:
    rows = {}
    for k in (2, 3, 4, 5):
        mu = fair_tilted_live_suffix_odd_mass(L, d, theta, k)
        rows[str(k)] = room_against_p_C(mu, C)
    return rows


def summary() -> dict[str, Any]:
    scales = []
    for exp10 in (12, 50, 100):
        log_y = exp10 * math.log(10.0)
        L = scale_L(log_y, N0_CERTIFIED)
        scale_row: dict[str, Any] = {"log10_y": exp10, "L": L}
        for C in (19, 41):
            d = math.ceil(C * L)
            theta = theta_of_C(C)
            scale_row[f"C{C}"] = {
                "d": d,
                "theta": theta,
                "p_C": p_of_C(C),
                "suffix": suffix_table(L, d, theta, C),
                "fair_tilted_live": fair_tilted_live(L, d, theta),
                "walsh": walsh_generating_function_budget(d, theta, k0=4),
            }
        scales.append(scale_row)

    # Geometry: contracted E-ending words fill a short landing interval; high-walk
    # E-ending words (odd share above 1/log2 3) are sparse in a long landing range.
    y = 10**5
    geometry = [
        cylinder_image_stats(y, (1, 0, 0)),  # OEE, u < 0, contracted fill
        cylinder_image_stats(y, (1, 0, 1, 0)),  # OEOE, u < 0
        cylinder_image_stats(y, (1, 1, 1, 0)),  # OOOE, u > 0, sparse
        cylinder_image_stats(y, (1, 1, 1, 1, 0)),  # OOOOE, u > 0, sparse
    ]
    high_walk_e = [g for g in geometry if g["ends_E"] and g["high_walk"] and g["members"] > 0]
    contracted_e = [g for g in geometry if g["ends_E"] and not g["high_walk"] and g["members"] > 0]
    high_walk_sparse = bool(high_walk_e) and all(
        g["density"] is not None and g["density"] < 0.05 for g in high_walk_e
    )
    contracted_dense = bool(contracted_e) and all(
        g["density"] is not None and g["density"] > 0.2 for g in contracted_e
    )

    # Room at the Tao depths: does any k=3,4 leave q_star < p_C?
    room_flags = {}
    for scale_row in scales:
        for C in (19, 41):
            block = scale_row[f"C{C}"]
            for k in ("3", "4"):
                room_flags[f"1e{scale_row['log10_y']}_C{C}_k{k}"] = block["suffix"][k]["room_below_p_C"]

    return {
        "git_commit": git_commit(),
        "N0": N0_CERTIFIED,
        "theta_19": THETA_19,
        "rho_19": RHO_19,
        "q_crit": Q_CRIT,
        "required_rate_star3": REQUIRED_RATE_STAR3,
        "least_C_pressure_at_q_star_examples": {
            "q_0.56": least_C_pressure(0.56, REQUIRED_RATE_STAR3),
            "q_0.60": least_C_pressure(0.60, REQUIRED_RATE_STAR3),
        },
        "chernoff_biased_at_C19": {
            "q_0.50": chernoff_biased_exponent(19, 0.5),
            "q_0.56": chernoff_biased_exponent(19, 0.56),
        },
        "scales": scales,
        "geometry": geometry,
        "classification": {
            "reset_high_walk_image_is_sparse": high_walk_sparse,
            "reset_contracted_image_can_fill": contracted_dense,
            "reset_is_H_q_at_unbounded_depth": True,
            "S_sampling_is_S_fairness": True,
            "walsh_fixed_order_is_e_o_d": True,
            "walsh_tail_is_e_theta_d": True,
            "walsh_two_sided_is_H_reparam": True,
            "paper_B_on_max_T_le_4_is_10_4_e": True,
            "decision": "CLOSE",
        },
        "room_below_p_C": room_flags,
    }


def main() -> None:
    result = summary()
    DATA_DIR.mkdir(parents=True, exist_ok=True)
    out = DATA_DIR / "summary.json"
    out.write_text(json.dumps(result, indent=2), encoding="utf-8")
    print(json.dumps(result, indent=2))
    print(out)


if __name__ == "__main__":
    main()
