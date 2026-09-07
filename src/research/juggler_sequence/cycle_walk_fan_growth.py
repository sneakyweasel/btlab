"""Wu-Wang transfer: polynomial cap on survivor-fan width.

Attack C of the post-fan-minimum Diophantine programme. Wu-Wang's
linear-independence measure for 1, log 2, log 3 implies

    a_{j+1} ≲ q_j^{3.1163051 + ε}

for the continued fraction of α = log 2 / log 3. Combined with the
already-proved fan geometry (width ~ a_{j+1}) this is a rigorous
growth law for survivor families. It does NOT give a_{j+1} = O(1)
and therefore does NOT prevent R_min → 1. The Baker/Rhin leftover-
killer slogan stays REFUTED; this branch never lower-bounds θ to
exclude a length.

Dossier: docs/problems/juggler_cycle_walk_fan_growth.md.
"""

from __future__ import annotations

from research.juggler_sequence.lean_paths import (
    DATA_ROOT,
)

import json
import math
from decimal import Decimal, localcontext
from fractions import Fraction
from pathlib import Path
from typing import Any

from research.juggler_sequence.cycle_finance import git_commit
from research.juggler_sequence.cycle_walk_competition import (
    X_HI_DEEP,
    X_LO_DEEP,
    _interval_cf,
)

DATA_DIR = (
    DATA_ROOT
    / "cycle_walk_fan_growth"
)
COMPETITION_SUMMARY = (
    DATA_DIR.parent / "cycle_walk_competition" / "summary.json"
)

# Wu, Qiang; Wang, Lihong, J. Number Theory 142 (2014) 264-273.
# |a + b log 2 + c log 3| ≥ H^{-4.1163051-ε}, H = max(|b|,|c|),
# hence μ(log 3) ≤ 5.1163051.
WU_WANG_NU = 4.1163051
WU_WANG_MU = 5.1163051
# Bondareva-Luchin-Salikhov, Chebyshevskii Sb. 19 (2018) 15-25.
# ν(1, ln 2, ln 3) ≤ 4.116201, μ(log 3) ≤ 5.116201. Same conclusion.
BLS_NU = 4.116201
BLS_MU = 5.116201

# CF algebra: |α - p/q| < 1/(a_{j+1} q^2) and
# |α - p/q| ≥ H^{-ν-ε} / (q log 3) with H = q for α < 1, so
# a_{j+1} < (log 3) q^{μ-2+ε} = (log 3) q^{3.1163051+ε}.
WW_EXPONENT = WU_WANG_MU - 2.0
BLS_EXPONENT = BLS_MU - 2.0
LN3 = math.log(3.0)

# Rhin / Simons-de Weger Lemma 12, already in the closed Baker branch:
# Λ > exp(-13.3 (0.46057 + log H)) = e^{-13.3*0.46057} H^{-13.3}.
RHIN_C = math.exp(-13.3 * 0.46057)
RHIN_POWER = 13.3

# High-precision observed continuation of α (NOT a big-int sandwich).
OBS_PREC = 80
OBS_MAX_TERMS = 48
OBS_Q_LIMIT = 10**24

CLASS_GREEN = "WALK_FAN_GROWTH_GREEN"
CLASS_CLOSED = "WALK_FAN_GROWTH_CLOSED"


def convergents_from_partial(partial: list[int]) -> list[tuple[int, int, int]]:
    """Return (index, p_j, q_j) for j ≥ 0, including a0.

    p_{-2}=0, p_{-1}=1; q_{-2}=1, q_{-1}=0.
    """

    p_m2, p_m1 = 0, 1
    q_m2, q_m1 = 1, 0
    out: list[tuple[int, int, int]] = []
    for j, a in enumerate(partial):
        p = a * p_m1 + p_m2
        q = a * q_m1 + q_m2
        out.append((j, p, q))
        p_m2, p_m1 = p_m1, p
        q_m2, q_m1 = q_m1, q
    return out


def quotient_rows(
    partial: list[int],
    certified_through: int,
    tag: str,
) -> list[dict[str, Any]]:
    """One row per next-quotient a_{j+1} sitting after convergent q_j."""

    conv = convergents_from_partial(partial)
    rows: list[dict[str, Any]] = []
    for j in range(len(partial) - 1):
        _, p_j, q_j = conv[j]
        a_next = partial[j + 1]
        if q_j <= 0:
            continue
        q_pow = q_j**WW_EXPONENT
        # Diagnostic ε = 0 envelope. Not a theorem at finite q
        # (Wu-Wang has an implicit H0(ε)); used only for consistency.
        ww_cap = LN3 * q_pow
        rhin_cap = (LN3 / RHIN_C) * (q_j ** (RHIN_POWER - 1.0))
        rows.append(
            {
                "cf": tag,
                "j": j,
                "p": p_j,
                "q": q_j,
                "a_next": a_next,
                "certified": j + 1 <= certified_through,
                "ww_cap_diagnostic": ww_cap,
                "a_over_ww_cap": a_next / ww_cap,
                "below_ww_diagnostic": a_next < ww_cap,
                "rhin_cap_diagnostic": rhin_cap,
                "a_over_rhin_cap": a_next / rhin_cap,
                "R_min_from_a": math.exp(4.0 / (a_next + 2.0)),
                "R_min_ww_floor": math.exp(4.0 / (ww_cap + 2.0)),
            }
        )
    return rows


def decimal_alpha_cf(
    max_terms: int = OBS_MAX_TERMS,
    q_limit: int = OBS_Q_LIMIT,
    prec: int = OBS_PREC,
) -> tuple[list[int], list[tuple[int, int]]]:
    """Uncertified CF of log 2 / log 3 from high-precision logs."""

    with localcontext() as ctx:
        ctx.prec = prec
        x = Decimal(2).ln() / Decimal(3).ln()
        partial: list[int] = []
        convergents: list[tuple[int, int]] = []
        p_m2, p_m1 = 0, 1
        q_m2, q_m1 = 1, 0
        for _ in range(max_terms):
            a = int(x)
            partial.append(a)
            p = a * p_m1 + p_m2
            q = a * q_m1 + q_m2
            convergents.append((p, q))
            if q > q_limit:
                break
            frac = x - Decimal(a)
            if frac == 0:
                break
            x = Decimal(1) / frac
            p_m2, p_m1 = p_m1, p
            q_m2, q_m1 = q_m1, q
    return partial, convergents


def certified_alpha_cf() -> dict[str, Any]:
    """Interval CF of every α in the deep competition sandwich."""

    lo = Fraction(*X_LO_DEEP)
    hi = Fraction(*X_HI_DEEP)
    partial, convergents = _interval_cf(lo, hi, q_limit=10**9)
    return {
        "partial_quotients": partial,
        "convergents": [[p, q] for p, q in convergents],
        "n_quotients": len(partial),
    }


def certified_theta_cf() -> dict[str, Any]:
    """Interval CF of θ_rot = 1 - α on the same sandwich."""

    lo = 1 - Fraction(*X_HI_DEEP)
    hi = 1 - Fraction(*X_LO_DEEP)
    partial, convergents = _interval_cf(lo, hi, q_limit=10**9)
    return {
        "partial_quotients": partial,
        "convergents": [[p, q] for p, q in convergents],
        "n_quotients": len(partial),
    }


def scale_table() -> list[dict[str, Any]]:
    """Wu-Wang-allowed (ε=0 diagnostic) a_max and R_min at sample q."""

    qs = (
        19,
        84,
        1054,
        25781,
        50508,
        176251,
        16785921,
        85137581,
        10**12,
        10**18,
    )
    rows = []
    for q in qs:
        cap = LN3 * (q**WW_EXPONENT)
        rows.append(
            {
                "q": q,
                "ww_a_max_diagnostic": cap,
                "R_min_ww_floor": math.exp(4.0 / (cap + 2.0)),
                "ln_R_min_ww_floor": 4.0 / (cap + 2.0),
            }
        )
    return rows


def invert_r_min_threshold(target: float) -> dict[str, Any]:
    """Smallest q at which the diagnostic WW cap allows R_min ≤ target.

    Solve (log 3) q^{3.1163051} ≥ 4 / ln(target) - 2.
    """

    ln_t = math.log(target)
    need = 4.0 / ln_t - 2.0
    q = (need / LN3) ** (1.0 / WW_EXPONENT)
    return {
        "target_R_min": target,
        "required_a": need,
        "q_threshold": q,
    }


def _census(rows: list[dict[str, Any]]) -> dict[str, Any]:
    """Summary ratios. The ε=0 diagnostic is not a theorem at tiny q;
    q ≥ 19 is the first leftover near-convergent.
    """

    if not rows:
        return {
            "n": 0,
            "max_a_over_ww_cap": None,
            "max_a": None,
            "q_at_max_a": None,
        }
    lab = [r for r in rows if r["q"] >= 19]
    pool = lab if lab else rows
    worst = max(pool, key=lambda r: r["a_over_ww_cap"])
    biggest = max(pool, key=lambda r: r["a_next"])
    return {
        "n": len(rows),
        "n_q_ge_19": len(lab),
        "max_a_over_ww_cap": worst["a_over_ww_cap"],
        "q_at_max_ratio": worst["q"],
        "a_at_max_ratio": worst["a_next"],
        "max_a": biggest["a_next"],
        "q_at_max_a": biggest["q"],
        "all_below_ww_diagnostic": all(r["below_ww_diagnostic"] for r in pool),
    }


def classify(
    alpha_rows: list[dict[str, Any]],
    certified_census: dict[str, Any],
    lab_floor: float,
) -> dict[str, Any]:
    certified = [r for r in alpha_rows if r["certified"]]
    below = certified_census["all_below_ww_diagnostic"]
    last = max(certified, key=lambda r: r["q"])
    no_uniform_gap = last["R_min_ww_floor"] < 1.0 + 1e-10
    lab_ratio = certified_census["max_a_over_ww_cap"]
    if below and no_uniform_gap:
        return {
            "label": CLASS_GREEN,
            "reason": (
                "Wu-Wang transfers to a polynomial cap a_{j+1} = "
                "O_ε(q_j^{3.1163051+ε}) on every partial quotient of "
                "log 2/log 3, hence on every survivor-fan width; every "
                "certified quotient with q≥19 sits below the ε=0 "
                f"diagnostic envelope (max a/cap = {lab_ratio:.3e} at "
                f"q={certified_census['q_at_max_ratio']}); the same "
                "envelope already allows R_min = 1 + o(10^{-10}) at "
                "laboratory q, so the bound cannot prevent "
                "e^{4/(a+2)} → 1"
            ),
            "max_certified_a_over_ww_cap_q_ge_19": lab_ratio,
            "largest_certified_q": last["q"],
            "R_min_ww_floor_at_largest_q": last["R_min_ww_floor"],
            "R_min_ww_floor_at_q19": lab_floor,
        }
    return {
        "label": CLASS_CLOSED,
        "reason": (
            "a certified laboratory quotient exceeded the diagnostic "
            "envelope, or the WW floor still claimed a uniform gap"
        ),
        "max_certified_a_over_ww_cap_q_ge_19": lab_ratio,
    }


def probe_payload() -> dict[str, Any]:
    stored = json.loads(COMPETITION_SUMMARY.read_text(encoding="utf-8"))
    cert = stored["x_certification_deep"]
    alpha_cf = certified_alpha_cf()
    theta_cf = certified_theta_cf()
    obs_partial, _ = decimal_alpha_cf()
    certified_n = alpha_cf["n_quotients"]
    # Observed continuation must reproduce the certified prefix.
    # Drop the terminal observed quotient: it can be a rounding artefact.
    prefix_match = obs_partial[:certified_n] == alpha_cf["partial_quotients"]
    obs_used = obs_partial[:-1] if len(obs_partial) > certified_n + 1 else obs_partial
    alpha_rows = quotient_rows(
        alpha_cf["partial_quotients"],
        certified_through=certified_n,
        tag="alpha",
    )
    if prefix_match and len(obs_used) > certified_n:
        extra = quotient_rows(
            obs_used,
            certified_through=certified_n,
            tag="alpha",
        )
        alpha_rows.extend(r for r in extra if not r["certified"])
    theta_rows = quotient_rows(
        theta_cf["partial_quotients"],
        certified_through=theta_cf["n_quotients"],
        tag="theta_rot",
    )
    scales = scale_table()
    thresholds = [
        invert_r_min_threshold(1.07),
        invert_r_min_threshold(1.01),
        invert_r_min_threshold(1.001),
        invert_r_min_threshold(1.000001),
    ]
    certified_alpha = [r for r in alpha_rows if r["certified"]]
    observed_alpha = [r for r in alpha_rows if not r["certified"]]
    large_certified = [r for r in certified_alpha if r["a_next"] >= 5]
    large_observed = [r for r in observed_alpha if r["a_next"] >= 5]
    certified_census = _census(certified_alpha)
    observed_census = _census(observed_alpha)
    lab_floor = next(s["R_min_ww_floor"] for s in scales if s["q"] == 19)
    return {
        "model": (
            "Wu-Wang linear-independence measure for 1, log 2, log 3 "
            "implies a_{j+1} = O_ε(q_j^{3.1163051+ε}) for the CF of "
            "log 2/log 3; survivor-fan width is that next quotient, so "
            "families are polynomially bounded in the seed. The bound "
            "does not give a = O(1) and does not prevent R_min → 1. "
            "Not a Baker leftover-killer (that slogan stays REFUTED)"
        ),
        "constants": {
            "wu_wang_nu": WU_WANG_NU,
            "wu_wang_mu": WU_WANG_MU,
            "ww_exponent": WW_EXPONENT,
            "bls_nu": BLS_NU,
            "bls_mu": BLS_MU,
            "bls_exponent": BLS_EXPONENT,
            "rhin_c": RHIN_C,
            "rhin_power": RHIN_POWER,
            "ln3": LN3,
        },
        "x_certification": {
            "x_lo": cert["x_lo"],
            "x_hi": cert["x_hi"],
            "certified": cert["certified"],
            "interval_width": cert["interval_width"],
            "recomputed_powers": False,
        },
        "alpha_cf_certified": alpha_cf,
        "theta_cf_certified": theta_cf,
        "alpha_cf_observed_uncertified": {
            "partial_quotients": obs_used,
            "raw_including_terminal": obs_partial,
            "terminal_dropped": obs_partial[-1] if obs_used != obs_partial else None,
            "prefix_matches_certified": prefix_match,
            "precision": OBS_PREC,
        },
        "alpha_quotient_rows": alpha_rows,
        "theta_quotient_rows": theta_rows,
        "large_certified_alpha_quotients": large_certified,
        "large_observed_alpha_quotients": large_observed,
        "certified_census": certified_census,
        "observed_census": observed_census,
        "ww_scale_table": scales,
        "r_min_thresholds": thresholds,
        "transfer": {
            "statement": (
                "for every ε>0 there is C_ε such that every partial "
                "quotient of log 2/log 3 with sufficiently large q_j "
                "obeys a_{j+1} ≤ C_ε q_j^{3.1163051+ε}; every "
                "survivor fan L_k = q + kQ therefore has width "
                "O_ε(q^{3.1163051+ε})"
            ),
            "does_not_bound_a_by_a_constant": True,
            "does_not_prevent_R_min_to_1": True,
            "not_a_leftover_killer": True,
        },
        "classification": classify(alpha_rows, certified_census, lab_floor),
        "not_a_halt_theorem": True,
        "no_cycle_all_lengths": False,
        "no_new_period_bound": True,
        "baker_killer_stays_refuted": True,
        "git_commit": git_commit(),
    }


def write_artifacts(payload: dict[str, Any] | None = None) -> dict[str, Any]:
    payload = payload or probe_payload()
    DATA_DIR.mkdir(parents=True, exist_ok=True)
    (DATA_DIR / "summary.json").write_text(
        json.dumps(payload, indent=2) + "\n", encoding="utf-8"
    )
    return payload


def main() -> None:
    payload = write_artifacts()
    print("certified α CF:", payload["alpha_cf_certified"]["partial_quotients"])
    print("certified θ CF:", payload["theta_cf_certified"]["partial_quotients"])
    obs = payload["alpha_cf_observed_uncertified"]
    print(
        "observed prefix matches certified:",
        obs["prefix_matches_certified"],
        "n_obs",
        len(obs["partial_quotients"]),
    )
    print("large certified α quotients (a ≥ 5):")
    for row in payload["large_certified_alpha_quotients"]:
        print(
            f"  a[{row['j']+1}]={row['a_next']} at q={row['q']}: "
            f"a/ww_cap={row['a_over_ww_cap']:.3e} "
            f"R_min(a)={row['R_min_from_a']:.6f} "
            f"R_min_WW={row['R_min_ww_floor']:.16f}"
        )
    print("large observed α quotients (a ≥ 5, terminal dropped):")
    for row in payload["large_observed_alpha_quotients"]:
        print(
            f"  a[{row['j']+1}]={row['a_next']} at q={row['q']}: "
            f"a/ww_cap={row['a_over_ww_cap']:.3e} "
            f"R_min(a)={row['R_min_from_a']:.6f}"
        )
    print("certified census q≥19:", payload["certified_census"])
    print("observed census q≥19:", payload["observed_census"])
    print("WW-allowed R_min floors:")
    for row in payload["ww_scale_table"]:
        print(
            f"  q={row['q']:<12} a_max≈{row['ww_a_max_diagnostic']:.4e} "
            f"R_min≥{row['R_min_ww_floor']:.16f}"
        )
    print("q-thresholds for WW-allowed R_min:")
    for row in payload["r_min_thresholds"]:
        print(
            f"  R_min≤{row['target_R_min']}: q≳{row['q_threshold']:.4g} "
            f"(need a≥{row['required_a']:.4g})"
        )
    print(payload["classification"]["label"])
    print(payload["classification"]["reason"])


if __name__ == "__main__":
    main()
