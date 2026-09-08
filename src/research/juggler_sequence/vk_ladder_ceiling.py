"""What the remaining elementary ladder is worth, in the units that decide.

The elementary production family adds one rung per word ``V_k = (OE)^k E``
(``V_2 = OEOEE``), each contributing a term
``3^-(k+1) * ((1/2)(3/4)^k)^lambda`` to the contagion recursion.  The
laboratory has audited ``V_2`` through ``V_6``, moving
``lambda** : 0.4801 -> 0.4926``, and every dossier ends by naming the next
rung as the best next question.

Theorem 5 of the production note already gives the limit of the whole
family in closed form: the tail telescopes and the recursion collapses to
``x + y/3 = 1`` with ``x = 2^-lambda``, ``y = (3/4)^lambda``, root
``0.4927``.  So the residual is known without computing any further rung.

What was never asked is what that residual buys.  ``lambda**`` reaches the
Tao reduction through one number, the required rate ``1 - lambda**``, and
that feeds only *discrete* constants: the least Chernoff depth ``C`` and
the least Azuma depth ``C(q)`` in the biased-split form.  A discrete
constant moves only when the rate crosses a threshold.  This module
computes those thresholds and compares them with the family limit, so the
question "is ``V_7`` worth an audit?" is answered for every ``k`` at once.
"""

from __future__ import annotations

import json
from typing import Any

from research.juggler_sequence.fate_contagion import RECURSIONS, lambda_root
from research.juggler_sequence.tao_reduction import (
    azuma_exponent,
    chernoff_exponent,
    least_C,
    least_C_biased,
)

#: Rungs whose constants are audited in the production note (V_2 .. V_6).
AUDITED_MAX_K = 6

#: Biased-split shares carried by the fate and Tao notes.
AZUMA_SHARES = (0.5, 0.55)

#: The three fixed terms of the recursion: sweep, block average on good
#: fibers, and the monotone-pairing rest coefficient.
BASE_TERMS: list[tuple[float, float]] = [
    (1.0, 0.5),
    (1.0 / 9.0, 3.0 / 8.0),
    (2.0 / 9.0, 0.75),
]


def vk_term(k: int) -> tuple[float, float]:
    """The ``V_k`` term ``(coefficient, scale)``: ``3^-(k+1)`` at ``(1/2)(3/4)^k``."""

    if k < 2:
        raise ValueError("the elementary family starts at V_2 = OEOEE")
    return (3.0 ** (-(k + 1)), 0.5 * (0.75**k))


def vk_recursion(k_max: int) -> list[tuple[float, float]]:
    """Recursion coefficients for the family truncated at ``V_{k_max}``."""

    return BASE_TERMS + [vk_term(k) for k in range(2, k_max + 1)]


def family_tail(lam: float, k_from: int) -> float:
    """Exact sum of the rungs ``V_k`` for ``k >= k_from`` at exponent ``lam``.

    ``sum_{k >= k_from} 3^-(k+1) x y^k = (x/3) (y/3)^k_from / (1 - y/3)``.
    """

    x = 2.0**-lam
    y = 0.75**lam
    return (x / 3.0) * (y / 3.0) ** k_from / (1.0 - y / 3.0)


def _bisect(f) -> float:
    lo, hi = 0.0, 1.0
    for _ in range(200):
        mid = (lo + hi) / 2.0
        if f(mid) > 0:
            lo = mid
        else:
            hi = mid
    return (lo + hi) / 2.0


def family_limit_closed_form() -> float:
    """Root of the collapsed equation ``2^-lambda + (3/4)^lambda / 3 = 1``."""

    return _bisect(lambda lam: 2.0**-lam + (0.75**lam) / 3.0 - 1.0)


def family_limit_by_series() -> float:
    """Root of the full recursion with the geometric tail summed exactly.

    Independent of :func:`family_limit_closed_form`; the two agreeing is the
    numerical check on the telescoping of production-note Theorem 5.
    """

    def f(lam: float) -> float:
        return sum(c * e**lam for c, e in BASE_TERMS) + family_tail(lam, 2) - 1.0

    return _bisect(f)


def downstream_constants(lam: float) -> dict[str, Any]:
    """The constants that ``lambda**`` actually decides, at exponent ``lam``."""

    rate = 1.0 - lam
    out: dict[str, Any] = {
        "lambda": lam,
        "required_rate": rate,
        "least_chernoff_C": least_C(rate),
    }
    for q in AZUMA_SHARES:
        out[f"least_azuma_C_{q}"] = least_C_biased(q, rate)
    return out


def chernoff_threshold(current_C: int) -> dict[str, float]:
    """The ``lambda`` needed to drop the least Chernoff depth below ``current_C``.

    ``least_C(rate)`` is the least ``C`` with ``e(C) > rate``, so it falls to
    ``current_C - 1`` exactly when ``rate < e(current_C - 1)``.
    """

    e_below = chernoff_exponent(current_C - 1)
    return {
        "target_C": current_C - 1,
        "exponent_at_target": e_below,
        "rate_must_be_below": e_below,
        "lambda_must_exceed": 1.0 - e_below,
    }


def azuma_threshold(q: float, current_C: int) -> dict[str, float]:
    """The ``lambda`` needed to drop the least Azuma depth below ``current_C``."""

    e_below = azuma_exponent(current_C - 1, q)
    return {
        "q": q,
        "target_C": current_C - 1,
        "exponent_at_target": e_below,
        "rate_must_be_below": e_below,
        "lambda_must_exceed": 1.0 - e_below,
    }


def ladder_rows(k_max: int = 24) -> list[dict[str, Any]]:
    """One row per truncation ``V_2 .. V_{k_max}``, with its downstream constants."""

    rows = []
    for k in range(2, k_max + 1):
        row = downstream_constants(lambda_root(vk_recursion(k)))
        row["k"] = k
        row["audited"] = k <= AUDITED_MAX_K
        rows.append(row)
    return rows


def ladder_report(k_max: int = 24) -> dict[str, Any]:
    """Price the whole remaining ladder against the thresholds it must cross."""

    lam_closed = family_limit_closed_form()
    lam_series = family_limit_by_series()
    rows = ladder_rows(k_max)
    by_k = {row["k"]: row for row in rows}
    last_audited = by_k[AUDITED_MAX_K]
    limit_row = downstream_constants(lam_closed)
    residual = lam_closed - last_audited["lambda"]

    thresholds: dict[str, Any] = {
        "chernoff": chernoff_threshold(last_audited["least_chernoff_C"]),
    }
    for q in AZUMA_SHARES:
        thresholds[f"azuma_{q}"] = azuma_threshold(q, last_audited[f"least_azuma_C_{q}"])

    shortfall = {name: t["lambda_must_exceed"] - lam_closed for name, t in thresholds.items()}
    cheapest = min(shortfall, key=lambda name: shortfall[name])

    return {
        "family_limit_closed_form": lam_closed,
        "family_limit_by_series": lam_series,
        "closed_form_agrees_with_series": abs(lam_closed - lam_series) < 1e-12,
        "last_audited_k": AUDITED_MAX_K,
        "last_audited": last_audited,
        "family_limit_constants": limit_row,
        "residual_lambda_past_last_audited": residual,
        "constants_unchanged_at_limit": all(
            limit_row[key] == last_audited[key]
            for key in last_audited
            if key.startswith("least_")
        ),
        "thresholds": thresholds,
        "shortfall_to_thresholds": shortfall,
        "cheapest_threshold": cheapest,
        "shortfall_over_residual": shortfall[cheapest] / residual if residual else None,
        "ladder_is_downstream_inert": all(v > 0.0 for v in shortfall.values()),
        "rows": rows,
    }


def last_effective_rung(k_max: int = 24) -> int | None:
    """Least ``k`` whose constants already equal the whole family's.

    Every rung after this one leaves all of them where they are, so this is
    where the ladder stops paying -- as opposed to where it stops moving
    ``lambda``, which is nowhere.
    """

    rows = ladder_rows(k_max)
    limit = downstream_constants(family_limit_closed_form())
    keys = [key for key in limit if key.startswith("least_")]
    for row in rows:
        if all(row[key] == limit[key] for key in keys):
            return row["k"]
    return None


def geometric_ratio(k_max: int = 24) -> dict[str, Any]:
    """Check that the residual to the limit shrinks by a constant factor per rung."""

    lam_inf = family_limit_closed_form()
    gaps = [(k, lam_inf - lambda_root(vk_recursion(k))) for k in range(2, k_max + 1)]
    ratios = [
        (gaps[i + 1][0], gaps[i + 1][1] / gaps[i][1])
        for i in range(len(gaps) - 1)
        if gaps[i][1] > 1e-15
    ]
    # Gaps fall by ~0.29 per rung, so beyond k ~ 14 they are near the double
    # precision floor and the measured ratio is noise.  Read it where the gap
    # is still comfortably above it.
    clean = [(k, r) for (k, r), (_, g) in zip(ratios, gaps[1:]) if g > 1e-11]
    return {
        "gaps": [{"k": k, "gap": g} for k, g in gaps],
        "ratios": [{"k": k, "ratio": r} for k, r in ratios],
        "predicted_ratio_y_over_3": (0.75**lam_inf) / 3.0,
        "settled_ratio": clean[-1][1] if clean else None,
        "settled_ratio_read_at_k": clean[-1][0] if clean else None,
    }


def official_lambda_starstar() -> float:
    """The recursion the notes call ``lambda**``, for cross-checking ``vk_recursion``."""

    return lambda_root(RECURSIONS["block_third_plus_oeoee_v6"])


#: Resolution of the natural-density census that the failure margin is read
#: against (``failure_margin.summary()["census_resolution"]``).
CENSUS_RESOLUTION = 0.06


def continuous_consumer(
    Cs: tuple[int, ...] = (20, 25, 30, 43, 50),
    qs: tuple[float, ...] = (0.5, 0.55, 0.6),
) -> dict[str, Any]:
    """Price the residual against the one downstream quantity that is not discrete.

    ``failure_margin.m(C, q)`` depends on the required rate continuously, so
    the remaining ladder does move it.  The question is whether it moves it by
    anything readable: the margin is compared against a census of resolution
    ``CENSUS_RESOLUTION``.
    """

    from research.juggler_sequence.failure_margin import failure_margin

    rate_audited = 1.0 - lambda_root(vk_recursion(AUDITED_MAX_K))
    rate_limit = 1.0 - family_limit_closed_form()
    rows = []
    for q in qs:
        for C in Cs:
            at_audited = failure_margin(C, q, rate_audited)["margin"]
            at_limit = failure_margin(C, q, rate_limit)["margin"]
            rows.append(
                {
                    "C": C,
                    "q": q,
                    "margin_at_last_audited": at_audited,
                    "margin_at_family_limit": at_limit,
                    "gain": at_limit - at_audited,
                    "gain_over_census_resolution": (at_limit - at_audited) / CENSUS_RESOLUTION,
                }
            )
    biggest = max(rows, key=lambda row: row["gain"])
    return {
        "census_resolution": CENSUS_RESOLUTION,
        "rows": rows,
        "largest_gain": biggest,
        "largest_gain_over_resolution": biggest["gain"] / CENSUS_RESOLUTION,
        "below_census_resolution": biggest["gain"] < CENSUS_RESOLUTION,
    }


def summary() -> dict[str, Any]:
    return {
        "ladder": ladder_report(),
        "geometry": geometric_ratio(),
        "last_effective_rung": last_effective_rung(),
        "official_lambda_starstar": official_lambda_starstar(),
        "continuous_consumer": continuous_consumer(),
    }


def main() -> None:
    print(json.dumps(summary(), indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
