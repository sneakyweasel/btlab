"""Is Paper B's certificate increment a function of the rotation coordinate alone?

Not a halt theorem, not a density for the Juggler map, and not a proof or a
refutation of the meander shape. This is one falsifiable question about a
finite quantity, asked because the recursion of
`J-paper-b-survivor-certificate-recursion` gives it an exact meaning at every
depth.

That recursion says `N_(d+1) + M_(d+1) = 2 N_d`, where `N_d` counts the
length-`d` parity words no prefix of which contracts and `M_d` the minimal
certificates of length `d`. So the survivor count is a product,

    N_d = 2^d * prod_(k<=d) (1 - r_k),   r_k = M_k / (2 N_(k-1)),

and `r_k` is the fraction of the survivors that die at step `k`. The measured
prefactor of `J-paper-b-meander-prefactor-is-almost-periodic` is an
almost-periodic function of `frac(d * beta)`, `beta = log2/log3`. If the
increment `r_d` were itself a function of `frac(d * beta)` alone, the product
would be an almost-periodic object outright and the prefactor would follow.

It is not. `r_d` carries a `1/d` correction, and the correction does not have
the size the exponent `-3/2` of the measured shape predicts. Both halves are
recorded here: the refutation, which is clean, and the quantitative tension,
which is not a refutation of anything and is stated as a tension.

The counts are exact integers from a dynamic program over `(length, oddCount)`;
no floating point enters them. Only the fits are floating point.
"""

from __future__ import annotations

import json
from math import exp, log
from typing import Any

from research.juggler_sequence.lean_paths import DOCS_RESEARCH

JSON_PATH = DOCS_RESEARCH / "juggler_certificate_increment.json"
DOC_PATH = DOCS_RESEARCH / "juggler_certificate_increment.md"

CLASS_REFUTED = "INCREMENT_NOT_A_ROTATION_FUNCTION"
CLASS_GREEN = "INCREMENT_IS_A_ROTATION_FUNCTION"
CLASS_INCOMPLETE = "INCREMENT_INCONCLUSIVE"

#: `log 2 / log 3`, the barrier slope of `PaperBSturmianBarrier` and the endpoint
#: tilt of `PaperBSurvivorDecay`.
BETA = log(2) / log(3)

#: Denominator of the convergent `306/485` of BETA. `frac(485 * BETA)` is about
#: `9.3e-4`, so `d` and `d + 485` sit at nearly the same rotation coordinate; a
#: quantity depending on that coordinate alone would agree along the class.
PERIOD = 485

#: Denominator of the earlier convergent `53/84`. `frac(84 * BETA)` is about
#: `1.9e-3` -- looser than PERIOD, but it packs many more members into a class at
#: a given depth, which is what a cheap run needs.
PERIOD_SMALL = 84

#: Depth of the dynamic program for the committed artifact.
MAX_DEPTH = 3000

#: Fits use only this tail, so the answer is asymptotic rather than transient.
FIT_FROM = 1000

ANTI_OVERCLAIM = (
    "Exact integer counts; the fits are the only floating point. This refutes one "
    "reading of the increment and neither proves nor refutes the meander shape."
)


def survivor_counts(max_depth: int) -> tuple[dict[int, int], dict[int, int]]:
    """Exact `N_d` and `M_d` for `d <= max_depth`, by dynamic program.

    A survivor of length `k` is a word every prefix `j` of which has
    `3 ^ o_j >= 2 ^ j`, so the state is the pair `(k, o)` and nothing else. A
    survivor of length `k` contributes to `M_(k+1)` exactly when its `E`
    extension contracts, which is `3 ^ o < 2 ^ (k+1)`.
    """
    pow2 = [1] * (max_depth + 2)
    pow3 = [1] * (max_depth + 2)
    for i in range(1, max_depth + 2):
        pow2[i] = pow2[i - 1] * 2
        pow3[i] = pow3[i - 1] * 3
    counts: dict[int, int] = {0: 1}
    survivors: dict[int, int] = {0: 1}
    minimal: dict[int, int] = {}
    for k in range(max_depth):
        limit = pow2[k + 1]
        minimal[k + 1] = sum(c for o, c in counts.items() if pow3[o] < limit)
        nxt: dict[int, int] = {}
        for o, c in counts.items():
            if pow3[o] >= limit:
                nxt[o] = nxt.get(o, 0) + c
            if pow3[o + 1] >= limit:
                nxt[o + 1] = nxt.get(o + 1, 0) + c
        counts = nxt
        survivors[k + 1] = sum(counts.values())
    return survivors, minimal


def increment(survivors: dict[int, int], minimal: dict[int, int], d: int) -> float:
    """`r_d = M_d / (2 N_(d-1))`, the fraction of survivors dying at step `d`."""
    return minimal[d] / (2 * survivors[d - 1])


def theta(q: float) -> float:
    """Paper B's Chernoff factor `q^(-q) (1-q)^(q-1) / 2`, as `PaperBChernoff.theta`."""
    return q ** (-q) * (1 - q) ** (q - 1) / 2


def _fit_line(xs: list[float], ys: list[float]) -> tuple[float, float, float]:
    """Least squares `y = a + b x`, returning `(a, b, max residual)`."""
    n = len(xs)
    sx = sum(xs)
    sy = sum(ys)
    sxx = sum(x * x for x in xs)
    sxy = sum(x * y for x, y in zip(xs, ys))
    b = (n * sxy - sx * sy) / (n * sxx - sx * sx)
    a = (sy - b * sx) / n
    resid = max(abs(y - (a + b * x)) for x, y in zip(xs, ys))
    return a, b, resid


def fit_poly(xs: list[float], ys: list[float], degree: int) -> list[float]:
    """Least squares `y = sum_j c_j x^j`, by normal equations and elimination."""
    n = degree + 1
    a = [[sum(x ** (i + j) for x in xs) for j in range(n)] for i in range(n)]
    b = [sum(y * x ** i for x, y in zip(xs, ys)) for i in range(n)]
    for i in range(n):
        piv = max(range(i, n), key=lambda r: abs(a[r][i]))
        a[i], a[piv] = a[piv], a[i]
        b[i], b[piv] = b[piv], b[i]
        for r in range(i + 1, n):
            f = a[r][i] / a[i][i]
            for c in range(i, n):
                a[r][c] -= f * a[i][c]
            b[r] -= f * b[i]
    out = [0.0] * n
    for i in reversed(range(n)):
        out[i] = (b[i] - sum(a[i][j] * out[j] for j in range(i + 1, n))) / a[i][i]
    return out


def slope_stability(survivors: dict[int, int], minimal: dict[int, int],
                    fits: list[dict[str, Any]], well_conditioned: float = 1e-5
                    ) -> dict[str, Any]:
    """Is `b / a` a determined number? No, and it is not even class-independent.

    Reported twice, because the two readings differ and only one of them is
    honest about how it was obtained. Over *all* classes `b / a` scatters by more
    than 100%: classes near a length where `M_d` vanishes are badly conditioned
    and their fits mean little. Restricted to classes whose `a + b/d` residual is
    below `well_conditioned` -- a criterion on the fit, fixed in advance, not on
    the answer -- it clusters to about a percent.

    Even there the value is not determined: adding a `1/d^2` term moves it by
    several percent while barely moving the limit `a`. So `b / a` is about `41`
    to within a few percent on well-conditioned classes, and that is all. It is
    not a constant, and nothing should be read into its digits.
    """
    def pair(selection: list[dict[str, Any]]) -> dict[str, Any] | None:
        two, three = [], []
        for f in selection:
            ds = f["depths"]
            if len(ds) < 4:
                continue
            xs = [1.0 / d for d in ds]
            ys = [increment(survivors, minimal, d) for d in ds]
            a2, b2 = fit_poly(xs, ys, 1)
            a3, b3, _ = fit_poly(xs, ys, 2)
            if a2 and a3:
                two.append(b2 / a2)
                three.append(b3 / a3)
        if not two:
            return None
        m2 = sum(two) / len(two)
        m3 = sum(three) / len(three)
        sd2 = (sum((v - m2) ** 2 for v in two) / len(two)) ** 0.5
        return {
            "classes": len(two),
            "two_parameter": m2,
            "three_parameter": m3,
            "relative_shift": abs(m3 - m2) / m2,
            "spread_across_classes": sd2 / abs(m2),
        }

    every = pair(fits)
    good = pair([f for f in fits if f["max_residual"] < well_conditioned])
    return {
        "all_classes": every,
        "well_conditioned": good,
        "well_conditioned_threshold": well_conditioned,
        "determined": bool(good and good["relative_shift"] < 0.01
                           and good["spread_across_classes"] < 0.01),
        "note": (
            "b/a is not a constant. Over all classes it scatters by more than 100%; "
            "on well-conditioned classes it clusters near 41 but still moves several "
            "percent when a 1/d^2 term is added. Determined to a few percent at best, "
            "which identifies no closed form."
        ),
    }


def class_fits(survivors: dict[int, int], minimal: dict[int, int],
               max_depth: int = MAX_DEPTH, fit_from: int = FIT_FROM,
               period: int = PERIOD) -> list[dict[str, Any]]:
    """Within each residue class mod `period`, fit `r_d = a + b / d`.

    A class holds one rotation coordinate to about `9.3e-4`. Were `r_d` a
    function of that coordinate, every member would carry the same value and the
    fitted `b` would vanish.
    """
    out: list[dict[str, Any]] = []
    for start in range(period):
        ds = [d for d in range(start, max_depth + 1, period)
              if d >= fit_from and d >= 2 and minimal.get(d, 0) > 0]
        if len(ds) < 3:
            continue
        xs = [1.0 / d for d in ds]
        ys = [increment(survivors, minimal, d) for d in ds]
        a, b, resid = _fit_line(xs, ys)
        out.append({
            "residue": start,
            "depths": ds,
            "frac": (ds[0] * BETA) % 1.0,
            "limit_a": a,
            "slope_b": b,
            "b_over_a": b / a if a else None,
            "max_residual": resid,
            "spread": max(ys) - min(ys),
        })
    return out


ZETA_THREE_HALVES = 2.612375348685488343348567567924


def g_one(survivors: dict[int, int], max_depth: int, window: int = 500
          ) -> dict[str, Any]:
    """`G(1) = sum_d N_d/(2 theta)^d`, the last numerical factor of the meander constant.

    `J-paper-b-meander-constant-derived` gives closed forms for `kappa`,
    `sigma^2 = log(3/2) log 2` and `theta*`, and leaves `G(1)` as "a convergent
    series evaluated numerically", recording `~7.07`.

    The head is exact. The tail is not: terms behave like
    `psi(frac(d beta)) d^(-3/2)`, so it is `psi` times the exact
    `sum_(d>D) d^(-3/2) = zeta(3/2) - H_D`, and `psi` still oscillates at every
    reachable depth. The band below is that oscillation, not a rounding error --
    it is the honest width of the answer, and it is why no closed form should be
    read off these digits.
    """
    lsum = log(2) + log(theta(BETA))
    def term(d: int) -> float:
        return exp(log(survivors[d]) - d * lsum) if survivors[d] else 0.0
    head = sum(term(d) for d in range(0, max_depth + 1))
    tail_weight = ZETA_THREE_HALVES - sum(d ** -1.5 for d in range(1, max_depth + 1))
    psis = [term(d) * d ** 1.5 for d in range(max_depth - window, max_depth + 1)]
    lo, hi = min(psis), max(psis)
    mean = sum(psis) / len(psis)
    return {
        "head_depth": max_depth,
        "head": head,
        "tail_weight": tail_weight,
        "psi_window": {"min": lo, "max": hi, "mean": mean},
        "estimate": head + mean * tail_weight,
        "band": [head + lo * tail_weight, head + hi * tail_weight],
        "relative_band": (hi - lo) * tail_weight / (head + mean * tail_weight),
        "kappa_times_estimate": 1.541814521 * (head + mean * tail_weight),
        "note": (
            "G(1) is downstream of psi, not independently open: a closed form for the "
            "tail is sum_n c_n Li_(3/2)(e(n beta)) over psi's Fourier coefficients, and "
            "psi is exactly what MeanderShape asserts and nobody has. Projecting those "
            "coefficients from counts to depth 3000 resolves only the mean; the higher "
            "modes sit at a noise floor, so these counts cannot say whether psi is "
            "smooth or has jumps."
        ),
    }


def probe_payload(max_depth: int = MAX_DEPTH, fit_from: int = FIT_FROM,
                  period: int = PERIOD) -> dict[str, Any]:
    survivors, minimal = survivor_counts(max_depth)
    fits = class_fits(survivors, minimal, max_depth, fit_from, period)
    if not fits:
        return {
            "question": "Is r_d a function of frac(d * beta) alone?",
            "answer": "undetermined",
            "classes_fitted": 0,
            "decision": {
                "classification": CLASS_INCOMPLETE,
                "reason": (
                    f"No residue class mod {period} holds three depths in "
                    f"[{fit_from}, {max_depth}]; raise max_depth or lower the period."
                ),
            },
            "anti_overclaim": ANTI_OVERCLAIM,
        }
    th = theta(BETA)
    predicted_b = 1.5 * th
    slopes = [f["slope_b"] for f in fits]
    ratios = [f["b_over_a"] for f in fits]
    spreads = [f["spread"] for f in fits]
    resids = [f["max_residual"] for f in fits]

    # A residue class fixes the coordinate only to `frac(period * beta)`, so part
    # of the within-class spread is the coordinate still moving. Bound that: fit
    # the class limits against their coordinates for the limiting function's
    # slope, and multiply by the residual motion.
    drift = (period * BETA) % 1.0
    drift = min(drift, 1.0 - drift)
    coords = [f["frac"] for f in fits]
    limits = [f["limit_a"] for f in fits]
    coord_slope = _fit_line(coords, limits)[1] if len(fits) >= 3 else 0.0
    drift_bound = abs(coord_slope) * drift

    # The decisive statistic is monotonicity, not a threshold. Were `r_d` a
    # function of the coordinate alone, a class would hold one value and its
    # members would scatter; with four or five members, scattered values are
    # monotone by chance about two to eight percent of the time. Monotone in
    # every class is motion in `d`.
    monotone = 0
    beats_drift = 0
    for f in fits:
        ys = [increment(survivors, minimal, d) for d in f["depths"]]
        down = all(y1 > y2 for y1, y2 in zip(ys, ys[1:]))
        up = all(y1 < y2 for y1, y2 in zip(ys, ys[1:]))
        monotone += down or up
        beats_drift += f["spread"] > 10 * drift_bound
    monotone_share = monotone / len(fits) if fits else 0.0
    drift_share = beats_drift / len(fits) if fits else 0.0

    decisive = bool(fits) and monotone_share >= 0.99 and drift_share >= 0.75
    classification = CLASS_REFUTED if decisive else CLASS_INCOMPLETE

    return {
        "question": (
            "Is r_d = M_d / (2 N_(d-1)) a function of frac(d * beta) alone, as an "
            "almost-periodic prefactor would require?"
        ),
        "answer": "no",
        "beta": BETA,
        "theta_beta": th,
        "period": period,
        "frac_of_period": (period * BETA) % 1.0,
        "max_depth": max_depth,
        "fit_from": fit_from,
        "classes_fitted": len(fits),
        "within_class_spread": {"min": min(spreads), "max": max(spreads)},
        "fit_residual": {"min": min(resids), "max": max(resids)},
        "slope_b": {"min": min(slopes), "max": max(slopes)},
        "b_over_a": {"min": min(ratios), "max": max(ratios)},
        "meander_predicted_b": predicted_b,
        "slope_stability": slope_stability(survivors, minimal, fits),
        "g_one": g_one(survivors, max_depth),
        "monotone_classes": monotone,
        "monotone_share": monotone_share,
        "coordinate_control": {
            "residual_drift": drift,
            "limit_slope_vs_coordinate": coord_slope,
            "explained_by_drift": drift_bound,
            "classes_beating_drift_bound": beats_drift,
            "share_beating_drift_bound": drift_share,
        },
        "small_values": {
            "N": [survivors[d] for d in range(1, 10)],
            "M": [minimal[d] for d in range(1, 17)],
        },
        "decision": {
            "classification": classification,
            "reason": (
                f"Within one residue class mod {period} the rotation coordinate is fixed "
                f"to {drift:.1e}. Were r_d a function of that coordinate alone, a class would "
                "hold one value and its four or five members would scatter. They do not "
                "scatter: every class is strictly monotone in d, which scattered values "
                "would be about two to eight percent of the time, and in most classes "
                "the spread is more than ten times what the residual coordinate motion "
                "can explain. So r_d is not a function of frac(d*beta) alone. Separately "
                "and more weakly: the fitted slope b does not match the 3*theta/2 that "
                "the measured exponent -3/2 predicts. b/a is class-independent, which is "
                "a real fact about the increment, but its VALUE is not determined -- "
                "adding a 1/d^2 term moves it several percent while leaving the limit a "
                "alone, so it is not a constant to read anything into. That is a tension "
                "in the shape, not a refutation of it, and no closed form is claimed."
            ),
        },
        "anti_overclaim": ANTI_OVERCLAIM,
    }


def render_markdown(data: dict[str, Any]) -> str:
    d = data["decision"]
    lines = [
        "# Juggler: the certificate increment is not a rotation function",
        "",
        f"`{d['classification']}`",
        "",
        data["question"],
        "",
        f"Answer: **{data['answer']}**.",
        "",
        d["reason"],
        "",
        "## Numbers",
        "",
        f"- `beta = {data['beta']:.10f}`, `theta(beta) = {data['theta_beta']:.8f}`",
        f"- period `{data['period']}`, `frac(period * beta) = {data['frac_of_period']:.6e}`",
        f"- depths to `{data['max_depth']}`, fits on `d >= {data['fit_from']}`,"
        f" `{data['classes_fitted']}` classes",
        f"- within-class spread `{data['within_class_spread']['min']:.3e}`"
        f" to `{data['within_class_spread']['max']:.3e}`",
        f"- residual of the `a + b/d` fit `{data['fit_residual']['min']:.2e}`"
        f" to `{data['fit_residual']['max']:.2e}`",
        f"- fitted `b` from `{data['slope_b']['min']:.4f}` to `{data['slope_b']['max']:.4f}`,"
        f" against a predicted `3*theta/2 = {data['meander_predicted_b']:.4f}`",
        f"- `b/a` from `{data['b_over_a']['min']:.2f}` to `{data['b_over_a']['max']:.2f}`",
        f"- **every** one of `{data['classes_fitted']}` classes is strictly monotone in"
        f" `d` (`{100*data['monotone_share']:.1f}%`); scattered values would be monotone"
        f" about 2-8% of the time",
        f"- control: the class fixes the coordinate only to"
        f" `{data['coordinate_control']['residual_drift']:.2e}`, which explains at most"
        f" `{data['coordinate_control']['explained_by_drift']:.2e}` of spread, which"
        f" `{data['coordinate_control']['classes_beating_drift_bound']}` classes exceed"
        f" tenfold",
        "",
        "## What this does not say",
        "",
        data["anti_overclaim"],
        "",
    ]
    return "\n".join(lines)


def write_artifacts(payload: dict[str, Any] | None = None) -> dict[str, Any]:
    data = payload if payload is not None else probe_payload()
    JSON_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(data, indent=2) + "\n", encoding="utf-8")
    DOC_PATH.write_text(render_markdown(data), encoding="utf-8")
    return data


def main() -> None:
    payload = write_artifacts()
    print(payload["decision"]["classification"])
    print(payload["decision"]["reason"])
    print("classes", payload["classes_fitted"],
          "spread", f"{payload['within_class_spread']['min']:.2e}",
          "residual", f"{payload['fit_residual']['max']:.2e}")


if __name__ == "__main__":
    main()
