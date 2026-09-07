"""Walk-charge vs finance: the asymptotic competition (arithmetic only).

Phase 0: chart the floor-scaled competition between the Diophantine
finance gap theta(L) and the census-free DK/IET walk envelope
(6/5) B_DK(L, o; n') along the survivor lattice. For each dangerous
length (a negative-side convergent denominator of
theta_rot = log(3/2)/log 3, or a semiconvergent fan member) compute
the exact big-int theta, the Ostrowski digit sum s(L), the DK kill
margin at the anchored laboratory floors, and the break-even floor
n*(L) at which the DK envelope first kills L. Then walk the
self-consistent schedule n_{j+1} = n*(first survivor at n_j) and
test the scaling law n* (ln n*)^2 theta / L -> 6/(5 ln 3).

Everything here is exact integer arithmetic plus the guarded float
comparison shared with Theorem 4.6. No floor verification is run:
floors beyond 162849448 are hypothetical schedule points and no new
period bound is claimed. Not a halt theorem, not a uniform B/theta
claim (REFUTED at fixed floor), and not a Baker revival (theta is
computed exactly, never lower-bounded).

Dossier: docs/problems/juggler_cycle_walk_competition.md.
"""

from __future__ import annotations

from research.juggler_sequence.lean_paths import (
    DATA_ROOT,
)

import json
import math
from fractions import Fraction
from pathlib import Path
from typing import Any

from research.juggler_sequence.cycle_finance import (
    EPS_CONST,
    PARITY_REL_GUARD,
    git_commit,
    o_min_and_theta,
)
from research.juggler_sequence.cycle_walk_charge import (
    CERTIFIED_FLOOR,
    deficit_D,
)
from research.juggler_sequence.cycle_walk_envelope import gap_lower
from research.juggler_sequence.cycle_walk_exchange import c_star_integral
from research.juggler_sequence.cycle_walk_ostrowski import (
    X_HI,
    X_LO,
    certify_x_bounds,
    greedy_digits,
)

DATA_DIR = (
    DATA_ROOT
    / "cycle_walk_competition"
)
OSTROWSKI_SUMMARY = (
    DATA_DIR.parent / "cycle_walk_ostrowski" / "summary.json"
)
NEW_FLOOR_KILL_176251 = (
    DATA_DIR.parent / "cycle_walk_charge" / "new_floor_kills" / "L176251.json"
)

# Deeper sandwich: consecutive convergents of x = log 2 / log 3 around
# q = 8.5e7 / 2.7e8, certified below by two pure big-int comparisons.
# Sides alternate: x > 171928773/272500658 and x < 53715833/85137581.
X_LO_DEEP = (171_928_773, 272_500_658)
X_HI_DEEP = (53_715_833, 85_137_581)

FLOOR_ZERO = CERTIFIED_FLOOR  # 26254995, J-residual-floor-twenty-six-million
FLOOR_ONE = 162_849_448  # new-floor extension, verification in flight

OFFSET_L, OFFSET_O = 1054, 665  # family step and its odd count
LN3 = math.log(3.0)
LAW_CONST = 6.0 / (5.0 * LN3)  # n* (ln n*)^2 theta / L -> 6/(5 ln 3)

Q_LIMIT_DEEP = 100_000_000
MAX_SCHEDULE_LEVELS = 80
BREAK_EVEN_HI = 80.0
# Transport-lemma domain: keep D = 1.05 e/n + 0.7 o/n^{3/2} small by
# solving only above n = 30 L (D <= 0.035 + o(1) there).
DOMAIN_FACTOR = 30.0

CLASS_GREEN = "WALK_COMPETITION_GREEN"
CLASS_PARK = "WALK_COMPETITION_PARK"
CLASS_CLOSED = "WALK_COMPETITION_CLOSED"

_POW3: dict[int, int] = {}


def pow3(exponent: int) -> int:
    value = _POW3.get(exponent)
    if value is None:
        value = 3**exponent
        _POW3[exponent] = value
    return value


def certify_deep_bounds() -> dict[str, Any]:
    """x strictly inside (X_LO_DEEP, X_HI_DEEP) by integer powers.

    x > p/q iff 2^q > 3^p; x < p/q iff 2^q < 3^p. The two 3-powers
    are cached and reused for the exact theta of the deep seeds.
    """

    p_lo, q_lo = X_LO_DEEP
    p_hi, q_hi = X_HI_DEEP
    lower_ok = (1 << q_lo) > pow3(p_lo)
    upper_ok = (1 << q_hi) < pow3(p_hi)
    width = float(Fraction(p_hi, q_hi) - Fraction(p_lo, q_lo))
    return {
        "x_lo": [p_lo, q_lo],
        "x_hi": [p_hi, q_hi],
        "lower_ok": lower_ok,
        "upper_ok": upper_ok,
        "certified": lower_ok and upper_ok,
        "interval_width": width,
    }


def _interval_cf(
    lo: Fraction, hi: Fraction, q_limit: int
) -> tuple[list[int], list[tuple[int, int]]]:
    """Shared-quotient CF of every value in (lo, hi); (p, q) convergents."""

    partial: list[int] = []
    convergents: list[tuple[int, int]] = []
    h_prev, h = 1, 0
    k_prev, k = 0, 1
    first = True
    while True:
        a_lo = int(lo) if lo >= 0 else -int(-lo) - 1
        a_hi = int(hi) if hi >= 0 else -int(-hi) - 1
        if a_lo != a_hi:
            break
        a = a_lo
        partial.append(a)
        if first:
            h_prev, h = 1, a
            k_prev, k = 0, 1
            first = False
        else:
            h_prev, h = h, a * h + h_prev
            k_prev, k = k, a * k + k_prev
            if k > q_limit:
                break
            convergents.append((h, k))
        frac_lo = lo - a
        frac_hi = hi - a
        if frac_lo == 0 or frac_hi == 0:
            break
        lo, hi = 1 / frac_hi, 1 / frac_lo
    return partial, convergents


def deep_theta_cf(q_limit: int = Q_LIMIT_DEEP) -> dict[str, Any]:
    """Certified CF data of theta_rot = 1 - x on the deep interval."""

    lo_t = 1 - Fraction(*X_HI_DEEP)
    hi_t = 1 - Fraction(*X_LO_DEEP)
    partial, convergents = _interval_cf(lo_t, hi_t, q_limit)
    denominators = [1] + [q for _, q in convergents]
    lo_x = Fraction(*X_LO_DEEP)
    hi_x = Fraction(*X_HI_DEEP)
    partial_x, convergents_x = _interval_cf(lo_x, hi_x, q_limit)
    return {
        "partial_quotients": partial,
        "denominators": denominators,
        "reached": max(denominators),
        "x_partial_quotients": partial_x,
        "x_convergents": [[p, q] for p, q in convergents_x],
    }


def o_min_exact(length: int) -> int:
    """Minimal o with 3^o > 2^L, decided by the deep interval or,
    when L x sits closer to an integer than the interval width, by
    one exact power comparison."""

    p_lo, q_lo = X_LO_DEEP
    p_hi, q_hi = X_HI_DEEP
    a_lo = (length * p_lo) // q_lo
    a_hi = (length * p_hi) // q_hi
    if a_lo == a_hi:
        return a_lo + 1
    if a_hi != a_lo + 1:
        raise RuntimeError(f"interval too wide at L={length}")
    # straddle: decide 3^a_hi vs 2^L exactly
    if pow3(a_hi) <= (1 << length):
        return a_hi + 1
    return a_hi


def theta_exact(length: int, odd_count: int | None = None) -> dict[str, Any]:
    """Exact theta = 1 - 2^L / 3^o with the o-minimality certificate."""

    o = odd_count if odd_count is not None else o_min_exact(length)
    p3 = pow3(o)
    p2 = 1 << length
    if not (p3 > p2 and p3 // 3 <= p2):
        raise RuntimeError(f"o={o} is not minimal at L={length}")
    return {"length": length, "odd_count": o, "theta": (p3 - p2) / p3}


def fan_thetas(
    base_length: int,
    base_odd: int,
    step_length: int,
    step_odd: int,
    k_max: int,
) -> list[dict[str, Any]]:
    """Exact thetas along L_k = base + k*step, incrementally."""

    cur3 = pow3(base_odd)
    cur2 = 1 << base_length
    step3 = pow3(step_odd)
    rows: list[dict[str, Any]] = []
    for k in range(1, k_max + 1):
        cur3 = cur3 * step3
        cur2 = cur2 << step_length
        if not (cur3 > cur2 and cur3 // 3 <= cur2):
            raise RuntimeError(f"fan o not minimal at k={k}")
        rows.append(
            {
                "length": base_length + k * step_length,
                "odd_count": base_odd + k * step_odd,
                "theta": (cur3 - cur2) / cur3,
                "fan_k": k,
            }
        )
    return rows


def dk_price(
    length: int,
    odd_count: int,
    digit_sum: int,
    theta: float,
    floor_n: float,
) -> dict[str, Any]:
    """DK/IET envelope price at floor n: kill margin theta / rhs."""

    log_n = math.log(floor_n) - deficit_D(length, odd_count, float(floor_n))
    star = c_star_integral(log_n)
    dk_cap = 2.0 * digit_sum / length
    c_dk = star["C"] + dk_cap
    scale = length / (math.exp(log_n) * log_n)
    rhs = EPS_CONST * c_dk * scale * (1.0 + PARITY_REL_GUARD)
    gap = gap_lower(log_n)
    return {
        "log_n": log_n,
        "C_star": star["C"],
        "C_dk": c_dk,
        "dk_cap": dk_cap,
        "cap_below_gap": dk_cap < gap,
        "rhs": rhs,
        "margin": theta / rhs if rhs else math.inf,
    }


def break_even_floor(
    length: int,
    odd_count: int,
    digit_sum: int,
    theta: float,
) -> dict[str, Any]:
    """Smallest floor at which the DK envelope kills L (outward)."""

    def margin_at(log_floor: float) -> float:
        return dk_price(
            length, odd_count, digit_sum, theta, math.exp(log_floor)
        )["margin"]

    lo = math.log(max(400.0, DOMAIN_FACTOR * length))
    hi = BREAK_EVEN_HI
    domain_floor = margin_at(lo) >= 1.0
    if domain_floor:
        hi = lo
    elif margin_at(hi) < 1.0:
        raise RuntimeError(f"break-even floor above e^{hi} at L={length}")
    else:
        for _ in range(200):
            mid = 0.5 * (lo + hi)
            if margin_at(mid) >= 1.0:
                hi = mid
            else:
                lo = mid
    n_star = math.exp(hi)
    while dk_price(length, odd_count, digit_sum, theta, n_star)["margin"] < 1.0:
        n_star *= 1.0 + 1e-12
    ln_n = math.log(n_star)
    law_ratio = (
        None
        if domain_floor
        else n_star * ln_n * ln_n * theta / (length * LAW_CONST)
    )
    return {
        "n_star": n_star,
        "ln_n_star": ln_n,
        "n_star_is_domain_floor": domain_floor,
        "margin_at_n_star": dk_price(
            length, odd_count, digit_sum, theta, n_star
        )["margin"],
        "law_ratio": law_ratio,
    }


def build_row(
    length: int,
    odd_count: int,
    theta: float,
    denominators: list[int],
    floors: tuple[float, ...] = (FLOOR_ZERO + 1, FLOOR_ONE + 1),
    tag: str = "",
) -> dict[str, Any]:
    digits = greedy_digits(length, denominators)
    if not digits["exact"]:
        raise RuntimeError(f"greedy decomposition not exact at L={length}")
    s = digits["digit_sum"]
    row: dict[str, Any] = {
        "length": length,
        "odd_count": odd_count,
        "theta": theta,
        "digit_sum": s,
        "blocks": digits["blocks"],
        "tag": tag,
    }
    for label, floor_n in zip(("floor0", "floor1"), floors):
        price = dk_price(length, odd_count, s, theta, floor_n)
        row[f"margin_{label}"] = price["margin"]
        row[f"cap_below_gap_{label}"] = price["cap_below_gap"]
    row.update(break_even_floor(length, odd_count, s, theta))
    return row


def collect_rows(denominators: list[int]) -> list[dict[str, Any]]:
    """Dangerous seeds, semiconvergent fans, and 1054-offset families."""

    rows: list[dict[str, Any]] = []

    def add(length: int, odd: int | None, theta: float | None, tag: str):
        if theta is None:
            t = theta_exact(length, odd)
            odd, theta = t["odd_count"], t["theta"]
        rows.append(build_row(length, odd, theta, denominators, tag=tag))

    # Negative-side convergent seeds (L x just below an integer).
    for seed in (50_508, 176_251, 16_785_921, 85_137_581):
        t = theta_exact(seed)
        add(seed, t["odd_count"], t["theta"], tag="seed")
        # 1054-offset family of the seed.
        cur3 = pow3(t["odd_count"])
        cur2 = 1 << seed
        step3 = pow3(OFFSET_O)
        for k in range(1, 5):
            cur3 *= step3
            cur2 <<= OFFSET_L
            if not (cur3 > cur2 and cur3 // 3 <= cur2):
                raise RuntimeError(f"offset o not minimal at {seed}+{k}*1054")
            add(
                seed + k * OFFSET_L,
                t["odd_count"] + k * OFFSET_O,
                (cur3 - cur2) / cur3,
                tag="offset",
            )

    # Fan A: 176251 + k * 301994, k = 1..54 (k = 1 is 478245; k = 55
    # is the next convergent 16785921, already a seed).
    base = theta_exact(176_251)
    step = theta_exact(301_994)  # positive side: theta near 2/3, harmless
    rows.append(
        build_row(
            301_994, step["odd_count"], step["theta"], denominators,
            tag="positive_convergent",
        )
    )
    # Positive-side convergent: o_min(301994) = p13 + 1, but along the
    # fan the odd count advances by exactly p13 = 190537 per block.
    for fan in fan_thetas(
        176_251, base["odd_count"], 301_994, step["odd_count"] - 1, 54
    ):
        rows.append(
            build_row(
                fan["length"], fan["odd_count"], fan["theta"], denominators,
                tag=f"fanA_k{fan['fan_k']}",
            )
        )

    # Fan B: 16785921 + k * 17087915, k = 1..3 (k = 4 is 85137581).
    base_b = theta_exact(16_785_921)
    step_b_o = 10_781_274  # odd count of the positive convergent 17087915
    for fan in fan_thetas(
        16_785_921, base_b["odd_count"], 17_087_915, step_b_o, 3
    ):
        rows.append(
            build_row(
                fan["length"], fan["odd_count"], fan["theta"], denominators,
                tag=f"fanB_k{fan['fan_k']}",
            )
        )

    rows.sort(key=lambda r: r["length"])
    return rows


def cross_checks(denominators: list[int]) -> dict[str, Any]:
    """Reproduce the certified DK margins and the new-floor DP kill."""

    ostrowski = json.loads(OSTROWSKI_SUMMARY.read_text(encoding="utf-8"))
    checks = []
    for stored in ostrowski["rows"]:
        length = int(stored["length"])
        odd = int(stored["odd_count"])
        exact = theta_exact(length, odd)
        digits = greedy_digits(length, denominators)
        price = dk_price(
            length, odd, digits["digit_sum"], exact["theta"], FLOOR_ZERO + 1
        )
        checks.append(
            {
                "length": length,
                "theta_rel_err": abs(exact["theta"] - stored["theta"])
                / stored["theta"],
                "digit_sum_stored": stored["digit_sum"],
                "digit_sum_deep": digits["digit_sum"],
                "margin_stored": stored["margin_dk"],
                "margin_recomputed": price["margin"],
                "margin_rel_err": abs(price["margin"] - stored["margin_dk"])
                / stored["margin_dk"],
            }
        )
    dp_kill = json.loads(NEW_FLOOR_KILL_176251.read_text(encoding="utf-8"))
    t176 = theta_exact(176_251)
    s176 = greedy_digits(176_251, denominators)["digit_sum"]
    dk_at_floor1 = dk_price(
        176_251, t176["odd_count"], s176, t176["theta"], FLOOR_ONE + 1
    )
    return {
        "n_rows": len(checks),
        "max_theta_rel_err": max(c["theta_rel_err"] for c in checks),
        "max_margin_rel_err": max(c["margin_rel_err"] for c in checks),
        "digit_sums_unchanged": all(
            c["digit_sum_stored"] == c["digit_sum_deep"] for c in checks
        ),
        "dp_kill_margin_176251_floor1": dp_kill["kill_margin"],
        "dk_margin_176251_floor1": dk_at_floor1["margin"],
        "dk_kills_176251_at_floor1": dk_at_floor1["margin"] > 1.0,
        "dk_below_dp": dk_at_floor1["margin"] < dp_kill["kill_margin"],
        "rows": checks,
    }


def schedule_walk(rows: list[dict[str, Any]]) -> dict[str, Any]:
    """Self-consistent schedule n_{j+1} = n*(first survivor at n_j).

    Anchors: FLOOR_ZERO (certified) and FLOOR_ONE (in flight). All
    later floors are hypothetical arithmetic; contiguity is over the
    priced rows only and no period bound is claimed.
    """

    levels: list[dict[str, Any]] = []
    anchored = [float(FLOOR_ZERO + 1), float(FLOOR_ONE + 1)]
    floor_n = anchored[0]
    for level in range(MAX_SCHEDULE_LEVELS):
        margins = [
            (
                row["length"],
                dk_price(
                    row["length"],
                    row["odd_count"],
                    row["digit_sum"],
                    row["theta"],
                    floor_n,
                )["margin"],
            )
            for row in rows
        ]
        survivors = [(length, m) for length, m in margins if m < 1.0]
        killed = [(length, m) for length, m in margins if m >= 1.0]
        first_survivor = min(survivors)[0] if survivors else None
        contiguous = first_survivor is None or all(
            m >= 1.0
            for length, m in margins
            if length < first_survivor
        )
        entry = {
            "level": level,
            "floor": floor_n,
            "anchored": level < len(anchored),
            "first_survivor": first_survivor,
            "n_killed": len(killed),
            "n_survivors": len(survivors),
            "contiguous_over_rows": contiguous,
        }
        if killed:
            entry["min_kill_margin"] = min(m for _, m in killed)
            entry["max_rho_killed"] = 1.0 / entry["min_kill_margin"]
        if first_survivor is not None:
            surv_margin = dict(margins)[first_survivor]
            entry["survivor_margin"] = surv_margin
            entry["required_improvement"] = 1.0 / surv_margin
            surv_row = next(
                r for r in rows if r["length"] == first_survivor
            )
            entry["survivor_n_star"] = surv_row["n_star"]
        levels.append(entry)
        if first_survivor is None:
            break
        if level + 1 < len(anchored):
            floor_n = anchored[level + 1]
        else:
            floor_n = next(
                r for r in rows if r["length"] == first_survivor
            )["n_star"]
    growth = [
        levels[j + 1]["floor"] / levels[j]["floor"]
        for j in range(len(levels) - 1)
    ]
    return {
        "n_levels": len(levels),
        "final_floor": levels[-1]["floor"],
        "all_lengths_killed_at_final": levels[-1]["first_survivor"] is None,
        "max_floor_growth": max(growth) if growth else None,
        "min_required_improvement": min(
            e["required_improvement"]
            for e in levels
            if "required_improvement" in e
        ),
        "levels": levels,
    }


def scaling_report(
    rows: list[dict[str, Any]], denominators: list[int]
) -> dict[str, Any]:
    """The law n*(ln n*)^2 theta / L -> 6/(5 ln 3) and the
    Diophantine growth n*(q_j) vs q_j q_{j+1} on the seeds."""

    seeds = [r for r in rows if r["tag"] == "seed"]
    dens = sorted(denominators)
    seed_rows = []
    for row in seeds:
        q = row["length"]
        later = [d for d in dens if d > q]
        q_next = later[0] if later else None
        entry = {
            "length": q,
            "theta": row["theta"],
            "n_star": row["n_star"],
            "law_ratio": row["law_ratio"],
        }
        if q_next is not None:
            entry["q_next"] = q_next
            entry["theta_times_q_next_over_ln3"] = (
                row["theta"] * q_next / LN3
            )
            entry["n_star_lnsq_over_qq"] = (
                row["n_star"] * row["ln_n_star"] ** 2 / (q * q_next)
            )
        seed_rows.append(entry)
    law_ratios = [
        r["law_ratio"] for r in rows if r["law_ratio"] is not None
    ]
    fan_a = [r for r in rows if r["tag"].startswith("fanA")]
    return {
        "law_constant": LAW_CONST,
        "n_interior_solves": len(law_ratios),
        "law_ratio_min": min(law_ratios),
        "law_ratio_max": max(law_ratios),
        "law_ratio_in_band": all(0.5 < x < 1.0 for x in law_ratios),
        "seed_rows": seed_rows,
        "n_star_growth_seeds": [
            seed_rows[j + 1]["n_star"] / seed_rows[j]["n_star"]
            for j in range(len(seed_rows) - 1)
        ],
        "fanA_n_star_first": fan_a[0]["n_star"] if fan_a else None,
        "fanA_n_star_last": fan_a[-1]["n_star"] if fan_a else None,
    }


def classify(
    old_bounds: dict[str, Any],
    deep_bounds: dict[str, Any],
    cf: dict[str, Any],
    checks: dict[str, Any],
    schedule: dict[str, Any],
    scaling: dict[str, Any],
) -> dict[str, Any]:
    certified = (
        old_bounds["certified"]
        and deep_bounds["certified"]
        and cf["reached"] >= 85_137_581
    )
    reproduced = (
        checks["max_theta_rel_err"] < 1e-9
        and checks["max_margin_rel_err"] < 1e-6
        and checks["digit_sums_unchanged"]
        and checks["dk_kills_176251_at_floor1"]
        and checks["dk_below_dp"]
    )
    resolved = (
        schedule["all_lengths_killed_at_final"]
        and scaling["law_ratio_in_band"]
    )
    if certified and reproduced and resolved:
        return {
            "label": CLASS_GREEN,
            "reason": (
                "deep sandwich certified and the DK pipeline reproduces "
                "the stored 19-row margins and the new-floor 176251 kill; "
                "every dangerous seed and fan member has an exact break-"
                "even floor obeying n*(ln n*)^2 theta/L in (0.5, 1) times "
                "6/(5 ln 3); the self-consistent schedule kills all "
                "priced rows but its floors grow like q_j q_{j+1} along "
                "the dangerous convergents"
            ),
        }
    if not certified:
        return {
            "label": CLASS_CLOSED,
            "reason": "the deep x-sandwich or CF certification failed",
        }
    if not reproduced:
        return {
            "label": CLASS_CLOSED,
            "reason": "the DK pipeline does not reproduce stored margins",
        }
    return {
        "label": CLASS_PARK,
        "reason": "schedule or scaling law incomplete on the priced rows",
    }


def probe_payload() -> dict[str, Any]:
    old_bounds = certify_x_bounds()
    deep_bounds = certify_deep_bounds()
    cf = deep_theta_cf()
    denominators = cf["denominators"]
    checks = cross_checks(denominators)
    rows = collect_rows(denominators)
    schedule = schedule_walk(rows)
    scaling = scaling_report(rows, denominators)
    return {
        "model": (
            "floor-scaled competition theta(L) vs (6/5) B_DK(L, o; n'): "
            "exact big-int theta, Ostrowski digit sum, DK envelope "
            "margin, break-even floor n*(L), self-consistent schedule, "
            "and the scaling law n*(ln n*)^2 theta/L -> 6/(5 ln 3)"
        ),
        "floors": {
            "floor0_certified": FLOOR_ZERO,
            "floor1_in_flight": FLOOR_ONE,
            "later_floors_hypothetical": True,
        },
        "x_certification_old": old_bounds,
        "x_certification_deep": deep_bounds,
        "theta_cf": {
            k: cf[k] for k in ("partial_quotients", "denominators", "reached")
        },
        "cross_checks": checks,
        "rows": rows,
        "schedule": schedule,
        "scaling": scaling,
        "classification": classify(
            old_bounds, deep_bounds, cf, checks, schedule, scaling
        ),
        "not_a_halt_theorem": True,
        "no_cycle_all_lengths": False,
        "not_a_uniform_ratio_theorem": True,
        "no_new_period_bound": True,
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
    deep = payload["x_certification_deep"]
    cf = payload["theta_cf"]
    checks = payload["cross_checks"]
    schedule = payload["schedule"]
    scaling = payload["scaling"]
    print(
        f"deep sandwich certified={deep['certified']} "
        f"width={deep['interval_width']:.3e} "
        f"q reached {cf['reached']}"
    )
    print(
        f"cross-checks theta_err={checks['max_theta_rel_err']:.2e} "
        f"margin_err={checks['max_margin_rel_err']:.2e} "
        f"dk_176251@floor1={checks['dk_margin_176251_floor1']:.4f} "
        f"(dp {checks['dp_kill_margin_176251_floor1']:.4f})"
    )
    print(
        f"rows={len(payload['rows'])} "
        f"levels={schedule['n_levels']} "
        f"final_floor={schedule['final_floor']:.3e} "
        f"all_killed={schedule['all_lengths_killed_at_final']} "
        f"min_required={schedule['min_required_improvement']:.4f}"
    )
    print(
        f"law_ratio in [{scaling['law_ratio_min']:.4f}, "
        f"{scaling['law_ratio_max']:.4f}] band={scaling['law_ratio_in_band']}"
    )
    for seed in scaling["seed_rows"]:
        qq = seed.get("n_star_lnsq_over_qq")
        print(
            f"  seed L={seed['length']:>9} theta={seed['theta']:.3e} "
            f"n*={seed['n_star']:.3e} law={seed['law_ratio']:.4f}"
            + (f" n*(ln)^2/qq'={qq:.3f}" if qq is not None else "")
        )
    print(payload["classification"]["label"])
    print(payload["classification"]["reason"])


if __name__ == "__main__":
    main()
