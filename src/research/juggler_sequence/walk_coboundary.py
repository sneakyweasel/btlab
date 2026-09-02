"""Lyapunov / coboundary correction to the walk.

Phase 0 only. The leading cocycle is

    Δu = log2(ln J(x) / ln x)  →  +log2(3/2) on odd,  −1 on even,

plus floor defects. The fan is nearly neutral for that cocycle. This
branch asks whether a bounded phase correction

    Φ(x) = log2(ln x) + ψ(ξ(x))

can produce uniformly nonnegative one-step or block-step drift on
sufficiently large AboveAnchor transitions.

Not a halt theorem, not a DK tightening, not a reopen of the closed
state-only log/loglog Lyapunov (block potential), and not a Paper A
edit.

Dossier: docs/problems/juggler_walk_coboundary.md.
"""

from __future__ import annotations

import json
import math
from pathlib import Path
from typing import Any, Callable, Iterable

from research.juggler_sequence.flight_divergent_structure import HIGH_FLYERS
from research.juggler_sequence.power_itineraries import ANTI_OVERCLAIM, floor_power

REPO_ROOT = Path(__file__).resolve().parents[3]
DATA_DIR = REPO_ROOT / "data" / "research" / "juggler" / "walk_coboundary"
JSON_PATH = DATA_DIR / "summary.json"

LOG2_3_2 = math.log2(1.5)
LN2 = math.log(2.0)

# Domain: ln x > 0 and J(x) stays in the log-log chart.
MIN_X = 16
SCIENCE_N_MAX = 4_000
TEST_N_MAX = 240
STEP_CAP = 80
PHASE_BIT_CAP = 53
PATH_BIT_CAP = 256
FAN_LEN = 19
MIN_FAMILY = 32
# Long prefixes inside the science window that carry both a fan
# climb (leading ≈ θ_19 ≈ 0.0196) and a post-peak collapse.
ADVERSARY_STARTS = (761, 1089, 1999)

CLASS_DEFEATED = "WALK_COBOUNDARY_DEFEATED"
CLASS_CANDIDATE = "WALK_COBOUNDARY_CANDIDATE"
CLASS_INCOMPLETE = "WALK_COBOUNDARY_INCOMPLETE"

ANTI = {
    **ANTI_OVERCLAIM,
    "halt_theorem": False,
    "eventual_descent_theorem": False,
    "paper_a_modified": False,
    "n0_raised": False,
    "dk_tightened": False,
    "block_potential_reopened": False,
}

# Sawtooth grid: Φ = log2(ln x) + a {α x^β}.
ALPHAS = (1.0, 0.5, math.log2(3.0), math.pi, math.sqrt(2.0))
BETAS = (0.25, 0.5, 0.75, 1.0, 1.25, 1.5, 2.0)
AMPS = (-2.0, -1.0, -0.5, 0.5, 1.0, 2.0)

# Three-phase basis on the floor-error coordinates.
BASIS_AMPS = (-1.5, -1.0, -0.5, 0.0, 0.5, 1.0, 1.5)
FOURIER_AMPS = (-1.5, -1.0, -0.5, 0.5, 1.0, 1.5)


def log2_ln(x: int) -> float:
    """log2(ln x) on integers x >= 3."""

    if x < 3:
        raise ValueError("log2_ln requires x >= 3")
    if x.bit_length() <= 53:
        return math.log2(math.log(x))
    return math.log2(LN2 * ((x.bit_length() - 1) + math.log2(x >> (x.bit_length() - 53))))


def leading_drift(src: int, dst: int) -> float:
    """Exact one-step / block increment of log2(ln ·).

    On an even perfect square src = k^2 the increment is exactly −1.
    """

    if src < 3 or dst < 3:
        raise ValueError("leading_drift requires arguments >= 3")
    k = math.isqrt(src)
    if k * k == src and dst == k:
        return -1.0
    return log2_ln(dst) - log2_ln(src)


def frac(val: float) -> float:
    return val - math.floor(val)


def frac_sqrt(x: int) -> float | None:
    s = math.isqrt(x)
    rem = x - s * s
    if rem == 0:
        return 0.0
    if x.bit_length() > 1020:
        return None
    return rem / (math.sqrt(x) + s)


def frac_three_halves(x: int) -> float | None:
    """{x^{3/2}} = {x {√x}}."""

    fs = frac_sqrt(x)
    if fs is None:
        return None
    return frac(x * fs)


def frac_fourth(x: int) -> float | None:
    if x.bit_length() > 1020:
        return None
    q = math.isqrt(math.isqrt(x))
    return math.sqrt(math.sqrt(float(x))) - q


def frac_alpha_pow(x: int, alpha: float, beta: float) -> float | None:
    """{α x^β} when the monomial sits in the float mantissa."""

    if x < 1 or alpha <= 0 or beta <= 0:
        return None
    if x.bit_length() > PHASE_BIT_CAP:
        return None
    log_val = math.log(alpha) + beta * math.log(x)
    if log_val >= 53.0 * LN2:
        return None
    return frac(math.exp(log_val))


def frac_log2(x: int, alpha: float) -> float:
    return frac(alpha * math.log2(x))


PhaseFn = Callable[[int], float | None]


def dphase(src: int, dst: int, phase: PhaseFn) -> float | None:
    ps = phase(src)
    pd = phase(dst)
    if ps is None or pd is None:
        return None
    return pd - ps


def drift_of(
    src: int,
    dst: int,
    phase: PhaseFn,
    amp: float,
) -> float | None:
    inc = dphase(src, dst, phase)
    if inc is None:
        return None
    return leading_drift(src, dst) + amp * inc


def even_square_tower(k: int, depth: int) -> list[int]:
    """The even-square tower k^{2^depth}, …, k^2, k with k even, k >= 4."""

    if k < 4 or k % 2 == 1 or depth < 1:
        raise ValueError("even_square_tower needs even k >= 4 and depth >= 1")
    xs = [k]
    cur = k
    for _ in range(depth):
        cur = cur * cur
        xs.append(cur)
    xs.reverse()
    return xs


def one_step_bounded_psi_obstruction(k: int = 4, depth: int = 4) -> dict[str, Any]:
    """Bounded ψ cannot cancel the even-square tower.

    On x = m^2 → m the leading increment is exactly −1. Summing
    ψ(m) − ψ(m^{2^N}) along the tower would have to be ≥ N, which
    a bounded ψ cannot do. Finite exceptional sets cannot absorb
    the whole infinite tower.
    """

    xs = even_square_tower(k, depth)
    leadings = [leading_drift(xs[i], xs[i + 1]) for i in range(len(xs) - 1)]
    named = {
        "sqrt": [dphase(xs[i], xs[i + 1], frac_sqrt) for i in range(len(xs) - 1)],
        "three_halves": [
            dphase(xs[i], xs[i + 1], frac_three_halves) for i in range(len(xs) - 1)
        ],
        "fourth": [dphase(xs[i], xs[i + 1], frac_fourth) for i in range(len(xs) - 1)],
    }
    return {
        "k": k,
        "depth": depth,
        "states": [str(x) if x.bit_length() > 53 else x for x in xs],
        "leadings": leadings,
        "leading_sum": sum(leadings),
        "named_dphase": named,
        "identity": "leading on even squares is exactly -1",
        "bounded_psi_impossible": True,
    }


def universe_one_steps(lo: int, hi: int) -> list[tuple[int, int]]:
    """Every one-step (n, J(n)) on [lo, hi] with both ends in the chart."""

    out: list[tuple[int, int]] = []
    for n in range(max(lo, MIN_X), hi + 1):
        y = floor_power(n)
        if y >= 3:
            out.append((n, y))
    return out


def prefix_path(n: int, step_cap: int = STEP_CAP, bit_cap: int = PATH_BIT_CAP) -> list[int]:
    """AboveAnchor prefix of n, including the start.

    The bit cap only stops the prefix; it does not discard earlier
    states. A 256-bit cap already sees both the fan climb and the
    post-peak collapse on the window adversaries (761, 1089).
    """

    if n < MIN_X:
        return []
    path = [n]
    x = n
    for _ in range(step_cap):
        y = floor_power(x)
        if y < n or y < 3:
            break
        if y.bit_length() > bit_cap:
            break
        path.append(y)
        x = y
    return path


def sliding_blocks(path: list[int], length: int) -> list[tuple[int, int]]:
    if length < 1 or len(path) <= length:
        return []
    return [(path[i], path[i + length]) for i in range(len(path) - length)]


def first_oe_pairs(lo: int, hi: int) -> list[tuple[int, int]]:
    """First mixed O^a E^r landing, including contractions."""

    out: list[tuple[int, int]] = []
    start = lo if lo % 2 else lo + 1
    start = max(start, MIN_X | 1)
    for n in range(start, hi + 1, 2):
        x = n
        a0 = 0
        while x % 2 == 1:
            x = floor_power(x)
            a0 += 1
            if a0 > 32 or x < 3:
                break
        r = 0
        while x % 2 == 0 and x >= 2:
            x = floor_power(x)
            r += 1
            if r > 32:
                break
        if a0 >= 1 and r >= 1 and x >= 3 and x.bit_length() <= PATH_BIT_CAP:
            out.append((n, x))
    return out


def near_neutral_pairs(
    pairs: list[tuple[int, int]],
    *,
    margin: float = 0.05,
) -> list[tuple[int, int]]:
    """Blocks whose leading cocycle is in the fan-scale hole."""

    out: list[tuple[int, int]] = []
    for src, dst in pairs:
        lead = leading_drift(src, dst)
        if abs(lead) < margin:
            out.append((src, dst))
    return out


def adversary_prefix_report(n: int) -> dict[str, Any]:
    """Fan margin versus post-peak need on one long AboveAnchor prefix."""

    path = prefix_path(n, step_cap=80, bit_cap=900)
    blocks = sliding_blocks(path, FAN_LEN)
    leads = [leading_drift(src, dst) for src, dst in blocks]
    fan = [v for v in leads if 0.0 < v < 0.05]
    collapse = [v for v in leads if v < 0.0]
    return {
        "n": n,
        "prefix_len": len(path) - 1,
        "peak_bits": max((x.bit_length() for x in path), default=0),
        "n_slide19": len(blocks),
        "n_fan": len(fan),
        "n_collapse": len(collapse),
        "fan_min_leading": min(fan) if fan else None,
        "collapse_min_leading": min(collapse) if collapse else None,
        "both_signs": bool(fan) and bool(collapse),
    }


def collect_families(
    lo: int,
    hi: int,
    *,
    extra_starts: Iterable[int] = (),
) -> dict[str, list[tuple[int, int]]]:
    one = universe_one_steps(lo, hi)
    prefix_one: list[tuple[int, int]] = []
    slide19: list[tuple[int, int]] = []
    starts = list(range(lo if lo % 2 else lo + 1, hi + 1, 2))
    starts.extend(n for n in extra_starts if n >= MIN_X)
    starts.extend(ADVERSARY_STARTS)
    seen_start: set[int] = set()
    for n in starts:
        if n in seen_start:
            continue
        seen_start.add(n)
        path = prefix_path(n)
        prefix_one.extend(sliding_blocks(path, 1))
        slide19.extend(sliding_blocks(path, FAN_LEN))
    return {
        "universe_one": one,
        "prefix_one": prefix_one,
        "slide19": slide19,
        "slide19_fan": near_neutral_pairs(slide19),
        "first_oe": first_oe_pairs(lo, hi),
    }


def _score(
    pairs: list[tuple[int, int]],
    phase: PhaseFn,
    amp: float,
) -> dict[str, Any] | None:
    if not pairs:
        return None
    worst = math.inf
    worst_pair = pairs[0]
    n_used = 0
    n_pos = 0
    for src, dst in pairs:
        val = drift_of(src, dst, phase, amp)
        if val is None:
            continue
        n_used += 1
        if val > 1e-12:
            n_pos += 1
        if val < worst:
            worst = val
            worst_pair = (src, dst)
    if n_used == 0:
        return None
    return {
        "min_drift": worst,
        "n_used": n_used,
        "n_positive": n_pos,
        "worst_src": worst_pair[0],
        "worst_dst": worst_pair[1],
        "amp": amp,
    }


def _score_combo(
    pairs: list[tuple[int, int]],
    phases: list[PhaseFn],
    amps: tuple[float, ...],
) -> dict[str, Any] | None:
    if not pairs or len(phases) != len(amps):
        return None
    worst = math.inf
    worst_pair = pairs[0]
    n_used = 0
    n_pos = 0
    for src, dst in pairs:
        total = leading_drift(src, dst)
        ok = True
        for phase, amp in zip(phases, amps, strict=True):
            if amp == 0.0:
                continue
            inc = dphase(src, dst, phase)
            if inc is None:
                ok = False
                break
            total += amp * inc
        if not ok:
            continue
        n_used += 1
        if total > 1e-12:
            n_pos += 1
        if total < worst:
            worst = total
            worst_pair = (src, dst)
    if n_used == 0:
        return None
    return {
        "min_drift": worst,
        "n_used": n_used,
        "n_positive": n_pos,
        "worst_src": worst_pair[0],
        "worst_dst": worst_pair[1],
        "amps": list(amps),
    }


def baseline(pairs: list[tuple[int, int]]) -> dict[str, Any] | None:
    return _score(pairs, lambda _x: 0.0, 0.0)


def search_sawtooth(pairs: list[tuple[int, int]]) -> dict[str, Any]:
    best: dict[str, Any] | None = None
    n_tried = 0
    for alpha in ALPHAS:
        for beta in BETAS:

            def phase(x: int, a: float = alpha, b: float = beta) -> float | None:
                return frac_alpha_pow(x, a, b)

            for amp in AMPS:
                n_tried += 1
                rec = _score(pairs, phase, amp)
                if rec is None:
                    continue
                rec = {**rec, "alpha": alpha, "beta": beta, "kind": "sawtooth"}
                if best is None or rec["min_drift"] > best["min_drift"]:
                    best = rec
    return {"n_tried": n_tried, "best": best}


def search_named_sawtooth(pairs: list[tuple[int, int]]) -> dict[str, Any]:
    named: dict[str, PhaseFn] = {
        "sqrt": frac_sqrt,
        "three_halves": frac_three_halves,
        "fourth": frac_fourth,
        "log2": lambda x: frac_log2(x, 1.0),
        "pi_log2": lambda x: frac_log2(x, math.pi),
        "theta_log2": lambda x: frac_log2(x, math.log2(3.0)),
    }
    best: dict[str, Any] | None = None
    for name, phase in named.items():
        for amp in AMPS:
            rec = _score(pairs, phase, amp)
            if rec is None:
                continue
            rec = {**rec, "phase": name, "kind": "named"}
            if best is None or rec["min_drift"] > best["min_drift"]:
                best = rec
    return {"best": best}


def search_basis(pairs: list[tuple[int, int]]) -> dict[str, Any]:
    phases = [frac_fourth, frac_sqrt, frac_three_halves]
    best: dict[str, Any] | None = None
    n_tried = 0
    for a in BASIS_AMPS:
        for b in BASIS_AMPS:
            for c in BASIS_AMPS:
                n_tried += 1
                rec = _score_combo(pairs, phases, (a, b, c))
                if rec is None:
                    continue
                rec = {**rec, "kind": "basis", "phases": ["fourth", "sqrt", "three_halves"]}
                if best is None or rec["min_drift"] > best["min_drift"]:
                    best = rec
    return {"n_tried": n_tried, "best": best}


def search_fourier(pairs: list[tuple[int, int]]) -> dict[str, Any]:
    named: dict[str, PhaseFn] = {
        "sqrt": frac_sqrt,
        "three_halves": frac_three_halves,
        "fourth": frac_fourth,
        "pi_log2": lambda x: frac_log2(x, math.pi),
    }
    best: dict[str, Any] | None = None
    n_tried = 0
    for name, phase in named.items():

        def cos_phase(x: int, p: PhaseFn = phase) -> float | None:
            val = p(x)
            return None if val is None else math.cos(2.0 * math.pi * val)

        def sin_phase(x: int, p: PhaseFn = phase) -> float | None:
            val = p(x)
            return None if val is None else math.sin(2.0 * math.pi * val)

        for a in FOURIER_AMPS:
            for b in FOURIER_AMPS:
                n_tried += 1
                rec = _score_combo(pairs, [cos_phase, sin_phase], (a, b))
                if rec is None:
                    continue
                rec = {**rec, "kind": "fourier", "phase": name}
                if best is None or rec["min_drift"] > best["min_drift"]:
                    best = rec
    return {"n_tried": n_tried, "best": best}


def even_dphase_wings(lo: int, hi: int) -> dict[str, Any]:
    """Sign-indefiniteness of Δ{ξ} on even one-steps, including squares."""

    named: dict[str, PhaseFn] = {
        "sqrt": frac_sqrt,
        "three_halves": frac_three_halves,
        "fourth": frac_fourth,
        "pi_log2": lambda x: frac_log2(x, math.pi),
    }
    out: dict[str, Any] = {}
    evens = [n for n in range(max(lo, MIN_X), hi + 1) if n % 2 == 0]
    for name, phase in named.items():
        incs: list[float] = []
        for n in evens:
            y = floor_power(n)
            if y < 3:
                continue
            inc = dphase(n, y, phase)
            if inc is not None:
                incs.append(inc)
        if not incs:
            continue
        out[name] = {
            "min": min(incs),
            "max": max(incs),
            "n": len(incs),
            "n_pos": sum(1 for v in incs if v > 0.05),
            "n_neg": sum(1 for v in incs if v < -0.05),
            "n_tiny": sum(1 for v in incs if abs(v) < 0.02),
            "both_wings": (
                min(incs) < -0.05 and max(incs) > 0.05
            ),
        }
    return out


def _round_best(rec: dict[str, Any] | None) -> dict[str, Any] | None:
    if rec is None:
        return None
    out = dict(rec)
    out["min_drift"] = round(float(rec["min_drift"]), 8)
    return out


def family_report(pairs: list[tuple[int, int]]) -> dict[str, Any]:
    base = baseline(pairs)
    saw = search_sawtooth(pairs)
    named = search_named_sawtooth(pairs)
    basis = search_basis(pairs)
    fourier = search_fourier(pairs)
    coverage = max(MIN_FAMILY, (len(pairs) + 1) // 2)

    def _covered(rec: dict[str, Any] | None) -> bool:
        return rec is not None and rec["n_used"] >= min(len(pairs), coverage)

    candidates = [
        r["best"]
        for r in (saw, named, basis, fourier)
        if _covered(r.get("best"))
    ]
    if not candidates and base is not None:
        candidates = [base]
    best = max(candidates, key=lambda r: r["min_drift"]) if candidates else None
    return {
        "n_pairs": len(pairs),
        "baseline": _round_best(base),
        "sawtooth": {**saw, "best": _round_best(saw.get("best"))},
        "named": {**named, "best": _round_best(named.get("best"))},
        "basis": {**basis, "best": _round_best(basis.get("best"))},
        "fourier": {**fourier, "best": _round_best(fourier.get("best"))},
        "best": _round_best(best),
    }


def _is_zero_correction(best: dict[str, Any] | None) -> bool:
    if best is None:
        return True
    if abs(float(best.get("amp", 1.0))) < 1e-15 and "amps" not in best:
        return True
    amps = best.get("amps")
    if amps is not None and all(abs(float(a)) < 1e-15 for a in amps):
        return True
    return False


def _rescues(family: dict[str, Any]) -> bool:
    """A non-zero ψ lifts a genuinely negative family of useful size."""

    best = family.get("best")
    base = family.get("baseline")
    if best is None or base is None:
        return False
    if best["n_used"] < MIN_FAMILY or base["n_used"] < MIN_FAMILY:
        return False
    if float(base["min_drift"]) >= 0.0:
        return False
    if _is_zero_correction(best):
        return False
    return float(best["min_drift"]) >= 0.0


def classify(payload: dict[str, Any]) -> str:
    if payload["obstruction"]["leading_sum"] != -payload["obstruction"]["depth"]:
        return CLASS_INCOMPLETE
    if any(_rescues(fam) for fam in payload["families"].values()):
        return CLASS_CANDIDATE
    return CLASS_DEFEATED


def build_summary(n_max: int = SCIENCE_N_MAX) -> dict[str, Any]:
    families_pairs = collect_families(MIN_X, n_max, extra_starts=HIGH_FLYERS)
    families = {name: family_report(pairs) for name, pairs in families_pairs.items()}
    obstruction = one_step_bounded_psi_obstruction()
    wings = even_dphase_wings(MIN_X, n_max)
    adversaries = [adversary_prefix_report(n) for n in ADVERSARY_STARTS]
    payload: dict[str, Any] = {
        "experiment": "juggler_walk_coboundary",
        "anti_overclaim": ANTI,
        "n_max": n_max,
        "min_x": MIN_X,
        "fan_len": FAN_LEN,
        "obstruction": obstruction,
        "adversaries": adversaries,
        "even_dphase_wings": wings,
        "families": families,
        "notes": {
            "phi": "Φ = log2(ln x) + ψ(ξ(x)); drift = Φ(J(x)) − Φ(x) or a block analogue",
            "one_step": (
                "any bounded ψ fails on the even-square tower: leading is "
                "exactly −1 and the telescoping correction is bounded"
            ),
            "fan": (
                "length-19 sliding blocks on AboveAnchor prefixes: the fan "
                "scale where the leading cocycle is nearly neutral"
            ),
            "discovery": (
                "a candidate is a bounded-complexity ψ with min drift >= 0 "
                "on a family; the even-square identity already kills one-step"
            ),
        },
    }
    payload["classification"] = classify(payload)
    payload["decision"] = (
        "CLOSE" if payload["classification"] == CLASS_DEFEATED else (
            "PROMOTE" if payload["classification"] == CLASS_CANDIDATE else "PARK"
        )
    )
    return payload


def write_artifacts(n_max: int = SCIENCE_N_MAX) -> dict[str, Any]:
    payload = build_summary(n_max)
    DATA_DIR.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2, allow_nan=False) + "\n", encoding="utf-8")
    return payload


def main(n_max: int = SCIENCE_N_MAX) -> dict[str, Any]:
    payload = write_artifacts(n_max)
    families = payload["families"]
    print(
        json.dumps(
            {
                "classification": payload["classification"],
                "decision": payload["decision"],
                "n_max": payload["n_max"],
                "obstruction_leading_sum": payload["obstruction"]["leading_sum"],
                "adversaries": payload["adversaries"],
                "wings_both": {
                    name: rec["both_wings"]
                    for name, rec in payload["even_dphase_wings"].items()
                },
                "best": {
                    name: families[name]["best"]
                    for name in families
                },
                "baseline": {
                    name: families[name]["baseline"]
                    for name in families
                },
            },
            indent=2,
        )
    )
    return payload


if __name__ == "__main__":
    main()
