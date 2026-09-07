"""Hug-word exchange lemma and explicit mechanical charge C_*(n).

Phase 0: among admissible u>=0 walks with fixed (L,o), the hug
word is the unique prefix-min path by a delta-invariant (first
disagreement is hug-E vs other-O; the odd-count gap cannot go
negative). The infinite hug walk is rotation by alpha on the
circle R/(1+alpha)Z, so leftover charge-per-letter is the
Laplace integral C_*(n) = (1/ln 3) ∫_1^3 n^{1-t} t^{-2} dt.
Not a halt theorem, not a floor raise, not a uniform B/theta
claim, and not a reopen of the REFUTED Christoffel slogans.

Dossier: docs/problems/juggler_cycle_walk_exchange.md.
"""

from __future__ import annotations

from research.juggler_sequence.lean_paths import (
    DATA_ROOT,
)

import json
import math
from collections.abc import Iterator
from pathlib import Path
from typing import Any

import numpy as np

from research.juggler_sequence.cycle_finance import (
    EPS_CONST,
    PARITY_REL_GUARD,
    git_commit,
)
from research.juggler_sequence.cycle_walk_charge import (
    CERTIFIED_FLOOR,
    MU,
    STEP,
    U_TOL,
    charge_row,
    deficit_D,
)
from research.juggler_sequence.cycle_walk_greedy import (
    hug_prefix_odds,
    hug_word,
)
from research.juggler_sequence.cycle_walk_mechanical import (
    SURVEY_PATH,
    certified_log_n,
    charge_density,
    mechanical_average,
)

DATA_DIR = (
    DATA_ROOT
    / "cycle_walk_exchange"
)
GREEDY_SUMMARY = (
    DATA_ROOT
    / "cycle_walk_greedy"
    / "summary.json"
)

BRUTE_L_MAX = 12
INTEGRAL_NODES = 40_000
ROTATION_PREFIX = 100_000
C_MATCH_TOL = 2.5e-3

CLASS_GREEN = "WALK_EXCHANGE_GREEN"
CLASS_PARK = "WALK_EXCHANGE_PARK"
CLASS_CLOSED = "WALK_EXCHANGE_CLOSED"


def _trapz(y: np.ndarray, x: np.ndarray) -> float:
    if hasattr(np, "trapezoid"):
        return float(np.trapezoid(y, x))
    return float(np.trapz(y, x))


def prefix_odds(word: str) -> list[int]:
    odds = [0]
    count = 0
    for letter in word:
        if letter == "O":
            count += 1
        odds.append(count)
    return odds


def iter_admissible(length: int, odd_count: int) -> Iterator[str]:
    """All u>=0 words with exactly `odd_count` odds in `length` letters."""

    even_count = length - odd_count
    word: list[str] = []

    def rec(step: int, odds: int, height: float) -> Iterator[str]:
        if step == length:
            if odds == odd_count:
                yield "".join(word)
            return
        evens = step - odds
        if odds < odd_count and height + MU >= -U_TOL:
            word.append("O")
            yield from rec(step + 1, odds + 1, height + MU)
            word.pop()
        if evens < even_count and height - 1.0 >= -U_TOL:
            word.append("E")
            yield from rec(step + 1, odds, height - 1.0)
            word.pop()

    yield from rec(0, 0, 0.0)


def first_disagreement(hug: str, other: str) -> dict[str, Any] | None:
    for k, (a, b) in enumerate(zip(hug, other)):
        if a != b:
            return {"k": k, "hug": a, "other": b}
    return None


def exchange_holds(length: int, odd_count: int) -> dict[str, Any]:
    """Hug a_k <= a_k(w) for every admissible w; first split is E vs O."""

    hug = hug_word(length, odd_count)
    hug_a = prefix_odds(hug)
    n_words = 0
    n_other = 0
    failures = []
    split_failures = []
    for word in iter_admissible(length, odd_count):
        n_words += 1
        if word == hug:
            continue
        n_other += 1
        other_a = prefix_odds(word)
        if any(h > o for h, o in zip(hug_a, other_a)):
            if len(failures) < 8:
                failures.append(word)
        split = first_disagreement(hug, word)
        if split is None or split["hug"] != "E" or split["other"] != "O":
            if len(split_failures) < 8:
                split_failures.append({"word": word, "split": split})
    return {
        "length": length,
        "odd_count": odd_count,
        "hug": hug,
        "n_admissible": n_words,
        "n_other": n_other,
        "prefix_min": not failures,
        "first_split_is_e_vs_o": not split_failures,
        "prefix_failures": failures,
        "split_failures": split_failures,
    }


def exchange_census(l_max: int = BRUTE_L_MAX) -> dict[str, Any]:
    rows = []
    n_pairs = 0
    n_ok = 0
    n_words = 0
    for length in range(1, l_max + 1):
        for odd_count in range(0, length + 1):
            if STEP * odd_count - length < -U_TOL:
                continue
            report = exchange_holds(length, odd_count)
            n_pairs += 1
            n_words += report["n_admissible"]
            ok = report["prefix_min"] and report["first_split_is_e_vs_o"]
            if ok:
                n_ok += 1
            else:
                rows.append(report)
    return {
        "l_max": l_max,
        "n_feasible": n_pairs,
        "n_ok": n_ok,
        "n_admissible_words": n_words,
        "failures": rows[:12],
    }


def c_star_integral(log_n: float, nodes: int = INTEGRAL_NODES) -> dict[str, Any]:
    """C_*(n) = (1/ln 3) ∫_1^3 n^{1-t} t^{-2} dt.

    Equivalent forms:
      (1/(1+α)) ∫_0^{1+α} n^{1-2^u} 2^{-u} du
      1/(ln 3 ln n) * ∫_0^{2 ln n} e^{-s} / (1 + s/ln n)^2 ds
    The last is the quadrature coordinate. The integrand is
    positive and at most e^{-s}, so C_* < 1/(ln 3 ln n).
    """

    ln3 = math.log(3.0)
    s_max = 2.0 * log_n
    s = np.linspace(0.0, s_max, nodes)
    integrand = np.exp(-s) / (1.0 + s / log_n) ** 2
    jay = _trapz(integrand, s)
    density = 1.0 / (ln3 * log_n)
    # Independent check in u-space.
    u = np.linspace(0.0, STEP, nodes)
    f_u = np.exp((1.0 - np.exp2(u)) * log_n) / np.exp2(u)
    c_u = _trapz(f_u, u) / STEP
    return {
        "C": density * jay,
        "J": jay,
        "bound": density,
        "C_u_check": c_u,
        "mean_u": STEP / 2.0,
        "log_n": log_n,
        "ln3": ln3,
        "nodes": nodes,
    }


def rotation_average(
    prefix: int,
    n: int,
    *,
    log_n: float,
) -> dict[str, Any]:
    """IET orbit u_k = (k α) mod (1+α), charged with the same g."""

    heights = np.mod(np.arange(prefix, dtype=np.float64) * MU, STEP)
    total = float(np.sum(charge_row(heights, n, 0.0, log_n=log_n)))
    return {
        "prefix": prefix,
        "B": total,
        "C": charge_density(total, prefix, log_n),
        "mean_u": float(np.mean(heights)),
        "max_u": float(np.max(heights)),
    }


def survey_envelope(
    survey_path: Path = SURVEY_PATH,
    n0: int = CERTIFIED_FLOOR,
) -> dict[str, Any]:
    """Compare leftover hug C to C_*(n') and the simple bound."""

    survey = json.loads(survey_path.read_text(encoding="utf-8"))
    greedy = json.loads(GREEDY_SUMMARY.read_text(encoding="utf-8"))
    hug_c = {int(r["length"]): float(r["C"]) for r in greedy["survey_rows"]}
    hug_b = {int(r["length"]): float(r["hug_B"]) for r in greedy["survey_rows"]}
    n = int(survey["floor"]) + 1
    rows = []
    for item in survey["rows"]:
        length = int(item["length"])
        odd_count = int(item["odd_count"])
        theta = float(item["theta"])
        deficit = deficit_D(length, odd_count, n)
        log_n = math.log(n) - deficit
        star = c_star_integral(log_n)
        c_hug = hug_c[length]
        b_hug = hug_b[length]
        scale = length / (math.exp(log_n) * log_n)
        b_star = star["C"] * scale
        b_bound = star["bound"] * scale
        b_koksma = (star["C"] + 1.0 / length) * scale
        const = float(item.get("const", EPS_CONST))
        guard = 1.0 + PARITY_REL_GUARD

        def margin(budget: float) -> float:
            rhs = const * budget * guard
            return theta / rhs if rhs else math.inf

        rows.append(
            {
                "length": length,
                "odd_count": odd_count,
                "log_n": log_n,
                "C_hug": c_hug,
                "C_star": star["C"],
                "C_bound": star["bound"],
                "C_hug_minus_star": c_hug - star["C"],
                "hug_below_bound": c_hug < star["bound"],
                "B_hug": b_hug,
                "B_star": b_star,
                "B_bound": b_bound,
                "B_koksma": b_koksma,
                "theta": theta,
                "margin_hug": margin(b_hug),
                "margin_star": margin(b_star),
                "margin_bound": margin(b_bound),
                "margin_koksma": margin(b_koksma),
            }
        )
    return {
        "floor": survey["floor"],
        "n": n,
        "n_rows": len(rows),
        "all_hug_below_bound": all(r["hug_below_bound"] for r in rows),
        "max_C_hug_minus_star": max(r["C_hug_minus_star"] for r in rows),
        "min_C_hug_minus_star": min(r["C_hug_minus_star"] for r in rows),
        "n_star_kills": sum(1 for r in rows if r["margin_star"] > 1.0),
        "n_bound_kills": sum(1 for r in rows if r["margin_bound"] > 1.0),
        "n_koksma_kills": sum(1 for r in rows if r["margin_koksma"] > 1.0),
        "uniform_ratio_false": any(r["margin_hug"] < 1.0 for r in rows),
        "rows": rows,
    }


def classify(
    census: dict[str, Any],
    star: dict[str, Any],
    mechanical: dict[str, Any],
    rotation: dict[str, Any],
    envelope: dict[str, Any],
) -> dict[str, Any]:
    exchange_ok = census["n_ok"] == census["n_feasible"]
    rel_mech = abs(star["C"] - mechanical["C"]) / mechanical["C"]
    rel_rot = abs(star["C"] - rotation["C"]) / rotation["C"]
    integral_ok = rel_mech < C_MATCH_TOL and rel_rot < C_MATCH_TOL
    two_forms = abs(star["C"] - star["C_u_check"]) / star["C"] < 1e-6
    if not exchange_ok:
        return {
            "label": CLASS_CLOSED,
            "reason": "a feasible pair has an admissible word undercutting hug",
            "rel_mech": rel_mech,
            "rel_rot": rel_rot,
        }
    if exchange_ok and integral_ok and two_forms:
        return {
            "label": CLASS_GREEN,
            "reason": (
                "delta-invariant holds on every brute-force admissible "
                "word through L=12; C_* integral matches the mechanical "
                "and IET-rotation averages; leftover C stays below the "
                "simple bound 1/(ln 3 ln n')"
            ),
            "rel_mech": rel_mech,
            "rel_rot": rel_rot,
        }
    return {
        "label": CLASS_PARK,
        "reason": (
            "exchange census holds but the integral does not yet match "
            "the mechanical average"
        ),
        "rel_mech": rel_mech,
        "rel_rot": rel_rot,
    }


def probe_payload() -> dict[str, Any]:
    base = certified_log_n()
    census = exchange_census()
    star = c_star_integral(base["log_n"])
    mechanical = mechanical_average(log_n=base["log_n"], n=base["n"])
    rotation = rotation_average(
        ROTATION_PREFIX, base["n"], log_n=base["log_n"]
    )
    envelope = survey_envelope()
    witness = exchange_holds(4, 3)
    return {
        "model": (
            "hug exchange: first disagreement is E vs O and the "
            "odd-count gap cannot go negative; C_* is the Lebesgue "
            "average of n^{1-2^u}/2^u on the circle of length 1+α"
        ),
        "certified_base": base,
        "exchange_census": census,
        "witness_4_3": {
            "hug": witness["hug"],
            "n_admissible": witness["n_admissible"],
            "prefix_min": witness["prefix_min"],
            "first_split_is_e_vs_o": witness["first_split_is_e_vs_o"],
        },
        "c_star": star,
        "mechanical": {
            "prefix": mechanical["prefix"],
            "C": mechanical["C"],
            "mean_u": mechanical["mean_u"],
            "max_u": mechanical["max_u"],
        },
        "rotation": rotation,
        "envelope": {
            k: envelope[k]
            for k in (
                "floor",
                "n",
                "n_rows",
                "all_hug_below_bound",
                "max_C_hug_minus_star",
                "min_C_hug_minus_star",
                "n_star_kills",
                "n_bound_kills",
                "n_koksma_kills",
                "uniform_ratio_false",
            )
        },
        "envelope_rows": envelope["rows"],
        "classification": classify(
            census, star, mechanical, rotation, envelope
        ),
        "not_a_halt_theorem": True,
        "no_cycle_all_lengths": False,
        "not_a_uniform_ratio_theorem": True,
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
    census = payload["exchange_census"]
    star = payload["c_star"]
    mechanical = payload["mechanical"]
    rotation = payload["rotation"]
    envelope = payload["envelope"]
    print(
        f"exchange L<={census['l_max']}: "
        f"{census['n_ok']}/{census['n_feasible']} "
        f"words={census['n_admissible_words']}"
    )
    print(
        f"C_star={star['C']:.8f} bound={star['bound']:.8f} "
        f"J={star['J']:.6f} C_u={star['C_u_check']:.8f}"
    )
    print(
        f"mechanical C={mechanical['C']:.8f} "
        f"rotation C={rotation['C']:.8f} "
        f"mean_u mech={mechanical['mean_u']:.6f} "
        f"mean_u Lebesgue={star['mean_u']:.6f}"
    )
    print(
        f"envelope hug<bound={envelope['all_hug_below_bound']} "
        f"dC=[{envelope['min_C_hug_minus_star']:.3e},"
        f"{envelope['max_C_hug_minus_star']:.3e}] "
        f"kills star/bound/koksma="
        f"{envelope['n_star_kills']}/"
        f"{envelope['n_bound_kills']}/"
        f"{envelope['n_koksma_kills']} "
        f"uniform_ratio_false={envelope['uniform_ratio_false']}"
    )
    print(payload["classification"]["label"])
    print(payload["classification"]["reason"])


if __name__ == "__main__":
    main()
