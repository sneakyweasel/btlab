"""Normalized Juggler defect. Not a termination theorem.

The preferred dimensionless object is the relative slack
``1 + q = n^{3^o} / T_w(n)^{2^k}``. Concatenation multiplies these
ratios. The surplus ratio ``R = Δ / (n^{3^o} - n^{2^k})`` is a
derived coordinate that encodes ``T_w(n) ≥ n`` whenever the
denominator is positive.
"""

from __future__ import annotations

from typing import Any

from research.juggler_sequence.defect_lower_bound import first_defect
from research.juggler_sequence.global_defect import (
    follows_itinerary,
    global_defect,
    image_after,
    itinerary_word,
    local_defect,
    odd_count,
)
from research.juggler_sequence.lean_paths import has_named, juggler_text
from research.juggler_sequence.power_itineraries import floor_power
from research.juggler_sequence.progress_coverage import is_odd_odd
from research.juggler_sequence.residual_chain import (
    CHAIN_CAP,
    HARD_PROBES,
    N_MAX,
    residual_chain,
    residual_excursion,
)

BIT_LIMIT = 4096

LEAN_THEOREMS = (
    "slackNum",
    "slackDen",
    "relativeSlack",
    "onePlusSlack",
    "formalSurplus",
    "defectRatio",
    "normalizedLocalDefect",
    "slack_identity",
    "onePlusSlack_concat",
    "relative_slack_even",
    "relative_slack_odd",
    "defectRatio_le_one_iff_image_ge",
    "onePlusSlack_ge_of_prefix",
    "image_eq_start_defectRatio",
    "residualStep_relative_slack",
    "residualStep_onePlusSlack_concat",
    "persistent_odd_residual_defect_pos",
)


def odd_even_word(a: int, b: int) -> str:
    return "O" * a + "E" * b


def bits_ok(base: int, exp: int, *, bit_limit: int = BIT_LIMIT) -> bool:
    if exp < 0 or base < 0:
        raise ValueError("bits_ok requires nonnegative base and exponent")
    if exp == 0 or base <= 1:
        return True
    return base.bit_length() * exp <= bit_limit


def slack_num(n: int, word: str) -> int:
    return n ** (3 ** odd_count(word))


def slack_den(n: int, word: str) -> int:
    return image_after(n, word) ** (2 ** len(word))


def one_plus_slack(n: int, word: str) -> tuple[int, int]:
    return slack_num(n, word), slack_den(n, word)


def relative_slack(n: int, word: str) -> tuple[int, int]:
    """Nat pair ``(Δ, T^{2^k})``. The ratio is ``q``."""
    return global_defect(n, word), slack_den(n, word)


def formal_surplus(n: int, word: str) -> int:
    """Signed integer surplus. Negative when the word is exponent-contracting."""
    return n ** (3 ** odd_count(word)) - n ** (2 ** len(word))


def defect_ratio(n: int, word: str) -> tuple[int, int] | None:
    """Exact pair ``(Δ, S)`` when ``S > 0``; otherwise undefined."""
    surplus = formal_surplus(n, word)
    if surplus <= 0:
        return None
    return global_defect(n, word), surplus


def eta_pair(x: int) -> tuple[int, int]:
    y = floor_power(x)
    return local_defect(x), y * y


def concat_product_holds(n: int, u: str, v: str) -> bool:
    mid = image_after(n, u)
    left = (
        slack_num(n, u + v)
        * slack_den(n, u) ** (3 ** odd_count(v))
        * slack_den(mid, v) ** (2 ** len(u))
    )
    right = (
        slack_num(n, u) ** (3 ** odd_count(v))
        * slack_num(mid, v) ** (2 ** len(u))
        * slack_den(n, u + v)
    )
    return left == right


def one_step_holds(n: int, word: str, letter: str) -> bool:
    if not follows_itinerary(n, word + letter):
        return False
    mid = image_after(n, word)
    eta_num, eta_den = eta_pair(mid)
    q_num, q_den = slack_num(n, word), slack_den(n, word)
    nxt = word + letter
    factor = 3 if letter == "O" else 1
    left = slack_num(n, nxt) * (q_den**factor) * (eta_den ** (2 ** len(word)))
    right = (q_num**factor) * ((eta_den + eta_num) ** (2 ** len(word))) * slack_den(
        n, nxt
    )
    return left == right


def measurable(n: int, word: str, *, bit_limit: int = BIT_LIMIT) -> bool:
    if not follows_itinerary(n, word):
        return False
    o = odd_count(word)
    k = len(word)
    end = image_after(n, word)
    return bits_ok(n, 3**o, bit_limit=bit_limit) and bits_ok(
        end, 2**k, bit_limit=bit_limit
    )


def identity_census(*, n_max: int = 40, k_max: int = 4) -> dict[str, Any]:
    concat_fail = 0
    step_fail = 0
    identity_fail = 0
    q_mono_fail = 0
    checked = 0
    for n in range(1, n_max + 1):
        for k in range(0, k_max + 1):
            word = itinerary_word(n, k)
            checked += 1
            num, den = one_plus_slack(n, word)
            if num != den + global_defect(n, word):
                identity_fail += 1
            for split in range(k + 1):
                u, v = word[:split], word[split:]
                if not concat_product_holds(n, u, v):
                    concat_fail += 1
                if u and den > 0 and slack_den(n, u) > 0:
                    left = slack_num(n, word) * slack_den(n, u)
                    right = slack_num(n, u) * slack_den(n, word)
                    if left < right:
                        q_mono_fail += 1
            if k >= 1:
                prefix, letter = word[:-1], word[-1]
                if not one_step_holds(n, prefix, letter):
                    step_fail += 1
    return {
        "n_max": n_max,
        "k_max": k_max,
        "checked": checked,
        "identity_fail": identity_fail,
        "concat_fail": concat_fail,
        "step_fail": step_fail,
        "q_mono_fail": q_mono_fail,
    }


def _ratio_float(pair: tuple[int, int] | None) -> float | None:
    if pair is None:
        return None
    num, den = pair
    return num / den


def _step_record(x: int, step: dict[str, Any]) -> dict[str, Any] | None:
    word = odd_even_word(step["a"], step["b"])
    if not measurable(x, word):
        return None
    y = step["y"]
    delta = global_defect(x, word)
    surplus = formal_surplus(x, word)
    den = slack_den(x, word)
    ratio = defect_ratio(x, word)
    eta_num, eta_den = eta_pair(x)
    return {
        "x": x,
        "y": y,
        "a": step["a"],
        "b": step["b"],
        "word": word,
        "delta": delta,
        "surplus": surplus,
        "q_num": delta,
        "q_den": den,
        "q": (delta / den) if den else None,
        "R": _ratio_float(ratio),
        "eta": (eta_num / eta_den) if eta_den else None,
        "eta_num": eta_num,
        "eta_den": eta_den,
        "first_defect": first_defect(x, word),
        "expanding": surplus > 0,
        "persistent": y > x and y >= 2 and is_odd_odd(y),
        "x_odd_odd": x >= 2 and is_odd_odd(x),
    }


def persistent_census(
    *, n_max: int = N_MAX, chain_cap: int = CHAIN_CAP
) -> dict[str, Any]:
    starts = []
    for n in range(3, n_max + 1, 2):
        if is_odd_odd(n):
            starts.append(n)
    for n in HARD_PROBES:
        if n not in starts:
            starts.append(n)

    rows: list[dict[str, Any]] = []
    r_decreases: list[dict[str, Any]] = []
    q_decreases: list[dict[str, Any]] = []
    skipped = 0
    min_R = None
    min_R_row = None
    min_persistent_R = None
    min_persistent_R_row = None
    eta_vals: list[float] = []
    r_ratios: list[float] = []

    for start in starts:
        chain = residual_chain(start, max_steps=chain_cap)
        prev: dict[str, Any] | None = None
        for raw in chain:
            rec = _step_record(raw["x"], raw)
            if rec is None:
                skipped += 1
                prev = None
                continue
            rows.append(rec)
            if rec["eta"] is not None and rec["x_odd_odd"]:
                eta_vals.append(rec["eta"])
            if rec["R"] is not None:
                if min_R is None or rec["R"] < min_R:
                    min_R = rec["R"]
                    min_R_row = {
                        "x": rec["x"],
                        "y": rec["y"],
                        "word": rec["word"],
                        "R": rec["R"],
                    }
                if rec["persistent"] and (
                    min_persistent_R is None or rec["R"] < min_persistent_R
                ):
                    min_persistent_R = rec["R"]
                    min_persistent_R_row = {
                        "x": rec["x"],
                        "y": rec["y"],
                        "word": rec["word"],
                        "R": rec["R"],
                    }
            if prev is not None and raw["i"] > 0:
                both_expanding = prev["R"] is not None and rec["R"] is not None
                if both_expanding and prev["R"] > 0:
                    growth = rec["R"] / prev["R"]
                    r_ratios.append(growth)
                    if rec["R"] < prev["R"]:
                        r_decreases.append(
                            {
                                "start": start,
                                "x": prev["x"],
                                "y": rec["x"],
                                "z": rec["y"],
                                "word0": prev["word"],
                                "word1": rec["word"],
                                "R0": prev["R"],
                                "R1": rec["R"],
                                "growth": growth,
                                "both_persistent": bool(
                                    prev["persistent"] and rec["persistent"]
                                ),
                            }
                        )
                if (
                    prev["q"] is not None
                    and rec["q"] is not None
                    and rec["q"] < prev["q"]
                ):
                    q_decreases.append(
                        {
                            "start": start,
                            "x": prev["x"],
                            "y": rec["x"],
                            "q0": prev["q"],
                            "q1": rec["q"],
                            "word0": prev["word"],
                            "word1": rec["word"],
                            "both_persistent": bool(
                                prev["persistent"] and rec["persistent"]
                            ),
                        }
                    )
            prev = rec

    expanding_persistent = [
        row for row in rows if row["persistent"] and row["expanding"]
    ]
    return {
        "n_max": n_max,
        "chain_cap": chain_cap,
        "starts": len(starts),
        "rows": len(rows),
        "skipped": skipped,
        "persistent_rows": sum(1 for row in rows if row["persistent"]),
        "expanding_persistent": len(expanding_persistent),
        "r_decreases": len(r_decreases),
        "q_decreases": len(q_decreases),
        "r_decrease_examples": r_decreases[:8],
        "q_decrease_examples": q_decreases[:8],
        "min_R": min_R,
        "min_R_row": min_R_row,
        "min_persistent_R": min_persistent_R,
        "min_persistent_R_row": min_persistent_R_row,
        "min_eta_odd_odd": min(eta_vals) if eta_vals else None,
        "max_eta_odd_odd": max(eta_vals) if eta_vals else None,
        "r_growth_min": min(r_ratios) if r_ratios else None,
        "r_growth_max": max(r_ratios) if r_ratios else None,
        "persistent_examples": [
            {
                "x": row["x"],
                "y": row["y"],
                "word": row["word"],
                "R": row["R"],
                "q": row["q"],
                "eta": row["eta"],
                "first_defect": row["first_defect"],
            }
            for row in rows
            if row["persistent"]
        ],
    }


def prefix_ratio_census(*, n_max: int = 80, k_max: int = 6) -> dict[str, Any]:
    """Running surplus ratio along one word. ``R`` may fall when a
    later letter creates more formal surplus than defect."""
    decreases = 0
    checked = 0
    examples: list[dict[str, Any]] = []
    min_R = None
    min_row = None
    for n in range(2, n_max + 1):
        word = itinerary_word(n, k_max)
        prev_R = None
        for k in range(1, k_max + 1):
            prefix = word[:k]
            if not measurable(n, prefix):
                break
            pair = defect_ratio(n, prefix)
            if pair is None:
                prev_R = None
                continue
            checked += 1
            R = pair[0] / pair[1]
            if min_R is None or R < min_R:
                min_R = R
                min_row = {"n": n, "word": prefix, "R": R, "end": image_after(n, prefix)}
            if prev_R is not None and R < prev_R:
                decreases += 1
                if len(examples) < 8:
                    examples.append(
                        {
                            "n": n,
                            "u": prefix[:-1],
                            "uv": prefix,
                            "R_u": prev_R,
                            "R_uv": R,
                        }
                    )
            prev_R = R
    return {
        "checked": checked,
        "decreases": decreases,
        "examples": examples,
        "min_R": min_R,
        "min_row": min_row,
    }


def surplus_vs_image_scan(*, n_max: int = 60, k_max: int = 4) -> dict[str, Any]:
    """``R ≤ 1`` iff ``T ≥ n`` whenever ``S > 0``. Not a new obstruction."""
    fail = 0
    checked = 0
    for n in range(1, n_max + 1):
        for k in range(0, k_max + 1):
            word = itinerary_word(n, k)
            pair = defect_ratio(n, word)
            if pair is None:
                continue
            checked += 1
            delta, surplus = pair
            end = image_after(n, word)
            le_one = delta <= surplus
            if le_one != (n <= end):
                fail += 1
    return {"checked": checked, "fail": fail}


def lean_api_present() -> dict[str, bool]:
    text = juggler_text()
    return {
        "sorry_free": "sorry" not in text and "admit" not in text,
        **{name: has_named(text, name) for name in LEAN_THEOREMS},
    }
