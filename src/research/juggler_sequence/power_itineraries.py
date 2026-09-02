"""Standalone falsifier for canonical fixed-word Juggler power inequalities.

Not a Research Engine control-layer experiment. Not a termination or
divergence theorem. Not a parity-frequency theorem. Float logarithms
are a filter only; every comparison verdict is integer arithmetic.
"""

from __future__ import annotations

import json
import math
from collections import defaultdict
from dataclasses import asdict, dataclass, field
from fractions import Fraction
from math import gcd, isqrt
from pathlib import Path
from typing import Any, Iterable
from research.juggler_sequence.lean_paths import (
    ENVELOPE,
    juggler_text,
)

REPO_ROOT = Path(__file__).resolve().parents[3]
JSON_PATH = REPO_ROOT / "docs" / "research" / "juggler_power_itineraries.json"
DOC_PATH = REPO_ROOT / "docs" / "research" / "juggler_power_itineraries.md"
LEAN_PATH = ENVELOPE

K_MAX = 8
N_MAX = 10**6
K9_ODD_COUNT = 6
EXACT_POW_BITS = 4096
GAP_BITS = 4096
CALIBRATION_OOOEE = (3, 25, 39)
WORD_OOOEE = "OOOEE"
LEAN_MODULE = "Problems.Juggler.Envelope"
LEAN_OOOEEEOO = "floorPower_oooeeeoo_eight_step_lt"
LEAN_OOOEE = "floorPower_oooee_five_step_lt"
LOG_GRID = (2, 10, 100, 1000, 10_000, 100_000, 1_000_000)

CLASS_GREEN = "POWER_WORD_GREEN"
CLASS_ORDER = "POWER_WORD_ORDER_SENSITIVE"
CLASS_COUNTER = "POWER_WORD_COUNTEREXAMPLE"
CLASS_EXCEPTIONAL = "POWER_WORD_EXCEPTIONAL_DOMAIN"
H1 = "H1"
H2 = "H2"
H3 = "H3"

ANTI_OVERCLAIM = {
    "global_termination": False,
    "global_divergence": False,
    "every_trajectory_contains_word": False,
    "parity_frequency_theorem": False,
    "finite_macro_transition_grammar": False,
    "average_formal_energy_decreases": False,
    "floating_point_verdict": False,
}


def floor_power(n: int) -> int:
    """Exact even/odd floor-power successor. Stdlib isqrt only. No bit budget."""

    if n < 1:
        raise ValueError("floor_power is defined on positive integers")
    if n % 2 == 0:
        return isqrt(n)
    return isqrt(n * n * n)


def itinerary(n: int, steps: int) -> tuple[int, ...]:
    if steps < 0:
        raise ValueError("steps must be nonnegative")
    path = [n]
    current = n
    for _ in range(steps):
        current = floor_power(current)
        path.append(current)
    return tuple(path)


def word_of(path: tuple[int, ...]) -> str:
    if len(path) < 2:
        return ""
    return "".join("O" if item % 2 else "E" for item in path[:-1])


def odd_count(word: str) -> int:
    return word.count("O")


def formal_exponent(k: int, o: int) -> Fraction:
    return Fraction(3**o, 2**k)


def formal_exponent_str(k: int, o: int) -> str:
    return f"{3 ** o}/{2 ** k}"


def regime_of(k: int, o: int) -> str:
    left = 3**o
    right = 2**k
    if left < right:
        return "contracting"
    if left > right:
        return "expanding"
    return "critical"


def expected_direction(k: int, o: int) -> str:
    kind = regime_of(k, o)
    if kind == "contracting":
        return "<"
    if kind == "expanding":
        return ">"
    return "="


def direction_of(cmp: int) -> str:
    if cmp < 0:
        return "<"
    if cmp > 0:
        return ">"
    return "="


def cmp_pow(m: int, a: int, n: int, b: int) -> int:
    """Exact comparison of m**a versus n**b. Returns -1, 0, or 1.

    Bit-length sandwiches and integer powers decide. A float logarithm
    is used only to skip a huge `pow` when the margin is enormous; it
    is never the recorded verdict.
    """

    if a < 0 or b < 0:
        raise ValueError("exponents must be nonnegative")
    if m < 0 or n < 0:
        raise ValueError("bases must be nonnegative")
    if a == 0 and b == 0:
        return 0
    if a == 0:
        if n == 0:
            return 1
        if n == 1:
            return 0
        return -1
    if b == 0:
        if m == 0:
            return -1
        if m == 1:
            return 0
        return 1
    if m == 0 and n == 0:
        return 0
    if m == 0:
        return -1
    if n == 0:
        return 1
    if m == 1 and n == 1:
        return 0
    if m == 1:
        return -1
    if n == 1:
        return 1

    g = gcd(a, b)
    a //= g
    b //= g
    lm = m.bit_length()
    ln = n.bit_length()
    if (lm - 1) * a >= ln * b:
        return 1
    if lm * a <= (ln - 1) * b:
        return -1

    bits_left = lm * a
    bits_right = ln * b
    if bits_left <= EXACT_POW_BITS and bits_right <= EXACT_POW_BITS:
        left = pow(m, a)
        right = pow(n, b)
        return (left > right) - (left < right)

    left_log = a * math.log(m)
    right_log = b * math.log(n)
    err = (abs(left_log) + abs(right_log)) * 1e-10 + 1e-6
    if left_log > right_log + err:
        return 1
    if left_log < right_log - err:
        return -1
    left = pow(m, a)
    right = pow(n, b)
    return (left > right) - (left < right)


def maybe_delta(n: int, b: int, m: int, a: int) -> int | None:
    """Raw n**b - m**a when both powers fit in GAP_BITS, else None."""

    if n < 1 or m < 1:
        return None
    if n.bit_length() * b > GAP_BITS or m.bit_length() * a > GAP_BITS:
        return None
    return pow(n, b) - pow(m, a)


@dataclass
class FailureRecord:
    word: str
    n: int
    k: int
    odd_count: int
    formal_exponent: str
    m: int
    expected_direction: str
    actual_direction: str
    onesided_holds: bool

    def as_dict(self) -> dict[str, Any]:
        return asdict(self)


@dataclass
class ItineraryStats:
    word: str
    k: int
    odd_count: int
    formal_exponent: str
    regime: str
    expected_direction: str
    realizations: int = 0
    twosided_ok: int = 0
    onesided_ok: int = 0
    equalities: int = 0
    first_n: int | None = None
    first_twosided_failure: FailureRecord | None = None
    first_twosided_failure_n_gt_1: FailureRecord | None = None
    first_onesided_failure: FailureRecord | None = None
    first_equality: FailureRecord | None = None
    min_delta: int | None = None
    min_delta_n: int | None = None
    delta_negative_seen: bool = False
    log_grid_deltas: dict[str, int | None] = field(default_factory=dict)

    def as_dict(self) -> dict[str, Any]:
        data = asdict(self)
        if self.first_twosided_failure is not None:
            data["first_twosided_failure"] = self.first_twosided_failure.as_dict()
        if self.first_twosided_failure_n_gt_1 is not None:
            data["first_twosided_failure_n_gt_1"] = (
                self.first_twosided_failure_n_gt_1.as_dict()
            )
        if self.first_onesided_failure is not None:
            data["first_onesided_failure"] = self.first_onesided_failure.as_dict()
        if self.first_equality is not None:
            data["first_equality"] = self.first_equality.as_dict()
        return data


def _failure(
    word: str, n: int, k: int, o: int, m: int, expected: str, actual: str, onesided: bool
) -> FailureRecord:
    return FailureRecord(
        word=word,
        n=n,
        k=k,
        odd_count=o,
        formal_exponent=formal_exponent_str(k, o),
        m=m,
        expected_direction=expected,
        actual_direction=actual,
        onesided_holds=onesided,
    )


def _update_word(
    stats: dict[str, ItineraryStats],
    word: str,
    n: int,
    m: int,
    k: int,
    *,
    track_gap: bool,
) -> None:
    o = odd_count(word)
    item = stats.get(word)
    if item is None:
        item = ItineraryStats(
            word=word,
            k=k,
            odd_count=o,
            formal_exponent=formal_exponent_str(k, o),
            regime=regime_of(k, o),
            expected_direction=expected_direction(k, o),
        )
        stats[word] = item
    item.realizations += 1
    if item.first_n is None:
        item.first_n = n
    a = 1 << k
    b = 3**o
    cmp = cmp_pow(m, a, n, b)
    actual = direction_of(cmp)
    onesided = cmp <= 0
    expected = item.expected_direction
    if onesided:
        item.onesided_ok += 1
    elif item.first_onesided_failure is None:
        item.first_onesided_failure = _failure(
            word, n, k, o, m, expected, actual, False
        )
    if actual == "=":
        item.equalities += 1
        if item.first_equality is None:
            item.first_equality = _failure(word, n, k, o, m, expected, actual, onesided)
    if actual == expected:
        item.twosided_ok += 1
    else:
        rec = _failure(word, n, k, o, m, expected, actual, onesided)
        if item.first_twosided_failure is None:
            item.first_twosided_failure = rec
        if n > 1 and item.first_twosided_failure_n_gt_1 is None:
            item.first_twosided_failure_n_gt_1 = rec
    if not track_gap or item.regime != "contracting":
        return
    delta = maybe_delta(n, b, m, a)
    if delta is None:
        return
    if delta < 0:
        item.delta_negative_seen = True
    if item.min_delta is None or delta < item.min_delta:
        item.min_delta = delta
        item.min_delta_n = n
    if n in LOG_GRID:
        item.log_grid_deltas[str(n)] = delta


def closest_to_one(k_max: int = K_MAX) -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    for k in range(1, k_max + 1):
        best_o = min(range(k + 1), key=lambda o: abs(3**o - 2**k))
        rows.append(
            {
                "k": k,
                "odd_count": best_o,
                "ratio": formal_exponent_str(k, best_o),
                "distance_to_one_numer": abs(3**best_o - 2**k),
                "regime": regime_of(k, best_o),
            }
        )
    return rows


def oooee_calibration(seeds: Iterable[int] = CALIBRATION_OOOEE) -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    for seed in seeds:
        path = itinerary(seed, 5)
        word = word_of(path)
        m = path[-1]
        cmp = cmp_pow(m, 32, seed, 27)
        rows.append(
            {
                "n": seed,
                "path": list(path),
                "word": word,
                "m": m,
                "cmp_m32_n27": direction_of(cmp),
                "t5_lt_n": m < seed,
                "matches_oooee": word == WORD_OOOEE,
            }
        )
    return rows


def run_probe(
    n_max: int = N_MAX,
    k_max: int = K_MAX,
    *,
    include_k9: bool = True,
    track_gap: bool = True,
) -> dict[str, ItineraryStats]:
    if n_max < 1:
        raise ValueError("n_max must be positive")
    if k_max < 1:
        raise ValueError("k_max must be positive")
    stats: dict[str, ItineraryStats] = {}
    for n in range(1, n_max + 1):
        current = n
        chars: list[str] = []
        for _k in range(1, k_max + 1):
            chars.append("O" if current % 2 else "E")
            current = floor_power(current)
            _update_word(stats, "".join(chars), n, current, _k, track_gap=track_gap)
        if include_k9 and k_max >= 8:
            ninth = "O" if current % 2 else "E"
            o = odd_count("".join(chars)) + (1 if ninth == "O" else 0)
            if o == K9_ODD_COUNT:
                current = floor_power(current)
                _update_word(
                    stats, "".join(chars) + ninth, n, current, 9, track_gap=track_gap
                )
    return stats


def _group_key(item: ItineraryStats) -> tuple[int, int]:
    return (item.k, item.odd_count)


def permutation_analysis(stats: dict[str, ItineraryStats]) -> list[dict[str, Any]]:
    groups: dict[tuple[int, int], list[ItineraryStats]] = defaultdict(list)
    for item in stats.values():
        groups[_group_key(item)].append(item)
    rows: list[dict[str, Any]] = []
    for key in sorted(groups):
        items = sorted(groups[key], key=lambda s: s.word)
        realized = [s for s in items if s.realizations > 0]
        if not realized:
            continue
        twosided_fail_gt1 = [
            s.word for s in realized if s.first_twosided_failure_n_gt_1 is not None
        ]
        twosided_ok_gt1 = [
            s.word for s in realized if s.first_twosided_failure_n_gt_1 is None
        ]
        onesided_fail = [s.word for s in realized if s.first_onesided_failure is not None]
        onesided_ok = [s.word for s in realized if s.first_onesided_failure is None]
        exceptional_only = [
            s.word
            for s in realized
            if s.first_twosided_failure is not None
            and s.first_twosided_failure_n_gt_1 is None
        ]

        def _verdict(fail: list[str], ok: list[str], exceptional: list[str]) -> str:
            if fail and ok:
                return H2
            if fail:
                return H1
            if exceptional and not fail:
                return H3
            return H1

        rows.append(
            {
                "k": key[0],
                "odd_count": key[1],
                "ratio": formal_exponent_str(key[0], key[1]),
                "regime": regime_of(key[0], key[1]),
                "realized_words": [s.word for s in realized],
                "realized_count": len(realized),
                "twosided_fail_n_gt_1": twosided_fail_gt1,
                "twosided_ok_n_gt_1": twosided_ok_gt1,
                "twosided_exceptional_only": exceptional_only,
                "onesided_fail": onesided_fail,
                "onesided_ok": onesided_ok,
                "twosided_hypothesis": _verdict(
                    twosided_fail_gt1, twosided_ok_gt1, exceptional_only
                ),
                "onesided_hypothesis": H2 if onesided_fail and onesided_ok else H1,
                "oe_eo": key == (2, 1),
            }
        )
    return rows


def _onesided_holds(stats: dict[str, ItineraryStats]) -> bool:
    return all(s.first_onesided_failure is None for s in stats.values())


def _contracting_twosided_holds_n_ge_2(stats: dict[str, ItineraryStats]) -> bool:
    return all(
        s.first_twosided_failure_n_gt_1 is None
        for s in stats.values()
        if s.regime == "contracting"
    )


def _mixed_contracting_twosided_holds_n_ge_2(stats: dict[str, ItineraryStats]) -> bool:
    return all(
        s.first_twosided_failure_n_gt_1 is None
        for s in stats.values()
        if s.regime == "contracting" and s.odd_count >= 1
    )


def _pure_even_strict_failures(stats: dict[str, ItineraryStats]) -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    for item in stats.values():
        if item.odd_count != 0 or item.first_twosided_failure_n_gt_1 is None:
            continue
        rec = item.first_twosided_failure_n_gt_1.as_dict()
        rec["equalities"] = item.equalities
        rows.append(rec)
    rows.sort(key=lambda rec: (rec["k"], rec["n"]))
    return rows


def _expanding_twosided_fails(stats: dict[str, ItineraryStats]) -> bool:
    expanding = [s for s in stats.values() if s.regime == "expanding" and s.realizations]
    return bool(expanding) and all(
        s.first_twosided_failure_n_gt_1 is not None for s in expanding
    )


def _order_sensitive_onesided(perm: list[dict[str, Any]]) -> bool:
    return any(row["onesided_hypothesis"] == H2 for row in perm)


def classify_probe(
    stats: dict[str, ItineraryStats], perm: list[dict[str, Any]] | None = None
) -> dict[str, Any]:
    if perm is None:
        perm = permutation_analysis(stats)
    onesided = _onesided_holds(stats)
    contracting_ok = _contracting_twosided_holds_n_ge_2(stats)
    mixed_contracting_ok = _mixed_contracting_twosided_holds_n_ge_2(stats)
    expanding_fails = _expanding_twosided_fails(stats)
    order_onesided = _order_sensitive_onesided(perm)
    order_twosided = any(row["twosided_hypothesis"] == H2 for row in perm)
    even_square_fails = _pure_even_strict_failures(stats)

    onesided_h = H2 if order_onesided else H1
    if order_twosided:
        twosided_h = H2
    elif any(row["twosided_hypothesis"] == H3 for row in perm):
        twosided_h = H3
    else:
        twosided_h = H1

    if order_onesided or order_twosided:
        label = CLASS_ORDER
        reason = "two words with the same (k,o) disagree on a non-exceptional state"
    elif expanding_fails and onesided:
        label = CLASS_COUNTER
        reason = (
            "The two-sided exponent-only law fails: expanding itineraries obey the "
            "floor upper bound rather than the reverse inequality, and pure-even "
            "strict contraction fails with equality on perfect squares; the "
            "one-sided composition T^k(n)^{2^k} <= n^{3^o} holds independently of order"
        )
    elif not mixed_contracting_ok and twosided_h == H3:
        label = CLASS_EXCEPTIONAL
        reason = "directed failures are confined to n=1 or another named finite set"
    elif contracting_ok and not expanding_fails:
        label = CLASS_GREEN
        reason = "the directed canonical comparison survived on the tested domain"
    else:
        label = CLASS_COUNTER
        reason = "the directed canonical comparison has a non-exceptional counterexample"

    near_critical = _near_critical_survivors(stats)
    lean_word = _select_lean_target(stats, label, onesided, mixed_contracting_ok)
    return {
        "classification": label,
        "reason": reason,
        "twosided_hypothesis": twosided_h,
        "onesided_hypothesis": onesided_h,
        "onesided_holds": onesided,
        "contracting_twosided_holds_n_ge_2": contracting_ok,
        "mixed_contracting_twosided_holds_n_ge_2": mixed_contracting_ok,
        "expanding_twosided_fails": expanding_fails,
        "pure_even_strict_failures": even_square_fails,
        "near_critical_contracting_survivors": near_critical,
        "lean_gate_open": lean_word is not None,
        "lean_target_word": None if lean_word is None else lean_word["word"],
        "lean_target": lean_word,
    }


def _near_critical_survivors(stats: dict[str, ItineraryStats]) -> list[dict[str, Any]]:
    families = ((5, 3), (8, 5), (9, 6))
    rows: list[dict[str, Any]] = []
    for k, o in families:
        if regime_of(k, o) != "contracting":
            continue
        words = [
            s
            for s in stats.values()
            if s.k == k and s.odd_count == o and s.realizations > 0
        ]
        survived = [s for s in words if s.first_twosided_failure_n_gt_1 is None]
        rows.append(
            {
                "k": k,
                "odd_count": o,
                "ratio": formal_exponent_str(k, o),
                "realized": len(words),
                "survived_n_ge_2": len(survived),
                "first_surviving_word": None if not survived else min(s.word for s in survived),
                "first_failure": None
                if all(s.first_twosided_failure_n_gt_1 is None for s in words)
                else min(
                    (
                        s.first_twosided_failure_n_gt_1.as_dict()
                        for s in words
                        if s.first_twosided_failure_n_gt_1 is not None
                    ),
                    key=lambda rec: (rec["n"], rec["word"]),
                ),
            }
        )
    return rows


def _select_lean_target(
    stats: dict[str, ItineraryStats],
    label: str,
    onesided: bool,
    contracting_ok: bool,
) -> dict[str, Any] | None:
    if not onesided or not contracting_ok:
        return None
    if label == CLASS_ORDER:
        return None
    for k, o in ((8, 5), (5, 3), (9, 6)):
        candidates = [
            s
            for s in stats.values()
            if s.k == k
            and s.odd_count == o
            and s.regime == "contracting"
            and s.realizations > 0
            and s.first_twosided_failure_n_gt_1 is None
            and s.word != WORD_OOOEE
        ]
        if not candidates:
            continue
        best = min(candidates, key=lambda s: (s.first_n or 10**18, s.word))
        return {
            "word": best.word,
            "k": best.k,
            "odd_count": best.odd_count,
            "ratio": best.formal_exponent,
            "first_n": best.first_n,
            "reason": "near-critical contracting survivor distinct from OOOEE",
        }
    return None


PRIORITY_FAMILIES = (
    ("27/32", 5, 3),
    ("243/256", 8, 5),
    ("9/8", 3, 2),
    ("81/64", 6, 4),
    ("729/512", 9, 6),
)


def family_table(stats: dict[str, ItineraryStats]) -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    for name, k, o in PRIORITY_FAMILIES:
        words = [
            s
            for s in stats.values()
            if s.k == k and s.odd_count == o and s.realizations > 0
        ]
        first_fail = None
        fails = [
            s.first_twosided_failure_n_gt_1
            for s in words
            if s.first_twosided_failure_n_gt_1 is not None
        ]
        if fails:
            rec = min(fails, key=lambda r: (r.n, r.word))
            first_fail = rec.as_dict()
        rows.append(
            {
                "name": name,
                "k": k,
                "odd_count": o,
                "regime": regime_of(k, o),
                "realized_words": len(words),
                "realizations": sum(s.realizations for s in words),
                "twosided_survivors_n_ge_2": sum(
                    1 for s in words if s.first_twosided_failure_n_gt_1 is None
                ),
                "onesided_survivors": sum(
                    1 for s in words if s.first_onesided_failure is None
                ),
                "first_twosided_failure_n_gt_1": first_fail,
                "sample_words": [s.word for s in sorted(words, key=lambda s: s.word)[:8]],
            }
        )
    return rows


def first_counterexample_table(stats: dict[str, ItineraryStats], *, limit: int = 24) -> list[dict[str, Any]]:
    records = [
        s.first_twosided_failure_n_gt_1.as_dict()
        for s in stats.values()
        if s.first_twosided_failure_n_gt_1 is not None
    ]
    records.sort(key=lambda rec: (rec["k"], rec["n"], rec["word"]))
    return records[:limit]


def gap_summary(stats: dict[str, ItineraryStats]) -> dict[str, Any]:
    contracting = [s for s in stats.values() if s.regime == "contracting" and s.realizations]
    sign_change = [s.word for s in contracting if s.delta_negative_seen]
    with_delta = [s for s in contracting if s.min_delta is not None]
    smallest = None
    if with_delta:
        best = min(with_delta, key=lambda s: (s.min_delta, s.word))
        smallest = {
            "word": best.word,
            "min_delta": best.min_delta,
            "min_delta_n": best.min_delta_n,
            "log_grid_deltas": best.log_grid_deltas,
        }
    focus_words = ("EE", "OE", "EO", WORD_OOOEE)
    focus = []
    for word in focus_words:
        item = stats.get(word)
        if item is None:
            continue
        focus.append(
            {
                "word": word,
                "min_delta": item.min_delta,
                "min_delta_n": item.min_delta_n,
                "delta_negative_seen": item.delta_negative_seen,
                "equalities": item.equalities,
                "log_grid_deltas": item.log_grid_deltas,
            }
        )
    return {
        "contracting_words_with_raw_delta": len(with_delta),
        "delta_sign_changes": sign_change,
        "smallest_recorded_delta": smallest,
        "focus": focus,
    }


def lean_oooeeeoo_proved() -> bool:
    text = LEAN_PATH.read_text(encoding="utf-8")
    return (
        f"theorem {LEAN_OOOEEEOO}" in text
        and f"theorem {LEAN_OOOEE}" in text
        and "sorry" not in text
        and "admit" not in text
    )


def attach_lean(payload: dict[str, Any]) -> dict[str, Any]:
    proved = lean_oooeeeoo_proved()
    payload["lean_module"] = LEAN_MODULE
    payload["lean_theorem"] = LEAN_OOOEEEOO
    payload["lean_status"] = "PROVED" if proved else "UNPROVED"
    payload["lean_oooee_intact"] = f"theorem {LEAN_OOOEE}" in LEAN_PATH.read_text(
        encoding="utf-8"
    )
    return payload


def probe_payload(
    stats: dict[str, ItineraryStats],
    *,
    n_max: int,
    k_max: int,
    include_k9: bool,
) -> dict[str, Any]:
    perm = permutation_analysis(stats)
    decision = classify_probe(stats, perm)
    oe = next((row for row in perm if row["oe_eo"]), None)
    payload = {
        "experiment": "juggler_power_itineraries",
        "engine_control_layer_modified": False,
        "n_max": n_max,
        "k_max": k_max,
        "include_k9_family_729_512": include_k9,
        "anti_overclaim": dict(ANTI_OVERCLAIM),
        "oooee_calibration": oooee_calibration(),
        "closest_to_one": closest_to_one(k_max),
        "priority_families": family_table(stats),
        "first_counterexamples": first_counterexample_table(stats),
        "permutation_analysis": perm,
        "oe_eo": oe,
        "gap_summary": gap_summary(stats),
        "decision": decision,
        "word_count": len(stats),
        "realized_word_count": sum(1 for s in stats.values() if s.realizations),
        "onesided_failures": [
            s.first_onesided_failure.as_dict()
            for s in stats.values()
            if s.first_onesided_failure is not None
        ],
        "n1_all_odd": {
            "word": "O" * min(k_max, 8),
            "path": list(itinerary(1, min(k_max, 8))),
            "note": "T(1)=1; 1^a = 1^b; both strict directions fail; one-sided <= holds",
        },
    }
    return attach_lean(payload)


def render_markdown(payload: dict[str, Any]) -> str:
    decision = payload["decision"]
    lines: list[str] = [
        "# Juggler fixed-word power inequalities",
        "",
        f"Status: **{decision['classification']}**",
        "",
        "Standalone computational falsifier. Not a Research Engine control-layer",
        "experiment, not a termination theorem, not a divergence theorem, and not",
        "a parity-frequency theorem. `OOOEE` is a calibration example.",
        "",
        "## Branch budget",
        "",
        "```text",
        "Mathematical target     Do fixed parity-word compositions obey the canonical",
        "                        integer-power comparison T^k(n)^{2^k} ≶ n^{3^o} with",
        "                        the sign of 3^o vs 2^k, independently of letter order?",
        "Novelty hypothesis      The OOOEE exponents 32 vs 27 are the general (k,o)",
        "                        shadow of floor-power composition, not a lucky word.",
        "Falsifier               A realizing n whose first |w| bits are w and whose",
        "                        power comparison has the opposite sign; or two words",
        "                        with the same (k,o) and different behaviour.",
        "Existing machinery      math.isqrt Juggler step; FloorPower.lean (OE, OO,",
        "                        OOOEE); Phase-12 calibration on n in {3,25,39}.",
        "Maximum Phase-0 scope   Exhaustive |w|<=8 on 1<=n<=N, plus a targeted",
        "                        (k,o)=(9,6) scan for 729/512. No engine-control edits.",
        "```",
        "",
        "## Metadata",
        "",
        f"- n_max: `{payload['n_max']}`",
        f"- k_max: `{payload['k_max']}`",
        f"- targeted k=9 family 729/512: `{payload['include_k9_family_729_512']}`",
        f"- engine control layer modified: `{payload['engine_control_layer_modified']}`",
        f"- classification: **{decision['classification']}**",
        f"- two-sided hypothesis: `{decision['twosided_hypothesis']}`",
        f"- one-sided hypothesis: `{decision['onesided_hypothesis']}`",
        f"- one-sided floor composition holds: `{decision['onesided_holds']}`",
        f"- contracting two-sided holds for n>=2: `{decision['contracting_twosided_holds_n_ge_2']}`",
        f"- mixed contracting two-sided holds for n>=2: `{decision.get('mixed_contracting_twosided_holds_n_ge_2')}`",
        f"- expanding two-sided fails: `{decision['expanding_twosided_fails']}`",
        f"- Lean gate open: `{decision['lean_gate_open']}`",
        f"- Lean target word: `{decision['lean_target_word']}`",
        f"- Lean status: `{payload.get('lean_status', 'UNPROVED')}`",
        f"- Lean theorem: `{payload.get('lean_theorem')}`",
        "",
        decision["reason"] + ".",
        "",
        "## OOOEE calibration",
        "",
        "| n | word | m = T^5(n) | m^32 ? n^27 | T^5(n)<n |",
        "| --- | --- | --- | --- | --- |",
    ]
    for row in payload["oooee_calibration"]:
        lines.append(
            f"| {row['n']} | `{row['word']}` | {row['m']} | `{row['cmp_m32_n27']}` | `{row['t5_lt_n']}` |"
        )
    lines.extend(
        [
            "",
            "## Closest formal exponent to 1",
            "",
            "| k | o | 3^o / 2^k | |3^o-2^k| | regime |",
            "| --- | --- | --- | --- | --- |",
        ]
    )
    for row in payload["closest_to_one"]:
        lines.append(
            f"| {row['k']} | {row['odd_count']} | `{row['ratio']}` | {row['distance_to_one_numer']} | {row['regime']} |"
        )
    lines.extend(
        [
            "",
            "## Priority families",
            "",
            "| ratio | (k,o) | regime | realized itineraries | two-sided survivors n>=2 | first n>1 failure |",
            "| --- | --- | --- | --- | --- | --- |",
        ]
    )
    for row in payload["priority_families"]:
        fail = row["first_twosided_failure_n_gt_1"]
        fail_s = "—" if fail is None else f"`{fail['word']}` at n={fail['n']}"
        lines.append(
            f"| `{row['name']}` | ({row['k']},{row['odd_count']}) | {row['regime']} | "
            f"{row['realized_words']} | {row['twosided_survivors_n_ge_2']} | {fail_s} |"
        )
    lines.extend(
        [
            "",
            "## First two-sided counterexamples (n>1)",
            "",
            "Expanding itineraries are expected to fail the reverse inequality because",
            "floor composition only yields the upper bound `T^k(n)^{2^k} <= n^{3^o}`.",
            "",
            "| word | n | k | o | exponent | m | expected | actual |",
            "| --- | --- | --- | --- | --- | --- | --- | --- |",
        ]
    )
    for rec in payload["first_counterexamples"]:
        lines.append(
            f"| `{rec['word']}` | {rec['n']} | {rec['k']} | {rec['odd_count']} | "
            f"`{rec['formal_exponent']}` | {rec['m']} | `{rec['expected_direction']}` | "
            f"`{rec['actual_direction']}` |"
        )
    if payload["onesided_failures"]:
        lines.extend(
            [
                "",
                "## One-sided floor-composition failures",
                "",
                "These falsify `T^k(n)^{2^k} <= n^{3^o}`.",
                "",
            ]
        )
        for rec in payload["onesided_failures"]:
            lines.append(
                f"- `{rec['word']}` at n={rec['n']}: m={rec['m']}, "
                f"actual `{rec['actual_direction']}`"
            )
    else:
        lines.extend(
            [
                "",
                "## One-sided floor composition",
                "",
                "No counterexample to `T^k(n)^{2^k} <= n^{3^o}` was found on the",
                "tested domain. Equality holds at the odd fixed point `n=1`.",
                "",
            ]
        )
    lines.extend(
        [
            "## Same-count permutations",
            "",
            "| (k,o) | ratio | regime | two-sided | one-sided | fail n>1 | ok n>1 |",
            "| --- | --- | --- | --- | --- | --- | --- |",
        ]
    )
    for row in payload["permutation_analysis"]:
        if row["k"] > 6 and not row["oe_eo"] and row["odd_count"] not in {3, 5, 6, 2, 4}:
            continue
        if row["k"] >= 7 and (row["k"], row["odd_count"]) not in {(8, 5), (9, 6), (8, 4)}:
            continue
        fail = ",".join(f"`{w}`" for w in row["twosided_fail_n_gt_1"][:4]) or "—"
        ok = ",".join(f"`{w}`" for w in row["twosided_ok_n_gt_1"][:4]) or "—"
        lines.append(
            f"| ({row['k']},{row['odd_count']}) | `{row['ratio']}` | {row['regime']} | "
            f"{row['twosided_hypothesis']} | {row['onesided_hypothesis']} | {fail} | {ok} |"
        )
    oe = payload.get("oe_eo")
    if oe:
        lines.extend(
            [
                "",
                "### OE vs EO",
                "",
                f"Both have formal exponent `{oe['ratio']}`. Two-sided: "
                f"{oe['twosided_hypothesis']}. One-sided: {oe['onesided_hypothesis']}.",
                "",
                f"- two-sided fail n>1: {oe['twosided_fail_n_gt_1']}",
                f"- two-sided ok n>1: {oe['twosided_ok_n_gt_1']}",
                "",
            ]
        )
    gap = payload["gap_summary"]
    lines.extend(
        [
            "## Power-gap sample",
            "",
            "Raw `Delta = n^{3^o} - T^k(n)^{2^k}` is computed only when both",
            "powers fit in 4096 bits. Sign changes of this gap would falsify",
            "the one-sided composition.",
            "",
            f"- contracting itineraries with a raw delta: {gap['contracting_words_with_raw_delta']}",
            f"- delta sign changes: {gap['delta_sign_changes'] or 'none'}",
            "",
        ]
    )
    for item in gap["focus"]:
        lines.append(
            f"- `{item['word']}`: min_delta={item['min_delta']} at n={item['min_delta_n']}; "
            f"equalities={item['equalities']}; sign_change={item['delta_negative_seen']}"
        )
    lines.extend(
        [
            "",
            "## Exceptional state",
            "",
            "`T(1)=1`. Every all-odd word is realized at `n=1` with equality",
            "`1^{2^k} = 1^{3^k}`. Strict two-sided inequalities fail; the one-sided",
            "upper bound holds. This is not a termination theorem.",
            "",
            "Pure-even words (`o=0`) have canonical comparison `T^k(n)^{2^k} < n`.",
            "Equality holds on the infinite family of even perfect-power towers",
            "(for example `E` at every even square, `EE` at `n=16`, `EEE` at `n=256`).",
            "That family is definitional `isqrt` exactness, not a mixed-word",
            "composition failure, and it is not a finite exceptional set.",
            "",
            "## Lean gate",
            "",
        ]
    )
    target = decision.get("lean_target")
    lean_status = payload.get("lean_status", "UNPROVED")
    if decision["lean_gate_open"] and target:
        lines.append(
            f"Open. Representative word `{target['word']}` of length {target['k']} "
            f"with ratio `{target['ratio']}`, first realized at n={target['first_n']}. "
            f"Lean `{lean_status}`: `{payload.get('lean_theorem')}`. "
            "Not a general-word theorem."
        )
    else:
        lines.append("Closed. No new FloorPower word theorem in this phase.")
    lines.extend(
        [
            "",
            "## Anti-overclaim",
            "",
        ]
    )
    for key, value in payload["anti_overclaim"].items():
        lines.append(f"- {key}: `{value}`")
    lines.extend(
        [
            "",
            "## Decision",
            "",
            f"**{decision['classification']}**",
            "",
            decision["reason"] + ".",
            "",
        ]
    )
    return "\n".join(lines) + "\n"


def compact_stats(stats: dict[str, ItineraryStats]) -> list[dict[str, Any]]:
    """Persist compact per-word rows needed to replay classification."""

    rows: list[dict[str, Any]] = []
    for word in sorted(stats, key=lambda w: (len(w), w)):
        item = stats[word]
        rows.append(
            {
                "word": item.word,
                "k": item.k,
                "odd_count": item.odd_count,
                "formal_exponent": item.formal_exponent,
                "regime": item.regime,
                "realizations": item.realizations,
                "twosided_ok": item.twosided_ok,
                "onesided_ok": item.onesided_ok,
                "equalities": item.equalities,
                "first_n": item.first_n,
                "first_twosided_failure": None
                if item.first_twosided_failure is None
                else item.first_twosided_failure.as_dict(),
                "first_twosided_failure_n_gt_1": None
                if item.first_twosided_failure_n_gt_1 is None
                else item.first_twosided_failure_n_gt_1.as_dict(),
                "first_onesided_failure": None
                if item.first_onesided_failure is None
                else item.first_onesided_failure.as_dict(),
                "min_delta": item.min_delta,
                "min_delta_n": item.min_delta_n,
                "delta_negative_seen": item.delta_negative_seen,
            }
        )
    return rows


def write_artifacts(
    payload: dict[str, Any] | None = None,
    *,
    n_max: int = N_MAX,
    k_max: int = K_MAX,
    include_k9: bool = True,
    stats: dict[str, ItineraryStats] | None = None,
) -> dict[str, Any]:
    used_stats = stats
    if payload is None:
        if used_stats is None:
            used_stats = run_probe(n_max=n_max, k_max=k_max, include_k9=include_k9)
        payload = probe_payload(
            used_stats, n_max=n_max, k_max=k_max, include_k9=include_k9
        )
        payload["words"] = compact_stats(used_stats)
    payload = attach_lean(payload)
    JSON_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")
    DOC_PATH.write_text(render_markdown(payload), encoding="utf-8")
    return payload


def main() -> None:
    payload = write_artifacts()
    decision = payload["decision"]
    print(decision["classification"])
    print(decision["reason"])
    print("lean_target", decision["lean_target_word"])


if __name__ == "__main__":
    main()
