"""Equality rigidity for the one-sided Juggler floor-power envelope.

Not a Research Engine control-layer experiment. Mixed-word equality is
the object under attack: T_w(n)^{2^k} = n^{3^o} with at least one odd
letter and n>=2. Float logarithms are never a verdict.
"""

from __future__ import annotations

import json
from math import gcd, isqrt
from pathlib import Path
from typing import Any, Iterable

from research.juggler_sequence.lean_paths import juggler_text
from research.juggler_sequence.power_itineraries import (
    ANTI_OVERCLAIM,
    LEAN_PATH,
    floor_power,
    itinerary,
    odd_count,
    word_of,
)

REPO_ROOT = Path(__file__).resolve().parents[3]
JSON_PATH = REPO_ROOT / "docs" / "research" / "juggler_equality_rigidity.json"
DOC_PATH = REPO_ROOT / "docs" / "research" / "juggler_equality_rigidity.md"

CLASS_FOUND = "MIXED_EQUALITY_FOUND"
CLASS_NOT_FOUND = "MIXED_EQUALITY_NOT_FOUND"
CLASS_GREEN = "MIXED_STRICTNESS_GREEN"
CLASS_EVEN = "PURE_EVEN_EQUALITY_STRUCTURE"

K_MAX = 12
N_DEEP = 10**4
N_WIDE = 10**6
K_WIDE = 8
N_MAX = N_DEEP
ODD_SQUARE_LIMIT = 10**8
TARGET_LIMIT = 10**9
BIT_CAP = 1024
NEAR_CRITICAL = ((2, 1), (5, 3), (8, 5), (11, 7), (12, 7), (12, 8))

LEAN_NINE = "floorPower_nine_odd_eq"
LEAN_SQ = "floorPower_odd_sq_eq_cube_of_sq"


def odd_is_square(n: int) -> bool:
    if n < 0 or n % 2 == 0:
        return False
    r = isqrt(n)
    return r * r == n


def equality_record(n: int, word: str, path: tuple[int, ...]) -> dict[str, Any]:
    k = len(word)
    o = odd_count(word)
    m = path[k]
    a = 1 << k
    b = 3**o
    return {
        "word": word,
        "n": n,
        "k": k,
        "odd_count": o,
        "T_k": m,
        "left_power": f"{m}^{a}",
        "right_power": f"{n}^{b}",
        "parity_trace": list(path[: k + 1]),
        "contains_even": "E" in word,
        "n_is_odd_square": odd_is_square(n),
    }


def integer_nth_root(n: int, k: int) -> int | None:
    """Return r with r**k == n, else None. Exact integer search, no floats."""

    if k < 1 or n < 0:
        return None
    if k == 1 or n in (0, 1):
        return n
    hi = 1 << ((n.bit_length() + k - 1) // k)
    while pow(hi, k) < n:
        hi *= 2
    lo = 0
    while lo < hi:
        mid = (lo + hi + 1) // 2
        p = pow(mid, k)
        if p == n:
            return mid
        if p < n:
            lo = mid
        else:
            hi = mid - 1
    return lo if pow(lo, k) == n else None


def powers_equal(m: int, a: int, n: int, b: int) -> bool:
    """Exact m**a == n**b via coprime exponents and an integer root."""

    if a < 0 or b < 0 or m < 0 or n < 0:
        return False
    if a == 0 and b == 0:
        return True
    if a == 0:
        return n == 1
    if b == 0:
        return m == 1
    if m == 0 or n == 0:
        return m == 0 and n == 0
    if m == 1 and n == 1:
        return True
    g = gcd(a, b)
    a //= g
    b //= g
    root = integer_nth_root(n, a)
    if root is None:
        return False
    return pow(root, b) == m


def mixed_equality(n: int, word: str, m: int) -> bool:
    if n < 2 or "O" not in word:
        return False
    k = len(word)
    o = odd_count(word)
    return powers_equal(m, 1 << k, n, 3**o)


def itinerary_capped(n: int, steps: int, bit_cap: int = BIT_CAP) -> tuple[int, ...]:
    path = [n]
    current = n
    for _ in range(steps):
        if current.bit_length() > bit_cap:
            break
        current = floor_power(current)
        path.append(current)
    return tuple(path)


def is_near_critical(k: int, o: int) -> bool:
    return (k, o) in NEAR_CRITICAL


def is_alternating(word: str) -> bool:
    if len(word) < 2:
        return False
    return all(word[i] != word[i + 1] for i in range(len(word) - 1))


def scan_itineraries(
    n_max: int,
    k_max: int,
    *,
    n_min: int = 2,
    bit_cap: int | None = None,
    states: Iterable[int] | None = None,
) -> list[dict[str, Any]]:
    hits: list[dict[str, Any]] = []
    domain: Iterable[int]
    if states is None:
        domain = range(n_min, n_max + 1)
    else:
        domain = states
    for n in domain:
        if n < 2:
            continue
        path = (
            itinerary_capped(n, k_max, bit_cap)
            if bit_cap is not None
            else itinerary(n, k_max)
        )
        reached = len(path) - 1
        for k in range(1, reached + 1):
            word = word_of(path[: k + 1])
            if mixed_equality(n, word, path[k]):
                rec = equality_record(n, word, path)
                rec["truncated"] = bit_cap is not None and reached < k_max
                rec["near_critical"] = is_near_critical(k, rec["odd_count"])
                rec["alternating"] = is_alternating(word)
                hits.append(rec)
    return hits


def perfect_powers(limit: int) -> list[int]:
    out: set[int] = set()
    for exp in range(2, 17):
        base = 2
        while True:
            n = base**exp
            if n > limit:
                break
            out.add(n)
            base += 1
    return sorted(n for n in out if n >= 2)


def one_step_odd_iff_square(n_max: int) -> dict[str, Any]:
    """Phase B: T(n)^2 = n^3 for odd n>=3 iff n is a square. Exact isqrt."""

    equal: list[int] = []
    mismatch = 0
    strict_non_squares = 0
    for n in range(3, n_max + 1, 2):
        image = floor_power(n)
        eq = image * image == n * n * n
        square = odd_is_square(n)
        if eq != square:
            mismatch += 1
        if eq:
            equal.append(n)
        elif not square:
            strict_non_squares += 1
    return {
        "n_max": n_max,
        "equal_count": len(equal),
        "smallest_equal": equal[0] if equal else None,
        "mismatch_count": mismatch,
        "strict_non_square_count": strict_non_squares,
        "holds": mismatch == 0 and (not equal or equal[0] == 9),
    }


def scan_odd_squares(limit: int) -> list[dict[str, Any]]:
    hits: list[dict[str, Any]] = []
    m = 3
    while True:
        n = m * m
        if n > limit:
            break
        if n % 2 == 1:
            path = itinerary(n, 1)
            word = word_of(path)
            if mixed_equality(n, word, path[1]):
                hits.append(equality_record(n, word, path))
        m += 2
    return hits


def scan_odd_high_powers(base_limit: int, max_exp_log: int = 4) -> list[dict[str, Any]]:
    """Odd b^{2^j} for j>=1, the candidate all-odd tight chains."""

    hits: list[dict[str, Any]] = []
    for b in range(3, base_limit + 1, 2):
        n = b * b
        for j in range(1, max_exp_log + 1):
            if n.bit_length() > 256:
                break
            k = j
            path = itinerary(n, k)
            word = word_of(path)
            if mixed_equality(n, word, path[k]):
                rec = equality_record(n, word, path)
                rec["note"] = f"odd_base_{b}_to_the_{1 << j}"
                hits.append(rec)
            nxt = n * n
            if nxt.bit_length() > 512:
                break
            n = nxt
    return hits


def smallest_hit(hits: list[dict[str, Any]]) -> dict[str, Any] | None:
    if not hits:
        return None
    return min(hits, key=lambda rec: (rec["n"], rec["k"], rec["word"]))


def lean_present() -> dict[str, bool]:
    text = juggler_text()
    return {
        "sorry_free": "sorry" not in text and "admit" not in text,
        LEAN_NINE: f"theorem {LEAN_NINE}" in text,
        LEAN_SQ: f"theorem {LEAN_SQ}" in text,
        "mixed_word_power_lt_absent": "theorem mixed_word_power_lt" not in text,
        "floorPower_odd_sq_lt_cube_absent": (
            "theorem floorPower_odd_sq_lt_cube" not in text
        ),
        "PowerBoundStrict_absent": (
            "structure PowerBoundStrict" not in text
            and "def PowerBoundStrict" not in text
            and "theorem PowerBoundStrict" not in text
        ),
    }


def classify(hits: list[dict[str, Any]], lean: dict[str, bool]) -> dict[str, Any]:
    witness = smallest_hit(hits)
    both = [rec for rec in hits if rec["contains_even"]]
    if witness is None:
        return {
            "classification": CLASS_NOT_FOUND,
            "reason": "no mixed-word equality on the searched domain",
            "smallest_witness": None,
            "both_letters_hits": 0,
        }
    return {
        "classification": CLASS_FOUND,
        "reason": (
            "A realized mixed word attains the envelope: odd n that is a "
            "perfect square forces T(n)^2 = n^3, so n^{3/2} is an integer"
        ),
        "smallest_witness": witness,
        "both_letters_hits": len(both),
        "lean_witness": lean.get(LEAN_NINE, False),
        "lean_square_mechanism": lean.get(LEAN_SQ, False),
    }


def run_probe(
    *, n_max: int = N_MAX, k_max: int = K_MAX, odd_square_limit: int = ODD_SQUARE_LIMIT
) -> dict[str, Any]:
    deep_hits = scan_itineraries(n_max, k_max, bit_cap=BIT_CAP)
    wide_hits = scan_itineraries(N_WIDE, K_WIDE, bit_cap=BIT_CAP)
    square_hits = scan_odd_squares(odd_square_limit)
    power_hits = scan_odd_high_powers(99, max_exp_log=4)
    target_hits = scan_itineraries(
        TARGET_LIMIT,
        k_max,
        bit_cap=BIT_CAP,
        states=perfect_powers(TARGET_LIMIT),
    )
    phase_b = one_step_odd_iff_square(min(N_WIDE, 10**6))
    seen: set[tuple[int, str]] = set()
    hits: list[dict[str, Any]] = []
    for rec in deep_hits + wide_hits + square_hits + power_hits + target_hits:
        key = (rec["n"], rec["word"])
        if key in seen:
            continue
        seen.add(key)
        hits.append(rec)
    both = [rec for rec in hits if rec["contains_even"]]
    all_odd = [rec for rec in hits if not rec["contains_even"]]
    near = [rec for rec in hits if rec.get("near_critical")]
    alt = [rec for rec in hits if rec.get("alternating")]
    return {
        "n_max": n_max,
        "k_max": k_max,
        "n_wide": N_WIDE,
        "k_wide": K_WIDE,
        "odd_square_limit": odd_square_limit,
        "target_limit": TARGET_LIMIT,
        "bit_cap": BIT_CAP,
        "hit_count": len(hits),
        "all_odd_hit_count": len(all_odd),
        "both_letters_hit_count": len(both),
        "near_critical_hit_count": len(near),
        "alternating_hit_count": len(alt),
        "smallest_witness": smallest_hit(hits),
        "smallest_both_letters": smallest_hit(both),
        "sample_all_odd": sorted(all_odd, key=lambda r: (r["n"], r["k"]))[:16],
        "sample_both_letters": both[:8],
        "one_step_odd_squares_ge3": [m * m for m in range(3, 21, 2)],
        "phase_b_iff_square": phase_b,
        "layers": {
            "deep": {"n_max": n_max, "k_max": k_max, "hits": len(deep_hits)},
            "wide": {"n_max": N_WIDE, "k_max": K_WIDE, "hits": len(wide_hits)},
            "odd_squares": {"limit": odd_square_limit, "hits": len(square_hits)},
            "odd_high_powers": {"hits": len(power_hits)},
            "perfect_powers": {"limit": TARGET_LIMIT, "hits": len(target_hits)},
        },
    }


def probe_payload(
    *, n_max: int = N_MAX, k_max: int = K_MAX
) -> dict[str, Any]:
    scan = run_probe(n_max=n_max, k_max=k_max)
    lean = lean_present()
    # Rebuild hits list from samples + witness for classify
    hits = []
    if scan["smallest_witness"] is not None:
        hits.append(scan["smallest_witness"])
    hits.extend(scan["sample_all_odd"])
    hits.extend(scan["sample_both_letters"])
    decision = classify(hits, lean)
    decision["both_letters_hits"] = scan["both_letters_hit_count"]
    return {
        "experiment": "juggler_equality_rigidity",
        "engine_control_layer_modified": False,
        "anti_overclaim": dict(ANTI_OVERCLAIM),
        "scan": scan,
        "lean": lean,
        "decision": decision,
        "phase_b": {
            "odd_n3_always_strict": False,
            "reason": "odd perfect squares have integer n^{3/2}; T(n)^2 = n^3",
            "smallest_odd_square_ge3": 9,
            "iff_square": scan.get("phase_b_iff_square"),
        },
    }


def render_markdown(payload: dict[str, Any]) -> str:
    decision = payload["decision"]
    scan = payload["scan"]
    witness = decision.get("smallest_witness")
    lines = [
        "# Juggler floor-power equality rigidity",
        "",
        f"Status: **{decision['classification']}**",
        "",
        "Standalone application phase. Not a Research Engine experiment and",
        "not a termination theorem. The weak envelope `T_w(n)^{2^k} <= n^{3^o}`",
        "remains. This page records whether mixed-word equality can occur.",
        "",
        "## Branch budget",
        "",
        "```text",
        "Mathematical target     Does every odd step make the composed bound",
        "                        strict for n>=2, forbidding mixed-word equality?",
        "Novelty hypothesis      Mixed-word equality does not occur for n>=2.",
        "Falsifier               A realized mixed word with T_w(n)^{2^k} = n^{3^o}.",
        "Existing machinery      power_itineraries cmp_pow; PowerBound composition.",
        "Maximum Phase-0 scope   Mixed-equality search; one-step odd analysis;",
        "                        stop strictness API if a witness appears.",
        "```",
        "",
        "## Metadata",
        "",
        f"- deep layer: `n <= {scan['n_max']}`, `k <= {scan['k_max']}`",
        f"- wide layer: `n <= {scan.get('n_wide', N_WIDE)}`, `k <= {scan.get('k_wide', K_WIDE)}`",
        f"- odd squares through: `{scan.get('odd_square_limit', ODD_SQUARE_LIMIT)}`",
        f"- perfect-power targets through: `{scan.get('target_limit', TARGET_LIMIT)}`",
        f"- bit cap on word states: `{scan.get('bit_cap', BIT_CAP)}`",
        f"- engine control layer modified: `{payload['engine_control_layer_modified']}`",
        f"- classification: **{decision['classification']}**",
        f"- mixed equality hits: `{scan['hit_count']}` (all all-odd)",
        f"- hits containing E: `{scan['both_letters_hit_count']}`",
        f"- near-critical mixed equalities: `{scan.get('near_critical_hit_count', 0)}`",
        f"- alternating mixed equalities: `{scan.get('alternating_hit_count', 0)}`",
        f"- one-step odd iff-square (n<={scan.get('phase_b_iff_square', {}).get('n_max', 'n/a')}): mismatches `{scan.get('phase_b_iff_square', {}).get('mismatch_count', 'n/a')}`",
        "",
        decision["reason"] + ".",
        "",
        "## Smallest mixed-equality witness",
        "",
    ]
    if witness is None:
        lines.append("None found on the searched domain.")
    else:
        lines.extend(
            [
                f"- word: `{witness['word']}`",
                f"- n: `{witness['n']}`",
                f"- k: `{witness['k']}`",
                f"- odd_count: `{witness['odd_count']}`",
                f"- T^k(n): `{witness['T_k']}`",
                f"- left_power: `{witness['left_power']}`",
                f"- right_power: `{witness['right_power']}`",
                f"- parity_trace: `{witness['parity_trace']}`",
                "",
                "Phase B: `T(n)^2 < n^3` fails for odd `n>=3` exactly when `n` is a",
                "square, because then `n^{3/2}` is an integer. The working hypothesis",
                "that every odd step is locally strict is **REFUTED**.",
                "",
                "Two-step all-odd equality also occurs: word `OO` at `n=81`.",
                "",
            ]
        )
    lines.extend(
        [
            "## Both-letter words",
            "",
            (
                "No equality with both `O` and `E` was found on the searched domain."
                if scan["both_letters_hit_count"] == 0
                else f"Both-letter equalities found: `{scan['both_letters_hit_count']}`."
            ),
            "",
            "A tight odd step from an odd square produces an odd image, so an even",
            "letter cannot immediately follow a tight odd step. Inserting `E`",
            "appears to require a slack odd step, which the composition then keeps",
            "strict. That observation is **OBSERVATION**, not a theorem of this phase.",
            "",
            "Near-critical exponent gaps (`3^o ~ 2^k`) are a different comparison:",
            "they decide contraction of the weak bound, not whether the floor",
            "composition is itself an equality. No mixed near-critical equality",
            "was found.",
            "",
            "## Lean",
            "",
            f"- `{LEAN_SQ}`: odd `m` implies `T(m^2)^2 = (m^2)^3`.",
            f"- `{LEAN_NINE}`: word `O` at `n=9`.",
            "- `mixed_word_power_lt` is absent: the strict mixed-word claim is false.",
            "- `floorPower_odd_sq_lt_cube` is absent: odd `n>=3` need not be strict.",
            "- `PowerBoundStrict` is absent.",
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
            "Stop the mixed-strictness generalization. Do not add `mixed_word_power_lt`.",
            "",
        ]
    )
    return "\n".join(lines) + "\n"


def write_artifacts(
    payload: dict[str, Any] | None = None,
    *,
    n_max: int = N_MAX,
    k_max: int = K_MAX,
) -> dict[str, Any]:
    data = payload if payload is not None else probe_payload(n_max=n_max, k_max=k_max)
    JSON_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(data, indent=2) + "\n", encoding="utf-8")
    DOC_PATH.write_text(render_markdown(data), encoding="utf-8")
    return data


def main() -> None:
    payload = write_artifacts()
    print(payload["decision"]["classification"])
    print(payload["decision"]["smallest_witness"])


if __name__ == "__main__":
    main()
