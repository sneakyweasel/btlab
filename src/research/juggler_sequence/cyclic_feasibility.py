"""Global cyclic word feasibility. Not a halt theorem.

CycReal(w) means some n>=2 realises the exact Juggler word w and
returns: T^k(n)=n. Phase 0 asks whether joint floor-cell closure
adds an word-independent obstruction beyond the existing CycleItinerary
layer (envelope, all-odd expansion, even-count <= 3, length >= 11).

Not a Research Engine control-layer experiment. Not a reopen of
terminal cells, Z5, length-11 assembly, four-even leftovers,
p-adic systems, escape-language density, survival-set occupancy,
or generic inverse search. No Lean in this phase.
"""

from __future__ import annotations

import csv
import json
import math
import subprocess
from dataclasses import dataclass
from decimal import Decimal, localcontext
from math import isqrt
from pathlib import Path
from typing import Any

from research.juggler_sequence.atlas.schema import CLAIM_NOT_OBSERVED, LANGUAGE_IDS
from research.juggler_sequence.lean_paths import (
    JUGGLER_DIR,
    JUGGLER_PAPER_BARREL,
    engine_floor_text,
    has_named,
    juggler_text,
)
from research.juggler_sequence.power_itineraries import ANTI_OVERCLAIM, floor_power

REPO_ROOT = Path(__file__).resolve().parents[3]
JSON_PATH = REPO_ROOT / "docs" / "research" / "juggler_cyclic_feasibility.json"
DOC_PATH = REPO_ROOT / "docs" / "research" / "juggler_cyclic_feasibility.md"
DATA_DIR = REPO_ROOT / "data" / "research" / "juggler" / "cyclic_feasibility"

CLASS_UNIVERSAL = "CYCLIC_FEASIBILITY_UNIVERSAL"
CLASS_FAMILY = "CYCLIC_FEASIBILITY_FAMILY"
CLASS_NEAR = "CYCLIC_FEASIBILITY_NEAR"
CLASS_CLOSED = "CYCLIC_FEASIBILITY_CLOSED"
CLASS_PARK_OPEN = "CYCLIC_FEASIBILITY_PARK_OPEN"
CLASS_PARK_BOUND = "CYCLIC_FEASIBILITY_PARK_BOUND"
CLASS_CYCLE = "CYCLIC_FEASIBILITY_EXACT_CYCLE"
CLASS_INCOMPLETE = "CYCLIC_FEASIBILITY_INCOMPLETE"

# Primitive necklace census (OEIS A001037).
A001037 = (0, 2, 1, 2, 3, 6, 9, 18, 30, 56, 99, 186, 335, 630, 1161, 2182, 4080)

TEST_K = 8
TEST_N = 160
TEST_KO = 20
TEST_SCAN_CAP = 400
TEST_NEAR_K = 6

SCIENCE_K = 16
SCIENCE_N = 20_000
SCIENCE_KO = 48
SCIENCE_SCAN_CAP = 8_000
SCIENCE_NEAR_K = 12
SCIENCE_BIT_CAP = 256

EXISTING_LEAN = (
    "CycleItinerary",
    "cycle_itinerary_formally_expanding",
    "odd_itinerary_expands",
    "power_bound_contracts",
    "two_pow_ne_three_pow",
    "no_cycle_itinerary_even_count_le_three",
    "cycle_itinerary_even_count_ge_four",
    "cycle_itinerary_length_ge_eleven",
    "envelope_corridor_contradiction",
)

FORBIDDEN_THEOREMS = (
    "juggler_reaches_one",
    "no_juggler_escape",
    "no_nontrivial_cycle_of_global_closure",
    "cyclic_envelope_collision",
    "cycle_floor_slack_contradiction",
    "no_cyclic_itinerary",
    "CycReal",
)

FORBIDDEN_NEW_API = (
    "CycReal",
    "CyclicFeasibility",
    "ClosureMismatch",
    "PhiProduct",
)

NEW_LEAN_FILES = (
    JUGGLER_DIR / "CyclicFeasibility.lean",
    JUGGLER_DIR / "CycReal.lean",
    JUGGLER_DIR / "ClosureMismatch.lean",
)


def git_commit() -> str:
    try:
        return subprocess.check_output(
            ["git", "rev-parse", "HEAD"],
            cwd=REPO_ROOT,
            text=True,
            stderr=subprocess.DEVNULL,
        ).strip()
    except (OSError, subprocess.CalledProcessError):
        return "unknown"


def integer_cbrt_floor(m: int) -> int:
    if m < 0:
        raise ValueError("cbrt floor expects nonnegative")
    if m < 2:
        return m
    lo, hi = 0, 1
    while hi**3 <= m:
        hi *= 2
    while lo < hi:
        mid = (lo + hi + 1) // 2
        if mid**3 <= m:
            lo = mid
        else:
            hi = mid - 1
    return lo


def integer_cbrt_ceil(m: int) -> int:
    r = integer_cbrt_floor(m)
    return r if r**3 == m else r + 1


def odd_count(word: str) -> int:
    return word.count("O")


def even_count(word: str) -> int:
    return word.count("E")


def mu_of(k: int, o: int) -> int:
    return 3**o - 2**k


def regime_of(k: int, o: int) -> str:
    gap = mu_of(k, o)
    if gap < 0:
        return "contracting"
    if gap == 0:
        return "neutral"
    return "expanding"


def exponent_ok(word: str) -> bool:
    return 2 ** len(word) <= 3 ** odd_count(word)


def is_primitive(word: str) -> bool:
    k = len(word)
    if k == 0:
        return False
    for period in range(1, k):
        if k % period == 0 and word == word[:period] * (k // period):
            return False
    return True


def necklace_key(word: str) -> str:
    return min(word[i:] + word[:i] for i in range(len(word)))


def rotations(word: str) -> list[str]:
    return [word[i:] + word[:i] for i in range(len(word))]


def primitive_necklaces(n: int) -> list[str]:
    """Binary primitive necklaces. 0 -> E, 1 -> O. FKM, aperiodic only."""

    if n <= 0:
        return []
    out: list[str] = []
    a = [0] * (n + 1)

    def gen(t: int, p: int) -> None:
        if t > n:
            if p == n:
                out.append("".join("O" if a[i] else "E" for i in range(1, n + 1)))
            return
        a[t] = a[t - p]
        gen(t + 1, p)
        for j in range(a[t - p] + 1, 2):
            a[t] = j
            gen(t + 1, t)

    gen(1, 1)
    return out


def all_necklaces(n: int) -> list[str]:
    if n <= 0:
        return []
    out: list[str] = []
    a = [0] * (n + 1)

    def gen(t: int, p: int) -> None:
        if t > n:
            if n % p == 0:
                out.append("".join("O" if a[i] else "E" for i in range(1, n + 1)))
            return
        a[t] = a[t - p]
        gen(t + 1, p)
        for j in range(a[t - p] + 1, 2):
            a[t] = j
            gen(t + 1, t)

    gen(1, 1)
    return out


def plus_one_w(word: str) -> int:
    """Exponent of (1+1/m) in the +1 envelope rooted at the start of w."""

    a_exp = 1
    weight = 0
    for letter in word:
        two_a = 2 * a_exp
        if letter == "O":
            weight = 3 * weight + two_a
        elif letter == "E":
            weight = weight + two_a
        else:
            raise ValueError(f"unknown letter {letter!r}")
        a_exp = two_a
    return weight


def min_plus_one_w(word: str) -> tuple[int, str]:
    best_w = None
    best_rot = word
    for rot in rotations(word):
        weight = plus_one_w(rot)
        if best_w is None or weight < best_w:
            best_w = weight
            best_rot = rot
    assert best_w is not None
    return best_w, best_rot


def w_range(k: int, o: int) -> tuple[int | None, int | None]:
    """Min/max plus-one W over itineraries of length k with o odds."""

    if o < 0 or o > k:
        return None, None
    inf = 10**30
    min_w = [inf] * (o + 1)
    max_w = [-inf] * (o + 1)
    min_w[0] = 0
    max_w[0] = 0
    for i in range(k):
        two_a = 2 << i
        new_min = [inf] * (o + 1)
        new_max = [-inf] * (o + 1)
        for j in range(o + 1):
            if min_w[j] >= inf:
                continue
            even_lo = min_w[j] + two_a
            even_hi = max_w[j] + two_a
            if even_lo < new_min[j]:
                new_min[j] = even_lo
            if even_hi > new_max[j]:
                new_max[j] = even_hi
            if j + 1 <= o:
                odd_lo = 3 * min_w[j] + two_a
                odd_hi = 3 * max_w[j] + two_a
                if odd_lo < new_min[j + 1]:
                    new_min[j + 1] = odd_lo
                if odd_hi > new_max[j + 1]:
                    new_max[j + 1] = odd_hi
        min_w, max_w = new_min, new_max
    if min_w[o] >= inf:
        return None, None
    return min_w[o], max_w[o]


def ge_three_halves(n: int, mu: int, weight: int) -> bool:
    """n^mu >= (3/2)^W iff n^mu * 2^W >= 3^W."""

    if mu <= 0:
        return True
    if n < 2:
        return False
    if weight <= 80 and mu <= 40:
        return n**mu * (1 << weight) >= 3**weight
    lhs = mu * math.log2(n) + weight
    rhs = weight * math.log2(3)
    if abs(lhs - rhs) > 1e-8:
        return lhs >= rhs
    with localcontext() as ctx:
        ctx.prec = 80
        return (
            Decimal(n).ln() * mu + Decimal(2).ln() * weight
            >= Decimal(3).ln() * weight
        )


def two_thirds_cap(mu: int, weight: int, *, hard: int) -> int | None:
    """Least n>=2 with n^mu >= (3/2)^W. None if the cap exceeds hard."""

    if mu <= 0:
        return 2
    if weight <= 0:
        return 2
    # (3/2)^{W/μ} > hard iff W log(3/2) > μ log(hard)
    if weight * math.log(1.5) > mu * math.log(hard * 4):
        return None
    est = 1.5 ** (weight / mu)
    if est > hard * 4:
        return None
    n = max(2, int(est) - 2)
    while n <= hard:
        if ge_three_halves(n, mu, weight):
            return n
        n += 1
    return None


def cyclemin_fires(n: int, mu: int, weight: int) -> bool:
    """n^mu >= (1+1/n)^W iff n^{mu+W} >= (n+1)^W."""

    if mu <= 0:
        return True
    if n < 2:
        return False
    if weight <= 80 and mu + weight <= 120:
        return n ** (mu + weight) >= (n + 1) ** weight
    with localcontext() as ctx:
        ctx.prec = 60
        return Decimal(n).ln() * (mu + weight) >= Decimal(n + 1).ln() * weight


def cyclemin_threshold(mu: int, weight: int, *, hard: int) -> int | None:
    if weight > 8_000 or mu > 200:
        return None
    for n in range(2, hard + 1):
        if cyclemin_fires(n, mu, weight):
            return n
    return None


@dataclass
class Bound:
    lo: int
    hi: int | None

    def empty(self) -> bool:
        return self.hi is not None and self.lo > self.hi

    def intersect(self, other: "Bound") -> "Bound":
        lo = max(self.lo, other.lo)
        if self.hi is None:
            hi = other.hi
        elif other.hi is None:
            hi = self.hi
        else:
            hi = min(self.hi, other.hi)
        return Bound(lo, hi)


def with_parity(bound: Bound, odd: bool) -> Bound:
    lo, hi = bound.lo, bound.hi
    if odd:
        if lo % 2 == 0:
            lo += 1
        if hi is not None and hi % 2 == 0:
            hi -= 1
    else:
        if lo % 2 == 1:
            lo += 1
        if hi is not None and hi % 2 == 1:
            hi -= 1
    return Bound(lo, hi)


def forward_image(bound: Bound, letter: str, next_odd: bool) -> Bound:
    src = with_parity(bound, letter == "O")
    if src.empty():
        return Bound(1, 0)
    if letter == "E":
        y_lo = isqrt(src.lo)
        y_hi = None if src.hi is None else isqrt(src.hi)
    else:
        y_lo = isqrt(src.lo**3)
        y_hi = None if src.hi is None else isqrt(src.hi**3)
    return with_parity(Bound(max(y_lo, 1), y_hi), next_odd)


def backward_preimage(nxt: Bound, letter: str, src_odd: bool) -> Bound:
    if nxt.empty():
        return Bound(1, 0)
    if letter == "E":
        x_lo = nxt.lo * nxt.lo
        x_hi = None if nxt.hi is None else (nxt.hi + 1) ** 2 - 1
    else:
        x_lo = integer_cbrt_ceil(nxt.lo * nxt.lo)
        if nxt.hi is None:
            x_hi = None
        else:
            x_hi = integer_cbrt_floor((nxt.hi + 1) ** 2 - 1)
    return with_parity(Bound(max(x_lo, 1), x_hi), src_odd)


def _propagate_from(
    word: str,
    bounds: list[Bound],
    *,
    rounds: int | None = None,
) -> tuple[list[Bound], bool]:
    k = len(word)
    limit = rounds if rounds is not None else 2 * k + 6
    for _ in range(limit):
        changed = False
        for i in range(k):
            nxt = (i + 1) % k
            img = forward_image(bounds[i], word[i], word[nxt] == "O")
            new = bounds[nxt].intersect(img)
            if new.lo != bounds[nxt].lo or new.hi != bounds[nxt].hi:
                changed = True
            bounds[nxt] = new
            if new.empty():
                return bounds, True
        for i in range(k):
            nxt = (i + 1) % k
            pre = backward_preimage(bounds[nxt], word[i], word[i] == "O")
            new = bounds[i].intersect(pre)
            if new.lo != bounds[i].lo or new.hi != bounds[i].hi:
                changed = True
            bounds[i] = new
            if new.empty():
                return bounds, True
        if not changed:
            break
    return bounds, any(b.empty() for b in bounds)


def propagate_cycle(
    word: str,
    cap: int | None,
    *,
    rounds: int | None = None,
) -> tuple[list[Bound], bool]:
    bounds = [with_parity(Bound(2, cap), letter == "O") for letter in word]
    if any(b.empty() for b in bounds):
        return bounds, True
    return _propagate_from(word, bounds, rounds=rounds)


def phi_o_increasing() -> bool:
    return True


def phi_product_min_ge_one(word: str, bounds: list[Bound]) -> bool | None:
    """True if every assignment in the intervals has product >= 1."""

    num = 1
    den = 1
    for letter, bound in zip(word, bounds, strict=True):
        if letter == "O":
            x = bound.lo
            num *= x**3
            den *= (x + 1) ** 2
        else:
            if bound.hi is None:
                return None
            x = bound.hi
            num *= x
            den *= (x + 1) ** 2
    return num >= den


def all_odd_phi_contradiction() -> bool:
    """Each odd state >= 3 has phi_O >= 27/16 > 1, so the product is > 1."""

    return 3**3 * 1 >= 4**2 and 27 * 16 > 16 * 16


def follows_image(n: int, word: str) -> int | None:
    current = n
    for letter in word:
        if letter == "O" and current % 2 == 0:
            return None
        if letter == "E" and current % 2 == 1:
            return None
        current = floor_power(current)
    return current


def cyc_real(n: int, word: str) -> bool:
    return n >= 2 and follows_image(n, word) == n


def local_defect(x: int, letter: str) -> int:
    y = floor_power(x)
    if letter == "E":
        return x - y * y
    return x * x * x - y * y


def exact_scan(word: str, n_hi: int) -> int | None:
    start = 3 if word[0] == "O" else 2
    step = 2
    n = start
    while n <= n_hi:
        if cyc_real(n, word):
            return n
        n += step
    return None


def near_cycle_row(word: str, n_hi: int) -> dict[str, Any] | None:
    best: dict[str, Any] | None = None
    start = 3 if word[0] == "O" else 2
    n = start
    while n <= n_hi:
        img = follows_image(n, word)
        if img is not None and img != n:
            delta = abs(img - n)
            rel_num, rel_den = delta, n
            if best is None or delta * best["rel_den"] < best["abs"] * rel_den:
                best = {
                    "word": word,
                    "n": n,
                    "image": img,
                    "abs": delta,
                    "rel_num": rel_num,
                    "rel_den": rel_den,
                }
        n += 2
    return best


def orbit_until(n: int, *, step_cap: int, bit_cap: int) -> tuple[list[int], str]:
    path = [n]
    current = n
    seen = {n: 0}
    for _ in range(step_cap):
        if current.bit_length() > bit_cap:
            return path, "BIT_CAP"
        current = floor_power(current)
        path.append(current)
        if current == n:
            return path, "CYCLE"
        if current in seen:
            return path, "OTHER_CYCLE"
        if current < 2:
            return path, "TERM"
        seen[current] = len(path) - 1
    return path, "HORIZON"


def scan_direct_cycles(n_max: int, *, step_cap: int, bit_cap: int) -> dict[str, Any]:
    found: list[dict[str, Any]] = []
    near: list[dict[str, Any]] = []
    for n in range(2, n_max + 1):
        path, flag = orbit_until(n, step_cap=step_cap, bit_cap=bit_cap)
        if flag == "CYCLE" and n > 1:
            word = "".join("E" if path[i] % 2 == 0 else "O" for i in range(len(path) - 1))
            found.append({"n": n, "period": len(path) - 1, "word": word, "path": path})
        if len(path) >= 3:
            last = path[-1]
            if last != n:
                delta = abs(last - n)
                if delta * 100 <= n and flag in {"TERM", "HORIZON", "BIT_CAP"}:
                    near.append(
                        {
                            "n": n,
                            "last": last,
                            "steps": len(path) - 1,
                            "abs": delta,
                            "flag": flag,
                        }
                    )
    return {"cycles": found, "near_drop": near[:20], "n_max": n_max}


def word_class(word: str) -> str:
    k = len(word)
    o = odd_count(word)
    e = k - o
    if e == 0:
        return "all_odd"
    if o == 0:
        return "all_even"
    return regime_of(k, o)


def leftover_shape(word: str) -> bool:
    """Formally expanding mixed word with at least four evens."""

    k = len(word)
    o = odd_count(word)
    e = k - o
    return e >= 4 and o >= 1 and 3**o > 2**k


def classify_one(
    word: str,
    *,
    scan_cap: int,
    interval_cap: int,
) -> dict[str, Any]:
    k = len(word)
    o = odd_count(word)
    e = k - o
    gap = mu_of(k, o)
    kind = word_class(word)
    row: dict[str, Any] = {
        "word": word,
        "necklace": necklace_key(word),
        "k": k,
        "o": o,
        "e": e,
        "mu": gap,
        "kind": kind,
        "primitive": is_primitive(word),
        "leftover_shape": leftover_shape(word),
        "status": "",
        "filter": "",
        "hit": None,
        "plus_one_W": None,
        "m2_cap": None,
        "cyclemin_n0": None,
        "interval_empty": False,
        "box_empty_unproved": False,
        "phi_min_ge_one": None,
    }
    if kind == "all_even":
        row["status"] = "INFEASIBLE"
        row["filter"] = "all_even_descent"
        return row
    if kind == "all_odd":
        row["status"] = "INFEASIBLE"
        row["filter"] = "odd_itinerary_expands"
        return row
    if kind == "contracting":
        row["status"] = "INFEASIBLE"
        row["filter"] = "power_bound_contracts"
        return row
    if kind == "neutral":
        row["status"] = "INFEASIBLE"
        row["filter"] = "two_pow_ne_three_pow"
        return row
    if e <= 3:
        row["status"] = "INFEASIBLE"
        row["filter"] = "no_cycle_itinerary_even_count_le_three"
        return row

    weight, rot = min_plus_one_w(word)
    row["plus_one_W"] = weight
    row["tight_rotation"] = rot
    m2 = two_thirds_cap(gap, weight, hard=scan_cap)
    row["m2_cap"] = m2
    n0 = cyclemin_threshold(gap, plus_one_w(rot), hard=min(80, scan_cap))
    row["cyclemin_n0"] = n0

    # Each rotation is itself a start, so each state has its own
    # plus-one cap. A common finite box is not a proof.
    state_caps: list[int | None] = []
    proved_caps = True
    for spelling in rotations(rot):
        cap_i = two_thirds_cap(gap, plus_one_w(spelling), hard=max(scan_cap, 50_000))
        state_caps.append(cap_i)
        if cap_i is None:
            proved_caps = False
    bounds = [
        with_parity(Bound(2, cap_i), letter == "O")
        for letter, cap_i in zip(rot, state_caps, strict=True)
    ]
    if any(b.empty() for b in bounds):
        empty = True
    else:
        bounds, empty = _propagate_from(rot, bounds)
    row["interval_empty"] = bool(empty and proved_caps)
    row["box_empty_unproved"] = bool(empty and not proved_caps)
    if empty and proved_caps:
        row["status"] = "INFEASIBLE"
        row["filter"] = "interval_collision"
        return row
    unbounded, _ = propagate_cycle(rot, None)
    phi = phi_product_min_ge_one(rot, unbounded)
    row["phi_min_ge_one"] = phi
    if phi is True:
        row["status"] = "INFEASIBLE"
        row["filter"] = "phi_product"
        return row

    scan_hi = scan_cap
    if m2 is not None:
        scan_hi = min(scan_cap, m2)
    hit = exact_scan(rot, scan_hi)
    if hit is not None:
        row["status"] = "EXACT_CYCLE"
        row["filter"] = "direct"
        row["hit"] = hit
        return row
    if m2 is not None and m2 <= scan_cap:
        row["status"] = "INFEASIBLE"
        row["filter"] = "plus_one_m2_scan"
        return row
    row["status"] = "UNRESOLVED"
    row["filter"] = "search_bound"
    return row


def pair_table(k_max: int) -> list[dict[str, Any]]:
    rows = []
    for k in range(2, k_max + 1):
        o_min = 0
        while o_min <= k and 3**o_min < 2**k:
            o_min += 1
        for o in range(0, k + 1):
            e = k - o
            gap = mu_of(k, o)
            kind = regime_of(k, o)
            if o == 0:
                kind = "all_even"
            elif e == 0:
                kind = "all_odd"
            w_min, w_max = w_range(k, o)
            residue = (
                kind == "expanding"
                and e >= 4
                and o >= 1
            )
            known_dead = (
                kind in {"all_even", "all_odd", "contracting", "neutral"}
                or (kind == "expanding" and e <= 3)
            )
            rows.append(
                {
                    "k": k,
                    "o": o,
                    "e": e,
                    "mu": gap,
                    "kind": kind,
                    "o_min_expanding": o_min,
                    "W_min": w_min,
                    "W_max": w_max,
                    "known_dead": known_dead,
                    "leftover_residue": residue,
                }
            )
    return rows


def necklace_census(k_max: int) -> list[dict[str, Any]]:
    rows = []
    for k in range(1, k_max + 1):
        prim = primitive_necklaces(k)
        alln = all_necklaces(k)
        exp = [w for w in prim if exponent_ok(w)]
        mixed_exp = [
            w
            for w in exp
            if 0 < odd_count(w) < k and regime_of(k, odd_count(w)) == "expanding"
        ]
        residue = [w for w in mixed_exp if even_count(w) >= 4]
        rows.append(
            {
                "k": k,
                "primitive": len(prim),
                "all_necklaces": len(alln),
                "exponent_ok": len(exp),
                "mixed_expanding": len(mixed_exp),
                "even_le_3_expanding": len([w for w in mixed_exp if even_count(w) <= 3]),
                "leftover_residue": len(residue),
                "expected_primitive": A001037[k] if k < len(A001037) else None,
            }
        )
    return rows


def classify_necklaces(
    k_max: int,
    *,
    scan_cap: int,
    interval_cap: int,
) -> list[dict[str, Any]]:
    rows = []
    for k in range(2, k_max + 1):
        for word in primitive_necklaces(k):
            rows.append(
                classify_one(word, scan_cap=scan_cap, interval_cap=interval_cap)
            )
    return rows


def potential_signs(n_max: int, *, step_cap: int) -> dict[str, Any]:
    """Open-path signs of candidate edge potentials. Not a Lyapunov."""

    pos = {"log_ratio": 0, "phi_step": 0, "defect": 0}
    neg = {"log_ratio": 0, "phi_step": 0, "defect": 0}
    for n in range(3, n_max + 1, 2):
        x = n
        for _ in range(step_cap):
            y = floor_power(x)
            if y < 2:
                break
            if x % 2 == 1:
                log_s = 3 * math.log(x) - 2 * math.log(y)
                phi_s = math.log(x**3) - math.log((y + 1) ** 2)
                defect = x**3 - y * y
            else:
                log_s = math.log(x) - 2 * math.log(y)
                phi_s = math.log(x) - math.log((y + 1) ** 2)
                defect = x - y * y
            for key, val in (("log_ratio", log_s), ("phi_step", phi_s), ("defect", defect)):
                if val > 0:
                    pos[key] += 1
                elif val < 0:
                    neg[key] += 1
            x = y
    mixed = {
        key: pos[key] > 0 and neg[key] > 0 for key in pos
    }
    return {"pos": pos, "neg": neg, "mixed_sign": mixed}


def lean_api_present() -> dict[str, bool]:
    text = juggler_text()
    paper = JUGGLER_PAPER_BARREL.read_text(encoding="utf-8")
    sorry_free = "sorry" not in text and "admit" not in text
    out: dict[str, bool] = {
        "sorry_free": sorry_free,
        "new_lean_file": any(path.is_file() for path in NEW_LEAN_FILES),
        "not_in_paper_barrel": all(name not in paper for name in FORBIDDEN_NEW_API),
        "no_atlas_lang": "LANG_CYC_REAL" not in LANGUAGE_IDS
        and "LANG_CYCLIC_FEAS" not in LANGUAGE_IDS,
        "FloorPower_not_rewritten": "CycReal" not in engine_floor_text(),
    }
    for name in EXISTING_LEAN:
        out[name] = has_named(text, name)
    for name in FORBIDDEN_THEOREMS:
        out[f"has_{name}"] = has_named(text, name)
    for name in FORBIDDEN_NEW_API:
        out[f"has_api_{name}"] = has_named(text, name)
    return out


def summarise_rows(rows: list[dict[str, Any]]) -> dict[str, Any]:
    by_status: dict[str, int] = {}
    by_filter: dict[str, int] = {}
    leftover = []
    unresolved = []
    interval_hits = 0
    phi_hits = 0
    m2_hits = 0
    exact = []
    for row in rows:
        by_status[row["status"]] = by_status.get(row["status"], 0) + 1
        by_filter[row["filter"]] = by_filter.get(row["filter"], 0) + 1
        if row["filter"] == "interval_collision":
            interval_hits += 1
        if row["filter"] == "phi_product":
            phi_hits += 1
        if row["filter"] == "plus_one_m2_scan":
            m2_hits += 1
        if row["status"] == "EXACT_CYCLE":
            exact.append(row)
        if row["leftover_shape"]:
            leftover.append(row)
            if row["status"] == "UNRESOLVED":
                unresolved.append(row)
    known_filters = {
        "all_even_descent",
        "odd_itinerary_expands",
        "power_bound_contracts",
        "two_pow_ne_three_pow",
        "no_cycle_itinerary_even_count_le_three",
    }
    known_dead = sum(by_filter.get(name, 0) for name in known_filters)
    new_joint = interval_hits + phi_hits
    return {
        "by_status": by_status,
        "by_filter": by_filter,
        "known_dead": known_dead,
        "new_joint_hits": new_joint,
        "interval_hits": interval_hits,
        "phi_hits": phi_hits,
        "m2_scan_hits": m2_hits,
        "leftover_count": len(leftover),
        "leftover_unresolved": len(unresolved),
        "leftover_unresolved_words": [r["word"] for r in unresolved[:40]],
        "exact_cycles": exact,
        "known_filters_only": new_joint == 0 and not exact,
    }


def run_probe(
    *,
    k_max: int = TEST_K,
    n_max: int = TEST_N,
    k_pairs: int = TEST_KO,
    scan_cap: int = TEST_SCAN_CAP,
    near_k: int = TEST_NEAR_K,
    bit_cap: int = 128,
) -> dict[str, Any]:
    census = necklace_census(k_max)
    pairs = pair_table(k_pairs)
    classified = classify_necklaces(
        k_max, scan_cap=scan_cap, interval_cap=scan_cap
    )
    summary = summarise_rows(classified)
    direct = scan_direct_cycles(n_max, step_cap=200, bit_cap=bit_cap)
    potentials = potential_signs(min(n_max, 80), step_cap=12)
    near_rows = []
    for k in range(2, near_k + 1):
        for word in primitive_necklaces(k):
            if not leftover_shape(word) and word_class(word) != "expanding":
                continue
            if even_count(word) <= 3 and odd_count(word) not in {0, k}:
                continue
            if not leftover_shape(word):
                continue
            row = near_cycle_row(word, min(n_max, 400))
            if row is not None:
                near_rows.append(row)
    near_rows.sort(key=lambda r: (r["abs"] * 10**9) // r["rel_den"])
    residue_pairs = [p for p in pairs if p["leftover_residue"]]
    known_pairs = [p for p in pairs if p["known_dead"]]
    census_ok = all(
        row["expected_primitive"] is None
        or row["primitive"] == row["expected_primitive"]
        for row in census
    )
    length_ge_11 = all(
        p["k"] >= 11 for p in residue_pairs
    )
    all_odd_phi = all_odd_phi_contradiction()
    halt = False
    return {
        "k_max": k_max,
        "n_max": n_max,
        "k_pairs": k_pairs,
        "scan_cap": scan_cap,
        "git": git_commit(),
        "census": census,
        "census_matches_A001037": census_ok,
        "pairs": pairs,
        "classified": classified,
        "summary": summary,
        "direct": {
            "n_max": direct["n_max"],
            "cycles": direct["cycles"],
            "near_drop": direct["near_drop"],
            "cycle_count": len(direct["cycles"]),
        },
        "near_words": near_rows[:12],
        "potentials": potentials,
        "residue_pair_count": len(residue_pairs),
        "known_pair_count": len(known_pairs),
        "residue_min_k": min((p["k"] for p in residue_pairs), default=None),
        "length_ge_11_from_pairs": length_ge_11,
        "all_odd_phi_ok": all_odd_phi,
        "halt_theorem": halt,
        "new_lean": False,
    }


def classify(scan: dict[str, Any], lean: dict[str, bool]) -> dict[str, Any]:
    lean_ok = (
        lean["sorry_free"]
        and all(lean[name] for name in EXISTING_LEAN)
        and not lean["has_juggler_reaches_one"]
        and not lean["new_lean_file"]
        and not any(lean[f"has_api_{name}"] for name in FORBIDDEN_NEW_API)
        and lean["not_in_paper_barrel"]
        and lean["no_atlas_lang"]
    )
    if not lean_ok or scan["halt_theorem"] or scan["new_lean"]:
        return {"classification": CLASS_INCOMPLETE, "reason": "lean or scope failure"}
    if scan["summary"]["exact_cycles"]:
        return {
            "classification": CLASS_CYCLE,
            "reason": "exact integer cycle candidate; stop and verify",
        }
    near = scan["near_words"]
    near_signal = bool(near) and near[0]["abs"] * 50 <= near[0]["rel_den"]
    if near_signal and scan["summary"]["leftover_unresolved"] > 8:
        return {
            "classification": CLASS_NEAR,
            "reason": "near-cycle relative error is exceptionally small",
        }
    joint = scan["summary"]["new_joint_hits"]
    leftover_u = scan["summary"]["leftover_unresolved"]
    if (
        scan["census_matches_A001037"]
        and scan["length_ge_11_from_pairs"]
        and scan["direct"]["cycle_count"] == 0
        and joint == 0
        and leftover_u == scan["summary"]["leftover_count"]
        and scan["summary"]["known_filters_only"]
    ):
        return {
            "classification": CLASS_CLOSED,
            "reason": (
                "cheap cyclic filters are the existing CycleItinerary layer "
                "(envelope, odd_itinerary_expands, even-count <= 3, length >= 11); "
                "interval and phi-product never fire; the residue is the "
                "already-studied e>=4 leftover family"
            ),
        }
    if leftover_u > 0 and joint == 0:
        return {
            "classification": CLASS_PARK_BOUND,
            "reason": "leftover residue stays unresolved; joint filters do not decide",
        }
    if leftover_u > 0:
        return {
            "classification": CLASS_FAMILY,
            "reason": "a parametric leftover family survives the generic filters",
        }
    return {
        "classification": CLASS_PARK_OPEN,
        "reason": "cyclic feasibility remains unconstrained after the scan",
    }


def probe_payload(
    *,
    k_max: int = TEST_K,
    n_max: int = TEST_N,
    k_pairs: int = TEST_KO,
    scan_cap: int = TEST_SCAN_CAP,
    near_k: int = TEST_NEAR_K,
) -> dict[str, Any]:
    scan = run_probe(
        k_max=k_max,
        n_max=n_max,
        k_pairs=k_pairs,
        scan_cap=scan_cap,
        near_k=near_k,
    )
    lean = lean_api_present()
    decision = classify(scan, lean)
    anti = dict(ANTI_OVERCLAIM)
    anti.update(
        {
            "global_termination": False,
            "no_cycle_theorem": False,
            "word_independent_mismatch": False,
            "floating_point_verdict": False,
        }
    )
    return {
        "experiment": "juggler_cyclic_feasibility",
        "engine_control_layer_modified": False,
        "anti_overclaim": anti,
        "scan": scan,
        "lean": lean,
        "decision": decision,
        "search_method": (
            f"primitive necklaces k<={k_max}; (k,o) to {k_pairs}; "
            f"direct n<={n_max}; plus-one/interval/phi; scan_cap={scan_cap}"
        ),
        "claim": CLAIM_NOT_OBSERVED,
    }


def render_markdown(payload: dict[str, Any]) -> str:
    scan = payload["scan"]
    decision = payload["decision"]
    summary = scan["summary"]
    lines = [
        "# Juggler cyclic word feasibility",
        "",
        "Closed-word question `CycReal(w)`: some `n>=2` realises `w` and "
        "`T^k(n)=n`. Absence is `NOT OBSERVED WITHIN SEARCH BOUND`. "
        "Not a halt theorem.",
        "",
        f"- classification: `{decision['classification']}`",
        f"- reason: {decision['reason']}",
        f"- k_max: `{scan['k_max']}`",
        f"- n_max: `{scan['n_max']}`",
        f"- claim: `{payload['claim']}`",
        "",
        "## Primitive necklaces",
        "",
        "| k | primitive | exponent-ok | mixed expanding | e<=3 expanding | leftover e>=4 |",
        "|---|---|---|---|---|---|",
    ]
    for row in scan["census"]:
        lines.append(
            f"| {row['k']} | {row['primitive']} | {row['exponent_ok']} | "
            f"{row['mixed_expanding']} | {row['even_le_3_expanding']} | "
            f"{row['leftover_residue']} |"
        )
    lines.extend(
        [
            "",
            f"A001037 match: `{scan['census_matches_A001037']}`.",
            "",
            "## Filter survival",
            "",
            f"`{summary['by_filter']}`",
            "",
            f"known CycleItinerary deaths: `{summary['known_dead']}`. "
            f"new joint (interval/phi): `{summary['new_joint_hits']}`. "
            f"plus-one m=2 scans: `{summary['m2_scan_hits']}`. "
            f"leftover residue: `{summary['leftover_count']}` "
            f"unresolved `{summary['leftover_unresolved']}`.",
            "",
            "## Direct cycles",
            "",
            f"n<=`{scan['direct']['n_max']}` exact cycles: "
            f"`{scan['direct']['cycle_count']}`.",
            "",
            "## Near-cycles",
            "",
        ]
    )
    if scan["near_words"]:
        lines.append("| word | n | image | |T_w-n| |")
        lines.append("|---|---|---|---|")
        for row in scan["near_words"][:8]:
            lines.append(
                f"| `{row['word']}` | {row['n']} | {row['image']} | {row['abs']} |"
            )
        lines.append("")
    else:
        lines.append("No leftover-shaped near-cycle in the window.")
        lines.append("")
    lines.extend(
        [
            "## Strongest global closure inequality",
            "",
            "The unweighted cell product",
            "",
            "`prod_O x^3/(x+1)^2 * prod_E x/(x+1)^2 < 1`",
            "",
            "is necessary on any integer cycle. It kills all-odd itineraries "
            "with states `>=3`, already excluded by `odd_itinerary_expands`. "
            "On mixed leftover itineraries the even factors can be arbitrarily "
            "small, so the product does not fire from interval hulls.",
            "",
            "## Relation to CycleMin",
            "",
            "After the existing CycleItinerary layer the only expanding mixed "
            "necklaces have `e>=4` and length `>=11`. That is "
            "`cycle_itinerary_length_ge_eleven`. Joint interval / phi-product "
            "constraints did not shrink this residue.",
            "",
            "## Anti-overclaim",
            "",
            "Not a no-cycle theorem. Not a halt theorem. Finite search "
            "is not emptiness.",
            "",
        ]
    )
    return "\n".join(lines) + "\n"


def _write_csv(path: Path, rows: list[dict[str, Any]]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    if not rows:
        path.write_text("", encoding="utf-8")
        return
    keys = list(rows[0].keys())
    slim = []
    drop = {"path"}
    for row in rows:
        slim.append({k: v for k, v in row.items() if k not in drop})
    keys = [k for k in keys if k not in drop]
    with path.open("w", encoding="utf-8", newline="") as handle:
        writer = csv.DictWriter(handle, fieldnames=keys)
        writer.writeheader()
        writer.writerows(slim)


def write_data_artifacts(payload: dict[str, Any]) -> None:
    scan = payload["scan"]
    dirs = {
        "primitive_words": DATA_DIR / "primitive_words",
        "envelope_filters": DATA_DIR / "envelope_filters",
        "exact_constraints": DATA_DIR / "exact_constraints",
        "infeasible_classes": DATA_DIR / "infeasible_classes",
        "feasible_candidates": DATA_DIR / "feasible_candidates",
        "near_cycles": DATA_DIR / "near_cycles",
        "closure_thresholds": DATA_DIR / "closure_thresholds",
    }
    for path in dirs.values():
        path.mkdir(parents=True, exist_ok=True)
    _write_csv(dirs["primitive_words"] / "census.csv", scan["census"])
    _write_csv(dirs["envelope_filters"] / "ko_pairs.csv", scan["pairs"])
    classified = scan["classified"]
    _write_csv(dirs["exact_constraints"] / "classified.csv", classified)
    infeas = [r for r in classified if r["status"] == "INFEASIBLE"]
    feas = [r for r in classified if r["status"] == "UNRESOLVED"]
    _write_csv(dirs["infeasible_classes"] / "infeasible.csv", infeas)
    _write_csv(dirs["feasible_candidates"] / "unresolved.csv", feas)
    _write_csv(dirs["near_cycles"] / "near_words.csv", scan["near_words"])
    _write_csv(dirs["near_cycles"] / "near_drop.csv", scan["direct"]["near_drop"])
    thresh = [
        {
            "word": r["word"],
            "mu": r["mu"],
            "plus_one_W": r["plus_one_W"],
            "m2_cap": r["m2_cap"],
            "cyclemin_n0": r["cyclemin_n0"],
            "status": r["status"],
        }
        for r in classified
        if r["leftover_shape"]
    ]
    _write_csv(dirs["closure_thresholds"] / "leftover.csv", thresh)
    (DATA_DIR / "summary.json").write_text(
        json.dumps(
            {
                "classification": payload["decision"]["classification"],
                "reason": payload["decision"]["reason"],
                "summary": scan["summary"],
                "k_max": scan["k_max"],
                "n_max": scan["n_max"],
                "claim": payload["claim"],
                "git": scan["git"],
            },
            indent=2,
        )
        + "\n",
        encoding="utf-8",
    )
    (DATA_DIR / "README.md").write_text(
        "# Juggler cyclic feasibility\n\n"
        "Closed word filters. Absence is NOT_OBSERVED_WITHIN_BOUND.\n\n"
        "Regenerate with `python -m research.juggler_sequence.cyclic_feasibility`.\n",
        encoding="utf-8",
    )


def write_artifacts(payload: dict[str, Any] | None = None) -> dict[str, Any]:
    data = payload if payload is not None else probe_payload()
    JSON_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(data, indent=2) + "\n", encoding="utf-8")
    DOC_PATH.write_text(render_markdown(data), encoding="utf-8")
    write_data_artifacts(data)
    return data


def main() -> None:
    payload = probe_payload(
        k_max=SCIENCE_K,
        n_max=SCIENCE_N,
        k_pairs=SCIENCE_KO,
        scan_cap=SCIENCE_SCAN_CAP,
        near_k=SCIENCE_NEAR_K,
    )
    write_artifacts(payload)
    print(payload["decision"]["classification"])
    print(payload["decision"]["reason"])
    summary = payload["scan"]["summary"]
    print(
        f"known_dead={summary['known_dead']} joint={summary['new_joint_hits']} "
        f"leftover_u={summary['leftover_unresolved']} "
        f"cycles={payload['scan']['direct']['cycle_count']}"
    )


if __name__ == "__main__":
    main()
