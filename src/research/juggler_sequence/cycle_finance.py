"""Cycle finance inequality for the Juggler floor-power map.

Not a halt theorem, not an escape statement, not a corridor
extension, and not a windowed population census.

A hypothetical cycle word is formally expanding (2^L < 3^o) yet the
orbit returns exactly, so the multiplicative surplus is financed by
floor defects, which are relatively O(1/x) in logarithms. The
dossier docs/problems/juggler_cycle_finance.md proves

    1 - 2^L/3^o  <=  (6/5) * sum 1/(x_i ln x_i)  <=  (6/5) L/(n ln n)

for any cycle with all states >= 12, hence

    n ln n  <=  (6/5) * L * 3^o / (3^o - 2^L),

worst at the minimal admissible o. Phase 0 tabulates the resulting
per-length minimum bound n_max(L) exactly for L <= 10^5, verifies a
descent-induction floor (every n <= N0 reaches 1), and stress-tests
the per-step bound eps_i <= (6/5)/x_{i+1} on real orbit segments.
A verified floor N0 excludes every length with n_max(L) <= N0.
The length-only parity refinement charges even states at n^2 and
internal odds at floor(n^{3/2}); write_parity_artifacts records
that table as exceptions_parity.json without touching the crude
exceptions.json.
Lean: CycleFinance.lean (cycleMin_finance, no_cycle_itinerary_length_le_nineteen,
cycle_itinerary_length_eighty_four_or_ge_eighty_five, cycle_itinerary_eliahou_leftover)
and CycleHeightFinance.lean
(cycle_itinerary_length_eighty_four_m_ge_three_or_ge_eighty_five).
Eliahou leftover: period 84, or a listed near-convergent, or >= 10^5.
The laboratory leftover is period 84 with at least three odd-runs,
or length >= 85.
"""

from __future__ import annotations

import hashlib
import json
import math
import os
import subprocess
import sys
import time
from concurrent.futures import ProcessPoolExecutor, as_completed
from fractions import Fraction
from math import isqrt
from pathlib import Path
from typing import Any

from research.juggler_sequence.lean_paths import (
    CYCLE_FINANCE,
    CYCLE_HEIGHT_FINANCE,
    JUGGLER_DIR,
    JUGGLER_PAPER_BARREL,
    has_named,
    juggler_text,
)

REPO_ROOT = Path(__file__).resolve().parents[3]
JSON_PATH = REPO_ROOT / "docs" / "research" / "juggler_cycle_finance.json"
DOC_PATH = REPO_ROOT / "docs" / "research" / "juggler_cycle_finance.md"
DATA_DIR = REPO_ROOT / "data" / "research" / "juggler" / "cycle_finance"

CLASS_GREEN = "CYCLE_FINANCE_GREEN"
CLASS_PARK = "CYCLE_FINANCE_PARK"
CLASS_CLOSED = "CYCLE_FINANCE_CLOSED"
CLASS_INCOMPLETE = "CYCLE_FINANCE_INCOMPLETE"

EPS_CONST = 1.2  # -ln(1-d) <= (6/5) d on [0, 1/6]
C_STAR = 6.0 * math.log(1.2)  # optimal uniform coeff 6 log(6/5) on [0, 1/6]
MIN_STATE = 12  # Lean reachesOne_of_lt_twelve: every n <= 11 reaches 1
LEAN_FLOOR = 11
PUBLISHED_FLOOR = 1_000_000
PARITY_REL_GUARD = 1e-9
PARITY_ABS_PAD = 1e-18
PARITY_SPOTLIGHT = (1053, 1054, 25780, 25781)

SCIENCE_L_MAX = 100_000
SCIENCE_FLOOR = 68_000_000
SCIENCE_SEEDS = (25, 27, 37, 365, 1999, 30817, 1_000_003)
TEST_L_MAX = 400
TEST_FLOOR = 2_000
TEST_SEEDS = (25, 37, 365)

REPORT_FLOORS = (11, 1_000, 1_000_000, 2_000_000, 68_000_000, 10**9)
GREEN_PREFIX = 100
STEP_CAP = 100_000
# Hard seeds at the 26.3M floor: 13782577 peaks at 160M bits,
# 13184021 at 269M bits. 512M is the working cap.
# Override with JUGGLER_FLOOR_BIT_CAP.
BIT_CAP = 512_000_000
PROGRESS_MIN_N = 100_000
PROGRESS_CHUNK = 250_000
PROGRESS_PATH = DATA_DIR / "floor_progress.json"
EXCEPTION_LIST_CAP = 500
ELIAHOU_TABLE_CUTOFF = 100_000
ELIAHOU_LEAN_PERIOD = 84

# L <= 8 with n_max(L) <= 11: finance + the Lean residual floor kill
# these lengths without the census; {3, 6} stay census-only.
EXPECTED_LEAN_KILL = (1, 2, 4, 5, 7, 8)

EXISTING_LEAN = (
    "cycle_itinerary_formally_expanding",
    "global_defect_identity",
    "no_cycle_itinerary_length_le_eight",
    "reachesOne_of_lt_twelve",
    "cycle_peak_finance",
    "cycleMin_finance",
    "cycle_finance_min_thirteen",
    "no_cycle_itinerary_length_le_ten",
    "cycle_itinerary_length_eleven_or_ge_fourteen",
    "reachesOne_of_lt_fifty_three",
    "cycle_finance_min_fifty_three",
    "finance_excludes_length_eleven",
    "no_cycle_itinerary_length_le_eleven",
    "cycle_itinerary_length_ge_fourteen",
    "finance_excludes_length_fourteen",
    "no_cycle_itinerary_length_le_eighteen",
    "cycle_itinerary_length_nineteen_or_ge_thirty",
    "cycle_itinerary_length_nineteen_or_ge_twenty",
    "eliahouTableCutoff",
    "EliahouLeftover",
    "EliahouTable",
    "cycle_itinerary_eliahou_leftover",
    "reachesOne_of_lt_two_hundred_fifty_seven",
    "cycle_finance_min_two_hundred_fifty_seven",
    "finance_excludes_length_nineteen",
    "no_cycle_itinerary_length_le_nineteen",
    "cycle_itinerary_length_ge_thirty",
    "cycle_itinerary_length_thirty_eight_or_ge_thirty_nine",
    "finance_excludes_length_thirtyeight",
    "cycle_itinerary_length_fifty_seven_or_ge_fifty_eight",
    "reachesOne_of_lt_two_hundred_sixty_one",
    "cycle_finance_min_two_hundred_sixty_one",
    "finance_excludes_length_fiftyseven",
    "finance_excludes_length_seventysix",
    "cycle_itinerary_length_eighty_four_or_ge_eighty_five",
    "cycle_itinerary_length_eighty_four_m_ge_three_or_ge_eighty_five",
)

FORBIDDEN_THEOREMS = (
    "juggler_reaches_one",
    "no_cycle_itinerary_any_length",
    "no_juggler_escape",
    "no_cycle_itinerary_length_eleven",
)

FORBIDDEN_NEW_API = (
    "FinanceInequality",
    "FinanceBound",
)

REQUIRED_LEAN_FILES = (CYCLE_FINANCE, CYCLE_HEIGHT_FINANCE)
FORBIDDEN_LEAN_FILES = (JUGGLER_DIR / "Finance.lean",)
PAPER_REQUIRED_IMPORT = "import Problems.Juggler.CycleFinance"
PAPER_FORBIDDEN = (
    "import Problems.Juggler.CycleHeightFinance",
    "FinanceInequality",
    "FinanceBound",
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


def n_max_from_bound(bound: float) -> int:
    """Largest n >= 1 with n*ln(n) <= bound. Conservative upward margin."""

    bound = bound * (1.0 + 1e-9) + 1.0
    if 2 * math.log(2) > bound:
        return 1
    hi = 4
    while hi * math.log(hi) <= bound:
        hi *= 2
    lo = 2
    while lo < hi:
        mid = (lo + hi + 1) // 2
        if mid * math.log(mid) <= bound:
            lo = mid
        else:
            hi = mid - 1
    return lo


def finance_rows(l_max: int) -> list[dict[str, Any]]:
    """Exact table L -> (o_min, theta, bound B, n_max). Bignum only.

    theta = (3^o - 2^L)/3^o = 1 - 2^L/3^o at the minimal admissible o.
    """

    rows: list[dict[str, Any]] = []
    pow2 = 1
    pow3 = 1
    o = 0
    best_theta = math.inf
    for length in range(1, l_max + 1):
        pow2 <<= 1
        while pow3 <= pow2:
            pow3 *= 3
            o += 1
        theta = (pow3 - pow2) / pow3
        bound = EPS_CONST * length / theta
        record = theta < best_theta
        if record:
            best_theta = theta
        rows.append(
            {
                "L": length,
                "o": o,
                "theta": theta,
                "bound": bound,
                "n_max": n_max_from_bound(bound),
                "record": record,
            }
        )
    return rows


def first_odd_image(n: int) -> int:
    """T(n) for odd n: floor(n^{3/2}) = isqrt(n^3)."""

    return isqrt(n * n * n)


def adversarial_valley_count(length: int, odd_count: int) -> int:
    """Worst-case odd-run count on a CycleMin: m ≤ min(o, e).

    A CycleMin word ends even (`cycleMin_not_end_odd`), so e ≥ 1
    and each odd-run is preceded by an even letter, hence m ≤ e.
    If e = 0 the table still evaluates at o_min; charge every odd
    at n (the conservative all-valley bound).
    """

    even_count = length - odd_count
    if even_count <= 0:
        return odd_count
    return min(odd_count, even_count)


def parity_sum_terms(n: int, length: int, odd_count: int) -> float:
    """Upper bound on Σ 1/(x_i ln x_i) at a CycleMin start n.

    Valleys (at most e) sit at n; other odds sit at t = ⌊n^{3/2}⌋;
    evens sit at n² (`cycleMin_even_ge_sq`).
    """

    if n < 3:
        return math.inf
    even_count = length - odd_count
    valleys = adversarial_valley_count(length, odd_count)
    climb = max(odd_count - valleys, 0)
    log_n = math.log(n)
    valley_term = valleys / (n * log_n)
    image = first_odd_image(n)
    if image < 3:
        climb_term = math.inf
    else:
        climb_term = climb / (image * math.log(image))
    even_term = even_count / (n * n * (2.0 * log_n))
    return valley_term + climb_term + even_term


def parity_rhs(
    n: int,
    length: int,
    odd_count: int,
    *,
    const: float = EPS_CONST,
) -> float:
    """Length-only joint-minima ceiling for θ at CycleMin n."""

    return const * parity_sum_terms(n, length, odd_count)


def parity_rhs_upper(
    n: int,
    length: int,
    odd_count: int,
    *,
    const: float = EPS_CONST,
) -> float:
    raw = parity_rhs(n, length, odd_count, const=const)
    if not math.isfinite(raw):
        return math.inf
    return raw * (1.0 + PARITY_REL_GUARD) + PARITY_ABS_PAD


def parity_rhs_lower(
    n: int,
    length: int,
    odd_count: int,
    *,
    const: float = EPS_CONST,
) -> float:
    raw = parity_rhs(n, length, odd_count, const=const)
    if not math.isfinite(raw):
        return 0.0
    return max(0.0, raw * (1.0 - PARITY_REL_GUARD) - PARITY_ABS_PAD)


def parity_excludes(
    length: int,
    odd_count: int,
    theta: float,
    n0: int,
    *,
    const: float = EPS_CONST,
) -> bool:
    """Exclude only when a lower bound on θ exceeds an upper bound on the RHS.

    Cycle minimum is at least n0 + 1 (every n ≤ n0 reaches 1).
    """

    start = max(n0 + 1, MIN_STATE)
    theta_lo = theta * (1.0 - PARITY_REL_GUARD)
    return theta_lo > parity_rhs_upper(
        start, length, odd_count, const=const
    )


def parity_survives_floor(
    length: int,
    odd_count: int,
    theta: float,
    n0: int,
    *,
    const: float = EPS_CONST,
) -> bool:
    """Survive only when an upper bound on θ is below a lower bound on the RHS."""

    start = max(n0 + 1, MIN_STATE)
    theta_hi = theta * (1.0 + PARITY_REL_GUARD)
    return theta_hi < parity_rhs_lower(
        start, length, odd_count, const=const
    )


def parity_n_max(
    length: int,
    odd_count: int,
    theta: float,
    *,
    const: float = EPS_CONST,
) -> int:
    """Largest n at which the padded inequality can still hold.

    Uses an inflated RHS, so the returned n_max is slightly large
    (conservative: do not exclude a length whose true n_max is
    just above the floor).
    """

    def holds(n: int) -> bool:
        return theta <= parity_rhs_upper(
            n, length, odd_count, const=const
        )

    if not holds(MIN_STATE):
        lo = 2
        hi = MIN_STATE - 1
        if not holds(lo):
            return 1
        while lo < hi:
            mid = (lo + hi + 1) // 2
            if holds(mid):
                lo = mid
            else:
                hi = mid - 1
        return lo
    hi = MIN_STATE
    while holds(hi):
        if hi > 10**18:
            return hi
        nxt = hi * 2
        if nxt <= hi:
            return hi
        hi = nxt
    lo = hi // 2
    while lo < hi:
        mid = (lo + hi + 1) // 2
        if holds(mid):
            lo = mid
        else:
            hi = mid - 1
    return lo


def parity_finance_rows(
    l_max: int,
    *,
    const: float = EPS_CONST,
) -> list[dict[str, Any]]:
    """Length-only parity table L -> (o_min, theta, n_max).

    o_min is exact integer (3^o > 2^L). n_max uses the padded
    joint-minima comparison at m = e = L − o.
    """

    rows: list[dict[str, Any]] = []
    pow2 = 1
    pow3 = 1
    o = 0
    best_theta = math.inf
    for length in range(1, l_max + 1):
        pow2 <<= 1
        while pow3 <= pow2:
            pow3 *= 3
            o += 1
        theta = (pow3 - pow2) / pow3
        record = theta < best_theta
        if record:
            best_theta = theta
        even_count = length - o
        rows.append(
            {
                "L": length,
                "o": o,
                "e": even_count,
                "theta": theta,
                "n_max": parity_n_max(length, o, theta, const=const),
                "record": record,
            }
        )
    return rows


def parity_floor_status(
    row: dict[str, Any],
    floor: int,
    *,
    const: float = EPS_CONST,
) -> str:
    """certified_exclude | certified_survive | uncertain."""

    length = row["L"]
    odd_count = row["o"]
    theta = row["theta"]
    excluded = parity_excludes(
        length, odd_count, theta, floor, const=const
    )
    survives = parity_survives_floor(
        length, odd_count, theta, floor, const=const
    )
    if excluded and not survives:
        return "certified_exclude"
    if survives and not excluded:
        return "certified_survive"
    return "uncertain"


def sha256_int_list(values: list[int]) -> str:
    payload = json.dumps(values, separators=(",", ":")).encode("ascii")
    return hashlib.sha256(payload).hexdigest()


def parity_scan(
    *,
    l_max: int = SCIENCE_L_MAX,
    floor: int = PUBLISHED_FLOOR,
    const: float = EPS_CONST,
) -> dict[str, Any]:
    """Certified length-only parity table at a published descent floor."""

    rows = parity_finance_rows(l_max, const=const)
    statuses = [parity_floor_status(row, floor, const=const) for row in rows]
    excluded = [
        row["L"]
        for row, status in zip(rows, statuses)
        if status == "certified_exclude"
    ]
    survivors = [
        row["L"]
        for row, status in zip(rows, statuses)
        if status == "certified_survive"
    ]
    uncertain = [
        row["L"]
        for row, status in zip(rows, statuses)
        if status == "uncertain"
    ]
    first = survivors[0] if survivors else None
    prefix = (first - 1) if first else rows[-1]["L"]
    spotlight = {
        str(length): next(row for row in rows if row["L"] == length)
        for length in PARITY_SPOTLIGHT
        if length <= l_max
    }
    records = [
        {
            "L": row["L"],
            "o": row["o"],
            "e": row["e"],
            "theta": row["theta"],
            "n_max": row["n_max"],
        }
        for row in rows
        if row["record"]
    ]
    return {
        "bound": "parity_6/5",
        "const": const,
        "c_star": C_STAR,
        "l_max": l_max,
        "floor": floor,
        "first_exception": first,
        "contiguous_prefix": prefix,
        "count": len(survivors),
        "excluded_count": len(excluded),
        "uncertain": uncertain,
        "uncertain_count": len(uncertain),
        "lengths": survivors,
        "records": records,
        "spotlight": {
            key: {
                "L": row["L"],
                "o": row["o"],
                "e": row["e"],
                "theta": row["theta"],
                "n_max": row["n_max"],
                "status": parity_floor_status(row, floor, const=const),
            }
            for key, row in spotlight.items()
        },
        "sha256_lengths": sha256_int_list(survivors),
        "certified_first_survivor_25781": first == 25781
        and prefix == 25780
        and not uncertain,
        "halt_theorem": False,
        "no_cycle_all_lengths": False,
    }


def write_parity_artifacts(
    payload: dict[str, Any] | None = None,
    *,
    l_max: int = SCIENCE_L_MAX,
    floor: int = PUBLISHED_FLOOR,
) -> dict[str, Any]:
    """Write exceptions_parity.json. Does not touch the crude table."""

    data = payload if payload is not None else parity_scan(
        l_max=l_max, floor=floor
    )
    DATA_DIR.mkdir(parents=True, exist_ok=True)
    path = DATA_DIR / "exceptions_parity.json"
    path.write_text(json.dumps(data, indent=2) + "\n", encoding="utf-8")
    return data


LATER_VALLEY_P = 9.0 / 8.0  # least expanding even-terminating circuit OOE


def o_min_and_theta(length: int) -> tuple[int, float]:
    """Minimal admissible o and θ = 1 − 2^L/3^o."""

    pow2 = 1 << length
    pow3 = 1
    odd_count = 0
    while pow3 <= pow2:
        pow3 *= 3
        odd_count += 1
    return odd_count, (pow3 - pow2) / pow3


def weight_sum_terms(
    n: int,
    length: int,
    odd_count: int,
    *,
    later_valley_p: float = 1.0,
) -> float:
    """Naive weight form Σ 1/(P x ln n) at CycleMin n.

    Valleys sit at n, internals at t = ⌊n^{3/2}⌋, evens at n².
    The start valley is charged at P = 1; any remaining valleys
    at later_valley_p (1 for P ≡ 1, 9/8 for the OOE test).
    Internals and evens stay at P = 1.
    """

    if n < 3:
        return math.inf
    even_count = length - odd_count
    valleys = adversarial_valley_count(length, odd_count)
    climb = max(odd_count - valleys, 0)
    log_n = math.log(n)
    image = first_odd_image(n)
    if image < 3:
        return math.inf
    if valleys <= 0:
        valley_term = 0.0
    elif later_valley_p <= 1.0 or valleys == 1:
        valley_term = valleys / (n * log_n)
    else:
        valley_term = (1.0 / (n * log_n)) + (
            (valleys - 1) / (later_valley_p * n * log_n)
        )
    climb_term = climb / (image * log_n)
    even_term = even_count / (n * n * log_n)
    return valley_term + climb_term + even_term


def weight_rhs(
    n: int,
    length: int,
    odd_count: int,
    *,
    const: float = EPS_CONST,
    later_valley_p: float = 1.0,
) -> float:
    return const * weight_sum_terms(
        n, length, odd_count, later_valley_p=later_valley_p
    )


def weight_rhs_upper(
    n: int,
    length: int,
    odd_count: int,
    *,
    const: float = EPS_CONST,
    later_valley_p: float = 1.0,
) -> float:
    raw = weight_rhs(
        n, length, odd_count, const=const, later_valley_p=later_valley_p
    )
    if not math.isfinite(raw):
        return math.inf
    return raw * (1.0 + PARITY_REL_GUARD) + PARITY_ABS_PAD


def weight_excludes(
    length: int,
    odd_count: int,
    theta: float,
    n0: int,
    *,
    const: float = EPS_CONST,
    later_valley_p: float = 1.0,
) -> bool:
    start = max(n0 + 1, MIN_STATE)
    theta_lo = theta * (1.0 - PARITY_REL_GUARD)
    return theta_lo > weight_rhs_upper(
        start,
        length,
        odd_count,
        const=const,
        later_valley_p=later_valley_p,
    )


def prefix_weight_row(
    length: int,
    *,
    floor: int = PUBLISHED_FLOOR,
    const: float = EPS_CONST,
) -> dict[str, Any]:
    odd_count, theta = o_min_and_theta(length)
    start = max(floor + 1, MIN_STATE)
    parity = parity_rhs(start, length, odd_count, const=const)
    p1 = weight_rhs(start, length, odd_count, const=const, later_valley_p=1.0)
    p98 = weight_rhs(
        start, length, odd_count, const=const, later_valley_p=LATER_VALLEY_P
    )
    return {
        "L": length,
        "o": odd_count,
        "e": length - odd_count,
        "theta": theta,
        "n": start,
        "parity_rhs": parity,
        "weight_P_ge_1_rhs": p1,
        "weight_later_valley_9_8_rhs": p98,
        "parity_excludes": parity_excludes(
            length, odd_count, theta, floor, const=const
        ),
        "weight_P_ge_1_excludes": weight_excludes(
            length, odd_count, theta, floor, const=const, later_valley_p=1.0
        ),
        "weight_later_valley_9_8_excludes": weight_excludes(
            length,
            odd_count,
            theta,
            floor,
            const=const,
            later_valley_p=LATER_VALLEY_P,
        ),
        "weight_P_ge_1_ge_parity": p1 + PARITY_ABS_PAD >= parity,
    }


def prefix_weight_scan(
    *,
    floor: int = PUBLISHED_FLOOR,
    const: float = EPS_CONST,
) -> dict[str, Any]:
    """Compare prefix-weight bounds on the parity leftover set."""

    payload = json.loads(
        (DATA_DIR / "exceptions_parity.json").read_text(encoding="utf-8")
    )
    lengths = list(payload["lengths"])
    rows = [
        prefix_weight_row(length, floor=floor, const=const)
        for length in lengths
    ]
    killed_p1 = [row["L"] for row in rows if row["weight_P_ge_1_excludes"]]
    killed_98 = [
        row["L"] for row in rows if row["weight_later_valley_9_8_excludes"]
    ]
    weaker = [row["L"] for row in rows if not row["weight_P_ge_1_ge_parity"]]
    spotlight = next(row for row in rows if row["L"] == 25781)
    return {
        "bound": "prefix_weight",
        "floor": floor,
        "n": max(floor + 1, MIN_STATE),
        "later_valley_p": LATER_VALLEY_P,
        "leftover_count": len(rows),
        "killed_by_parity": [row["L"] for row in rows if row["parity_excludes"]],
        "killed_by_weight_P_ge_1": killed_p1,
        "killed_by_weight_later_valley_9_8": killed_98,
        "weight_P_ge_1_weaker_failures": weaker,
        "no_leftover_excluded": not killed_p1 and not killed_98,
        "certified_no_leftover_excluded": not killed_p1
        and not any(row["parity_excludes"] for row in rows),
        "spotlight_25781": spotlight,
        "rows": rows,
        "halt_theorem": False,
        "no_cycle_all_lengths": False,
    }


def write_prefix_weight_artifacts(
    payload: dict[str, Any] | None = None,
    *,
    floor: int = PUBLISHED_FLOOR,
) -> dict[str, Any]:
    data = payload if payload is not None else prefix_weight_scan(floor=floor)
    DATA_DIR.mkdir(parents=True, exist_ok=True)
    path = DATA_DIR / "prefix_weights.json"
    path.write_text(json.dumps(data, indent=2) + "\n", encoding="utf-8")
    return data


def eliahou_leftover(
    length: int,
    exceptions: list[int] | tuple[int, ...] | set[int],
    *,
    cutoff: int = ELIAHOU_TABLE_CUTOFF,
) -> bool:
    """Eliahou leftover: Lean period, listed near-convergent, or >= cutoff."""

    return (
        length == ELIAHOU_LEAN_PERIOD
        or length in exceptions
        or cutoff <= length
    )


def eliahou_exceptions(
    rows: list[dict[str, Any]],
    floor: int,
) -> list[int]:
    """Lengths whose finance n_max exceeds the verified floor."""

    return [row["L"] for row in rows if row["n_max"] > floor]


def eliahou_table_holds(
    rows: list[dict[str, Any]],
    floor: int,
    exceptions: list[int] | tuple[int, ...] | set[int],
    *,
    cutoff: int = ELIAHOU_TABLE_CUTOFF,
) -> bool:
    """Every L in [30, cutoff) outside exceptions has n_max <= floor."""

    exception_set = set(exceptions)
    for row in rows:
        length = row["L"]
        if 30 <= length < cutoff and length not in exception_set:
            if row["n_max"] > floor:
                return False
    return True


def eliahou_packaging(
    rows: list[dict[str, Any]],
    floor: int,
    *,
    cutoff: int = ELIAHOU_TABLE_CUTOFF,
) -> dict[str, Any]:
    """Theorem-shaped leftover from the existing finance table."""

    exceptions = eliahou_exceptions(rows, floor)
    nineteen = next((row for row in rows if row["L"] == ELIAHOU_LEAN_PERIOD), None)
    return {
        "lean_period": ELIAHOU_LEAN_PERIOD,
        "cutoff": cutoff,
        "exceptions": exceptions,
        "exception_count": len(exceptions),
        "table_holds": eliahou_table_holds(
            rows, floor, exceptions, cutoff=cutoff
        ),
        "nineteen_computationally_excluded": (
            nineteen is not None and nineteen["n_max"] <= floor
        ),
    }


def exception_summary(
    rows: list[dict[str, Any]],
    floors: tuple[int, ...] = REPORT_FLOORS,
) -> list[dict[str, Any]]:
    """Per floor: lengths whose finance bound exceeds the floor."""

    out = []
    for floor in floors:
        exceptions = [row["L"] for row in rows if row["n_max"] > floor]
        first = exceptions[0] if exceptions else None
        out.append(
            {
                "floor": floor,
                "count": len(exceptions),
                "first_exception": first,
                "contiguous_prefix": (first - 1) if first else rows[-1]["L"],
                "lengths": exceptions[:EXCEPTION_LIST_CAP],
                "truncated": len(exceptions) > EXCEPTION_LIST_CAP,
            }
        )
    return out


def census_cross_check(rows: list[dict[str, Any]]) -> dict[str, Any]:
    """Compare finance + Lean floor against the length-<=8 Lean census."""

    small = {row["L"]: row["n_max"] for row in rows if row["L"] <= 8}
    killed = tuple(sorted(length for length, nm in small.items() if nm <= LEAN_FLOOR))
    return {
        "n_max_by_length": small,
        "killed_by_lean_floor": killed,
        "matches_expected": killed == EXPECTED_LEAN_KILL,
        "census_only_lengths": tuple(
            sorted(set(small) - set(killed))
        ),
    }


def _odd_chunk_first_passage(
    start: int, stop: int, step_cap: int, bit_cap: int
) -> tuple[list[int], list[int], list[int], int, int, int, int, int]:
    """Walk odds in [start, stop].

    Returns step-cap failures, bit-cap failures, other failures,
    max_steps, hardest, max_bits, max_bits_seed, total_steps.
    Parity and the iterate use exact integer arithmetic only.
    """

    step_failures: list[int] = []
    bit_failures: list[int] = []
    other_failures: list[int] = []
    max_steps = 0
    hardest = 0
    max_bits = 0
    max_bits_seed = 0
    total_steps = 0
    if start % 2 == 0:
        start += 1
    for n in range(start, stop + 1, 2):
        x = n
        steps = 0
        ok = True
        local_bits = 0
        while x >= n:
            if x % 2 == 0:
                x = isqrt(x)
            else:
                x = isqrt(x * x * x)
            steps += 1
            bits = x.bit_length()
            if bits > local_bits:
                local_bits = bits
            if steps > step_cap:
                step_failures.append(n)
                ok = False
                break
            if bits > bit_cap:
                bit_failures.append(n)
                ok = False
                break
        total_steps += steps
        if local_bits > max_bits:
            max_bits = local_bits
            max_bits_seed = n
        if ok and steps > max_steps:
            max_steps = steps
            hardest = n
    return (
        step_failures,
        bit_failures,
        other_failures,
        max_steps,
        hardest,
        max_bits,
        max_bits_seed,
        total_steps,
    )


def _floor_workers(n_top: int, workers: int | None) -> int:
    if workers is not None:
        return max(1, workers)
    if n_top < PROGRESS_MIN_N:
        return 1
    env = os.environ.get("JUGGLER_FLOOR_WORKERS")
    if env:
        return max(1, int(env))
    cpu = os.cpu_count() or 1
    return max(1, cpu - 1)


def _format_hms(seconds: float) -> str:
    total = max(0, int(seconds))
    hours, rem = divmod(total, 3600)
    minutes, secs = divmod(rem, 60)
    if hours:
        return f"{hours}:{minutes:02d}:{secs:02d}"
    return f"{minutes}:{secs:02d}"


def _report_floor_progress(payload: dict[str, Any]) -> None:
    DATA_DIR.mkdir(parents=True, exist_ok=True)
    PROGRESS_PATH.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")
    chunks = ""
    if "chunks_done" in payload and "chunks_total" in payload:
        chunks = f"  chunks={payload['chunks_done']}/{payload['chunks_total']}"
    line = (
        f"verify_floor {payload['pct']:5.1f}%  "
        f"n={payload['n']}/{payload['n_top']}  "
        f"{payload['rate_n_per_s']:.0f} n/s  "
        f"elapsed={payload['elapsed']}  eta={payload['eta']}  "
        f"hardest={payload['hardest_seed']} steps={payload['max_steps']}  "
        f"bits={payload['max_bits']}  fail={payload['failure_count']}"
        f"{chunks}"
    )
    print(line, file=sys.stderr, flush=True)


def verify_floor(
    n_top: int,
    *,
    step_cap: int = STEP_CAP,
    bit_cap: int = BIT_CAP,
    progress: bool | None = None,
    workers: int | None = None,
) -> dict[str, Any]:
    """Descent induction: every 2 <= n <= n_top has an iterate < n.

    Evens n >= 2 drop in one square-root step, so only odds are
    walked. By strong induction (base n=2 -> 1) every such n
    reaches 1. Exact integer arithmetic; failures list is expected
    empty. Large windows print progress to stderr and
    ``data/research/juggler/cycle_finance/floor_progress.json``.
    """

    if progress is None:
        progress = n_top >= PROGRESS_MIN_N
    env_bits = os.environ.get("JUGGLER_FLOOR_BIT_CAP")
    if env_bits:
        bit_cap = max(bit_cap, int(env_bits))
    worker_count = _floor_workers(n_top, workers)
    max_steps = 0
    max_bits = 0
    hardest = 0
    max_bits_seed = 0
    total_steps = 0
    step_failures: list[int] = []
    bit_failures: list[int] = []
    other_failures: list[int] = []
    started = time.perf_counter()

    def absorb(
        chunk_step: list[int],
        chunk_bit: list[int],
        chunk_other: list[int],
        chunk_steps: int,
        chunk_hard: int,
        chunk_bits: int,
        chunk_bits_seed: int,
        chunk_total: int,
    ) -> None:
        nonlocal max_steps, max_bits, hardest, max_bits_seed, total_steps
        step_failures.extend(chunk_step)
        bit_failures.extend(chunk_bit)
        other_failures.extend(chunk_other)
        total_steps += chunk_total
        if chunk_bits > max_bits:
            max_bits = chunk_bits
            max_bits_seed = chunk_bits_seed
        if chunk_steps > max_steps:
            max_steps = chunk_steps
            hardest = chunk_hard

    def emit(n_done: int) -> None:
        elapsed = time.perf_counter() - started
        rate = n_done / elapsed if elapsed > 0 else 0.0
        remain = (n_top - n_done) / rate if rate > 0 else 0.0
        _report_floor_progress(
            {
                "n": n_done,
                "n_top": n_top,
                "pct": 100.0 * n_done / n_top if n_top else 100.0,
                "rate_n_per_s": rate,
                "elapsed_s": elapsed,
                "eta_s": remain,
                "elapsed": _format_hms(elapsed),
                "eta": _format_hms(remain),
                "hardest_seed": hardest,
                "max_steps": max_steps,
                "max_bits": max_bits,
                "max_bits_seed": max_bits_seed,
                "total_steps": total_steps,
                "failure_count": (
                    len(step_failures) + len(bit_failures) + len(other_failures)
                ),
                "bit_failure_count": len(bit_failures),
                "step_failure_count": len(step_failures),
                "workers": worker_count,
            }
        )

    chunks = [
        (start, min(start + PROGRESS_CHUNK - 1, n_top))
        for start in range(3, n_top + 1, PROGRESS_CHUNK)
    ]
    if worker_count == 1 or len(chunks) <= 1:
        for start, stop in chunks:
            absorb(*_odd_chunk_first_passage(start, stop, step_cap, bit_cap))
            if progress:
                emit(stop)
    else:
        if progress:
            print(
                f"verify_floor n_top={n_top} workers={worker_count} "
                f"chunks={len(chunks)}",
                file=sys.stderr,
                flush=True,
            )
        done = 0
        with ProcessPoolExecutor(max_workers=worker_count) as pool:
            futures = {
                pool.submit(
                    _odd_chunk_first_passage, start, stop, step_cap, bit_cap
                ): stop
                for start, stop in chunks
            }
            for future in as_completed(futures):
                absorb(*future.result())
                done += 1
                if progress:
                    # Chunk completions, not ordered n.
                    emit(min(n_top, done * PROGRESS_CHUNK))

    if progress:
        emit(n_top)

    failures = step_failures + bit_failures + other_failures
    return {
        "n_top": n_top,
        "verified": not failures,
        "failures": failures[:20],
        "step_failures": step_failures[:20],
        "bit_failures": bit_failures[:20],
        "max_first_passage_steps": max_steps,
        "hardest_seed": hardest,
        "max_bits_seen": max_bits,
        "max_bits_seed": max_bits_seed,
        "total_first_passage_steps": total_steps,
        "step_cap": step_cap,
        "bit_cap": bit_cap,
        "workers": worker_count,
        "elapsed_s": time.perf_counter() - started,
    }


def orbit_slack(seed: int, *, max_steps: int = 400) -> dict[str, Any]:
    """Per-step finance bookkeeping along a real orbit segment.

    Checks the exact step identity x'^2 = x^e - d with 0 <= d <= 2x',
    the relative bound eps <= (6/5)/x' for states >= 12, and the
    unrolled identity t_k = P_k (t_0 - sum eps_i / P_{i+1}).
    """

    x = seed
    t0 = math.log(seed)
    partial = Fraction(1)
    eps_sum_scaled = 0.0
    steps = 0
    checked = 0
    step_ok = True
    d_ok = True
    worst_margin = math.inf
    identity_err = 0.0
    eps_over_t = 0.0
    bound_over_t = 0.0
    d_ratio_sum = 0.0
    for _ in range(max_steps):
        if x < 2:
            break
        exponent = 1 if x % 2 == 0 else 3
        power = x if exponent == 1 else x * x * x
        nxt = isqrt(power)
        defect = power - nxt * nxt
        if not 0 <= defect <= 2 * nxt:
            d_ok = False
        delta = defect / power
        eps = -0.5 * math.log1p(-delta)
        if nxt >= MIN_STATE:
            checked += 1
            # 1/nxt via logs: nxt may exceed float range.
            inv_nxt = math.exp(-math.log(nxt))
            ratio = eps / (EPS_CONST * inv_nxt) if inv_nxt > 0.0 else 0.0
            worst_margin = min(worst_margin, 1.0 - ratio)
            if ratio > 1.0 + 1e-9:
                step_ok = False
            t_next = math.log(nxt)
            eps_over_t += eps / t_next
            bound_over_t += EPS_CONST * inv_nxt / t_next
            d_ratio_sum += defect / (2 * nxt)
        partial *= Fraction(exponent, 2)
        eps_sum_scaled += eps / float(partial)
        steps += 1
        if nxt > 1:
            predicted = float(partial) * (t0 - eps_sum_scaled)
            actual = math.log(nxt)
            scale = max(abs(actual), 1.0)
            identity_err = max(identity_err, abs(predicted - actual) / scale)
        x = nxt
    return {
        "seed": seed,
        "steps": steps,
        "checked_states": checked,
        "reached_one": x < 2,
        "step_bound_ok": step_ok,
        "defect_bound_ok": d_ok,
        "worst_margin": None if worst_margin is math.inf else worst_margin,
        "identity_rel_err": identity_err,
        "tightness": (eps_over_t / bound_over_t) if bound_over_t else None,
        "mean_defect_ratio": (d_ratio_sum / checked) if checked else None,
    }


def lean_api_present() -> dict[str, bool]:
    combined = juggler_text()
    named = {name: has_named(combined, name) for name in EXISTING_LEAN}
    forbidden = {
        f"has_{name}": has_named(combined, name) for name in FORBIDDEN_THEOREMS
    }
    paper = JUGGLER_PAPER_BARREL.read_text(encoding="utf-8")
    return {
        "sorry_free": "sorry" not in combined and "admit" not in combined,
        **named,
        **forbidden,
        **{
            f"has_api_{name}": has_named(combined, name)
            for name in FORBIDDEN_NEW_API
        },
        "cycle_finance_present": all(
            path.is_file() for path in REQUIRED_LEAN_FILES
        ),
        "no_extra_finance_file": not any(
            path.is_file() for path in FORBIDDEN_LEAN_FILES
        ),
        "cycle_finance_in_paper_barrel": PAPER_REQUIRED_IMPORT in paper,
        "not_in_paper_barrel": all(name not in paper for name in PAPER_FORBIDDEN),
    }


def run_probe(
    *,
    l_max: int = TEST_L_MAX,
    floor: int = TEST_FLOOR,
    seeds: tuple[int, ...] = TEST_SEEDS,
) -> dict[str, Any]:
    rows = finance_rows(l_max)
    floors = tuple(sorted(set(REPORT_FLOORS) | {floor}))
    exceptions = exception_summary(rows, floors)
    census = census_cross_check(rows)
    floor_check = verify_floor(floor)
    slack = [orbit_slack(seed) for seed in seeds]
    records = [
        {key: row[key] for key in ("L", "o", "theta", "n_max")}
        for row in rows
        if row["record"]
    ]
    achieved = next(item for item in exceptions if item["floor"] == floor)
    leftover = eliahou_packaging(rows, floor, cutoff=min(l_max, ELIAHOU_TABLE_CUTOFF))
    return {
        "l_max": l_max,
        "floor": floor,
        "floor_check": floor_check,
        "records": records,
        "exceptions": exceptions,
        "eliahou": leftover,
        "achieved": achieved,
        "census": census,
        "slack": slack,
        "git": git_commit(),
        "halt_theorem": False,
        "no_cycle_all_lengths": False,
        "escape_claim": False,
        "corridor_extension": False,
        "population_census_reopen": False,
    }


def classify(scan: dict[str, Any], lean: dict[str, bool]) -> dict[str, Any]:
    lean_ok = (
        lean["sorry_free"]
        and all(lean[name] for name in EXISTING_LEAN)
        and not any(lean[f"has_{name}"] for name in FORBIDDEN_THEOREMS)
        and not any(lean[f"has_api_{name}"] for name in FORBIDDEN_NEW_API)
        and lean["cycle_finance_present"]
        and lean["no_extra_finance_file"]
        and lean["cycle_finance_in_paper_barrel"]
        and lean["not_in_paper_barrel"]
    )
    if not lean_ok:
        return {"classification": CLASS_INCOMPLETE, "reason": f"lean_ok={lean_ok}"}
    if scan["halt_theorem"] or scan["no_cycle_all_lengths"]:
        return {
            "classification": CLASS_INCOMPLETE,
            "reason": "out-of-scope claim",
        }
    slack_ok = all(
        row["step_bound_ok"] and row["defect_bound_ok"] for row in scan["slack"]
    )
    if not slack_ok:
        return {
            "classification": CLASS_CLOSED,
            "reason": (
                "the per-step bound eps <= (6/5)/x' or the defect bound "
                "d <= 2x' failed on a real orbit segment; the derivation "
                "constant does not hold as stated"
            ),
        }
    floor_ok = scan["floor_check"]["verified"]
    census_ok = scan["census"]["matches_expected"]
    prefix = scan["achieved"]["contiguous_prefix"]
    if floor_ok and census_ok and prefix >= GREEN_PREFIX:
        return {
            "classification": CLASS_GREEN,
            "reason": (
                "per-step finance bounds hold on every measured orbit step; "
                f"descent induction verifies every n <= {scan['floor']} "
                "reaches 1; finance excludes every cycle length "
                f"L <= {prefix} at once, far beyond the length-8 census; "
                "exceptional lengths are exactly the near-convergent ones"
            ),
        }
    if floor_ok and census_ok:
        return {
            "classification": CLASS_PARK,
            "reason": (
                "the inequality holds but the contiguous excluded prefix "
                f"is only {prefix}; the floor is too low for the first "
                "near-convergent length"
            ),
        }
    return {
        "classification": CLASS_PARK,
        "reason": (
            f"floor verified={floor_ok}, census cross-check={census_ok}; "
            "one of the supporting computations is incomplete"
        ),
    }


def probe_payload(
    *,
    l_max: int = TEST_L_MAX,
    floor: int = TEST_FLOOR,
    seeds: tuple[int, ...] = TEST_SEEDS,
) -> dict[str, Any]:
    scan = run_probe(l_max=l_max, floor=floor, seeds=seeds)
    lean = lean_api_present()
    decision = classify(scan, lean)
    return {
        "experiment": "juggler_cycle_finance",
        "engine_control_layer_modified": False,
        "anti_overclaim": {
            "halt_theorem": False,
            "no_cycle_all_lengths": False,
            "escape_claim": False,
            "corridor_extension": False,
            "population_census_reopen": False,
            "lean_finance_added": True,
            "floor_is_lean_verified": False,
        },
        "scan": scan,
        "lean": lean,
        "decision": decision,
        "search_method": (
            f"exact gap table L<={l_max}; descent-induction floor {floor}; "
            f"slack seeds {list(seeds)}"
        ),
    }


def render_markdown(payload: dict[str, Any]) -> str:
    decision = payload["decision"]
    scan = payload["scan"]
    floor_check = scan["floor_check"]
    lines = [
        "# Juggler cycle finance inequality",
        "",
        f"Status: **{decision['classification']}**",
        "",
        "Finance bound n ln n <= (6/5) L 3^o/(3^o - 2^L) on cycle minima.",
        "Not a halt theorem. Not a no-cycle-of-any-length theorem.",
        "The floor is COMPUTATIONALLY VERIFIED, not Lean.",
        "",
        "## Metadata",
        "",
        f"- classification: **{decision['classification']}**",
        f"- gap table: L <= `{scan['l_max']}` exact bignum",
        f"- floor: every 2 <= n <= `{scan['floor']}` reaches 1: "
        f"`{floor_check['verified']}` "
        f"(max first-passage steps `{floor_check['max_first_passage_steps']}` "
        f"at seed `{floor_check['hardest_seed']}`, "
        f"peak `{floor_check['max_bits_seen']}` bits)",
        f"- contiguous excluded prefix at this floor: "
        f"L <= `{scan['achieved']['contiguous_prefix']}`",
        f"- exceptional lengths at this floor: "
        f"`{scan['achieved']['count']}`",
        f"- Eliahou leftover: period `{scan['eliahou']['lean_period']}`, or "
        f"one of `{scan['eliahou']['exception_count']}` listed "
        f"near-convergents, or `>= {scan['eliahou']['cutoff']}` "
        f"(table holds `{scan['eliahou']['table_holds']}`; "
        f"lean period computationally excluded "
        f"`{scan['eliahou']['nineteen_computationally_excluded']}`)",
        "",
        decision["reason"] + ".",
        "",
        "## Census cross-check (L <= 8)",
        "",
        f"- n_max by length: `{scan['census']['n_max_by_length']}`",
        f"- killed by finance + Lean residual floor: "
        f"`{list(scan['census']['killed_by_lean_floor'])}`",
        f"- census-only lengths: "
        f"`{list(scan['census']['census_only_lengths'])}`",
        "",
        "## Record (near-convergent) lengths",
        "",
    ]
    for row in scan["records"]:
        lines.append(
            f"- L=`{row['L']}` o=`{row['o']}` theta=`{row['theta']:.3e}` "
            f"n_max=`{row['n_max']}`"
        )
    lines.extend(["", "## Exceptional lengths by floor", ""])
    for item in scan["exceptions"]:
        lines.append(
            f"- floor `{item['floor']}`: count `{item['count']}`, "
            f"first `{item['first_exception']}`, "
            f"contiguous prefix `{item['contiguous_prefix']}`"
        )
    lines.extend(["", "## Orbit slack", ""])
    for row in scan["slack"]:
        lines.append(
            f"- seed `{row['seed']}`: steps `{row['steps']}` "
            f"step bound ok `{row['step_bound_ok']}` "
            f"defect bound ok `{row['defect_bound_ok']}` "
            f"identity err `{row['identity_rel_err']:.2e}` "
            f"tightness `{row['tightness'] if row['tightness'] is None else round(row['tightness'], 4)}`"
        )
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


def write_data_artifacts(payload: dict[str, Any]) -> None:
    DATA_DIR.mkdir(parents=True, exist_ok=True)
    scan = payload["scan"]
    (DATA_DIR / "records.json").write_text(
        json.dumps(scan["records"], indent=2) + "\n", encoding="utf-8"
    )
    (DATA_DIR / "exceptions.json").write_text(
        json.dumps(scan["exceptions"], indent=2) + "\n", encoding="utf-8"
    )
    (DATA_DIR / "slack.json").write_text(
        json.dumps(scan["slack"], indent=2) + "\n", encoding="utf-8"
    )
    (DATA_DIR / "floor.json").write_text(
        json.dumps(scan["floor_check"], indent=2) + "\n", encoding="utf-8"
    )
    (DATA_DIR / "census_cross_check.json").write_text(
        json.dumps(scan["census"], indent=2) + "\n", encoding="utf-8"
    )
    summary = {
        "classification": payload["decision"]["classification"],
        "reason": payload["decision"]["reason"],
        "l_max": scan["l_max"],
        "floor": scan["floor"],
        "floor_verified": scan["floor_check"]["verified"],
        "contiguous_prefix": scan["achieved"]["contiguous_prefix"],
        "exception_count": scan["achieved"]["count"],
        "git": scan["git"],
    }
    (DATA_DIR / "summary.json").write_text(
        json.dumps(summary, indent=2) + "\n", encoding="utf-8"
    )
    (DATA_DIR / "README.md").write_text(
        "# Cycle finance inequality\n\n"
        "Finance bound n ln n <= (6/5) L 3^o/(3^o - 2^L) on Juggler cycle\n"
        "minima, exact gap table, descent-induction floor, orbit slack.\n"
        "Not a halt theorem. The floor is COMPUTATIONALLY VERIFIED.\n\n"
        "Regenerate with `python -m research.juggler_sequence.cycle_finance`.\n"
        "Length-only parity table: `exceptions_parity.json` "
        "(write_parity_artifacts; does not replace this crude table).\n",
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
        l_max=SCIENCE_L_MAX,
        floor=SCIENCE_FLOOR,
        seeds=SCIENCE_SEEDS,
    )
    write_artifacts(payload)
    scan = payload["scan"]
    print(payload["decision"]["classification"])
    print(payload["decision"]["reason"])
    print(
        f"floor_verified={scan['floor_check']['verified']} "
        f"prefix={scan['achieved']['contiguous_prefix']} "
        f"exceptions={scan['achieved']['count']} "
        f"records={len(scan['records'])}"
    )


if __name__ == "__main__":
    main()
