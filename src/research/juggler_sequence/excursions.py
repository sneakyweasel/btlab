"""First-return-below excursions for the Juggler floor-power map.

Not a Research Engine control-layer experiment. Not a halt theorem.
Defines τ_<, τ_≤, and the peak/return split, then certifies completed
returns only by exponent gap, first-defect compensation when the gap
is formable, or an exact peak-suffix comparison. Full-word Δ >
formal_gap is T<n rewritten and is not a certificate. ResidualStep is
not extended. A search-horizon miss is not a bound L.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import sqlite3
import subprocess
import time
from collections import Counter
from pathlib import Path
from typing import Any

from research.juggler_sequence.compensated_contraction import (
    first_defect_sufficient,
    formal_gap,
)
from research.juggler_sequence.envelope_defect import (
    first_nonexact_index,
    local_defect,
    tiny_deficit,
)
from research.juggler_sequence.equality_language import is_monochrome
from research.juggler_sequence.near_extremal_prefixes import exponent_gap
from research.juggler_sequence.power_algebra import local_tight
from research.juggler_sequence.lean_paths import ENVELOPE, RESIDUALS, juggler_text
from research.juggler_sequence.power_itineraries import (
    ANTI_OVERCLAIM,
    EXACT_POW_BITS,
    cmp_pow,
    floor_power,
    odd_count,
    word_of,
)

REPO_ROOT = Path(__file__).resolve().parents[3]
JSON_PATH = REPO_ROOT / "docs" / "research" / "juggler_excursions.json"
DOC_PATH = REPO_ROOT / "docs" / "research" / "juggler_excursions.md"
LEAN_NEW = REPO_ROOT / "formal" / "Problems" / "Engine" / "Excursions.lean"
FLOOR_PATH = ENVELOPE
RESIDUAL_PATH = RESIDUALS
DATA_DIR = REPO_ROOT / "data" / "research" / "juggler" / "excursions"

CLASS_ENVELOPE = "EXCURSION_ENVELOPE_GREEN"
CLASS_DEFECT = "FIRST_RETURN_DEFECT_GREEN"
CLASS_MCE = "MINIMAL_COUNTEREXAMPLE_ROUTE_GREEN"
CLASS_STRUCTURE = "EXCURSION_STRUCTURE_GREEN"
CLASS_COUNTER = "EXCURSION_COUNTEREXAMPLE"
CLASS_COMPLEX = "EXCURSION_INDUCTION_COMPLEX"
CLASS_INCOMPLETE = "EXCURSION_INCOMPLETE"

STATUS_RETURNED = "RETURNED"
STATUS_HORIZON = "HORIZON_EXCEEDED"
STATUS_BIT_CAP = "BIT_CAP"

CERT_EXPONENT = "EXPONENT"
CERT_FIRST_DEFECT = "FIRST_DEFECT"
CERT_PEAK_SUFFIX = "PEAK_SUFFIX"
CERT_COMPUTED = "COMPUTED_ONLY"

START_EVEN = "EVEN_AUTO"
START_OE = "OE_AUTO"
START_ODD_ODD = "ODD_ODD_START"
START_OTHER = "OTHER"

N_MIN = 2
N_MAX = 2000
HORIZON = 10_000
BIT_CAP = 4096
BIT_LIMIT = 80
CHUNK_SIZE = 200
HARD_STARTS = (9, 37, 49, 69, 77, 173)
ALGORITHM_VERSION = "excursion-v1"
SEARCH_PREFIX = "juggler-excursions-phase0"

FORBIDDEN_ENGINES = (
    "CycleEngine",
    "ResidualGraph",
    "RemainderDynamics",
    "PowerHeight",
    "ResidualStep",
    "CycleDiophantine",
)

FLOOR_LEMMAS = (
    "power_bound_word",
    "power_bound_contracts",
    "power_bound_eq_iff_extremal",
    "power_bound_compensated_contracts",
)


def search_id_for(n_start: int, n_end: int) -> str:
    return f"{SEARCH_PREFIX}-n{n_start}-{n_end}"


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


def first_return_below(
    n: int,
    horizon: int = HORIZON,
    *,
    bit_cap: int = BIT_CAP,
) -> dict[str, Any]:
    """First k with T^k(n) < n, or a safety stop. Never named first_return."""

    path, status, tau_lt, _tau_le = _walk_returns(n, horizon, bit_cap)
    return {"path": path, "status": status, "tau": tau_lt}


def first_return_at_or_below(
    n: int,
    horizon: int = HORIZON,
    *,
    bit_cap: int = BIT_CAP,
) -> dict[str, Any]:
    path, status, _tau_lt, tau_le = _walk_returns(n, horizon, bit_cap)
    le_status = status
    if tau_le is not None and status == STATUS_HORIZON:
        le_status = STATUS_RETURNED
    return {"path": path, "status": le_status, "tau": tau_le}


def peak_index(path: tuple[int, ...] | list[int]) -> int:
    """First index at which the path attains its maximum."""

    if not path:
        raise ValueError("peak_index requires a nonempty path")
    peak = path[0]
    index = 0
    for pos, value in enumerate(path):
        if value > peak:
            peak = value
            index = pos
    return index


def _walk_returns(
    n: int,
    horizon: int,
    bit_cap: int,
) -> tuple[tuple[int, ...], str, int | None, int | None]:
    if n < 1:
        raise ValueError("first-return walks require n >= 1")
    if horizon < 1:
        raise ValueError("horizon must be at least 1")
    if bit_cap < 1:
        raise ValueError("bit_cap must be at least 1")
    path = [n]
    current = n
    tau_lt: int | None = None
    tau_le: int | None = None
    status = STATUS_HORIZON
    for step in range(1, horizon + 1):
        current = floor_power(current)
        path.append(current)
        if current.bit_length() > bit_cap:
            status = STATUS_BIT_CAP
            break
        if tau_le is None and current <= n:
            tau_le = step
        if current < n:
            tau_lt = step
            status = STATUS_RETURNED
            break
    return tuple(path), status, tau_lt, tau_le


def peak_suffix_certifies(peak: int, n: int, s: int, q: int) -> bool | None:
    """Whether P^{3^q} < n^{2^s}. None if the comparison is unavailable."""

    if s <= 0 or peak < 1 or n < 1 or q < 0:
        return None
    if peak == 1:
        return n > 1
    odd_exp = 3**q
    even_exp = 1 << s
    pbits = peak.bit_length()
    nbits = n.bit_length()
    if pbits * odd_exp <= (nbits - 1) * even_exp:
        return True
    if (pbits - 1) * odd_exp >= nbits * even_exp:
        return False
    if pbits * odd_exp <= EXACT_POW_BITS and nbits * even_exp <= EXACT_POW_BITS:
        return cmp_pow(peak, odd_exp, n, even_exp) < 0
    return None


def prefix_envelope_holds(peak: int, n: int, r: int, o_u: int) -> bool | None:
    """Whether P^{2^r} <= n^{3^{o_u}}. None if the comparison is unavailable."""

    if r < 0 or o_u < 0 or peak < 1 or n < 1:
        return None
    if r == 0:
        return peak <= n
    odd_exp = 3**o_u
    even_exp = 1 << r
    pbits = peak.bit_length()
    nbits = n.bit_length()
    if (pbits - 1) * even_exp >= nbits * odd_exp:
        return False
    if pbits * even_exp <= (nbits - 1) * odd_exp:
        return True
    if pbits * even_exp <= EXACT_POW_BITS and nbits * odd_exp <= EXACT_POW_BITS:
        return cmp_pow(peak, even_exp, n, odd_exp) <= 0
    return None


def start_class(n: int, word: str) -> str:
    if n % 2 == 0 and word == "E":
        return START_EVEN
    if word == "OE":
        return START_OE
    if n % 2 == 1 and floor_power(n) % 2 == 1:
        return START_ODD_ODD
    return START_OTHER


def _certificates(
    gap: int,
    first_ok: bool | None,
    peak_ok: bool | None,
) -> list[str]:
    tags: list[str] = []
    if gap > 0:
        tags.append(CERT_EXPONENT)
    if first_ok is True:
        tags.append(CERT_FIRST_DEFECT)
    if peak_ok is True:
        tags.append(CERT_PEAK_SUFFIX)
    if not tags:
        tags.append(CERT_COMPUTED)
    return tags


def excursion_row(
    n: int,
    *,
    horizon: int = HORIZON,
    bit_cap: int = BIT_CAP,
    bit_limit: int = BIT_LIMIT,
) -> dict[str, Any]:
    if n < 1:
        raise ValueError("excursion_row requires n >= 1")
    path, status, tau_lt, tau_le = _walk_returns(n, horizon, bit_cap)
    word = word_of(path) if len(path) >= 2 else ""
    peak_pos = peak_index(path)
    peak = path[peak_pos]
    if status != STATUS_RETURNED or tau_lt is None:
        return {
            "n": n,
            "status": status,
            "tau_lt": tau_lt,
            "tau_le": tau_le,
            "word": word,
            "k": len(word),
            "odd_count": odd_count(word) if word else 0,
            "exponent_gap": None,
            "peak": peak,
            "peak_index": peak_pos,
            "return_value": None,
            "return_deficit": None,
            "peak_overshoot": peak - n,
            "r": peak_pos,
            "o_u": odd_count(word[:peak_pos]) if peak_pos else 0,
            "s": None,
            "q": None,
            "first_defect_index": first_nonexact_index(path),
            "first_defect": None,
            "first_defect_branch": None,
            "first_defect_state": None,
            "formal_gap": None,
            "global_delta": None,
            "full_delta_exceeds_gap": None,
            "first_defect_sufficient": None,
            "peak_suffix_certifies": None,
            "prefix_envelope_holds": None,
            "certificates": [],
            "start_class": start_class(n, word) if word else START_OTHER,
            "horizon": horizon,
            "bit_cap": bit_cap,
        }

    k = tau_lt
    word = word_of(path)
    odds = odd_count(word)
    gap = exponent_gap(k, odds)
    image = path[-1]
    r = peak_pos
    prefix = word[:r]
    suffix = word[r:]
    o_u = odd_count(prefix)
    s = len(suffix)
    q = odd_count(suffix)
    defect_index = first_nonexact_index(path)
    defect_value = None if defect_index is None else local_defect(path[defect_index])
    defect_branch = None if defect_index is None else word[defect_index]
    defect_state = None if defect_index is None else path[defect_index]
    formal = formal_gap(n, k, odds, bit_limit=bit_limit)
    deficit = tiny_deficit(n, image, k, odds, bit_limit=bit_limit)
    full_exceeds = None if formal is None or deficit is None else deficit > formal
    first_ok = first_defect_sufficient(n, word, bit_limit=bit_limit)
    peak_ok = peak_suffix_certifies(peak, n, s, q)
    prefix_ok = prefix_envelope_holds(peak, n, r, o_u)
    certs = _certificates(gap, first_ok, peak_ok)
    return {
        "n": n,
        "status": status,
        "tau_lt": tau_lt,
        "tau_le": tau_le,
        "word": word,
        "k": k,
        "odd_count": odds,
        "exponent_gap": gap,
        "peak": peak,
        "peak_index": peak_pos,
        "return_value": image,
        "return_deficit": n - image,
        "peak_overshoot": peak - n,
        "r": r,
        "o_u": o_u,
        "s": s,
        "q": q,
        "first_defect_index": defect_index,
        "first_defect": defect_value,
        "first_defect_branch": defect_branch,
        "first_defect_state": defect_state,
        "formal_gap": formal,
        "global_delta": deficit,
        "full_delta_exceeds_gap": full_exceeds,
        "first_defect_sufficient": first_ok,
        "peak_suffix_certifies": peak_ok,
        "prefix_envelope_holds": prefix_ok,
        "certificates": certs,
        "start_class": start_class(n, word),
        "horizon": horizon,
        "bit_cap": bit_cap,
    }


def _slim_row(row: dict[str, Any], *, word_cap: int = 80) -> dict[str, Any]:
    word = row.get("word") or ""
    preview = word if len(word) <= word_cap else word[:word_cap] + "…"
    return {
        "n": row["n"],
        "status": row["status"],
        "tau_lt": row["tau_lt"],
        "tau_le": row["tau_le"],
        "k": row["k"],
        "odd_count": row["odd_count"],
        "exponent_gap": row["exponent_gap"],
        "word_preview": preview,
        "itinerary_length": len(word),
        "peak": row["peak"],
        "peak_index": row["peak_index"],
        "return_value": row["return_value"],
        "return_deficit": row["return_deficit"],
        "peak_overshoot": row["peak_overshoot"],
        "r": row["r"],
        "o_u": row["o_u"],
        "s": row["s"],
        "q": row["q"],
        "first_defect_index": row["first_defect_index"],
        "first_defect": row["first_defect"],
        "certificates": list(row["certificates"]),
        "start_class": row["start_class"],
        "peak_suffix_certifies": row["peak_suffix_certifies"],
        "first_defect_sufficient": row["first_defect_sufficient"],
        "prefix_envelope_holds": row["prefix_envelope_holds"],
        "full_delta_exceeds_gap": row["full_delta_exceeds_gap"],
    }


def analyze_rows(rows: list[dict[str, Any]]) -> dict[str, Any]:
    returned = [row for row in rows if row["status"] == STATUS_RETURNED]
    unfinished = [row for row in rows if row["status"] != STATUS_RETURNED]
    odd_starts = [row for row in returned if row["n"] % 2 == 1]
    odd_long = [row for row in odd_starts if (row["k"] or 0) > 1]
    odd_odd = [row for row in returned if row["start_class"] == START_ODD_ODD]
    cert_counts: Counter[str] = Counter()
    combo_counts: Counter[str] = Counter()
    class_counts: Counter[str] = Counter()
    for row in returned:
        class_counts[row["start_class"]] += 1
        combo_counts["+".join(row["certificates"])] += 1
        for tag in row["certificates"]:
            cert_counts[tag] += 1

    computed_only = [
        row for row in returned if row["certificates"] == [CERT_COMPUTED]
    ]
    computed_odd_odd = [
        row for row in computed_only if row["start_class"] == START_ODD_ODD
    ]
    shapes = sorted(
        {
            (row["r"], row["o_u"], row["s"], row["q"], row["start_class"])
            for row in computed_odd_odd
        }
    )

    lemma_a_odd = all(not (row["word"] and set(row["word"]) == {"O"}) for row in odd_starts)
    lemma_a_universal = all(
        not is_monochrome(row["word"] or "") for row in returned if row["word"]
    )
    even_extremal = [
        row["n"] for row in returned if row["word"] == "E" and row["n"] % 2 == 0
    ]
    lemma_b = all(not (row["word"] and set(row["word"]) == {"O"}) for row in returned)
    exact_odd_returns = []
    for row in returned:
        word = row["word"] or ""
        if not word or set(word) != {"O"}:
            continue
        path = first_return_below(row["n"], horizon=row.get("horizon") or HORIZON)["path"]
        if all(local_tight(state) for state in path[:-1]):
            exact_odd_returns.append(row["n"])
    lemma_b_exact = not exact_odd_returns

    weak = [row for row in odd_long if CERT_COMPUTED in row["certificates"]]
    defect_vs_peak = [
        {
            "n": row["n"],
            "first_defect_index": row["first_defect_index"],
            "peak_index": row["peak_index"],
            "defect_before_peak": (
                row["first_defect_index"] is not None
                and row["first_defect_index"] < row["peak_index"]
            ),
            "certificates": list(row["certificates"]),
        }
        for row in weak
    ]
    no_first_defect = [
        row
        for row in odd_odd
        if row["first_defect_sufficient"] is not True
    ]
    no_first_shapes = sorted(
        {(row["r"], row["o_u"], row["s"], row["q"]) for row in no_first_defect}
    )

    def _deficit_key(row: dict[str, Any]) -> tuple[int, int]:
        return (row["return_deficit"] or 10**18, row["n"])

    def _peak_ratio_pair(left: dict[str, Any], right: dict[str, Any]) -> bool:
        return (left["peak"] or 0) * right["n"] > (right["peak"] or 0) * left["n"]

    grazers = sorted(odd_long, key=_deficit_key)[:20]
    tall = list(odd_long)
    for index in range(1, len(tall)):
        cursor = tall[index]
        pos = index
        while pos > 0 and _peak_ratio_pair(cursor, tall[pos - 1]):
            tall[pos] = tall[pos - 1]
            pos -= 1
        tall[pos] = cursor
    tallest = tall[:20]

    mce_candidates = [
        {
            "n": row["n"],
            "return_value": row["return_value"],
            "first_defect_state": row["first_defect_state"],
            "peak": row["peak"],
            "note": (
                "return_value < n by definition; first_defect_state and "
                "peak are flags only, not a measure M"
            ),
        }
        for row in computed_odd_odd[:12]
    ]

    certified = [row for row in returned if CERT_COMPUTED not in row["certificates"]]
    fraction = (len(certified) / len(returned)) if returned else None
    prefix_ok = sum(1 for row in returned if row["prefix_envelope_holds"] is True)
    prefix_fail = [
        row["n"] for row in returned if row["prefix_envelope_holds"] is False
    ]
    tautology_used = any(
        CERT_FIRST_DEFECT not in row["certificates"]
        and row["full_delta_exceeds_gap"] is True
        and CERT_COMPUTED not in row["certificates"]
        and CERT_EXPONENT not in row["certificates"]
        and CERT_PEAK_SUFFIX not in row["certificates"]
        for row in returned
    )

    return {
        "row_count": len(rows),
        "returned": len(returned),
        "unfinished": [_slim_row(row) for row in unfinished],
        "unfinished_count": len(unfinished),
        "start_class_counts": dict(class_counts),
        "certificate_counts": dict(cert_counts),
        "certificate_combo_counts": dict(combo_counts),
        "odd_odd_returned": len(odd_odd),
        "computed_only_count": len(computed_only),
        "computed_only_odd_odd_count": len(computed_odd_odd),
        "computed_only_shapes": [list(item) for item in shapes],
        "certified_count": len(certified),
        "certified_fraction": fraction,
        "lemma_a_odd_holds": lemma_a_odd,
        "lemma_a_universal_holds": lemma_a_universal,
        "lemma_a_universal_counterexample": even_extremal[:5],
        "lemma_b_holds": lemma_b,
        "lemma_b_exact_holds": lemma_b_exact,
        "lemma_b_exact_counterexamples": exact_odd_returns,
        "lemma_c_defect_vs_peak": defect_vs_peak[:20],
        "lemma_d_no_first_defect_count": len(no_first_defect),
        "lemma_d_shapes": [list(item) for item in no_first_shapes],
        "grazers": [_slim_row(row) for row in grazers],
        "tallest": [_slim_row(row) for row in tallest],
        "computed_only_sample": [_slim_row(row) for row in computed_odd_odd[:20]],
        "mce_candidate_flags": mce_candidates,
        "prefix_envelope_true": prefix_ok,
        "prefix_envelope_false": prefix_fail,
        "tautological_delta_used_as_certificate": tautology_used,
        "hard": [_slim_row(row) for row in returned if row["n"] in HARD_STARTS],
        "max_tau": max((row["tau_lt"] or 0) for row in returned) if returned else 0,
        "max_peak_bits": max((row["peak"] or 0).bit_length() for row in returned)
        if returned
        else 0,
    }


def classify(analysis: dict[str, Any], lean: dict[str, Any]) -> dict[str, Any]:
    if not lean.get("sorry_free") or lean.get("Excursions_present"):
        return {
            "classification": CLASS_INCOMPLETE,
            "reason": "Lean gate failed: new file present or sorry detected",
        }
    if analysis.get("tautological_delta_used_as_certificate"):
        return {
            "classification": CLASS_INCOMPLETE,
            "reason": "full-word Δ was treated as a certificate",
        }
    if analysis.get("unfinished_count"):
        return {
            "classification": CLASS_INCOMPLETE,
            "reason": (
                f"{analysis['unfinished_count']} starts missed the horizon "
                "or bit cap; that cutoff is not a bound L"
            ),
        }
    if analysis.get("prefix_envelope_false"):
        return {
            "classification": CLASS_COUNTER,
            "secondary": [],
            "reason": (
                "prefix envelope P^{2^r} <= n^{3^{o_u}} failed on "
                f"{analysis['prefix_envelope_false']}"
            ),
        }
    if not analysis.get("lemma_b_holds") or not analysis.get("lemma_b_exact_holds"):
        return {
            "classification": CLASS_COUNTER,
            "secondary": [],
            "reason": "an odd tower returned below the start",
        }
    leftover = analysis.get("computed_only_odd_odd_count") or 0
    shapes = analysis.get("computed_only_shapes") or []
    odd_odd = analysis.get("odd_odd_returned") or 0
    combos = analysis.get("certificate_combo_counts") or {}
    exponent_all = leftover == 0 and odd_odd > 0 and all(
        CERT_EXPONENT in name.split("+") for name in combos
    )
    defect_only = any(
        CERT_FIRST_DEFECT in name.split("+") and CERT_EXPONENT not in name.split("+")
        for name in combos
    )
    if leftover == 0 and odd_odd > 0 and exponent_all:
        return {
            "classification": CLASS_ENVELOPE,
            "secondary": [CLASS_DEFECT] if defect_only else [],
            "reason": (
                "every first-return-below word in the window is formally "
                "contracting (2^k > 3^o); first-defect and peak-suffix "
                "never certify a return that the exponent gap misses"
            ),
        }
    if leftover == 0 and odd_odd > 0 and defect_only:
        return {
            "classification": CLASS_DEFECT,
            "secondary": [],
            "reason": (
                "some first-return words have 2^k <= 3^o and are certified "
                "only by first-defect compensation"
            ),
        }
    if leftover > 0 and 1 <= len(shapes) <= 4:
        return {
            "classification": CLASS_STRUCTURE,
            "secondary": [CLASS_COMPLEX] if leftover > 20 else [],
            "reason": (
                f"{leftover} COMPUTED_ONLY odd-odd returns collapse to "
                f"{len(shapes)} split shapes"
            ),
        }
    return {
        "classification": CLASS_COMPLEX,
        "secondary": [CLASS_COUNTER] if not analysis.get("lemma_a_universal_holds") else [],
        "reason": (
            f"{leftover} COMPUTED_ONLY odd-odd first returns remain; "
            f"{len(shapes)} split shapes; return_value < n is not a new "
            "measure M; no well-founded excursion invariant emerged"
        ),
    }


def lean_api_present() -> dict[str, Any]:
    floor = juggler_text()
    residual = RESIDUAL_PATH.read_text(encoding="utf-8") if RESIDUAL_PATH.is_file() else ""
    new_text = LEAN_NEW.read_text(encoding="utf-8") if LEAN_NEW.is_file() else ""
    sorry_free = (
        "sorry" not in floor
        and "admit" not in floor
        and "sorry" not in residual
        and "admit" not in residual
        and "sorry" not in new_text
        and "admit" not in new_text
    )
    out: dict[str, Any] = {
        "sorry_free": sorry_free,
        "Excursions_absent": not LEAN_NEW.is_file(),
        "Excursions_present": LEAN_NEW.is_file(),
        "ResidualStep_not_extended": "def ResidualStep" in residual
        and "ExcursionReturn" not in residual
        and "first_return_below" not in residual,
        "no_global_termination_theorem": "theorem juggler_reaches_one" not in floor
        and "theorem first_return_contraction" not in floor
        and "theorem first_return_envelope" not in floor,
        "forbidden_engines": list(FORBIDDEN_ENGINES),
    }
    for name in FLOOR_LEMMAS:
        out[name] = name in floor
    return out


def scan_range(
    n_start: int,
    n_end: int,
    *,
    horizon: int = HORIZON,
    bit_cap: int = BIT_CAP,
    bit_limit: int = BIT_LIMIT,
) -> list[dict[str, Any]]:
    if n_start < 1 or n_end < n_start:
        raise ValueError("scan_range requires 1 <= n_start <= n_end")
    return [
        excursion_row(n, horizon=horizon, bit_cap=bit_cap, bit_limit=bit_limit)
        for n in range(n_start, n_end + 1)
    ]


def probe_payload(
    rows: list[dict[str, Any]],
    *,
    n_start: int,
    n_end: int,
    horizon: int = HORIZON,
    bit_cap: int = BIT_CAP,
) -> dict[str, Any]:
    analysis = analyze_rows(rows)
    lean = lean_api_present()
    decision = classify(analysis, lean)
    anti = dict(ANTI_OVERCLAIM)
    anti.update(
        {
            "search_horizon_is_L": False,
            "full_delta_is_certificate": False,
            "finite_progress_for_all": False,
            "minimal_nonterm_rebuilt": False,
            "first_return_means_orbit_period": False,
            "global_termination": False,
        }
    )
    return {
        "experiment": "juggler_excursions",
        "engine_control_layer_modified": False,
        "anti_overclaim": anti,
        "window": {
            "n_start": n_start,
            "n_end": n_end,
            "horizon": horizon,
            "bit_cap": bit_cap,
            "hard_starts": list(HARD_STARTS),
            "algorithm_version": ALGORITHM_VERSION,
            "search_id": search_id_for(n_start, n_end),
        },
        "scan": {
            "analysis": analysis,
            "residual_step_extended": False,
            "explicit_L": False,
            "adversarial_engine": False,
            "cycle_diophantine_reopened": False,
        },
        "lean": lean,
        "decision": decision,
        "search_method": (
            "first_return_below on each n; certificates are exponent gap, "
            "first_defect_sufficient, or peak_suffix_certifies via cmp_pow "
            f"sandwiches; HARD_STARTS {HARD_STARTS}; "
            f"window n={n_start}..{n_end}; horizon {horizon} is not L"
        ),
    }


def render_markdown(payload: dict[str, Any]) -> str:
    decision = payload["decision"]
    analysis = payload["scan"]["analysis"]
    lean = payload["lean"]
    window = payload["window"]
    lines = [
        "# Juggler first-return-below excursions",
        "",
        f"Status: **{decision['classification']}**",
        "",
        "Standalone application phase. Not a Research Engine experiment",
        "and not a termination theorem. The unit is a complete first",
        "return strictly below the starting value. Full-word Δ >",
        "formal_gap on a completed return is T<n rewritten.",
        "",
        "## Branch budget",
        "",
        "```text",
        "Mathematical target     Can first-return-below words be certified by envelope/defect?",
        "Novelty hypothesis      the complete excursion is the right FiniteProgress unit",
        "Falsifier               COMPUTED_ONLY grazers with no structure, or T<n rewritten",
        "Existing machinery      power_bound_*, first-defect, cmp_pow, FiniteProgress",
        "Maximum Phase-0 scope   n=2..2000 + HARD_STARTS; persist; classify; no Lean",
        "```",
        "",
        "## Metadata",
        "",
        f"- search_id: `{window['search_id']}`",
        f"- algorithm_version: `{window['algorithm_version']}`",
        f"- window: `n={window['n_start']}..{window['n_end']}`",
        f"- horizon: `{window['horizon']}` (not L)",
        f"- bit_cap: `{window['bit_cap']}`",
        f"- engine control layer modified: `{payload['engine_control_layer_modified']}`",
        f"- classification: **{decision['classification']}**",
        f"- secondary: `{decision.get('secondary')}`",
        f"- sorry-free: `{lean['sorry_free']}`",
        "",
        decision["reason"] + ".",
        "",
        "## Census",
        "",
        f"- rows: `{analysis['row_count']}`",
        f"- returned: `{analysis['returned']}`",
        f"- unfinished: `{analysis['unfinished_count']}`",
        f"- odd-odd returned: `{analysis['odd_odd_returned']}`",
        f"- start classes: `{analysis['start_class_counts']}`",
        f"- certificate tags: `{analysis['certificate_counts']}`",
        f"- certificate combos: `{analysis['certificate_combo_counts']}`",
        f"- certified fraction: `{analysis['certified_fraction']}`",
        f"- COMPUTED_ONLY: `{analysis['computed_only_count']}`",
        f"- COMPUTED_ONLY odd-odd: `{analysis['computed_only_odd_odd_count']}`",
        f"- COMPUTED_ONLY shapes: `{analysis['computed_only_shapes']}`",
        f"- max τ_<: `{analysis['max_tau']}`",
        f"- max peak bits: `{analysis['max_peak_bits']}`",
        "",
        "## Lemmas",
        "",
        f"- A odd starts not an odd tower: `{analysis['lemma_a_odd_holds']}`",
        f"- A universal (false if even E appears): `{analysis['lemma_a_universal_holds']}`",
        f"- A universal counterexample sample: `{analysis['lemma_a_universal_counterexample']}`",
        f"- B no all-odd return word: `{analysis['lemma_b_holds']}`",
        f"- B exact odd ascent does not return: `{analysis['lemma_b_exact_holds']}`",
        f"- D no-first-defect count: `{analysis['lemma_d_no_first_defect_count']}`",
        f"- D shapes: `{analysis['lemma_d_shapes']}`",
        f"- prefix envelope false: `{analysis['prefix_envelope_false']}`",
        f"- tautological Δ used as certificate: `{analysis['tautological_delta_used_as_certificate']}`",
        "",
        "## Hard starts",
        "",
    ]
    for row in analysis["hard"]:
        lines.append(
            f"- n=`{row['n']}` τ=`{row['tau_lt']}` class=`{row['start_class']}` "
            f"k=`{row['k']}` o=`{row['odd_count']}` G=`{row['exponent_gap']}` "
            f"peak=`{row['peak']}` return=`{row['return_value']}` "
            f"deficit=`{row['return_deficit']}` split=`({row['r']},{row['o_u']},{row['s']},{row['q']})` "
            f"certs=`{row['certificates']}` word=`{row['word_preview']}`"
        )
    lines.extend(
        [
            "",
            "## Grazers (smallest n − C(n) among odd k>1)",
            "",
        ]
    )
    for row in analysis["grazers"][:12]:
        lines.append(
            f"- n=`{row['n']}` deficit=`{row['return_deficit']}` return=`{row['return_value']}` "
            f"k=`{row['k']}` certs=`{row['certificates']}` word=`{row['word_preview']}`"
        )
    lines.extend(["", "## Tallest odd peaks", ""])
    for row in analysis["tallest"][:8]:
        lines.append(
            f"- n=`{row['n']}` peak=`{row['peak']}` overshoot=`{row['peak_overshoot']}` "
            f"k=`{row['k']}` certs=`{row['certificates']}`"
        )
    lines.extend(["", "## Lean", ""])
    for name in FLOOR_LEMMAS:
        lines.append(f"- `{name}`: `{lean.get(name)}`")
    lines.extend(
        [
            f"- new Excursions file absent: `{lean.get('Excursions_absent')}`",
            f"- ResidualStep not extended: `{lean.get('ResidualStep_not_extended')}`",
            f"- no global halt theorem: `{lean.get('no_global_termination_theorem')}`",
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
            "A search-horizon miss is not a bound L. Do not claim termination.",
            "",
        ]
    )
    return "\n".join(lines) + "\n"


def write_artifacts(payload: dict[str, Any]) -> dict[str, Any]:
    JSON_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")
    DOC_PATH.write_text(render_markdown(payload), encoding="utf-8")
    return payload


def search_config(
    n_start: int = N_MIN,
    n_end: int = N_MAX,
    *,
    horizon: int = HORIZON,
    bit_cap: int = BIT_CAP,
    chunk_size: int = CHUNK_SIZE,
) -> dict[str, Any]:
    return {
        "search_id": search_id_for(n_start, n_end),
        "algorithm_version": ALGORITHM_VERSION,
        "n_start": n_start,
        "n_end": n_end,
        "horizon": horizon,
        "bit_cap": bit_cap,
        "chunk_size": chunk_size,
        "hard_starts": list(HARD_STARTS),
        "arithmetic": "python-int",
    }


def _db_path(root: Path) -> Path:
    return root / "search.sqlite"


def _connect(root: Path) -> sqlite3.Connection:
    con = sqlite3.connect(_db_path(root))
    con.execute("PRAGMA journal_mode=WAL")
    return con


def _init_schema(con: sqlite3.Connection) -> None:
    con.executescript(
        """
        CREATE TABLE IF NOT EXISTS chunks (
            chunk_id INTEGER PRIMARY KEY,
            n_start INTEGER NOT NULL,
            n_end INTEGER NOT NULL,
            status TEXT NOT NULL,
            checksum TEXT
        );
        CREATE TABLE IF NOT EXISTS rows (
            n INTEGER PRIMARY KEY,
            status TEXT NOT NULL,
            tau_lt INTEGER,
            payload TEXT NOT NULL
        );
        CREATE TABLE IF NOT EXISTS meta (
            key TEXT PRIMARY KEY,
            value TEXT NOT NULL
        );
        """
    )


def _chunk_ranges(n_start: int, n_end: int, chunk_size: int) -> list[tuple[int, int]]:
    ranges: list[tuple[int, int]] = []
    cursor = n_start
    while cursor <= n_end:
        ranges.append((cursor, min(n_end, cursor + chunk_size - 1)))
        cursor += chunk_size
    return ranges


def init(
    data_dir: Path | None = None,
    *,
    n_start: int = N_MIN,
    n_end: int = N_MAX,
    horizon: int = HORIZON,
    bit_cap: int = BIT_CAP,
    chunk_size: int = CHUNK_SIZE,
) -> Path:
    root = DATA_DIR if data_dir is None else data_dir
    (root / "summaries").mkdir(parents=True, exist_ok=True)
    (root / "analysis").mkdir(parents=True, exist_ok=True)
    (root / "ranges").mkdir(parents=True, exist_ok=True)
    config = search_config(
        n_start, n_end, horizon=horizon, bit_cap=bit_cap, chunk_size=chunk_size
    )
    (root / "search_config.json").write_text(
        json.dumps(config, indent=2) + "\n", encoding="utf-8"
    )
    manifest_path = root / "manifest.json"
    if not manifest_path.is_file():
        manifest_path.write_text(
            json.dumps(
                {
                    "search_id": config["search_id"],
                    "algorithm_version": ALGORITHM_VERSION,
                    "n_range": [n_start, n_end],
                    "horizon": horizon,
                    "completion_status": "PENDING",
                    "git_commit": git_commit(),
                    "checksum": None,
                },
                indent=2,
            )
            + "\n",
            encoding="utf-8",
        )
    readme = root / "README.md"
    if not readme.is_file():
        readme.write_text(_readme_text(), encoding="utf-8")
    con = _connect(root)
    try:
        _init_schema(con)
        existing = con.execute("SELECT COUNT(*) FROM chunks").fetchone()[0]
        stored_id = con.execute(
            "SELECT value FROM meta WHERE key = 'search_id'"
        ).fetchone()
        if existing == 0 or (stored_id and stored_id[0] != config["search_id"]):
            con.execute("DELETE FROM chunks")
            con.execute("DELETE FROM rows")
            con.execute("DELETE FROM meta")
            for index, (lo, hi) in enumerate(_chunk_ranges(n_start, n_end, chunk_size)):
                con.execute(
                    "INSERT INTO chunks(chunk_id, n_start, n_end, status) VALUES (?,?,?,?)",
                    (index, lo, hi, "PENDING"),
                )
            for key, value in {
                "search_id": config["search_id"],
                "algorithm_version": ALGORITHM_VERSION,
                "n_start": str(n_start),
                "n_end": str(n_end),
                "horizon": str(horizon),
                "bit_cap": str(bit_cap),
            }.items():
                con.execute(
                    "INSERT OR REPLACE INTO meta(key, value) VALUES (?,?)",
                    (key, value),
                )
        con.commit()
    finally:
        con.close()
    return root


def _readme_text() -> str:
    return (
        "# Juggler first-return-below excursions\n\n"
        "Phase-0 structure census of first returns strictly below the "
        "starting value. SQLite `search.sqlite` is the row source of "
        "truth and is gitignored. `summaries/` and `analysis/` hold the "
        "classification. A search-horizon miss is not a bound L and not "
        "a termination theorem.\n\n"
        "```text\n"
        "README.md\n"
        "search_config.json\n"
        "manifest.json\n"
        "search.sqlite          # gitignored\n"
        "ranges/                # gitignored spill\n"
        "summaries/\n"
        "analysis/\n"
        "```\n\n"
        "Commands:\n\n"
        "```text\n"
        "python -m research.juggler_sequence.excursions init\n"
        "python -m research.juggler_sequence.excursions run\n"
        "python -m research.juggler_sequence.excursions resume\n"
        "python -m research.juggler_sequence.excursions status\n"
        "python -m research.juggler_sequence.excursions summarize\n"
        "```\n"
    )


def _load_config(root: Path) -> dict[str, Any]:
    path = root / "search_config.json"
    if path.is_file():
        return json.loads(path.read_text(encoding="utf-8"))
    return search_config()


def _run_chunk(
    lo: int,
    hi: int,
    *,
    horizon: int,
    bit_cap: int,
) -> list[dict[str, Any]]:
    return scan_range(lo, hi, horizon=horizon, bit_cap=bit_cap)


def _chunk_checksum(rows: list[dict[str, Any]]) -> str:
    digest = hashlib.sha256()
    for row in sorted(rows, key=lambda item: item["n"]):
        digest.update(
            f"{row['n']}|{row['status']}|{row['tau_lt']}|{row['certificates']}\n".encode()
        )
    return digest.hexdigest()


def _load_rows(con: sqlite3.Connection) -> list[dict[str, Any]]:
    out = []
    for (payload,) in con.execute("SELECT payload FROM rows ORDER BY n"):
        out.append(json.loads(payload))
    return out


def _write_data_tree(
    payload: dict[str, Any],
    root: Path,
    runtime_ms: int,
    *,
    checksum: str,
) -> None:
    analysis = payload["scan"]["analysis"]
    phase0 = {
        "search_id": payload["window"]["search_id"],
        "algorithm_version": ALGORITHM_VERSION,
        "git_commit": git_commit(),
        "window": payload["window"],
        "decision": payload["decision"],
        "analysis": analysis,
    }
    phase_text = json.dumps(phase0, indent=2) + "\n"
    (root / "summaries" / "phase0.json").write_text(phase_text, encoding="utf-8")
    (root / "summaries" / "summary.md").write_text(
        render_markdown(payload), encoding="utf-8"
    )
    (root / "analysis" / "census.json").write_text(
        json.dumps(
            {
                "start_class_counts": analysis["start_class_counts"],
                "certificate_counts": analysis["certificate_counts"],
                "certificate_combo_counts": analysis["certificate_combo_counts"],
                "computed_only_shapes": analysis["computed_only_shapes"],
                "lemma_d_shapes": analysis["lemma_d_shapes"],
            },
            indent=2,
        )
        + "\n",
        encoding="utf-8",
    )
    (root / "analysis" / "grazers.json").write_text(
        json.dumps(analysis["grazers"], indent=2) + "\n", encoding="utf-8"
    )
    (root / "analysis" / "hard.json").write_text(
        json.dumps(analysis["hard"], indent=2) + "\n", encoding="utf-8"
    )
    (root / "analysis" / "computed_only.json").write_text(
        json.dumps(analysis["computed_only_sample"], indent=2) + "\n", encoding="utf-8"
    )
    (root / "analysis" / "lemmas.json").write_text(
        json.dumps(
            {
                "lemma_a_odd_holds": analysis["lemma_a_odd_holds"],
                "lemma_a_universal_holds": analysis["lemma_a_universal_holds"],
                "lemma_a_universal_counterexample": analysis[
                    "lemma_a_universal_counterexample"
                ],
                "lemma_b_holds": analysis["lemma_b_holds"],
                "lemma_b_exact_holds": analysis["lemma_b_exact_holds"],
                "lemma_c_defect_vs_peak": analysis["lemma_c_defect_vs_peak"],
                "lemma_d_no_first_defect_count": analysis["lemma_d_no_first_defect_count"],
                "lemma_d_shapes": analysis["lemma_d_shapes"],
                "mce_candidate_flags": analysis["mce_candidate_flags"],
            },
            indent=2,
        )
        + "\n",
        encoding="utf-8"
    )
    (root / "manifest.json").write_text(
        json.dumps(
            {
                "search_id": payload["window"]["search_id"],
                "algorithm_version": ALGORITHM_VERSION,
                "git_commit": git_commit(),
                "n_range": [payload["window"]["n_start"], payload["window"]["n_end"]],
                "horizon": payload["window"]["horizon"],
                "completion_status": "COMPLETE",
                "checksum": checksum,
                "checksum_sha256_phase0": hashlib.sha256(
                    phase_text.encode("utf-8")
                ).hexdigest(),
                "runtime_ms": runtime_ms,
                "classification": payload["decision"]["classification"],
            },
            indent=2,
        )
        + "\n",
        encoding="utf-8",
    )


def run(
    data_dir: Path | None = None,
    *,
    n_start: int | None = None,
    n_end: int | None = None,
    horizon: int | None = None,
    bit_cap: int | None = None,
) -> dict[str, Any]:
    if n_start is None or n_end is None:
        root_guess = DATA_DIR if data_dir is None else data_dir
        cfg = _load_config(root_guess) if (root_guess / "search_config.json").is_file() else {}
        n_start = n_start if n_start is not None else int(cfg.get("n_start", N_MIN))
        n_end = n_end if n_end is not None else int(cfg.get("n_end", N_MAX))
        horizon = horizon if horizon is not None else int(cfg.get("horizon", HORIZON))
        bit_cap = bit_cap if bit_cap is not None else int(cfg.get("bit_cap", BIT_CAP))
    assert n_start is not None and n_end is not None
    horizon = HORIZON if horizon is None else horizon
    bit_cap = BIT_CAP if bit_cap is None else bit_cap
    root = init(
        data_dir,
        n_start=n_start,
        n_end=n_end,
        horizon=horizon,
        bit_cap=bit_cap,
    )
    started = time.perf_counter()
    con = _connect(root)
    try:
        pending = list(
            con.execute(
                "SELECT chunk_id, n_start, n_end FROM chunks WHERE status != 'COMPLETE' ORDER BY chunk_id"
            )
        )
        for chunk_id, lo, hi in pending:
            rows = _run_chunk(lo, hi, horizon=horizon, bit_cap=bit_cap)
            checksum = _chunk_checksum(rows)
            for row in rows:
                con.execute(
                    "INSERT OR REPLACE INTO rows(n, status, tau_lt, payload) VALUES (?,?,?,?)",
                    (row["n"], row["status"], row["tau_lt"], json.dumps(row)),
                )
            con.execute(
                "UPDATE chunks SET status = 'COMPLETE', checksum = ? WHERE chunk_id = ?",
                (checksum, chunk_id),
            )
            con.commit()
        all_rows = _load_rows(con)
        table_checksum = _chunk_checksum(all_rows)
        con.execute(
            "INSERT OR REPLACE INTO meta(key, value) VALUES ('checksum', ?)",
            (table_checksum,),
        )
        con.commit()
    finally:
        con.close()
    payload = probe_payload(
        all_rows, n_start=n_start, n_end=n_end, horizon=horizon, bit_cap=bit_cap
    )
    runtime_ms = int((time.perf_counter() - started) * 1000)
    _write_data_tree(payload, root, runtime_ms, checksum=table_checksum)
    if root.resolve() == DATA_DIR.resolve():
        write_artifacts(payload)
    return payload


def load_manifest(data_dir: Path | None = None) -> dict[str, Any] | None:
    path = (DATA_DIR if data_dir is None else data_dir) / "manifest.json"
    if not path.is_file():
        return None
    return json.loads(path.read_text(encoding="utf-8"))


def resume(data_dir: Path | None = None) -> dict[str, Any] | None:
    root = DATA_DIR if data_dir is None else data_dir
    manifest = load_manifest(root)
    phase = root / "summaries" / "phase0.json"
    if manifest and manifest.get("completion_status") == "COMPLETE" and phase.is_file():
        return None
    return run(root)


def status(data_dir: Path | None = None) -> dict[str, Any]:
    root = DATA_DIR if data_dir is None else data_dir
    manifest = load_manifest(root)
    if manifest is None:
        return {"completed": False, "reason": "no manifest"}
    info = dict(manifest)
    db = _db_path(root)
    if db.is_file():
        con = _connect(root)
        try:
            counts = dict(
                con.execute(
                    "SELECT status, COUNT(*) FROM chunks GROUP BY status"
                ).fetchall()
            )
            info["chunk_status_counts"] = counts
            info["row_count"] = con.execute("SELECT COUNT(*) FROM rows").fetchone()[0]
        finally:
            con.close()
    return info


def summarize(data_dir: Path | None = None) -> dict[str, Any]:
    root = DATA_DIR if data_dir is None else data_dir
    phase = root / "summaries" / "phase0.json"
    if not phase.is_file():
        payload = run(root)
        return payload["decision"]
    stored = json.loads(phase.read_text(encoding="utf-8"))
    lean = lean_api_present()
    payload = {
        "experiment": "juggler_excursions",
        "engine_control_layer_modified": False,
        "anti_overclaim": {
            **dict(ANTI_OVERCLAIM),
            "search_horizon_is_L": False,
            "full_delta_is_certificate": False,
            "finite_progress_for_all": False,
            "minimal_nonterm_rebuilt": False,
            "first_return_means_orbit_period": False,
            "global_termination": False,
        },
        "window": stored["window"],
        "scan": {
            "analysis": stored["analysis"],
            "residual_step_extended": False,
            "explicit_L": False,
            "adversarial_engine": False,
            "cycle_diophantine_reopened": False,
        },
        "lean": lean,
        "decision": stored["decision"],
        "search_method": "summarize from summaries/phase0.json",
    }
    if root.resolve() == DATA_DIR.resolve():
        write_artifacts(payload)
    (root / "summaries" / "summary.md").write_text(
        render_markdown(payload), encoding="utf-8"
    )
    return payload["decision"]


def main() -> None:
    parser = argparse.ArgumentParser(description="Juggler first-return-below excursions")
    parser.add_argument(
        "command",
        nargs="?",
        default="run",
        choices=("init", "run", "resume", "status", "summarize"),
    )
    parser.add_argument("--data-dir", type=Path, default=None)
    parser.add_argument("--n-start", type=int, default=None)
    parser.add_argument("--n-end", type=int, default=None)
    parser.add_argument("--horizon", type=int, default=None)
    args = parser.parse_args()
    if args.command == "init":
        path = init(
            args.data_dir,
            n_start=args.n_start or N_MIN,
            n_end=args.n_end or N_MAX,
            horizon=args.horizon or HORIZON,
        )
        print(path)
        return
    if args.command == "run":
        payload = run(
            args.data_dir,
            n_start=args.n_start,
            n_end=args.n_end,
            horizon=args.horizon,
        )
        print(payload["decision"]["classification"])
        print(payload["decision"]["reason"])
        return
    if args.command == "resume":
        payload = resume(args.data_dir)
        if payload is None:
            print("already complete")
            return
        print(payload["decision"]["classification"])
        return
    if args.command == "status":
        print(json.dumps(status(args.data_dir), indent=2))
        return
    decision = summarize(args.data_dir)
    print(decision["classification"])


if __name__ == "__main__":
    main()
