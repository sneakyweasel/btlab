"""Two-sided minimal-counterexample corridor for the Juggler map.

Not a Research Engine control-layer experiment. Not a halt theorem.
Not the REFUTED two-sided exponent-only law from power_itineraries. For a
pivot x = T^j(n) and a realized suffix of length s, compare the exact
forward envelope x^{2^r} <= n^{3^o} with the reverse constraint
n^{2^s} <= x^{3^q} forced by T^s(x) >= n plus the suffix envelope.
ResidualStep is not extended. CycleDiophantine is not reopened.
"""

from __future__ import annotations

import hashlib
import json
import subprocess
from pathlib import Path
from typing import Any

from research.juggler_sequence.compensated_contraction import formal_gap
from research.juggler_sequence.envelope_defect import (
    first_nonexact_index,
    local_defect,
)
from research.juggler_sequence.equality_language import is_monochrome
from research.juggler_sequence.excursions import first_return_below
from research.juggler_sequence.near_extremal_prefixes import exponent_gap
from research.juggler_sequence.lean_paths import (
    CYCLE_DIOPHANTINE,
    ENVELOPE,
    MINIMAL,
    RESIDUALS,
    juggler_text,
)
from research.juggler_sequence.power_itineraries import (
    ANTI_OVERCLAIM,
    EXACT_POW_BITS,
    cmp_pow,
    odd_count,
    word_of,
)

REPO_ROOT = Path(__file__).resolve().parents[3]
JSON_PATH = REPO_ROOT / "docs" / "research" / "juggler_corridor.json"
DOC_PATH = REPO_ROOT / "docs" / "research" / "juggler_corridor.md"
LEAN_NEW = REPO_ROOT / "formal" / "Problems" / "Engine" / "Corridor.lean"
FLOOR_PATH = ENVELOPE
RESIDUAL_PATH = RESIDUALS
MIN_PATH = MINIMAL
CYCLE_PATH = CYCLE_DIOPHANTINE
DATA_DIR = REPO_ROOT / "data" / "research" / "juggler" / "corridor"

CLASS_PACK = "CORRIDOR_REPACKAGING"
CLASS_RIGID = "CORRIDOR_RIGIDITY_GREEN"
CLASS_DEFECT = "CORRIDOR_DEFECT_GREEN"
CLASS_COUNTER = "CORRIDOR_COUNTEREXAMPLE"
CLASS_INCOMPLETE = "CORRIDOR_INCOMPLETE"

N_MIN = 2
N_MAX = 2000
HORIZON = 10_000
BIT_CAP = 4096
BIT_LIMIT = 80
X_BITS_KEEP = 128
SAMPLE_CAP = 20
HARD_STARTS = (9, 37, 49, 69, 77, 173)
TALL_STARTS = (193, 557, 761)
ALGORITHM_VERSION = "corridor-v1"
SEARCH_PREFIX = "juggler-corridor-phase0"
PIVOT_POLICY = "every j in 0..tau-1"
SUFFIX_POLICY = "every s>=1 with j+s<=tau; stay-above iff j+s<tau"

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


def cmp_pow_safe(left: int, left_exp: int, right: int, right_exp: int) -> int | None:
    """Compare left**left_exp versus right**right_exp. None if unavailable.

    Bit-length sandwiches and cmp_pow inside EXACT_POW_BITS decide.
    A float logarithm is never the recorded verdict.
    """

    if left_exp < 0 or right_exp < 0:
        raise ValueError("exponents must be nonnegative")
    if left < 0 or right < 0:
        raise ValueError("bases must be nonnegative")
    if left_exp == 1 and right_exp == 1:
        return (left > right) - (left < right)
    if left_exp == 0 and right_exp == 0:
        return 0
    if left <= 1 or right <= 1:
        return cmp_pow(left, left_exp, right, right_exp)
    lm = left.bit_length()
    ln = right.bit_length()
    if (lm - 1) * left_exp >= ln * right_exp:
        return 1
    if lm * left_exp <= (ln - 1) * right_exp:
        return -1
    if lm * left_exp <= EXACT_POW_BITS and ln * right_exp <= EXACT_POW_BITS:
        return cmp_pow(left, left_exp, right, right_exp)
    return None


def _prefix_odds(word: str) -> list[int]:
    odds = [0]
    count = 0
    for letter in word:
        if letter == "O":
            count += 1
        elif letter != "E":
            raise ValueError(f"invalid word letter {letter!r}")
        odds.append(count)
    return odds


def _keep_x(x: int) -> int | None:
    return x if x.bit_length() <= X_BITS_KEEP else None


def corridor_row(
    n: int,
    j: int,
    s: int,
    *,
    path: tuple[int, ...] | list[int] | None = None,
    tau: int | None = None,
    word: str | None = None,
    prefix_odds: list[int] | None = None,
    first_defect_index: int | None = None,
    first_defect_value: int | None = None,
    bit_limit: int = BIT_LIMIT,
) -> dict[str, Any]:
    """Exact C_{j,s} on a realized first-return path of n."""

    if n < 1 or j < 0 or s < 1:
        raise ValueError("corridor_row requires n>=1, j>=0, s>=1")
    if path is None:
        walked = first_return_below(n, horizon=HORIZON, bit_cap=BIT_CAP)
        path = walked["path"]
        tau = walked["tau"]
    if tau is None:
        raise ValueError("corridor_row requires a finite tau_<")
    if j + s > tau:
        raise ValueError("corridor_row requires j+s <= tau_<")
    if word is None:
        word = word_of(tuple(path))
    if prefix_odds is None:
        prefix_odds = _prefix_odds(word)
    x = path[j]
    r = j
    o = prefix_odds[j]
    q = prefix_odds[j + s] - prefix_odds[j]
    prefix = word[:r]
    suffix = word[j : j + s]
    image = path[j + s]
    stay_above = j + s < tau
    combined_k = r + s
    combined_o = o + q
    gap = exponent_gap(combined_k, combined_o)
    forward_cmp = cmp_pow_safe(x, 1 << r, n, 3**o)
    reverse_cmp = cmp_pow_safe(n, 1 << s, x, 3**q)
    forward_ok = None if forward_cmp is None else forward_cmp <= 0
    reverse_ok = None if reverse_cmp is None else reverse_cmp <= 0
    reverse_fires = reverse_cmp is not None and reverse_cmp > 0
    compat = gap <= 0
    fullword_contracts = gap > 0
    prefix_eq = forward_cmp == 0
    reverse_eq = reverse_cmp == 0
    prefix_mixed_eq = prefix_eq and r >= 1 and not is_monochrome(prefix)
    suffix_mixed_eq = reverse_eq and s >= 1 and not is_monochrome(suffix)
    prefix_extremal_eq = prefix_eq and r >= 1 and is_monochrome(prefix) and bool(prefix)
    suffix_extremal_eq = reverse_eq and s >= 1 and is_monochrome(suffix) and bool(suffix)
    defect_index = first_defect_index
    defect_value = first_defect_value
    if defect_index is not None and defect_index >= r + s:
        defect_index = None
        defect_value = None
    combined_formal = formal_gap(n, combined_k, combined_o, bit_limit=bit_limit)
    defect_over_gap = (
        stay_above
        and compat
        and defect_value is not None
        and combined_formal is not None
        and defect_value > combined_formal
    )
    novel_reverse = reverse_fires and not fullword_contracts
    return {
        "n": n,
        "j": j,
        "x": _keep_x(x),
        "x_bits": x.bit_length(),
        "r": r,
        "o": o,
        "s": s,
        "q": q,
        "word_prefix": prefix,
        "word_suffix": suffix,
        "image": _keep_x(image),
        "image_ge_n": image >= n,
        "stay_above": stay_above,
        "is_return_suffix": j + s == tau,
        "forward_cmp": forward_cmp,
        "reverse_cmp": reverse_cmp,
        "forward_ok": forward_ok,
        "reverse_ok": reverse_ok,
        "reverse_fires": reverse_fires,
        "compat": compat,
        "fullword_contracts": fullword_contracts,
        "exponent_gap": gap,
        "slack": (3**combined_o) - (1 << combined_k),
        "prefix_eq": prefix_eq,
        "reverse_eq": reverse_eq,
        "prefix_mixed_eq": prefix_mixed_eq,
        "suffix_mixed_eq": suffix_mixed_eq,
        "prefix_extremal_eq": prefix_extremal_eq,
        "suffix_extremal_eq": suffix_extremal_eq,
        "first_defect_index": defect_index,
        "first_defect": defect_value,
        "combined_formal_gap": combined_formal,
        "defect_over_gap": defect_over_gap,
        "novel_reverse": novel_reverse,
        "tau": tau,
    }


def corridors_of(
    n: int,
    *,
    horizon: int = HORIZON,
    bit_cap: int = BIT_CAP,
    bit_limit: int = BIT_LIMIT,
) -> dict[str, Any]:
    walked = first_return_below(n, horizon=horizon, bit_cap=bit_cap)
    path = walked["path"]
    tau = walked["tau"]
    status = walked["status"]
    if tau is None:
        return {
            "n": n,
            "status": status,
            "tau": None,
            "word": word_of(tuple(path)) if len(path) >= 2 else "",
            "rows": [],
        }
    word = word_of(tuple(path))
    odds = _prefix_odds(word)
    defect_index = first_nonexact_index(tuple(path))
    defect_value = None if defect_index is None else local_defect(path[defect_index])
    rows = [
        corridor_row(
            n,
            j,
            s,
            path=path,
            tau=tau,
            word=word,
            prefix_odds=odds,
            first_defect_index=defect_index,
            first_defect_value=defect_value,
            bit_limit=bit_limit,
        )
        for j in range(tau)
        for s in range(1, tau - j + 1)
    ]
    return {
        "n": n,
        "status": status,
        "tau": tau,
        "word": word,
        "peak_bits": max(path).bit_length(),
        "rows": rows,
    }


def _slim(row: dict[str, Any]) -> dict[str, Any]:
    return {
        "n": row["n"],
        "j": row["j"],
        "s": row["s"],
        "r": row["r"],
        "o": row["o"],
        "q": row["q"],
        "x_bits": row["x_bits"],
        "x": row["x"],
        "word_prefix": row["word_prefix"],
        "word_suffix": row["word_suffix"],
        "stay_above": row["stay_above"],
        "is_return_suffix": row["is_return_suffix"],
        "forward_cmp": row["forward_cmp"],
        "reverse_cmp": row["reverse_cmp"],
        "compat": row["compat"],
        "exponent_gap": row["exponent_gap"],
        "slack": row["slack"],
        "prefix_eq": row["prefix_eq"],
        "reverse_eq": row["reverse_eq"],
        "prefix_mixed_eq": row["prefix_mixed_eq"],
        "suffix_mixed_eq": row["suffix_mixed_eq"],
        "prefix_extremal_eq": row["prefix_extremal_eq"],
        "novel_reverse": row["novel_reverse"],
        "defect_over_gap": row["defect_over_gap"],
    }


def _identity_failure(row: dict[str, Any]) -> dict[str, Any] | None:
    if not row["stay_above"]:
        return None
    if row["forward_cmp"] is not None and not row["forward_ok"]:
        return {"kind": "forward", **_slim(row)}
    if row["reverse_cmp"] is not None and not row["reverse_ok"]:
        return {"kind": "reverse", **_slim(row)}
    if not row["compat"]:
        return {"kind": "compat", **_slim(row)}
    return None


def analyze_starts(
    n_start: int,
    n_end: int,
    *,
    extra: tuple[int, ...] = (),
    horizon: int = HORIZON,
    bit_cap: int = BIT_CAP,
    bit_limit: int = BIT_LIMIT,
) -> dict[str, Any]:
    starts = list(range(n_start, n_end + 1))
    for value in extra:
        if value not in starts:
            starts.append(value)
    stay_above_count = 0
    return_count = 0
    returned = 0
    unfinished: list[int] = []
    even_stay = 0
    identity_failures: list[dict[str, Any]] = []
    mixed_eq: list[dict[str, Any]] = []
    extremal_eq_count = 0
    both_eq: list[dict[str, Any]] = []
    novel_stay: list[dict[str, Any]] = []
    novel_return: list[dict[str, Any]] = []
    defect_novel: list[dict[str, Any]] = []
    forward_unavailable = 0
    reverse_unavailable = 0
    closest: list[dict[str, Any]] = []
    hard: list[dict[str, Any]] = []
    tall: list[dict[str, Any]] = []
    max_tau = 0
    max_peak_bits = 0
    corridor_count = 0

    for n in starts:
        bundle = corridors_of(n, horizon=horizon, bit_cap=bit_cap, bit_limit=bit_limit)
        if bundle["tau"] is None:
            unfinished.append(n)
            continue
        returned += 1
        max_tau = max(max_tau, bundle["tau"])
        max_peak_bits = max(max_peak_bits, bundle["peak_bits"])
        stay_n = 0
        return_n = 0
        ident_n = 0
        extremal_n = 0
        min_slack = None
        for row in bundle["rows"]:
            corridor_count += 1
            if row["stay_above"]:
                stay_above_count += 1
                stay_n += 1
                if n % 2 == 0:
                    even_stay += 1
                fail = _identity_failure(row)
                if fail is not None:
                    ident_n += 1
                    if len(identity_failures) < SAMPLE_CAP:
                        identity_failures.append(fail)
                if row["forward_cmp"] is None:
                    forward_unavailable += 1
                if row["reverse_cmp"] is None:
                    reverse_unavailable += 1
                if row["novel_reverse"]:
                    if len(novel_stay) < SAMPLE_CAP:
                        novel_stay.append(_slim(row))
                if row["defect_over_gap"]:
                    if len(defect_novel) < SAMPLE_CAP:
                        defect_novel.append(_slim(row))
                if row["compat"] and (min_slack is None or row["slack"] < min_slack):
                    min_slack = row["slack"]
                if row["compat"]:
                    closest.append(row)
                    closest.sort(key=lambda item: (item["slack"], item["n"], item["j"], item["s"]))
                    if len(closest) > SAMPLE_CAP:
                        closest.pop()
            else:
                return_count += 1
                return_n += 1
                if row["novel_reverse"] and len(novel_return) < SAMPLE_CAP:
                    novel_return.append(_slim(row))
            if row["prefix_mixed_eq"] or row["suffix_mixed_eq"]:
                if len(mixed_eq) < SAMPLE_CAP:
                    mixed_eq.append(_slim(row))
            if row["prefix_extremal_eq"] or row["suffix_extremal_eq"]:
                extremal_eq_count += 1
                extremal_n += 1
            if row["prefix_eq"] and row["reverse_eq"] and row["r"] >= 1 and row["s"] >= 1:
                if len(both_eq) < SAMPLE_CAP:
                    both_eq.append(_slim(row))
        summary = {
            "n": n,
            "tau": bundle["tau"],
            "word": bundle["word"],
            "peak_bits": bundle["peak_bits"],
            "stay_above": stay_n,
            "return_suffixes": return_n,
            "identity_failures": ident_n,
            "extremal_eq": extremal_n,
            "min_slack": min_slack,
        }
        if n in HARD_STARTS:
            hard.append(summary)
        if n in TALL_STARTS:
            tall.append(summary)

    return {
        "n_start": n_start,
        "n_end": n_end,
        "extra": list(extra),
        "returned": returned,
        "unfinished": unfinished,
        "unfinished_count": len(unfinished),
        "corridor_count": corridor_count,
        "stay_above_count": stay_above_count,
        "return_count": return_count,
        "even_stay_above_count": even_stay,
        "identity_failures": identity_failures,
        "identity_failure_count": len(identity_failures),
        "forward_unavailable": forward_unavailable,
        "reverse_unavailable": reverse_unavailable,
        "mixed_eq": mixed_eq,
        "extremal_eq_count": extremal_eq_count,
        "both_eq": both_eq,
        "novel_stay": novel_stay,
        "novel_return": novel_return,
        "defect_novel": defect_novel,
        "closest_slack": [_slim(row) for row in closest],
        "hard": hard,
        "tall": tall,
        "max_tau": max_tau,
        "max_peak_bits": max_peak_bits,
        "search_horizon_is_not_L": True,
    }


def lean_api_present() -> dict[str, Any]:
    floor = juggler_text()
    residual = RESIDUAL_PATH.read_text(encoding="utf-8") if RESIDUAL_PATH.is_file() else ""
    minimum = MIN_PATH.read_text(encoding="utf-8") if MIN_PATH.is_file() else ""
    cycle = CYCLE_PATH.read_text(encoding="utf-8") if CYCLE_PATH.is_file() else ""
    new_text = LEAN_NEW.read_text(encoding="utf-8") if LEAN_NEW.is_file() else ""
    combined = floor + residual + minimum + cycle + new_text
    out: dict[str, Any] = {
        "sorry_free": "sorry" not in combined and "admit" not in combined,
        "Corridor_absent": not LEAN_NEW.is_file(),
        "Corridor_present": LEAN_NEW.is_file(),
        "minimal_nonterm_image_ge": "theorem minimal_nonterm_image_ge" in minimum,
        "ResidualStep_not_extended": "def ResidualStep" in residual
        and "CorridorPivot" not in residual
        and "two_sided_corridor" not in residual,
        "CycleDiophantine_not_rewritten": "corridor" not in cycle.lower(),
        "no_global_termination_theorem": "theorem juggler_reaches_one" not in combined
        and "theorem corridor_induction" not in combined
        and "theorem two_sided_envelope" not in floor,
        "no_forbidden_engine": all(name not in residual for name in FORBIDDEN_ENGINES[0:4])
        and "PowerHeight" not in floor,
        "forbidden_engines": list(FORBIDDEN_ENGINES),
    }
    for name in FLOOR_LEMMAS:
        out[name] = f"theorem {name}" in floor or f"def {name}" in floor
    return out


def classify(analysis: dict[str, Any], lean: dict[str, Any]) -> dict[str, Any]:
    lean_ok = (
        lean.get("sorry_free")
        and lean.get("Corridor_absent")
        and lean.get("power_bound_word")
        and lean.get("power_bound_contracts")
        and lean.get("power_bound_eq_iff_extremal")
        and lean.get("minimal_nonterm_image_ge")
        and lean.get("ResidualStep_not_extended")
        and lean.get("no_global_termination_theorem")
    )
    if not lean_ok:
        return {
            "classification": CLASS_INCOMPLETE,
            "reason": "Lean gate failed: new file, missing lemma, or sorry",
        }
    if analysis.get("unfinished_count"):
        return {
            "classification": CLASS_INCOMPLETE,
            "reason": (
                f"{analysis['unfinished_count']} starts missed the horizon "
                "or bit cap; that cutoff is not a bound L"
            ),
        }
    if analysis.get("identity_failures") or analysis.get("novel_stay"):
        return {
            "classification": CLASS_COUNTER,
            "secondary": [],
            "reason": (
                "a stay-above corridor violated forward, reverse, or "
                "compat, or reverse fired while 3^{o+q} >= 2^{r+s}"
            ),
        }
    if analysis.get("mixed_eq"):
        return {
            "classification": CLASS_COUNTER,
            "secondary": [CLASS_RIGID],
            "reason": (
                "a non-monochrome prefix or suffix saturated an envelope; "
                "that contradicts power_bound_eq_iff_extremal"
            ),
        }
    if analysis.get("defect_novel"):
        return {
            "classification": CLASS_COUNTER,
            "secondary": [CLASS_DEFECT],
            "reason": (
                "first defect exceeded the concatenated formal gap on a "
                "stay-above corridor with G<=0"
            ),
        }
    if analysis.get("novel_return"):
        return {
            "classification": CLASS_DEFECT,
            "secondary": [],
            "reason": (
                "a first-return suffix has n^{2^s} > x^{3^q} while "
                "3^{o+q} >= 2^{r+s}; the reverse bound is not the "
                "concatenated exponent test"
            ),
        }
    if analysis.get("both_eq"):
        return {
            "classification": CLASS_RIGID,
            "secondary": [],
            "reason": (
                "both corridor sides saturated simultaneously on a "
                "nonempty prefix and suffix"
            ),
        }
    even_ok = analysis.get("even_stay_above_count") == 0
    if not even_ok:
        return {
            "classification": CLASS_COUNTER,
            "reason": "an even start produced a stay-above corridor of length >= 1",
        }
    return {
        "classification": CLASS_PACK,
        "secondary": [],
        "reason": (
            "on stay-above segments, forward, reverse, and compat are "
            "the concatenated envelope plus image>=n; reverse never "
            "fires unless the concatenated word is formally contracting; "
            "equality hits are only known extremal towers"
        ),
    }


def extra_starts() -> tuple[int, ...]:
    return tuple(n for n in HARD_STARTS + TALL_STARTS if n > N_MAX)


def scan_window(
    *,
    n_start: int = N_MIN,
    n_end: int = N_MAX,
    extra: tuple[int, ...] | None = None,
) -> dict[str, Any]:
    return analyze_starts(
        n_start,
        n_end,
        extra=extra if extra is not None else extra_starts(),
    )


def run_probe(
    *,
    n_start: int = N_MIN,
    n_end: int = N_MAX,
) -> dict[str, Any]:
    window = scan_window(n_start=n_start, n_end=n_end)
    return {
        "window": window,
        "residual_step_extended": False,
        "explicit_L": False,
        "adversarial_engine": False,
        "cycle_diophantine_reopened": False,
        "two_sided_exponent_law_reopened": False,
    }


def probe_payload(
    *,
    n_start: int = N_MIN,
    n_end: int = N_MAX,
) -> dict[str, Any]:
    scan = run_probe(n_start=n_start, n_end=n_end)
    lean = lean_api_present()
    decision = classify(scan["window"], lean)
    anti = dict(ANTI_OVERCLAIM)
    anti.update(
        {
            "search_horizon_is_L": False,
            "finite_progress_for_all": False,
            "minimal_nonterm_rebuilt": False,
            "global_termination": False,
            "two_sided_exponent_law": False,
            "corridor_is_new_progress": False,
            "floating_point_verdict": False,
        }
    )
    return {
        "experiment": "juggler_corridor",
        "engine_control_layer_modified": False,
        "anti_overclaim": anti,
        "window": {
            "n_start": n_start,
            "n_end": n_end,
            "horizon": HORIZON,
            "bit_cap": BIT_CAP,
            "hard_starts": list(HARD_STARTS),
            "tall_starts": list(TALL_STARTS),
            "algorithm_version": ALGORITHM_VERSION,
            "search_id": search_id_for(n_start, n_end),
            "pivot_policy": PIVOT_POLICY,
            "suffix_policy": SUFFIX_POLICY,
        },
        "scan": scan,
        "lean": lean,
        "decision": decision,
        "search_method": (
            "first_return_below then every C_j,s with j+s<=tau; "
            "forward/reverse via cmp_pow sandwiches; compat is "
            "2^{r+s} vs 3^{o+q}; HARD_STARTS "
            f"{HARD_STARTS}; TALL_STARTS {TALL_STARTS}; "
            f"window n={n_start}..{n_end}; horizon {HORIZON} is not L"
        ),
    }


def render_markdown(payload: dict[str, Any]) -> str:
    decision = payload["decision"]
    analysis = payload["scan"]["window"]
    lean = payload["lean"]
    window = payload["window"]
    lines = [
        "# Juggler two-sided minimal-counterexample corridor",
        "",
        f"Status: **{decision['classification']}**",
        "",
        "Standalone application phase. Not a Research Engine experiment",
        "and not a termination theorem. Not the REFUTED two-sided",
        "exponent-only law. A corridor is the pair of exact inequalities",
        "x^{2^r} <= n^{3^o} and n^{2^s} <= x^{3^q} at a pivot x = T^j(n).",
        "",
        "## Branch budget",
        "",
        "```text",
        "Mathematical target     On stay-above prefixes, does a pivot corridor",
        "                        constrain x beyond 2^{r+s} <= 3^{o+q}?",
        "Novelty hypothesis      prefix defect or closure forces extremality",
        "                        or a contraction the full word misses",
        "Falsifier               every exact predicate is power_bound_word + image>=n",
        "Existing machinery      power_bound_*, first-defect, cmp_pow,",
        "                        minimal_nonterm_image_ge, excursion corpus",
        "Maximum Phase-0 scope   one probe; stay-above + first-return census; no Lean",
        "```",
        "",
        "## Metadata",
        "",
        f"- search_id: `{window['search_id']}`",
        f"- algorithm_version: `{window['algorithm_version']}`",
        f"- window: `n={window['n_start']}..{window['n_end']}`",
        f"- horizon: `{window['horizon']}` (not L)",
        f"- bit_cap: `{window['bit_cap']}`",
        f"- pivot_policy: `{window['pivot_policy']}`",
        f"- suffix_policy: `{window['suffix_policy']}`",
        f"- engine control layer modified: `{payload['engine_control_layer_modified']}`",
        f"- classification: **{decision['classification']}**",
        f"- secondary: `{decision.get('secondary')}`",
        f"- sorry-free: `{lean['sorry_free']}`",
        "",
        decision["reason"] + ".",
        "",
        "## Census",
        "",
        f"- returned: `{analysis['returned']}`",
        f"- unfinished: `{analysis['unfinished_count']}`",
        f"- corridors: `{analysis['corridor_count']}`",
        f"- stay-above: `{analysis['stay_above_count']}`",
        f"- return suffixes: `{analysis['return_count']}`",
        f"- even stay-above: `{analysis['even_stay_above_count']}`",
        f"- identity failures: `{analysis['identity_failure_count']}`",
        f"- forward unavailable: `{analysis['forward_unavailable']}`",
        f"- reverse unavailable: `{analysis['reverse_unavailable']}`",
        f"- mixed equality: `{len(analysis['mixed_eq'])}`",
        f"- extremal equality count: `{analysis['extremal_eq_count']}`",
        f"- both sides equal: `{len(analysis['both_eq'])}`",
        f"- novel reverse stay-above: `{len(analysis['novel_stay'])}`",
        f"- novel reverse at return: `{len(analysis['novel_return'])}`",
        f"- defect over gap: `{len(analysis['defect_novel'])}`",
        f"- max τ_<: `{analysis['max_tau']}`",
        f"- max peak bits: `{analysis['max_peak_bits']}`",
        "",
        "## Closest stay-above slack",
        "",
    ]
    if not analysis["closest_slack"]:
        lines.append("- none")
    for row in analysis["closest_slack"][:12]:
        lines.append(
            f"- n=`{row['n']}` j=`{row['j']}` s=`{row['s']}` slack=`{row['slack']}` "
            f"G=`{row['exponent_gap']}` prefix=`{row['word_prefix']}` "
            f"suffix=`{row['word_suffix']}` extremal_eq=`{row['prefix_extremal_eq']}`"
        )
    lines.extend(["", "## Hard starts", ""])
    for row in analysis["hard"]:
        lines.append(
            f"- n=`{row['n']}` τ=`{row['tau']}` stay=`{row['stay_above']}` "
            f"return=`{row['return_suffixes']}` ident=`{row['identity_failures']}` "
            f"extremal_eq=`{row['extremal_eq']}` min_slack=`{row['min_slack']}` "
            f"word=`{row['word']}`"
        )
    lines.extend(["", "## Tall starts", ""])
    for row in analysis["tall"]:
        lines.append(
            f"- n=`{row['n']}` τ=`{row['tau']}` peak_bits=`{row['peak_bits']}` "
            f"stay=`{row['stay_above']}` min_slack=`{row['min_slack']}`"
        )
    lines.extend(["", "## Lean", ""])
    for name in FLOOR_LEMMAS:
        lines.append(f"- `{name}`: `{lean.get(name)}`")
    lines.extend(
        [
            f"- `minimal_nonterm_image_ge`: `{lean.get('minimal_nonterm_image_ge')}`",
            f"- new Corridor file absent: `{lean.get('Corridor_absent')}`",
            f"- ResidualStep not extended: `{lean.get('ResidualStep_not_extended')}`",
            f"- CycleDiophantine not rewritten: `{lean.get('CycleDiophantine_not_rewritten')}`",
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
            "A finite stay-above prefix is not a minimal counterexample.",
            "A search-horizon miss is not a bound L. Do not claim termination.",
            "",
        ]
    )
    return "\n".join(lines) + "\n"


def _checksum(analysis: dict[str, Any], classification: str) -> str:
    blob = json.dumps(
        {
            "classification": classification,
            "returned": analysis["returned"],
            "corridor_count": analysis["corridor_count"],
            "stay_above_count": analysis["stay_above_count"],
            "identity_failure_count": analysis["identity_failure_count"],
            "extremal_eq_count": analysis["extremal_eq_count"],
            "mixed_eq": len(analysis["mixed_eq"]),
            "novel_stay": len(analysis["novel_stay"]),
            "novel_return": len(analysis["novel_return"]),
            "max_tau": analysis["max_tau"],
        },
        sort_keys=True,
        separators=(",", ":"),
    )
    return hashlib.sha256(blob.encode("utf-8")).hexdigest()


def _config(n_start: int, n_end: int) -> dict[str, Any]:
    return {
        "search_id": search_id_for(n_start, n_end),
        "algorithm_version": ALGORITHM_VERSION,
        "n_start": n_start,
        "n_end": n_end,
        "horizon": HORIZON,
        "bit_cap": BIT_CAP,
        "pivot_policy": PIVOT_POLICY,
        "suffix_policy": SUFFIX_POLICY,
        "hard_starts": list(HARD_STARTS),
        "tall_starts": list(TALL_STARTS),
        "arithmetic": "python-int",
    }


def _manifest(payload: dict[str, Any]) -> dict[str, Any]:
    window = payload["window"]
    analysis = payload["scan"]["window"]
    return {
        "search_id": window["search_id"],
        "git_commit": git_commit(),
        "algorithm_version": ALGORITHM_VERSION,
        "start_range": [window["n_start"], window["n_end"]],
        "maximum_horizon": window["horizon"],
        "pivot_policy": window["pivot_policy"],
        "suffix_policy": window["suffix_policy"],
        "completion_status": "COMPLETE" if analysis["unfinished_count"] == 0 else "INCOMPLETE",
        "checksum": _checksum(analysis, payload["decision"]["classification"]),
        "classification": payload["decision"]["classification"],
        "runtime_note": "in-memory Phase-0 census; no sqlite",
    }


def write_artifacts(
    payload: dict[str, Any] | None = None,
    *,
    n_start: int = N_MIN,
    n_end: int = N_MAX,
) -> dict[str, Any]:
    data = payload if payload is not None else probe_payload(n_start=n_start, n_end=n_end)
    JSON_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(data, indent=2) + "\n", encoding="utf-8")
    DOC_PATH.write_text(render_markdown(data), encoding="utf-8")
    DATA_DIR.mkdir(parents=True, exist_ok=True)
    (DATA_DIR / "summaries").mkdir(exist_ok=True)
    (DATA_DIR / "analysis").mkdir(exist_ok=True)
    (DATA_DIR / "traces").mkdir(exist_ok=True)
    (DATA_DIR / "README.md").write_text(
        "# Juggler two-sided corridor\n\n"
        "Phase-0 census of exact pivot corridors C_{j,s} on first-return\n"
        "paths. Stay-above means every state through T^{j+s}(n) is >= n.\n"
        "This is not a minimal counterexample and not a termination theorem.\n"
        "Not the REFUTED two-sided exponent-only law.\n\n"
        "```text\n"
        "README.md\n"
        "manifest.json\n"
        "config.json\n"
        "summaries/\n"
        "analysis/\n"
        "traces/\n"
        "```\n\n"
        "From the repository root:\n\n"
        "```text\n"
        "python -m research.juggler_sequence.corridor\n"
        "```\n\n"
        "The Research Engine control layer is not used. ResidualStep is\n"
        "not extended.\n",
        encoding="utf-8",
    )
    window = data["window"]
    (DATA_DIR / "config.json").write_text(
        json.dumps(_config(window["n_start"], window["n_end"]), indent=2) + "\n",
        encoding="utf-8",
    )
    (DATA_DIR / "manifest.json").write_text(
        json.dumps(_manifest(data), indent=2) + "\n", encoding="utf-8"
    )
    (DATA_DIR / "summaries" / "summary.md").write_text(
        render_markdown(data), encoding="utf-8"
    )
    (DATA_DIR / "summaries" / "phase0.json").write_text(
        json.dumps(
            {
                "decision": data["decision"],
                "window": data["window"],
                "census": {
                    key: data["scan"]["window"][key]
                    for key in (
                        "returned",
                        "unfinished_count",
                        "corridor_count",
                        "stay_above_count",
                        "return_count",
                        "even_stay_above_count",
                        "identity_failure_count",
                        "extremal_eq_count",
                        "max_tau",
                        "max_peak_bits",
                    )
                },
            },
            indent=2,
        )
        + "\n",
        encoding="utf-8",
    )
    analysis = data["scan"]["window"]
    (DATA_DIR / "analysis" / "census.json").write_text(
        json.dumps(
            {
                "returned": analysis["returned"],
                "unfinished": analysis["unfinished"],
                "corridor_count": analysis["corridor_count"],
                "stay_above_count": analysis["stay_above_count"],
                "return_count": analysis["return_count"],
                "even_stay_above_count": analysis["even_stay_above_count"],
                "identity_failure_count": analysis["identity_failure_count"],
                "forward_unavailable": analysis["forward_unavailable"],
                "reverse_unavailable": analysis["reverse_unavailable"],
                "extremal_eq_count": analysis["extremal_eq_count"],
                "max_tau": analysis["max_tau"],
                "max_peak_bits": analysis["max_peak_bits"],
            },
            indent=2,
        )
        + "\n",
        encoding="utf-8",
    )
    (DATA_DIR / "analysis" / "hard.json").write_text(
        json.dumps(analysis["hard"], indent=2) + "\n", encoding="utf-8"
    )
    (DATA_DIR / "analysis" / "identities.json").write_text(
        json.dumps(
            {
                "identity_failures": analysis["identity_failures"],
                "mixed_eq": analysis["mixed_eq"],
                "both_eq": analysis["both_eq"],
                "novel_stay": analysis["novel_stay"],
                "novel_return": analysis["novel_return"],
                "defect_novel": analysis["defect_novel"],
            },
            indent=2,
        )
        + "\n",
        encoding="utf-8",
    )
    (DATA_DIR / "traces" / "closest_slack.json").write_text(
        json.dumps(analysis["closest_slack"], indent=2) + "\n", encoding="utf-8"
    )
    return data


def main() -> None:
    payload = write_artifacts()
    print(payload["decision"]["classification"])
    print(payload["decision"]["reason"])


if __name__ == "__main__":
    main()
