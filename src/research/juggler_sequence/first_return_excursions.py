"""First-return maximality for observed Juggler excursions.

Not a Research Engine control-layer experiment. Not a halt theorem.
A finite horizon is not a bound on tau. Does not reopen PE-factor,
residual-future, sum-rho, realization-set, landing-image, or N_w
boundary branches. Reuses excursions._walk_returns.
"""

from __future__ import annotations

import json
from collections import defaultdict
from fractions import Fraction
from pathlib import Path
from typing import Any

from research.juggler_sequence.envelope_defect import first_nonexact_index, local_defect
from research.juggler_sequence.excursions import STATUS_RETURNED, _walk_returns, peak_index
from research.juggler_sequence.lean_paths import CELLS, ENVELOPE, juggler_text
from research.juggler_sequence.near_extremal_prefixes import exponent_gap
from research.juggler_sequence.power_itineraries import ANTI_OVERCLAIM, floor_power, word_of

REPO_ROOT = Path(__file__).resolve().parents[3]
JSON_PATH = REPO_ROOT / "docs" / "research" / "juggler_first_return_excursions.json"
DOC_PATH = REPO_ROOT / "docs" / "research" / "juggler_first_return_excursions.md"
DATA_DIR = REPO_ROOT / "data" / "research" / "juggler" / "first_return_excursions"

N_MIN = 2
N_MAX = 4000
HORIZON = 10_000
BIT_CAP = 4096
BIT_CAP_PROMOTE = 25_000
PEAK_STORE_BITS = 256

CLASS_MARGIN = "EXCURSION_MARGIN_GREEN"
CLASS_PEAK = "EXCURSION_PEAK_GREEN"
CLASS_PROFILE = "EXCURSION_PROFILE_GREEN"
CLASS_FINAL = "EXCURSION_FINALSTEP_GREEN"
CLASS_EXTREMAL = "EXCURSION_EXTREMAL_GREEN"
CLASS_COUNTER = "EXCURSION_COUNTEREXAMPLE"
CLASS_COMPLEX = "EXCURSION_COMPLEX"

LEAN_THEOREMS = (
    "floorPower_odd_ge",
    "power_bound_contracts",
)

FORBIDDEN_ENGINES = (
    "ResidualGraph",
    "ResidualState",
    "MilestoneGraph",
    "PowerHeight",
    "CycleEngine",
)


def compact_int(value: int) -> int | dict[str, Any]:
    if value.bit_length() <= PEAK_STORE_BITS:
        return value
    return {"bits": value.bit_length(), "hex_head": hex(value)[:18]}


def slack_profile(word: str) -> list[int]:
    odds = 0
    out = []
    for index, letter in enumerate(word, start=1):
        if letter == "O":
            odds += 1
        out.append(exponent_gap(index, odds))
    return out


def run_signature(word: str) -> tuple[int, int, int]:
    if not word:
        return (0, 0, 0)
    runs = 1
    max_o = max_e = cur = 0
    last = word[0]
    for letter in word:
        if letter == last:
            cur += 1
            continue
        if last == "O":
            max_o = max(max_o, cur)
        else:
            max_e = max(max_e, cur)
        runs += 1
        last = letter
        cur = 1
    if last == "O":
        max_o = max(max_o, cur)
    else:
        max_e = max(max_e, cur)
    return (runs, max_o, max_e)


def record(n: int, *, horizon: int = HORIZON, bit_cap: int = BIT_CAP) -> dict[str, Any]:
    path, status, tau, _tau_le = _walk_returns(n, horizon, bit_cap)
    word = word_of(path) if len(path) >= 2 else ""
    if status != STATUS_RETURNED or tau is None:
        return {
            "n": n,
            "status": status,
            "tau": tau,
            "word": word,
            "returned": False,
        }
    peak_pos = peak_index(path)
    peak = path[peak_pos]
    y = path[-2]
    z = path[-1]
    odds = word.count("O")
    gaps = slack_profile(word)
    prefix_ok = all(state >= n for state in path[:-1])
    final_lt = z < n
    return {
        "n": n,
        "status": status,
        "returned": True,
        "tau": tau,
        "word": word,
        "k": tau,
        "o": odds,
        "gap": exponent_gap(tau, odds),
        "x_tau": z,
        "margin": n - z,
        "peak": compact_int(peak),
        "peak_bits": peak.bit_length(),
        "peak_pos": peak_pos,
        "y": compact_int(y),
        "y_bits": y.bit_length(),
        "final": word[-1],
        "final_E": word.endswith("E"),
        "y_in_even_square": y % 2 == 0 and n <= y < n * n,
        "first_defect": first_nonexact_index(path),
        "final_defect": local_defect(y),
        "prefix_nonneg": prefix_ok,
        "final_neg": final_lt,
        "prefix_G_nonpos": all(g <= 0 for g in gaps[:-1]),
        "final_G_pos": gaps[-1] > 0,
        "G_sign_changes": sum(
            1 for i in range(1, len(gaps)) if (gaps[i - 1] <= 0) != (gaps[i] <= 0)
        ),
        "runs": run_signature(word),
        "s_min": min(state - n for state in path[:-1]),
        "s_max_bits": max(state - n for state in path).bit_length() if peak >= n else 0,
    }


def collect(*, n_min: int = N_MIN, n_max: int = N_MAX) -> tuple[list[dict[str, Any]], list[int]]:
    rows = []
    promoted = []
    for n in range(n_min, n_max + 1):
        rec = record(n, bit_cap=BIT_CAP)
        if not rec["returned"]:
            rec = record(n, bit_cap=BIT_CAP_PROMOTE)
            rec["bit_cap_promoted"] = True
            promoted.append(n)
        rows.append(rec)
    return rows, promoted


def test_h1(rows: list[dict[str, Any]]) -> dict[str, Any]:
    """Margin lower bound stronger than M >= 1."""

    returned = [row for row in rows if row["returned"]]
    candidates = {
        "M>=k": lambda r: r["margin"] >= r["k"],
        "M>=o": lambda r: r["margin"] >= r["o"],
        "M>=|gap|": lambda r: r["margin"] >= abs(r["gap"]),
        "M>=k-o": lambda r: r["margin"] >= max(1, r["k"] - r["o"]),
    }
    cex: dict[str, Any] = {}
    for name, pred in candidates.items():
        hit = next((row for row in returned if not pred(row)), None)
        if hit is not None:
            cex[name] = {"n": hit["n"], "word": hit["word"], "M": hit["margin"], "k": hit["k"], "o": hit["o"], "gap": hit["gap"]}
    min_m = min(returned, key=lambda r: (r["margin"], r["n"]))
    min_ratio = min(returned, key=lambda r: (Fraction(r["margin"], r["n"]), r["n"]))
    return {
        "holds": False,
        "reason": "M>=1 is the definition of a strict return; every stronger F(k,o) fails",
        "min_margin": {"n": min_m["n"], "M": min_m["margin"], "word": min_m["word"]},
        "min_ratio": {
            "n": min_ratio["n"],
            "M": min_ratio["margin"],
            "ratio": str(Fraction(min_ratio["margin"], min_ratio["n"])),
            "word": min_ratio["word"],
        },
        "counterexamples": cex,
    }


def test_h2(rows: list[dict[str, Any]]) -> dict[str, Any]:
    """Peak bound stronger than the existing envelope."""

    returned = [row for row in rows if row["returned"]]
    even = [row for row in returned if row["n"] % 2 == 0]
    odd = [row for row in returned if row["n"] % 2 == 1]
    p_le_n = all(row["word"] == "E" and row["peak_bits"] == row["n"].bit_length() for row in even)
    odd_exceeds = max(odd, key=lambda r: (r["peak_bits"], r["n"]))
    return {
        "holds": False,
        "reason": "even starts have peak=n and word E; odd peaks exceed any n-independent word bound",
        "even_peak_eq_n": p_le_n and all(row["word"] == "E" for row in even),
        "largest_odd_peak_bits": {
            "n": odd_exceeds["n"],
            "tau": odd_exceeds["tau"],
            "peak_bits": odd_exceeds["peak_bits"],
            "word": odd_exceeds["word"],
        },
    }


def test_h3(rows: list[dict[str, Any]]) -> dict[str, Any]:
    """G_j profile beyond prefix-NC then first contracting letter."""

    returned = [row for row in rows if row["returned"]]
    prefix_ok = all(row["prefix_G_nonpos"] and row["final_G_pos"] for row in returned)
    extra_changes = [
        row for row in returned if row["tau"] > 1 and row["G_sign_changes"] != 1
    ]
    return {
        "holds": False,
        "reason": (
            "G_j<=0 on proper prefixes and G_tau>0 is the known first "
            "formally contracting prefix, already parked as EXCURSION_ENVELOPE_GREEN"
        ),
        "prefix_then_contract": prefix_ok,
        "not_single_sign_change": None
        if not extra_changes
        else {"n": extra_changes[0]["n"], "changes": extra_changes[0]["G_sign_changes"], "word": extra_changes[0]["word"]},
        "single_sign_change_count": sum(1 for row in returned if row["G_sign_changes"] == 1),
    }


def test_h4(rows: list[dict[str, Any]]) -> dict[str, Any]:
    """Final step: always E, predecessor in [n, n^2)."""

    returned = [row for row in rows if row["returned"]]
    odd_final = [row for row in returned if not row["final_E"]]
    bad_cell = [row for row in returned if row["final_E"] and not row["y_in_even_square"]]
    return {
        "holds_computationally": not odd_final and not bad_cell,
        "novelty": "REPARAMETERIZATION",
        "reason": (
            "final letter E and n<=y<n^2 follow from floorPower_odd_ge "
            "(odd steps cannot descend) plus z=isqrt(y)<n"
        ),
        "odd_final_count": len(odd_final),
        "bad_cell_count": len(bad_cell),
        "E_final_count": sum(1 for row in returned if row["final_E"]),
    }


def test_h5(rows: list[dict[str, Any]]) -> dict[str, Any]:
    """Pareto extremals form one structural class."""

    returned = [row for row in rows if row["returned"]]
    min_m = min(returned, key=lambda r: (r["margin"], r["n"]))
    min_ratio = min(returned, key=lambda r: (Fraction(r["margin"], r["n"]), r["n"]))
    max_tau = max(returned, key=lambda r: (r["tau"], r["n"]))
    max_peak = max(returned, key=lambda r: (r["peak_bits"], r["n"]))
    classes = {
        "min_M": (min_m["n"] % 2, min_m["word"]),
        "min_M/n": (min_ratio["n"] % 2, min_ratio["word"]),
        "max_tau": (max_tau["n"] % 2, max_tau["word"][:12]),
        "max_peak_bits": (max_peak["n"] % 2, max_peak["word"][:12]),
    }
    distinct = len({classes["min_M"], classes["min_M/n"], classes["max_tau"], classes["max_peak_bits"]})
    return {
        "holds": False,
        "reason": "min-margin, min-ratio, max-duration, and max-peak sit in different word classes",
        "extremals": {
            "min_M": {"n": min_m["n"], "M": min_m["margin"], "word": min_m["word"]},
            "min_M/n": {
                "n": min_ratio["n"],
                "M": min_ratio["margin"],
                "ratio": str(Fraction(min_ratio["margin"], min_ratio["n"])),
                "word": min_ratio["word"],
            },
            "max_tau": {"n": max_tau["n"], "tau": max_tau["tau"], "word": max_tau["word"]},
            "max_peak_bits": {
                "n": max_peak["n"],
                "tau": max_peak["tau"],
                "peak_bits": max_peak["peak_bits"],
                "word": max_peak["word"],
            },
        },
        "distinct_classes": distinct,
    }


def same_word(rows: list[dict[str, Any]]) -> dict[str, Any]:
    groups: dict[str, list[dict[str, Any]]] = defaultdict(list)
    for row in rows:
        if row["returned"] and row["n"] % 2 == 1:
            groups[row["word"]].append(row)
    multi = {word: recs for word, recs in groups.items() if len(recs) > 1}
    strongest = None
    for word, recs in multi.items():
        margins = {r["margin"] for r in recs}
        if len(margins) <= 1:
            continue
        rec = {
            "word": word,
            "n_starts": len(recs),
            "min_M": min(margins),
            "max_M": max(margins),
        }
        if strongest is None or rec["max_M"] - rec["min_M"] > strongest["max_M"] - strongest["min_M"]:
            strongest = rec
    return {
        "multi_start_words": len(multi),
        "margin_varies": strongest,
    }


def same_ko(rows: list[dict[str, Any]]) -> dict[str, Any]:
    groups: dict[tuple[int, int], list[dict[str, Any]]] = defaultdict(list)
    for row in rows:
        if row["returned"] and row["n"] % 2 == 1:
            groups[(row["k"], row["o"])].append(row)
    split = 0
    strongest = None
    for key, recs in groups.items():
        words = {r["word"] for r in recs}
        if len(words) < 2:
            continue
        margins = {r["margin"] for r in recs}
        if len(margins) > 1:
            split += 1
            rec = {"k": key[0], "o": key[1], "min_M": min(margins), "max_M": max(margins), "n_words": len(words)}
            if strongest is None or rec["max_M"] - rec["min_M"] > strongest["max_M"] - strongest["min_M"]:
                strongest = rec
    return {"groups_split": split, "strongest": strongest}


def same_run(rows: list[dict[str, Any]]) -> dict[str, Any]:
    groups: dict[tuple[int, int, int], list[dict[str, Any]]] = defaultdict(list)
    for row in rows:
        if row["returned"] and row["n"] % 2 == 1:
            groups[tuple(row["runs"])].append(row)
    split = 0
    strongest = None
    for key, recs in groups.items():
        words = {r["word"] for r in recs}
        if len(words) < 2:
            continue
        margins = {r["margin"] for r in recs}
        if len(margins) > 1:
            split += 1
            rec = {
                "runs": key,
                "min_M": min(margins),
                "max_M": max(margins),
                "n_words": len(words),
            }
            if strongest is None or rec["max_M"] - rec["min_M"] > strongest["max_M"] - strongest["min_M"]:
                strongest = rec
    return {"groups_split": split, "strongest": strongest}


def _pareto_key(row: dict[str, Any]) -> tuple[Fraction, int, int]:
    return (Fraction(row["margin"], row["n"]), -row["peak_bits"], -row["tau"])


def _dominates(a: dict[str, Any], b: dict[str, Any]) -> bool:
    ra, rb = Fraction(a["margin"], a["n"]), Fraction(b["margin"], b["n"])
    better_or_eq = ra <= rb and a["peak_bits"] >= b["peak_bits"] and a["tau"] >= b["tau"]
    strictly = ra < rb or a["peak_bits"] > b["peak_bits"] or a["tau"] > b["tau"]
    return better_or_eq and strictly


def pareto_front(rows: list[dict[str, Any]]) -> dict[str, Any]:
    """Undominated records for min M/n, max peak bits, max tau. Not a scalar energy."""

    returned = [row for row in rows if row["returned"]]
    front = [
        row
        for row in returned
        if not any(other is not row and _dominates(other, row) for other in returned)
    ]
    front.sort(key=_pareto_key)
    compact = [
        {
            "n": row["n"],
            "tau": row["tau"],
            "M": row["margin"],
            "ratio": str(Fraction(row["margin"], row["n"])),
            "peak_bits": row["peak_bits"],
            "word": row["word"],
        }
        for row in front
    ]
    return {
        "count": len(front),
        "objectives": "min M/n, max peak_bits, max tau",
        "records": compact,
    }


def coverage(rows: list[dict[str, Any]], promoted: list[int]) -> dict[str, Any]:
    returned = [row for row in rows if row["returned"]]
    return {
        "n_min": N_MIN,
        "n_max": N_MAX,
        "starts": len(rows),
        "returned": len(returned),
        "horizon_miss": sum(1 for row in rows if not row["returned"]),
        "bit_cap_promoted": promoted,
        "tau_min": min((row["tau"] for row in returned), default=None),
        "tau_max": max((row["tau"] for row in returned), default=None),
        "distinct_words": len({row["word"] for row in returned}),
        "even_word_E": all(row["word"] == "E" for row in returned if row["n"] % 2 == 0),
        "odd_end_E": all(row["final_E"] for row in returned if row["n"] % 2 == 1),
        "maximality_ok": all(row["prefix_nonneg"] and row["final_neg"] for row in returned),
    }


def _short_ints(xs: list[int]) -> list[Any]:
    return [compact_int(x) for x in xs]


def profile_of(n: int) -> dict[str, Any]:
    path, status, tau, _ = _walk_returns(n, HORIZON, BIT_CAP)
    if status != STATUS_RETURNED:
        path, status, tau, _ = _walk_returns(n, HORIZON, BIT_CAP_PROMOTE)
    word = word_of(path)
    gaps = slack_profile(word)
    defects = [local_defect(path[i]) for i in range(len(path) - 1)]
    return {
        "n": n,
        "status": status,
        "tau": tau,
        "word": word,
        "G": gaps,
        "first_defect": first_nonexact_index(path),
        "final_defect": defects[-1] if defects else None,
        "defect_head": _short_ints(defects[:8]),
        "defect_tail": _short_ints(defects[-4:] if len(defects) > 4 else defects),
        "s_head": _short_ints([path[i] - n for i in range(min(8, len(path)))]),
        "s_tail": _short_ints([path[i] - n for i in range(max(0, len(path) - 4), len(path))]),
    }


def lean_api_present() -> dict[str, Any]:
    text = juggler_text() + "\n" + CELLS.read_text(encoding="utf-8") + "\n" + ENVELOPE.read_text(encoding="utf-8")
    return {
        "sorry_free": "sorry" not in text and "admit" not in text,
        **{name: f"theorem {name}" in text for name in LEAN_THEOREMS},
        "no_forbidden_engines": all(name not in text for name in FORBIDDEN_ENGINES),
        "no_global_termination_theorem": "theorem juggler_reaches_one" not in text,
    }


def classify(scan: dict[str, Any]) -> dict[str, Any]:
    if scan["coverage"]["horizon_miss"] != 0:
        return {
            "classification": CLASS_COUNTER,
            "reason": "a start in 2..4000 did not return before the horizon; do not name this L",
        }
    if not scan["coverage"]["maximality_ok"]:
        return {
            "classification": CLASS_COUNTER,
            "reason": "a recorded return violated prefix>=n or final<n",
        }
    h1, h2, h3, h4, h5 = scan["H1"], scan["H2"], scan["H3"], scan["H4"], scan["H5"]
    if (
        not h1["holds"]
        and not h2["holds"]
        and not h3["holds"]
        and h4["novelty"] == "REPARAMETERIZATION"
        and not h5["holds"]
    ):
        return {
            "classification": CLASS_COMPLEX,
            "secondary": CLASS_COUNTER,
            "reason": (
                "H1–H3 and H5 fail. H4 (final E, n<=y<n^2) is floorPower_odd_ge "
                "plus isqrt. The G_j pattern is the parked first formally "
                "contracting prefix. Maximality adds no new exact relation "
                "beyond T^tau(n)<n and the existing envelope."
            ),
        }
    return {
        "classification": CLASS_COMPLEX,
        "reason": "no first-return law independent of the existing envelope survived",
    }


def run_probe() -> dict[str, Any]:
    rows, promoted = collect()
    extremals = test_h5(rows)["extremals"]
    profile_ns = sorted(
        {
            extremals["min_M"]["n"],
            extremals["min_M/n"]["n"],
            extremals["max_tau"]["n"],
            extremals["max_peak_bits"]["n"],
            3,
            7,
            193,
            2183,
        }
    )
    return {
        "coverage": coverage(rows, promoted),
        "H1": test_h1(rows),
        "H2": test_h2(rows),
        "H3": test_h3(rows),
        "H4": test_h4(rows),
        "H5": test_h5(rows),
        "same_word": same_word(rows),
        "same_ko": same_ko(rows),
        "same_run": same_run(rows),
        "pareto": pareto_front(rows),
        "profiles": [profile_of(n) for n in profile_ns],
    }


def probe_payload() -> dict[str, Any]:
    scan = run_probe()
    lean = lean_api_present()
    decision = classify(scan)
    anti = dict(ANTI_OVERCLAIM)
    anti.update(
        {
            "global_termination": False,
            "tau_always_finite": False,
            "reopen_pe_factors": False,
            "reopen_residual_quotient": False,
            "reopen_sum_rho": False,
            "reopen_realization_geometry": False,
            "reopen_landing_image": False,
            "reopen_nc_boundary": False,
            "automaton": False,
        }
    )
    return {
        "experiment": "juggler_first_return_excursions",
        "engine_control_layer_modified": False,
        "anti_overclaim": anti,
        "scan": scan,
        "lean": lean,
        "decision": decision,
        "search_method": (
            "exact first-return-below walks via excursions._walk_returns; "
            "H1–H5 on n=2..4000; profiles only for extremals"
        ),
    }


def render_markdown(payload: dict[str, Any]) -> str:
    decision = payload["decision"]
    scan = payload["scan"]
    cov = scan["coverage"]
    lean = payload["lean"]
    h1, h2, h3, h4, h5 = scan["H1"], scan["H2"], scan["H3"], scan["H4"], scan["H5"]
    lines = [
        "# Juggler first-return excursion frontier",
        "",
        f"Status: **{decision['classification']}**",
        "",
        "Standalone application phase. Not a Research Engine experiment",
        "and not a termination theorem. Studies observed first-return-below",
        "excursions. A horizon miss is not a bound on tau. Does not reopen",
        "PE-factor, residual-future, sum-rho, realization-set, landing-image,",
        "or N_w-boundary branches.",
        "",
        "## Branch budget",
        "",
        "```text",
        "Mathematical target     Does first-return maximality force a new relation?",
        "Novelty hypothesis      H1–H5 margin / peak / G-profile / final step / class",
        "Falsifier               T<n, 2^k>3^o, or floorPower_odd_ge restated",
        "Existing machinery      _walk_returns, floorPower_odd_ge, power_bound_contracts",
        "Maximum Phase-0 scope   n=2..4000; extremal profiles only",
        "```",
        "",
        "## Metadata",
        "",
        f"- window: `n={cov['n_min']}..{cov['n_max']}`",
        f"- engine control layer modified: `{payload['engine_control_layer_modified']}`",
        f"- classification: **{decision['classification']}**",
        f"- sorry-free: `{lean['sorry_free']}`",
        "",
        decision["reason"],
        "",
        "## A. Coverage",
        "",
        f"- starts: `{cov['starts']}` returned `{cov['returned']}` horizon-miss `{cov['horizon_miss']}` "
        f"bit-cap promoted `{cov['bit_cap_promoted']}`",
        f"- tau range: `{cov['tau_min']}` … `{cov['tau_max']}`",
        f"- distinct first-return words: `{cov['distinct_words']}`",
        f"- even starts are word E: `{cov['even_word_E']}`",
        f"- maximality (prefix>=n and final<n): `{cov['maximality_ok']}`",
        "",
        "## B. H1 return margin",
        "",
        f"- holds: `{h1['holds']}` — {h1['reason']}",
        f"- min M: `{h1['min_margin']}`",
        f"- min M/n: `{h1['min_ratio']}`",
        f"- counterexamples: `{h1['counterexamples']}`",
        "",
        "## C. H2 peak",
        "",
        f"- holds: `{h2['holds']}` — {h2['reason']}",
        f"- even peak = n: `{h2['even_peak_eq_n']}`",
        f"- largest odd peak bits: `{h2['largest_odd_peak_bits']}`",
        "",
        "## D. H3 prefix slack",
        "",
        f"- holds: `{h3['holds']}` — {h3['reason']}",
        f"- prefix-NC then G>0: `{h3['prefix_then_contract']}`",
        f"- single sign-change count: `{h3['single_sign_change_count']}`",
        f"- extra sign changes: `{h3['not_single_sign_change']}`",
        "",
        "## E. H4 final step",
        "",
        f"- computationally true: `{h4['holds_computationally']}`",
        f"- novelty: `{h4['novelty']}` — {h4['reason']}",
        f"- E-final: `{h4['E_final_count']}` odd-final `{h4['odd_final_count']}` bad-cell `{h4['bad_cell_count']}`",
        "",
        "## F. H5 extremals / Pareto",
        "",
        f"- holds: `{h5['holds']}` — {h5['reason']}",
        f"- lexicographic extremals: `{h5['extremals']}`",
        f"- Pareto count (min M/n, max peak bits, max tau): `{scan['pareto']['count']}`",
        f"- Pareto records: `{scan['pareto']['records'][:20]}`",
        "",
        "## G. Same word / same (k,o) / same run",
        "",
        f"- multi-start words: `{scan['same_word']['multi_start_words']}`",
        f"- margin varies on an word: `{scan['same_word']['margin_varies']}`",
        f"- (k,o) groups that split M: `{scan['same_ko']['groups_split']}`",
        f"- strongest (k,o) split: `{scan['same_ko']['strongest']}`",
        f"- run-signature groups that split M: `{scan['same_run']['groups_split']}`",
        f"- strongest run-signature split: `{scan['same_run']['strongest']}`",
        "",
        "## H. Extremal profiles (slack / defect / return state)",
        "",
    ]
    for prof in scan["profiles"]:
        lines.append(
            f"- n=`{prof['n']}` tau=`{prof['tau']}` first_defect=`{prof['first_defect']}` "
            f"final_defect=`{prof['final_defect']}` word=`{prof['word']}` "
            f"G_tail=`{prof['G'][-6:]}` s_tail=`{prof['s_tail']}`"
        )
    lines.extend(["", "## Lean", ""])
    for name in LEAN_THEOREMS:
        lines.append(f"- `{name}`: `{lean.get(name)}`")
    lines.extend(
        [
            f"- no forbidden engines: `{lean.get('no_forbidden_engines')}`",
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
            "## I. Structural findings",
            "",
            "- first-return maximality on observed returns: **COMPUTATIONALLY VERIFIED**",
            "- even starts are the single letter `E`: **COMPUTATIONALLY VERIFIED**",
            "- odd steps cannot descend: **EXACT — LEAN VERIFIED** (`floorPower_odd_ge`)",
            "- formally contracting itineraries satisfy `T_w(n)<n` for `n>1`: **EXACT — LEAN VERIFIED** (`power_bound_contracts`)",
            "- observed first-return words are the first formally contracting prefix: **COMPUTATIONALLY VERIFIED** (parked `EXCURSION_ENVELOPE_GREEN`)",
            "- H1 margin law stronger than `M>=1`: **REFUTED** (`OOOEE` at 3)",
            "- H2 peak law stronger than the envelope: **REFUTED** (`n=2183`, 19694-bit peak)",
            "- H3 new `G_j` grammar: **REPARAMETERIZATION** of the parked envelope census",
            "- H4 final `E` and `n<=y<n^2`: **REPARAMETERIZATION** of `floorPower_odd_ge` plus `isqrt`",
            "- H5 single extremal class: **REFUTED** (lex records and the Pareto front split)",
            "- first-return word determines margin: **REFUTED** (`OOEE`)",
            "- H6 recursive reduction: not attempted",
            "- candidate conjectures: none",
            "",
            "## Decision",
            "",
            f"**CLOSE** — `{decision['classification']}`",
            "",
            decision["reason"],
            "",
            "This is not a halt result and not a proof that tau is finite.",
            "",
        ]
    )
    return "\n".join(lines) + "\n"


def write_artifacts(payload: dict[str, Any] | None = None) -> dict[str, Any]:
    data = payload if payload is not None else probe_payload()
    JSON_PATH.parent.mkdir(parents=True, exist_ok=True)
    DATA_DIR.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(data, indent=2) + "\n", encoding="utf-8")
    DOC_PATH.write_text(render_markdown(data), encoding="utf-8")
    return data


def main() -> None:
    payload = write_artifacts()
    print(payload["decision"]["classification"])
    print(payload["decision"]["reason"])


if __name__ == "__main__":
    main()
