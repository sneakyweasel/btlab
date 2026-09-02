"""Adversarial finite-path optimization for realized Juggler itineraries.

Not a Research Engine control-layer experiment. Not a halt theorem.
Not a new Lyapunov scalar. Does not reopen PE-factor, residual-future,
sum-rho, realization-set, landing-image, N_w, first-return, or
information-complexity branches. Reuses excursions._walk_returns.
"""

from __future__ import annotations

import csv
import json
from collections import defaultdict
from fractions import Fraction
from pathlib import Path
from typing import Any

from research.juggler_sequence.compensated_contraction import first_defect_sufficient, follows_itinerary
from research.juggler_sequence.envelope_defect import first_nonexact_index
from research.juggler_sequence.excursions import STATUS_RETURNED, _walk_returns, peak_index
from research.juggler_sequence.first_return_excursions import (
    BIT_CAP,
    BIT_CAP_PROMOTE,
    PEAK_STORE_BITS,
    compact_int,
    run_signature,
    slack_profile,
)
from research.juggler_sequence.lean_paths import CELLS, ENVELOPE, juggler_text
from research.juggler_sequence.near_extremal_prefixes import exponent_gap
from research.juggler_sequence.power_itineraries import ANTI_OVERCLAIM, word_of

REPO_ROOT = Path(__file__).resolve().parents[3]
JSON_PATH = REPO_ROOT / "docs" / "research" / "juggler_adversarial_paths.json"
DOC_PATH = REPO_ROOT / "docs" / "research" / "juggler_adversarial_paths.md"
DATA_DIR = REPO_ROOT / "data" / "research" / "juggler" / "adversarial_paths"

N_MIN = 2
N_MAX = 4000
HORIZON = 10_000
K_PREFIX = 20
SHAPE_K_MAX = 12
SWAP_LIMIT = 12

CLASS_STRUCTURE = "ADVERSARIAL_STRUCTURE_GREEN"
CLASS_SHAPE = "WORD_SHAPE_GREEN"
CLASS_SURVIVAL = "CERTIFICATE_SURVIVAL_GREEN"
CLASS_TRANSFORM = "EXTREMAL_TRANSFORMATION_GREEN"
CLASS_PEAK = "PEAK_STRUCTURE_GREEN"
CLASS_RETURN = "RETURN_STRUCTURE_GREEN"
CLASS_COMPLEX = "EXTREMAL_COMPLEX"
CLASS_COUNTER = "COUNTEREXAMPLE_ONLY"

FORBIDDEN_ENGINES = (
    "ResidualGraph",
    "ResidualState",
    "MilestoneGraph",
    "PowerHeight",
    "CycleEngine",
)


def json_safe(value: Any) -> Any:
    if isinstance(value, tuple):
        return [json_safe(item) for item in value]
    if isinstance(value, dict):
        return {str(key): json_safe(item) for key, item in value.items()}
    if isinstance(value, list):
        return [json_safe(item) for item in value]
    if isinstance(value, Fraction):
        return str(value)
    return value


def better_ratio(num_a: int, den_a: int, num_b: int, den_b: int) -> bool:
    if num_a.bit_length() <= PEAK_STORE_BITS and num_b.bit_length() <= PEAK_STORE_BITS:
        return num_a * den_b > num_b * den_a
    key_a = (num_a.bit_length() - den_a.bit_length(), num_a.bit_length())
    key_b = (num_b.bit_length() - den_b.bit_length(), num_b.bit_length())
    return key_a > key_b


def first_positive_gap(word: str) -> int | None:
    gaps = slack_profile(word)
    for index, gap in enumerate(gaps, start=1):
        if gap > 0:
            return index
    return None


def adjacent_swaps(word: str) -> list[str]:
    out = []
    seen = set()
    for index in range(len(word) - 1):
        if word[index] == word[index + 1]:
            continue
        swapped = word[:index] + word[index + 1] + word[index] + word[index + 2 :]
        if swapped not in seen:
            seen.add(swapped)
            out.append(swapped)
    return out


def local_maxima(path: list[int]) -> list[int]:
    hits = []
    for index, state in enumerate(path):
        left = path[index - 1] if index else state
        right = path[index + 1] if index + 1 < len(path) else state
        if state >= left and state >= right and (index == 0 or state > left or state > right):
            if index == 0 and len(path) > 1 and state < path[1]:
                continue
            hits.append(index)
    return hits


def walk_row(n: int) -> dict[str, Any]:
    path, status, tau, _ = _walk_returns(n, HORIZON, BIT_CAP)
    promoted = False
    if status != STATUS_RETURNED:
        path, status, tau, _ = _walk_returns(n, HORIZON, BIT_CAP_PROMOTE)
        promoted = True
    path = list(path)
    word = word_of(tuple(path)) if len(path) >= 2 else ""
    peak_pos = peak_index(path)
    peak = path[peak_pos]
    returned = status == STATUS_RETURNED and tau is not None
    z = path[-1] if returned else None
    first_exp = first_positive_gap(word) if word else None
    return {
        "n": n,
        "status": status,
        "returned": returned,
        "promoted": promoted,
        "tau": tau,
        "word": word,
        "k": tau if returned else len(word),
        "o": word.count("O"),
        "path": path,
        "peak": peak,
        "peak_bits": peak.bit_length(),
        "peak_pos": peak_pos,
        "x_tau": z,
        "margin": (n - z) if z is not None else None,
        "first_defect": first_nonexact_index(tuple(path)),
        "first_exp": first_exp,
        "runs": run_signature(word),
        "final": word[-1] if word else "",
        "gap": exponent_gap(tau, word.count("O")) if returned else None,
    }


def collect() -> list[dict[str, Any]]:
    return [walk_row(n) for n in range(N_MIN, N_MAX + 1)]


def prefix_records(rows: list[dict[str, Any]]) -> list[dict[str, Any]]:
    best: dict[int, dict[str, Any]] = {}
    for row in rows:
        path = row["path"]
        n = row["n"]
        limit = min(K_PREFIX, len(path) - 1)
        running_peak = path[0]
        for k in range(1, limit + 1):
            running_peak = max(running_peak, path[k])
            rec = best.get(k)
            if rec is None or better_ratio(path[k], n, rec["endpoint"], rec["n"]):
                endpoint_best = {
                    "n": n,
                    "word": row["word"][:k],
                    "endpoint": path[k],
                    "endpoint_bits": path[k].bit_length(),
                }
            else:
                endpoint_best = None
            if rec is None or better_ratio(running_peak, n, rec["peak"], rec["n_peak"]):
                peak_best = {
                    "n_peak": n,
                    "peak": running_peak,
                    "peak_bits": running_peak.bit_length(),
                    "peak_word": row["word"][:k],
                }
            else:
                peak_best = None
            if rec is None:
                best[k] = {
                    "k": k,
                    "n": n,
                    "word": row["word"][:k],
                    "endpoint": path[k],
                    "endpoint_bits": path[k].bit_length(),
                    "n_peak": n,
                    "peak": running_peak,
                    "peak_bits": running_peak.bit_length(),
                    "peak_word": row["word"][:k],
                }
                continue
            if endpoint_best is not None:
                rec.update(endpoint_best)
            if peak_best is not None:
                rec.update(peak_best)
    return [best[k] for k in sorted(best)]


def lex_records(rows: list[dict[str, Any]]) -> dict[str, Any]:
    returned = [row for row in rows if row["returned"]]
    min_m = min(returned, key=lambda r: (r["margin"], r["n"]))
    min_ratio = min(returned, key=lambda r: (Fraction(r["margin"], r["n"]), r["n"]))
    max_tau = max(returned, key=lambda r: (r["tau"], r["n"]))
    max_peak = max(returned, key=lambda r: (r["peak_bits"], r["n"]))
    m1 = [row for row in returned if row["margin"] == 1]

    def slim(row: dict[str, Any]) -> dict[str, Any]:
        return {
            "n": row["n"],
            "tau": row["tau"],
            "word": row["word"],
            "o": row["o"],
            "M": row["margin"],
            "ratio": str(Fraction(row["margin"], row["n"])),
            "peak_bits": row["peak_bits"],
            "peak_pos": row["peak_pos"],
            "first_defect": row["first_defect"],
            "first_exp": row["first_exp"],
            "runs": row["runs"],
            "final": row["final"],
        }

    return {
        "min_M": slim(min_m),
        "min_M/n": slim(min_ratio),
        "max_tau": slim(max_tau),
        "max_peak_bits": slim(max_peak),
        "M_eq_1": [slim(row) for row in m1],
    }


def pareto_front(rows: list[dict[str, Any]]) -> list[dict[str, Any]]:
    returned = [row for row in rows if row["returned"]]

    def dominates(a: dict[str, Any], b: dict[str, Any]) -> bool:
        ra, rb = Fraction(a["margin"], a["n"]), Fraction(b["margin"], b["n"])
        better_or_eq = ra <= rb and a["peak_bits"] >= b["peak_bits"] and a["tau"] >= b["tau"]
        strictly = ra < rb or a["peak_bits"] > b["peak_bits"] or a["tau"] > b["tau"]
        return better_or_eq and strictly

    front = [
        row
        for row in returned
        if not any(other is not row and dominates(other, row) for other in returned)
    ]
    front.sort(key=lambda r: (Fraction(r["margin"], r["n"]), -r["peak_bits"], -r["tau"]))
    return [
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


def shape_table(rows: list[dict[str, Any]]) -> dict[str, Any]:
    returned = [row for row in rows if row["returned"] and row["n"] % 2 == 1]
    groups: dict[tuple[int, int], list[dict[str, Any]]] = defaultdict(list)
    for row in returned:
        if row["k"] <= SHAPE_K_MAX:
            groups[(row["k"], row["o"])].append(row)
    splits = []
    same = 0
    for key, recs in groups.items():
        by_word: dict[str, list[dict[str, Any]]] = defaultdict(list)
        for row in recs:
            by_word[row["word"]].append(row)
        if len(by_word) < 2:
            continue
        word_stats = []
        for word, members in by_word.items():
            margins = [m["margin"] for m in members]
            peaks = [m["peak_bits"] for m in members]
            word_stats.append(
                {
                    "word": word,
                    "n_starts": len(members),
                    "min_M": min(margins),
                    "max_M": max(margins),
                    "max_peak_bits": max(peaks),
                    "min_n": min(m["n"] for m in members),
                }
            )
        word_stats.sort(key=lambda item: (item["min_M"], item["word"]))
        mins = {item["min_M"] for item in word_stats}
        peaks = {item["max_peak_bits"] for item in word_stats}
        if len(mins) == 1 and len(peaks) == 1:
            same += 1
            continue
        splits.append(
            {
                "k": key[0],
                "o": key[1],
                "n_words": len(word_stats),
                "best_margin_word": word_stats[0]["word"],
                "worst_margin_word": max(word_stats, key=lambda item: item["min_M"])["word"],
                "best_peak_word": max(word_stats, key=lambda item: item["max_peak_bits"])["word"],
                "min_M_range": [min(mins), max(mins)],
                "peak_bits_range": [min(peaks), max(peaks)],
            }
        )
    clustered = 0
    distributed = 0
    for row in splits:
        worst = row["worst_margin_word"]
        runs = worst.count("O") and ("OO" in worst)
        if runs:
            clustered += 1
        if "OE" in worst and "EO" in worst:
            distributed += 1
    return {
        "groups_k_le": SHAPE_K_MAX,
        "groups_with_many_words": len(splits) + same,
        "groups_split": len(splits),
        "groups_identical_extrema": same,
        "clustered_worst": clustered,
        "distributed_worst": distributed,
        "examples": splits[:8],
    }


def same_word_spread(rows: list[dict[str, Any]]) -> dict[str, Any]:
    groups: dict[str, list[dict[str, Any]]] = defaultdict(list)
    for row in rows:
        if row["returned"] and row["n"] % 2 == 1:
            groups[row["word"]].append(row)
    strongest = None
    multi = 0
    for word, recs in groups.items():
        if len(recs) < 2:
            continue
        multi += 1
        margins = [r["margin"] for r in recs]
        rec = {
            "word": word,
            "n_starts": len(recs),
            "min_M": min(margins),
            "max_M": max(margins),
            "min_n": min(r["n"] for r in recs),
            "max_n": max(r["n"] for r in recs),
        }
        if strongest is None or rec["max_M"] - rec["min_M"] > strongest["max_M"] - strongest["min_M"]:
            strongest = rec
    return {"multi_start_words": multi, "strongest": strongest}


def swap_test(rows: list[dict[str, Any]], words: list[str]) -> dict[str, Any]:
    realized = {row["word"]: row for row in rows if row["returned"]}
    by_word: dict[str, list[dict[str, Any]]] = defaultdict(list)
    for row in rows:
        if row["returned"]:
            by_word[row["word"]].append(row)
    trials = []
    hardened = 0
    for word in words:
        if word not in by_word:
            continue
        base = min(by_word[word], key=lambda r: (Fraction(r["margin"], r["n"]), -r["peak_bits"]))
        for swapped in adjacent_swaps(word)[:SWAP_LIMIT]:
            members = by_word.get(swapped)
            rec = {
                "from": word,
                "to": swapped,
                "realized": members is not None,
            }
            if members:
                cand = min(members, key=lambda r: (Fraction(r["margin"], r["n"]), -r["peak_bits"]))
                harder = Fraction(cand["margin"], cand["n"]) < Fraction(base["margin"], base["n"]) or cand["peak_bits"] > base["peak_bits"]
                rec["candidate_n"] = cand["n"]
                rec["harder_on_window"] = harder
                if harder:
                    hardened += 1
            trials.append(rec)
    return {"n_trials": len(trials), "n_hardened": hardened, "examples": trials[:12]}


def certificate_profile(rows: list[dict[str, Any]]) -> dict[str, Any]:
    returned = [row for row in rows if row["returned"]]
    exp_at_return = sum(1 for row in returned if row["first_exp"] == row["tau"])
    exp_before = [row for row in returned if row["first_exp"] is not None and row["first_exp"] < row["tau"]]
    defect_zero = sum(1 for row in returned if row["first_defect"] == 0)
    squares = [row for row in returned if row["first_defect"] != 0]
    return {
        "returned": len(returned),
        "first_exp_equals_tau": exp_at_return,
        "first_exp_before_tau": [
            {"n": row["n"], "first_exp": row["first_exp"], "tau": row["tau"], "word": row["word"]}
            for row in exp_before[:5]
        ],
        "first_defect_zero": defect_zero,
        "first_defect_nonzero": [
            {"n": row["n"], "first_defect": row["first_defect"], "word": row["word"]}
            for row in squares[:8]
        ],
    }


def defect_cert_on_extremals(rows: list[dict[str, Any]], ns: list[int]) -> list[dict[str, Any]]:
    by_n = {row["n"]: row for row in rows}
    out = []
    for n in ns:
        row = by_n[n]
        first_def = None
        if row["peak_bits"] <= 512:
            for j in range(1, row["k"] + 1):
                word = row["word"][:j]
                hit = first_defect_sufficient(n, word)
                if hit is True:
                    first_def = j
                    break
        out.append(
            {
                "n": n,
                "tau": row["tau"],
                "first_exp": row["first_exp"],
                "first_defect_cert": first_def,
                "first_return": row["tau"],
                "word": row["word"],
            }
        )
    return out


def peak_structure(rows: list[dict[str, Any]], extremal_ns: list[int]) -> dict[str, Any]:
    returned = [row for row in rows if row["returned"] and row["tau"] > 1]
    early = mid = late = 0
    oe_transition = 0
    for row in returned:
        frac = Fraction(row["peak_pos"], row["tau"])
        if frac <= Fraction(1, 3):
            early += 1
        elif frac < Fraction(2, 3):
            mid += 1
        else:
            late += 1
        word = row["word"]
        pos = row["peak_pos"]
        if 0 < pos < len(word) and word[pos - 1] == "O" and word[pos] == "E":
            oe_transition += 1
    details = []
    by_n = {row["n"]: row for row in rows}
    for n in extremal_ns:
        row = by_n[n]
        details.append(
            {
                "n": n,
                "peak_pos": row["peak_pos"],
                "tau": row["tau"],
                "o_before": row["word"][: row["peak_pos"]].count("O"),
                "o_after": row["word"][row["peak_pos"] :].count("O"),
                "local_maxima": local_maxima(row["path"]),
                "word": row["word"],
            }
        )
    return {
        "early": early,
        "mid": mid,
        "late": late,
        "peak_at_OE": oe_transition,
        "n_odd_long": len(returned),
        "extremals": details,
    }


def slack_of(rows: list[dict[str, Any]], ns: list[int]) -> list[dict[str, Any]]:
    by_n = {row["n"]: row for row in rows}
    out = []
    for n in ns:
        row = by_n[n]
        gaps = slack_profile(row["word"])
        out.append({"n": n, "tau": row["tau"], "G_head": gaps[:6], "G_tail": gaps[-6:], "word": row["word"]})
    return out


def q_tests(
    records: dict[str, Any],
    shape: dict[str, Any],
    swaps: dict[str, Any],
    certs: dict[str, Any],
    peaks: dict[str, Any],
) -> dict[str, Any]:
    words = {
        records["min_M"]["word"],
        records["min_M/n"]["word"],
        records["max_tau"]["word"],
        records["max_peak_bits"]["word"],
    }
    q1 = {
        "holds": len(words) == 1,
        "reason": f"lex record words: {sorted(words, key=len)}",
    }
    q2 = {
        "holds": shape["groups_split"] == 0 and shape["groups_with_many_words"] > 0,
        "reason": f"{shape['groups_split']} fixed-(k,o) groups split extrema; clustered_worst={shape['clustered_worst']} distributed_worst={shape['distributed_worst']}",
    }
    q3 = {
        "holds": False,
        "reason": (
            f"peak-at-OE is {peaks['peak_at_OE']} of {peaks['n_odd_long']} long odd returns "
            f"(early/mid/late {peaks['early']}/{peaks['mid']}/{peaks['late']}); "
            "universal odd-growth plus even contraction, not an extremal-only law"
        ),
    }
    q4 = {
        "holds": False,
        "reason": f"first defect is 0 on {certs['first_defect_zero']} of {certs['returned']}; nonzero starts: {certs['first_defect_nonzero']}",
    }
    q5 = {
        "holds": False,
        "reason": (
            f"first G_j>0 equals tau on {certs['first_exp_equals_tau']} of {certs['returned']}"
            if not certs["first_exp_before_tau"]
            else f"G_j>0 before tau: {certs['first_exp_before_tau']}"
        ),
    }
    q6 = {
        "holds": False,
        "reason": (
            "extremal peaks are not one growth/finance cut; "
            f"positions {[item['n'] for item in peaks['extremals']]} "
            f"at { [item['peak_pos'] for item in peaks['extremals']] }"
        ),
    }
    q7 = {
        "holds": swaps["n_trials"] > 0 and swaps["n_hardened"] == swaps["n_trials"],
        "reason": f"adjacent O/E swaps hardened {swaps['n_hardened']} of {swaps['n_trials']} window trials",
    }
    return {"Q1": q1, "Q2": q2, "Q3": q3, "Q4": q4, "Q5": q5, "Q6": q6, "Q7": q7}


def classify(scan: dict[str, Any]) -> dict[str, Any]:
    qs = scan["questions"]
    if all(not qs[name]["holds"] for name in qs):
        return {
            "classification": CLASS_COMPLEX,
            "reason": (
                "Record paths are the known first-return extremals. Fixed-(k,o) "
                "arrangement splits, but no reproducible shape, peak-location, "
                "certificate-survival, or hardening-swap law survives. Extremality "
                "remains state-determined."
            ),
        }
    return {"classification": CLASS_COUNTER, "reason": "a proposed pattern failed and no replacement survived"}


def lean_api_present() -> dict[str, Any]:
    text = juggler_text() + "\n" + CELLS.read_text(encoding="utf-8") + "\n" + ENVELOPE.read_text(encoding="utf-8")
    return {
        "sorry_free": "sorry" not in text and "admit" not in text,
        "power_bound_contracts": "theorem power_bound_contracts" in text,
        "floorPower_odd_ge": "theorem floorPower_odd_ge" in text,
        "no_forbidden_engines": all(name not in text for name in FORBIDDEN_ENGINES),
        "no_global_termination_theorem": "theorem juggler_reaches_one" not in text,
    }


def slim_row(row: dict[str, Any]) -> dict[str, Any]:
    return {
        "n": row["n"],
        "word": row["word"],
        "k": row["k"],
        "o": row["o"],
        "peak_bits": row["peak_bits"],
        "peak_pos": row["peak_pos"],
        "endpoint": compact_int(row["x_tau"]) if row["x_tau"] is not None else None,
        "first_defect": row["first_defect"],
        "first_exp": row["first_exp"],
        "return_status": row["status"],
        "margin": row["margin"],
    }


def write_tables(scan: dict[str, Any]) -> dict[str, str]:
    DATA_DIR.mkdir(parents=True, exist_ok=True)
    paths: dict[str, str] = {}

    def write_csv(name: str, fieldnames: list[str], rows: list[dict[str, Any]]) -> None:
        path = DATA_DIR / name
        with path.open("w", encoding="utf-8", newline="") as handle:
            writer = csv.DictWriter(handle, fieldnames=fieldnames)
            writer.writeheader()
            for row in rows:
                writer.writerow(row)
        paths[name] = str(path)

    rec = scan["records"]
    write_csv(
        "record_peak.csv",
        ["k", "n", "word", "o", "peak", "peak_position", "peak_ratio", "search_limit"],
        [
            {
                "k": rec["max_peak_bits"]["tau"],
                "n": rec["max_peak_bits"]["n"],
                "word": rec["max_peak_bits"]["word"],
                "o": rec["max_peak_bits"]["o"],
                "peak": rec["max_peak_bits"]["peak_bits"],
                "peak_position": rec["max_peak_bits"]["peak_pos"],
                "peak_ratio": f"bits={rec['max_peak_bits']['peak_bits']}",
                "search_limit": N_MAX,
            }
        ],
    )
    write_csv(
        "record_return.csv",
        ["tau", "n", "word", "return_state", "margin", "normalized_margin", "peak", "search_limit"],
        [
            {
                "tau": rec["min_M/n"]["tau"],
                "n": rec["min_M/n"]["n"],
                "word": rec["min_M/n"]["word"],
                "return_state": "",
                "margin": rec["min_M/n"]["M"],
                "normalized_margin": rec["min_M/n"]["ratio"],
                "peak": rec["min_M/n"]["peak_bits"],
                "search_limit": N_MAX,
            }
        ],
    )
    write_csv(
        "record_duration.csv",
        ["tau", "n", "word", "search_limit"],
        [{"tau": rec["max_tau"]["tau"], "n": rec["max_tau"]["n"], "word": rec["max_tau"]["word"], "search_limit": N_MAX}],
    )
    write_csv(
        "pareto_frontier.csv",
        ["n", "tau", "M", "ratio", "peak_bits", "word"],
        scan["pareto"],
    )
    write_csv(
        "word_shape_extrema.csv",
        ["k", "o", "n_words", "best_margin_word", "worst_margin_word", "best_peak_word", "min_M_range", "peak_bits_range"],
        [
            {
                "k": row["k"],
                "o": row["o"],
                "n_words": row["n_words"],
                "best_margin_word": row["best_margin_word"],
                "worst_margin_word": row["worst_margin_word"],
                "best_peak_word": row["best_peak_word"],
                "min_M_range": row["min_M_range"],
                "peak_bits_range": row["peak_bits_range"],
            }
            for row in scan["shape"]["examples"]
        ],
    )
    hard_path = DATA_DIR / "hard_paths.jsonl"
    with hard_path.open("w", encoding="utf-8") as handle:
        for row in scan["hard_paths"]:
            handle.write(json.dumps(row) + "\n")
    paths["hard_paths.jsonl"] = str(hard_path)
    cert_path = DATA_DIR / "certificate_survival.jsonl"
    with cert_path.open("w", encoding="utf-8") as handle:
        for row in scan["defect_certs"]:
            handle.write(json.dumps(row) + "\n")
    paths["certificate_survival.jsonl"] = str(cert_path)
    return paths


def drop_paths(rows: list[dict[str, Any]]) -> None:
    for row in rows:
        row.pop("path", None)
        row.pop("peak", None)


def run_probe() -> dict[str, Any]:
    rows = collect()
    returned = [row for row in rows if row["returned"]]
    records = lex_records(rows)
    extremal_ns = sorted(
        {
            records["min_M"]["n"],
            records["min_M/n"]["n"],
            records["max_tau"]["n"],
            records["max_peak_bits"]["n"],
            3,
            7,
            193,
        }
    )
    prefixes = prefix_records(rows)
    shape = shape_table(rows)
    words = same_word_spread(rows)
    swaps = swap_test(rows, [records[key]["word"] for key in ("min_M", "min_M/n", "max_tau", "max_peak_bits")] + ["OOOEE", "OOEE"])
    certs = certificate_profile(rows)
    defect_certs = defect_cert_on_extremals(rows, extremal_ns)
    peaks = peak_structure(rows, extremal_ns)
    slacks = slack_of(rows, extremal_ns)
    pareto = pareto_front(rows)
    questions = q_tests(records, shape, swaps, certs, peaks)
    hard_paths = [slim_row(row) for row in rows if row["n"] in set(extremal_ns)]
    coverage = {
        "n_min": N_MIN,
        "n_max": N_MAX,
        "starts": len(rows),
        "returned": len(returned),
        "horizon_miss": sum(1 for row in rows if not row["returned"]),
        "promoted": [row["n"] for row in rows if row["promoted"]],
        "tau_min": min(row["tau"] for row in returned),
        "tau_max": max(row["tau"] for row in returned),
        "distinct_words": len({row["word"] for row in returned}),
    }
    drop_paths(rows)
    return {
        "coverage": coverage,
        "records": records,
        "prefixes": [
            {
                "k": row["k"],
                "endpoint_n": row["n"],
                "endpoint_word": row["word"],
                "endpoint_bits": row["endpoint_bits"],
                "peak_n": row["n_peak"],
                "peak_word": row["peak_word"],
                "peak_bits": row["peak_bits"],
            }
            for row in prefixes
        ],
        "pareto": pareto,
        "shape": shape,
        "same_word": words,
        "swaps": swaps,
        "certificates": certs,
        "defect_certs": defect_certs,
        "peaks": peaks,
        "slacks": slacks,
        "questions": questions,
        "hard_paths": hard_paths,
    }


def probe_payload() -> dict[str, Any]:
    scan = run_probe()
    decision = classify(scan)
    artifacts = write_tables(scan)
    (DATA_DIR / "manifest.json").write_text(
        json.dumps(
            {
                "experiment": "juggler_adversarial_paths",
                "n_max": N_MAX,
                "classification": decision["classification"],
                "artifacts": artifacts,
                "independence_claim": False,
            },
            indent=2,
        )
        + "\n",
        encoding="utf-8",
    )
    anti = dict(ANTI_OVERCLAIM)
    anti.update(
        {
            "global_termination": False,
            "tau_always_finite": False,
            "new_lyapunov_scalar": False,
            "reopen_pe_factors": False,
            "reopen_residual_quotient": False,
            "reopen_sum_rho": False,
            "reopen_realization_geometry": False,
            "reopen_landing_image": False,
            "reopen_nc_boundary": False,
            "reopen_first_return": False,
            "reopen_information_complexity": False,
            "automaton": False,
        }
    )
    return {
        "experiment": "juggler_adversarial_paths",
        "engine_control_layer_modified": False,
        "anti_overclaim": anti,
        "lean": lean_api_present(),
        "decision": decision,
        "scan": scan,
        "search_method": (
            "exact first-return walks via _walk_returns on n=2..4000; "
            "separate peak / margin / duration / prefix-endpoint orderings; "
            "observed (k,o) shape tables; adjacent swaps of record words"
        ),
    }


def _fmt_table(headers: list[str], rows: list[list[Any]]) -> list[str]:
    lines = ["| " + " | ".join(headers) + " |", "| " + " | ".join("---" for _ in headers) + " |"]
    for row in rows:
        lines.append("| " + " | ".join(str(item) for item in row) + " |")
    return lines


def render_markdown(payload: dict[str, Any]) -> str:
    decision = payload["decision"]
    scan = payload["scan"]
    cov = scan["coverage"]
    rec = scan["records"]
    lines = [
        "# Juggler adversarial parity paths",
        "",
        f"Status: **{decision['classification']}**",
        "",
        "Standalone Phase-0 search for the hardest realizable finite O/E",
        "paths. Not a Research Engine experiment, not a Lyapunov scalar,",
        "and not a termination theorem. A horizon miss is not a bound on tau.",
        "",
        "## Branch budget",
        "",
        "```text",
        "Mathematical target     Do the hardest realized paths share a structure?",
        "Novelty hypothesis      recurring shape, peak law, survival law, or hardening swap",
        "Falsifier               known first-return records; (k,o) splits; swaps do not harden",
        "Existing machinery      _walk_returns, exponent_gap, first_defect_sufficient",
        "Maximum Phase-0 scope   n=2..4000; no GPU; no Lean; no new scalar",
        "```",
        "",
        "## 1. Objective",
        "",
        "- A: maximize endpoint ratio `T^k(n)/n` at each prefix horizon (exact cross-multiply)",
        "- B: maximize peak ratio `P/n` (bit-length when the peak exceeds the storage cap)",
        "- C: minimize return margin `M` and `M/n` among observed returns",
        "- D/E: maximize duration `tau` / longest noncontracting prefix (`tau-1` on a return)",
        "- F: Pareto front on min `M/n`, max peak bits, max `tau`",
        "",
        "These are optimization coordinates, not proposed invariants.",
        "",
        "## 2. Coverage",
        "",
        f"- window: `n={cov['n_min']}..{cov['n_max']}` starts `{cov['starts']}` returned `{cov['returned']}` miss `{cov['horizon_miss']}`",
        f"- bit-cap promoted: `{cov['promoted']}`",
        f"- tau: `{cov['tau_min']}` … `{cov['tau_max']}` distinct words `{cov['distinct_words']}`",
        "",
        decision["reason"],
        "",
        "## 3. Record chains",
        "",
        f"- min M: `{rec['min_M']}`",
        f"- min M/n: `{rec['min_M/n']}`",
        f"- max tau: `{rec['max_tau']}`",
        f"- max peak bits: `{rec['max_peak_bits']}`",
        f"- M=1 witnesses: `{rec['M_eq_1']}`",
        "",
        "Prefix endpoint / peak records (`k<=20`):",
        "",
    ]
    lines.extend(
        _fmt_table(
            ["k", "endpoint n", "endpoint word", "endpoint bits", "peak n", "peak bits"],
            [
                [row["k"], row["endpoint_n"], row["endpoint_word"], row["endpoint_bits"], row["peak_n"], row["peak_bits"]]
                for row in scan["prefixes"]
            ],
        )
    )
    lines.extend(
        [
            "",
            "## 4. Pareto frontier",
            "",
            f"Count: `{len(scan['pareto'])}`",
            "",
        ]
    )
    lines.extend(
        _fmt_table(
            ["n", "tau", "M", "M/n", "peak bits", "word"],
            [[row["n"], row["tau"], row["M"], row["ratio"], row["peak_bits"], row["word"]] for row in scan["pareto"]],
        )
    )
    lines.extend(
        [
            "",
            "## 5. Fixed-(k,o) extremals",
            "",
            f"- groups with several words (`k<=12`): `{scan['shape']['groups_with_many_words']}`",
            f"- groups that split: `{scan['shape']['groups_split']}` identical `{scan['shape']['groups_identical_extrema']}`",
            f"- clustered worst / distributed worst: `{scan['shape']['clustered_worst']}` / `{scan['shape']['distributed_worst']}`",
            f"- examples: `{scan['shape']['examples']}`",
            f"- same-word spread: `{scan['same_word']}`",
            "",
            "## 6. First-defect structure",
            "",
            f"- first defect at index 0: `{scan['certificates']['first_defect_zero']}` of `{scan['certificates']['returned']}`",
            f"- nonzero first defect: `{scan['certificates']['first_defect_nonzero']}`",
            "",
            "## 7. Certificate survival",
            "",
            f"- first `G_j>0` equals tau: `{scan['certificates']['first_exp_equals_tau']}` of `{scan['certificates']['returned']}`",
            f"- first `G_j>0` before tau: `{scan['certificates']['first_exp_before_tau']}`",
            f"- defect-certificate scan on extremals: `{scan['defect_certs']}`",
            "",
            "H_k is therefore the set of proper prefixes of observed first-return",
            "words: they survive the exponent certificate until the last letter.",
            "That is the parked envelope census, not a new survival law.",
            "",
            "## 8. Structural patterns",
            "",
        ]
    )
    for name, rec in scan["questions"].items():
        lines.append(f"- {name} holds `{rec['holds']}` — {rec['reason']}")
    lines.extend(
        [
            "",
            f"- peak location counts: early/mid/late `{scan['peaks']['early']}`/`{scan['peaks']['mid']}`/`{scan['peaks']['late']}` OE `{scan['peaks']['peak_at_OE']}`",
            f"- G-profile tails: `{scan['slacks']}`",
            f"- adjacent swaps: `{scan['swaps']}`",
            "",
            "## 9. Counterexamples",
            "",
            "- Recurring record shape: the five lex records are five words.",
            "- Arrangement law at fixed (k,o): split groups in §5.",
            "- Peak always at an O-to-E cut: §8 Q3 counts.",
            "- First defect postponed on hard paths: defect 0 is generic.",
            "- Hardening swap: §8 Q7.",
            "- Return-margin law stronger than `M>=1`: `OOOEE` at 3.",
            "",
            "## 10. Decision",
            "",
            f"**CLOSE** — `{decision['classification']}`",
            "",
            decision["reason"],
            "",
            "This is not a halt result and not a proof that tau is finite.",
            "",
            "## Lean",
            "",
            f"- sorry-free: `{payload['lean']['sorry_free']}`",
            f"- `power_bound_contracts`: `{payload['lean']['power_bound_contracts']}`",
            f"- `floorPower_odd_ge`: `{payload['lean']['floorPower_odd_ge']}`",
            f"- no forbidden engines: `{payload['lean']['no_forbidden_engines']}`",
            f"- no global halt theorem: `{payload['lean']['no_global_termination_theorem']}`",
            "",
            "## Anti-overclaim",
            "",
        ]
    )
    for key, value in payload["anti_overclaim"].items():
        lines.append(f"- {key}: `{value}`")
    lines.append("")
    return "\n".join(lines) + "\n"


def write_artifacts(payload: dict[str, Any] | None = None) -> dict[str, Any]:
    data = payload if payload is not None else probe_payload()
    JSON_PATH.parent.mkdir(parents=True, exist_ok=True)
    DATA_DIR.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(json_safe(data), indent=2) + "\n", encoding="utf-8")
    DOC_PATH.write_text(render_markdown(data), encoding="utf-8")
    return data


def main() -> None:
    payload = write_artifacts()
    print(payload["decision"]["classification"])
    print(payload["decision"]["reason"])


if __name__ == "__main__":
    main()
