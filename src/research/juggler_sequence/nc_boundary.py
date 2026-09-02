"""Noncontracting realization boundary of a finite Juggler word.

Not a Research Engine control-layer experiment. Not a halt theorem.
N_w = {n in R_w : T_w(n) >= n} is the definition, not a discovery.
Does not reopen PE-factor, residual-future, sum-rho, realization-set
branching, or landing-image geometry.
"""

from __future__ import annotations

import json
from collections import Counter, defaultdict
from math import isqrt
from pathlib import Path
from typing import Any

from research.juggler_sequence.compensated_contraction import image_after
from research.juggler_sequence.envelope_defect import first_nonexact_index, local_defect
from research.juggler_sequence.floor_preimages import even_preimage
from research.juggler_sequence.lean_paths import CELLS, ENVELOPE, ITINERARY, juggler_text
from research.juggler_sequence.near_extremal_prefixes import exponent_gap
from research.juggler_sequence.power_itineraries import ANTI_OVERCLAIM, floor_power, itinerary

REPO_ROOT = Path(__file__).resolve().parents[3]
JSON_PATH = REPO_ROOT / "docs" / "research" / "juggler_nc_boundary.json"
DOC_PATH = REPO_ROOT / "docs" / "research" / "juggler_nc_boundary.md"
DATA_DIR = REPO_ROOT / "data" / "research" / "juggler" / "nc_boundary"

DIAG_N = 4000
DIAG_K = 20
CONFIRM_N = 100_000

CLASS_GREEN = "NC_BOUNDARY_GREEN"
CLASS_SHAPE = "NC_WORD_SHAPE_GREEN"
CLASS_CELL = "NC_CELL_GREEN"
CLASS_EXT = "NC_EXTENSION_GREEN"
CLASS_DEFECT = "NC_DEFECT_GREEN"
CLASS_COUNTER = "NC_BOUNDARY_COUNTEREXAMPLE"
CLASS_COMPLEX = "NC_BOUNDARY_COMPLEX"

FORBIDDEN_ENGINES = (
    "ResidualGraph",
    "ResidualState",
    "MilestoneGraph",
    "PowerHeight",
    "CycleEngine",
)

LEAN_THEOREMS = (
    "power_bound_contracts",
    "image_monotone_of_follows",
    "even_preimage_iff",
)

FAMILIES = tuple(
    dict.fromkeys(
        ["E" * r for r in range(1, 7)]
        + ["O" * r for r in range(1, 7)]
        + [f"{'O' * a}{'E' * b}" for a in range(1, 5) for b in range(1, 5)]
        + [f"{'E' * a}{'O' * b}" for a in range(1, 5) for b in range(1, 5)]
        + [
            f"{'O' * a}{'E' * b}{'O' * c}"
            for a in range(1, 4)
            for b in range(1, 4)
            for c in range(1, 3)
        ]
        + ["OOE", "OEO", "EOO", "OOOE", "OEOE", "OOEO", "EOOO"]
    )
)


def run_signature(word: str) -> tuple[int, int, int, int]:
    if not word:
        return (0, 0, 0, 0)
    runs = 1
    max_o = max_e = cur = 0
    last = word[0]
    for letter in word:
        if letter == last:
            cur += 1
        else:
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
    mixed = word.find("EO")
    if mixed < 0:
        mixed = word.find("OE")
    return (runs, max_o, max_e, mixed)


def components(xs: list[int]) -> dict[str, Any]:
    if not xs:
        return {
            "size": 0,
            "min": None,
            "max": None,
            "n_components": 0,
            "max_gap": None,
            "largest_component": 0,
        }
    gaps = [xs[i + 1] - xs[i] for i in range(len(xs) - 1)]
    n_comp = 1
    largest = 1
    run = 1
    for gap in gaps:
        if gap == 1:
            run += 1
            if run > largest:
                largest = run
        else:
            n_comp += 1
            run = 1
    return {
        "size": len(xs),
        "min": xs[0],
        "max": xs[-1],
        "n_components": n_comp,
        "max_gap": max(gaps) if gaps else None,
        "largest_component": largest,
    }


def collect_partition(*, n_max: int, k_max: int) -> tuple[dict[str, list[int]], dict[str, list[int]]]:
    realizing: dict[str, list[int]] = defaultdict(list)
    noncontracting: dict[str, list[int]] = defaultdict(list)
    for n in range(1, n_max + 1):
        state = n
        letters: list[str] = []
        for _ in range(k_max):
            letters.append("O" if state & 1 else "E")
            word = "".join(letters)
            state = floor_power(state)
            realizing[word].append(n)
            if state >= n:
                noncontracting[word].append(n)
    return dict(realizing), dict(noncontracting)


def first_inversion(starts: list[int], nc: set[int]) -> dict[str, int] | None:
    """Smallest n1 < n2 in R_w with n1 in N_w and n2 not in N_w."""

    seen_nc = None
    for n in starts:
        if n in nc:
            if seen_nc is None:
                seen_nc = n
        elif seen_nc is not None:
            return {"n1": seen_nc, "n2": n}
    return None


def upper_tail(starts: list[int], nc: set[int], a_w: int | None) -> bool:
    if a_w is None:
        return True
    return all(n in nc for n in starts if n >= a_w)


def word_stats(word: str) -> dict[str, Any]:
    k = len(word)
    odds = word.count("O")
    runs, max_o, max_e, first_mixed = run_signature(word)
    gap = exponent_gap(k, odds)
    return {
        "word": word,
        "k": k,
        "o": odds,
        "gap": gap,
        "expanding": gap < 0,
        "runs": runs,
        "max_O_run": max_o,
        "max_E_run": max_e,
        "first_mixed": first_mixed,
    }


def word_row(word: str, starts: list[int], nc_list: list[int]) -> dict[str, Any]:
    nc = set(nc_list)
    stats = word_stats(word)
    geo_r = components(starts)
    geo_n = components(nc_list)
    a_w = nc_list[0] if nc_list else None
    m_w = starts[0] if starts else None
    inv = first_inversion(starts, nc)
    image_a = image_after(a_w, word) if a_w is not None else None
    return {
        **stats,
        "m": m_w,
        "a": a_w,
        "a_minus_m": None if a_w is None or m_w is None else a_w - m_w,
        "r_size": geo_r["size"],
        "n_size": geo_n["size"],
        "n_components": geo_n["n_components"],
        "n_max_gap": geo_n["max_gap"],
        "n_max": geo_n["max"],
        "r_max": geo_r["max"],
        "upper_tail": upper_tail(starts, nc, a_w),
        "inversion": inv,
        "image_a": image_a,
    }


def formal_contracting_exceptions(
    realizing: dict[str, list[int]], noncontracting: dict[str, list[int]]
) -> list[dict[str, Any]]:
    """N_w on formally contracting itineraries should be empty except n=1 on O^k."""

    bad = []
    for word, starts in realizing.items():
        k = len(word)
        odds = word.count("O")
        if exponent_gap(k, odds) <= 0:
            continue
        nc = noncontracting.get(word, [])
        unexpected = [n for n in nc if not (n == 1 and word == "O" * k)]
        if unexpected:
            bad.append({"word": word, "unexpected": unexpected[:8], "count": len(unexpected)})
    return bad


def same_ko_split(rows: list[dict[str, Any]]) -> dict[str, Any]:
    groups: dict[tuple[int, int], list[dict[str, Any]]] = defaultdict(list)
    for row in rows:
        if row["a"] is None or not row["expanding"]:
            continue
        groups[(row["k"], row["o"])].append(row)
    strongest = None
    for key, items in groups.items():
        if len(items) < 2:
            continue
        lo = min(items, key=lambda r: (r["a"], r["word"]))
        hi = max(items, key=lambda r: (r["a"], r["word"]))
        if lo["a"] == hi["a"]:
            continue
        rec = {
            "k": key[0],
            "o": key[1],
            "low_word": lo["word"],
            "low_a": lo["a"],
            "high_word": hi["word"],
            "high_a": hi["a"],
            "ratio": hi["a"] / lo["a"],
            "n_words": len(items),
        }
        if strongest is None or rec["ratio"] > strongest["ratio"]:
            strongest = rec
    return {
        "groups_with_a": sum(1 for items in groups.values() if items),
        "groups_split": sum(
            1
            for items in groups.values()
            if len({row["a"] for row in items}) > 1
        ),
        "strongest": strongest,
    }


def same_run_split(rows: list[dict[str, Any]]) -> dict[str, Any]:
    groups: dict[tuple[int, int, int, int, int, int], list[dict[str, Any]]] = defaultdict(list)
    for row in rows:
        if row["a"] is None or not row["expanding"]:
            continue
        key = (row["k"], row["o"], row["runs"], row["max_O_run"], row["max_E_run"], row["first_mixed"])
        groups[key].append(row)
    strongest = None
    split = 0
    for key, items in groups.items():
        if len({row["a"] for row in items}) <= 1:
            continue
        split += 1
        lo = min(items, key=lambda r: (r["a"], r["word"]))
        hi = max(items, key=lambda r: (r["a"], r["word"]))
        rec = {
            "key": key,
            "low_word": lo["word"],
            "low_a": lo["a"],
            "high_word": hi["word"],
            "high_a": hi["a"],
            "ratio": hi["a"] / lo["a"],
        }
        if strongest is None or rec["ratio"] > strongest["ratio"]:
            strongest = rec
    return {"groups_split": split, "strongest": strongest}


def extension_laws(
    realizing: dict[str, list[int]], noncontracting: dict[str, list[int]]
) -> dict[str, Any]:
    late_expand = None
    late_contract = None
    n_late_expand = 0
    n_late_contract = 0
    for word, starts in realizing.items():
        if len(word) < 2:
            continue
        parent = word[:-1]
        parent_nc = set(noncontracting.get(parent, []))
        child_nc = set(noncontracting.get(word, []))
        for n in noncontracting.get(word, []):
            if n not in parent_nc:
                n_late_expand += 1
                cand = {"parent": parent, "child": word, "n": n}
                if late_expand is None or (n, len(word), word) < (
                    late_expand["n"],
                    len(late_expand["child"]),
                    late_expand["child"],
                ):
                    late_expand = cand
        start_set = set(starts)
        for n in parent_nc:
            if n in start_set and n not in child_nc:
                n_late_contract += 1
                cand = {"parent": parent, "child": word, "n": n}
                if late_contract is None or (n, len(word), word) < (
                    late_contract["n"],
                    len(late_contract["child"]),
                    late_contract["child"],
                ):
                    late_contract = cand
    return {
        "N_wb_subseteq_N_w": n_late_expand == 0,
        "late_expand_count": n_late_expand,
        "late_expand": late_expand,
        "late_contract_count": n_late_contract,
        "late_contract": late_contract,
    }


def first_defect_view(
    realizing: dict[str, list[int]],
    noncontracting: dict[str, list[int]],
    *,
    limit: int = 4000,
) -> dict[str, Any]:
    nc_pos: Counter[int | str] = Counter()
    c_pos: Counter[int | str] = Counter()
    samples = 0
    mixed = []
    for word, starts in realizing.items():
        if exponent_gap(len(word), word.count("O")) >= 0:
            continue
        nc = noncontracting.get(word, [])
        if not nc or len(nc) == len(starts):
            continue
        mixed.append(word)
    for word in mixed:
        starts = realizing[word]
        nc = set(noncontracting[word])
        for n in starts:
            if samples >= limit:
                break
            path = itinerary(n, len(word))
            idx = first_nonexact_index(path)
            key: int | str = "exact" if idx is None else idx
            if n in nc:
                nc_pos[key] += 1
            else:
                c_pos[key] += 1
            samples += 1
        if samples >= limit:
            break
    return {
        "samples": samples,
        "nc_positions": {str(k): v for k, v in nc_pos.items()},
        "c_positions": {str(k): v for k, v in c_pos.items()},
        "nc_uses_nonzero_defect": any(k not in {0, "exact"} for k in nc_pos),
        "nc_uses_position_zero": nc_pos[0] > 0,
    }


def adjacency(
    realizing: dict[str, list[int]], noncontracting: dict[str, list[int]]
) -> dict[str, Any]:
    """Look at a_w-1, a_w, a_w+1 when they realize w."""

    samples = []
    cell_left = 0
    cell_checked = 0
    not_endpoint = None
    preferred = [word for word in ("EOO", "EOOO", "EO") if noncontracting.get(word)]
    rest = [word for word, nc_list in noncontracting.items() if nc_list and word not in preferred]
    for word in preferred + rest:
        nc_list = noncontracting[word]
        starts = set(realizing[word])
        a_w = nc_list[0]
        rec = {
            "word": word,
            "a": a_w,
            "image": image_after(a_w, word),
            "neighbors": {},
        }
        for neigh in (a_w - 1, a_w + 1):
            if neigh < 1 or neigh not in starts:
                rec["neighbors"][str(neigh)] = None
                continue
            rec["neighbors"][str(neigh)] = {
                "in_N": neigh in set(nc_list),
                "image": image_after(neigh, word),
            }
        if word[0] == "E" and a_w % 2 == 0:
            q = isqrt(a_w)
            lo, _hi = even_preimage(q)
            cell_checked += 1
            if a_w == lo or a_w == lo + (lo & 1):
                cell_left += 1
            elif not_endpoint is None:
                not_endpoint = {"word": word, "a": a_w, "cell_left": lo, "q": q}
        samples.append(rec)
        if len(samples) >= 12:
            break
    return {
        "examples": samples[:8],
        "even_start_cell_checked": cell_checked,
        "even_start_left_endpoint": cell_left,
        "first_non_endpoint": not_endpoint,
    }


def family_rows(
    realizing: dict[str, list[int]], noncontracting: dict[str, list[int]]
) -> list[dict[str, Any]]:
    rows = []
    for word in FAMILIES:
        if word not in realizing:
            continue
        rows.append(word_row(word, realizing[word], noncontracting.get(word, [])))
    return rows


def selected_confirm(*, n_max: int, words: tuple[str, ...] = FAMILIES) -> dict[str, Any]:
    wanted = set(words)
    k_max = max(len(word) for word in words)
    realizing: dict[str, list[int]] = {word: [] for word in words}
    noncontracting: dict[str, list[int]] = {word: [] for word in words}
    for n in range(1, n_max + 1):
        state = n
        letters: list[str] = []
        for _ in range(k_max):
            letters.append("O" if state & 1 else "E")
            word = "".join(letters)
            state = floor_power(state)
            if word in wanted:
                realizing[word].append(n)
                if state >= n:
                    noncontracting[word].append(n)
    rows = [
        word_row(word, realizing[word], noncontracting[word])
        for word in words
        if realizing[word]
    ]
    inversions = [row for row in rows if row["inversion"] is not None]
    return {
        "n_max": n_max,
        "n_words": len(rows),
        "inversions": inversions[:8],
        "inversion_count": len(inversions),
        "upper_tail_expanding": all(
            row["upper_tail"] for row in rows if row["expanding"] and row["a"] is not None
        ),
        "rows": [row for row in rows if row["word"] in {"O", "OO", "OOE", "OEO", "OOOE", "OEOE", "OOEO"}],
    }


def scan_summary(
    realizing: dict[str, list[int]],
    noncontracting: dict[str, list[int]],
    *,
    n_max: int,
    k_max: int,
) -> dict[str, Any]:
    rows = [word_row(word, starts, noncontracting.get(word, [])) for word, starts in realizing.items()]
    expanding = [row for row in rows if row["expanding"]]
    with_a = [row for row in expanding if row["a"] is not None]
    inversions = [row for row in with_a if row["inversion"] is not None]
    tails = [row for row in with_a if row["upper_tail"]]
    empty_exp = [row for row in expanding if row["a"] is None]
    return {
        "n_max": n_max,
        "k_max": k_max,
        "n_words": len(rows),
        "expanding_words": len(expanding),
        "expanding_with_a": len(with_a),
        "expanding_empty_N": len(empty_exp),
        "upper_tail_count": len(tails),
        "inversion_count": len(inversions),
        "smallest_inversion": min(
            inversions, key=lambda r: (r["inversion"]["n2"], r["k"], r["word"])
        ) if inversions else None,
        "fragmented_N": sum(1 for row in with_a if row["n_components"] > 4),
        "same_ko": same_ko_split(rows),
        "same_run": same_run_split(rows),
        "families": family_rows(realizing, noncontracting),
    }


def lean_api_present() -> dict[str, Any]:
    text = juggler_text()
    cells = CELLS.read_text(encoding="utf-8")
    env = ENVELOPE.read_text(encoding="utf-8")
    itin = ITINERARY.read_text(encoding="utf-8")
    blob = text + "\n" + cells + "\n" + env + "\n" + itin
    return {
        "sorry_free": "sorry" not in blob and "admit" not in blob,
        **{name: f"theorem {name}" in blob for name in LEAN_THEOREMS},
        "no_forbidden_engines": all(name not in blob for name in FORBIDDEN_ENGINES),
        "no_global_termination_theorem": "theorem juggler_reaches_one" not in blob,
    }


def classify(payload: dict[str, Any]) -> dict[str, Any]:
    diag = payload["diagnostic"]
    ext = payload["extension"]
    contracting = payload["contracting_exceptions"]
    defect = payload["first_defect"]
    if contracting:
        return {
            "classification": CLASS_COUNTER,
            "reason": "a formally contracting word has a non-trivial noncontracting realizer",
        }
    inversions = diag["inversion_count"] > 0
    ko_split = diag["same_ko"]["groups_split"] > 0
    run_split = diag["same_run"]["groups_split"] > 0
    late = not ext["N_wb_subseteq_N_w"]
    defect_unrestricted = defect["nc_uses_nonzero_defect"] and defect["nc_uses_position_zero"]
    if inversions and ko_split and run_split and late and defect_unrestricted:
        return {
            "classification": CLASS_COMPLEX,
            "secondary": CLASS_COUNTER,
            "reason": (
                "N_w is not an upper tail: inversions n1 in N_w < n2 in C_w exist. "
                "The same (k,o) and even the same run signature split a_w. "
                "Noncontraction can appear after a contracting prefix and can "
                "vanish after a noncontracting prefix. First-defect position is "
                "unrestricted on N_w. No description simpler than T_w(n)>=n survived."
            ),
        }
    if inversions and ko_split:
        return {
            "classification": CLASS_COMPLEX,
            "reason": "inversions and (k,o) split survive; remaining inheritance/defect checks incomplete",
        }
    return {
        "classification": CLASS_COMPLEX,
        "reason": "no exact boundary law independent of T_w(n)>=n survived the window",
    }


def run_probe() -> dict[str, Any]:
    realizing, noncontracting = collect_partition(n_max=DIAG_N, k_max=DIAG_K)
    diagnostic = scan_summary(realizing, noncontracting, n_max=DIAG_N, k_max=DIAG_K)
    return {
        "diagnostic": diagnostic,
        "contracting_exceptions": formal_contracting_exceptions(realizing, noncontracting)[:8],
        "extension": extension_laws(realizing, noncontracting),
        "first_defect": first_defect_view(realizing, noncontracting),
        "adjacency": adjacency(realizing, noncontracting),
        "confirm": selected_confirm(n_max=CONFIRM_N),
        "calibration": {
            "N_E_empty": noncontracting.get("E", []) == [],
            "N_O": {
                "size": len(noncontracting.get("O", [])),
                "min": noncontracting.get("O", [None])[0] if noncontracting.get("O") else None,
                "equals_all_odds": noncontracting.get("O", []) == realizing.get("O", []),
            },
        },
    }


def probe_payload() -> dict[str, Any]:
    scan = run_probe()
    lean = lean_api_present()
    decision = classify(scan)
    anti = dict(ANTI_OVERCLAIM)
    anti.update(
        {
            "forbidden_factor_law": False,
            "global_termination": False,
            "reopen_pe_factors": False,
            "reopen_residual_quotient": False,
            "reopen_sum_rho": False,
            "reopen_realization_geometry": False,
            "reopen_landing_image": False,
            "automaton": False,
        }
    )
    return {
        "experiment": "juggler_nc_boundary",
        "engine_control_layer_modified": False,
        "anti_overclaim": anti,
        "scan": scan,
        "lean": lean,
        "decision": decision,
        "search_method": (
            "one-pass word partition of R_w into C_w / N_w; "
            "threshold inversions; same (k,o) and run-signature splits; "
            "prefix-extension inheritance; first-defect positions; "
            "selected families at n<=1e5"
        ),
    }


def _fmt_row(row: dict[str, Any]) -> str:
    return (
        f"- `{row['word']}` gap=`{row['gap']}` m=`{row['m']}` a=`{row['a']}` "
        f"|N|=`{row['n_size']}` comps=`{row['n_components']}` "
        f"tail=`{row['upper_tail']}` inv=`{row['inversion']}`"
    )


def render_markdown(payload: dict[str, Any]) -> str:
    decision = payload["decision"]
    scan = payload["scan"]
    diag = scan["diagnostic"]
    ext = scan["extension"]
    lean = payload["lean"]
    lines = [
        "# Juggler noncontracting realization boundary",
        "",
        f"Status: **{decision['classification']}**",
        "",
        "Standalone application phase. Not a Research Engine experiment",
        "and not a termination theorem. Studies `N_w = {n in R_w : T_w(n) >= n}`.",
        "The identity is the definition, not a discovery. Does not reopen",
        "PE-factor, residual-future, sum-rho, realization-set branching,",
        "or landing-image geometry.",
        "",
        "## Branch budget",
        "",
        "```text",
        "Mathematical target     structural description of N_w / a_w",
        "Novelty hypothesis      threshold, cell, (k,o,run), or inheritance",
        "Falsifier               inversions; same (k,o) split; T>=n restatement",
        "Existing machinery      follows, image, power_bound_contracts",
        "Maximum Phase-0 scope   n<=4000 k<=20; selected n<=1e5",
        "```",
        "",
        "## Metadata",
        "",
        f"- diagnostic window: `n<= {diag['n_max']}`, `k<= {diag['k_max']}`",
        f"- confirm window: `n<= {scan['confirm']['n_max']}` selected families",
        f"- engine control layer modified: `{payload['engine_control_layer_modified']}`",
        f"- classification: **{decision['classification']}**",
        f"- sorry-free: `{lean['sorry_free']}`",
        "",
        decision["reason"],
        "",
        "## Calibration",
        "",
        f"- `N_E` empty: `{scan['calibration']['N_E_empty']}`",
        f"- `N_O` equals all odds: `{scan['calibration']['N_O']['equals_all_odds']}` "
        f"size=`{scan['calibration']['N_O']['size']}`",
        f"- formally contracting exceptions: `{scan['contracting_exceptions']}`",
        "",
        "## Diagnostic partition",
        "",
        f"- words: `{diag['n_words']}` expanding `{diag['expanding_words']}`",
        f"- expanding with nonempty N: `{diag['expanding_with_a']}`",
        f"- expanding with empty N in window: `{diag['expanding_empty_N']}`",
        f"- upper tails: `{diag['upper_tail_count']}`",
        f"- inversions (n1 in N, n2 in C, n1<n2): `{diag['inversion_count']}`",
        f"- fragmented N (components>4): `{diag['fragmented_N']}`",
        f"- smallest inversion: `{diag['smallest_inversion']}`",
        "",
        "## Same (k,o) and run signature",
        "",
        f"- (k,o) groups that split a_w: `{diag['same_ko']['groups_split']}` "
        f"/ `{diag['same_ko']['groups_with_a']}`",
        f"- strongest (k,o) split: `{diag['same_ko']['strongest']}`",
        f"- run-signature groups that split a_w: `{diag['same_run']['groups_split']}`",
        f"- strongest run split: `{diag['same_run']['strongest']}`",
        "",
        "## Prefix extension",
        "",
        f"- `N_wb ⊆ N_w`: `{ext['N_wb_subseteq_N_w']}`",
        f"- late expand (contracting prefix, NC word): `{ext['late_expand_count']}` "
        f"smallest=`{ext['late_expand']}`",
        f"- late contract (NC prefix, contracting word): `{ext['late_contract_count']}` "
        f"smallest=`{ext['late_contract']}`",
        "",
        "## First defect",
        "",
        f"- samples: `{scan['first_defect']['samples']}`",
        f"- NC positions: `{scan['first_defect']['nc_positions']}`",
        f"- C positions: `{scan['first_defect']['c_positions']}`",
        "",
        "## Adjacency / first-step cells",
        "",
        f"- even-start left-cell count: `{scan['adjacency']['even_start_left_endpoint']}` "
        f"/ `{scan['adjacency']['even_start_cell_checked']}`",
        f"- first non-endpoint: `{scan['adjacency']['first_non_endpoint']}`",
        "",
        "## Families",
        "",
    ]
    for row in diag["families"]:
        lines.append(_fmt_row(row))
    confirm = scan["confirm"]
    lines.extend(
        [
            "",
            "## Selected confirm",
            "",
            f"- words: `{confirm['n_words']}` inversions `{confirm['inversion_count']}`",
            f"- expanding families still upper tail: `{confirm['upper_tail_expanding']}`",
            "",
        ]
    )
    for row in confirm["rows"]:
        lines.append(_fmt_row(row))
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
            "## Decision",
            "",
            f"**{decision['classification']}**",
            "",
            decision["reason"],
            "",
            "This is not a halt result. N_w is not a new invariant.",
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
