"""Realization-set geometry of the Juggler prefix trie.

Not a Research Engine control-layer experiment. Not a halt theorem.
Does not reopen PE-factor grammar or residual-future quotients.
Absence under a scan bound is never a forbidden-factor claim.
"""

from __future__ import annotations

import json
import statistics
from collections import Counter, defaultdict
from pathlib import Path
from typing import Any, Iterable

from research.juggler_sequence.atlas.packed import pack_word, split_word_id, unpack_word
from research.juggler_sequence.atlas.storage import DEFAULT_DATA_DIR, connect, sqlite_path
from research.juggler_sequence.compensated_contraction import follows_itinerary, image_after
from research.juggler_sequence.floor_preimages import even_preimage, odd_preimage_integers
from research.juggler_sequence.lean_paths import CELLS, COLLAPSE
from research.juggler_sequence.power_itineraries import ANTI_OVERCLAIM, floor_power

REPO_ROOT = Path(__file__).resolve().parents[3]
JSON_PATH = REPO_ROOT / "docs" / "research" / "juggler_realization_geometry.json"
DOC_PATH = REPO_ROOT / "docs" / "research" / "juggler_realization_geometry.md"
DATA_DIR = REPO_ROOT / "data" / "research" / "juggler" / "realization_geometry"

DIAG_N = 4000
DIAG_K = 12
CONFIRM_N = 100_000
CONFIRM_K = 12
SELECTED_N = 10_000_000
ATLAS_EID = "wa-20260827T200310Z-cuda-k20-n100000000"
ATLAS_N = 100_000_000

FIRST_UNARY = ("EEEEE", "EEEEO", "EEEOE")
FIRST_HOLES = ("EEEEEE", "EEEEOE", "EEEOEO")
ADVERSARIAL = (
    "E",
    "EE",
    "EEE",
    "EEEE",
    "EEEEE",
    "EO",
    "EOE",
    "EOO",
    "O",
    "OO",
    "OOO",
    "OE",
    "OEO",
    "OOE",
    "EEO",
    "OEEEE",
    "OOOOE",
)

CLASS_GREEN = "REALIZATION_GEOMETRY_GREEN"
CLASS_AMPLIFY = "REALIZER_AMPLIFICATION_GREEN"
CLASS_CELL = "CELL_GEOMETRY_GREEN"
CLASS_CORRIDOR = "CORRIDOR_GREEN"
CLASS_ROOT = "ROOT_FACTOR_GREEN"
CLASS_COUNTER = "REALIZATION_COUNTEREXAMPLE"
CLASS_COMPLEX = "REALIZATION_GEOMETRY_COMPLEX"

FORBIDDEN_ENGINES = (
    "ResidualGraph",
    "ResidualState",
    "MilestoneGraph",
    "PowerHeight",
    "CycleEngine",
)

LEAN_THEOREMS = (
    "even_tower_to_one",
    "even_preimage_iff",
    "odd_preimage_iff",
    "odd_preimage_unique",
)


def even_tower(r: int) -> int:
    if r < 1:
        raise ValueError("even_tower requires r >= 1")
    return 2 ** (1 << (r - 1))


def leading_run(word: str, letter: str) -> int:
    n = 0
    for ch in word:
        if ch != letter:
            break
        n += 1
    return n


def interval_label(geo: dict[str, Any]) -> str:
    if geo["size"] == 0:
        return "EMPTY"
    if geo["n_components"] == 1:
        return "SINGLE_INTERVAL"
    largest_frac = geo["largest_frac"] or 0.0
    if geo["n_components"] <= 4 or largest_frac >= 0.8:
        return "FEW_INTERVALS"
    return "FRAGMENTED"


def prepend_E(starts: list[int], n_max: int) -> list[int]:
    """R_{Ew}(N) from R_w via even inverse-floor cells, clipped to N."""

    out: list[int] = []
    for q in starts:
        lo, hi = even_preimage(q)
        if lo > n_max:
            continue
        start = lo + (lo & 1)
        if start < 2:
            start = 2
        out.extend(range(start, min(hi, n_max + 1), 2))
    return out


def prepend_O(starts: list[int], n_max: int) -> list[int]:
    """R_{Ow}(N) predicted from R_w(N) via odd cells. Landings > N are lost."""

    out: list[int] = []
    for q in starts:
        for n in odd_preimage_integers(q):
            if n % 2 == 1 and 1 <= n <= n_max:
                out.append(n)
    out.sort()
    return out


def corridor_recurrence(
    realizing: dict[str, list[int]], *, n_max: int, k_max: int
) -> dict[str, Any]:
    empty = list(range(1, n_max + 1))
    pred_e = prepend_E(empty, n_max)
    pred_o = prepend_O(empty, n_max)
    actual_e = realizing.get("E", [])
    actual_o = realizing.get("O", [])
    tower_ok = True
    for r in range(1, min(5, k_max)):
        parent = "E" * r
        child = parent + "E"
        if parent not in realizing:
            continue
        if prepend_E(realizing[parent], n_max) != realizing.get(child, []):
            tower_ok = False
            break
    mismatches_e = 0
    mismatches_o = 0
    checked = 0
    first_e = None
    first_o = None
    for word, starts in realizing.items():
        if len(word) >= k_max:
            continue
        checked += 1
        pred = prepend_E(starts, n_max)
        actual = realizing.get("E" + word, [])
        if pred != actual:
            mismatches_e += 1
            if first_e is None:
                first_e = {"word": word, "predicted": len(pred), "actual": len(actual)}
        pred = prepend_O(starts, n_max)
        actual = realizing.get("O" + word, [])
        if pred != actual:
            mismatches_o += 1
            if first_o is None:
                first_o = {
                    "word": word,
                    "predicted": len(pred),
                    "actual": len(actual),
                    "missing": len(actual) - len(pred),
                }
    return {
        "empty_prepend_E_exact": pred_e == actual_e,
        "empty_prepend_O_exact": pred_o == actual_o,
        "empty_prepend_O_predicted": len(pred_o),
        "empty_prepend_O_actual": len(actual_o),
        "empty_prepend_O_leak": len(actual_o) - len(pred_o),
        "even_tower_prepend_exact": tower_ok,
        "checked_prefixes": checked,
        "prepend_E_mismatches": mismatches_e,
        "prepend_O_mismatches": mismatches_o,
        "first_prepend_E_mismatch": first_e,
        "first_prepend_O_mismatch": first_o,
        "append_rule": "R_{wb} = {n in R_w : T_w(n) has parity b}",
        "prepend_E_rule": "R_{Ew}(N) = union_{q in R_w(N)} (even_preimage(q) ∩ 2Z ∩ [1,N])",
        "prepend_O_rule": "R_{Ow} = union_{q in R_w} (odd_cell(q) ∩ (2Z+1)); not closed on [1,N]",
    }


def selected_root_scan(
    *, n_max: int = SELECTED_N, words: tuple[str, ...] = FIRST_HOLES + FIRST_UNARY
) -> dict[str, Any]:
    """Exact root membership for a few words, no full trie."""

    k_max = max(len(word) for word in words)
    wanted = set(words)
    stats = {word: {"size": 0, "min": None, "max": None} for word in words}
    for n in range(1, n_max + 1):
        state = n
        letters: list[str] = []
        for _ in range(k_max):
            letters.append("O" if state & 1 else "E")
            word = "".join(letters)
            if word in wanted:
                rec = stats[word]
                rec["size"] += 1
                if rec["min"] is None:
                    rec["min"] = n
                rec["max"] = n
            state = floor_power(state)
    return {"n_max": n_max, "words": stats}


def degree_label(mask: int) -> str:
    has_o = bool(mask & 1)
    has_e = bool(mask & 2)
    if has_o and has_e:
        return "BINARY"
    if has_o:
        return "UNARY_O"
    if has_e:
        return "UNARY_E"
    return "DEAD"


def collect_realizing(*, n_max: int, k_max: int) -> dict[str, list[int]]:
    """One-pass nested realizing sets. Sorted lists, no extra index."""

    realizing: dict[str, list[int]] = defaultdict(list)
    for n in range(1, n_max + 1):
        state = n
        letters: list[str] = []
        for _ in range(k_max):
            letters.append("O" if state & 1 else "E")
            realizing["".join(letters)].append(n)
            state = floor_power(state)
    return dict(realizing)


def gap_geometry(xs: list[int], *, n_max: int) -> dict[str, Any]:
    if not xs:
        return {
            "size": 0,
            "min": None,
            "max": None,
            "span": None,
            "density": 0.0,
            "n_gaps": 0,
            "mean_gap": None,
            "median_gap": None,
            "max_gap": None,
            "n_components": 0,
            "largest_component": 0,
            "largest_frac": None,
        }
    gaps = [xs[i + 1] - xs[i] for i in range(len(xs) - 1)]
    interior = [g for g in gaps if g > 1]
    components = 1
    largest = 1
    run = 1
    for g in gaps:
        if g == 1:
            run += 1
            if run > largest:
                largest = run
        else:
            components += 1
            run = 1
    return {
        "size": len(xs),
        "min": xs[0],
        "max": xs[-1],
        "span": xs[-1] - xs[0],
        "density": len(xs) / n_max,
        "n_gaps": len(interior),
        "mean_gap": statistics.fmean(gaps) if gaps else None,
        "median_gap": statistics.median(gaps) if gaps else None,
        "max_gap": max(gaps) if gaps else None,
        "n_components": components,
        "largest_component": largest,
        "largest_frac": largest / len(xs),
    }


def child_sets(
    word: str, starts: list[int]
) -> tuple[list[int], list[int], list[int]]:
    child_o: list[int] = []
    child_e: list[int] = []
    uncovered: list[int] = []
    for n in starts:
        landing = image_after(n, word)
        if landing & 1:
            child_o.append(n)
        else:
            child_e.append(n)
    return child_o, child_e, uncovered


def landing_stats(word: str, starts: list[int]) -> dict[str, Any]:
    parities = Counter()
    values: list[int] = []
    for n in starts:
        landing = image_after(n, word)
        values.append(landing)
        parities[landing & 1] += 1
    unique = sorted(set(values))
    return {
        "n_unique_landings": len(unique),
        "landing_min": unique[0] if unique else None,
        "landing_max": unique[-1] if unique else None,
        "odd_landings": parities[1],
        "even_landings": parities[0],
        "monochrome": len(parities) == 1,
        "singleton_landing": len(unique) == 1,
    }


def prefix_row(word: str, starts: list[int], *, n_max: int) -> dict[str, Any]:
    child_o, child_e, uncovered = child_sets(word, starts)
    mask = (1 if child_o else 0) | (2 if child_e else 0)
    geo = gap_geometry(starts, n_max=n_max)
    land = landing_stats(word, starts)
    scale_sep = None
    if child_o and child_e:
        scale_sep = child_o[-1] < child_e[0] or child_e[-1] < child_o[0]
    return {
        "word": word,
        "length": len(word),
        "lead_E": leading_run(word, "E"),
        "lead_O": leading_run(word, "O"),
        "odd_count": word.count("O"),
        "class": degree_label(mask),
        "mask": mask,
        "rho_O": len(child_o) / len(starts) if starts else None,
        "rho_E": len(child_e) / len(starts) if starts else None,
        "uncovered": len(uncovered),
        "child_O": len(child_o),
        "child_E": len(child_e),
        "child_O_min": child_o[0] if child_o else None,
        "child_E_min": child_e[0] if child_e else None,
        "child_O_max": child_o[-1] if child_o else None,
        "child_E_max": child_e[-1] if child_e else None,
        "scale_separated": scale_sep,
        "interval_class": interval_label(geo),
        **geo,
        **land,
    }


def window_census(realizing: dict[str, list[int]], *, n_max: int, k_max: int) -> dict[str, Any]:
    rows = [prefix_row(word, starts, n_max=n_max) for word, starts in realizing.items()]
    by_len: dict[int, Counter[str]] = defaultdict(Counter)
    uncovered_total = 0
    unary_monochrome = 0
    unary_total = 0
    binary_separated = 0
    binary_total = 0
    unary_singleton = 0
    regain = []
    for row in rows:
        by_len[row["length"]][row["class"]] += 1
        uncovered_total += row["uncovered"]
        if row["class"] in {"UNARY_O", "UNARY_E"}:
            unary_total += 1
            if row["monochrome"]:
                unary_monochrome += 1
            if row["singleton_landing"]:
                unary_singleton += 1
        if row["class"] == "BINARY":
            binary_total += 1
            if row["scale_separated"]:
                binary_separated += 1
    for row in rows:
        if row["class"] not in {"UNARY_O", "UNARY_E"} or row["length"] >= k_max:
            continue
        child = row["word"] + ("O" if row["class"] == "UNARY_O" else "E")
        child_row = next((r for r in rows if r["word"] == child), None)
        if child_row and child_row["class"] == "BINARY":
            regain.append({"parent": row["word"], "child": child, "min": row["min"]})
    lead_e_unary = Counter()
    lead_e_n = Counter()
    interval_by_degree: dict[str, Counter[str]] = defaultdict(Counter)
    for row in rows:
        interval_by_degree[row["class"]][row["interval_class"]] += 1
        if row["length"] != k_max - 1:
            continue
        lead_e_n[row["lead_E"]] += 1
        if row["class"] in {"UNARY_O", "UNARY_E"}:
            lead_e_unary[row["lead_E"]] += 1
    return {
        "n_max": n_max,
        "k_max": k_max,
        "n_words": len(rows),
        "uncovered_total": uncovered_total,
        "unary_total": unary_total,
        "unary_monochrome": unary_monochrome,
        "unary_singleton_landing": unary_singleton,
        "binary_total": binary_total,
        "binary_scale_separated": binary_separated,
        "unary_to_binary": regain[:20],
        "unary_to_binary_count": len(regain),
        "profile": {str(k): dict(by_len[k]) for k in sorted(by_len)},
        "interval_by_degree": {key: dict(val) for key, val in interval_by_degree.items()},
        "lead_E_unary_frac_at_horizon": {
            str(lead): (lead_e_unary[lead] / lead_e_n[lead] if lead_e_n[lead] else None)
            for lead in sorted(lead_e_n)
        },
        "adversarial": [prefix_row(w, realizing[w], n_max=n_max) for w in ADVERSARIAL if w in realizing],
        "first_unary_in_window": [
            prefix_row(w, realizing[w], n_max=n_max) for w in FIRST_UNARY if w in realizing
        ],
    }


def atlas_available(data_dir: Path = DEFAULT_DATA_DIR) -> bool:
    return sqlite_path(data_dir).is_file()


def reproduce_atlas(*, data_dir: Path = DEFAULT_DATA_DIR, experiment_id: str = ATLAS_EID) -> dict[str, Any]:
    if not atlas_available(data_dir):
        return {"available": False}
    con = connect(data_dir)
    try:
        tower = []
        for r in range(1, 8):
            word = "E" * r
            length, packed = pack_word(word)
            row = con.execute(
                """
                SELECT min_realizer, realization_status
                FROM realizers
                WHERE experiment_id = ? AND word_id = ?
                """,
                (experiment_id, (length << 32) | packed),
            ).fetchone()
            tower.append(
                {
                    "r": r,
                    "word": word,
                    "min_realizer": None if row is None else row[0],
                    "status": None if row is None else row[1],
                    "tower": even_tower(r) if r <= 6 else None,
                }
            )
        unary_parents = []
        for word in FIRST_UNARY:
            length, packed = pack_word(word)
            mask = con.execute(
                """
                SELECT successor_mask, continuation_count
                FROM continuations
                WHERE experiment_id = ? AND word_id = ? AND language_id = 'REALIZABLE'
                """,
                (experiment_id, (length << 32) | packed),
            ).fetchone()
            real = con.execute(
                """
                SELECT min_realizer, realization_status
                FROM realizers
                WHERE experiment_id = ? AND word_id = ?
                """,
                (experiment_id, (length << 32) | packed),
            ).fetchone()
            unary_parents.append(
                {
                    "word": word,
                    "min_realizer": None if real is None else real[0],
                    "status": None if real is None else real[1],
                    "mask": None if mask is None else mask[0],
                    "class": None if mask is None else degree_label(mask[0]),
                }
            )
        holes = []
        for word in FIRST_HOLES:
            length, packed = pack_word(word)
            real = con.execute(
                """
                SELECT min_realizer, realization_status
                FROM realizers
                WHERE experiment_id = ? AND word_id = ?
                """,
                (experiment_id, (length << 32) | packed),
            ).fetchone()
            holes.append(
                {
                    "word": word,
                    "min_realizer": None if real is None else real[0],
                    "status": None if real is None else real[1],
                }
            )
        lead = defaultdict(lambda: [0, 0])
        rows = con.execute(
            """
            SELECT w.packed, w.length, c.continuation_count
            FROM continuations c
            JOIN words w ON w.word_id = c.word_id
            WHERE c.experiment_id = ? AND c.language_id = 'REALIZABLE' AND w.length = 19
            """,
            (experiment_id,),
        )
        for packed, length, d in rows:
            word = unpack_word(length, packed)
            lead_e = leading_run(word, "E")
            lead[lead_e][0] += 1
            if d == 1:
                lead[lead_e][1] += 1
        ee_frozen = 0
        ee_unary = 0
        for packed, length, d in con.execute(
            """
            SELECT w.packed, w.length, c.continuation_count
            FROM continuations c
            JOIN words w ON w.word_id = c.word_id
            WHERE c.experiment_id = ? AND c.language_id = 'REALIZABLE' AND w.length = 12
            """,
            (experiment_id,),
        ):
            word = unpack_word(length, packed)
            if word.startswith("EE"):
                ee_frozen += 1
                if d == 1:
                    ee_unary += 1
    finally:
        con.close()
    return {
        "available": True,
        "experiment_id": experiment_id,
        "tower": tower,
        "first_unary": unary_parents,
        "first_holes": holes,
        "ee_prefix_length_12": {"count": ee_frozen, "unary": ee_unary},
        "lead_E_unary_length_19": {
            str(k): {"nodes": v[0], "unary": v[1], "frac": v[1] / v[0] if v[0] else None}
            for k, v in sorted(lead.items())
        },
    }


def classify_missing_child(
    parent: str,
    lost: str,
    *,
    interior: dict[str, Any] | None = None,
    atlas_n: int = ATLAS_N,
) -> dict[str, Any]:
    child = parent + lost
    if child == "EEEEEE":
        return {
            "parent": parent,
            "lost": lost,
            "child": child,
            "status": "SCALE_LIMITED",
            "certificate_type": "EVEN_TOWER",
            "min_root": even_tower(6),
            "reason": f"m(E^6)=even_tower(6)={even_tower(6)} > atlas n_max={atlas_n}",
        }
    rec = None
    if interior and interior.get("words"):
        rec = interior["words"].get(child)
    if rec and rec.get("min_state") is not None:
        y = rec["min_state"]
        if rec.get("states_within_atlas"):
            return {
                "parent": parent,
                "lost": lost,
                "child": child,
                "status": "SEARCH_INCONSISTENT",
                "certificate_type": "INTERIOR_STATE",
                "min_interior_state": y,
                "reason": "an interior realizing state lies inside the atlas bound",
            }
        if y > atlas_n:
            return {
                "parent": parent,
                "lost": lost,
                "child": child,
                "status": "SCALE_LIMITED",
                "certificate_type": "INTERIOR_STATE",
                "min_interior_state": y,
                "reason": (
                    f"smallest interior realizing state {y} > atlas n_max={atlas_n}; "
                    "no rooted realizer in the scan"
                ),
            }
    return {
        "parent": parent,
        "lost": lost,
        "child": child,
        "status": "SEARCH_UNOBSERVED",
        "certificate_type": "ATLAS_ABSENCE",
        "reason": "absent as a rooted prefix under the atlas bound; no interior-state certificate",
    }


def interior_factors(
    *,
    words: Iterable[str] = FIRST_HOLES,
    data_dir: Path = DEFAULT_DATA_DIR,
    experiment_id: str = ATLAS_EID,
    length: int = 20,
    atlas_n: int = ATLAS_N,
) -> dict[str, Any]:
    if not atlas_available(data_dir):
        return {"available": False}
    packed_targets = {word: pack_word(word)[1] for word in words}
    lengths = {word: len(word) for word in words}
    con = connect(data_dir)
    try:
        rows = con.execute(
            """
            SELECT w.packed, r.min_realizer
            FROM realizers r JOIN words w ON w.word_id = r.word_id
            WHERE r.experiment_id = ? AND r.realization_status = 'FOUND' AND w.length = ?
            """,
            (experiment_id, length),
        ).fetchall()
    finally:
        con.close()
    best: dict[str, dict[str, Any]] = {
        word: {
            "count": 0,
            "min_position": None,
            "min_state": None,
            "states_within_atlas": 0,
            "example": None,
        }
        for word in words
    }
    for packed, min_n in rows:
        packed_i = int(packed)
        start = int(min_n)
        seen_host = {word: False for word in words}
        state = start
        for pos in range(0, length):
            for word, fp in packed_targets.items():
                fac_len = lengths[word]
                if pos + fac_len > length:
                    continue
                if ((packed_i >> pos) & ((1 << fac_len) - 1)) != fp:
                    continue
                rec = best[word]
                if not seen_host[word]:
                    rec["count"] += 1
                    seen_host[word] = True
                if state <= atlas_n:
                    rec["states_within_atlas"] += 1
                if rec["min_position"] is None or pos < rec["min_position"]:
                    rec["min_position"] = pos
                if rec["min_state"] is None or state < rec["min_state"]:
                    rec["min_state"] = state
                    rec["example"] = {
                        "position": pos,
                        "n": start,
                        "state": state,
                        "host": unpack_word(length, packed_i),
                        "follows": follows_itinerary(state, word),
                    }
            if pos + 1 < length:
                state = floor_power(state)
    for rec in best.values():
        rec["min_root_status"] = "NOT_FOUND_WITHIN_BOUND"
    return {"available": True, "length": length, "atlas_n": atlas_n, "words": best}


def amplification_laws(realizing: dict[str, list[int]]) -> dict[str, Any]:
    """Test m(wE) >= m(w)^2 and the even-landing identity m(wE)=m(w)."""

    square_cex = None
    odd_landing_square_cex = None
    even_landing_identity_fail = None
    tower_ok = True
    for r in range(1, 5):
        parent = "E" * r
        child = parent + "E"
        if parent not in realizing or child not in realizing:
            continue
        if realizing[child][0] != realizing[parent][0] ** 2:
            tower_ok = False
    samples = 0

    def _better(current: dict[str, Any] | None, cand: dict[str, Any]) -> dict[str, Any]:
        if current is None:
            return cand
        key = (cand["m_w"], len(cand["word"]), cand["word"])
        old = (current["m_w"], len(current["word"]), current["word"])
        return cand if key < old else current

    for word, starts in realizing.items():
        if not starts:
            continue
        child = word + "E"
        if child not in realizing:
            continue
        m_w = starts[0]
        m_we = realizing[child][0]
        landing = image_after(m_w, word)
        samples += 1
        rec = {"word": word, "m_w": m_w, "m_wE": m_we, "landing": landing}
        if landing % 2 == 0 and m_we != m_w:
            even_landing_identity_fail = _better(even_landing_identity_fail, rec)
        if m_we < m_w * m_w:
            square_cex = _better(square_cex, rec)
        if landing % 2 == 1 and m_we < m_w * m_w:
            odd_landing_square_cex = _better(odd_landing_square_cex, rec)
    return {
        "samples": samples,
        "tower_identity_in_window": tower_ok,
        "square_law_counterexample": square_cex,
        "odd_landing_square_counterexample": odd_landing_square_cex,
        "even_landing_identity_fail": even_landing_identity_fail,
    }


def atlas_unary_return(
    *, data_dir: Path = DEFAULT_DATA_DIR, experiment_id: str = ATLAS_EID
) -> dict[str, Any]:
    if not atlas_available(data_dir):
        return {"available": False}
    con = connect(data_dir)
    try:
        rows = con.execute(
            """
            SELECT c.word_id, c.successor_mask, c.continuation_count
            FROM continuations c
            WHERE c.experiment_id = ? AND c.language_id = 'REALIZABLE'
            """,
            (experiment_id,),
        ).fetchall()
    finally:
        con.close()
    by_id = {int(wid): (int(mask), int(d)) for wid, mask, d in rows}
    returns = []
    ee_returns = []
    for wid, (mask, d) in by_id.items():
        if d != 1:
            continue
        length, packed = split_word_id(wid)
        if length >= 19:
            continue
        keep_o = bool(mask & 1)
        child_len, child_packed = length + 1, packed | ((1 if keep_o else 0) << length)
        child_id = (child_len << 32) | child_packed
        child = by_id.get(child_id)
        if child is None or child[1] != 2:
            continue
        word = unpack_word(length, packed)
        rec = {"parent": word, "child": unpack_word(child_len, child_packed)}
        returns.append(rec)
        if word.startswith("EE"):
            ee_returns.append(rec)
    return {
        "available": True,
        "unary_to_binary_examples": returns[:20],
        "unary_to_binary_count": len(returns),
        "ee_unary_to_binary": ee_returns[:10],
        "ee_unary_to_binary_count": len(ee_returns),
    }


def next_step_cells(m: int) -> dict[str, Any]:
    lo, hi = even_preimage(m)
    evens = [n for n in range(lo, hi) if n % 2 == 0]
    odds = [n for n in odd_preimage_integers(m) if n % 2 == 1]
    return {"even_parents": evens[:8], "n_even_parents": len(evens), "odd_parents": odds}


def lean_api_present() -> dict[str, Any]:
    text = COLLAPSE.read_text(encoding="utf-8") + "\n" + CELLS.read_text(encoding="utf-8")
    return {
        "sorry_free": "sorry" not in text and "admit" not in text,
        **{
            name: (f"theorem {name}" in text or f"def {name}" in text)
            for name in LEAN_THEOREMS
        },
        "no_forbidden_engines": all(name not in text for name in FORBIDDEN_ENGINES),
        "no_global_termination_theorem": "theorem juggler_reaches_one" not in text,
    }


def classify(payload: dict[str, Any]) -> dict[str, Any]:
    diag = payload["diagnostic"]
    amp = payload["amplification"]
    atlas = payload["atlas"]
    interior = payload["interior"]
    corridor = payload["corridor"]
    missing = payload["missing_children"]
    if diag["uncovered_total"] != 0:
        return {
            "classification": CLASS_COUNTER,
            "reason": "child split left uncovered realizers; landing-parity semantics failed",
        }
    if atlas.get("available") and not all(
        row["status"] == "NOT_FOUND_WITHIN_BOUND" for row in atlas["first_holes"]
    ):
        return {
            "classification": CLASS_COUNTER,
            "reason": "a first hole was FOUND as a rooted prefix under the atlas bound",
        }
    if any(row["status"] == "SEARCH_INCONSISTENT" for row in missing):
        return {
            "classification": CLASS_COUNTER,
            "reason": "an interior realizing state of a first hole lies inside the atlas bound",
        }
    square_fails = amp["square_law_counterexample"] is not None
    odd_square_fails = amp["odd_landing_square_counterexample"] is not None
    landing_is_degree = (
        diag["unary_total"] > 0 and diag["unary_monochrome"] == diag["unary_total"]
    )
    prepend_e_exact = (
        corridor["empty_prepend_E_exact"]
        and corridor["even_tower_prepend_exact"]
        and corridor["prepend_E_mismatches"] == 0
    )
    prepend_o_leaks = (
        not corridor["empty_prepend_O_exact"] and corridor["prepend_O_mismatches"] > 0
    )
    holes_scale = all(row["status"] == "SCALE_LIMITED" for row in missing)
    interior_ok = interior.get("available") and all(
        rec["count"] > 0
        and rec["min_position"]
        and rec["min_position"] >= 1
        and rec["min_state"] is not None
        and rec["min_state"] > ATLAS_N
        and rec.get("example", {}).get("follows")
        for rec in interior["words"].values()
    )
    if (
        landing_is_degree
        and prepend_e_exact
        and prepend_o_leaks
        and holes_scale
        and interior_ok
        and square_fails
        and odd_square_fails
    ):
        return {
            "classification": CLASS_COMPLEX,
            "secondary": CLASS_COUNTER,
            "reason": (
                "Appending a letter is the landing-parity filter of T_w(R_w), which "
                "is the definition of follows. Prepending E is the even-cell union "
                "already in even_preimage_iff; it is exact on every finite window. "
                "Prepending O leaks the window because odd landings escape [1,N]. "
                "Naive m(wE)>=m(w)^2 fails after an odd letter (OOOE at 3; OEEE "
                "7->41). The first holes are SCALE_LIMITED, not CELL_EMPTY. No "
                "new set geometry beyond follows plus inverse-floor cells survived."
            ),
        }
    if landing_is_degree:
        return {
            "classification": CLASS_CELL,
            "reason": "unary iff landing parity is monochrome; cell/root certificates incomplete",
        }
    return {
        "classification": CLASS_COMPLEX,
        "reason": "no stable geometric rule beyond scan-bound counts",
    }


def run_probe() -> dict[str, Any]:
    realizing = collect_realizing(n_max=DIAG_N, k_max=DIAG_K)
    diagnostic = window_census(realizing, n_max=DIAG_N, k_max=DIAG_K)
    confirm_realizing = collect_realizing(n_max=CONFIRM_N, k_max=CONFIRM_K)
    confirm = window_census(confirm_realizing, n_max=CONFIRM_N, k_max=CONFIRM_K)
    interior = interior_factors()
    eeee_diag = next((row for row in diagnostic["adversarial"] if row["word"] == "EEEE"), None)
    return {
        "diagnostic": diagnostic,
        "confirm": {
            "n_max": confirm["n_max"],
            "k_max": confirm["k_max"],
            "n_words": confirm["n_words"],
            "uncovered_total": confirm["uncovered_total"],
            "unary_total": confirm["unary_total"],
            "unary_monochrome": confirm["unary_monochrome"],
            "unary_singleton_landing": confirm["unary_singleton_landing"],
            "binary_scale_separated": confirm["binary_scale_separated"],
            "binary_total": confirm["binary_total"],
            "unary_to_binary_count": confirm["unary_to_binary_count"],
            "unary_to_binary": confirm["unary_to_binary"],
            "profile": confirm["profile"],
            "interval_by_degree": confirm["interval_by_degree"],
            "lead_E_unary_frac_at_horizon": confirm["lead_E_unary_frac_at_horizon"],
        },
        "corridor": corridor_recurrence(realizing, n_max=DIAG_N, k_max=DIAG_K),
        "amplification": amplification_laws(realizing),
        "atlas": reproduce_atlas(),
        "interior": interior,
        "missing_children": [
            classify_missing_child("EEEEE", "E", interior=interior),
            classify_missing_child("EEEEO", "E", interior=interior),
            classify_missing_child("EEEOE", "O", interior=interior),
        ],
        "selected_roots": selected_root_scan(),
        "window_artefact": {
            "word": "EEEE",
            "diagnostic_class": None if eeee_diag is None else eeee_diag["class"],
            "atlas_class": "BINARY",
            "reason": "n<=4000 cannot see m(EEEEE)=65536, so EEEE looks UNARY_O in the small window",
        },
        "atlas_unary_return": atlas_unary_return(),
        "next_step_cell_example": {
            "m=2": next_step_cells(2),
            "m=1": next_step_cells(1),
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
            "automaton": False,
        }
    )
    return {
        "experiment": "juggler_realization_geometry",
        "engine_control_layer_modified": False,
        "anti_overclaim": anti,
        "scan": scan,
        "lean": lean,
        "decision": decision,
        "search_method": (
            "nested R_w by one-pass word; append children by landing parity; "
            "prepend children by even_preimage / odd_cell; interior states of first holes; "
            "selected exact roots at n<=1e7"
        ),
    }


def _fmt_row(row: dict[str, Any]) -> str:
    return (
        f"- `{row['word']}` class=`{row['class']}` |R|=`{row['size']}` "
        f"min=`{row['min']}` max=`{row['max']}` rho_O=`{row['rho_O']}` "
        f"rho_E=`{row['rho_E']}` landings=`{row['n_unique_landings']}` "
        f"mono=`{row['monochrome']}` sep=`{row['scale_separated']}`"
    )


def render_markdown(payload: dict[str, Any]) -> str:
    decision = payload["decision"]
    scan = payload["scan"]
    diag = scan["diagnostic"]
    confirm = scan["confirm"]
    atlas = scan["atlas"]
    amp = scan["amplification"]
    interior = scan["interior"]
    lean = payload["lean"]
    lines = [
        "# Juggler realization-set geometry",
        "",
        f"Status: **{decision['classification']}**",
        "",
        "Standalone application phase. Not a Research Engine experiment",
        "and not a termination theorem. Studies the realizing sets",
        "`R_w(N) = {n <= N : follows(n,w)}` of the prefix trie. Does not",
        "reopen PE-factor grammar or residual-future quotients.",
        "",
        "## Branch budget",
        "",
        "```text",
        "Mathematical target     What geometry of R_w makes a prefix unary?",
        "Novelty hypothesis      inverse-floor cells / scale of R_w force d(w)=1",
        "Falsifier               unary without monochrome landings, or a square",
        "                        amplification law that survives mixed itineraries, or",
        "                        a hole that is CELL_EMPTY rather than scale",
        "Existing machinery      follows_itinerary, image_after, even_preimage, atlas trie",
        "Maximum Phase-0 scope   R_w on n<=4000 then 1e5; selected roots n<=1e7",
        "```",
        "",
        "## Metadata",
        "",
        f"- diagnostic window: `n<= {diag['n_max']}`, `k<= {diag['k_max']}`",
        f"- confirm window: `n<= {confirm['n_max']}`, `k<= {confirm['k_max']}`",
        f"- engine control layer modified: `{payload['engine_control_layer_modified']}`",
        f"- classification: **{decision['classification']}**",
        f"- sorry-free: `{lean['sorry_free']}`",
        "",
        decision["reason"],
        "",
        "## Atlas reproduction",
        "",
    ]
    if atlas.get("available"):
        lines.append("Even tower `m(E^r)` versus `2^{2^{r-1}}`:")
        lines.append("")
        for row in atlas["tower"]:
            lines.append(
                f"- r=`{row['r']}` word=`{row['word']}` min=`{row['min_realizer']}` "
                f"tower=`{row['tower']}` status=`{row['status']}`"
            )
        lines.extend(["", "First unary parents:", ""])
        for row in atlas["first_unary"]:
            lines.append(
                f"- `{row['word']}` min=`{row['min_realizer']}` class=`{row['class']}`"
            )
        lines.extend(["", "First rooted holes:", ""])
        for row in atlas["first_holes"]:
            lines.append(f"- `{row['word']}` status=`{row['status']}`")
        ee = atlas["ee_prefix_length_12"]
        lines.extend(
            [
                "",
                f"- `EE…` words at length 12: `{ee['count']}` unary `{ee['unary']}`",
                "",
                "Leading-`E` unary fraction at length 19:",
                "",
            ]
        )
        for key, rec in atlas["lead_E_unary_length_19"].items():
            lines.append(
                f"- leadE=`{key}` nodes=`{rec['nodes']}` unary=`{rec['unary']}` frac=`{rec['frac']}`"
            )
    else:
        lines.append("Atlas SQLite was not available.")
    lines.extend(["", "## Missing-child status", ""])
    for row in scan["missing_children"]:
        lines.append(
            f"- `{row['child']}` status=`{row['status']}` — {row['reason']}"
        )
    if interior.get("available"):
        lines.extend(["", "## Root versus interior", ""])
        for word, rec in interior["words"].items():
            ex = rec["example"]
            lines.append(
                f"- `{word}` hosts=`{rec['count']}` min_pos=`{rec['min_position']}` "
                f"min_state=`{rec['min_state']}` in_atlas=`{rec['states_within_atlas']}` "
                f"follows=`{ex['follows'] if ex else None}` host_n=`{ex['n'] if ex else None}` "
                f"host=`{ex['host'] if ex else None}`"
            )
    selected = scan.get("selected_roots", {})
    if selected.get("words"):
        lines.extend(["", f"## Selected exact roots n<=`{selected['n_max']}`", ""])
        for word, rec in selected["words"].items():
            lines.append(
                f"- `{word}` |R|=`{rec['size']}` min=`{rec['min']}` max=`{rec['max']}`"
            )
    artefact = scan.get("window_artefact")
    if artefact:
        lines.extend(
            [
                "",
                "## Window artefact",
                "",
                f"- `{artefact['word']}` diagnostic=`{artefact['diagnostic_class']}` "
                f"atlas=`{artefact['atlas_class']}` — {artefact['reason']}",
            ]
        )
    corridor = scan.get("corridor")
    if corridor:
        lines.extend(
            [
                "",
                "## Set recurrence",
                "",
                f"- prepend E on the empty word: exact=`{corridor['empty_prepend_E_exact']}`",
                f"- prepend O on the empty word: exact=`{corridor['empty_prepend_O_exact']}` "
                f"predicted=`{corridor['empty_prepend_O_predicted']}` "
                f"actual=`{corridor['empty_prepend_O_actual']}` "
                f"leak=`{corridor['empty_prepend_O_leak']}`",
                f"- even-tower prepend E: `{corridor['even_tower_prepend_exact']}`",
                f"- prepend E mismatches among prefixes: `{corridor['prepend_E_mismatches']}`",
                f"- prepend O mismatches among prefixes: `{corridor['prepend_O_mismatches']}` "
                f"first=`{corridor['first_prepend_O_mismatch']}`",
                f"- append rule: {corridor['append_rule']}",
                f"- prepend E rule: {corridor['prepend_E_rule']}",
                f"- prepend O rule: {corridor['prepend_O_rule']}",
            ]
        )
    lines.extend(
        [
            "",
            "## Diagnostic realizing sets",
            "",
            f"- words: `{diag['n_words']}`",
            f"- uncovered realizers: `{diag['uncovered_total']}`",
            f"- unary nodes: `{diag['unary_total']}` monochrome landings `{diag['unary_monochrome']}`",
            f"- unary with a singleton landing: `{diag['unary_singleton_landing']}`",
            f"- binary nodes: `{diag['binary_total']}` scale-separated children `{diag['binary_scale_separated']}`",
            f"- unary prefixes that regain two children: `{diag['unary_to_binary_count']}`",
            f"- interval classes by degree: `{diag.get('interval_by_degree')}`",
            "",
            "Branching profile (diagnostic):",
            "",
        ]
    )
    for length, counts in diag["profile"].items():
        lines.append(f"- k=`{length}` {counts}")
    lines.extend(["", "Adversarial prefixes in the diagnostic window:", ""])
    for row in diag["adversarial"]:
        lines.append(_fmt_row(row))
    lines.extend(
        [
            "",
            "## Confirm window",
            "",
            f"- words: `{confirm['n_words']}` uncovered `{confirm['uncovered_total']}`",
            f"- unary `{confirm['unary_total']}` monochrome `{confirm['unary_monochrome']}`",
            f"- singleton landings `{confirm['unary_singleton_landing']}`",
            f"- binary scale-separated `{confirm['binary_scale_separated']}` / `{confirm['binary_total']}`",
            f"- unary-to-binary `{confirm['unary_to_binary_count']}`",
            "",
        ]
    )
    if confirm["unary_to_binary"]:
        lines.append("Smallest unary-to-binary returns in the confirm window:")
        lines.append("")
        for rec in confirm["unary_to_binary"][:8]:
            lines.append(f"- `{rec['parent']}` → `{rec['child']}` min=`{rec['min']}`")
        lines.append("")
    ret = scan["atlas_unary_return"]
    if ret.get("available"):
        lines.extend(
            [
                "Atlas unary-to-binary (capped scan of continuations):",
                "",
                f"- examples found: `{ret['unary_to_binary_count']}`",
                f"- among `EE…` parents: `{ret['ee_unary_to_binary_count']}`",
                "",
            ]
        )
        for rec in ret["unary_to_binary_examples"][:8]:
            lines.append(f"- `{rec['parent']}` → `{rec['child']}`")
        lines.append("")
    lines.extend(
        [
            "## Minimum-realizer extension",
            "",
            f"- tower identity in the diagnostic window: `{amp['tower_identity_in_window']}`",
            f"- square-law counterexample: `{amp['square_law_counterexample']}`",
            f"- odd-landing square counterexample: `{amp['odd_landing_square_counterexample']}`",
            f"- even-landing identity fail: `{amp['even_landing_identity_fail']}`",
            "",
            "The identity `m(E^{r+1})=m(E^r)^2` is special to the pure even",
            "tower. After an odd letter, `m(wE)=m(w)` whenever `T_w(m(w))` is",
            "even. The square lower bound does not survive mixed itineraries.",
            "",
            "## Lean",
            "",
        ]
    )
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
            "This is not a halt result and not a forbidden-factor law.",
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
