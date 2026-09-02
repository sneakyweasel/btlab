"""Formal vs realized AboveAnchor language gap.

Not a Research Engine control-layer experiment. Not a halt theorem.
Not a reopen of JUGGLER_LANGUAGE_IS_KNOWN_GRAMMAR, parity balance,
or macro-event coupling. Not a new atlas language tag.

Phase 0 enumerates the shared prefix-noncontracting language and
compares it to AboveAnchor prefixes of integer trajectories.
Absence is NOT_OBSERVED_WITHIN_BOUND, never a prohibition.
"""

from __future__ import annotations

import json
import struct
from collections import Counter
from pathlib import Path
from typing import Any

from research.juggler_sequence.atlas.packed import (
    pack_word,
    run_signature,
    unpack_word,
    word_id,
    word_metadata,
)
from research.juggler_sequence.atlas.schema import (
    CLAIM_NOT_OBSERVED,
    LANG_REALIZABLE,
    STATUS_FOUND,
)
from research.juggler_sequence.atlas.storage import DEFAULT_DATA_DIR, sqlite_path
from research.juggler_sequence.lean_paths import (
    JUGGLER_DIR,
    JUGGLER_PAPER_BARREL,
    engine_floor_text,
    has_named,
    juggler_text,
)
from research.juggler_sequence.minimum_relative import above_anchor
from research.juggler_sequence.near_extremal_prefixes import (
    prefix_nc_words,
    prefix_noncontracting,
)
from research.juggler_sequence.parity_balance import prefix_survives
from research.juggler_sequence.power_itineraries import ANTI_OVERCLAIM, floor_power

REPO_ROOT = Path(__file__).resolve().parents[3]
JSON_PATH = REPO_ROOT / "docs" / "research" / "juggler_formal_realized_gap.json"
DOC_PATH = REPO_ROOT / "docs" / "research" / "juggler_formal_realized_gap.md"
DATA_DIR = REPO_ROOT / "data" / "research" / "juggler" / "formal_realized_gap"

CLASS_CLOSED = "FORMAL_REALIZED_GAP_CLOSED"
CLASS_PARK = "FORMAL_REALIZED_GAP_PARK"
CLASS_GREEN = "FORMAL_REALIZED_GAP_GREEN"
CLASS_INCOMPLETE = "FORMAL_REALIZED_GAP_INCOMPLETE"

SCIENCE_K_MAX = 20
SCIENCE_N_MAX = 1_000_000
SCIENCE_HOLD_SPLIT = 500_000
TEST_K_MAX = 8
TEST_N_MAX = 400
LEFTOVERS = (37, 365, 501, 1517, 6187)
HARD_KEEP = 32
F_SAMPLE = 48
LEFTOVER_CAP = 4000

EXISTING_LEAN = (
    "prefixNoncontracting",
    "aboveAnchor_not_envelope_drop",
    "aboveAnchor_not_odd_even",
    "isolatedOddSurvival_bound",
    "AboveAnchor",
    "power_bound_word",
)

FORBIDDEN_THEOREMS = (
    "juggler_reaches_one",
    "no_juggler_escape",
    "all_finiteProgress",
)

FORBIDDEN_NEW_API = (
    "FormalLanguage",
    "FormalRealizedGap",
    "AboveAnchorLanguage",
    "SurvivalLanguage",
)

NEW_LEAN_FILES = (
    JUGGLER_DIR / "FormalLanguage.lean",
    JUGGLER_DIR / "FormalRealizedGap.lean",
    JUGGLER_DIR / "AboveAnchorLanguage.lean",
)

WITNESS_STARTS = (5, 37, 365)


def is_formal(word: str) -> bool:
    """Shared formal membership: every prefix is noncontracting."""

    return prefix_noncontracting(word)


def formal_by_length(k_max: int) -> dict[int, list[str]]:
    if k_max < 0:
        raise ValueError("k_max must be nonnegative")
    out: dict[int, list[str]] = {n: [] for n in range(1, k_max + 1)}
    for word in prefix_nc_words(k_max):
        out[len(word)].append(word)
    for words in out.values():
        words.sort()
    return out


def walk_aa(n: int, k_max: int) -> tuple[int, int]:
    """Return (packed AA prefix, S(n) capped at k_max).

    S(n) is the largest k such that T^j(n) >= n for every j <= k.
    The packed word uses the first S letters, LSB = first symbol.
    """

    if n < 2:
        raise ValueError("walk_aa requires n >= 2")
    if k_max < 0:
        raise ValueError("k_max must be nonnegative")
    packed = 0
    state = n
    depth = 0
    for step in range(1, k_max + 1):
        nxt = floor_power(state)
        if nxt < n:
            break
        packed |= (state & 1) << (step - 1)
        state = nxt
        depth = step
    return packed, depth


def survival_depth(n: int, cap: int = LEFTOVER_CAP) -> int:
    """Uncapped S(n) up to cap, for leftover laboratories only."""

    packed, depth = walk_aa(n, cap)
    del packed
    return depth


def first_factor_index(word: str, factor: str) -> int | None:
    pos = word.find(factor)
    return None if pos < 0 else pos


def run_lengths(word: str, letter: str) -> tuple[int, ...]:
    runs: list[int] = []
    current = 0
    for item in word:
        if item == letter:
            current += 1
            continue
        if current:
            runs.append(current)
            current = 0
    if current:
        runs.append(current)
    return tuple(runs)


def word_features(word: str) -> dict[str, Any]:
    length, packed = pack_word(word)
    meta = word_metadata(length, packed)
    odds = int(meta["odd_count"])
    return {
        "word": word,
        "length": length,
        "packed": packed,
        "word_id": int(meta["word_id"]),
        "odd_count": odds,
        "even_count": int(meta["even_count"]),
        "odd_runs": list(run_lengths(word, "O")),
        "even_runs": list(run_lengths(word, "E")),
        "first_oo": first_factor_index(word, "OO"),
        "first_ooo": first_factor_index(word, "OOO"),
        "envelope_slack": 3**odds - (1 << length),
        "run_signature": str(meta["run_signature"]),
        "status": CLAIM_NOT_OBSERVED,
    }


def hamming_distance(left: str, right: str) -> int:
    if len(left) != len(right):
        raise ValueError("hamming_distance requires equal lengths")
    return sum(a != b for a, b in zip(left, right))


def scan_aa(
    *,
    n_max: int,
    k_max: int,
    n_begin: int = 3,
    extras: tuple[int, ...] = LEFTOVERS,
    hold_split: int | None = None,
) -> dict[str, Any]:
    """Collect AA prefixes from odd starts and leftover laboratories."""

    if n_max < 1 or k_max < 0:
        raise ValueError("invalid scan bounds")
    realized: list[set[int]] = [set() for _ in range(k_max + 1)]
    hold_realized: list[set[int]] = [set() for _ in range(k_max + 1)]
    first_realizer: dict[int, int] = {}
    hard: list[tuple[int, int, int]] = []
    starts = set(range(n_begin + (n_begin % 2 == 0), n_max + 1, 2))
    starts.update(n for n in extras if n >= 2)
    scanned = 0
    for n in sorted(starts):
        packed, depth = walk_aa(n, k_max)
        scanned += 1
        if depth > 0:
            hard.append((depth, n, packed))
        in_hold = hold_split is not None and n <= hold_split
        for length in range(1, depth + 1):
            prefix = packed & ((1 << length) - 1)
            realized[length].add(prefix)
            wid = word_id(length, prefix)
            prev = first_realizer.get(wid)
            if prev is None or n < prev:
                first_realizer[wid] = n
            if in_hold:
                hold_realized[length].add(prefix)
    hard.sort(key=lambda row: (-row[0], row[1]))
    hard_rows = []
    for depth, n, packed in hard[:HARD_KEEP]:
        word = unpack_word(depth, packed) if depth else ""
        hard_rows.append(
            {
                "n": n,
                "S": depth,
                "word": word,
                "leftover": n in extras,
            }
        )
    leftover_S = {str(n): survival_depth(n) for n in extras if n >= 2}
    return {
        "n_max": n_max,
        "k_max": k_max,
        "n_begin": n_begin,
        "hold_split": hold_split,
        "scanned": scanned,
        "realized": realized,
        "hold_realized": hold_realized,
        "first_realizer": first_realizer,
        "hard_starts": hard_rows,
        "leftover_S": leftover_S,
    }


def gap_rows(
    formal: dict[int, list[str]],
    realized: list[set[int]],
    k_max: int,
) -> list[dict[str, Any]]:
    rows = []
    for length in range(1, k_max + 1):
        formal_packed = {pack_word(word)[1] for word in formal[length]}
        aa = realized[length]
        realized_formal = formal_packed & aa
        dead = formal_packed - aa
        extra_aa = aa - formal_packed
        n_formal = len(formal_packed)
        n_real = len(realized_formal)
        ratio = (n_real / n_formal) if n_formal else 1.0
        rows.append(
            {
                "N": length,
                "formal": n_formal,
                "realized_aa": n_real,
                "dead": len(dead),
                "R_N": ratio,
                "extra_aa_not_formal": len(extra_aa),
            }
        )
    return rows


def minimal_unobserved(
    formal: dict[int, list[str]],
    realized: list[set[int]],
    k_max: int,
) -> list[str]:
    """Shortest formal itineraries with no AA realizer whose parent was realized."""

    out: list[str] = []
    for length in range(1, k_max + 1):
        for word in formal[length]:
            packed = pack_word(word)[1]
            if packed in realized[length]:
                continue
            if length == 1:
                out.append(word)
                continue
            parent = packed & ((1 << (length - 1)) - 1)
            if parent in realized[length - 1]:
                out.append(word)
    return out


def matched_controls(
    word: str,
    realized_words: list[str],
    *,
    limit: int = 4,
) -> dict[str, Any]:
    odds = word.count("O")
    evens = len(word) - odds
    odd_runs = run_lengths(word, "O")
    even_runs = run_lengths(word, "E")
    signature = run_signature(*pack_word(word))
    same_counts = [
        other
        for other in realized_words
        if other.count("O") == odds and len(other) - other.count("O") == evens
    ]
    same_runs = [
        other
        for other in realized_words
        if run_lengths(other, "O") == odd_runs and run_lengths(other, "E") == even_runs
    ]
    same_sig = [
        other for other in realized_words if run_signature(*pack_word(other)) == signature
    ]
    hamming1 = [
        other for other in realized_words if hamming_distance(word, other) == 1
    ]
    return {
        "same_counts": same_counts[:limit],
        "same_run_multiset": same_runs[:limit],
        "same_signature": same_sig[:limit],
        "hamming1": hamming1[:limit],
        "n_same_counts": len(same_counts),
        "n_same_run_multiset": len(same_runs),
        "n_same_signature": len(same_sig),
        "n_hamming1": len(hamming1),
    }


def _all_share(words: list[str], pred) -> bool:
    return bool(words) and all(pred(word) for word in words)


def mine_property(
    minimal: list[str],
    formal: dict[int, list[str]],
) -> dict[str, Any]:
    """Search for the simplest exact invariant of F_j that is not all of L_formal."""

    if not minimal:
        return {
            "found": False,
            "name": None,
            "reason": "empty F_j",
            "counts": {},
        }
    lengths = sorted({len(word) for word in minimal})
    formal_pool = [word for length in lengths for word in formal[length]]
    counts = {
        "n_minimal": len(minimal),
        "lengths": dict(Counter(len(word) for word in minimal)),
        "end_E": sum(word.endswith("E") for word in minimal),
        "one_E": sum(word.count("E") == 1 for word in minimal),
        "o_then_e": sum(
            word == "O" * (len(word) - 1) + "E" for word in minimal if word
        ),
        "start_OOE": sum(word.startswith("OOE") for word in minimal),
        "start_OOO": sum(word.startswith("OOO") for word in minimal),
        "slack_le_1": sum(
            3 ** word.count("O") - (1 << len(word)) <= 1 for word in minimal
        ),
    }
    first_oo = Counter(first_factor_index(word, "OO") for word in minimal)
    first_e = Counter(word.find("E") for word in minimal)
    signatures = Counter(run_signature(*pack_word(word)) for word in minimal)
    counts["first_oo"] = {str(key): value for key, value in first_oo.items()}
    counts["first_E"] = {str(key): value for key, value in first_e.most_common(8)}
    counts["top_signatures"] = signatures.most_common(8)

    candidates: list[tuple[str, Any]] = [
        ("ends_with_E", lambda w: w.endswith("E")),
        ("exactly_one_E", lambda w: w.count("E") == 1),
        ("is_O_then_E", lambda w: len(w) >= 2 and w == "O" * (len(w) - 1) + "E"),
        ("starts_OOE", lambda w: w.startswith("OOE")),
        ("starts_OOO", lambda w: w.startswith("OOO")),
        ("tight_slack_le_1", lambda w: 3 ** w.count("O") - (1 << len(w)) <= 1),
        ("has_OOO", lambda w: "OOO" in w),
        ("no_OOO", lambda w: "OOO" not in w),
    ]
    if len(first_e) == 1:
        pos = next(iter(first_e))
        candidates.append((f"first_E_at_{pos}", lambda w, p=pos: w.find("E") == p))
    if len(first_oo) == 1:
        pos = next(iter(first_oo))
        candidates.append(
            (f"first_OO_at_{pos}", lambda w, p=pos: first_factor_index(w, "OO") == p)
        )

    distinctive: list[dict[str, Any]] = []
    for name, pred in candidates:
        if not _all_share(minimal, pred):
            continue
        formal_hit = sum(1 for word in formal_pool if pred(word))
        if formal_hit == len(formal_pool):
            continue
        distinctive.append(
            {
                "name": name,
                "formal_same_lengths": formal_hit,
                "formal_pool": len(formal_pool),
            }
        )
    found = bool(distinctive)
    name = distinctive[0]["name"] if distinctive else None
    reason = (
        "no exact predicate holds on all F_j and fails on some formal word"
        if not found
        else "exact predicate on every minimal unobserved prefix"
    )
    return {
        "found": found,
        "name": name,
        "reason": reason,
        "distinctive": distinctive,
        "counts": counts,
    }


def hold_minimal_and_later(
    formal: dict[int, list[str]],
    hold_realized: list[set[int]],
    full_realized: list[set[int]],
    k_max: int,
) -> dict[str, Any]:
    hold_F = minimal_unobserved(formal, hold_realized, k_max)
    later = []
    for word in hold_F:
        length, packed = pack_word(word)
        if packed in full_realized[length]:
            later.append(word)
    fraction = (len(later) / len(hold_F)) if hold_F else 0.0
    return {
        "n_hold_minimal": len(hold_F),
        "n_later": len(later),
        "later_fraction": fraction,
        "later_sample": later[:F_SAMPLE],
        "hold_sample": hold_F[:F_SAMPLE],
    }


def hard_language_ratio(
    hard_starts: list[dict[str, Any]],
    formal: dict[int, list[str]],
    realized: list[set[int]],
    k_max: int,
) -> dict[str, Any]:
    if not hard_starts:
        return {"n_hard": 0, "hard_words": 0, "ordinary_R": None, "hard_R": None}
    hard_sets: list[set[int]] = [set() for _ in range(k_max + 1)]
    for row in hard_starts:
        word = row["word"]
        packed, depth = pack_word(word) if word else (0, 0)
        if word:
            packed = pack_word(word)[1]
            depth = len(word)
        for length in range(1, min(depth, k_max) + 1):
            hard_sets[length].add(packed & ((1 << length) - 1))
    last = k_max
    n_formal = len(formal[last])
    ordinary_r = (
        len({pack_word(w)[1] for w in formal[last]} & realized[last]) / n_formal
        if n_formal
        else 1.0
    )
    hard_r = (
        len({pack_word(w)[1] for w in formal[last]} & hard_sets[last]) / n_formal
        if n_formal
        else 0.0
    )
    return {
        "n_hard": len(hard_starts),
        "hard_words_at_k": len(hard_sets[last]),
        "ordinary_R": ordinary_r,
        "hard_R": hard_r,
        "hard_thinner": hard_r + 1e-12 < ordinary_r * 0.5,
    }


def atlas_follows_control(
    formal: dict[int, list[str]],
    k_max: int,
) -> dict[str, Any]:
    """Optional: formal itineraries missing from atlas REALIZABLE prefixes."""

    path = sqlite_path(DEFAULT_DATA_DIR)
    if not path.is_file():
        return {"available": False, "reason": "word_atlas.sqlite absent"}
    try:
        from research.juggler_sequence.atlas.storage import connect
    except ImportError:
        return {"available": False, "reason": "atlas storage unavailable"}
    con = connect(DEFAULT_DATA_DIR)
    try:
        row = con.execute(
            "SELECT experiment_id FROM experiments ORDER BY start_time DESC LIMIT 1"
        ).fetchone()
        if row is None:
            return {"available": False, "reason": "no atlas experiment"}
        eid = row[0]
        missing_by_n: dict[str, int] = {}
        sample: list[str] = []
        for length in range(1, k_max + 1):
            found = {
                int(item[0])
                for item in con.execute(
                    """
                    SELECT word_id FROM realizers
                    WHERE experiment_id = ? AND realization_status = ?
                      AND (word_id >> 32) = ?
                    """,
                    (eid, STATUS_FOUND, length),
                )
            }
            miss = 0
            for word in formal[length]:
                length_i, packed = pack_word(word)
                if word_id(length_i, packed) not in found:
                    miss += 1
                    if len(sample) < 16:
                        sample.append(word)
            missing_by_n[str(length)] = miss
        return {
            "available": True,
            "experiment_id": eid,
            "language": LANG_REALIZABLE,
            "missing_by_N": missing_by_n,
            "sample": sample,
        }
    finally:
        con.close()


def leftover_aa_words(k_max: int) -> dict[str, Any]:
    rows = {}
    for n in WITNESS_STARTS:
        packed, depth = walk_aa(n, k_max)
        word = unpack_word(depth, packed) if depth else ""
        rows[str(n)] = {
            "S": depth,
            "word": word,
            "formal": is_formal(word) if word else True,
            "above_anchor": above_anchor(n, word) if word else True,
        }
    return rows


def write_packed_bin(path: Path, packed: list[int]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    ordered = sorted(packed)
    path.write_bytes(struct.pack("<" + "I" * len(ordered), *ordered) if ordered else b"")


def write_data_artifacts(
    *,
    formal: dict[int, list[str]],
    realized: list[set[int]],
    minimal: list[str],
    hard_starts: list[dict[str, Any]],
    first_realizer: dict[int, int],
    k_max: int,
    n_max: int,
    hold_split: int | None,
    git_commit: str,
) -> None:
    DATA_DIR.mkdir(parents=True, exist_ok=True)
    for length in range(1, k_max + 1):
        write_packed_bin(
            DATA_DIR / f"formal_words_{length}.bin",
            [pack_word(word)[1] for word in formal[length]],
        )
        write_packed_bin(DATA_DIR / f"aa_words_{length}.bin", sorted(realized[length]))
    with (DATA_DIR / "minimal_unobserved.jsonl").open("w", encoding="utf-8") as handle:
        for word in minimal:
            row = word_features(word)
            row["n_max"] = n_max
            row["k_max"] = k_max
            row["min_realizer"] = first_realizer.get(row["word_id"])
            handle.write(json.dumps(row) + "\n")
    (DATA_DIR / "hard_starts.jsonl").write_text(
        "".join(json.dumps(row) + "\n" for row in hard_starts),
        encoding="utf-8",
    )
    provenance = {
        "n_max": n_max,
        "k_max": k_max,
        "hold_split": hold_split,
        "leftovers": list(LEFTOVERS),
        "git_commit": git_commit,
        "claim": CLAIM_NOT_OBSERVED,
    }
    (DATA_DIR / "provenance.json").write_text(
        json.dumps(provenance, indent=2) + "\n", encoding="utf-8"
    )


def git_commit() -> str:
    try:
        from research.juggler_sequence.atlas.storage import git_commit as atlas_commit

        return atlas_commit(REPO_ROOT)
    except Exception:
        return "working-tree"


def run_probe(
    *,
    k_max: int = TEST_K_MAX,
    n_max: int = TEST_N_MAX,
    hold_split: int | None = None,
    write_data: bool = False,
) -> dict[str, Any]:
    formal = formal_by_length(k_max)
    scan = scan_aa(
        n_max=n_max,
        k_max=k_max,
        hold_split=hold_split,
    )
    gaps = gap_rows(formal, scan["realized"], k_max)
    minimal = minimal_unobserved(formal, scan["realized"], k_max)
    realized_words = {
        length: [unpack_word(length, packed) for packed in sorted(scan["realized"][length])]
        for length in range(1, k_max + 1)
    }
    control_sample = []
    for word in minimal[: min(12, len(minimal))]:
        control_sample.append(
            {
                "word": word,
                "features": word_features(word),
                "controls": matched_controls(word, realized_words[len(word)]),
            }
        )
    mined = mine_property(minimal, formal)
    hold = (
        hold_minimal_and_later(
            formal, scan["hold_realized"], scan["realized"], k_max
        )
        if hold_split is not None
        else {
            "n_hold_minimal": None,
            "n_later": None,
            "later_fraction": None,
        }
    )
    hard = hard_language_ratio(
        scan["hard_starts"], formal, scan["realized"], k_max
    )
    leftovers = leftover_aa_words(k_max)
    leftover_formal = all(row["formal"] and row["above_anchor"] for row in leftovers.values())
    extra_aa = sum(row["extra_aa_not_formal"] for row in gaps)
    last = gaps[-1] if gaps else None
    atlas = atlas_follows_control(formal, min(k_max, 20))
    commit = git_commit()
    if write_data:
        write_data_artifacts(
            formal=formal,
            realized=scan["realized"],
            minimal=minimal,
            hard_starts=scan["hard_starts"],
            first_realizer=scan["first_realizer"],
            k_max=k_max,
            n_max=n_max,
            hold_split=hold_split,
            git_commit=commit,
        )
    return {
        "basin": "ordinary_integers",
        "k_max": k_max,
        "n_max": n_max,
        "hold_split": hold_split,
        "scanned": scan["scanned"],
        "gaps": gaps,
        "last": last,
        "n_minimal": len(minimal),
        "minimal_sample": [word_features(word) for word in minimal[:F_SAMPLE]],
        "minimal_by_length": dict(Counter(len(word) for word in minimal)),
        "property": mined,
        "holdout": hold,
        "hard": hard,
        "hard_starts": scan["hard_starts"],
        "leftovers": leftovers,
        "leftover_S": scan["leftover_S"],
        "leftover_formal": leftover_formal,
        "controls": control_sample,
        "atlas": atlas,
        "extra_aa_not_formal": extra_aa,
        "git_commit": commit,
        "letter_chain": False,
        "cyclemin_in_language": False,
        "formal_realized_lean": False,
        "paper_a_modified": False,
        "halt_theorem": False,
        "new_atlas_language": False,
    }


def lean_api_present() -> dict[str, bool]:
    combined = juggler_text()
    named = {name: has_named(combined, name) for name in EXISTING_LEAN}
    forbidden = {name: has_named(combined, name) for name in FORBIDDEN_THEOREMS}
    new_api = {name: has_named(combined, name) for name in FORBIDDEN_NEW_API}
    paper = JUGGLER_PAPER_BARREL.read_text(encoding="utf-8")
    schema = (
        REPO_ROOT / "src" / "research" / "juggler_sequence" / "atlas" / "schema.py"
    ).read_text(encoding="utf-8")
    return {
        "sorry_free": "sorry" not in combined and "admit" not in combined,
        **named,
        **{f"has_{name}": present for name, present in forbidden.items()},
        **{f"has_api_{name}": present for name, present in new_api.items()},
        "new_lean_file": any(path.is_file() for path in NEW_LEAN_FILES),
        "not_in_paper_barrel": "FormalLanguage" not in paper
        and "FormalRealizedGap" not in paper,
        "no_atlas_lang_formal": "LANG_FORMAL" not in schema
        and "LANG_ABOVE_ANCHOR" not in schema,
        "FloorPower_not_rewritten": "CycleItinerary" not in engine_floor_text(),
    }


def classify(scan: dict[str, Any], lean: dict[str, bool]) -> dict[str, Any]:
    lean_ok = (
        lean["sorry_free"]
        and all(lean[name] for name in EXISTING_LEAN)
        and not lean["has_juggler_reaches_one"]
        and not lean["new_lean_file"]
        and not any(lean[f"has_api_{name}"] for name in FORBIDDEN_NEW_API)
        and lean["not_in_paper_barrel"]
        and lean["no_atlas_lang_formal"]
    )
    if not lean_ok:
        return {"classification": CLASS_INCOMPLETE, "reason": f"lean_ok={lean_ok}"}
    if (
        scan["letter_chain"]
        or scan["cyclemin_in_language"]
        or scan["halt_theorem"]
        or scan["formal_realized_lean"]
        or scan["new_atlas_language"]
        or scan["extra_aa_not_formal"]
        or not scan["leftover_formal"]
    ):
        return {"classification": CLASS_INCOMPLETE, "reason": "out-of-scope claim or AA leak"}

    last = scan["last"]
    hold_frac = scan["holdout"].get("later_fraction")
    mined = scan["property"]
    hard = scan["hard"]
    r_n = last["R_N"] if last else 0.0
    dead_frac = (last["dead"] / last["formal"]) if last and last["formal"] else 0.0

    windowy = hold_frac is not None and hold_frac >= 0.25
    distinctive = bool(mined.get("found"))
    scale_like = mined.get("name") in {
        "is_O_then_E",
        "exactly_one_E",
        "ends_with_E",
        "tight_slack_le_1",
    }
    thin = last is not None and r_n >= 0.85 and scan["n_minimal"] <= 4
    empty_gap = last is not None and last["dead"] == 0
    equally_rich = last is not None and dead_frac >= 0.25 and not distinctive
    hard_only = bool(hard.get("hard_thinner")) and equally_rich

    if empty_gap or thin:
        return {
            "classification": CLASS_CLOSED,
            "reason": (
                "thin gap: formal language is nearly the AA language in-window, "
                "or F_j is empty"
            ),
        }
    if windowy and (not distinctive or scale_like):
        return {
            "classification": CLASS_CLOSED,
            "reason": (
                "F_j from the low-n half realizes later; remaining unobserved "
                "prefixes are window or scale artefacts, not a new exact P"
            ),
        }
    if distinctive and not scale_like and not windowy:
        return {
            "classification": CLASS_GREEN,
            "reason": (
                f"minimal unobserved prefixes share exact property {mined['name']}"
            ),
        }
    if hard_only:
        return {
            "classification": CLASS_PARK,
            "reason": (
                "ordinary D_N is unstructured; hard starts occupy a thinner "
                "realized language"
            ),
        }
    if equally_rich or not distinctive:
        return {
            "classification": CLASS_CLOSED,
            "reason": (
                "D_N stays rich and F_j has no simple exact P beyond envelope "
                "or scale; the formal abstraction is not losing an word-level law"
            ),
        }
    return {
        "classification": CLASS_GREEN,
        "reason": mined.get("reason", "candidate property"),
    }


def probe_payload(
    *,
    k_max: int = TEST_K_MAX,
    n_max: int = TEST_N_MAX,
    hold_split: int | None = None,
    write_data: bool = False,
) -> dict[str, Any]:
    scan = run_probe(
        k_max=k_max,
        n_max=n_max,
        hold_split=hold_split,
        write_data=write_data,
    )
    lean = lean_api_present()
    decision = classify(scan, lean)
    anti = dict(ANTI_OVERCLAIM)
    anti.update(
        {
            "global_non_realizability": False,
            "forbidden_factor_theorem": False,
            "search_horizon_is_L": False,
            "cyclemin_in_language": False,
            "formal_realized_lean": False,
            "new_atlas_language": False,
            "letter_chain": False,
            "global_termination": False,
        }
    )
    return {
        "experiment": "juggler_formal_realized_gap",
        "engine_control_layer_modified": False,
        "anti_overclaim": anti,
        "scan": scan,
        "lean": lean,
        "decision": decision,
        "search_method": (
            "prefixNoncontracting enumeration; AA walk until T^j < n; "
            f"k<={k_max}, odd n<={n_max}, leftovers {list(LEFTOVERS)}; "
            "hold-out split; matched Hamming/run controls; no CycleMin words"
        ),
    }


def render_markdown(payload: dict[str, Any]) -> str:
    decision = payload["decision"]
    scan = payload["scan"]
    lean = payload["lean"]
    last = scan["last"] or {}
    mined = scan["property"]
    hold = scan["holdout"]
    lines = [
        "# Juggler formal vs realized AboveAnchor language",
        "",
        f"Status: **{decision['classification']}**",
        "",
        "Shared prefix-noncontracting language versus integer AboveAnchor prefixes.",
        "Not a halt theorem. Absence is NOT_OBSERVED_WITHIN_BOUND.",
        "",
        "## Branch budget",
        "",
        "```text",
        "Mathematical target     simple exact P for D_N, or equally rich",
        "Novelty hypothesis      Lean forgets one AA-realizability feature",
        "Maximum Phase-0 scope   enumerate L_formal; AA scan; F_j; hold-out",
        "```",
        "",
        "## Metadata",
        "",
        f"- classification: **{decision['classification']}**",
        f"- k_max: `{scan['k_max']}` n_max: `{scan['n_max']}` hold_split: `{scan['hold_split']}`",
        f"- scanned starts: `{scan['scanned']}`",
        f"- last N formal/AA/dead: `{last.get('formal')}` / `{last.get('realized_aa')}` / `{last.get('dead')}`",
        f"- R_N: `{last.get('R_N')}`",
        f"- |F_j|: `{scan['n_minimal']}`",
        f"- property: `{mined.get('name')}` found=`{mined.get('found')}`",
        f"- hold-out later fraction: `{hold.get('later_fraction')}`",
        f"- leftover AA prefixes formal: `{scan['leftover_formal']}`",
        f"- extra AA not formal: `{scan['extra_aa_not_formal']}`",
        "",
        decision["reason"] + ".",
        "",
        "## Counts by length",
        "",
    ]
    for row in scan["gaps"]:
        lines.append(
            f"- N=`{row['N']}` formal=`{row['formal']}` AA=`{row['realized_aa']}` "
            f"dead=`{row['dead']}` R_N=`{row['R_N']:.6f}`"
        )
    lines.extend(
        [
            "",
            "## Minimal unobserved prefixes",
            "",
            f"Count `{scan['n_minimal']}` by length `{scan['minimal_by_length']}`.",
            f"Claim language: `{CLAIM_NOT_OBSERVED}`.",
            "",
        ]
    )
    for row in scan["minimal_sample"][:16]:
        lines.append(
            f"- `{row['word']}` slack=`{row['envelope_slack']}` "
            f"sig=`{row['run_signature']}` first_OO=`{row['first_oo']}`"
        )
    lines.extend(
        [
            "",
            "## Property search",
            "",
            f"- found: `{mined.get('found')}` name: `{mined.get('name')}`",
            f"- reason: {mined.get('reason')}",
            f"- distinctive: `{mined.get('distinctive')}`",
            "",
            "## Hold-out",
            "",
            f"- hold F_j: `{hold.get('n_hold_minimal')}` later: `{hold.get('n_later')}` "
            f"fraction: `{hold.get('later_fraction')}`",
            "",
            "## Hard starts",
            "",
            f"- ordinary R: `{scan['hard'].get('ordinary_R')}` hard R: `{scan['hard'].get('hard_R')}`",
            f"- thinner: `{scan['hard'].get('hard_thinner')}`",
            "",
        ]
    )
    for row in scan["hard_starts"][:12]:
        lines.append(
            f"- n=`{row['n']}` S=`{row['S']}` leftover=`{row['leftover']}` word=`{row['word']}`"
        )
    lines.extend(["", "## Leftover witnesses", ""])
    for n in WITNESS_STARTS:
        row = scan["leftovers"][str(n)]
        lines.append(
            f"- `{n}`: S=`{row['S']}` formal=`{row['formal']}` "
            f"AA=`{row['above_anchor']}` word=`{row['word']}`"
        )
    lines.extend(["", "## Atlas follows control", ""])
    atlas = scan["atlas"]
    if atlas.get("available"):
        lines.append(
            f"- experiment `{atlas.get('experiment_id')}` missing-by-N "
            f"`{atlas.get('missing_by_N')}`"
        )
    else:
        lines.append(f"- unavailable: `{atlas.get('reason')}`")
    lines.extend(["", "## Existing Lean (unchanged)", ""])
    for name in EXISTING_LEAN:
        lines.append(f"- `{name}`: `{lean[name]}`")
    lines.extend(
        [
            f"- new Lean file: `{lean['new_lean_file']}`",
            f"- no LANG_FORMAL / LANG_ABOVE_ANCHOR: `{lean['no_atlas_lang_formal']}`",
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


def write_summary(payload: dict[str, Any]) -> None:
    DATA_DIR.mkdir(parents=True, exist_ok=True)
    scan = payload["scan"]
    last = scan["last"] or {}
    summary = {
        "classification": payload["decision"]["classification"],
        "reason": payload["decision"]["reason"],
        "k_max": scan["k_max"],
        "n_max": scan["n_max"],
        "R_N": last.get("R_N"),
        "formal": last.get("formal"),
        "realized_aa": last.get("realized_aa"),
        "dead": last.get("dead"),
        "n_minimal": scan["n_minimal"],
        "property": scan["property"].get("name"),
        "property_found": scan["property"].get("found"),
        "holdout_later_fraction": scan["holdout"].get("later_fraction"),
        "hard_thinner": scan["hard"].get("hard_thinner"),
        "claim": CLAIM_NOT_OBSERVED,
    }
    (DATA_DIR / "summary.json").write_text(
        json.dumps(summary, indent=2) + "\n", encoding="utf-8"
    )
    (DATA_DIR / "summary.md").write_text(render_markdown(payload), encoding="utf-8")


def write_artifacts(payload: dict[str, Any] | None = None) -> dict[str, Any]:
    data = payload if payload is not None else probe_payload()
    JSON_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(data, indent=2) + "\n", encoding="utf-8")
    DOC_PATH.write_text(render_markdown(data), encoding="utf-8")
    write_summary(data)
    return data


def main() -> None:
    payload = probe_payload(
        k_max=SCIENCE_K_MAX,
        n_max=SCIENCE_N_MAX,
        hold_split=SCIENCE_HOLD_SPLIT,
        write_data=True,
    )
    write_artifacts(payload)
    print(payload["decision"]["classification"])
    print(payload["decision"]["reason"])
    last = payload["scan"]["last"]
    if last:
        print(
            f"N={last['N']} formal={last['formal']} AA={last['realized_aa']} "
            f"dead={last['dead']} R_N={last['R_N']}"
        )
    print("F_j", payload["scan"]["n_minimal"], payload["scan"]["property"].get("name"))


if __name__ == "__main__":
    main()
