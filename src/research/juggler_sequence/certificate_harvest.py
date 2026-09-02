"""First-descent leftover-class harvest. Not a halt theorem.

Adapts the parked Word Atlas GPU engine. Not a recensus, not a new
atlas language tag, not Paper A/B, and not a claim that every
positive integer reaches 1.

A certificate is the first realized word w with T^{|w|}(n) < n.
Coarse bins are E, OE, OOEE, leftover. The leftover histogram is
first-contracting packed words only.
"""

from __future__ import annotations

import json
import re
import subprocess
from collections import Counter
from pathlib import Path
from typing import Any

from research.juggler_sequence.atlas.native import (
    find_binary,
    parse_harvest_tsv,
    run_harvest,
)
from research.juggler_sequence.atlas.packed import (
    dense_index,
    dense_size,
    pack_word,
    run_signature,
    unpack_word,
)
from research.juggler_sequence.atlas.schema import (
    CLAIM_NOT_OBSERVED,
    CLAIM_OBSERVED,
    LANGUAGE_IDS,
)
from research.juggler_sequence.lean_paths import (
    JUGGLER_DIR,
    JUGGLER_PAPER_BARREL,
    engine_floor_text,
    has_named,
    juggler_text,
)
from research.juggler_sequence.minimal_anchor_closure import trajectory_until_drop
from research.juggler_sequence.power_words import ANTI_OVERCLAIM, floor_power

REPO_ROOT = Path(__file__).resolve().parents[3]
JSON_PATH = REPO_ROOT / "docs" / "research" / "juggler_certificate_harvest.json"
DOC_PATH = REPO_ROOT / "docs" / "research" / "juggler_certificate_harvest.md"
DATA_DIR = REPO_ROOT / "data" / "research" / "juggler" / "certificate_harvest"

CLASS_PARK = "CERTIFICATE_HARVEST_PARK"
CLASS_GREEN = "CERTIFICATE_HARVEST_GREEN"
CLASS_CLOSED = "CERTIFICATE_HARVEST_CLOSED"
CLASS_INCOMPLETE = "CERTIFICATE_HARVEST_INCOMPLETE"

TEST_N_MAX = 400
TEST_K_MAX = 20
SCIENCE_K_MAX = 20
SCIENCE_N_MAX = 10**9
SCALE_SPLIT = 10**8
OPTIONAL_N_MAX = 10**10
CPU_FINISH_CAP = 4000
LONG_WORD_CAP = 64
CPU_FINISH_MAX_STARTS = 10_000

UNARY_OE = re.compile(r"^O+E+$")

EXISTING_LEAN = (
    "even_finiteProgress",
    "odd_even_finiteProgress",
    "FiniteProgress",
)

FORBIDDEN_THEOREMS = (
    "juggler_reaches_one",
    "no_juggler_escape",
    "all_finiteProgress",
)

FORBIDDEN_NEW_API = (
    "CertificateHarvest",
    "LeftoverHistogram",
    "HarvestClass",
)

NEW_LEAN_FILES = (
    JUGGLER_DIR / "CertificateHarvest.lean",
    JUGGLER_DIR / "LeftoverHistogram.lean",
)

FIXTURE_E = (6, "E")
FIXTURE_OE = (7, "OE")
FIXTURE_OOEE = (5, "OOEE")
FIXTURE_LEFTOVER = (9, "OOEOE")


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


def classify_word(word: str) -> str:
    if word == "E":
        return "E"
    if word == "OE":
        return "OE"
    if word == "OOEE":
        return "OOEE"
    return "leftover"


def first_certificate(
    n: int,
    *,
    k_max: int = TEST_K_MAX,
    step_cap: int = CPU_FINISH_CAP,
) -> dict[str, Any]:
    if n < 2:
        return {
            "n": n,
            "cls": "skip",
            "word": "",
            "length": 0,
            "packed": 0,
            "uncapped": False,
        }
    state = n
    chars: list[str] = []
    limit = max(k_max, step_cap)
    for _depth in range(1, limit + 1):
        chars.append("O" if state % 2 else "E")
        nxt = floor_power(state)
        if nxt < n:
            word = "".join(chars)
            length = len(word)
            packed = pack_word(word)[1] if length <= 64 else None
            return {
                "n": n,
                "cls": classify_word(word),
                "word": word,
                "length": length,
                "packed": packed,
                "uncapped": False,
            }
        state = nxt
    word = "".join(chars[:k_max])
    return {
        "n": n,
        "cls": "uncapped",
        "word": word,
        "length": k_max,
        "packed": pack_word(word)[1] if word else 0,
        "uncapped": True,
    }


def empty_tables(k_max: int) -> dict[str, Any]:
    size = dense_size(k_max)
    return {
        "k_max": k_max,
        "count_skip": 0,
        "count_e": 0,
        "count_oe": 0,
        "count_ooee": 0,
        "count_leftover": 0,
        "count_uncapped": 0,
        "count_overflow": 0,
        "count_long": 0,
        "replayed_overflow": 0,
        "replayed_uncapped": 0,
        "overflow_truncated": False,
        "uncapped_truncated": False,
        "hist": [0] * size,
        "min_n": [None] * size,
        "long_words": Counter(),
        "long_min_n": {},
    }


def _bump_leftover(tables: dict[str, Any], word: str, n: int) -> None:
    k_max = int(tables["k_max"])
    if len(word) <= k_max:
        length, packed = pack_word(word)
        idx = dense_index(length, packed)
        tables["hist"][idx] += 1
        prev = tables["min_n"][idx]
        if prev is None or n < prev:
            tables["min_n"][idx] = n
        tables["count_leftover"] += 1
        return
    tables["count_long"] += 1
    tables["count_leftover"] += 1
    tables["long_words"][word[:LONG_WORD_CAP]] += 1
    key = word[:LONG_WORD_CAP]
    prev = tables["long_min_n"].get(key)
    if prev is None or n < prev:
        tables["long_min_n"][key] = n


def apply_hit(tables: dict[str, Any], hit: dict[str, Any]) -> None:
    cls = hit["cls"]
    if cls == "skip":
        tables["count_skip"] += 1
    elif cls == "E":
        tables["count_e"] += 1
    elif cls == "OE":
        tables["count_oe"] += 1
    elif cls == "OOEE":
        tables["count_ooee"] += 1
    elif cls == "leftover":
        _bump_leftover(tables, hit["word"], hit["n"])
    else:
        tables["count_uncapped"] += 1


def harvest_exact(
    n_begin: int,
    n_max: int,
    *,
    k_max: int = TEST_K_MAX,
    step_cap: int = CPU_FINISH_CAP,
) -> dict[str, Any]:
    tables = empty_tables(k_max)
    tables["n_begin"] = n_begin
    tables["n_max"] = n_max
    tables["backend"] = "python"
    for n in range(n_begin, n_max + 1):
        apply_hit(tables, first_certificate(n, k_max=k_max, step_cap=step_cap))
    return tables


def merge_unresolved(tables: dict[str, Any], starts: list[int], *, k_max: int) -> None:
    for n in starts:
        hit = first_certificate(n, k_max=k_max, step_cap=CPU_FINISH_CAP)
        if hit["cls"] == "uncapped":
            try:
                path = trajectory_until_drop(n, cap=CPU_FINISH_CAP)
            except ValueError:
                tables["count_uncapped"] += 1
                continue
            word = "".join("O" if item % 2 else "E" for item in path[:-1])
            hit = {
                "n": n,
                "cls": classify_word(word),
                "word": word,
                "length": len(word),
                "packed": pack_word(word)[1] if len(word) <= 64 else None,
                "uncapped": False,
            }
        if hit["cls"] == "leftover":
            _bump_leftover(tables, hit["word"], n)
        elif hit["cls"] == "E":
            tables["count_e"] += 1
        elif hit["cls"] == "OE":
            tables["count_oe"] += 1
        elif hit["cls"] == "OOEE":
            tables["count_ooee"] += 1
        else:
            tables["count_uncapped"] += 1


def tables_from_native(raw: dict[str, object], *, finish: bool = True) -> dict[str, Any]:
    k_max = int(raw["k_max"])
    tables = empty_tables(k_max)
    tables["n_begin"] = int(raw["n_begin"])
    tables["n_max"] = int(raw["n_max"])
    tables["backend"] = str(raw["backend"])
    tables["count_skip"] = int(raw["count_skip"])
    tables["count_e"] = int(raw["count_e"])
    tables["count_oe"] = int(raw["count_oe"])
    tables["count_ooee"] = int(raw["count_ooee"])
    tables["count_leftover"] = int(raw["count_leftover"])
    tables["count_uncapped"] = 0
    tables["count_overflow"] = 0
    tables["overflow_truncated"] = bool(raw["overflow_truncated"])
    tables["uncapped_truncated"] = bool(raw["uncapped_truncated"])
    tables["hist"] = list(raw["hist"])  # type: ignore[arg-type]
    tables["min_n"] = list(raw["min_n"])  # type: ignore[arg-type]
    overflow_n = list(raw.get("overflow_n") or [])
    uncapped_n = list(raw.get("uncapped_n") or [])
    native_overflow = int(raw["count_overflow"])
    native_uncapped = int(raw["count_uncapped"])
    pending = len(overflow_n) + len(uncapped_n)
    do_finish = bool(finish) and pending <= CPU_FINISH_MAX_STARTS
    if do_finish:
        merge_unresolved(tables, overflow_n, k_max=k_max)
        merge_unresolved(tables, uncapped_n, k_max=k_max)
        tables["count_overflow"] = max(0, native_overflow - len(overflow_n))
        if native_uncapped > len(uncapped_n):
            tables["count_uncapped"] += native_uncapped - len(uncapped_n)
            tables["uncapped_truncated"] = True
        tables["replayed_overflow"] = len(overflow_n)
        tables["replayed_uncapped"] = len(uncapped_n)
    else:
        tables["count_overflow"] = native_overflow
        tables["count_uncapped"] = native_uncapped
        tables["replayed_overflow"] = 0
        tables["replayed_uncapped"] = 0
        if pending > CPU_FINISH_MAX_STARTS:
            tables["cpu_finish_skipped"] = pending
    return tables


def leftover_rows(tables: dict[str, Any]) -> list[dict[str, Any]]:
    k_max = int(tables["k_max"])
    rows: list[dict[str, Any]] = []
    hist: list[int] = tables["hist"]
    min_n: list[int | None] = tables["min_n"]
    for length in range(1, k_max + 1):
        for packed in range(1 << length):
            idx = dense_index(length, packed)
            count = hist[idx]
            if count == 0:
                continue
            word = unpack_word(length, packed)
            rows.append(
                {
                    "word": word,
                    "length": length,
                    "packed": packed,
                    "count": count,
                    "min_n": min_n[idx],
                    "run_signature": run_signature(length, packed),
                    "unary_block": bool(UNARY_OE.match(word)),
                }
            )
    for word, count in tables["long_words"].items():
        length, packed = pack_word(word) if len(word) <= 64 else (len(word), None)
        rows.append(
            {
                "word": word,
                "length": len(word),
                "packed": packed,
                "count": count,
                "min_n": tables["long_min_n"].get(word),
                "run_signature": run_signature(length, packed) if packed is not None else "long",
                "unary_block": bool(UNARY_OE.match(word)),
                "long": True,
            }
        )
    rows.sort(key=lambda row: (-int(row["count"]), int(row["length"]), str(row["word"])))
    return rows


def signature_histogram(rows: list[dict[str, Any]]) -> list[dict[str, Any]]:
    grouped: dict[str, dict[str, Any]] = {}
    for row in rows:
        key = str(row["run_signature"])
        cur = grouped.get(key)
        if cur is None:
            grouped[key] = {
                "run_signature": key,
                "count": int(row["count"]),
                "words": 1,
                "min_n": row["min_n"],
                "unary_block": bool(row["unary_block"]),
            }
        else:
            cur["count"] += int(row["count"])
            cur["words"] += 1
            if row["min_n"] is not None and (
                cur["min_n"] is None or row["min_n"] < cur["min_n"]
            ):
                cur["min_n"] = row["min_n"]
    out = list(grouped.values())
    out.sort(key=lambda item: (-int(item["count"]), str(item["run_signature"])))
    return out


def coarse_of(tables: dict[str, Any]) -> dict[str, int]:
    return {
        "skip": int(tables["count_skip"]),
        "E": int(tables["count_e"]),
        "OE": int(tables["count_oe"]),
        "OOEE": int(tables["count_ooee"]),
        "leftover": int(tables["count_leftover"]),
        "uncapped": int(tables["count_uncapped"]),
        "overflow": int(tables["count_overflow"]),
        "long": int(tables["count_long"]),
        "replayed_overflow": int(tables.get("replayed_overflow") or 0),
        "replayed_uncapped": int(tables.get("replayed_uncapped") or 0),
    }


def word_shares(rows: list[dict[str, Any]], total: int) -> dict[str, float]:
    if total <= 0:
        return {}
    return {str(row["word"]): int(row["count"]) / total for row in rows}


def scale_drift(
    low_rows: list[dict[str, Any]],
    high_rows: list[dict[str, Any]],
    low_total: int,
    high_total: int,
) -> dict[str, Any]:
    low = word_shares(low_rows, low_total)
    high = word_shares(high_rows, high_total)
    keys = set(low) | set(high)
    deltas = []
    for key in keys:
        delta = high.get(key, 0.0) - low.get(key, 0.0)
        deltas.append({"word": key, "delta": delta, "low": low.get(key, 0.0), "high": high.get(key, 0.0)})
    deltas.sort(key=lambda item: -abs(float(item["delta"])))
    tv = 0.5 * sum(abs(float(item["delta"])) for item in deltas)
    return {
        "tv": tv,
        "max_abs_delta": abs(float(deltas[0]["delta"])) if deltas else 0.0,
        "top_deltas": deltas[:12],
    }


def analyze_window(tables: dict[str, Any], name: str) -> dict[str, Any]:
    rows = leftover_rows(tables)
    coarse = coarse_of(tables)
    leftover = coarse["leftover"]
    unary = sum(int(row["count"]) for row in rows if row["unary_block"])
    multi = leftover - unary
    oooo_star = sum(
        int(row["count"])
        for row in rows
        if row["unary_block"] and str(row["word"]).startswith("OOOO")
    )
    return {
        "name": name,
        "n_begin": tables.get("n_begin"),
        "n_max": tables.get("n_max"),
        "backend": tables.get("backend"),
        "coarse": coarse,
        "leftover_words": rows[:40],
        "leftover_words_all": rows,
        "n_leftover_types": len(rows),
        "signatures": signature_histogram(rows)[:24],
        "unary_block_count": unary,
        "multi_block_count": multi,
        "oooo_star_count": oooo_star,
        "unary_share": (unary / leftover) if leftover else 0.0,
        "oooo_star_share": (oooo_star / leftover) if leftover else 0.0,
        "overflow_truncated": bool(tables.get("overflow_truncated")),
        "uncapped_truncated": bool(tables.get("uncapped_truncated")),
    }


def load_native_window(path: Path) -> dict[str, Any]:
    raw = parse_harvest_tsv(path)
    return tables_from_native(raw, finish=True)


def run_native_window(
    n_begin: int,
    n_max: int,
    *,
    k_max: int,
    backend: str,
    output: Path,
) -> dict[str, Any]:
    run_harvest(
        k_max=k_max,
        n_max=n_max,
        n_begin=n_begin,
        backend=backend,
        output=output,
        list_cap=0 if n_max >= 10**7 else 10_000,
    )
    raw = parse_harvest_tsv(output)
    return tables_from_native(raw, finish=True)


def run_probe(
    *,
    n_max: int = TEST_N_MAX,
    k_max: int = TEST_K_MAX,
    backend: str = "python",
    scale_split: int | None = None,
    optional_n_max: int | None = None,
    data_dir: Path | None = None,
) -> dict[str, Any]:
    windows: list[dict[str, Any]] = []
    if backend == "python":
        tables = harvest_exact(2, n_max, k_max=k_max)
        windows.append(analyze_window(tables, "all"))
        if scale_split is not None and scale_split < n_max:
            low = harvest_exact(2, scale_split, k_max=k_max)
            high = harvest_exact(scale_split + 1, n_max, k_max=k_max)
            windows.append(analyze_window(low, "low"))
            windows.append(analyze_window(high, "high"))
    else:
        root = data_dir if data_dir is not None else DATA_DIR
        root.mkdir(parents=True, exist_ok=True)
        split = scale_split if scale_split is not None and scale_split < n_max else None
        if split is None:
            out = root / f"harvest-{n_max}.tsv"
            tables = load_native_window(out) if out.is_file() else run_native_window(
                2,
                n_max,
                k_max=k_max,
                backend=backend,
                output=out,
            )
            windows.append(analyze_window(tables, "all"))
        else:
            low_path = root / f"harvest-{split}.tsv"
            high_path = root / f"harvest-{split + 1}-{n_max}.tsv"
            low = load_native_window(low_path) if low_path.is_file() else run_native_window(
                2,
                split,
                k_max=k_max,
                backend=backend,
                output=low_path,
            )
            high = load_native_window(high_path) if high_path.is_file() else run_native_window(
                split + 1,
                n_max,
                k_max=k_max,
                backend=backend,
                output=high_path,
            )
            windows.append(analyze_window(_merge_tables(low, high), "all"))
            windows.append(analyze_window(low, "low"))
            windows.append(analyze_window(high, "high"))
        if (
            optional_n_max is not None
            and optional_n_max > n_max
            and not any(w.get("overflow_truncated") or w.get("uncapped_truncated") for w in windows)
        ):
            ultra = run_native_window(
                n_max + 1,
                optional_n_max,
                k_max=k_max,
                backend=backend,
                output=root / f"harvest-{n_max + 1}-{optional_n_max}.tsv",
            )
            windows.append(analyze_window(ultra, "ultra"))

    by_name = {str(w["name"]): w for w in windows}
    drift = None
    if "low" in by_name and "high" in by_name:
        drift = scale_drift(
            by_name["low"].get("leftover_words_all") or by_name["low"]["leftover_words"],
            by_name["high"].get("leftover_words_all") or by_name["high"]["leftover_words"],
            int(by_name["low"]["coarse"]["leftover"]),
            int(by_name["high"]["coarse"]["leftover"]),
        )
    all_w = by_name.get("all") or windows[0]
    fixtures = {
        "E": first_certificate(FIXTURE_E[0], k_max=k_max)["word"] == FIXTURE_E[1],
        "OE": first_certificate(FIXTURE_OE[0], k_max=k_max)["word"] == FIXTURE_OE[1],
        "OOEE": first_certificate(FIXTURE_OOEE[0], k_max=k_max)["word"] == FIXTURE_OOEE[1],
        "leftover": first_certificate(FIXTURE_LEFTOVER[0], k_max=k_max)["word"]
        == FIXTURE_LEFTOVER[1],
    }
    unary_share = float(all_w["unary_share"])
    oooo_share = float(all_w["oooo_star_share"])
    only_oooo_star = unary_share >= 0.98 and oooo_share >= 0.95
    return {
        "n_max": n_max,
        "k_max": k_max,
        "backend": backend,
        "windows": windows,
        "drift": drift,
        "fixtures": fixtures,
        "fixtures_ok": all(fixtures.values()),
        "unary_share": unary_share,
        "oooo_star_share": oooo_share,
        "only_oooo_star": only_oooo_star,
        "n_leftover_types": int(all_w["n_leftover_types"]),
        "coarse": all_w["coarse"],
        "overflow_truncated": any(bool(w.get("overflow_truncated")) for w in windows),
        "uncapped_truncated": any(bool(w.get("uncapped_truncated")) for w in windows),
        "native_available": find_binary() is not None,
        "git": git_commit(),
        "letter_chain": False,
        "word_language_reopen": False,
        "halt_theorem": False,
        "atlas_language_tag": False,
        "certificate_harvest_lean": False,
        "claim": CLAIM_OBSERVED,
    }


def _merge_tables(left: dict[str, Any], right: dict[str, Any]) -> dict[str, Any]:
    out = empty_tables(int(left["k_max"]))
    out["n_begin"] = min(int(left["n_begin"]), int(right["n_begin"]))
    out["n_max"] = max(int(left["n_max"]), int(right["n_max"]))
    out["backend"] = left.get("backend")
    for key in (
        "count_skip",
        "count_e",
        "count_oe",
        "count_ooee",
        "count_leftover",
        "count_uncapped",
        "count_overflow",
        "count_long",
        "replayed_overflow",
        "replayed_uncapped",
    ):
        out[key] = int(left.get(key) or 0) + int(right.get(key) or 0)
    out["overflow_truncated"] = bool(left.get("overflow_truncated") or right.get("overflow_truncated"))
    out["uncapped_truncated"] = bool(left.get("uncapped_truncated") or right.get("uncapped_truncated"))
    for i, (a, b) in enumerate(zip(left["hist"], right["hist"], strict=True)):
        out["hist"][i] = int(a) + int(b)
        av = left["min_n"][i]
        bv = right["min_n"][i]
        if av is None:
            out["min_n"][i] = bv
        elif bv is None:
            out["min_n"][i] = av
        else:
            out["min_n"][i] = min(av, bv)
    out["long_words"] = left["long_words"] + right["long_words"]
    mins = dict(left["long_min_n"])
    for key, val in right["long_min_n"].items():
        prev = mins.get(key)
        mins[key] = val if prev is None else min(prev, val)
    out["long_min_n"] = mins
    return out


def lean_api_present() -> dict[str, bool]:
    combined = juggler_text()
    named = {name: has_named(combined, name) for name in EXISTING_LEAN}
    forbidden = {name: has_named(combined, name) for name in FORBIDDEN_THEOREMS}
    paper = JUGGLER_PAPER_BARREL.read_text(encoding="utf-8")
    return {
        "sorry_free": "sorry" not in combined and "admit" not in combined,
        **named,
        **{f"has_{name}": present for name, present in forbidden.items()},
        **{
            f"has_api_{name}": has_named(combined, name)
            for name in FORBIDDEN_NEW_API
        },
        "new_lean_file": any(path.is_file() for path in NEW_LEAN_FILES),
        "not_in_paper_barrel": all(name not in paper for name in FORBIDDEN_NEW_API),
        "no_atlas_lang": "LANG_HARVEST" not in combined and "LANG_HARVEST" not in LANGUAGE_IDS,
        "FloorPower_not_rewritten": "CycleWord" not in engine_floor_text(),
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
    if not lean_ok or not scan["fixtures_ok"] or scan["halt_theorem"] or scan["atlas_language_tag"]:
        return {"classification": CLASS_INCOMPLETE, "reason": "lean or fixture failure"}
    drift = scan.get("drift") or {}
    tv = float(drift.get("tv") or 0.0)
    if scan["only_oooo_star"] and tv < 0.08:
        return {
            "classification": CLASS_CLOSED,
            "reason": (
                "leftover histogram is only OOOO* then evens, with no new "
                "shape and no scale drift"
            ),
        }
    if tv >= 0.15:
        return {
            "classification": CLASS_GREEN,
            "reason": (
                "leftover word shares drift with scale enough to kill a "
                "product-density reading"
            ),
        }
    return {
        "classification": CLASS_PARK,
        "reason": (
            "leftover mass is a short mixed O/E-block list with small "
            "scale drift; a verification bound, not a new law"
        ),
    }


def probe_payload(
    *,
    n_max: int = TEST_N_MAX,
    k_max: int = TEST_K_MAX,
    backend: str = "python",
    scale_split: int | None = None,
    optional_n_max: int | None = None,
    data_dir: Path | None = None,
) -> dict[str, Any]:
    scan = run_probe(
        n_max=n_max,
        k_max=k_max,
        backend=backend,
        scale_split=scale_split,
        optional_n_max=optional_n_max,
        data_dir=data_dir,
    )
    lean = lean_api_present()
    decision = classify(scan, lean)
    anti = dict(ANTI_OVERCLAIM)
    anti.update(
        {
            "global_termination": False,
            "density_theorem": False,
            "atlas_language_tag": False,
            "word_atlas_recensus": False,
            "certificate_harvest_lean": False,
        }
    )
    return {
        "experiment": "juggler_certificate_harvest",
        "engine_control_layer_modified": False,
        "anti_overclaim": anti,
        "scan": scan,
        "lean": lean,
        "decision": decision,
        "search_method": (
            "first-descent certificate harvest; leftover-class histogram only; "
            f"k_max={k_max}, n<={n_max}, backend={backend}"
        ),
        "claim": CLAIM_NOT_OBSERVED if decision["classification"] != CLASS_GREEN else CLAIM_OBSERVED,
    }


def render_markdown(payload: dict[str, Any]) -> str:
    scan = payload["scan"]
    decision = payload["decision"]
    coarse = scan["coarse"]
    lines = [
        "# Juggler leftover-class certificate harvest",
        "",
        "First contracting word after Theorem 4.1 / `OOEE`. "
        "Absence is `NOT OBSERVED WITHIN SEARCH BOUND`. Not a halt theorem.",
        "",
        f"- classification: `{decision['classification']}`",
        f"- reason: {decision['reason']}",
        f"- n_max: `{scan['n_max']}`",
        f"- k_max: `{scan['k_max']}`",
        f"- backend: `{scan['backend']}`",
        f"- claim: `{payload['claim']}`",
        "",
        "## Coarse counts",
        "",
        "| class | count |",
        "|---|---|",
    ]
    for key in ("E", "OE", "OOEE", "leftover", "uncapped", "overflow", "long"):
        lines.append(f"| {key} | {coarse.get(key, 0)} |")
    lines.extend(
        [
            "",
            f"Leftover types: `{scan['n_leftover_types']}`. "
            f"Unary `O+E+` share: `{scan['unary_share']:.4f}`. "
            f"`OOOO*` share: `{scan['oooo_star_share']:.4f}`.",
            "",
        ]
    )
    drift = scan.get("drift")
    if drift:
        lines.extend(
            [
                "## Scale split",
                "",
                f"Total-variation of leftover word shares: `{drift['tv']:.4f}`. "
                f"Max abs delta: `{drift['max_abs_delta']:.4f}`.",
                "",
            ]
        )
    for window in scan["windows"]:
        lines.extend(
            [
                f"## Window `{window['name']}` ({window['n_begin']}..{window['n_max']})",
                "",
                f"Backend `{window['backend']}`. Leftover types `{window['n_leftover_types']}`.",
                "",
                "| word | count | min n | signature | unary |",
                "|---|---|---|---|---|",
            ]
        )
        for row in window["leftover_words"][:20]:
            lines.append(
                f"| `{row['word']}` | {row['count']} | {row['min_n']} | "
                f"`{row['run_signature']}` | {row['unary_block']} |"
            )
        lines.append("")
    lines.extend(
        [
            "## Anti-overclaim",
            "",
            "Not a termination theorem. Not a new atlas language. "
            "Not a density theorem unless classification is GREEN.",
            "",
        ]
    )
    return "\n".join(lines) + "\n"


def write_data_artifacts(payload: dict[str, Any]) -> None:
    DATA_DIR.mkdir(parents=True, exist_ok=True)
    scan = payload["scan"]
    (DATA_DIR / "summary.json").write_text(
        json.dumps(
            {
                "classification": payload["decision"]["classification"],
                "reason": payload["decision"]["reason"],
                "n_max": scan["n_max"],
                "coarse": scan["coarse"],
                "n_leftover_types": scan["n_leftover_types"],
                "unary_share": scan["unary_share"],
                "oooo_star_share": scan["oooo_star_share"],
                "drift": scan.get("drift"),
                "claim": payload["claim"],
                "git": scan["git"],
            },
            indent=2,
        )
        + "\n",
        encoding="utf-8",
    )
    rows = []
    for window in scan["windows"]:
        for row in window["leftover_words"]:
            rows.append({"window": window["name"], **row})
    (DATA_DIR / "leftover_histogram.json").write_text(
        json.dumps(rows, indent=2) + "\n",
        encoding="utf-8",
    )
    (DATA_DIR / "README.md").write_text(
        "# Juggler leftover-class certificate harvest\n\n"
        "Histogram only. Absence is NOT_OBSERVED_WITHIN_BOUND.\n\n"
        "Regenerate with `python -m research.juggler_sequence.certificate_harvest`.\n",
        encoding="utf-8",
    )


def write_artifacts(payload: dict[str, Any] | None = None) -> dict[str, Any]:
    data = payload if payload is not None else probe_payload()
    for window in data.get("scan", {}).get("windows", []):
        window.pop("leftover_words_all", None)
    JSON_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(data, indent=2) + "\n", encoding="utf-8")
    DOC_PATH.write_text(render_markdown(data), encoding="utf-8")
    write_data_artifacts(data)
    return data


def main() -> None:
    backend = "cuda" if find_binary() is not None else "python"
    payload = probe_payload(
        n_max=SCIENCE_N_MAX,
        k_max=SCIENCE_K_MAX,
        backend=backend if backend == "cuda" else "python",
        scale_split=SCALE_SPLIT,
        optional_n_max=None,
        data_dir=DATA_DIR,
    )
    write_artifacts(payload)
    print(payload["decision"]["classification"])
    print(payload["decision"]["reason"])
    print(payload["scan"]["coarse"])


if __name__ == "__main__":
    main()
