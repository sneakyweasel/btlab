"""Scientific census report. Computational observation, not a prohibition."""

from __future__ import annotations

import json
from collections import Counter
from pathlib import Path
from typing import Any

from research.juggler_sequence.atlas.api import build, factor_set
from research.juggler_sequence.atlas.packed import split_word_id, unpack_word
from research.juggler_sequence.atlas.query import continuation_histogram
from research.juggler_sequence.atlas.schema import (
    CLAIM_CLOSED,
    CLAIM_NOT_OBSERVED,
    CLAIM_OBSERVED,
    LANG_PE_CERTIFIED,
    LANG_PE_RUN,
    LANG_REALIZABLE,
    PE_CERTIFIED,
    STATUS_FOUND,
)
from research.juggler_sequence.atlas.storage import DEFAULT_DATA_DIR, connect
from research.juggler_sequence.normalized_defect import odd_even_word
from research.juggler_sequence.itinerary_language import (
    LATE_PE_FACTORS,
    collect_slices,
    factors,
    grammar_concatenations,
    legal_pe_blocks,
)


def realized_by_length(con, experiment_id: str, k_max: int) -> dict[int, int]:
    rows = con.execute(
        """
        SELECT (word_id >> 32) AS length, COUNT(*)
        FROM realizers
        WHERE experiment_id = ? AND realization_status = ?
        GROUP BY length
        ORDER BY length
        """,
        (experiment_id, STATUS_FOUND),
    ).fetchall()
    out = {r: 0 for r in range(1, k_max + 1)}
    for length, count in rows:
        out[int(length)] = int(count)
    return out


def pe_words_by_length(con, experiment_id: str, language_id: str) -> dict[int, int]:
    rows = con.execute(
        """
        SELECT word_id FROM pe_records
        WHERE experiment_id = ? AND language_id = ?
        """,
        (experiment_id, language_id),
    ).fetchall()
    counts: Counter[int] = Counter()
    for (wid,) in rows:
        length, _ = split_word_id(int(wid))
        counts[length] += 1
    return dict(sorted(counts.items()))


def pe_run_records_a_k(con, experiment_id: str) -> list[dict[str, Any]]:
    rows = con.execute(
        """
        SELECT word_id, min_n, end_state, pe_definition
        FROM pe_records
        WHERE experiment_id = ? AND language_id = ?
        ORDER BY min_n
        """,
        (experiment_id, LANG_PE_CERTIFIED),
    ).fetchall()
    best: dict[int, dict[str, Any]] = {}
    for wid, min_n, end_state, pe_def in rows:
        length, packed = split_word_id(int(wid))
        rec = best.get(length)
        if rec is None or min_n < rec["min_n"]:
            best[length] = {
                "k": length,
                "min_n": min_n,
                "word": unpack_word(length, packed),
                "end_state": end_state,
                "pe_definition": pe_def,
            }
    return [best[k] for k in sorted(best)]


def grammar_factors(r_max: int) -> dict[int, set[str]]:
    words = grammar_concatenations()
    slices = collect_slices(words, r_max)
    return {r: set(slices["fact"][r]) for r in range(1, r_max + 1)}


def block_factors(r_max: int) -> dict[int, set[str]]:
    words = [odd_even_word(a, b) for a, b in legal_pe_blocks()]
    out: dict[int, set[str]] = {r: set() for r in range(1, r_max + 1)}
    for word in words:
        for r in range(1, min(len(word), r_max) + 1):
            out[r] |= factors(word, r)
    return out


def science_report(
    *,
    experiment_id: str,
    data_dir: Path,
    r_max: int,
) -> dict[str, Any]:
    con = connect(data_dir)
    try:
        exp = con.execute(
            "SELECT k_max, n_max, record_counts FROM experiments WHERE experiment_id = ?",
            (experiment_id,),
        ).fetchone()
        if exp is None:
            raise ValueError(f"unknown experiment {experiment_id}")
        k_max, n_max, raw_counts = int(exp[0]), int(exp[1]), exp[2]
        realized = realized_by_length(con, experiment_id, k_max)
        pe_blocks = pe_words_by_length(con, experiment_id, LANG_PE_CERTIFIED)
        pe_runs = pe_words_by_length(con, experiment_id, LANG_PE_RUN)
        a_k = pe_run_records_a_k(con, experiment_id)
        cont = continuation_histogram(
            LANG_REALIZABLE, experiment_id=experiment_id, data_dir=data_dir
        )
    finally:
        con.close()

    p_r = {
        r: len(factor_set(LANG_REALIZABLE, r, experiment_id=experiment_id, data_dir=data_dir))
        for r in range(1, r_max + 1)
    }
    p_pe = {
        r: len(factor_set(LANG_PE_CERTIFIED, r, experiment_id=experiment_id, data_dir=data_dir))
        for r in range(1, r_max + 1)
    }
    p_pe_run = {
        r: len(factor_set(LANG_PE_RUN, r, experiment_id=experiment_id, data_dir=data_dir))
        for r in range(1, r_max + 1)
    }
    grammar = grammar_factors(r_max)
    blocks = block_factors(r_max)
    missing_vs_grammar = {}
    missing_vs_blocks = {}
    missing_all_binary = {}
    for r in range(1, r_max + 1):
        observed_run = set(
            factor_set(LANG_PE_RUN, r, experiment_id=experiment_id, data_dir=data_dir)
        )
        observed_pe = set(
            factor_set(LANG_PE_CERTIFIED, r, experiment_id=experiment_id, data_dir=data_dir)
        )
        universe = {
            "".join("O" if (m >> i) & 1 else "E" for i in range(r)) for m in range(1 << r)
        }
        missing_vs_grammar[r] = sorted(grammar[r] - observed_run)
        missing_vs_blocks[r] = sorted(blocks[r] - observed_pe)
        missing_all_binary[r] = sorted(universe - observed_run)
    return {
        "experiment_id": experiment_id,
        "k_max": k_max,
        "n_max": n_max,
        "record_counts": json.loads(raw_counts) if raw_counts else {},
        "realized_by_length": realized,
        "pe_certified_by_length": pe_blocks,
        "pe_run_by_length": pe_runs,
        "a_k": a_k,
        "p_r": p_r,
        "p_pe": p_pe,
        "p_pe_run": p_pe_run,
        "missing_pe_run_vs_grammar": missing_vs_grammar,
        "missing_pe_vs_blocks": missing_vs_blocks,
        "missing_all_binary_in_pe_run": missing_all_binary,
        "late_known_window_factors": LATE_PE_FACTORS,
        "continuations": cont,
        "claims": {
            "realized": CLAIM_OBSERVED,
            "missing": CLAIM_NOT_OBSERVED,
            "closed_itinerary_language": CLAIM_CLOSED,
            "pe_definition": PE_CERTIFIED,
        },
    }


def write_science_markdown(report: dict[str, Any], path: Path) -> None:
    lines = [
        "# Juggler word atlas scientific census",
        "",
        "This is a computational observation under a search bound. It is not a",
        "termination theorem and not a forbidden-factor law.",
        "",
        f"- experiment_id: `{report['experiment_id']}`",
        f"- k_max: {report['k_max']}",
        f"- n_max: {report['n_max']}",
        f"- PE definition: `{PE_CERTIFIED}`",
        f"- realized itineraries: {CLAIM_OBSERVED}",
        f"- missing words: {CLAIM_NOT_OBSERVED}",
        f"- word-language branch: {CLAIM_CLOSED} (`JUGGLER_LANGUAGE_IS_KNOWN_GRAMMAR`)",
        "",
        "## Realizable words by length",
        "",
        "| k | realized | universe 2^k |",
        "|---|----------|--------------|",
    ]
    for k, count in report["realized_by_length"].items():
        lines.append(f"| {k} | {count} | {1 << k} |")
    lines += [
        "",
        "## Factor complexity",
        "",
        "| r | p(r) REALIZABLE | p_PE(r) PE_CERTIFIED | p_PE_run(r) |",
        "|---|-----------------|----------------------|-------------|",
    ]
    for r in sorted(report["p_r"]):
        lines.append(
            f"| {r} | {report['p_r'][r]} | {report['p_pe'][r]} | {report['p_pe_run'][r]} |"
        )
    lines += [
        "",
        "## Grammar-legal PE-run factors not observed within bound",
        "",
        "These are **not** certified forbidden words.",
        "",
    ]
    any_missing = False
    for r, words in report["missing_pe_run_vs_grammar"].items():
        if not words:
            continue
        any_missing = True
        lines.append(f"- r={r} ({CLAIM_NOT_OBSERVED}): `{', '.join(words)}`")
    if not any_missing:
        lines.append(
            f"- none in r=1..{max(report['missing_pe_run_vs_grammar'])} "
            f"({CLAIM_OBSERVED} vs the known O^a E^b concatenations)"
        )
    lines += [
        "",
        "## Does PE-run contain every binary factor?",
        "",
        "No, and isolated-odd factors such as `EOE` are the known block grammar,",
        "not a new law. Remaining absences are listed only as "
        f"{CLAIM_NOT_OBSERVED}.",
        "",
    ]
    for r, words in report["missing_all_binary_in_pe_run"].items():
        if r > 6:
            lines.append(f"- r={r}: {len(words)} binary words {CLAIM_NOT_OBSERVED}")
        elif words:
            shown = ", ".join(words[:16])
            extra = "" if len(words) <= 16 else f" … +{len(words) - 16}"
            lines.append(f"- r={r}: `{shown}`{extra}")
    lines += [
        "",
        "## PE-run record a_k",
        "",
        "Minimum observed start of a PE_CERTIFIED word of length k. Failure to",
        "find a longer run is not a finite PE-run bound.",
        "",
        "| k | min_n | word | pe_definition |",
        "|---|-------|------|---------------|",
    ]
    for row in report["a_k"]:
        lines.append(
            f"| {row['k']} | {row['min_n']} | `{row['word']}` | {row['pe_definition']} |"
        )
    lines += [
        "",
        "## Continuation histogram (REALIZABLE)",
        "",
        "| length | d | count |",
        "|--------|---|-------|",
    ]
    for row in report["continuations"]:
        lines.append(f"| {row['length']} | {row['d']} | {row['count']} |")
    lines += [
        "",
        "## Closed-branch reminder",
        "",
        "Do not promote a linguistic rewrite of a≥2 or 3^{#O}>2^{|w|}.",
        "Known late window factors `EEEEEE` (14237) and `OEEEEO` (9157) stay",
        "window artefacts, not surviving forbidden-factor laws.",
        "",
    ]
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def run_science(
    *,
    k_max: int = 20,
    n_max: int = 100_000_000,
    pe_n_max: int | None = None,
    backend: str = "cuda",
    data_dir: Path | None = None,
    r_max: int = 8,
) -> dict[str, Any]:
    root = Path(data_dir) if data_dir is not None else DEFAULT_DATA_DIR
    print(
        f"juggler-atlas science k_max={k_max} n_max={n_max} "
        f"pe_n_max={pe_n_max} backend={backend}",
        flush=True,
    )
    payload = build(
        k_max=k_max,
        n_max=n_max,
        backend=backend,
        pe_n_max=pe_n_max,
        data_dir=root,
    )
    eid = payload["experiment_id"]
    report = science_report(experiment_id=eid, data_dir=root, r_max=r_max)
    report["build"] = {
        "backend": payload.get("backend"),
        "pe_n_max": payload.get("pe_n_max"),
        "native": payload.get("native"),
        "record_counts": payload.get("record_counts"),
    }
    md = root / "summaries" / f"{eid}.md"
    js = root / "summaries" / f"{eid}.json"
    write_science_markdown(report, md)
    js.parent.mkdir(parents=True, exist_ok=True)
    js.write_text(json.dumps(report, indent=2, sort_keys=True), encoding="utf-8")
    report["markdown_path"] = str(md)
    report["json_path"] = str(js)
    return report
