"""Explicit external review clients and jobs. Never imported by MCP discovery."""
from __future__ import annotations

import datetime
import random
from collections import defaultdict
from concurrent.futures import ThreadPoolExecutor
from typing import Any, Callable
from . import identities as _fp_identities
from . import matching as _fp_matching
from . import verdicts as _fp_verdicts


def jev_ask(model: str = "jev-latest", timeout: float = 60.0) -> _fp_verdicts.Ask:
    """The real asker: one Choice question per call over the TypeSafe SDK.

    The SDK reads ``TYPESAFE_API_KEY`` from the environment.  Imported here rather than at
    the top so that the index, the scorer and the tests need neither the package nor a key.
    """
    try:
        from typesafe_sdk import Choice, TypeSafeClient
    except ImportError as exc:  # pragma: no cover - depends on the environment
        raise SystemExit(
            "typesafe-sdk is not installed: pip install typesafe-sdk, then set TYPESAFE_API_KEY"
        ) from exc
    client = TypeSafeClient(timeout=timeout)

    def ask(state: dict[str, Any], instructions: str,
            criteria: dict[str, str | None]) -> dict[str, Any]:
        response = client.system_one(
            state=state,
            questions={"pick": Choice(instructions=instructions, criteria=criteria)},
            model=model,
        )
        answer = response.choices["pick"]
        return {
            "choice": answer.choice,
            "confidence": float(answer.confidence),
            "probabilities": {k: float(v) for k, v in answer.probabilities.items()},
            "model": response.model,
            "input_tokens": int(response.usage.input_tokens),
        }

    return ask


def _run(items: list[Any], fn: Callable[[Any], Any], workers: int) -> list[Any]:
    if workers > 1 and len(items) > 1:
        with ThreadPoolExecutor(workers) as pool:
            return list(pool.map(fn, items))
    return [fn(item) for item in items]


def jev_propose(
    index: dict[str, Any], ledger: list[dict[str, Any]], ask: _fp_verdicts.Ask,
    cached: dict[str, Any] | None = None, refresh: bool = False,
    limit: int | None = None, workers: int = 4,
) -> dict[str, Any]:
    """Ask Jev, once per unresolved row, which of its file's theorems states the row.

    Every row the scorer queues is asked, not only the ones the scorer is confident about:
    on the 21 September 2026 sample the scorer fired on ten of thirty rows and Jev put the
    recorded declaration first on nineteen, so the rows the scorer rates low are where Jev
    earns its keep.  Verdicts are cached under ``jev_key``: a row whose key still matches is
    reused unless ``refresh``, a row resolved since is dropped, and ``limit`` caps how many
    are asked in one run, the rest keeping whatever verdict they had.  Cost is input tokens
    only, reported in ``totals``.
    """
    prior = (cached or {}).get("rows", {})
    rows: dict[str, Any] = {}
    pending: list[tuple[dict[str, Any], list[dict[str, Any]], str, int, Any]] = []
    for row, cands, _defs in _fp_matching._queue(index, ledger):
        if not cands:
            continue
        offer = _fp_verdicts.jev_shortlist(row, cands)
        key = _fp_verdicts.jev_key(row, offer)
        old = prior.get(row["id"])
        if old is not None and old.get("key") == key and not refresh:
            rows[row["id"]] = old
            continue
        pending.append((row, offer, key, len(cands), old))
    todo = pending if limit is None else pending[:limit]
    for row, _offer, _key, _in_file, old in pending[len(todo):]:
        if old is not None:
            rows[row["id"]] = old
    today = datetime.date.today().isoformat()

    def one(
        item: tuple[dict[str, Any], list[dict[str, Any]], str, int, Any]
    ) -> tuple[str, dict[str, Any], int]:
        row, offer, key, in_file, _old = item
        state, criteria = _fp_verdicts.jev_question(row, offer)
        v = ask(state, _fp_verdicts.JEV_INSTRUCTIONS, criteria)
        ranked = sorted(v["probabilities"].items(), key=lambda kv: (-kv[1], kv[0]))[:5]
        verdict = {
            "key": key,
            "model": v["model"],
            "asked": today,
            "choice": v["choice"],
            "confidence": round(float(v["confidence"]), 3),
            "probabilities": {k: round(float(p), 3) for k, p in ranked},
            "shortlist": len(offer),
            "in_file": in_file,
        }
        return row["id"], verdict, int(v.get("input_tokens", 0))

    tokens = 0
    for rid, verdict, used in _run(todo, one, workers):
        rows[rid] = verdict
        tokens += used
    totals = {"answered": len(rows), "asked_now": len(todo),
              "reused": len(rows) - len(todo), "input_tokens": tokens}
    return _fp_verdicts._jev_record(rows, (cached or {}).get("calibration"), totals,
                       (cached or {}).get("coverage"))


def jev_calibrate(
    index: dict[str, Any], ledger: list[dict[str, Any]], ask: _fp_verdicts.Ask,
    sample: int | None = None, seed: int = 0, workers: int = 4,
) -> dict[str, Any]:
    """Score Jev the way ``calibrate`` scores the scorer: on rows whose answer is recorded.

    Same population -- rows naming exactly one declaration, in a file offering at least two
    theorems -- and the recorded declaration is offered like any other, so the measurement is
    of the same question ``jev_propose`` asks.  Stored with its date, model, sample and seed
    in the verdict record; the digest quotes the stored figures and never a hardcoded one.
    """
    by_file: dict[str, list[dict[str, Any]]] = defaultdict(list)
    for d in index["declarations"]:
        if d["kind"] in ("theorem", "lemma"):
            by_file[d["file"]].append(d)
    resolved = [r for r in ledger if len(_fp_identities.row_decls(r)) == 1]
    eligible: list[tuple[dict[str, Any], list[dict[str, Any]]]] = []
    for row in resolved:
        cands = by_file.get(_fp_identities.lean_key(row.get("lean")), [])
        if len(cands) >= 2 and any(d["name"] == _fp_identities.row_decls(row)[0] for d in cands):
            eligible.append((row, cands))
    chosen = eligible
    if sample is not None and sample < len(eligible):
        chosen = random.Random(seed).sample(eligible, sample)

    def one(item: tuple[dict[str, Any], list[dict[str, Any]]]) -> dict[str, Any]:
        row, cands = item
        truth = _fp_identities.row_decls(row)[0]
        offer = _fp_verdicts.jev_shortlist(row, cands)
        state, criteria = _fp_verdicts.jev_question(row, offer)
        v = ask(state, _fp_verdicts.JEV_INSTRUCTIONS, criteria)
        ranked = [k for k, _ in sorted(v["probabilities"].items(),
                                       key=lambda kv: (-kv[1], kv[0]))]
        sw = _fp_matching.words(row["statement"])
        scorer = sorted(cands, key=lambda d: _fp_matching.similarity(sw, d), reverse=True)[0]["name"]
        return {
            "id": row["id"], "truth": truth, "choice": v["choice"],
            "confidence": round(float(v["confidence"]), 3),
            "top3": truth in ranked[:3], "offered": any(d["name"] == truth for d in offer),
            "scorer": scorer, "model": v["model"],
            "input_tokens": int(v.get("input_tokens", 0)),
        }

    results = _run(chosen, one, workers)
    confident = [r for r in results if r["confidence"] >= _fp_verdicts.JEV_REVIEW]
    misses = [{"id": r["id"], "truth": r["truth"], "choice": r["choice"],
               "confidence": r["confidence"], "scorer": r["scorer"]}
              for r in results if r["choice"] != r["truth"]]
    return {
        "asked": datetime.date.today().isoformat(),
        "model": sorted({r["model"] for r in results})[-1] if results else None,
        "resolved": len(resolved),
        "eligible": len(eligible),
        "sampled": len(results),
        "seed": seed,
        "top1": sum(r["choice"] == r["truth"] for r in results),
        "top3": sum(r["top3"] for r in results),
        "none": sum(r["choice"] == _fp_verdicts.JEV_NONE for r in results),
        "truth_not_offered": sum(not r["offered"] for r in results),
        "confident": len(confident),
        "confident_correct": sum(r["choice"] == r["truth"] for r in confident),
        "scorer_top1": sum(r["scorer"] == r["truth"] for r in results),
        "input_tokens": sum(r["input_tokens"] for r in results),
        "misses": sorted(misses, key=lambda m: (-m["confidence"], m["id"])),
    }


def jev_ask_nouls(model: str = "jev-latest", timeout: float = 60.0) -> _fp_verdicts.AskNouls:
    """The real asker for the coverage questions: several Nouls over one state per call."""
    try:
        from typesafe_sdk import Noul, TypeSafeClient
    except ImportError as exc:  # pragma: no cover - depends on the environment
        raise SystemExit(
            "typesafe-sdk is not installed: pip install typesafe-sdk, then set TYPESAFE_API_KEY"
        ) from exc
    client = TypeSafeClient(timeout=timeout)

    def ask(state: dict[str, Any], questions: dict[str, str]) -> dict[str, Any]:
        response = client.system_one(
            state=state,
            questions={qid: Noul(instructions=text) for qid, text in questions.items()},
            model=model,
        )
        return {
            "nouls": {qid: float(response.nouls[qid].noul) for qid in questions},
            "model": response.model,
            "input_tokens": int(response.usage.input_tokens),
        }

    return ask


def _no_ask(state: dict[str, Any], questions: dict[str, str]) -> dict[str, Any]:
    raise RuntimeError("no question may be asked in this run")


def jev_coverage(
    index: dict[str, Any], ledger: list[dict[str, Any]], ask: _fp_verdicts.AskNouls,
    cached: dict[str, Any] | None = None, refresh: bool = False,
    limit: int | None = None, only: set[str] | None = None, workers: int = 4,
) -> dict[str, Any]:
    """Ask Jev, once per resolved row, whether the declarations it names cover its claim.

    The retag rule -- ``EXACT — LEAN VERIFIED`` only when the Lean theorem covers the English
    statement -- has had no mechanism behind it: the proposal digest names the two ways a join
    records a part as the whole and leaves both to the reader.  This asks the rule as four
    Nouls over the claim and every declaration the row names, and caches the answers under
    ``coverage_key`` in the verdict record, beside the offer verdicts.  ``only`` restricts a
    run to some row ids, which is how one retag is checked; ``limit`` and ``refresh`` are as in
    ``jev_propose``, and ``limit=0`` rewrites the artifacts from the cache without asking.
    Advisory: the ledger is never written.
    """
    record = dict(cached or {})
    prior = (record.get("coverage") or {}).get("rows", {})
    rows: dict[str, Any] = {}
    pending: list[tuple[dict[str, Any], list[dict[str, Any]], str, Any]] = []
    unfound: dict[str, list[str]] = {}
    for row, decls, missing in _fp_verdicts._resolved(index, ledger):
        old = prior.get(row["id"])
        if missing:
            unfound[row["id"]] = missing
            continue
        if only is not None and row["id"] not in only:
            if old is not None:
                rows[row["id"]] = old
            continue
        key = _fp_verdicts.coverage_key(row, decls)
        if old is not None and old.get("key") == key and not refresh:
            rows[row["id"]] = old
            continue
        pending.append((row, decls, key, old))
    todo = pending if limit is None else pending[:limit]
    for row, _decls, _key, old in pending[len(todo):]:
        if old is not None:
            rows[row["id"]] = old
    today = datetime.date.today().isoformat()

    def one(
        item: tuple[dict[str, Any], list[dict[str, Any]], str, Any]
    ) -> tuple[str, dict[str, Any], int]:
        row, decls, key, _old = item
        v = ask(_fp_verdicts.coverage_state(row, decls), _fp_verdicts.JEV_COVERAGE_QUESTIONS)
        verdict: dict[str, Any] = {
            "key": key, "model": v["model"], "asked": today,
            "decls": [d["name"] for d in decls],
        }
        for qid in _fp_verdicts.JEV_COVERAGE_QUESTIONS:
            verdict[qid] = round(float(v["nouls"][qid]), 3)
        return row["id"], verdict, int(v.get("input_tokens", 0))

    tokens = 0
    for rid, verdict, used in _run(todo, one, workers):
        rows[rid] = verdict
        tokens += used
    earlier = (record.get("coverage") or {}).get("asked")
    coverage = {
        "asked": today if todo else earlier,
        "totals": {"answered": len(rows), "asked_now": len(todo),
                   "reused": len(rows) - len(todo), "input_tokens": tokens,
                   "unfound": len(unfound)},
        "rows": dict(sorted(rows.items())),
    }
    return _fp_verdicts._jev_record(record.get("rows", {}), record.get("calibration"),
                       record.get("totals", dict(_fp_verdicts._EMPTY_TOTALS)), coverage)
