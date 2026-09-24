"""Explicit CLI dispatch and artifact writers; queries delegate to read-only catalogues."""
from __future__ import annotations

import argparse
import collections
import io
import json
import sys
from typing import Any
from . import advisory as _fp_advisory
from . import graph as _fp_graph
from . import matching as _fp_matching
from . import reports as _fp_reports
from . import source as _fp_source
from . import verdicts as _fp_verdicts
from . import workspace as _fp_workspace


def _write_jev_artifacts(index: dict[str, Any], ledger: list[dict[str, Any]],
                         record: dict[str, Any], *, persist_evidence: bool = True) -> None:
    """Keep advisory evidence in Git; reproducible views belong in the local cache."""
    if persist_evidence:
        _fp_workspace.JEV.parent.mkdir(parents=True, exist_ok=True)
        _fp_workspace.JEV.write_text(_fp_source.render(record), encoding="utf-8")
    _fp_workspace.PROPOSALS.parent.mkdir(parents=True, exist_ok=True)
    _fp_workspace.PROPOSALS.write_text(_fp_source.render(_fp_matching.propose(index, ledger, jev=record)), encoding="utf-8")
    _fp_workspace.REVIEW.parent.mkdir(parents=True, exist_ok=True)
    _fp_workspace.REVIEW.write_text(_fp_reports.review_digest(index, ledger, jev=record), encoding="utf-8")
    _fp_workspace.COVERAGE.parent.mkdir(parents=True, exist_ok=True)
    _fp_workspace.COVERAGE.write_text(_fp_reports.coverage_digest(index, ledger, jev=record), encoding="utf-8")
    for path in ((_fp_workspace.JEV,) if persist_evidence else ()) + (_fp_workspace.PROPOSALS, _fp_workspace.REVIEW, _fp_workspace.COVERAGE):
        print(f"wrote {path.relative_to(_fp_workspace.ROOT).as_posix()}")


def main(argv: list[str] | None = None) -> int:
    arguments = list(sys.argv[1:] if argv is None else argv)
    if arguments[:1] == ['semantic']:
        from formalpedia_semantic import main as semantic_main
        return semantic_main(arguments[1:])
    ap = argparse.ArgumentParser(description="A theorem index over the Lean sources.")
    sub = ap.add_subparsers(dest="cmd", required=True)
    sub.add_parser('semantic', help='compiled types, structural search, dependencies and snapshot differences')
    p = sub.add_parser("build", help="rebuild the index")
    p.add_argument("--check", action="store_true", help="check freshness without writing")
    sub.add_parser("status", help="live catalogue health and saved-index freshness")
    p = sub.add_parser("claim", help="an exact ledger claim and its declaration statements")
    p.add_argument("id")
    p = sub.add_parser("search", help="ranked search across names, statements, docs and exact claims")
    p.add_argument("text")
    p.add_argument("--limit", type=int, default=20)
    p.add_argument("--offset", type=int, default=0)
    p.add_argument("--namespace")
    p.add_argument("--module")
    p.add_argument("--kind")
    p.add_argument("--ledger-id")
    p.add_argument("--include-private", action="store_true")
    p.add_argument("--include-deprecated", action="store_true")
    p.add_argument("--scope", choices=['active', 'archive', 'all'], default='active')
    p.add_argument("--json", action="store_true")
    p = sub.add_parser("show", help="one declaration; ambiguous short names return alternatives")
    p.add_argument("name")
    p.add_argument("--module")
    p.add_argument("--include-private", action="store_true")
    p = sub.add_parser("impact", help="modules rebuilt by a change to this module or file")
    p.add_argument("target")
    p = sub.add_parser("mathlib", help="search Mathlib through Loogle; hits checked against the pinned Mathlib")
    p.add_argument("query", help='a name, type pattern or subexpression, e.g. "Real.sqrt, _ * _"')
    p.add_argument("--limit", type=int, default=20)
    p.add_argument("--json", action="store_true")
    p = sub.add_parser("audits", help="recorded #print axioms artifacts: consistency and coverage")
    p.add_argument("--limit", type=int, default=50)
    p.add_argument("--offset", type=int, default=0)
    p.add_argument("--check", action="store_true", help="exit 1 when any artifact problem is found")
    sub.add_parser("dag", help="rebuild the claim graph over ledger-carrying modules")
    sub.add_parser("propose", help="rank declarations for rows that name none")
    sub.add_parser("papers", help="each manuscript's reachable trust surface")
    sub.add_parser("review", help="write the confident proposals as a readable digest")
    p = sub.add_parser("jev-propose",
                       help="ask Jev which theorem each unresolved row means; verdicts are cached")
    p.add_argument("--model", default="jev-latest")
    p.add_argument("--refresh", action="store_true",
                   help="ask again where a cached verdict still matches")
    p.add_argument("--limit", type=int, default=None, help="ask about at most this many rows now")
    p.add_argument("--workers", type=int, default=4)
    p = sub.add_parser("jev-calibrate",
                       help="score Jev against rows whose declaration is recorded")
    p.add_argument("--model", default="jev-latest")
    p.add_argument("--sample", type=int, default=None,
                   help="rows to draw; every eligible row if omitted")
    p.add_argument("--seed", type=int, default=0)
    p.add_argument("--workers", type=int, default=4)
    p = sub.add_parser("jev-coverage",
                       help="ask Jev whether each resolved row's declarations cover its claim")
    p.add_argument("--model", default="jev-latest")
    p.add_argument("--refresh", action="store_true",
                   help="ask again where a cached verdict still matches")
    p.add_argument("--limit", type=int, default=None,
                   help="ask about at most this many rows now; 0 rewrites from the cache")
    p.add_argument("--rows", default=None,
                   help="comma-separated ledger ids to ask about, e.g. the row being retagged")
    p.add_argument("--workers", type=int, default=4)
    args = ap.parse_args(argv)

    if args.cmd == "mathlib":
        from . import mathlib as _fp_mathlib
        try:
            result = _fp_mathlib.search(args.query, limit=args.limit)
        except ValueError as exc:
            print(str(exc), file=sys.stderr)
            return 2
        if args.json:
            print(_fp_source.render(result), end="")
        else:
            print(f"Loogle ({result['status']}); pinned Mathlib {result['mathlib_pinned_rev']}")
            for hit in result.get("hits", []):
                print(f"{hit['name']}  [{hit['module']}; pinned: {hit['pinned']['status']}]")
                print(f"    {hit['type']}")
            for key in ("reason", "remedy"):
                if result.get(key):
                    print(f"{key}: {result[key]}")
            if result.get("suggestions"):
                print("suggestions: " + "; ".join(result["suggestions"]))
            print(result["limitations"])
        return 0 if result["status"] in {"found", "no_hits"} else 1

    if args.cmd in {"search", "show", "status", "claim", "impact", "audits"}:
        from formalpedia_catalog import Catalogue
        catalogue = Catalogue()
        try:
            if args.cmd == "search":
                result = catalogue.search(args.text, namespace=args.namespace, module=args.module,
                    kind=args.kind, ledger_id=args.ledger_id, include_private=args.include_private,
                    include_deprecated=args.include_deprecated, limit=args.limit, offset=args.offset,
                    scope=args.scope)
                if args.json:
                    print(_fp_source.render(result), end="")
                else:
                    for row in result["results"]:
                        print(f"{row['id']}  [{row['kind']}; source {row['trust']}]  {row['file']}:{row['line']}")
                        if row["doc"]:
                            print(f"    {row['doc']}")
                    print(f"-- {result['total']} matching; next offset: {result['next_offset']}")
                return 0
            if args.cmd == "show":
                result = catalogue.show(args.name, module=args.module,
                                        include_private=args.include_private)
            elif args.cmd == "claim":
                result = catalogue.claim(args.id)
            elif args.cmd == "impact":
                result = catalogue.impact(args.target)
            elif args.cmd == "audits":
                result = catalogue.audits(limit=args.limit, offset=args.offset)
                print(_fp_source.render(result), end="")
                return 1 if args.check and result["problem_count"] else 0
            else:
                result = catalogue.status()
            print(_fp_source.render(result), end="")
            return 2 if result.get("status") == "ambiguous" else 1 if result.get("status") == "not_found" else 0
        except (ValueError, RuntimeError) as exc:
            print(str(exc), file=sys.stderr)
            return 2

    if args.cmd == "jev-coverage":
        index = _fp_source.load()
        ledger = json.load(io.open(_fp_workspace.LEDGER, encoding="utf-8"))
        only = {s.strip() for s in args.rows.split(",") if s.strip()} if args.rows else None
        ask = _fp_advisory._no_ask if args.limit == 0 else _fp_advisory.jev_ask_nouls(args.model)
        record = _fp_advisory.jev_coverage(index, ledger, ask, cached=_fp_verdicts.load_jev(), refresh=args.refresh,
                              limit=args.limit, only=only, workers=args.workers)
        _write_jev_artifacts(index, ledger, record, persist_evidence=args.limit != 0)
        t = record["coverage"]["totals"]
        print(f"{t['answered']} resolved rows carry a coverage verdict: asked {t['asked_now']} "
              f"now ({t['input_tokens']} input tokens), reused {t['reused']}"
              + (f"; {t['unfound']} rows name a declaration the index lacks" if t["unfound"]
                 else ""))
        rows = _fp_verdicts.coverage_rows(index, ledger, record)
        bands = collections.Counter(r["band"] for r in rows if r["band"])
        print(f"  {bands['covered']} covered, {bands['doubtful']} doubtful, "
              f"{bands['not_covered']} not covered; {sum(r['flagged'] for r in rows)} listed "
              f"for review, {sum(r['verdict'] == 'stale' for r in rows)} stale")
        for r in rows:
            if only and r["id"] in only and r["verdict"] != "unasked":
                reading = _fp_verdicts.JEV_COVERAGE_READINGS.get(r["reading"] or "", "no failure mode")
                print(f"  {r['id']}: {r['band']}; covers {r['covers']}, claim broader "
                      f"{r['claim_broader']}, declaration narrower {r['decl_narrower']}, "
                      f"different result {r['different_result']} -> {reading}")
        return 0

    if args.cmd == "jev-propose":
        index = _fp_source.load()
        ledger = json.load(io.open(_fp_workspace.LEDGER, encoding="utf-8"))
        record = _fp_advisory.jev_propose(index, ledger, _fp_advisory.jev_ask(args.model), cached=_fp_verdicts.load_jev(),
                             refresh=args.refresh, limit=args.limit, workers=args.workers)
        _write_jev_artifacts(index, ledger, record)
        t = record["totals"]
        print(f"{t['answered']} rows carry a verdict: asked {t['asked_now']} now "
              f"({t['input_tokens']} input tokens), reused {t['reused']}")
        merged = _fp_matching.propose(index, ledger, jev=record)
        s = merged["jev"] or {}
        print(f"  {s.get('picks', 0)} picks ({s.get('confident', 0)} at or above {_fp_verdicts.JEV_REVIEW}), "
              f"{s.get('none', 0)} none of these, {s.get('agree_with_scorer', 0)} agreeing with "
              f"the scorer; {merged['worth_reviewing']} rows now worth reviewing")
        return 0

    if args.cmd == "jev-calibrate":
        index = _fp_source.load()
        ledger = json.load(io.open(_fp_workspace.LEDGER, encoding="utf-8"))
        cal = _fp_advisory.jev_calibrate(index, ledger, _fp_advisory.jev_ask(args.model), sample=args.sample,
                            seed=args.seed, workers=args.workers)
        cached = _fp_verdicts.load_jev()
        record = _fp_verdicts._jev_record((cached or {}).get("rows", {}), cal,
                             (cached or {}).get("totals", dict(_fp_verdicts._EMPTY_TOTALS)),
                             (cached or {}).get("coverage"))
        _write_jev_artifacts(index, ledger, record)
        print(f"{cal['sampled']} of {cal['eligible']} eligible rows ({cal['model']}, seed "
              f"{cal['seed']}, {cal['input_tokens']} input tokens)")
        print(f"  recorded declaration first: {cal['top1']}; in the top three: {cal['top3']}; "
              f"none of these: {cal['none']}; not offered: {cal['truth_not_offered']}")
        print(f"  at or above {_fp_verdicts.JEV_REVIEW}: {cal['confident_correct']} of {cal['confident']} "
              f"right; scorer first candidate right: {cal['scorer_top1']}")
        for m in cal["misses"]:
            print(f"    miss {m['id']}: recorded {m['truth']}, Jev {m['choice']} "
                  f"({m['confidence']}), scorer {m['scorer']}")
        return 0

    if args.cmd == "build":
        index = _fp_source.build()
        if args.check:
            if not _fp_workspace.INDEX.exists() or _fp_workspace.INDEX.read_text(encoding="utf-8") != _fp_source.render(index):
                print("Saved index is stale; run python tools/formalpedia.py build", file=sys.stderr)
                return 1
            print("Saved index matches the current Lean sources and ledger.")
            return 0
        _fp_workspace.INDEX.parent.mkdir(parents=True, exist_ok=True)
        _fp_workspace.INDEX.write_text(_fp_source.render(index), encoding="utf-8")
        t = index["totals"]
        print(f"{t['declarations']} declarations in {t['modules']} modules")
        print(f"  trust: {t['trust']}")
        print(f"  declarations under a ledger row: {t['declarations_with_a_ledger_row']}")
        return 0

    if args.cmd == "review":
        index = _fp_source.load()
        ledger = json.load(io.open(_fp_workspace.LEDGER, encoding="utf-8"))
        _fp_workspace.REVIEW.parent.mkdir(parents=True, exist_ok=True)
        _fp_workspace.REVIEW.write_text(_fp_reports.review_digest(index, ledger), encoding="utf-8")
        print(f"wrote {_fp_workspace.REVIEW.relative_to(_fp_workspace.ROOT)}")
        return 0

    if args.cmd == "papers":
        for label, s in _fp_graph.paper_surface(_fp_source.load()).items():
            if not s["present"]:
                print(f"{label}: root {s['root']} is not in the index")
                continue
            print(f"{label} ({s['root']}): {s['modules']} modules, "
                  f"{s['declarations']} declarations")
            print(f"   proofs running native_decide: {s['compiler_trusted'] or 'none'}")
            resting = [n for n in s["compiler_dependent"] if n not in s["compiler_trusted"]]
            print(f"   resting on one through citation: {resting or 'none'}")
            if s["open"]:
                print(f"   carrying sorry: {s['open']}")
        return 0

    if args.cmd == "propose":
        index = _fp_source.load()
        ledger = json.load(io.open(_fp_workspace.LEDGER, encoding="utf-8"))
        out = _fp_matching.propose(index, ledger)
        _fp_workspace.PROPOSALS.parent.mkdir(parents=True, exist_ok=True)
        _fp_workspace.PROPOSALS.write_text(_fp_source.render(out), encoding="utf-8")
        print(f"{out['unresolved']} unresolved rows; {out['worth_reviewing']} worth reviewing; "
              f"{out['composite']} name two or more of their own declarations")
        return 0

    if args.cmd == "dag":
        index = _fp_source.load()
        ledger = json.load(io.open(_fp_workspace.LEDGER, encoding="utf-8"))
        graph = _fp_graph.dag(index, ledger)
        _fp_workspace.DAG.parent.mkdir(parents=True, exist_ok=True)
        _fp_workspace.DAG.write_text(_fp_source.render(graph), encoding="utf-8")
        g = graph["totals"]
        print(f"{g['nodes']} modules carry {g['ledger_rows_placed']} ledger rows")
        print(f"  {g['edges_before_reduction']} edges -> {g['edges']} after transitive reduction")
        return 0

    raise AssertionError(f"Unhandled command: {args.cmd}")
