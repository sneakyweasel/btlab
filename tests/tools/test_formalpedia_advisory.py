"""Formalpedia advisory regressions; live corpus snapshots are isolated by conftest."""
from __future__ import annotations

import io
import json

from formalpedia_core import (
    advisory as fp_advisory,
    identities as fp_identities,
    matching as fp_matching,
    reports as fp_reports,
    source as fp_source,
    verdicts as fp_verdicts,
    workspace as fp_workspace,
)


def _fake_ask(*, confidence: float = 0.95, pick: dict[str, str] | None = None,
              none_for: set[str] = frozenset(), seen: list | None = None):
    """An ``ask`` that answers from the criteria it is offered and never touches the network.

    Default answer: the alphabetically first theorem offered.  ``pick`` overrides per row,
    including names the file does not offer, which is how the known-bad path is exercised;
    ``none_for`` answers "none of these" for those rows; ``seen`` collects every question.
    """
    def ask(state, instructions, criteria):
        if seen is not None:
            seen.append((state, criteria))
        names = sorted(n for n in criteria if n != fp_verdicts.JEV_NONE)
        rid = state["ledger_id"]
        if rid in none_for:
            choice = fp_verdicts.JEV_NONE
        elif pick and rid in pick:
            choice = pick[rid]
        else:
            choice = names[0]
        rest = (1.0 - confidence) / max(1, len(criteria) - 1)
        probs = {n: rest for n in criteria}
        probs[choice] = confidence
        return {"choice": choice, "confidence": confidence, "probabilities": probs,
                "model": "jev-test", "input_tokens": 100}
    return ask


def _queue_ids(index, ledger) -> set[str]:
    return {row["id"] for row, cands, _ in fp_matching._queue(index, ledger) if cands}


def test_jev_propose_asks_each_unresolved_row_about_its_own_file_and_nothing_else(corpus_index) -> None:
    """Jev is offered exactly the theorems the scorer may propose: the row's own file, minus
    declarations another row already claims, plus the option that none of them is the claim.
    The tests above pin those two rules for the scorer; this pins them for the offer."""
    index = corpus_index
    ledger = json.load(io.open(fp_workspace.LEDGER, encoding="utf-8"))
    seen: list = []
    record = fp_advisory.jev_propose(index, ledger, _fake_ask(seen=seen), workers=1)
    asked = {state["ledger_id"] for state, _ in seen}
    assert asked == _queue_ids(index, ledger) == set(record["rows"])
    by_file: dict[str, set[str]] = {}
    for d in index["declarations"]:
        by_file.setdefault(d["file"], set()).add(d["name"])
    taken = {(fp_identities.lean_key(r.get("lean")), n) for r in ledger for n in fp_identities.row_decls(r)}
    rows = {r["id"]: r for r in ledger}
    for state, criteria in seen:
        assert fp_verdicts.JEV_NONE in criteria
        key = fp_identities.lean_key(rows[state["ledger_id"]]["lean"])
        for name in criteria:
            if name == fp_verdicts.JEV_NONE:
                continue
            assert name in by_file[key], f"{state['ledger_id']}: {name} is not in {key}"
            assert (key, name) not in taken, f"{state['ledger_id']}: {name} is already claimed"
        assert len(criteria) - 1 <= fp_verdicts.JEV_SHORTLIST
    for verdict in record["rows"].values():
        fields = {"key", "model", "asked", "choice", "confidence", "shortlist", "in_file"}
        assert fields <= set(verdict)
    assert record["totals"]["asked_now"] == len(seen) == record["totals"]["answered"]


def test_jev_propose_reuses_a_verdict_until_the_row_or_its_offer_changes(corpus_index) -> None:
    """A verdict costs tokens and can differ between runs, so an unchanged row keeps the
    answer it has.  The key covers the statement, the file and the names offered: any of
    those moving re-asks that row alone, ``refresh`` re-asks them all, a row resolved since
    is dropped rather than carried, and ``limit`` leaves the rows it does not reach as they
    were instead of forgetting them."""
    index = corpus_index
    ledger = json.load(io.open(fp_workspace.LEDGER, encoding="utf-8"))
    first = fp_advisory.jev_propose(index, ledger, _fake_ask(), workers=1)
    n = first["totals"]["answered"]
    assert n > 0
    seen: list = []
    again = fp_advisory.jev_propose(index, ledger, _fake_ask(seen=seen), cached=first, workers=1)
    assert seen == [] and again["rows"] == first["rows"]
    assert again["totals"] == {"answered": n, "asked_now": 0, "reused": n, "input_tokens": 0}
    seen = []
    fp_advisory.jev_propose(index, ledger, _fake_ask(seen=seen), cached=first, refresh=True, workers=1)
    assert len(seen) == n
    moved = json.loads(json.dumps(first))
    victim = next(iter(moved["rows"]))
    moved["rows"][victim]["key"] = "0000000000000000"
    moved["rows"]["A-row-resolved-since"] = dict(moved["rows"][victim])
    seen = []
    third = fp_advisory.jev_propose(index, ledger, _fake_ask(seen=seen), cached=moved, workers=1)
    assert [s["ledger_id"] for s, _ in seen] == [victim]
    assert "A-row-resolved-since" not in third["rows"]
    seen = []
    capped = fp_advisory.jev_propose(index, ledger, _fake_ask(seen=seen), cached=first, refresh=True,
                            limit=3, workers=1)
    assert len(seen) == 3 and capped["totals"]["answered"] == n


def test_propose_routes_a_confident_jev_pick_to_review_and_leaves_the_candidates_alone(corpus_index) -> None:
    """Jev's answer is a field beside the scorer's candidates, never a substitute: candidates
    and definitions are identical with and without it.  What it may change is the routing,
    and only upward: a pick at or above JEV_REVIEW lists the row; a pick below it and a
    "none of these" leave the scorer's verdict as it was."""
    index = corpus_index
    ledger = json.load(io.open(fp_workspace.LEDGER, encoding="utf-8"))
    ids = sorted(_queue_ids(index, ledger))
    none_for = set(ids[::3])
    sure = fp_advisory.jev_propose(index, ledger, _fake_ask(confidence=0.95, none_for=none_for),
                          workers=1)
    unsure = fp_advisory.jev_propose(index, ledger, _fake_ask(confidence=0.4), workers=1)
    plain = fp_matching.propose(index, ledger, jev={})
    base = {r["id"]: r for r in plain["rows"]}
    by_file: dict[str, set[str]] = {}
    for d in index["declarations"]:
        by_file.setdefault(d["file"], set()).add(d["name"])
    for record, routes in ((sure, True), (unsure, False)):
        merged = fp_matching.propose(index, ledger, jev=record)
        assert merged["jev"]["answered"] == len(record["rows"])
        assert merged["jev"]["picks"] + merged["jev"]["none"] == merged["jev"]["answered"]
        for r in merged["rows"]:
            b = base[r["id"]]
            assert r["candidates"] == b["candidates"]
            assert r.get("definitions") == b.get("definitions")
            assert r["confidence"] in {"review", "low"}
            jv = r.get("jev")
            if jv is None:
                assert r["id"] not in record["rows"]
                assert r["confidence"] == b["confidence"]
            elif jv["verdict"] == "none":
                assert r["id"] in none_for and jv["decl"] is None
                assert r["confidence"] == b["confidence"]
            else:
                assert jv["verdict"] == "pick"
                assert jv["decl"] in by_file[fp_identities.lean_key(r["lean"])]
                assert r["confidence"] == ("review" if routes else b["confidence"])
                assert jv["routed"] == (routes and b["confidence"] == "low")
    assert fp_matching.propose(index, ledger, jev=sure)["worth_reviewing"] > plain["worth_reviewing"]
    assert fp_matching.propose(index, ledger, jev=unsure)["worth_reviewing"] == plain["worth_reviewing"]


def test_propose_ignores_a_jev_pick_that_the_file_does_not_offer(corpus_index) -> None:
    """The known-bad input.  A cached name that is not in the offer -- claimed by another
    row since, renamed, or invented -- is recorded as not_a_candidate and routes nothing;
    the digest says so and never renders it as a candidate."""
    index = corpus_index
    ledger = json.load(io.open(fp_workspace.LEDGER, encoding="utf-8"))
    plain = fp_matching.propose(index, ledger, jev={})
    shown = next(r for r in plain["rows"] if r["confidence"] == "review" and r["candidates"])
    hidden = next(r for r in plain["rows"] if r["confidence"] == "low" and r["candidates"])
    bad = fp_advisory.jev_propose(
        index, ledger,
        _fake_ask(confidence=0.99,
                  pick={shown["id"]: "no_such_theorem", hidden["id"]: "no_such_theorem"}),
        workers=1)
    merged = {r["id"]: r for r in fp_matching.propose(index, ledger, jev=bad)["rows"]}
    for rid, before in ((shown["id"], "review"), (hidden["id"], "low")):
        jv = merged[rid]["jev"]
        assert jv["verdict"] == "not_a_candidate" and jv["decl"] is None
        assert merged[rid]["confidence"] == before
    text = fp_reports.review_digest(index, ledger, jev=bad)
    assert "which this file does not offer; ignored" in text
    assert "`no_such_theorem`" in text
    assert "**Jev's candidate.** `no_such_theorem`" not in text


def test_propose_marks_a_verdict_stale_once_the_row_or_the_offer_moved(corpus_index) -> None:
    """A verdict answers one wording of the claim against one offer.  When either changes,
    the cached answer is shown as stale and routes nothing until jev-propose re-asks."""
    index = corpus_index
    ledger = json.load(io.open(fp_workspace.LEDGER, encoding="utf-8"))
    record = fp_advisory.jev_propose(index, ledger, _fake_ask(confidence=0.99), workers=1)
    plain = {r["id"]: r for r in fp_matching.propose(index, ledger, jev={})["rows"]}
    victim = next(rid for rid in record["rows"] if plain[rid]["confidence"] == "low")
    stale = json.loads(json.dumps(record))
    stale["rows"][victim]["key"] = "0000000000000000"
    merged = {r["id"]: r for r in fp_matching.propose(index, ledger, jev=stale)["rows"]}
    assert merged[victim]["jev"]["verdict"] == "stale"
    assert merged[victim]["confidence"] == "low"
    fresh = {r["id"]: r for r in fp_matching.propose(index, ledger, jev=record)["rows"]}
    assert fresh[victim]["jev"]["verdict"] == "pick"
    assert fresh[victim]["confidence"] == "review" and fresh[victim]["jev"]["routed"] is True


def test_review_digest_shows_jev_beside_the_scorer_and_quotes_its_stored_calibration(corpus_index) -> None:
    """Each listed entry carries Jev's answer next to the scorer's candidate; a disagreement
    prints Jev's declaration in full so the reviewer reads both; and the figures in the
    opening come from the stored, dated calibration record, never from a constant."""
    index = corpus_index
    ledger = json.load(io.open(fp_workspace.LEDGER, encoding="utf-8"))
    record = fp_advisory.jev_propose(index, ledger, _fake_ask(confidence=0.9), workers=1)
    record["calibration"] = {
        "asked": "2026-09-21", "model": "jev-test", "sampled": 30, "top1": 19, "top3": 26,
        "confident": 21, "confident_correct": 16, "scorer_top1": 16,
    }
    text = fp_reports.review_digest(index, ledger, jev=record)
    merged = fp_matching.propose(index, ledger, jev=record)
    listed = [r for r in merged["rows"] if r["confidence"] == "review" and r["candidates"]]
    assert text.count("**Jev.**") == sum(1 for r in listed if r.get("jev"))
    disagreeing = [r for r in listed if r["jev"]["verdict"] == "pick"
                   and r["jev"]["decl"] != r["candidates"][0]["decl"]]
    assert len(disagreeing) > 0
    assert text.count("**Jev's candidate.**") == len(disagreeing)
    assert "first 19 times, in its top three 26 times" in text
    assert "right 16 of 21 times at or above 0.7" in text
    entries = text.count("\n## ")
    assert text.count("**Candidate.**") == entries == text.count("**Row.**")
    assert "rows below, of" in text


def test_jev_calibrate_scores_the_recorded_answer_on_the_scorer_s_own_population(corpus_index) -> None:
    """Same rows as calibrate(): one recorded declaration, in a file offering at least two.
    A fake that always answers the recorded name scores every row; one that never does
    scores none, and the misses list names the rows it got wrong."""
    index = corpus_index
    ledger = json.load(io.open(fp_workspace.LEDGER, encoding="utf-8"))
    truth = {r["id"]: fp_identities.row_decls(r)[0] for r in ledger if len(fp_identities.row_decls(r)) == 1}
    oracle = fp_advisory.jev_calibrate(index, ledger, _fake_ask(pick=truth, confidence=0.9),
                              sample=12, seed=1, workers=1)
    assert oracle["sampled"] == 12 and oracle["top1"] == 12 == oracle["top3"]
    assert oracle["confident"] == 12 == oracle["confident_correct"] and oracle["misses"] == []
    assert oracle["resolved"] == fp_matching.calibrate(index, ledger)["resolved"]
    assert oracle["eligible"] <= oracle["resolved"]
    blind = fp_advisory.jev_calibrate(index, ledger, _fake_ask(none_for=set(truth)),
                             sample=12, seed=1, workers=1)
    assert blind["top1"] == 0 and blind["none"] == 12 and len(blind["misses"]) == 12
    assert {m["id"] for m in blind["misses"]} <= set(truth)


def test_jev_key_tracks_the_statement_the_file_and_the_offer() -> None:
    row = {"id": "X", "statement": "a claim", "lean": "Problems/X.lean"}
    offer = [{"name": "a"}, {"name": "b"}]
    key = fp_verdicts.jev_key(row, offer)
    assert key != fp_verdicts.jev_key({**row, "statement": "a claim."}, offer)
    assert key != fp_verdicts.jev_key(row, offer[:1])
    assert key != fp_verdicts.jev_key({**row, "lean": "Problems/Y.lean"}, offer)
    assert key == fp_verdicts.jev_key(dict(row), list(offer))


def _fake_nouls(answer: dict[str, dict[str, float]] | None = None, *, seen: list | None = None):
    """An ``AskNouls`` that rates every row covered -- 0.9 for coverage, 0.1 for each failure
    mode -- unless ``answer`` maps a ledger id to the probabilities to return instead."""
    def ask(state, questions):
        if seen is not None:
            seen.append((state, questions))
        nouls = {"covers": 0.9, "claim_broader": 0.1, "decl_narrower": 0.1,
                 "different_result": 0.05}
        nouls.update((answer or {}).get(state["ledger_id"], {}))
        return {"nouls": {q: nouls[q] for q in questions}, "model": "jev-test",
                "input_tokens": 100}
    return ask


def test_jev_coverage_asks_every_resolved_row_with_all_the_declarations_it_names(corpus_index) -> None:
    """The retag rule is about the declarations a row names, all of them: a row joined to a
    list is asked about the list, and the four questions are the constant ones.  The offer
    verdicts and the calibration already in the record survive the run untouched."""
    index = corpus_index
    ledger = json.load(io.open(fp_workspace.LEDGER, encoding="utf-8"))
    # Exercise exclusion independently of which historical claims remain in the lab.
    ledger.append(dict(next(r for r in ledger if fp_identities.row_decls(r)),
                       id='test-refuted-row', tag='REFUTED'))
    offers = fp_advisory.jev_propose(index, ledger, _fake_ask(), workers=1)
    offers["calibration"] = {"asked": "2026-09-21", "model": "jev-test", "sampled": 1,
                             "top1": 1, "top3": 1, "confident": 1, "confident_correct": 1,
                             "scorer_top1": 1}
    seen: list = []
    record = fp_advisory.jev_coverage(index, ledger, _fake_nouls(seen=seen), cached=offers, workers=1)
    resolved = {r["id"]: fp_identities.row_decls(r) for r in ledger
                if fp_identities.row_decls(r) and r["tag"] != "REFUTED"}
    source_names = {r['id']: [d['name'] for d in decls]
                    for r, decls, missing in fp_verdicts._resolved(index, ledger) if not missing}
    assert any(fp_identities.row_decls(r) and r["tag"] == "REFUTED" for r in ledger)  # the exclusion bites
    assert {s["ledger_id"] for s, _ in seen} == set(resolved) == set(record["coverage"]["rows"])
    for state, questions in seen:
        assert [d["name"] for d in state["declarations"]] == source_names[state["ledger_id"]]
        assert all(d["statement"] for d in state["declarations"])
        assert list(questions) == list(fp_verdicts.JEV_COVERAGE_QUESTIONS)
    for verdict in record["coverage"]["rows"].values():
        assert set(fp_verdicts.JEV_COVERAGE_QUESTIONS) <= set(verdict)
        assert {"key", "model", "asked", "decls"} <= set(verdict)
    assert record["rows"] == offers["rows"] and record["calibration"] == offers["calibration"]
    assert record["coverage"]["totals"]["asked_now"] == len(seen) == len(resolved)
    assert record["coverage"]["totals"]["unfound"] == 0


def test_jev_coverage_lists_a_known_bad_row_and_clears_the_covered_ones(example_catalog) -> None:
    """The known-bad input.  A row Jev rates as broader than its declaration is filed as not
    covered with that reading; a row with doubtful coverage and no mode above half is listed
    under the doubtful mark and says so; a row rated covered is left off even when a failure
    mode is high, because coverage alone lists; a record of all-covered rows lists nothing."""
    index, ledger = example_catalog
    ids = [r["id"] for r in ledger if fp_identities.row_decls(r) and r["tag"] != "REFUTED"]
    broad, doubtful, covered = ids[0], ids[-1], ids[1]
    answer = {broad: {"covers": 0.1, "claim_broader": 0.9},
              doubtful: {"covers": 0.3},
              covered: {"covers": 0.55, "decl_narrower": 0.8}}
    record = fp_advisory.jev_coverage(index, ledger, _fake_nouls(answer), workers=1)
    rows = {r["id"]: r for r in fp_verdicts.coverage_rows(index, ledger, record)}
    assert rows[broad]["flagged"] and rows[broad]["reading"] == "claim_broader"
    assert rows[broad]["band"] == "not_covered"
    assert rows[doubtful]["flagged"] and rows[doubtful]["reading"] is None
    assert rows[doubtful]["band"] == "doubtful"
    assert not rows[covered]["flagged"] and rows[covered]["band"] == "covered"
    assert rows[covered]["reading"] == "decl_narrower"
    assert sum(r["flagged"] for r in rows.values()) == 2
    text = fp_reports.coverage_digest(index, ledger, jev=record)
    assert text.startswith("# Coverage review queue")
    assert text.count("\n## ") == 2
    first, mark, second = (text.index(f"`{broad}`"), text.index("**Doubtful from here"),
                           text.index(f"`{doubtful}`"))
    assert first < mark < second                                       # lowest coverage first
    assert "Reads as: the claim asserts more than the declarations state (0.9)" in text
    assert "coverage itself is doubtful" in text
    assert f"resolved rows: {len(ids) - 2} covered," in text
    assert "1 doubtful, 1 not covered; 2 are" in text
    statement = next(r["statement"] for r in ledger if r["id"] == broad)
    assert ("likeliest mis-joins" in text) == (len(statement) < 150)
    assert text.count("```lean") == len(fp_identities.row_decls(next(r for r in ledger if r["id"] == broad))) \
        + len(fp_identities.row_decls(next(r for r in ledger if r["id"] == doubtful)))
    clean = fp_reports.coverage_digest(index, ledger, jev=fp_advisory.jev_coverage(index, ledger, _fake_nouls(),
                                                                  workers=1))
    assert "\n## " not in clean and "0 are\nlisted below" in clean
    assert "Doubtful from here" not in clean


def test_jev_coverage_reuses_verdicts_until_the_row_or_its_declarations_change(example_catalog) -> None:
    """The key covers the statement and the declarations' text, so a row is re-asked when
    either moves and otherwise keeps its answer; ``only`` asks the named rows and keeps the
    rest; ``limit=0`` asks nothing; a changed row shows as stale and is not listed."""
    index, ledger = example_catalog
    first = fp_advisory.jev_coverage(index, ledger, _fake_nouls(), workers=1)
    n = first["coverage"]["totals"]["answered"]
    seen: list = []
    again = fp_advisory.jev_coverage(index, ledger, _fake_nouls(seen=seen), cached=first, workers=1)
    assert seen == [] and again["coverage"]["rows"] == first["coverage"]["rows"]
    victim = next(iter(first["coverage"]["rows"]))
    seen = []
    some = fp_advisory.jev_coverage(index, ledger, _fake_nouls(seen=seen), cached=first,
                           refresh=True, only={victim}, workers=1)
    assert [s["ledger_id"] for s, _ in seen] == [victim]
    assert some["coverage"]["totals"]["answered"] == n
    seen = []
    none = fp_advisory.jev_coverage(index, ledger, _fake_nouls(seen=seen), cached=first,
                           refresh=True, limit=0, workers=1)
    assert seen == [] and none["coverage"]["totals"]["answered"] == n
    moved = json.loads(json.dumps(ledger))
    row = next(r for r in moved if r["id"] == victim)
    row["statement"] = row["statement"] + " And one more claim."
    rows = {r["id"]: r for r in fp_verdicts.coverage_rows(index, moved, first)}
    assert rows[victim]["verdict"] == "stale" and not rows[victim]["flagged"]
    assert "need a rerun" in fp_reports.coverage_digest(index, moved, jev=first)
    seen = []
    fp_advisory.jev_coverage(index, moved, _fake_nouls(seen=seen), cached=first, workers=1)
    assert [s["ledger_id"] for s, _ in seen] == [victim]

    # Changing the declaration itself must invalidate its verdict too. Rebuild
    # from a real temporary source file, leaving the original ledger untouched.
    source = fp_workspace.FORMAL / "Problems" / "Example.lean"
    source.write_text(source.read_text(encoding="utf-8").replace(
        f"theorem {victim} : True", f"theorem {victim} : True ∧ True"
    ), encoding="utf-8")
    changed = fp_source.build()
    seen = []
    fp_advisory.jev_coverage(changed, ledger, _fake_nouls(seen=seen), cached=first, workers=1)
    assert [s["ledger_id"] for s, _ in seen] == [victim]
