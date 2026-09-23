"""Formalpedia reports regressions; live corpus snapshots are isolated by conftest."""
from __future__ import annotations

import io
from research.claims import load_claims
import json

from formalpedia_core import (
    cli as fp_cli,
    graph as fp_graph,
    identities as fp_identities,
    matching as fp_matching,
    reports as fp_reports,
    source as fp_source,
    workspace as fp_workspace,
)


def test_review_digest_pairs_each_row_with_its_candidate_s_prose(corpus_index) -> None:
    """The digest exists so a person can decide; deciding needs the docstring beside the row."""
    index = corpus_index
    ledger = load_claims(fp_workspace.ROOT).entries
    text = fp_reports.review_digest(index, ledger)
    assert "# Declaration review queue" in text
    assert "rows below, of" in text
    # every entry carries a candidate line and a quoted docstring block
    entries = text.count("\n## ")
    assert entries > 0
    assert text.count("**Candidate.**") == entries
    assert text.count("**Row.**") == entries


def test_review_digest_warns_about_both_part_for_whole_failures(corpus_index) -> None:
    """Neither is scored, and both record a part as the whole: a row broader than its
    candidate, and a candidate narrower than its row. The digest names a worked example of
    each, because a reviewer cannot see either one in the numbers."""
    index = corpus_index
    ledger = load_claims(fp_workspace.ROOT).entries
    text = fp_reports.review_digest(index, ledger)
    assert "record a part as the whole" in text
    assert "BTC-select3" in text                      # row broader than candidate
    assert "BTN-sdrg-lambda1-interval" in text        # candidate narrower than row


def test_every_digest_entry_shows_a_docstring_or_a_signature(corpus_index) -> None:
    """An entry offering only a name cannot be answered. Nine of the confident candidates
    carry no docstring, so the digest falls back to the statement the docstring would have
    paraphrased."""
    index = corpus_index
    ledger = load_claims(fp_workspace.ROOT).entries
    text = fp_reports.review_digest(index, ledger)
    entries = text.count("\n## ")
    assert text.count("> ") + text.count("```lean") >= entries
    assert "(no docstring)" not in text


def test_the_digest_computes_its_precision_rather_than_asserting_one(corpus_index) -> None:
    """A hardcoded figure goes stale silently: 96% was quoted for twenty-five ticks after the
    calibration set had outgrown the easy rows it was measured on. The real number was 86%.

    Calibration measures the scorer, and the scorer proposes one declaration, so it runs on
    the rows that name exactly one. A row naming its whole inventory has no single answer to
    be scored against and would only dilute the figure.
    """
    index = corpus_index
    ledger = load_claims(fp_workspace.ROOT).entries
    cal = fp_matching.calibrate(index, ledger)
    assert cal["resolved"] == sum(1 for r in ledger if len(fp_identities.row_decls(r)) == 1)
    assert cal["resolved"] < sum(1 for r in ledger if fp_identities.row_decls(r))
    assert 0 < cal["correct"] <= cal["fires"]
    text = fp_reports.review_digest(index, ledger)
    assert f"all {cal['resolved']} single-declaration rows" in text
    assert "96%" not in text


def test_digest_flags_a_top_candidate_that_extends_a_runner_up(corpus_index) -> None:
    """Helper and special-case lemmas are named by extending their main theorem, so a longer
    top candidate beside a shorter runner-up is the shape that cost two wrong answers:
    q_eq_iff_of_same_bal over q_eq_iff, and predecessor_on_F over unique_predecessor."""
    index = corpus_index
    ledger = load_claims(fp_workspace.ROOT).entries
    text = fp_reports.review_digest(index, ledger)
    flagged = 0
    for row in fp_matching.propose(index, ledger)["rows"]:
        if row["confidence"] != "review" or len(row["candidates"]) < 2:
            continue
        top = row["candidates"][0]["decl"]
        if any(top != c["decl"] and top.startswith(c["decl"]) for c in row["candidates"][1:]):
            flagged += 1
    assert text.count("Careful:") == flagged


def test_coverage_digest_says_so_when_jev_has_not_been_asked(corpus_index) -> None:
    index = corpus_index
    ledger = load_claims(fp_workspace.ROOT).entries
    text = fp_reports.coverage_digest(index, ledger, jev={})
    assert "has not been asked yet" in text and "\n## " not in text


def test_reports_ignore_stale_exports_and_see_source_changes(tmp_path, monkeypatch):
    formal = tmp_path / "formal"
    source = formal / "Core" / "Example.lean"
    source.parent.mkdir(parents=True)
    source.write_text("namespace Example\ntheorem first : True := by trivial\nend Example\n")
    ledger = tmp_path / "docs/claims/shared/example.json"
    ledger.parent.mkdir(parents=True, exist_ok=True)
    ledger.write_text("[]")
    saved = tmp_path / "stale.json"
    saved.write_text("not even valid JSON: a report must never read this")
    for name, value in {"ROOT": tmp_path, "FORMAL": formal, "LEDGER": ledger, "INDEX": saved}.items():
        monkeypatch.setattr(fp_workspace, name, value)
    assert {d["name"] for d in fp_source.load()["declarations"]} == {"first"}
    source.write_text("namespace Example\ntheorem second : True := by trivial\nend Example\n")
    assert {d["name"] for d in fp_source.load()["declarations"]} == {"second"}
    assert saved.read_text().startswith("not even valid JSON")


def test_report_commands_rebuild_consistently_without_saved_inventory(example_catalog, tmp_path, monkeypatch):
    index, ledger = example_catalog
    cache = tmp_path / ".cache" / "formalpedia"
    ledger_path = tmp_path / "docs/claims/shared/example.json"
    ledger_path.parent.mkdir(parents=True, exist_ok=True)
    ledger_path.write_text(json.dumps(ledger), encoding="utf-8")
    evidence = tmp_path / "evidence.json"
    evidence.write_text('{"rows": {}, "coverage": {"rows": {}}, "retained_evidence": true}')
    original_evidence = evidence.read_bytes()
    outputs = {"INDEX": "index.json", "DAG": "dag.json", "PROPOSALS": "decl_proposals.json",
               "REVIEW": "decl_review.md", "COVERAGE": "coverage_review.md"}
    monkeypatch.setattr(fp_workspace, "ROOT", tmp_path)
    monkeypatch.setattr(fp_workspace, "LEDGER", ledger_path)
    monkeypatch.setattr(fp_workspace, "JEV", evidence)
    for name, filename in outputs.items():
        monkeypatch.setattr(fp_workspace, name, cache / filename)
    # Report commands work before any saved index exists, and all five exports
    # retain deterministic content. No external advisory request is made.
    cases = [
        (["propose"], fp_workspace.PROPOSALS, fp_source.render(fp_matching.propose(index, ledger))),
        (["dag"], fp_workspace.DAG, fp_source.render(fp_graph.dag(index, ledger))),
        (["review"], fp_workspace.REVIEW, fp_reports.review_digest(index, ledger)),
        (["jev-coverage", "--limit", "0"], fp_workspace.COVERAGE, fp_reports.coverage_digest(index, ledger)),
        (["build"], fp_workspace.INDEX, fp_source.render(index)),
    ]
    for args, path, expected in cases:
        assert fp_cli.main(args) == 0
        assert path.read_text(encoding="utf-8") == expected
    assert evidence.read_bytes() == original_evidence
    assert fp_workspace.REVIEW.read_text(encoding="utf-8").startswith("# ")
    assert fp_cli.main(["build", "--check"]) == 0
    fp_workspace.INDEX.write_text("stale")
    assert fp_cli.main(["build", "--check"]) == 1
