"""Formalpedia matching regressions; live corpus snapshots are isolated by conftest."""
from __future__ import annotations

from research.claims import load_claims

from formalpedia_core import (
    identities as fp_identities,
    matching as fp_matching,
    workspace as fp_workspace,
)


def test_proposals_are_never_written_into_the_ledger(corpus_index) -> None:
    """The queue is advisory. Its own calibration is why: 86% precision is one wrong mapping
    in seven, fine for a list a person reads and wrong for a ledger whose purpose is making a
    claim checkable."""
    index = corpus_index
    ledger = load_claims(fp_workspace.ROOT).entries
    out = fp_matching.propose(index, ledger)
    proposed = {r["id"] for r in out["rows"]}
    resolved = {r["id"] for r in ledger if r.get("decl")}
    assert not (proposed & resolved), sorted(proposed & resolved)[:5]
    for r in out["rows"]:
        assert r["confidence"] in {"review", "low"}


def test_every_proposed_candidate_lives_in_the_row_s_own_file(corpus_index) -> None:
    index = corpus_index
    ledger = load_claims(fp_workspace.ROOT).entries
    by_file = {}
    for d in index["declarations"]:
        by_file.setdefault(d["file"], set()).add(d["name"])
    for r in fp_matching.propose(index, ledger)["rows"]:
        lean = r.get("lean")
        if not (isinstance(lean, str) and lean.endswith(".lean")):
            continue
        names = by_file.get(fp_identities.lean_key(lean), set())
        for c in r["candidates"]:
            assert c["decl"] in names, f"{r['id']}: {c['decl']} not in {lean}"


def test_proposals_never_offer_a_declaration_another_row_already_claims(corpus_index) -> None:
    """Two rows on one declaration is rejected by the ledger's own collision test, so a queue
    that offers a taken declaration spends a reviewer's judgement on a foregone answer.
    Two of the 43 confident entries did exactly that before this filter."""
    index = corpus_index
    ledger = load_claims(fp_workspace.ROOT).entries
    taken = {(r["lean"], name) for r in ledger for name in fp_identities.row_decls(r)}
    offered = [
        f"{row['id']} -> {c['decl']}"
        for row in fp_matching.propose(index, ledger)["rows"]
        for c in row["candidates"]
        if (row["lean"], c["decl"]) in taken
    ]
    assert offered == [], offered


def test_definitions_are_ranked_apart_from_theorems(corpus_index) -> None:
    """Merging them into one ranking displaces the true answer on rows already resolved --
    measured at 3 of 103 -- so a row that means a `def` gets its own short list instead."""
    index = corpus_index
    ledger = load_claims(fp_workspace.ROOT).entries
    kinds = {d["name"]: d["kind"] for d in index["declarations"]}
    for row in fp_matching.propose(index, ledger)["rows"]:
        for c in row["candidates"]:
            assert kinds.get(c["decl"]) in ("theorem", "lemma"), c["decl"]
        for d in row.get("definitions", []):
            assert kinds.get(d["decl"]) in ("def", "abbrev"), d["decl"]
