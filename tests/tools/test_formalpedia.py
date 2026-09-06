"""The theorem index, and the two invariants it exists to keep honest.

The corpus is sorry-free and all but a named handful is kernel-checked.  Both facts are
asserted in the manuscripts, so both are worth a test that reads the Lean rather than the
prose: Paper A's Section 1.2 states the trust boundary positively, and a new
``native_decide`` slipping in anywhere would make that sentence false.
"""

from __future__ import annotations

import io
import json
import sys
from pathlib import Path

REPO = Path(__file__).resolve().parents[2]
TOOLS = REPO / "tools"
if str(TOOLS) not in sys.path:
    sys.path.insert(0, str(TOOLS))

import formalpedia as fp

JUGGLER_COMPILER_TRUST = {
    "greedy_eq_ostro_below_window",
    "window_digit_scan",
}
"""The two Ostrowski scans Paper A names as the only proofs off the kernel in its layer."""


def test_the_index_covers_the_libraries_and_not_the_build_output() -> None:
    paths = fp.sources()
    assert paths, "no Lean sources found"
    assert not any(".lake" in p.parts for p in paths)


def test_every_declaration_carries_its_location_and_trust() -> None:
    index = fp.build()
    assert index["totals"]["declarations"] > 3000
    for d in index["declarations"]:
        assert d["name"] and d["module"] and d["file"]
        assert d["line"] >= 1
        assert d["trust"] in {"kernel", "compiler", "open"}


def test_the_corpus_carries_no_sorry() -> None:
    index = fp.build()
    open_ = [d["name"] for d in index["declarations"] if d["trust"] == "open"]
    assert open_ == [], open_


def test_the_juggler_layer_keeps_only_the_two_named_scans_off_the_kernel() -> None:
    index = fp.build()
    found = {
        d["name"]
        for d in index["declarations"]
        if d["trust"] == "compiler" and d["module"].startswith("Problems.Juggler")
    }
    assert found == JUGGLER_COMPILER_TRUST, found


def test_a_docstring_belongs_to_the_declaration_it_sits_above() -> None:
    """Regression: reaching backwards for any earlier ``/--`` gave one paragraph to many."""
    text = "/-- First. -/\ntheorem a : True := trivial\n\ntheorem b : True := trivial\n"
    assert fp._docstring(text, text.index("theorem a")) == "First."
    assert fp._docstring(text, text.index("theorem b")) == ""


def test_dependents_reverses_the_import_graph() -> None:
    index = fp.build()
    rev = fp.dependents(index)
    for target, importers in rev.items():
        for name in importers:
            assert target in index["modules"][name]["imports"]


def test_impact_of_a_leaf_is_a_superset_of_its_direct_importers() -> None:
    index = fp.build()
    rev = fp.dependents(index)
    for module in list(index["modules"])[:40]:
        assert set(rev.get(module, [])) <= set(fp.transitive(rev, module))


def test_the_claim_graph_is_acyclic_and_reduced() -> None:
    """A DAG is only useful if it is both: cycles make it unreadable, redundancy makes it long."""
    index = fp.build()
    ledger = json.load(io.open(fp.LEDGER, encoding="utf-8"))
    g = fp.dag(index, ledger)
    edges = {name: set(node["depends_on"]) for name, node in g["nodes"].items()}

    # acyclic: a depth-first walk never revisits a node on its own stack
    state: dict[str, int] = {}

    def visit(n: str) -> None:
        state[n] = 1
        for d in edges.get(n, ()):
            assert state.get(d) != 1, f"cycle through {n} -> {d}"
            if state.get(d) is None:
                visit(d)
        state[n] = 2

    for n in edges:
        if state.get(n) is None:
            visit(n)

    # reduced: no edge is implied by a two-step path already in the graph
    for n, ds in edges.items():
        for d in ds:
            assert not (edges.get(d, set()) & ds), f"{n} -> {d} is implied by another path"

    assert g["totals"]["edges"] < g["totals"]["edges_before_reduction"]


def test_every_graph_node_carries_at_least_one_ledger_row() -> None:
    """The graph is over claims, not over the whole corpus; a node with no row is noise."""
    index = fp.build()
    ledger = json.load(io.open(fp.LEDGER, encoding="utf-8"))
    g = fp.dag(index, ledger)
    empty = [n for n, node in g["nodes"].items() if not node["ledger"]]
    assert empty == [], empty


def test_proposals_are_never_written_into_the_ledger() -> None:
    """The queue is advisory. Its own calibration is why: 96% precision is one wrong
    mapping in twenty-five, fine for a list a person reads and wrong for a ledger whose
    purpose is making a claim checkable."""
    index = fp.build()
    ledger = json.load(io.open(fp.LEDGER, encoding="utf-8"))
    out = fp.propose(index, ledger)
    proposed = {r["id"] for r in out["rows"]}
    resolved = {r["id"] for r in ledger if r.get("decl")}
    assert not (proposed & resolved), sorted(proposed & resolved)[:5]
    for r in out["rows"]:
        assert r["confidence"] in {"review", "low"}


def test_every_proposed_candidate_lives_in_the_row_s_own_file() -> None:
    index = fp.build()
    ledger = json.load(io.open(fp.LEDGER, encoding="utf-8"))
    by_file = {}
    for d in index["declarations"]:
        by_file.setdefault(d["file"], set()).add(d["name"])
    for r in fp.propose(index, ledger)["rows"]:
        lean = r.get("lean")
        if not (isinstance(lean, str) and lean.endswith(".lean")):
            continue
        names = by_file.get("formal/" + lean, set())
        for c in r["candidates"]:
            assert c["decl"] in names, f"{r['id']}: {c['decl']} not in {lean}"


PAPER_A_OFF_KERNEL = ["greedy_eq_ostro_below_window", "window_digit_scan"]
"""Paper A's Section 1.2 states the trust boundary positively: kernel-checked throughout the
layer except the two Ostrowski scans.  This is that sentence, as an assertion."""


def test_paper_a_keeps_exactly_the_two_ostrowski_scans_off_the_kernel() -> None:
    surface = fp.paper_surface(fp.build())["Paper A"]
    assert surface["present"], "Problems.JugglerPaper is missing from the index"
    assert surface["compiler_trusted"] == PAPER_A_OFF_KERNEL, surface["compiler_trusted"]


def test_paper_b_is_kernel_checked_throughout() -> None:
    surface = fp.paper_surface(fp.build())["Paper B"]
    assert surface["present"], "Problems.JugglerParityPaper is missing from the index"
    assert surface["compiler_trusted"] == [], surface["compiler_trusted"]


def test_no_paper_reaches_a_sorry() -> None:
    """A `sorry` anywhere under a paper root would make its verification claim false."""
    for label, surface in fp.paper_surface(fp.build()).items():
        if surface["present"]:
            assert surface["open"] == [], f"{label}: {surface['open']}"


def test_paper_reachability_is_not_the_same_set_as_the_directory() -> None:
    """Why the paper roots matter: the Juggler directory holds modules no paper imports, so a
    directory count answers a different question than a trust sentence does.  If these ever
    coincided the distinction would be free, and the roots could be dropped."""
    index = fp.build()
    reach = fp.reachable(index)
    root = fp.PAPER_ROOTS["Paper A"]
    reached = reach.get(root, set()) | {root}
    in_dir = {m for m in index["modules"] if m.startswith("Problems.Juggler")}
    assert in_dir - reached, "every Juggler module is now reachable from Paper A"
    assert reached & in_dir, "Paper A reaches no Juggler module at all"


def test_declares_requires_the_name_to_end_at_the_match() -> None:
    """The corpus names helper lemmas by extending their main theorem, so 519 of 4,528 names
    are a proper prefix of another. A substring check cannot tell them apart; this one can."""
    text = (
        "theorem power_bound_compensated_contracts_follows (h : True) : True := trivial\n"
    )
    assert not fp.declares(text, "power_bound_compensated_contracts")
    assert fp.declares(text, "power_bound_compensated_contracts_follows")


def test_declares_finds_a_real_declaration_in_the_corpus() -> None:
    path = fp.ROOT / "formal" / "Problems" / "Juggler" / "CycleFinance.lean"
    text = path.read_text(encoding="utf-8")
    assert fp.declares(text, "cycleMin_finance")
    assert not fp.declares(text, "cycleMin_financ")
    assert not fp.declares(text, "cycleMin_finance_extra_suffix")


def test_the_prefix_collision_surface_is_real_and_measured() -> None:
    """If this ever drops to zero the `declares` boundary stops mattering and can go."""
    names = {d["name"] for d in fp.build()["declarations"]}
    shadowed = {n for n in names if any(o != n and o.startswith(n) for o in names)}
    assert len(shadowed) > 100, len(shadowed)


def test_review_digest_pairs_each_row_with_its_candidate_s_prose() -> None:
    """The digest exists so a person can decide; deciding needs the docstring beside the row."""
    index = fp.build()
    ledger = json.load(io.open(fp.LEDGER, encoding="utf-8"))
    text = fp.review_digest(index, ledger)
    assert "# Declaration review queue" in text
    assert "rows below, of" in text
    # every entry carries a candidate line and a quoted docstring block
    entries = text.count("\n## ")
    assert entries > 0
    assert text.count("**Candidate.**") == entries
    assert text.count("**Row.**") == entries


def test_review_digest_warns_that_composite_rows_are_unscored() -> None:
    """A reviewer who accepts a composite row's headline theorem records a part as the whole,
    and no score in the queue signals that -- so the digest has to say it in words."""
    index = fp.build()
    ledger = json.load(io.open(fp.LEDGER, encoding="utf-8"))
    text = fp.review_digest(index, ledger)
    assert "composite" in text
    assert "BTC-select3" in text


def test_proposals_never_offer_a_declaration_another_row_already_claims() -> None:
    """Two rows on one declaration is rejected by the ledger's own collision test, so a queue
    that offers a taken declaration spends a reviewer's judgement on a foregone answer.
    Two of the 43 confident entries did exactly that before this filter."""
    index = fp.build()
    ledger = json.load(io.open(fp.LEDGER, encoding="utf-8"))
    taken = {(r["lean"], r["decl"]) for r in ledger if r.get("decl")}
    offered = [
        f"{row['id']} -> {c['decl']}"
        for row in fp.propose(index, ledger)["rows"]
        for c in row["candidates"]
        if (row["lean"], c["decl"]) in taken
    ]
    assert offered == [], offered
