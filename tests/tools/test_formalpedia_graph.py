"""Formalpedia graph regressions; live corpus snapshots are isolated by conftest."""
from __future__ import annotations

from research.claims import load_claims

from formalpedia_core import (
    graph as fp_graph,
    workspace as fp_workspace,
)


def test_dependents_reverses_the_import_graph(corpus_index) -> None:
    index = corpus_index
    rev = fp_graph.dependents(index)
    for target, importers in rev.items():
        for name in importers:
            assert target in index["modules"][name]["imports"]


def test_impact_of_a_leaf_is_a_superset_of_its_direct_importers(corpus_index) -> None:
    index = corpus_index
    rev = fp_graph.dependents(index)
    for module in list(index["modules"])[:40]:
        assert set(rev.get(module, [])) <= set(fp_graph.transitive(rev, module))


def test_the_claim_graph_is_acyclic_and_reduced(corpus_index) -> None:
    """A DAG is only useful if it is both: cycles make it unreadable, redundancy makes it long."""
    index = corpus_index
    ledger = load_claims(fp_workspace.ROOT).entries
    g = fp_graph.dag(index, ledger)
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


def test_every_graph_node_carries_at_least_one_ledger_row(corpus_index) -> None:
    """The graph is over claims, not over the whole corpus; a node with no row is noise."""
    index = corpus_index
    ledger = load_claims(fp_workspace.ROOT).entries
    g = fp_graph.dag(index, ledger)
    empty = [n for n, node in g["nodes"].items() if not node["ledger"]]
    assert empty == [], empty
