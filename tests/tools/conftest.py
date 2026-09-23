"""Isolated snapshots for tests that inspect the committed Lean corpus.

Build once per pytest worker, never cache the production source reader. Each test
gets its own copy, so ledger edits, monkeypatches and mutable report consumers
cannot contaminate later tests. Temporary-checkout freshness tests call the real
reader themselves and do not use these fixtures.
"""

from copy import deepcopy
import json

import pytest

@pytest.fixture(scope="session")
def _corpus_snapshot():
    from formalpedia_core import source

    return source.build()


@pytest.fixture
def corpus_index(_corpus_snapshot):
    return deepcopy(_corpus_snapshot)


@pytest.fixture(scope="session")
def _paper_surface_snapshot(_corpus_snapshot):
    from formalpedia_core import graph

    return graph.paper_surface(deepcopy(_corpus_snapshot))


@pytest.fixture
def paper_surfaces(_paper_surface_snapshot):
    return deepcopy(_paper_surface_snapshot)


@pytest.fixture
def example_catalog(tmp_path, monkeypatch):
    """Small live checkout for report, cache and mutation behavior."""
    from formalpedia_core import source, workspace

    formal = tmp_path / "formal"
    folder = formal / "Problems"
    folder.mkdir(parents=True)
    (folder / "Example.lean").write_text(
        "namespace Example\n"
        "/-- First claim. -/\ntheorem first : True := by trivial\n"
        "/-- Second claim. -/\ntheorem second : True := by trivial\n"
        "/-- Third claim. -/\ntheorem third : True := by trivial\n"
        "/-- An offered claim. -/\ntheorem offered : True := by trivial\n"
        "end Example\n", encoding="utf-8",
    )
    ledger = [
        {"id": name, "source": "formal/Problems/Example.lean", "tag": "EXACT — HUMAN PROOF", "statement": f"The {name} claim.",
         "lean": "Problems/Example.lean", "decl": f"Example.{name}"}
        for name in ("first", "second", "third")
    ]
    ledger.append({"id": "unresolved", "source": "formal/Problems/Example.lean", "tag": "CONJECTURE", "statement": "An offered claim.",
                   "lean": "Problems/Example.lean"})
    ledger_path = tmp_path / "docs/claims/shared/example.json"
    ledger_path.parent.mkdir(parents=True, exist_ok=True)
    ledger_path.write_text(json.dumps(ledger), encoding="utf-8")
    for name, value in {"ROOT": tmp_path, "FORMAL": formal, "LEDGER": ledger_path,
                        "JEV": tmp_path / "evidence.json"}.items():
        monkeypatch.setattr(workspace, name, value)
    return source.build(), ledger
