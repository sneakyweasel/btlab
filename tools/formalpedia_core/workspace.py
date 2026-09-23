"""Checkout paths and library roots; no scanning, building or external calls."""
from __future__ import annotations

from pathlib import Path

LIBRARIES = ("Core", "Representation", "Operators", "Problems", "BTCalculus")
"""The lean_lib roots; imports outside them belong to Mathlib or the standard library."""


def configure(root: Path) -> None:
    """Select one checkout at process startup, before constructing any catalogues.

    Paths are shared by source discovery and CLI writers. Never reconfigure a
    serving process: use one MCP process per checkout or worktree instead.
    """
    global ROOT, FORMAL, LEDGER, CACHE, INDEX, DAG, PROPOSALS, REVIEW, JEV, COVERAGE
    ROOT = root.resolve()
    FORMAL = ROOT / "formal"
    LEDGER = ROOT / "docs/theory/theorem_ledger.json"
    CACHE = ROOT / ".cache/formalpedia"
    INDEX = CACHE / "index.json"
    DAG = CACHE / "dag.json"
    PROPOSALS = CACHE / "decl_proposals.json"
    REVIEW = CACHE / "decl_review.md"
    JEV = ROOT / "data/research/formalpedia/jev_verdicts.json"
    COVERAGE = CACHE / "coverage_review.md"


configure(Path(__file__).resolve().parents[2])
