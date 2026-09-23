"""Stable repository paths for Juggler computations and formalization.

Module registration and source inspection live in lean_registry, so adding a
research module cannot invalidate path-only consumers or publication inputs."""

from __future__ import annotations

from pathlib import Path


def repo_root() -> Path:
    """Walk from this file to the directory that contains ``pyproject.toml``."""
    for path in Path(__file__).resolve().parents:
        if (path / "pyproject.toml").is_file():
            return path
    raise RuntimeError("pyproject.toml not found above lean_paths.py")


REPO_ROOT = repo_root()
CAPSULE_ROOT = REPO_ROOT / "attacks" / "juggler"
INDEX_PATH = CAPSULE_ROOT / "index.json"
FORMAL_DIR = REPO_ROOT / "formal"
DATA_ROOT = REPO_ROOT / "data" / "research" / "juggler"
DOCS_ROOT = REPO_ROOT / "docs"
DOCS_RESEARCH = DOCS_ROOT / "research"
DOCS_THEORY = DOCS_ROOT / "theory"
BRANCHES_ROOT = DOCS_ROOT / "problems"
CONJECTURES_ROOT = REPO_ROOT / "conjectures"
JUGGLER_DIR = FORMAL_DIR / "Problems" / "Juggler"
JUGGLER_BARREL = FORMAL_DIR / "Problems" / "Juggler.lean"
JUGGLER_PAPER_BARREL = FORMAL_DIR / "Problems" / "JugglerPaper.lean"
ENGINE_DIR = FORMAL_DIR / "Problems" / "Engine"
