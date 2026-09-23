"""Explicit destinations for reproducible research reports and data."""
from __future__ import annotations

from pathlib import Path

_CHECKOUT = Path(__file__).resolve().parents[3]


def artifact_path(canonical: Path, output_root: Path | None = None) -> Path:
    """Keep the checkout-relative layout under an optional output root.

    With no override, an explicitly invoked probe regenerates its canonical
    artifacts. Tests and exploratory runs supply a temporary directory instead.
    Input paths and module globals are never changed.
    """
    if output_root is None:
        return canonical
    relative = canonical.resolve().relative_to(_CHECKOUT)
    return Path(output_root).resolve() / relative
