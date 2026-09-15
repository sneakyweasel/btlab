"""Every paper's release gate must pass on the live repository.

Papers A and B each had a test calling their own `check`; Paper C had none, and CI ran
no paper gate directly.  On 2026-09-15 both holes fired on the same day:

  * a change to `src/research/juggler_sequence/tao_reduction.py` -- an overflow fix, not
    a manuscript edit -- staled Paper C's pinned inputs, and nothing in the suite noticed;
  * a manuscript edit to Paper B shipped without a rebuild, because `build_paper_b.py`
    compared only its PDF-to-PDF copies and the Zenodo fields and never consulted the
    digests its own manifest records.

Both were found by running the gates by hand during a consolidation pass.  The lesson is
that a source change anywhere under `src/` can stale a paper manifest, and only that
paper's own gate says so -- so the suite has to run them.

This discovers the build tools instead of listing them, so a paper that ships with a
build script and no working gate fails here rather than going quiet.
"""
from __future__ import annotations

import importlib.util
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parents[2]
BUILDERS = sorted(ROOT.glob("tools/build_paper_*.py"))


def _load(path: Path):
    spec = importlib.util.spec_from_file_location(f"gate_{path.stem}", path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def test_every_paper_build_tool_is_discovered() -> None:
    """Three today.  A fourth must be picked up automatically, not added by hand."""
    names = {p.name for p in BUILDERS}
    assert names >= {"build_paper_a.py", "build_paper_b.py", "build_paper_c.py"}, names


@pytest.mark.parametrize("builder", BUILDERS, ids=lambda p: p.stem)
def test_the_paper_gate_exists_and_passes_on_the_live_repository(builder: Path) -> None:
    """The gate must exist, be callable on the repository, and be satisfied.

    A failure here means a committed paper disagrees with its source or its pinned
    inputs: rebuild with `python tools/<builder>.py` and commit the regenerated
    artifacts.  It does not mean the test is wrong.
    """
    module = _load(builder)
    check = getattr(module, "check", None)
    assert callable(check), f"{builder.name} has no check(); a paper without a gate"
    check(ROOT)
