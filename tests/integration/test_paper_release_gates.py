"""Every paper's release gate must pass on the live repository.

Papers A and B each had a test calling their own `check`; Paper C had none, and CI ran
no paper gate directly.  On 2026-09-15 both holes fired on the same day:

  * a change to `src/research/juggler_sequence/tao_reduction.py` -- an overflow fix, not
    a manuscript edit -- staled Paper C's pinned inputs, and nothing in the suite noticed;
  * a manuscript edit to Paper B shipped without a rebuild, because Paper B's builder
    compared only its PDF-to-PDF copies and the Zenodo fields and never consulted the
    digests its own manifest records.

Both were found by running the gates by hand during a consolidation pass.  The lesson is
that a source change anywhere under `src/` can stale a paper manifest, and only that
paper's own gate says so -- so the suite has to run them.

This discovers the papers from their settings in `tools/papers/` instead of listing them,
so a paper added there is gated here automatically. Every paper uses the one builder,
`tools/build_paper.py`.
"""
from __future__ import annotations

import importlib.util
from pathlib import Path
import sys

import pytest

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "tools"))
from build_paper import Paper, letters  # noqa: E402

LETTERS = letters(ROOT)


def _load(path: Path):
    spec = importlib.util.spec_from_file_location(f"gate_{path.stem}", path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


paper_pin = _load(ROOT / "tools/paper_pin.py")


def test_every_paper_is_discovered_and_no_private_builder_remains() -> None:
    """Five today, all through one builder; a per-paper build script would be a special case."""
    assert set(LETTERS) >= set("abcde"), LETTERS
    assert not sorted(ROOT.glob("tools/build_paper_*.py"))


@pytest.mark.parametrize("letter", LETTERS)
def test_the_paper_gate_exists_and_passes_on_the_live_repository(letter: str) -> None:
    """The gate must exist, be callable on the repository, and be satisfied.

    A failure here means a committed paper disagrees with its source or its pinned
    inputs: rebuild with `python tools/build_paper.py <letter>` and commit the regenerated
    artifacts.  It does not mean the test is wrong.
    """
    Paper(letter, ROOT).check(ROOT)


@pytest.mark.parametrize("letter", LETTERS)
def test_the_provenance_pin_names_a_commit_that_holds_the_inputs(letter: str) -> None:
    """A paper's printed commit must be one a reader can actually follow.

    The gate above cannot see this.  It compares the live files to the digests in the
    paper's own release manifest, and the builder writes that manifest from those same
    live files, so the two agree by construction and the commit in the manuscript is
    never read.  Paper A's pin was therefore free to name a commit of 31 August 2026
    at which two of the data files its Appendix B points to did not exist, and it went
    on naming it through the 9 September deposit and for twelve days after.

    `tools/paper_pin.py` has the whole argument.  A paper that prints no repository
    block skips here, because it makes no claim to falsify; Papers B and C are in that
    state today, and the test below keeps a suite of nothing but skips from reading as
    a pass.
    """
    try:
        paper_pin.verify(ROOT, Paper(letter, ROOT))
    except (paper_pin.NoPinClaimed, paper_pin.PinUnavailable) as exc:
        pytest.skip(str(exc))


def test_at_least_one_paper_pin_was_really_verified() -> None:
    """Guard the skips above from swallowing the gate whole.

    Both skip paths are legitimate one paper at a time and worthless all at once: a
    shallow checkout, which CI took by default until `fetch-depth: 0` was set, makes
    every pin unverifiable, and a suite that skips every one of them has checked
    nothing while reporting no failure.  This says so instead.
    """
    verified = []
    for letter in LETTERS:
        try:
            verified.append(paper_pin.verify(ROOT, Paper(letter, ROOT)))
        except (paper_pin.NoPinClaimed, paper_pin.PinUnavailable):
            continue
    assert verified, (
        "no paper's provenance pin could be verified at all. Either every manuscript "
        "has lost its repository block, or this checkout has no history to check it "
        "against -- clone with full depth, or check out with fetch-depth 0 in CI.")
