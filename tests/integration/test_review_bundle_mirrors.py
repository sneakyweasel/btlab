"""The reviewer bundle and the companion site must not carry drifting copies of docs/theory.

`juggler_review/README.md` names `docs/theory/` the source of truth for the
three manuscripts and says not to hand-edit both copies.  Nothing enforced
that, and the two trees have been edited in lockstep by hand.

This gate used to hold a hand-written list of mirrored filenames, and that list
fell behind in three separate ways at once.  It named seven of the twenty-two
files the two trees then shared.  It carried an exclusion for
`juggler_finite_dynamics_formalization.md` on the ground that the bundle copy
was trimmed and the laboratory copy carried extra table rows -- true when it was
written, and false for a long while before anyone looked, the two having
converged to the same 1387 lines.  And `figures/juggler_lean_layers.png` sat
drifted for a week after `b5654437` re-rendered the `docs/theory` copy alone,
because a figure was never on the list to begin with.

A list that has to be extended by hand every time someone copies a file will
keep falling behind, and each of those three failures is silent: the gate stays
green while the thing it names goes wrong.  So the pairing is computed rather
than written down.  Every tracked path present under both roots must agree byte
for byte, and a path only one tree carries is not a pair at all.

That last point preserves the old behaviour worth keeping: a bundle that drops
a mirror and keeps only the built PDF still passes, because the dropped file
stops being a shared path.  That remains the tidier end state.

A copy that is genuinely meant to differ goes in `DELIBERATELY_DIFFERENT` by
relative path, where the reason is written down and stays visible, instead of
being excluded by silent omission from a list.  It is empty today.
"""

from __future__ import annotations

import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
SOURCE = ROOT / "docs" / "theory"
BUNDLE = ROOT / "juggler_review"

#: Relative paths the two trees carry on purpose in different form.  Each entry
#: needs a reason here, and a reason that stops being true should remove it.
DELIBERATELY_DIFFERENT: frozenset[str] = frozenset()

#: A path that must always be shared, so a broken prefix computation cannot make
#: this file pass by comparing nothing at all.
CANARY = "juggler_parity_discrepancy_note.md"

#: The companion site serves its own copies of the three built PDFs, and nothing
#: checked them.  `test_manuscript_consistency.py` reads the app's TypeScript --
#: constants, claims, glossary and two pages -- and never the files the site
#: actually serves, so a manuscript could be rebuilt in docs/theory and the
#: deployed site would go on serving the previous PDF with nothing to say so.
COMPANION = ROOT / "web" / "juggler-companion" / "public" / "papers"

SERVED = (
    "juggler_finite_dynamics_note.pdf",
    "juggler_parity_discrepancy_note.pdf",
    "juggler_fate_almost_all_note.pdf",
)


def tracked_under(prefix: str) -> set[str]:
    """Paths git tracks under `prefix`, relative to it.

    Tracked rather than walked: an untracked scratch file that happens to exist
    under both roots is not a mirror anyone promised to keep.
    """
    out = subprocess.run(
        ["git", "ls-files", "-z", "--", prefix],
        cwd=ROOT,
        capture_output=True,
        text=True,
        check=True,
    ).stdout
    return {path[len(prefix):] for path in out.split("\0") if path}


def shared_paths() -> list[str]:
    both = tracked_under("docs/theory/") & tracked_under("juggler_review/")
    return sorted(both - DELIBERATELY_DIFFERENT)


def test_bundle_carries_no_drifting_copy_of_docs_theory():
    pairs = shared_paths()
    assert CANARY in pairs, (
        f"{CANARY} is not being compared, so this test is not comparing the trees"
    )
    drifted = [
        rel for rel in pairs
        if (SOURCE / rel).read_bytes() != (BUNDLE / rel).read_bytes()
    ]
    assert drifted == []


def test_companion_served_papers_match_docs_theory():
    """The PDFs the site serves are the PDFs in docs/theory.

    Unlike the bundle above, a missing file is a failure rather than a tidier
    end state: the bundle may drop a mirror and keep only the built PDF, but a
    companion paper that is absent is a link the deployed site cannot serve.

    If the site should instead pin to a released Zenodo kit rather than to the
    working manuscripts, this is the place to say so.  Today every copy agrees.
    """
    drifted: list[str] = []
    for name in SERVED:
        source = SOURCE / name
        served = COMPANION / name
        assert source.exists(), f"{name} is not in docs/theory"
        assert served.exists(), f"{name} is not in the companion public/papers"
        if source.read_bytes() != served.read_bytes():
            drifted.append(name)
    assert drifted == []
