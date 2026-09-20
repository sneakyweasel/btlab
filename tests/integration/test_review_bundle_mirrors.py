"""The reviewer bundle and the companion site must not carry drifting copies of docs/theory.

`juggler_review/README.md` names `docs/theory/` the source of truth for the
three manuscripts and says not to hand-edit both copies.  Nothing enforced
that, and the two trees have been edited in lockstep by hand.

`juggler_finite_dynamics_formalization.md` was excluded here, on the grounds
that it shares a filename across the two trees without being a copy: the bundle
version trimmed for an external reader, the laboratory version carrying table
rows the bundle dropped.  That was true once -- the two blobs differ across
dozens of commits in the history -- but they converged, and every commit that
has touched them since has written both sides identically, 1387 lines each.

An exclusion describing a distinction the files no longer have is worse than no
exclusion at all, because real drift would then read as the intended state.  So
it is mirrored like the rest.  Re-trimming the bundle copy is an editorial
decision about the packet, and it would mean taking this name back off the list
deliberately rather than leaving the gate blind to it.

The test also passes if the mirrors are removed and only the built PDFs
remain, which is the tidier end state.
"""

from __future__ import annotations

from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
SOURCE = ROOT / "docs" / "theory"
BUNDLE = ROOT / "juggler_review"

MIRRORED = (
    "juggler_finite_dynamics_note.md",
    "juggler_parity_discrepancy_note.md",
    "juggler_fate_almost_all_note.md",
    "paper_b_audit_ledger.md",
    "juggler_finite_dynamics_reviewer_packet.md",
    # Build guides.  `PAPER_A_BUILD.md` was missing from the bundle entirely
    # while the reviewer packet told reviewers it was there; `PAPER_C_BUILD.md`
    # was already a verbatim copy that nothing enforced.
    "PAPER_A_BUILD.md",
    "PAPER_C_BUILD.md",
    # Converged with its laboratory copy; see the header.
    "juggler_finite_dynamics_formalization.md",
)

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


def test_bundle_manuscript_mirrors_match_docs_theory():
    drifted: list[str] = []
    for name in MIRRORED:
        source = SOURCE / name
        copy = BUNDLE / name
        if not copy.exists():
            continue
        assert source.exists(), f"{name} in the bundle with no docs/theory source"
        if source.read_bytes() != copy.read_bytes():
            drifted.append(name)
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
