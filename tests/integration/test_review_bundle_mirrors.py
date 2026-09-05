"""The reviewer bundle must not carry drifting copies of docs/theory.

`juggler_review/README.md` names `docs/theory/` the source of truth for the
three manuscripts and says not to hand-edit both copies.  Nothing enforced
that, and the two trees have been edited in lockstep by hand.

`juggler_finite_dynamics_formalization.md` is deliberately excluded: it shares
a filename across the two trees but is *not* a copy.  The bundle version is
trimmed for an external reader and the laboratory version carries table rows
(isolated-E last run, first-intersection taxonomy, homogeneous-run sliding,
peak-valley composition) that the bundle drops.  Copying either way loses text.

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
