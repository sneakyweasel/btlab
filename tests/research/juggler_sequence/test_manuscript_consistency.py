"""Cross-document consistency for Paper A.

Every defect found in the last three iterations of work on this paper was the same species:
a change to the manuscript that silently invalidated prose elsewhere.  Extending Theorem 5.8's
window to q_14 falsified an Appendix A row, a glossary entry, six passages in the reviewer
packet, a constant in the companion app, and -- worst -- a line in the app's NOT_CLAIMED list,
which asserted the opposite of the new text.  None of it was covered by a test, because prose
is not executable.

These tests make that class checkable.  They do not verify mathematics; they verify that the
manuscript, the certificate, the review materials and the app agree about the numbers they all
quote, and that the manuscript's own numbering is in document order.
"""

from __future__ import annotations

import io
import re
from pathlib import Path

import pytest

from research.juggler_sequence import paper_a_audit as A

ROOT = Path(__file__).resolve().parents[3]
PAPER = ROOT / "docs" / "theory" / "juggler_finite_dynamics_note.md"
MIRROR = ROOT / "juggler_review" / "juggler_finite_dynamics_note.md"
PACKET = ROOT / "juggler_review" / "juggler_finite_dynamics_reviewer_packet.md"
README = ROOT / "juggler_review" / "README.md"
FORMALIZATION = ROOT / "juggler_review" / "juggler_finite_dynamics_formalization.md"
APP_CONSTANTS = ROOT / "web" / "juggler-companion" / "src" / "juggler" / "constants.ts"
APP_CLAIMS = ROOT / "web" / "juggler-companion" / "src" / "content" / "claims.ts"
APP_GLOSSARY = ROOT / "web" / "juggler-companion" / "src" / "content" / "glossary.ts"

REVIEW_DOCS = [PACKET, README, FORMALIZATION]


def read(p: Path) -> str:
    return io.open(p, encoding="utf-8").read()


# --- the manuscript's own numbering ---


def test_section_5_items_are_in_document_order() -> None:
    """Regression: Propositions 5.15/5.16 once sat between Theorems 5.8 and 5.9."""
    text = read(PAPER)
    found = re.findall(r"^\*\*(?:Theorem|Lemma|Corollary|Proposition) (5\.\d+[a-z]?)",
                       text, re.MULTILINE)

    def key(label: str) -> tuple[int, str]:
        m = re.match(r"5\.(\d+)([a-z]?)", label)
        return int(m.group(1)), m.group(2)

    keys = [key(f) for f in found]
    assert keys == sorted(keys), found


def test_every_numbered_item_is_unique_in_the_body() -> None:
    """Uniqueness holds in the body only: Appendix D deliberately restates the Section 3
    theorems above their proofs, which is not a numbering defect."""
    text = read(PAPER)
    body = text[: text.index("## Appendix")]
    found = re.findall(r"^\*\*(?:Theorem|Lemma|Corollary|Proposition) (\d+\.\d+[a-z]?)",
                       body, re.MULTILINE)
    assert len(found) == len(set(found)), [f for f in found if found.count(f) > 1]


def test_no_number_is_used_for_two_different_items() -> None:
    """The real numbering invariant, given that appendices both restate and introduce.

    Appendix D restates the Section 3 theorems above their proofs (same number, same title --
    fine), and Appendix C introduces Theorems 2.4-2.7 continuing Section 2's numbering (new
    number, not in the body -- also fine).  What must never happen is one number carrying two
    different titles.
    """
    text = read(PAPER)
    pairs = re.findall(
        r"^\*\*(?:Theorem|Lemma|Corollary|Proposition) (\d+\.\d+[a-z]?) \(([^)]*)\)",
        text, re.MULTILINE)
    titles: dict[str, set[str]] = {}
    for num, title in pairs:
        titles.setdefault(num, set()).add(title.strip().rstrip("."))
    clashes = {n: t for n, t in titles.items() if len(t) > 1}
    assert not clashes, clashes


# --- the window, which is what actually drifted ---


def test_window_endpoint_agrees_everywhere() -> None:
    """The extended window must read the same in the paper, the review docs and the app."""
    hi = str(A.WINDOW_HI)
    assert hi in read(PAPER)
    for doc in REVIEW_DOCS:
        assert hi in read(doc), doc.name
    assert "WALK_WINDOW_HI = 16_785_921" in read(APP_CONSTANTS)


def test_no_document_still_quotes_the_old_window_as_the_window() -> None:
    """301994 is legitimate as q_13 and in the fan arithmetic, but not as a window endpoint."""
    bad = re.compile(r"\[\s*50508\s*,\s*301994\s*\)")
    for doc in [PAPER, MIRROR, PACKET, README, FORMALIZATION, APP_CLAIMS, APP_GLOSSARY]:
        assert not bad.search(read(doc)), doc.name


def test_window_covers_the_whole_fan() -> None:
    """The window's endpoint is exactly the last fan member: q_14 = L_55."""
    assert A.WINDOW_HI == A.fan_length(A.FAN_LEN - 1) == 16785921


# --- constants shared by the manuscript, the certificate and the app ---


@pytest.mark.parametrize("name,value", [
    ("PAPER_FLOOR", 1_000_000), ("PAPER_PERIOD", 25_781),
    ("LAB_FLOOR", 26_254_995), ("LAB_PARITY_PERIOD", 50_508),
    ("LAB_WALK_PERIOD", 176_251),
    ("PRINTED_FLOOR", 162_849_448), ("PRINTED_PERIOD", 478_245),
])
def test_app_constants_match_the_certificate(name: str, value: int) -> None:
    src = read(APP_CONSTANTS)
    m = re.search(rf"export const {name} = ([\d_]+);", src)
    assert m, name
    assert int(m.group(1).replace("_", "")) == value


def test_certified_floors_and_bounds_match_the_audit() -> None:
    """The four (floor, period) pairs the paper prints are the audit's FLOORS table."""
    pairs = {(n0, bound) for n0, bound, _site in A.FLOORS}
    assert (10**6, 25781) in pairs
    assert (26254995, 50508) in pairs
    # the paper writes floors in LaTeX (10^6, 26254995, ...), so match either form
    text = read(PAPER)
    for n0, _bound, _ in A.FLOORS:
        plain = str(n0)
        latex = "10^{%d}" % len(plain[1:]) if plain[0] == "1" and set(plain[1:]) == {"0"} else None
        assert plain in text or (latex and latex in text), n0


def test_fan_endpoints_quoted_in_the_paper() -> None:
    for k in (0, 1, 2):
        assert str(A.fan_length(k)) in read(PAPER)
    assert str(A.fan_length(55)) in read(PAPER)


# --- the mirror, which reviewers actually read ---


def test_review_mirror_matches_the_manuscript() -> None:
    assert read(PAPER) == read(MIRROR), "juggler_review mirror is stale; re-copy it"


# --- Appendix A must mention every registered Lean module ---


def test_appendix_A_mentions_the_fan_law_module() -> None:
    """Regression: FanLaw.lean was registered and built but absent from Appendix A."""
    text = read(PAPER)
    idx = text.index("## Appendix A")
    appendix = text[idx:]
    assert "FanLaw.lean" in appendix
    for name in ("fanLambda_affine", "fan_positive_iff", "fanLambda_55_pos"):
        assert name in appendix, name
