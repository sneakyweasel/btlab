"""Every reference a manuscript lists should be cited in its body.

A listed-but-uncited reference is the kind of thing a referee notices and an
author does not, because the bibliography is written last and edited least.
This scans the manuscripts under `docs/theory/` and fails on a NEW one.

Two are already there and are deliberately not failures; see `ACCEPTED`.
"""

from __future__ import annotations

import re
from pathlib import Path

REPO = Path(__file__).resolve().parents[2]
THEORY = REPO / "docs" / "theory"

#: Superseded dated snapshots. They are kept as history, not maintained, and
#: holding them to the live standard would only teach people to edit history.
FROZEN = {"juggler_parity_discrepancy_note_2026_09_04.md"}

#: Listed-but-uncited references that are known and left alone, with why.
#: Adding to this is an editorial decision about someone's bibliography, so it
#: wants a reason and not just a number.
ACCEPTED: dict[str, dict[int, str]] = {
    "juggler_fate_almost_all_note.md": {
        8: (
            "Lagarias (ed.), The Ultimate Challenge -- the standard Collatz "
            "volume, listed as general background. This note carries a DOI, so "
            "whether a background reference needs an inline citation is the "
            "author's call and not a gate's."
        ),
        9: (
            "Weisstein, MathWorld 'Juggler Sequence' -- the sequence's "
            "reference entry, same reasoning as 8."
        ),
    },
}


def _cited(body: str) -> set[int]:
    """Reference numbers cited in `body`, allowing locators.

    A citation bracket is a comma-separated list whose items each begin with a
    number, so `[3, 4]` and `[9, Section 6]` both count. Anything else is not
    a citation: a first pass that took every integer inside square brackets
    swept up intervals like `[0, 1]` and coordinates like `[260]`, which made
    the audit report references as cited that are not.
    """
    found: set[int] = set()
    for match in re.finditer(r"\[([^\]\[]{1,80})\]", body):
        numbers, usable = [], True
        for part in (p.strip() for p in match.group(1).split(",")):
            head = re.match(r"^(\d+)(\s+[A-Za-z].*)?$", part)
            if head:
                numbers.append(int(head.group(1)))
            elif re.match(
                r"^(Section|Theorem|Corollary|Lemma|Chapter|Prop|pp?\.)", part
            ):
                continue
            else:
                usable = False
                break
        if usable:
            found.update(numbers)
    return found


def _manuscripts() -> list[tuple[str, set[int], set[int]]]:
    out = []
    for path in sorted(THEORY.glob("*.md")):
        if path.name in FROZEN:
            continue
        text = path.read_text(encoding="utf-8")
        split = re.search(r"\n#+ References\s*\n(.*)$", text, re.S)
        if not split:
            continue
        listed = {int(n) for n in re.findall(r"^(\d+)\.\s", split.group(1), re.M)}
        if listed:
            out.append((path.name, listed, _cited(text[: split.start()])))
    return out


def test_every_listed_reference_is_cited() -> None:
    """A new uncited reference fails; the two known ones are in ACCEPTED."""
    surprises = {}
    for name, listed, cited in _manuscripts():
        allowed = ACCEPTED.get(name, {})
        missing = sorted(n for n in listed if n not in cited and n not in allowed)
        if missing:
            surprises[name] = missing
    assert not surprises, (
        "reference(s) listed but never cited in the body:\n"
        + "\n".join(f"    {k}: {v}" for k, v in surprises.items())
        + "\n\nCite them, drop them, or add them to ACCEPTED with a reason."
    )


def test_accepted_entries_are_still_uncited() -> None:
    """Drop an entry from ACCEPTED once the manuscript cites it."""
    stale = {}
    for name, listed, cited in _manuscripts():
        fixed = sorted(n for n in ACCEPTED.get(name, {}) if n in cited or n not in listed)
        if fixed:
            stale[name] = fixed
    assert not stale, (
        f"ACCEPTED entries no longer apply and should be removed: {stale}"
    )


def test_paper_b_cites_lagarias_for_the_rate() -> None:
    """The attribution fixed on 20 September, pinned so it cannot slip back.

    The manuscript had said the exponential rate "is not folklore" and
    credited Hikawa's July 2026 preprint, citing Lagarias nowhere in 3200
    lines. The rate is Theorem D of the 1985 survey and the link is an
    identity, `2^(-eta) = vartheta(p)`, checked to fifty digits in
    `test_jump_spectrum.py`.
    """
    paper = (THEORY / "juggler_parity_discrepancy_note.md").read_text(
        encoding="utf-8"
    )
    assert "Theorem D of Lagarias" in paper
    assert "10.1080/00029890.1985.11971528" in paper
    assert "the rate is not folklore" not in paper
    # Hikawa keeps the weight-basis form and the conjecture
    assert "Conjecture 7.1" in paper


def test_prose_ledger_references_resolve() -> None:
    """A row id named in prose must exist, or the prose is pointing at nothing.

    `paper_b_prior_art_and_names.md` argues almost entirely by reference: what
    is prior, what survives, and which row backs each. A renamed or deleted
    row would leave the argument reading as if it were still supported. This
    resolves every backticked `J-...` id in `docs/theory/*.md` against the
    ledger.
    """
    import json

    ledger = json.loads(
        (REPO / "docs" / "theory" / "theorem_ledger.json").read_text(
            encoding="utf-8"
        )
    )
    known = {row["id"] for row in ledger}

    dangling: dict[str, list[str]] = {}
    for path in sorted(THEORY.glob("*.md")):
        if path.name in FROZEN:
            continue
        cited = set(re.findall(r"`(J-[a-z0-9-]+)`", path.read_text(encoding="utf-8")))
        missing = sorted(c for c in cited if c not in known)
        if missing:
            dangling[path.name] = missing
    assert not dangling, (
        "prose names ledger rows that do not exist:\n"
        + "\n".join(f"    {k}: {v}" for k, v in dangling.items())
    )
