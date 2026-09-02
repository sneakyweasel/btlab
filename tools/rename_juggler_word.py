"""Rename Juggler 'word' to 'itinerary'. Does not touch BT packWord."""

from __future__ import annotations

import re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]

WALK = [
    ROOT / "formal" / "Problems" / "Juggler",
    ROOT / "formal" / "Problems" / "Juggler.lean",
    ROOT / "formal" / "Problems" / "JugglerPaper.lean",
    ROOT / "src" / "research" / "juggler_sequence",
    ROOT / "tests" / "research" / "juggler_sequence",
    ROOT / "web" / "juggler-companion" / "src",
    ROOT / "docs" / "theory",
    ROOT / "docs" / "problems",
    ROOT / "docs" / "research",
    ROOT / "docs" / "juggler_branch_ledger.md",
    ROOT / "docs" / "research_journal.md",
    ROOT / "conjectures",
    ROOT / "AGENTS.md",
    ROOT / "juggler_review" / "juggler_finite_dynamics_note.md",
    ROOT / "juggler_review" / "juggler_finite_dynamics_formalization.md",
    ROOT / "juggler_review" / "juggler_finite_dynamics_reviewer_packet.md",
    ROOT / "juggler_review" / "README.md",
]

SKIP_DIR_NAMES = {
    "node_modules",
    "__pycache__",
    ".git",
    "word_atlas",
}

TEXT_SUFFIX = {
    ".lean",
    ".py",
    ".ts",
    ".tsx",
    ".md",
    ".json",
    ".toml",
    ".css",
}

# Longest identifier / phrase first.
REPLACEMENTS: list[tuple[str, str]] = [
    ("has_no_cycle_word", "has_no_cycle_itinerary"),
    ("no_cycle_word", "no_cycle_itinerary"),
    ("cycle_word_formally_expanding", "cycle_itinerary_formally_expanding"),
    ("cycle_word", "cycle_itinerary"),
    ("CycleWord", "CycleItinerary"),
    ("cycleWordB", "cycleItineraryB"),
    ("cycleWord", "cycleItinerary"),
    ("rotateWord", "rotateItinerary"),
    ("rotate_word", "rotate_itinerary"),
    ("follows_iff_word", "follows_iff_itinerary"),
    ("followsWord", "followsItinerary"),
    ("follows_word", "follows_itinerary"),
    ("expandingWord", "expandingItinerary"),
    ("parseWord", "parseItinerary"),
    ("parse_word", "parse_itinerary"),
    ("WalkChargeWords", "WalkChargeItineraries"),
    ("AppearingWord", "AppearingItinerary"),
    ("WordStats", "ItineraryStats"),
    ("WordLanguage", "ItineraryLanguage"),
    ("WordTab", "ItineraryTab"),
    ("WORD_PRESETS", "ITINERARY_PRESETS"),
    ("wordPrefix", "itineraryPrefix"),
    ("wordSuffix", "itinerarySuffix"),
    ("wordFactor", "itineraryFactor"),
    ("word_zero", "itinerary_zero"),
    ("word_succ", "itinerary_succ"),
    ("word_length", "itinerary_length"),
    ("gapped_cycle_word", "gapped_cycle_itinerary"),
    ("leftover_words", "leftover_itineraries"),
    ("power_words", "power_itineraries"),
    ("word_language", "itinerary_language"),
    ("cycle word", "cycle itinerary"),
    ("Cycle word", "Cycle itinerary"),
    ("Cycle Word", "Cycle itinerary"),
    ("realized word", "realized itinerary"),
    ("Realized word", "Realized itinerary"),
    ("formal word", "formal itinerary"),
    ("Formal word", "Formal itinerary"),
    ("rotation word", "rotation itinerary"),
    ("Rotation word", "Rotation itinerary"),
    ("hug word", "hug itinerary"),
    ("Hug word", "Hug itinerary"),
    ("word identity", "itinerary identity"),
    ("Word identity", "Itinerary identity"),
    ("combinatorial word", "combinatorial itinerary"),
    ("parity word", "parity itinerary"),
    ("finite word", "finite itinerary"),
    ("Finite word", "Finite itinerary"),
    ("expanding word", "expanding itinerary"),
    ("Expanding word", "Expanding itinerary"),
    ("contracting word", "contracting itinerary"),
    ("minimum-based word", "minimum-based itinerary"),
    ("leftover word", "leftover itinerary"),
    ("Leftover word", "Leftover itinerary"),
    ("bootstrap word", "bootstrap itinerary"),
    ("survivor word", "survivor itinerary"),
    ("mixed word", "mixed itinerary"),
    ("all-odd word", "all-odd itinerary"),
    ("all-odd words", "all-odd itineraries"),
    ("those words", "those itineraries"),
    ("these words", "these itineraries"),
    ("the words", "the itineraries"),
    ("The words", "The itineraries"),
    ("a word", "an itinerary"),
    ("A word", "An itinerary"),
    ("the word", "the itinerary"),
    ("The word", "The itinerary"),
    ("this word", "this itinerary"),
    ("This word", "This itinerary"),
    ("that word", "that itinerary"),
    ("That word", "That itinerary"),
    ("any word", "any itinerary"),
    ("every word", "every itinerary"),
    ("no word", "no itinerary"),
    ("No word", "No itinerary"),
    ("of words", "of itineraries"),
    ("of word", "of itinerary"),
    ("word so far", "itinerary so far"),
    ("Word so far", "Itinerary so far"),
    ("Word from", "Itinerary from"),
    ("words over", "itineraries over"),
    ("word of length", "itinerary of length"),
    ("words of length", "itineraries of length"),
    ("word census", "itinerary census"),
    ("word geometry", "itinerary geometry"),
    ("word obstruction", "itinerary obstruction"),
    ("word restrictions", "itinerary restrictions"),
    ("**Word.**", "**Itinerary.**"),
    ("**Word**", "**Itinerary**"),
    ("# Word", "# Itinerary"),
]

# After phrases, leftover identifier-ish `word` in Lean/TS/Py.
IDENT_WORD = [
    (re.compile(r"\bwordEOO\b"), "itineraryEOO"),
    (re.compile(r"\bdef word\b"), "def itinerary"),
    (re.compile(r"\btheorem word\b"), "theorem itinerary"),
    (re.compile(r"\blemma word\b"), "lemma itinerary"),
    (re.compile(r"(?<![A-Za-z0-9_])word n\b"), "itinerary n"),
    (re.compile(r"(?<![A-Za-z0-9_])word \("), "itinerary ("),
    (re.compile(r"\[word,"), "[itinerary,"),
    (re.compile(r"\[word\]"), "[itinerary]"),
    (re.compile(r"\bword,"), "itinerary,"),
    (re.compile(r"`word`"), "`itinerary`"),
    (re.compile(r"`word "), "`itinerary "),
]

PROTECT = [
    ("packWord", "⟦PACKWORD⟧"),
    ("in other words", "⟦INOTHERWORDS⟧"),
    ("In other words", "⟦INOTHERWORDS_CAP⟧"),
    ("keywords", "⟦KEYWORDS⟧"),
    ("password", "⟦PASSWORD⟧"),
    ("WordSimp", "⟦WORDSIMP⟧"),
    ("Representation.Words", "⟦REPWORDS⟧"),
    ("control_word", "⟦CONTROLWORD⟧"),
    ("word_atlas", "⟦WORDATLAS⟧"),
    ("formal_words", "⟦FORMALWORDS⟧"),
    ("coeffword", "⟦COEFFWORD⟧"),
    ("rewrite-word", "⟦REWRITEWORD⟧"),
    ("rewrite word", "⟦REWRITEWORDSP⟧"),
]


def iter_files() -> list[Path]:
    out: list[Path] = []
    for root in WALK:
        if root.is_file():
            if root.suffix in TEXT_SUFFIX:
                out.append(root)
            continue
        if not root.is_dir():
            continue
        for path in root.rglob("*"):
            if not path.is_file():
                continue
            if any(part in SKIP_DIR_NAMES for part in path.parts):
                continue
            if path.suffix not in TEXT_SUFFIX:
                continue
            out.append(path)
    return out


def rewrite(text: str) -> str:
    for src, tok in PROTECT:
        text = text.replace(src, tok)
    for src, dst in REPLACEMENTS:
        text = text.replace(src, dst)
    for pat, dst in IDENT_WORD:
        text = pat.sub(dst, text)
    for src, tok in PROTECT:
        text = text.replace(tok, src)
    return text


def main() -> None:
    changed = 0
    for path in iter_files():
        original = path.read_text(encoding="utf-8")
        updated = rewrite(original)
        if updated != original:
            path.write_text(updated, encoding="utf-8", newline="\n")
            changed += 1
            print(path.relative_to(ROOT))
    print(f"updated {changed} files")


if __name__ == "__main__":
    main()
