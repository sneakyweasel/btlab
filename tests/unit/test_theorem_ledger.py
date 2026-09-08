"""Theorem ledger paths must exist; markdown must match the JSON."""

from __future__ import annotations

import json
import re
import subprocess
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "tools"))

from render_theorem_ledger import HEADER, TAGS, check_tags  # noqa: E402

ROOT = Path(__file__).resolve().parents[2]
JSON_PATH = ROOT / "docs" / "theory" / "theorem_ledger.json"
LEAN_VERIFIED = "EXACT — LEAN VERIFIED"


def _entries() -> list[dict]:
    return json.loads(JSON_PATH.read_text(encoding="utf-8"))


def _decls(row: dict) -> list[str]:
    """The declarations a row names. ``decl`` is a string for one, a list for many."""
    decl = row.get("decl")
    if not decl:
        return []
    return [decl] if isinstance(decl, str) else list(decl)


def test_ledger_ids_are_unique():
    ids = [row["id"] for row in _entries()]
    assert ids
    assert len(ids) == len(set(ids))


def test_ledger_required_fields():
    required = ("id", "tag", "statement", "source", "lean", "tests")
    for row in _entries():
        for key in required:
            assert key in row, f"{row.get('id')}: missing {key}"
        source = ROOT / str(row["source"])
        assert source.is_file(), f"{row['id']}: missing source {row['source']}"


def test_ledger_test_paths_exist():
    for row in _entries():
        tests = row.get("tests") or []
        assert tests, f"{row['id']}: tests must be a non-empty list"
        for rel in tests:
            path = ROOT / rel
            assert path.is_file(), f"{row['id']}: missing test {rel}"


def test_ledger_lean_paths_exist_when_required():
    for row in _entries():
        lean = str(row.get("lean") or "").strip()
        if not lean:
            assert row["tag"] != LEAN_VERIFIED, f"{row['id']}: LEAN VERIFIED needs a lean path"
            continue
        path = ROOT / "formal" / lean
        if not path.exists():
            path = ROOT / lean
        assert path.exists(), f"{row['id']}: missing lean {lean}"
        if row["tag"] == LEAN_VERIFIED:
            assert path.is_file() or path.is_dir(), f"{row['id']}: lean path is not a file or dir"


def test_ledger_tags_are_in_the_fixed_vocabulary():
    assert check_tags(_entries()) == []


def test_documented_tags_match_the_whitelist():
    for tag in TAGS:
        assert f"`{tag}`" in HEADER, f"{tag} is missing from the rendered tag list"
    readme = (ROOT / "docs" / "README.md").read_text(encoding="utf-8")
    for tag in TAGS:
        assert tag in readme, f"{tag} is missing from docs/README.md"


def test_ledger_markdown_is_generated():
    script = ROOT / "tools" / "render_theorem_ledger.py"
    result = subprocess.run(
        [sys.executable, str(script), "--check"],
        cwd=ROOT,
        check=False,
        capture_output=True,
        text=True,
    )
    assert result.returncode == 0, result.stdout + result.stderr


def test_decl_when_present_names_a_declaration_in_the_rows_own_file():
    """The ``decl`` field is the join the ``lean`` file pointer cannot make.

    A row naming a declaration that is not in its file is worse than a row naming none:
    it reads as a resolved claim while pointing somewhere else.
    """
    import re

    for row in _entries():
        decls = _decls(row)
        if not decls:
            continue
        lean = str(row.get("lean") or "").strip()
        assert lean.endswith(".lean"), f"{row['id']}: decl needs a file, not {lean!r}"
        text = (ROOT / "formal" / lean).read_text(encoding="utf-8")
        assert len(decls) == len(set(decls)), f"{row['id']}: repeats a declaration"
        for decl in decls:
            pattern = (rf"^\s*(?:theorem|lemma|def|abbrev|instance|structure)\s+"
                       rf"{re.escape(decl)}\b")
            assert re.search(pattern, text, re.MULTILINE), f"{row['id']}: {decl} not in {lean}"


def test_lean_trust_is_recorded_wherever_a_declaration_is_named():
    """``EXACT — LEAN VERIFIED`` does not distinguish kernel from ``native_decide``.

    Paper A's Section 1.2 states that boundary in prose; a row that names its declaration
    can carry it as data, so the tag stops having two meanings.
    """
    for row in _entries():
        decls = _decls(row)
        if decls:
            assert row.get("lean_trust") in {"kernel", "compiler", "mixed", "open"}, row["id"]
            if row["lean_trust"] == "mixed":
                assert len(decls) > 1, f"{row['id']}: one declaration cannot be mixed"
                assert row.get("compiler_decls"), f"{row['id']}: mixed must say which"
            for name in row.get("compiler_decls", []):
                assert name in decls, f"{row['id']}: compiler_decls has unnamed {name}"


def test_a_statement_naming_a_lean_theorem_names_one_that_exists():
    """Rows say "Lean theorem `foo`" in prose; that is the join, and it must resolve.

    This convention is how 34 rows were matched to their declaration. It only stays useful
    if a rename cannot quietly leave the sentence pointing at nothing.
    """
    import re

    named = re.compile(r"Lean theorem\s+([A-Za-z][A-Za-z0-9_']*_[A-Za-z0-9_']+)")
    decl = re.compile(r"^\s*(?:theorem|lemma|def|abbrev|instance|structure)\s+([A-Za-z_][A-Za-z0-9_'!?.]*)",
                      re.MULTILINE)
    broken = []
    for row in _entries():
        lean = str(row.get("lean") or "").strip()
        if not lean.endswith(".lean"):
            continue
        path = ROOT / "formal" / lean
        if not path.is_file():
            continue
        present = set(decl.findall(path.read_text(encoding="utf-8")))
        for name in named.findall(row["statement"]):
            if name not in present:
                broken.append(f"{row['id']}: names {name}, absent from {lean}")
    assert broken == [], broken


def test_decl_agrees_with_the_theorem_the_statement_names():
    """Where a row both names a theorem in prose and carries `decl`, they must be the same."""
    import re

    named = re.compile(r"Lean theorem\s+([A-Za-z][A-Za-z0-9_']*_[A-Za-z0-9_']+)")
    for row in _entries():
        decls = _decls(row)
        if len(decls) != 1:
            continue
        names = named.findall(row["statement"])
        if names:
            assert decls[0] in names, f"{row['id']}: decl={decls[0]} but prose names {names}"


def test_no_two_rows_claim_the_same_declaration():
    """A theorem backs one claim. Two rows on one declaration means at least one is wrong,
    or the two rows are really one -- either way it wants a person's eye, not silence."""
    import collections

    claims = collections.Counter(
        (row["lean"], name) for row in _entries() for name in _decls(row)
    )
    shared = {k: v for k, v in claims.items() if v > 1}
    assert shared == {}, shared


def test_no_row_chose_a_declaration_far_worse_than_one_it_names():
    """A row citing a sibling is normal prose, not a mis-join.

    The earlier form of this guard flagged any row whose statement named a declaration other
    than its `decl`. That fired seven times and caught nothing: "the dictionary *for*
    origin_particular", "particular_concat at c_R = 0", "equivalently energy_telescope on the
    zero word" are all correct joins with a citation.

    What did catch a real error was the size of the gap. `J-cyclemin-hug-charge-max` had been
    joined to `stateCharge_antitone`, a supporting lemma scoring 0.06, while naming
    `hug_charge_maximal` at 0.233 -- and the row is composite, so no single `decl` was right.
    Every correct join sits below 1.7x; that one was 3.9x. The threshold is set at 3x, which
    is wide enough to stay quiet on citation and narrow enough to have caught the one mistake.
    """
    import sys

    sys.path.insert(0, str(ROOT / "tools"))
    import formalpedia as fp

    index = fp.build()
    byname = {(d["file"], d["name"]): d for d in index["declarations"]}
    ident = re.compile(r"[A-Za-z][A-Za-z0-9_']*_[A-Za-z0-9_']+")
    bad = []
    for row in _entries():
        # The gap test asks whether a row picked the wrong single theorem. A row that names
        # its whole inventory has no single answer to be wrong about, so it has nothing to say.
        decls = _decls(row)
        if len(decls) != 1:
            continue
        decl = decls[0]
        path = "formal/" + str(row.get("lean"))
        chosen = byname.get((path, decl))
        if chosen is None:
            continue
        words = fp.words(row["statement"])
        mine = fp.similarity(words, chosen)
        for name in dict.fromkeys(ident.findall(row["statement"])):
            other = byname.get((path, name))
            if other is None or name == decl:
                continue
            if fp.similarity(words, other) > 3.0 * max(mine, 1e-9):
                bad.append(f"{row['id']}: chose {decl} ({mine:.3f}) over {name} "
                           f"({fp.similarity(words, other):.3f})")
    assert bad == [], bad

def test_no_row_credits_native_decide_to_a_kernel_checked_declaration():
    """Tactic names drift out of prose the way constants do.

    ``J-cyclemin-walk-ostrowski-arithmetic`` credited ``theta_sandwich_upper/lower`` to
    ``native_decide`` after both had been converted to ``norm_num``; their own docstrings
    said "Kernel-checked". A row naming a declaration beside the words ``native_decide``
    should be naming one that actually uses it.
    """
    import re

    for row in _entries():
        statement = row.get("statement", "")
        if "native_decide" not in statement:
            continue
        lean = str(row.get("lean") or "").strip()
        if not lean.endswith(".lean"):
            continue
        path = ROOT / "formal" / lean
        if not path.is_file():
            continue
        text = path.read_text(encoding="utf-8")
        # names appearing within 120 characters before the word native_decide
        for m in re.finditer(r"native_decide", statement):
            window = statement[max(0, m.start() - 120): m.start()]
            for name in re.findall(r"[A-Za-z][A-Za-z0-9_']*_[A-Za-z0-9_']+", window):
                block = re.search(
                    r"(?:^|\n)\s*theorem\s+" + re.escape(name) + r"(?![A-Za-z0-9_'])(.*?)(?=\n\s*(?:theorem|lemma|def|/--)|\Z)",
                    text, re.S)
                if block is not None:
                    assert "native_decide" in block.group(1), (
                        f"{row['id']}: names {name} beside native_decide, but it does not use it"
                    )


def test_recorded_trust_matches_what_the_declarations_actually_are():
    """``lean_trust`` is a claim about the kernel boundary, so the Lean must still agree.

    Paper A Section 1.2 states that boundary in prose and the ledger is what backs it. A row
    that says ``kernel`` while one of its declarations proves by ``native_decide`` reads as
    machine-checked at a strength it does not have -- the exact confusion the flat
    ``EXACT — LEAN VERIFIED`` tag caused before the trust field existed.
    """
    import sys

    sys.path.insert(0, str(ROOT / "tools"))
    import formalpedia as fp

    index = fp.build()
    byname = {(d["file"], d["name"]): d for d in index["declarations"]}
    for row in _entries():
        decls = _decls(row)
        recorded = row.get("lean_trust")
        if not decls or recorded == "open":
            continue
        found = {}
        for name in decls:
            d = byname.get(("formal/" + str(row.get("lean")), name))
            if d is not None:
                found[name] = d["trust"]
        if not found:
            continue
        levels = set(found.values())
        expected = levels.pop() if len(levels) == 1 else "mixed"
        assert recorded == expected, f"{row['id']}: says {recorded}, Lean says {expected} ({found})"
        if expected == "mixed":
            compiler = sorted(n for n, t in found.items() if t == "compiler")
            assert sorted(row.get("compiler_decls", [])) == compiler, (
                f"{row['id']}: compiler_decls should be {compiler}"
            )
