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

#: The one reason a row may name no test. A reading of a primary source is evidence no
#: Python test reaches; every other kind leaves something in the repository to hold.
EVIDENCE_WITHOUT_TESTS = frozenset({"literature"})

#: Tags that assert an artifact in the repository, so a row carrying one has a test to name.
TESTABLE_TAGS = frozenset({LEAN_VERIFIED, "COMPUTATIONALLY VERIFIED"})

#: Modifiers Lean allows in front of a declaration's keyword, in any order and any number.
#: The index reads them (``tools/formalpedia.py``, ``DECL``); the gates below did not, so
#: ``noncomputable def budget`` was a declaration the index held and the gate denied.
DECL_MODIFIER = r"(?:(?:private|protected|noncomputable|partial|unsafe|nonrec)\s+)*"

#: The keywords a declaration opens with.
DECL_KEYWORD = r"(?:theorem|lemma|def|abbrev|instance|structure)"

#: What may not follow a declaration's name. ``\b`` was wrong at both ends here, because ``'``
#: is not a word character: it accepted ``foo`` against ``theorem foo'`` and rejected ``foo'``
#: against ``theorem foo'``. Lean's identifiers admit ``'``, ``!`` and ``?``, so the end of a
#: name is the absence of one of those, not a word boundary.
DECL_TAIL = r"(?![A-Za-z0-9_'!?])"

#: An attribute block in front of the keyword, on the declaration's own line. 70 declarations
#: in ``formal/`` are written ``@[simp] theorem foo``; the index reads them
#: (``tools/formalpedia.py``, ``_ATTR``) and without this the gate would deny all 70.
DECL_ATTR = r"(?:@\[[^\]]*\][ \t]*)*"

#: The name a declaration line opens with, captured.
DECL_NAME = r"([A-Za-z_][A-Za-z0-9_'!?.]*)"

#: Every declaration a file opens, by name.
DECL_LINE = re.compile(
    rf"^\s*{DECL_ATTR}{DECL_MODIFIER}{DECL_KEYWORD}\s+{DECL_NAME}", re.MULTILINE
)


def _declares(text: str, name: str) -> bool:
    """Does ``text`` open a declaration named exactly ``name``?"""
    return re.search(
        rf"^\s*{DECL_ATTR}{DECL_MODIFIER}{DECL_KEYWORD}\s+{re.escape(name)}{DECL_TAIL}",
        text,
        re.MULTILINE,
    ) is not None


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
    """A row names the tests that exercise it, or says in the data why none does.

    ``"tests": []`` carried two meanings and the assertion could not tell them apart: a row
    nobody had wired to the test that already held it, and a row whose evidence is a reading
    of a primary source, which no Python test reaches. Eleven rows sat in that gap. Six were
    the first kind -- Paper B Lean modules whose siblings on the same files already cite
    ``test_layer_architecture`` and ``test_paper_b_prefix_count`` -- and they are wired now.
    Five were the second: the external-input audit, whose evidence is Rhin p. 160 and
    Wu-Wang p. 266 read at source. Nothing in the repository holds those, and the audit
    module that looks like their test records the state BEFORE the reading.

    So the distinction is carried as data, the way ``lean_trust`` carries the kernel
    boundary. The waiver must be declared, and a row may not claim it while naming a Lean
    module or asserting a computation -- both leave something a test can reach.
    """
    for row in _entries():
        tests = row.get("tests") or []
        evidence = row.get("evidence")
        if evidence is not None:
            assert evidence in EVIDENCE_WITHOUT_TESTS, (
                f"{row['id']}: unknown evidence {evidence!r}, "
                f"expected one of {sorted(EVIDENCE_WITHOUT_TESTS)}"
            )
            assert not tests, f"{row['id']}: declares {evidence} evidence and also names tests"
        if not tests:
            assert evidence in EVIDENCE_WITHOUT_TESTS, (
                f"{row['id']}: names no test and gives no reason; either cite the test that "
                f"exercises it or declare evidence from {sorted(EVIDENCE_WITHOUT_TESTS)}"
            )
            assert not str(row.get("lean") or "").strip(), (
                f"{row['id']}: claims {evidence} evidence but names a Lean module, which "
                "test_layer_architecture holds"
            )
            assert row["tag"] not in TESTABLE_TAGS, (
                f"{row['id']}: claims {evidence} evidence under {row['tag']}, which asserts "
                "something a test can reach"
            )
        for rel in tests:
            path = ROOT / rel
            assert path.is_file(), f"{row['id']}: missing test {rel}"


#: Rows whose `lean` value the invariant below cannot yet hold to.
#: Each needs a human verdict, not a parser change, and the set must not grow.
LEAN_PATH_EXCEPTIONS = {
    "C-affine-formula": (
        "names the directory Problems/Collatz/ rather than a module, while tagged "
        "EXACT - LEAN VERIFIED. No single declaration states its conclusion "
        "T^m(n)=(3^m n+C)/2^K: the affine endpoint threePow * n + C = twoPow * x appears "
        "in Cycles.lean and FixedInteger.lean only as a HYPOTHESIS. Either a declaration "
        "proves it and should be named, or the tag is wrong. Both are mathematical calls."
    ),
}


def test_every_lean_row_is_attributed_to_its_module_in_the_index():
    """A row's `lean` must resolve to a module that formalpedia credits the row to.

    The invariant whose absence cost 346 declarations: tools/formalpedia.py prepended
    "formal/" unconditionally, so the 43 rows whose value already began with "formal/"
    keyed to "formal/formal/..." and matched nothing. Those rows were attached to no
    module and every gate stayed green, because the gates above accept either spelling
    and never ask whether the index agrees.

    Attribution is the thing to assert, not presence. A first draft of this test checked
    that the row's file appears in the index at all and passed against the broken index
    too: `modules` always held all 315 entries, because the bug corrupted which rows a
    module was credited with, not whether the module existed. Checked against the
    pre-fix index at a9f8efce, this formulation fails on exactly those 43 rows and the
    current index passes.
    """
    index = json.loads((ROOT / "data" / "research" / "formalpedia" / "index.json")
                       .read_text(encoding="utf-8"))
    # Keyed by resolved path, so the check never re-implements the prefix convention it guards.
    by_path = {(ROOT / m["file"]).resolve(): (name, m)
               for name, m in index["modules"].items() if m.get("file")}

    orphaned = []
    for row in _entries():
        lean = str(row.get("lean") or "").strip()
        if not lean or row["id"] in LEAN_PATH_EXCEPTIONS:
            continue
        if not lean.endswith(".lean"):
            orphaned.append(f"{row['id']}: lean {lean!r} is not a .lean file")
            continue
        hit = next((c for c in ((ROOT / "formal" / lean).resolve(), (ROOT / lean).resolve())
                    if c.is_file()), None)
        if hit is None:
            orphaned.append(f"{row['id']}: lean {lean!r} resolves to no file")
            continue
        if hit not in by_path:
            orphaned.append(f"{row['id']}: {lean!r} exists but formalpedia indexes no module for it")
            continue
        name, module = by_path[hit]
        listed = {entry if isinstance(entry, str) else entry.get("id")
                  for entry in (module.get("ledger") or [])}
        if row["id"] not in listed:
            orphaned.append(
                f"{row['id']}: {name} does not credit it - the row names a module and the "
                f"module has never heard of the row. Rebuild data/research/formalpedia/, and "
                f"if it persists the attribution is broken again")
    assert orphaned == [], chr(10).join(orphaned)


def test_the_lean_path_exception_list_does_not_grow():
    """New rows fix the invariant; they do not join the exception list."""
    assert set(LEAN_PATH_EXCEPTIONS) == {"C-affine-formula"}


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


#: Declarations the gate denied while the index held them, as (file, name). Six sit behind
#: ``noncomputable``; one ends in a prime. Every one of them is real, indexed, and was
#: rejected -- which is why 42 otherwise-correct ``decl`` entries were dropped on 2026-09-21
#: while the coverage audit's not-covered band was rejoined (506dd239).
DENIED_BY_THE_OLD_GATE = (
    ("Problems/Juggler/ReturnWordLoss.lean", "budget"),
    ("Problems/Juggler/FateChernoff.lean", "oddFailures"),
    ("Problems/Juggler/FateChernoff.lean", "scaleRatio"),
    ("Problems/Juggler/FateShareLaw.lean", "extremeMeasure"),
    ("Problems/Juggler/FateShareLaw.lean", "phi"),
    ("Problems/Juggler/QuarticCells.lean", "logEta"),
    ("Problems/Juggler/FateTaoReduction.lean", "treeLevel_logMass_le'"),
)

#: The regex the gates carried before the widening, kept so the defect cannot come back
#: unnoticed. A later simplification that restores ``\b`` will fail this file, not the band.
_SUPERSEDED = r"^\s*(?:theorem|lemma|def|abbrev|instance|structure)\s+{}\b"


def test_the_declaration_regex_reads_the_forms_lean_actually_writes():
    """A declaration may wear a modifier, and a name may end in a prime.

    The gate's alternation began at the keyword, so ``noncomputable def budget`` never
    matched: the modifier stood where the keyword had to be. And the name ended at ``\\b``,
    which cannot close after ``'`` -- a non-word character -- so ``treeLevel_logMass_le'``
    failed against its own declaration line.

    Neither failure is a ledger error. Both names are in the file, both are in the index, and
    the gate said no. That is the shape of a check that is green for nothing: it was not
    holding the ledger to the Lean, it was holding it to a subset of Lean's syntax.

    The replacement is stricter, not looser, in the one place the two differ on real input.
    ``\\b`` accepted ``foo`` against ``theorem foo'`` -- the wrong declaration, silently -- and
    the lookahead does not.
    """
    for rel, name in DENIED_BY_THE_OLD_GATE:
        text = (ROOT / "formal" / rel).read_text(encoding="utf-8")
        assert _declares(text, name), f"{name} is declared in {rel} and the gate denies it"
        assert not re.search(_SUPERSEDED.format(re.escape(name)), text, re.MULTILINE), (
            f"{name} in {rel}: the old regex was expected to fail here; if it now passes, "
            f"this record is stale and the widening needs re-justifying"
        )

    # A name genuinely absent from a file is still absent. `phi` is declared in FateShareLaw,
    # not in FateChernoff, and a gate that cannot tell those apart is not a join.
    chernoff = (ROOT / "formal" / "Problems/Juggler/FateChernoff.lean").read_text(encoding="utf-8")
    for absent in ("phi", "oddFailure", "oddFailuresX", "scaleRati", "notADeclarationAtAll"):
        assert not _declares(chernoff, absent), f"{absent} is not in FateChernoff.lean"

    # The prime is part of the name, and the pair it separates is real: FateTaoReduction
    # carries `treeLevel_logMass_le` at 2 <= n0 and `treeLevel_logMass_le'` at 3 <= n0. Each
    # must resolve to itself. `\b` could not do that -- it matched the unprimed name against
    # the primed line as happily as against its own, which is the mis-join this gate exists
    # to catch, arriving through the boundary rather than through the data.
    tao = (ROOT / "formal" / "Problems/Juggler/FateTaoReduction.lean").read_text(encoding="utf-8")
    assert _declares(tao, "treeLevel_logMass_le")
    assert _declares(tao, "treeLevel_logMass_le'")
    assert not _declares(tao, "treeLevel_logMass_l")

    # Both directions of the prime, on a sample small enough to read.
    sample = "noncomputable def budget : Nat := 0\ntheorem foo' : True := trivial\n"
    assert _declares(sample, "budget")
    assert _declares(sample, "foo'")
    assert not _declares(sample, "foo"), "`theorem foo'` does not declare `foo`"
    assert not _declares(sample, "budg")


def test_the_gate_resolves_every_declaration_the_index_holds():
    """The gate and the index must agree on what a declaration is.

    They did not: 214 declarations across 81 files were in the index and invisible to the
    gate. A row naming one of them could be correct in the data, correct in the Lean, and
    still rejected -- and the only way out was to drop the field, which is what happened.
    Parity is the property worth asserting, because it is the one that failed.
    """
    import collections
    import sys

    sys.path.insert(0, str(ROOT / "tools"))
    import formalpedia as fp

    indexed = collections.defaultdict(set)
    for d in fp.build()["declarations"]:
        indexed[d["file"]].add(d["name"])
    assert indexed, "the index is empty; this check would pass for nothing"

    missing = {}
    for rel, names in indexed.items():
        seen = set(DECL_LINE.findall((ROOT / rel).read_text(encoding="utf-8")))
        if names - seen:
            missing[rel] = sorted(names - seen)
    assert missing == {}, missing


def test_decl_when_present_names_a_declaration_in_the_rows_own_file():
    """The ``decl`` field is the join the ``lean`` file pointer cannot make.

    A row naming a declaration that is not in its file is worse than a row naming none:
    it reads as a resolved claim while pointing somewhere else.
    """
    for row in _entries():
        decls = _decls(row)
        if not decls:
            continue
        lean = str(row.get("lean") or "").strip()
        assert lean.endswith(".lean"), f"{row['id']}: decl needs a file, not {lean!r}"
        text = (ROOT / "formal" / lean).read_text(encoding="utf-8")
        assert len(decls) == len(set(decls)), f"{row['id']}: repeats a declaration"
        for decl in decls:
            assert _declares(text, decl), f"{row['id']}: {decl} not in {lean}"


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
    named = re.compile(r"Lean theorem\s+([A-Za-z][A-Za-z0-9_']*_[A-Za-z0-9_']+)")
    broken = []
    for row in _entries():
        lean = str(row.get("lean") or "").strip()
        if not lean.endswith(".lean"):
            continue
        path = ROOT / "formal" / lean
        if not path.is_file():
            continue
        present = set(DECL_LINE.findall(path.read_text(encoding="utf-8")))
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
                # The block ends at the next declaration, and a declaration wearing a
                # modifier is still one: without that, a body ran on past its own `end`
                # into the neighbour below and could be credited with the neighbour's
                # `native_decide`. 31 theorem blocks in `formal/` over-ran that way.
                block = re.search(
                    rf"(?:^|\n)\s*{DECL_ATTR}{DECL_MODIFIER}theorem\s+{re.escape(name)}{DECL_TAIL}"
                    rf"(.*?)(?=\n\s*(?:{DECL_ATTR}{DECL_MODIFIER}{DECL_KEYWORD}|/--)|\Z)",
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
