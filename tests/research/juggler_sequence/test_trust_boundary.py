"""The trust-boundary table must keep matching the repository.

A table that overstates what Lean checks is worse than none, because it converts an honest
"nothing here is machine-checked" into apparent corroboration.  So every identifier the table
prints has to be declared, the two rows that carry the paper have to keep saying what they say,
and the module list has to match what the citations actually resolve to.
"""

from __future__ import annotations

import importlib.util
import io
import re
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parents[3]
PAPER = ROOT / "docs" / "theory" / "juggler_parity_discrepancy_note.md"
MIRROR = ROOT / "juggler_review" / "juggler_parity_discrepancy_note.md"

_spec = importlib.util.spec_from_file_location("trust_boundary", ROOT / "tools" / "trust_boundary.py")
TB = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(TB)

IDENT = re.compile(r"`([a-z][A-Za-z0-9_']*)`")


def text() -> str:
    return io.open(PAPER, encoding="utf-8").read()


def table() -> str:
    src = text()
    start = src.index("The boundary between those three kinds of warrant")
    return src[start:src.index("### 1.2 Related work", start)]


def test_table_sits_in_the_verification_section() -> None:
    src = text()
    assert src.index("### 1.1 Verification") < src.index(
        "The boundary between those three kinds of warrant") < src.index("### 1.2 Related work")


def test_every_identifier_in_the_table_is_declared_in_lean() -> None:
    """The table may only name theorems the repository actually has."""
    decl = TB.declared()
    named = {m.group(1) for m in IDENT.finditer(table())} - {"ring"}
    assert named, "table names no identifiers"
    missing = sorted(n for n in named if n not in decl)
    assert not missing, missing


def test_every_identifier_in_the_table_is_reachable() -> None:
    """Reachable from Paper B's own barrel, which is what the table tells a reader to build."""
    decl = TB.declared()
    reach = TB.reachable_modules(TB.PAPER_B_ROOT)
    named = {m.group(1) for m in IDENT.finditer(table())} - {"ring"}
    unreachable = sorted(n for n in named if decl.get(n) not in reach)
    assert not unreachable, unreachable


def test_the_paper_cites_nothing_lean_does_not_declare() -> None:
    """`ring` is the one backticked name that is a tactic, not a theorem, and the table says so."""
    undeclared = [r["name"] for r in TB.audit() if not r["declared"]]
    assert undeclared == ["ring"], undeclared
    assert "not as the name of" in table()


def test_lemma_5_2_still_has_no_machine_check() -> None:
    """The row that carries the paper. If a Lean name ever appears in Lemma 5.2's span, the
    table's "none" becomes false and the claim has to be rewritten, not quietly outgrown."""
    src = text()
    start = src.index("**Lemma 5.2 (level-2 waves: the mixed-piece bound).**")
    end = src.index("**Lemma 5.2b (frozen-shape interpolant", start)
    names = {m.group(1) for m in IDENT.finditer(src[start:end])} - {"ring"}
    assert not names, names
    assert "| **Lem. 5.2(i), (ii), (iii)** | **this paper** | **none** |" in table()


def test_theorem_5_3_cites_only_step_5b_constants() -> None:
    """Two names, both constants inside Step 5b; no part of the assembly is checked."""
    src = text()
    start = src.index("**Theorem 5.3 (kernel cancellation).**")
    end = src.index("## 5. Depth-four equidistribution", start)
    names = {m.group(1) for m in IDENT.finditer(src[start:end])} - {"ring"}
    assert names == {"step5b_curvature_norm", "sublevel_raised_threshold"}, names
    assert "no part of the assembly" in table()


def test_module_list_matches_what_the_citations_resolve_to() -> None:
    """The table names the modules a reader would have to build; it must be the real set."""
    mods = sorted({r["module"] for r in TB.audit() if r["declared"]})
    assert mods == ["MasterIdentity", "MeanValues", "MonomialSplitting",
                    "PaperBAssembly", "ThresholdCertificate"], mods
    t = table()
    for m in mods:
        assert "`%s`" % m in t, m
    assert "five modules" in t


def test_paper_b_root_imports_exactly_its_own_modules() -> None:
    """The barrel must import the five modules the citations resolve to, and nothing else.

    An extra import would make the barrel claim more than the paper cites; a missing one would
    make the table's build instruction wrong.
    """
    src = io.open(TB.PAPER_B_ROOT, encoding="utf-8").read()
    imported = sorted(re.findall(r"^import Problems\.Juggler\.(\w+)", src, re.MULTILINE))
    cited = sorted({r["module"] for r in TB.audit() if r["declared"]})
    assert imported == cited, (imported, cited)


def test_the_two_paper_barrels_share_no_module() -> None:
    """Paper A's barrel and Paper B's are disjoint, which is what makes each one a boundary."""
    a = TB.reachable_modules(TB.PAPER_A_ROOT)
    b = TB.reachable_modules(TB.PAPER_B_ROOT)
    assert a and b and not (a & b), sorted(a & b)
    assert "shares no module with Paper A" in table()


def test_table_tells_the_reader_how_to_build_it() -> None:
    assert "lake build Problems.JugglerParityPaper" in table()
    assert (ROOT / "formal" / "Problems" / "JugglerParityPaper.lean").exists()


@pytest.mark.parametrize("external,source", [
    ("van der Corput", "Lem. 3.3"), ("Erdős–Turán", "Lem. 3.4"), ("Vaaler", "Lem. 3.5"),
])
def test_classical_inputs_are_the_ones_the_paper_cites(external: str, source: str) -> None:
    """Exactly four statements carry an external reference; three are the classical tools."""
    t = table()
    assert external in t, external
    assert source in t, source


def test_mirror_carries_the_table() -> None:
    assert text() == io.open(MIRROR, encoding="utf-8").read()
