"""Paper A's citations must resolve, and its trust claim must stay true.

Paper B has had a trust boundary and an axiom check since the referee asked for one. Paper A
had neither: its own audit probe checks convergents, the fan law, Rhin bounds and window
margins, all numerical, and never asks whether a Lean name it cites exists or is reachable
from the barrel the paper tells a reader to build. A module cited by the prose but absent
from that barrel makes the paper's build instruction wrong while every test stays green, and
that is exactly what happened once already.

These are the same three questions the Paper B suite asks, asked of Paper A.
"""

from __future__ import annotations

import importlib.util
import io
import re
import shutil
import subprocess
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parents[3]
PAPER = ROOT / "docs" / "theory" / "juggler_finite_dynamics_note.md"
MIRROR = ROOT / "juggler_review" / "juggler_finite_dynamics_note.md"
FORMAL = ROOT / "formal"
CHECK = FORMAL / "AxiomCheckPaperA.lean"
EXPECTED = FORMAL / "AxiomCheckPaperA.expected"

_spec = importlib.util.spec_from_file_location(
    "trust_boundary", ROOT / "tools" / "trust_boundary.py")
TB = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(TB)

HEX64 = re.compile(r"^[0-9a-f]{64}$")

# Backticked lowercase names in Paper A that are deliberately not Lean declarations:
# two tactics, two Python probe modules, and two JSON field names.
#: Backticked in the paper but not declarations of the Juggler layer: tactic names, probe
#: ids, and -- since 14 September 2026 -- `propext`, which is a Lean core axiom the trust
#: paragraph now names directly, and `window_digit_scan`, the retired native scan that
#: paragraph records historically. A retired name stays here only while the paper still
#: tells its story; delete it when the prose drops it.
NOT_DECLARATIONS = {
    "native_decide", "norm_num",
    "cycle_walk_ostrowski", "cycle_walk_window",
    "killed_by_budget", "lengths",
    "propext", "window_digit_scan",
}


def rows() -> list[dict[str, object]]:
    return TB.audit(TB.PAPER_A, TB.PAPER_A_ROOT)


def test_every_cited_declaration_is_reachable_from_paper_a_barrel() -> None:
    """The paper tells a reader to build one barrel; every name it cites must be in it."""
    unreachable = sorted(
        str(r["name"]) for r in rows() if r["declared"] and not r["reachable"])
    assert not unreachable, unreachable


def test_every_cited_declaration_has_an_unambiguous_identity() -> None:
    ambiguous = {str(r["name"]): r["candidates"] for r in rows() if r["ambiguous"]}
    assert not ambiguous, ambiguous


def test_the_undeclared_citations_are_all_carve_outs() -> None:
    """Anything backticked and not declared must be a checksum, a probe, or a tactic."""
    undeclared = sorted(str(r["name"]) for r in rows() if not r["declared"])
    stray = [n for n in undeclared if not HEX64.match(n) and n not in NOT_DECLARATIONS]
    assert not stray, stray


def test_the_paper_names_the_barrel_it_tells_you_to_build() -> None:
    text = io.open(PAPER, encoding="utf-8").read()
    assert "lake build Problems.JugglerPaper" in text
    assert TB.PAPER_A_ROOT.is_file()


def test_the_axiom_check_covers_exactly_the_cited_declarations() -> None:
    """The check file must ask about every declared citation and nothing else."""
    asked = set(TB.dependency_requests(CHECK.read_text(encoding="utf-8")))
    cited = {str(r["qualified_name"]) for r in rows() if r["declared"]}
    assert asked == cited


#: Paper A's Lean layer had exactly one proof off the kernel until 14 September 2026:
#: `window_digit_scan`, a `native_decide` pass over 251486 window lengths that sharpened
#: the Ostrowski digit cap from the structural 47 to 37. Nothing consumed the 37, so it
#: was retired and `window_digit_cap` reproved from `greedyDigitSum_le`. There is now no
#: authorized native consumer, and this dict must stay empty: an entry here is a
#: compiler-trust assumption in a deposited paper's surface, and it should be argued for
#: in the paper before it is recorded here.
NATIVE_EXCEPTIONS: dict[str, set[str]] = {}


def test_nothing_leaves_the_kernel() -> None:
    """Every dependency, with no authorized native consumer to except."""
    cited = {str(row["qualified_name"]) for row in rows() if row["declared"]}
    TB.validate_dependency_records(EXPECTED.read_text(encoding="utf-8"), cited, NATIVE_EXCEPTIONS)
    assert "native_decide" not in EXPECTED.read_text(encoding="utf-8")
    text = io.open(PAPER, encoding="utf-8").read()
    assert "Juggler layer without exception" in text, (
        "the layer is exception-free; the paper must say so. It may still name "
        "`window_digit_scan` historically -- it does -- so this checks the claim "
        "rather than the absence of the name."
    )


def test_the_axiom_check_actually_runs() -> None:
    """Slow but the point: the recorded output is regenerated, not trusted."""
    if shutil.which("lake") is None:
        pytest.skip("no lake on PATH")
    out = subprocess.run(["lake", "env", "lean", "AxiomCheckPaperA.lean"],
                         cwd=FORMAL, capture_output=True, text=True,
                         encoding="utf-8", errors="replace", timeout=900)
    assert out.returncode == 0, (out.stdout + out.stderr)[-8000:]
    assert not out.stderr.strip(), out.stderr
    TB.validate_dependency_records(out.stdout, set(TB.dependency_requests(CHECK.read_text(encoding="utf-8"))),
                                   NATIVE_EXCEPTIONS)
    assert out.stdout.strip() == io.open(EXPECTED, encoding="utf-8").read().strip()


def test_mirror_carries_the_paper() -> None:
    assert io.open(PAPER, encoding="utf-8").read() == io.open(MIRROR, encoding="utf-8").read()



#: The live policy is empty, so the control harness below uses a synthetic exception
#: instead. Otherwise every test of the accept path would loop over nothing and pass
#: vacuously, and the validator's handling of an authorized native consumer would stop
#: being checked at exactly the moment the repository stopped having one.
NATIVE_DEPENDENCY = "Problems.Example.scan._native.native_decide.ax_1_1"
CONTROL_EXCEPTIONS = {"Problems.Example.native": {NATIVE_DEPENDENCY}}


def dependency_control(extra: str = "") -> tuple[str, set[str]]:
    ordinary = "Problems.Example.clean"
    lines = [f"'{ordinary}' depends on axioms: [propext{extra}]\n"]
    lines.extend(f"'{name}' depends on axioms: [propext,\n {NATIVE_DEPENDENCY}]\n"
                 for name in CONTROL_EXCEPTIONS)
    return "".join(lines), {ordinary, *CONTROL_EXCEPTIONS}


def test_complete_dependency_policy_accepts_exact_named_native_exceptions():
    raw, expected = dependency_control()
    records = TB.validate_dependency_records(raw, expected, CONTROL_EXCEPTIONS)
    assert records["Problems.Example.clean"] == frozenset({"propext"})
    assert CONTROL_EXCEPTIONS, "the accept path must have something to accept"
    for name in CONTROL_EXCEPTIONS:
        assert records[name] - TB.STANDARD_DEPENDENCIES == {NATIVE_DEPENDENCY}


@pytest.mark.parametrize("extra", ["Unexpected.foundation", "Lean.ofReduceBool", "sorryAx", NATIVE_DEPENDENCY])
def test_any_nonstandard_dependency_on_an_ordinary_consumer_is_rejected(extra):
    raw, expected = dependency_control(", " + extra)
    with pytest.raises(ValueError, match="Unexpected dependencies"):
        TB.validate_dependency_records(raw, expected, CONTROL_EXCEPTIONS)


def test_named_native_consumer_cannot_hide_an_additional_dependency():
    raw, expected = dependency_control()
    raw = raw.replace(NATIVE_DEPENDENCY + "]", NATIVE_DEPENDENCY + ", Hidden.foundation]", 1)
    with pytest.raises(ValueError, match="Unexpected dependencies"):
        TB.validate_dependency_records(raw, expected, CONTROL_EXCEPTIONS)
