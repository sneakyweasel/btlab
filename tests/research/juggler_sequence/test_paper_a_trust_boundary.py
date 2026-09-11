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
NOT_DECLARATIONS = {
    "native_decide", "norm_num",
    "cycle_walk_ostrowski", "cycle_walk_window",
    "killed_by_budget", "lengths",
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


NATIVE_DEPENDENCY = "Problems.Juggler.window_digit_scan._native.native_decide.ax_1_1"
NATIVE_EXCEPTIONS = {
    "Problems.Juggler.window_digit_cap": {NATIVE_DEPENDENCY},
    "Problems.Juggler.window_digit_scan": {NATIVE_DEPENDENCY},
}


def test_only_the_declared_exception_leaves_the_kernel() -> None:
    """Check every dependency, including any extra attached to an authorized native consumer."""
    cited = {str(row["qualified_name"]) for row in rows() if row["declared"]}
    TB.validate_dependency_records(EXPECTED.read_text(encoding="utf-8"), cited, NATIVE_EXCEPTIONS)
    text = io.open(PAPER, encoding="utf-8").read()
    assert "`window_digit_scan`" in text


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



def dependency_control(extra: str = "") -> tuple[str, set[str]]:
    ordinary = "Problems.Example.clean"
    lines = [f"'{ordinary}' depends on axioms: [propext{extra}]\n"]
    lines.extend(f"'{name}' depends on axioms: [propext,\n {NATIVE_DEPENDENCY}]\n"
                 for name in NATIVE_EXCEPTIONS)
    return "".join(lines), {ordinary, *NATIVE_EXCEPTIONS}


def test_complete_dependency_policy_accepts_exact_named_native_exceptions():
    raw, expected = dependency_control()
    records = TB.validate_dependency_records(raw, expected, NATIVE_EXCEPTIONS)
    assert records["Problems.Example.clean"] == frozenset({"propext"})
    for name in NATIVE_EXCEPTIONS:
        assert records[name] - TB.STANDARD_DEPENDENCIES == {NATIVE_DEPENDENCY}


@pytest.mark.parametrize("extra", ["Unexpected.foundation", "Lean.ofReduceBool", "sorryAx", NATIVE_DEPENDENCY])
def test_any_nonstandard_dependency_on_an_ordinary_consumer_is_rejected(extra):
    raw, expected = dependency_control(", " + extra)
    with pytest.raises(ValueError, match="Unexpected dependencies"):
        TB.validate_dependency_records(raw, expected, NATIVE_EXCEPTIONS)


def test_named_native_consumer_cannot_hide_an_additional_dependency():
    raw, expected = dependency_control()
    raw = raw.replace(NATIVE_DEPENDENCY + "]", NATIVE_DEPENDENCY + ", Hidden.foundation]", 1)
    with pytest.raises(ValueError, match="Unexpected dependencies"):
        TB.validate_dependency_records(raw, expected, NATIVE_EXCEPTIONS)


def test_native_exception_is_required_and_cannot_move_to_another_consumer():
    raw, expected = dependency_control()
    with pytest.raises(ValueError, match="Unexpected dependencies"):
        TB.validate_dependency_records(raw.replace(",\n " + NATIVE_DEPENDENCY, "", 1),
                                       expected, NATIVE_EXCEPTIONS)
    with pytest.raises(ValueError, match="Unexpected dependencies"):
        TB.validate_dependency_records(raw, expected,
                                       {"Problems.Example.clean": {NATIVE_DEPENDENCY}})


@pytest.mark.parametrize("change", ["missing", "extra", "duplicate", "warning", "garbage", "malformed"])
def test_incomplete_or_malformed_dependency_output_is_rejected(change):
    raw, expected = dependency_control()
    if change == "missing":
        raw = raw.split("\n", 1)[1]
    elif change == "extra":
        raw += "'Extra.result' does not depend on any axioms\n"
    elif change == "duplicate":
        raw += raw.split("\n", 1)[0] + "\n"
    elif change == "warning":
        raw = "warning: unexpected diagnostic\n" + raw
    elif change == "garbage":
        raw += "trailing output"
    else:
        raw = raw.replace("[propext]", "[propext,]")
    with pytest.raises(ValueError):
        TB.validate_dependency_records(raw, expected, NATIVE_EXCEPTIONS)


def test_empty_and_wrapped_dependency_sets_with_full_identifiers():
    raw = ("'Problems.Example.getLast?_append_cons' depends on axioms: [propext,\n"
           " Classical.choice, Quot.sound]\n"
           "'Problems.Example.A₁' does not depend on any axioms\n"
           "'Problems.Example.primed\'' depends on axioms: []\n")
    expected = {"Problems.Example.getLast?_append_cons", "Problems.Example.A₁", "Problems.Example.primed'"}
    records = TB.validate_dependency_records(raw, expected)
    assert not records["Problems.Example.A₁"]
    assert records["Problems.Example.getLast?_append_cons"] == TB.STANDARD_DEPENDENCIES


def test_dependency_requests_keep_question_marks_and_unicode_and_reject_duplicates():
    source = ("import Problems.Example\n-- #print axioms Wrong.result\n"
              "#print axioms Problems.Example.getLast?_append_cons\n"
              "#print axioms Problems.Example.A₁\n")
    assert TB.dependency_requests(source) == ["Problems.Example.getLast?_append_cons", "Problems.Example.A₁"]
    with pytest.raises(ValueError, match="Repeated"):
        TB.dependency_requests(source + "#print axioms Problems.Example.A₁\n")
