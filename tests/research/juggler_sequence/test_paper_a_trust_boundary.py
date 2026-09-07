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
    asked = set(re.findall(r"^#print axioms\s+([A-Za-z0-9_.']+)$",
                           io.open(CHECK, encoding="utf-8").read(), re.M))
    cited = {str(r["name"]) for r in rows() if r["declared"]}
    assert {a.rsplit(".", 1)[-1] for a in asked} == cited


def records(raw: str) -> list[str]:
    """`#print axioms` wraps long lines; a record starts at a quote."""
    out: list[str] = []
    cur = ""
    for line in raw.splitlines():
        if line.startswith("'"):
            if cur:
                out.append(cur)
            cur = line
        else:
            cur += " " + line.strip()
    if cur:
        out.append(cur)
    return out


def test_only_the_declared_exception_leaves_the_kernel() -> None:
    """Section 1.2 claims one `native_decide`. Its consumers inherit the axiom and the
    paper says so, but nothing else may carry one."""
    recs = records(io.open(EXPECTED, encoding="utf-8").read())
    assert len(recs) == len([r for r in rows() if r["declared"]])
    off = sorted(r.split("'")[1] for r in recs if "native_decide" in r)
    assert off == ["Problems.Juggler.window_digit_cap",
                   "Problems.Juggler.window_digit_scan"], off
    text = io.open(PAPER, encoding="utf-8").read()
    assert "`window_digit_scan`" in text


def test_the_axiom_check_actually_runs() -> None:
    """Slow but the point: the recorded output is regenerated, not trusted."""
    if shutil.which("lake") is None:
        pytest.skip("no lake on PATH")
    out = subprocess.run(["lake", "env", "lean", "AxiomCheckPaperA.lean"],
                         cwd=FORMAL, capture_output=True, text=True, timeout=900)
    assert out.returncode == 0, out.stderr[-2000:]
    assert out.stdout.strip() == io.open(EXPECTED, encoding="utf-8").read().strip()


def test_mirror_carries_the_paper() -> None:
    assert io.open(PAPER, encoding="utf-8").read() == io.open(MIRROR, encoding="utf-8").read()
