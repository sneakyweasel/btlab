"""Hygiene guards for the Lean corpus.

Cleaning once decays. These are the three checks that hold the state a
cleanup reaches, in the same spirit as ``test_formalpedia.py``: they read
the corpus rather than the prose, and they fail when it drifts.

* **duplicate names** — the same fact under two names is the hazard the
  formalpedia guide warns about: the next reader cannot tell which one the
  manuscripts cite. Must be zero.
* **orphans** — declarations referenced nowhere and mentioned in no
  document are dead scaffolding, a terminal result nobody cites, or a third
  copy. A budget that must not grow, not a demand for zero.
* **build warnings** — noise hides signal. A budget that must not grow,
  behind ``--runslow`` because it needs a full ``lake build``.
"""

from __future__ import annotations

import collections
import json
import pathlib
import re
import subprocess

import pytest

REPO = pathlib.Path(__file__).resolve().parents[2]
INDEX = REPO / "data" / "research" / "formalpedia" / "index.json"
FORMAL = REPO / "formal"
DOCS = REPO / "docs"

#: Declarations referenced nowhere in the repository but their own definition.
#: Measured after the deduplication pass at 281; lower it when you clear some,
#: never raise it. Most are small intermediate lemmas nobody consumed, plus the
#: two companion-figure schema modules whose lemmas the TypeScript mirrors.
ORPHAN_BUDGET = 285

#: Directories whose contents are not ours, and the generated index, which
#: lists every declaration by name and would make each look referenced.
SCAN_SKIP = {".lake", "node_modules", ".git", "dist", "__pycache__"}
SCAN_SUFFIXES = {".lean", ".md", ".ts", ".tsx", ".py"}

#: Warnings from ``lake build Problems.Juggler Problems.JugglerPaper``.
#: Two remain, both cases where the linter is wrong:
#: ``FinanceTransfer:796`` — its suggested ``(tac1; tac2)`` does not compile,
#: because ``<;>`` runs ``omega`` per remaining goal and one branch has none;
#: ``DenjoyKoksmaOrbit:44`` — ``if_pos`` is half a compound ``simp only`` term.
WARNING_BUDGET = 2


def juggler_declarations() -> list[dict]:
    raw = json.loads(INDEX.read_text(encoding="utf-8"))
    decls = raw if isinstance(raw, list) else raw["declarations"]
    return [d for d in decls if d.get("module", "").startswith("Problems.Juggler")]


def test_no_duplicate_declaration_names() -> None:
    """One fact, one name. Two names is the hazard, whatever the modules."""
    counts = collections.Counter(d["name"] for d in juggler_declarations())
    duplicates = sorted(n for n, c in counts.items() if c > 1)
    assert duplicates == [], duplicates


def test_orphan_declarations_do_not_grow() -> None:
    """A new declaration should be used, or cited, or not written.

    The scan covers the whole repository, not just ``formal/`` and ``docs/``:
    the companion mirrors Lean schema declarations in TypeScript, so a
    Lean-only scan reports those as orphans when they are load-bearing for the
    figure. It skips the generated formalpedia index, which lists every
    declaration by name and would make each one look referenced.

    Structure fields are excluded: they are reached by dot notation, which a
    name scan cannot see.
    """
    decls = [d for d in juggler_declarations() if "." not in d["name"]]
    blob = []
    for path in REPO.rglob("*"):
        if not path.is_file() or path.suffix not in SCAN_SUFFIXES:
            continue
        if any(part in SCAN_SKIP for part in path.parts):
            continue
        blob.append(path.read_text(encoding="utf-8", errors="ignore"))
    whole = "\n".join(blob)
    orphans = [d["name"] for d in decls if whole.count(d["name"]) <= 1]
    assert len(orphans) <= ORPHAN_BUDGET, (
        f"{len(orphans)} orphans, budget {ORPHAN_BUDGET}; "
        f"examples: {sorted(orphans)[:5]}"
    )


@pytest.mark.slow
def test_lean_build_warning_budget() -> None:
    """Warnings must not accumulate: noise is what hides the real one.

    Only meaningful on a *cold* build. Lean reports a module's warnings when
    it compiles that module, so on a warm cache ``lake build`` rebuilds
    nothing, prints nothing, and a naive count would pass at zero while the
    warnings are still there. This skips in that case rather than reporting a
    pass it did not earn; run it after a change, or from a clean build in CI.
    """
    proc = subprocess.run(
        ["lake", "build", "Problems.Juggler", "Problems.JugglerPaper"],
        cwd=FORMAL,
        capture_output=True,
        text=True,
        timeout=7200,
    )
    output = proc.stdout + proc.stderr
    assert proc.returncode == 0, output[-3000:]
    rebuilt = len(re.findall(r"^\S*\s*\[\d+/\d+\] Building ", output, flags=re.M))
    if rebuilt == 0:
        pytest.skip("warm cache: nothing rebuilt, so no warnings were reported")
    warnings = re.findall(r"^warning: ", output, flags=re.M)
    assert len(warnings) <= WARNING_BUDGET, (
        f"{len(warnings)} warnings over {rebuilt} rebuilt modules, "
        f"budget {WARNING_BUDGET}"
    )
