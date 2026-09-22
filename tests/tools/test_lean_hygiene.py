"""Hygiene guards for the Lean corpus.

Cleaning once decays. These are the three checks that hold the state a
cleanup reaches, in the same spirit as ``test_formalpedia.py``: they read
the corpus rather than the prose, and they fail when it drifts.

* **duplicate identities** — two public source declarations must not share
  one fully qualified Lean name. Reusing a basename in separate namespaces
  is valid; this check does not attempt semantic theorem deduplication.
* **unresolved lexical candidates** — current public declarations without
  resolved source/document references need review. This is not proof of dead
  code: type-directed and ambiguous references can require compiled evidence.
  The historical review budget must not silently grow.
* **build warnings** — noise hides signal. A budget that must not grow,
  behind ``--runslow`` because it needs a full ``lake build``.
"""

from __future__ import annotations

import importlib.util
import pathlib
import shutil
import subprocess
from types import SimpleNamespace

import pytest

REPO = pathlib.Path(__file__).resolve().parents[2]
FORMAL = REPO / "formal"

_spec = importlib.util.spec_from_file_location("hygiene_trust_boundary", REPO / "tools/trust_boundary.py")
TB = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(TB)

_spec = importlib.util.spec_from_file_location("hygiene_helpers", REPO / "tools/lean_hygiene.py")
H = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(H)

#: Unresolved lexical candidates from the live qualified inventory.
#: A newly exposed backlog must be reviewed, not hidden by increasing this cap.
#:
#: 404 is a reviewed figure, not a raised ceiling. 285 was calibrated in
#: 44f3aa02 (2026-09-08) against a different metric: basenames read from the
#: generated formalpedia index, scored by ``corpus.count(name) <= 1``, a raw
#: substring count. 555775aa (2026-09-11) replaced that with namespace-resolved
#: qualified identifiers -- strictly stricter -- and carried 285 across
#: unchanged. The count at that commit was already 432. So 439-against-285
#: compared two measurements, and this gate has been red since the metric
#: changed rather than drifting for months: 432 (09-11), 437 (09-13), 439.
#:
#: Of those 439, 35 were real references the scanner could not see, and are
#: now credited instead of capped: 20 cited only by the ``decl`` field of the
#: theorem ledger, which ``render_theorem_ledger`` never emits into the
#: scanned markdown, and 15 reached by projection onto a declared value
#: (``witness.field``), where the resolver dropped the token rather than
#: crediting the head.
#:
#: The remaining 404 were reviewed against a compiled dependency graph taken
#: from the Lean environment, not from the sources. 8 are live and lexically
#: ambiguous -- ``J.cutForbiddens`` where two structures share a field name;
#: they are visible in ``ambiguous_tokens``. 396 have no consumer in the
#: compiled environment and no citation anywhere. They are kept, not deleted:
#: no module on disk is wholly orphaned (worst ratio 50%), so there is no dead
#: layer to retire, and 44f3aa02 already established that the two largest
#: clusters are the companion's display schema, not dead mathematics.
#: Lower this when a cluster is cleared; never raise it to go green.
#: docs/problems/juggler_orphan_declaration_gate.md
#:
#: 404 -> 402 on merge, by citation and not by deletion: nothing was removed
#: from the Lean corpus and candidates are unchanged at 4836. The two that
#: cleared are SeamData.cycleParent and JoinFigure.rigidity, named as
#: counterexamples in the gate dossier, the journal entry and a ledger row --
#: documenting an orphan cites it, so writing the ceremony prose for one
#: removes it from the list. Any budget measured before that prose exists is
#: systematically too loose.
#:
#: A first attempt at this merge read 399 and was wrong. The scan walked
#: .claude/worktrees, where concurrent agent sessions keep full repository
#: copies, and a copy's declaration line counts as a reference to the
#: original -- so the figure fell by however many worktrees happened to be on
#: disk. ".claude" is now in SCAN_SKIP; see the note there.
#:
#: 18 September 2026: held as a share, not a count. The absolute form did not
#: survive the corpus it guards. Paper B's formalisation added 257 declarations
#: to the 4836 above; 28 of them were uncited, the count reached 433, and the
#: gate read that as a regression. It was the opposite. Citing those 28 left
#: 405 against 5093 candidates -- 7.95%, where the calibrated 402 of 4836 had
#: been 8.31%. The corpus got cleaner and an absolute cap called it a failure,
#: because a count cannot tell "more unreviewed backlog" from "more
#: mathematics" and only the first is what this gate is for.
#:
#: Compared by cross-multiplication of integers, so the verdict never depends
#: on a float. It ratchets: lower it when a cluster clears, never raise it to go
#: green. Growing the denominator with *cited* declarations is the only honest
#: way the absolute allowance rises, and that is the behaviour that was wanted.
#:
#: The calibration history above, and the compiled-dependency review that
#: produced 402, are unchanged and still apply. Only the shape of the
#: comparison changed.
#:
#: 18 September 2026, raised to 1000/10000 by the repository owner, who asked
#: for it explicitly after the gate interrupted a third consecutive branch. This
#: is a deliberate reset of the level, not a measurement: at the time of the
#: change the share stood at 413 of 5168, or 7.99%, against an allowance of
#: 7.96% -- failing by two declarations, and already failing before the branch
#: that surfaced it (413 of 5138, 8.04%). The backlog it refuses is real and is
#: listed by namespace in the orphan report; `Problems.Juggler` alone carries
#: 303 of it. Nothing was cited to reach the new level and nothing should be
#: read as cleared by it.
#:
#: The ratchet above still binds every agent: do not raise this again to go
#: green. Only the owner reset it.
#:
#: Citation then followed, and the paragraph above is left standing because it
#: was true of the reset: nothing was cited *to reach* the new level. Six whole
#: clusters were cited afterwards, 126 declarations, none deleted and no Lean
#: source touched -- IdealCycleMin 48, IdealLollipop 43, RankedReturn 11,
#: DepthFourFive 10, RealizedGridBounds 7, FullUpperCellChargeBounds 7 --
#: taking the share to 287 of 5168, or 5.55%. The two largest had sat at the
#: top of the list since 09-08 with no dossier and no ledger row; they are
#: documented at docs/architecture/juggler_ideal_cycle_model.md, the rest in
#: the Lean interfaces note. The headroom that remains is the owner's
#: deliberate setting, not slack nobody noticed.
#:
#: One measured correction to the partition above, worth not re-deriving. The
#: "live but reached only by an ambiguous token" part is recorded there as 8
#: laboratory-wide. Among those 126 alone it was 16: the seven display
#: projections shared by SureLetterSite and JoinFigure, three on RankedReturn,
#: and six on the charge and grid records. 15 more remain among the 287. Such a
#: declaration cannot be cited by its basename -- the token lands in
#: ``ambiguous_tokens`` and credits nothing, by design, because two
#: declarations really do answer to that name. Spell enough of the namespace:
#: ``RealizedGridBounds.gap_pos``, not ``gap_pos``.
ORPHAN_RATIO_NUM = 1000
ORPHAN_RATIO_DEN = 10000

#: Warnings from ``lake build Problems.Juggler Problems.JugglerPaper``.
#: Two remain, and the reason recorded here until 14 September 2026 was
#: wrong.  It said both were cases where the linter is mistaken, and both
#: were in fact fixable -- the fixes compile, and were verified by deleting
#: the module's oleans and building it from source:
#:
#:   FinanceTransfer:796   cases c <;> simp [ih]; omega
#:   DenjoyKoksmaOrbit:44  simp only at h
#:
#: The earlier note described a different edit than the one that works.  For
#: FinanceTransfer it read the suggestion as ``cases c <;> (simp [ih]; omega)``,
#: which does run ``omega`` once per branch and does fail where a branch has
#: no goal left; ``;`` binds looser than ``<;>``, so ``cases c <;> simp [ih];
#: omega`` is ``(cases c <;> simp [ih]); omega`` and ``omega`` sees one goal.
#: For DenjoyKoksmaOrbit it removed ``if_pos`` alone and left ``rfl``; the
#: linter's column covers the whole compound term ``if_pos rfl``.
#:
#: They stay for an unrelated reason, and it is not a Lean one.  Both files
#: are pinned by ``docs/theory/paper_a_release.json``, which records a
#: SHA-256 of every Paper A input as a provenance claim about the built PDF.
#: Editing either invalidates that manifest, and restoring it means a full
#: pandoc + xelatex rebuild that rewrites the PDF, the TeX, the Zenodo
#: metadata and four export copies -- a published binary changing in git for
#: two tactic cleanups that alter no statement.  That trade was put to the
#: maintainer on 14 September 2026 and declined.
#:
#: So this budget is now a record of a coupling, not of a linter defect:
#: Paper A's byte-level input pin makes its Lean unrefactorable without a
#: republish.  Lower it to 0 in the same change that next rebuilds Paper A.
WARNING_BUDGET = 2


def juggler_declarations() -> list[dict]:
    return [row for rows in TB.declaration_index().values() for row in rows
            if H.juggler_module(str(row["module_name"]))]


def duplicate_public_declaration_locations() -> dict[str, list[str]]:
    """Read current sources; a generated basename index cannot identify Lean constants."""
    duplicates = {}
    for name, rows in TB.declaration_index().items():
        locations = [f"{row['module_name']}:{row['line']}" for row in rows
                     if row["module_name"] == "Problems.Juggler"
                     or str(row["module_name"]).startswith("Problems.Juggler.")]
        if len(locations) > 1:
            duplicates[name] = sorted(locations)
    return duplicates


def test_no_duplicate_declaration_names() -> None:
    """One public qualified name has one source declaration, regardless of module."""
    duplicates = duplicate_public_declaration_locations()
    assert duplicates == {}, duplicates


def test_duplicate_audit_distinguishes_namespaces_and_detects_new_sources(tmp_path, monkeypatch) -> None:
    """Same basenames are valid, but a newly added duplicate cannot hide behind a stale index."""
    folder = tmp_path / "formal" / "Problems" / "Juggler"
    folder.mkdir(parents=True)
    first = """namespace Problems.Juggler
namespace First
theorem shared : True := by trivial
private theorem internal : True := by trivial
end First
end Problems.Juggler
"""
    (folder / "First.lean").write_text(first, encoding="utf-8")
    (folder / "Second.lean").write_text(first.replace("First", "Second"), encoding="utf-8")
    monkeypatch.setattr(TB, "ROOT", tmp_path)
    assert duplicate_public_declaration_locations() == {}
    (folder / "Copy.lean").write_text(first, encoding="utf-8")
    assert duplicate_public_declaration_locations() == {
        "Problems.Juggler.First.shared": ["Problems.Juggler.Copy:3", "Problems.Juggler.First:3"]
    }


def test_orphan_declarations_do_not_grow() -> None:
    """Keep unresolved lexical reference candidates visible for review.

    The current qualified inventory is checked against identifier tokens in
    Lean, companion sources, tests and documentation. Generated inventories
    and their review lists cannot make declarations appear referenced.
    Structure fields are outside the explicit-source candidate inventory.

    This conservative source check is not a dead-code proof: unresolved
    namespace, open-namespace and type-directed references may need an
    independent compiled dependency review.

    The bound is a share of the live inventory rather than a count, so that
    formalising more mathematics does not fail the gate on its own. What must
    not grow is the *proportion* of the corpus nobody has written down.
    """
    report = H.orphan_report(REPO, TB)
    orphans = [row["qualified_name"] for row in report["orphans"]]
    candidates = report["candidate_count"]
    assert candidates > 0, "no live qualified candidates: the inventory failed to load"
    allowed = ORPHAN_RATIO_NUM * candidates // ORPHAN_RATIO_DEN
    assert len(orphans) * ORPHAN_RATIO_DEN <= ORPHAN_RATIO_NUM * candidates, (
        f"{len(orphans)} unresolved lexical candidates of {candidates} live public ones, "
        f"a share of {len(orphans) / candidates:.4f}; the reviewed share is "
        f"{ORPHAN_RATIO_NUM / ORPHAN_RATIO_DEN:.4f}, which allows {allowed} here. "
        f"Examples: {orphans[:10]}. This is not established dead code; ambiguous and "
        "type-directed references require review. Cite them or clear a cluster; do not "
        "raise the share to go green."
    )


@pytest.mark.slow
def test_lean_build_warning_budget() -> None:
    """Warnings must not accumulate: noise is what hides the real one.

    Lake replays cached diagnostics. Built/Replayed records and located
    Juggler warnings are evidence even without a recompile. Truly silent
    scoped output is skipped, and excess warnings are checked before that
    decision. Dependency diagnostics do not consume the Juggler budget.

    Skips without a toolchain. This is the only Lean-calling test in the suite
    that lacked that guard, and it is why CI's python job failed the moment the
    ruff gate stopped failing first: no lake on that runner, FileNotFoundError,
    the whole Pytest step down in seconds. The guard leaves a hole -- CI's
    python job has no lake and the lean job does not run pytest, so nothing
    enforces this budget in CI. It is enforced locally and by whoever runs
    --runslow with a toolchain. Closing that hole means giving the lean job a
    Python and pointing it here.
    """
    if shutil.which("lake") is None:
        pytest.skip("no lake on PATH; the warning budget needs a toolchain")
    proc = subprocess.run(
        ["lake", "build", "Problems.Juggler", "Problems.JugglerPaper"],
        cwd=FORMAL,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        text=True,
        timeout=7200,
    )
    output = proc.stdout
    assert proc.returncode == 0, output[-3000:]
    report = H.parse_build_output(output)
    assert not report["unlocated"], f"Unscoped warning records require review: {report['unlocated']}"
    assert len(report["warnings"]) <= WARNING_BUDGET, (
        f"{len(report['warnings'])} Juggler warnings; budget {WARNING_BUDGET}; "
        f"records: {report['warnings']}"
    )
    if not report["has_scoped_evidence"]:
        pytest.skip("no scoped Built/Replayed records or diagnostics; warning state not observed")


@pytest.mark.parametrize("status", ["Built", "Replayed"])
def test_warning_gate_counts_actual_and_cached_diagnostics(status, monkeypatch) -> None:
    output = (f"⚠ [42/99] {status} Problems.Juggler.Example\n"
              "warning: Problems/Juggler/Example.lean:7:2: unused tactic\n")
    monkeypatch.setattr(shutil, "which", lambda _name: "/usr/bin/lake")
    monkeypatch.setattr(subprocess, "run", lambda *a, **kw: SimpleNamespace(returncode=0, stdout=output))
    monkeypatch.setitem(globals(), "WARNING_BUDGET", 0)
    with pytest.raises(AssertionError, match="1 Juggler warnings"):
        test_lean_build_warning_budget()


def test_warning_gate_does_not_skip_unadorned_scoped_warnings(monkeypatch) -> None:
    output = "warning: Problems/Juggler/Example.lean:7:2: unused tactic\n"
    monkeypatch.setattr(shutil, "which", lambda _name: "/usr/bin/lake")
    monkeypatch.setattr(subprocess, "run", lambda *a, **kw: SimpleNamespace(returncode=0, stdout=output))
    monkeypatch.setitem(globals(), "WARNING_BUDGET", 0)
    with pytest.raises(AssertionError, match="1 Juggler warnings"):
        test_lean_build_warning_budget()


def test_warning_parser_scopes_locations_and_ignores_hint_text() -> None:
    output = """\x1b[33m⚠ [1/5] Replayed Problems.Juggler.A\x1b[0m
warning: Mathlib/Other.lean:1:2: dependency warning
Hint: the word warning: here is continuation text
warning: C:\\repo\\formal\\Problems\\Juggler\\A.lean:2:3: local warning
Problems/Juggler/A.lean:4:5: warning: alternate format
warning: .lake/packages/vendor/Problems/Juggler/External.lean:1:1: external
✔ [2/5] Built Problems.JugglerPaper (1s)
"""
    report = H.parse_build_output(output)
    assert len(report["warnings"]) == 2
    assert [w["line"] for w in report["warnings"]] == [2, 4]
    assert [m["status"] for m in report["modules"]] == ["Replayed", "Built"]
    assert report["has_scoped_evidence"]


def test_warning_gate_skips_only_unobserved_scope(monkeypatch) -> None:
    output = "✔ [1/1] Built Mathlib.Other\nBuild completed successfully (1 jobs).\n"
    monkeypatch.setattr(shutil, "which", lambda _name: "/usr/bin/lake")
    monkeypatch.setattr(subprocess, "run", lambda *a, **kw: SimpleNamespace(returncode=0, stdout=output))
    with pytest.raises(pytest.skip.Exception, match="warning state not observed"):
        test_lean_build_warning_budget()



def test_warning_gate_reports_missing_scope_instead_of_claiming_zero(monkeypatch) -> None:
    output = "warning: diagnostic without a source or module\nBuild completed successfully (0 jobs).\n"
    monkeypatch.setattr(shutil, "which", lambda _name: "/usr/bin/lake")
    monkeypatch.setattr(subprocess, "run", lambda *a, **kw: SimpleNamespace(returncode=0, stdout=output))
    with pytest.raises(AssertionError, match="Unscoped warning"):
        test_lean_build_warning_budget()


def test_warning_text_cannot_forge_a_success_record() -> None:
    report = H.parse_build_output(
        "warning: Problems/Juggler/A.lean:7:2: do not mistake [1/2] Built Problems.Juggler.A for a record\n")
    assert len(report["warnings"]) == 1
    assert report["modules"] == []


def _orphan_fixture(tmp_path, monkeypatch, sources, documents=None):
    folder = tmp_path / "formal/Problems/Juggler"
    folder.mkdir(parents=True)
    for name, source in sources.items():
        (folder / name).write_text(source, encoding="utf-8")
    for name, source in (documents or {}).items():
        path = tmp_path / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(source, encoding="utf-8")
    monkeypatch.setattr(TB, "ROOT", tmp_path)
    return H.orphan_report(tmp_path, TB)


def test_orphan_inventory_is_live_and_generated_lists_are_not_references(tmp_path, monkeypatch) -> None:
    report = _orphan_fixture(tmp_path, monkeypatch,
        {"Fresh.lean": "namespace Problems.Juggler\ntheorem fresh : True := by trivial\nend Problems.Juggler\n"},
        {"data/research/formalpedia/index.json": "[]",
         "docs/research/formalpedia_decl_review.md": "Problems.Juggler.fresh"})
    assert report["candidate_count"] == 1
    assert [d["qualified_name"] for d in report["orphans"]] == ["Problems.Juggler.fresh"]


@pytest.mark.parametrize("folder", [".build", "tmp", ".venv-seed", "venv", ".tox"])
def test_temporary_and_dependency_copies_are_not_lean_consumers(tmp_path, monkeypatch, folder) -> None:
    report = _orphan_fixture(tmp_path, monkeypatch,
        {"Fresh.lean": "namespace Problems.Juggler\ntheorem fresh : True := by trivial\nend Problems.Juggler\n"},
        {f"{folder}/copy.md": "Problems.Juggler.fresh"})
    assert [d["qualified_name"] for d in report["orphans"]] == ["Problems.Juggler.fresh"]


def test_orphan_tokens_resolve_namespaces_without_prefix_or_self_credit(tmp_path, monkeypatch) -> None:
    source = """namespace Problems.Juggler
namespace A
theorem same : True := by trivial
private theorem consume : True := same
theorem loop : True := by exact loop
theorem prefix : True := by trivial
end A
namespace B
theorem same : True := by trivial
end B
end Problems.Juggler
"""
    report = _orphan_fixture(tmp_path, monkeypatch, {"Names.lean": source},
                             {"docs/use.md": "`prefix_extension` and `same` are not resolved uses."})
    assert [d["qualified_name"] for d in report["orphans"]] == [
        "Problems.Juggler.A.loop", "Problems.Juggler.A.prefix", "Problems.Juggler.B.same"]
    assert "same" in report["ambiguous_tokens"]


def test_orphan_exact_qualified_and_method_tokens_are_credited(tmp_path, monkeypatch) -> None:
    source = """namespace Problems.Juggler
namespace A
theorem exact_name : True := by trivial
theorem method_name : True := by trivial
end A
end Problems.Juggler
"""
    report = _orphan_fixture(tmp_path, monkeypatch, {"Used.lean": source},
                             {"docs/use.md": "`Problems.Juggler.A.exact_name` and `h.method_name`."})
    assert report["orphans"] == []


def test_orphan_lean_comments_and_other_namespace_are_not_consumers(tmp_path, monkeypatch) -> None:
    source = """namespace Problems.Juggler
namespace A
theorem unused : True := by trivial
end A
namespace B
theorem anchor : True := by trivial
end B
/- A.unused is only a comment, not a consuming proof. -/
end Problems.Juggler
"""
    report = _orphan_fixture(tmp_path, monkeypatch, {"Comments.lean": source},
                             {"docs/use.md": "Problems.Juggler.B.unused and Problems.Juggler.B.anchor"})
    assert [d["qualified_name"] for d in report["orphans"]] == ["Problems.Juggler.A.unused"]


def test_orphan_private_header_and_recursion_do_not_credit_public_alias(tmp_path, monkeypatch) -> None:
    source = """namespace Problems.Juggler
namespace A
theorem same : True := by trivial
end A
namespace B
private theorem same : True := by exact same
end B
end Problems.Juggler
"""
    report = _orphan_fixture(tmp_path, monkeypatch, {"PrivateNames.lean": source})
    assert [d["qualified_name"] for d in report["orphans"]] == ["Problems.Juggler.A.same"]
