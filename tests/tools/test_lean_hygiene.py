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

#: Historical cap, unchanged by the switch to a live qualified inventory.
#: A newly exposed backlog must be reviewed, not hidden by increasing this cap.
ORPHAN_BUDGET = 285

#: Warnings from ``lake build Problems.Juggler Problems.JugglerPaper``.
#: Two remain, both cases where the linter is wrong:
#: ``FinanceTransfer:796`` — its suggested ``(tac1; tac2)`` does not compile,
#: because ``<;>`` runs ``omega`` per remaining goal and one branch has none;
#: ``DenjoyKoksmaOrbit:44`` — ``if_pos`` is half a compound ``simp only`` term.
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
    independent compiled dependency review. The historical cap is unchanged.
    """
    report = H.orphan_report(REPO, TB)
    orphans = [row["qualified_name"] for row in report["orphans"]]
    assert len(orphans) <= ORPHAN_BUDGET, (
        f"{len(orphans)} unresolved lexical candidates, review budget {ORPHAN_BUDGET}; "
        f"live public candidates {report['candidate_count']}; examples: {orphans[:10]}. "
        "This is not established dead code; ambiguous and type-directed references require review."
    )


@pytest.mark.slow
def test_lean_build_warning_budget() -> None:
    """Warnings must not accumulate: noise is what hides the real one.

    Lake replays cached diagnostics. Built/Replayed records and located
    Juggler warnings are evidence even without a recompile. Truly silent
    scoped output is skipped, and excess warnings are checked before that
    decision. Dependency diagnostics do not consume the Juggler budget.
    """
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
    monkeypatch.setattr(subprocess, "run", lambda *a, **kw: SimpleNamespace(returncode=0, stdout=output))
    monkeypatch.setitem(globals(), "WARNING_BUDGET", 0)
    with pytest.raises(AssertionError, match="1 Juggler warnings"):
        test_lean_build_warning_budget()


def test_warning_gate_does_not_skip_unadorned_scoped_warnings(monkeypatch) -> None:
    output = "warning: Problems/Juggler/Example.lean:7:2: unused tactic\n"
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
    monkeypatch.setattr(subprocess, "run", lambda *a, **kw: SimpleNamespace(returncode=0, stdout=output))
    with pytest.raises(pytest.skip.Exception, match="warning state not observed"):
        test_lean_build_warning_budget()



def test_warning_gate_reports_missing_scope_instead_of_claiming_zero(monkeypatch) -> None:
    output = "warning: diagnostic without a source or module\nBuild completed successfully (0 jobs).\n"
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
