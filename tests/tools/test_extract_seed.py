"""The seed extractor: slicing, splitting and scoping, on a synthetic Lean file.

The seed is what the local prover learns from, so the two things that matter
are that a record's statement plus proof is the declaration the kernel saw,
and that nothing off the kernel gets in. The first is checked here on a file
that exercises binders with ``:=`` inside, attributes, docstrings, nested
sections with their own ``open`` and ``variable`` lines, and term-mode bodies.
The second is a filter on the index's ``trust`` field, checked on the summary.
"""

from __future__ import annotations

import json
import sys
from pathlib import Path

REPO = Path(__file__).resolve().parents[2]
SEED_TOOLS = REPO / "tools" / "seed"
if str(SEED_TOOLS) not in sys.path:
    sys.path.insert(0, str(SEED_TOOLS))

import extract_seed as es  # noqa: E402
import verify as vf  # noqa: E402

LEAN = """\
import Mathlib.Tactic
import Core.Basic

/-! Module docstring. The word
namespace Fake
inside a comment must not open a scope. -/

open Nat

namespace Outer

variable {n : ℕ}
  (hn : 0 < n)

section Inner
open Finset in
/-- A docstring
on two lines. -/
@[simp]
theorem with_attr (h : n = 1 := by rfl) : n = 1 := by
  exact h

theorem term_mode : 1 + 1 = 2 :=
  rfl
end Inner

theorem after_section : n = n := by
  -- a comment with := in it
  rfl

end Outer
"""


def lines() -> list[str]:
    return LEAN.splitlines()


def test_split_body_ignores_binder_and_comment_assignments() -> None:
    text = "theorem t (h : n = 1 := by rfl) : n = 1 := by\n  -- x := y\n  exact h"
    statement, proof, mode = es.split_body(text)
    assert mode == "tactic"
    assert statement == "theorem t (h : n = 1 := by rfl) : n = 1 := by"
    assert proof == "\n  -- x := y\n  exact h"


def test_split_body_equation_compiler() -> None:
    text = "theorem t : ∀ n : ℕ, n = n\n  | 0 => rfl\n  | n + 1 => by simp"
    statement, proof, mode = es.split_body(text)
    assert mode == "equations"
    assert statement == "theorem t : ∀ n : ℕ, n = n"
    assert proof == "\n  | 0 => rfl\n  | n + 1 => by simp"


def test_split_body_term_mode() -> None:
    statement, proof, mode = es.split_body("theorem t : 1 = 1 :=\n  rfl")
    assert mode == "term"
    assert statement == "theorem t : 1 = 1 :="
    assert proof == "\n  rfl"


def test_slice_takes_attributes_open_in_and_docstring() -> None:
    L = lines()
    start = next(i for i, l in enumerate(L) if l.startswith("theorem with_attr"))
    first, last, doc = es.slice_decl(L, start)
    assert L[first] == "open Finset in"
    assert L[first + 1].startswith("/--")
    assert L[first + 3] == "@[simp]"
    assert L[last] == "  exact h"
    assert doc == "/-- A docstring\non two lines. -/"


def test_header_context_tracks_scopes_and_skips_comments() -> None:
    L = lines()
    start = next(i for i, l in enumerate(L) if l.startswith("theorem with_attr"))
    imports, ctx = es.header_context(L, start)
    assert imports == ["import Mathlib.Tactic", "import Core.Basic"]
    assert ctx == [
        "open Nat",
        "namespace Outer",
        "variable {n : ℕ}\n  (hn : 0 < n)",
        "section Inner",
    ]
    after = next(i for i, l in enumerate(L) if l.startswith("theorem after_section"))
    _, ctx_after = es.header_context(L, after)
    assert ctx_after == ["open Nat", "namespace Outer", "variable {n : ℕ}\n  (hn : 0 < n)"]
    assert not any("Fake" in c for c in ctx_after)


def test_build_excludes_compiler_trust_and_reconstructs(tmp_path: Path, monkeypatch) -> None:
    src = tmp_path / "formal" / "Fake.lean"
    src.parent.mkdir()
    src.write_text(LEAN, encoding="utf-8")
    L = lines()
    line_of = lambda prefix: 1 + next(i for i, l in enumerate(L) if l.startswith(prefix))  # noqa: E731
    index = {"declarations": [
        {"name": "Outer.with_attr", "module": "Fake", "file": "formal/Fake.lean",
         "line": line_of("theorem with_attr"), "kind": "theorem", "trust": "kernel", "doc": "", "ledger": []},
        {"name": "Outer.term_mode", "module": "Fake", "file": "formal/Fake.lean",
         "line": line_of("theorem term_mode"), "kind": "theorem", "trust": "kernel", "doc": "", "ledger": []},
        {"name": "Outer.after_section", "module": "Fake", "file": "formal/Fake.lean",
         "line": line_of("theorem after_section"), "kind": "theorem", "trust": "compiler", "doc": "", "ledger": []},
        {"name": "Outer.someDef", "module": "Fake", "file": "formal/Fake.lean",
         "line": 1, "kind": "def", "trust": "kernel", "doc": "", "ledger": []},
    ]}
    index_path = tmp_path / "index.json"
    index_path.write_text(json.dumps(index), encoding="utf-8")
    monkeypatch.setattr(es, "ROOT", tmp_path)
    summary = es.build(index_path, tmp_path / "seed")
    assert summary["kernel_theorems"] == 2
    assert summary["excluded_compiler_trust"] == 1
    assert summary["tactic"] == 1 and summary["term"] == 1 and summary["failed"] == []
    [rec] = [json.loads(l) for l in (tmp_path / "seed" / "seed.jsonl").open(encoding="utf-8")]
    assert rec["name"] == "Outer.with_attr"
    assert rec["statement"].startswith("open Finset in\n/-- A docstring")
    assert rec["statement"].endswith(":= by")
    assert rec["first_tactic"] == "exact"
    assert rec["context"].endswith("section Inner")
    # statement + proof is the declaration the kernel saw, up to the space before `by`
    assert (rec["statement"] + rec["proof"]).replace(":= by", ":=by") == rec["full"].replace(":= by", ":=by")
    assert rec["span"] == [line_of("open Finset in"), line_of("  exact h")]


def test_splice_replaces_span_and_probes_short_name() -> None:
    L = lines()
    first = 1 + next(i for i, l in enumerate(L) if l.startswith("open Finset in"))
    last = 1 + next(i for i, l in enumerate(L) if l == "  exact h")
    statement = "\n".join(L[first - 1:last - 1]).rsplit(" by", 1)[0] + " by"
    out = vf.splice(L, [first, last], statement, "\n  simpa using h")
    assert "  exact h" not in out
    assert "  simpa using h\n\n#print axioms with_attr\n" in out
    assert out.startswith("import Mathlib.Tactic\n")
    assert out.rstrip().endswith("end Outer")
    assert "theorem term_mode" in out  # the rest of the file is untouched


def test_gate_rejects_errors_sorry_and_native_decide() -> None:
    assert vf.gate(None, "", 5)[1].startswith("timeout")
    assert vf.gate(1, "f.lean:3:2: error: unsolved goals", 5)[1] == "compile error"
    assert vf.gate(0, "f.lean:3:2: warning: declaration uses 'sorry'\n'x' depends on axioms: [sorryAx]", 5)[1] == "sorry"
    assert vf.gate(0, "'x' depends on axioms: [propext, Lean.ofReduceBool]", 5)[1] == "forbidden axioms: Lean.ofReduceBool"
    assert vf.gate(0, "'x' depends on axioms: [propext, Classical.choice, Quot.sound]", 5)[0]
    assert vf.gate(0, "'x' does not depend on any axioms", 5)[0]
