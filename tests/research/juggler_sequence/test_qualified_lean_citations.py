"""Citation identity must survive namespaces, comments, and same-named modules."""
from __future__ import annotations

import importlib.util
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parents[3]
_spec = importlib.util.spec_from_file_location("qualified_trust_boundary", ROOT / "tools/trust_boundary.py")
TB = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(TB)


def test_namespace_sections_qualified_tokens_and_comments():
    source = '''
namespace Problems.Example
/- namespace Fake
/- nested comment -/
theorem invented : True := by trivial
-/
section localVariables
@[simp] theorem local_result : True := by trivial
end localVariables
namespace RankedReturn
theorem terminal_actual_factorization : True := by trivial
end RankedReturn
theorem RankedReturn.other_result : True := by trivial
private theorem hidden : True := by trivial
def text : String := "namespace Wrong\\nend Problems.Example"
theorem _root_.Global.result : True := by trivial
end Problems.Example
theorem top_level : True := by trivial
'''
    names = [name for name, _ in TB.source_declarations(source)]
    assert names == [
        "Problems.Example.local_result",
        "Problems.Example.RankedReturn.terminal_actual_factorization",
        "Problems.Example.RankedReturn.other_result", "Problems.Example.text",
        "Global.result", "top_level",
    ]


def test_citation_ambiguity_never_chooses_the_first_file(tmp_path, monkeypatch):
    formal = tmp_path / "formal"
    for area in ("First", "Second"):
        folder = formal / "Problems" / area
        folder.mkdir(parents=True)
        (folder / "Shared.lean").write_text(
            f"namespace Problems.{area}\n"
            "theorem result : True := by trivial\n"
            f"end Problems.{area}\n", encoding="utf-8")
    barrel = formal / "Problems/Paper.lean"
    barrel.write_text("import Problems.First.Shared\n", encoding="utf-8")
    paper = tmp_path / "paper.md"
    paper.write_text("## Proofs\n`result` and `Problems.Second.result` and "
                     "`Problems.First.result`.\n", encoding="utf-8")
    monkeypatch.setattr(TB, "ROOT", tmp_path)
    monkeypatch.setattr(TB, "PAPER_A_ROOT", barrel)
    rows = {row["name"]: row for row in TB.audit(paper, barrel)}
    ambiguous = rows["result"]
    assert ambiguous["ambiguous"] and not ambiguous["declared"]
    assert ambiguous["qualified_name"] is None
    assert ambiguous["candidates"] == ["Problems.First.result", "Problems.Second.result"]
    assert "result" not in TB.declared()
    # Both filenames are Shared.lean. Reachability must compare complete modules.
    assert rows["Problems.First.result"]["reachable"]
    assert not rows["Problems.Second.result"]["reachable"]
    assert rows["Problems.Second.result"]["qualified_name"] == "Problems.Second.result"


def test_dotted_declaration_is_resolved_by_its_actual_basename():
    declarations = TB.source_declarations(
        "namespace Problems.Returns\n"
        "theorem RankedReturn.terminal : True := by trivial\n"
        "end Problems.Returns\n")
    assert declarations == [("Problems.Returns.RankedReturn.terminal", 2)]
    index = {name: [{"qualified_name": name, "module": "Returns"}]
             for name, _ in declarations}
    assert TB.resolve_name("terminal", index)[0]["qualified_name"] == declarations[0][0]
    assert TB.resolve_name("RankedReturn.terminal", index)[0]["qualified_name"] == declarations[0][0]


def test_global_short_name_does_not_hide_a_namespace_collision():
    index = {name: [{"qualified_name": name}] for name in ("result", "Problems.Example.result")}
    assert len(TB.resolve_name("result", index)) == 2
    assert TB.resolve_name("Problems.Example.result", index) == index["Problems.Example.result"]


def test_comments_and_strings_preserve_declaration_line_numbers():
    source = '/- comment\n/- nested -/ -/\n-- theorem phantom\n' \
             'def label := "theorem fake \\"x\\""\n' \
             'theorem actual : True := by trivial\n'
    assert TB.source_declarations(source) == [("label", 4), ("actual", 5)]


def test_unresolved_repository_qualification_is_not_silently_discarded(tmp_path, monkeypatch):
    folder = tmp_path / "formal/Problems"
    folder.mkdir(parents=True)
    module = folder / "Returns.lean"
    module.write_text(
        "namespace Problems.ReturnWordLoss\n"
        "theorem actual : True := by trivial\n"
        "structure Certificate where\n  flag : Bool\n"
        "end Problems.ReturnWordLoss\n", encoding="utf-8")
    barrel = folder / "Paper.lean"
    barrel.write_text("import Problems.Returns\n", encoding="utf-8")
    paper = tmp_path / "paper.md"
    paper.write_text(
        "`ReturnWordLoss.missing` `Problems.ReturnWordLoss.missing` "
        "`_root_.Problems.ReturnWordLoss.actual` "
        "`_root_.Problems.ReturnWordLoss.missing` "
        "`Certificate` `research.juggler_sequence.external_probe` "
        "`Real.sqrt` `Problems.Returns` `Returns.lean`", encoding="utf-8")
    monkeypatch.setattr(TB, "ROOT", tmp_path)
    monkeypatch.setattr(TB, "PAPER_A_ROOT", barrel)
    rows = {row["name"]: row for row in TB.audit(paper, barrel)}
    assert set(rows) == {
        "ReturnWordLoss.missing", "Problems.ReturnWordLoss.missing", "Certificate",
        "_root_.Problems.ReturnWordLoss.actual", "_root_.Problems.ReturnWordLoss.missing"}
    assert not rows["ReturnWordLoss.missing"]["declared"]
    assert not rows["Problems.ReturnWordLoss.missing"]["declared"]
    assert rows["Certificate"]["qualified_name"] == "Problems.ReturnWordLoss.Certificate"
    assert rows["Certificate"]["reachable"]
    assert rows["_root_.Problems.ReturnWordLoss.actual"]["qualified_name"] == \
        "Problems.ReturnWordLoss.actual"
    assert not rows["_root_.Problems.ReturnWordLoss.missing"]["declared"]


def test_absolute_name_cannot_fall_back_to_a_different_namespace():
    full = "Other.Problems.Example.result"
    index = {full: [{"qualified_name": full}]}
    assert TB.resolve_name("Problems.Example.result", index) == []
    assert TB.resolve_name("_root_.Problems.Example.result", index) == []
    assert TB.resolve_name("Example.result", index) == index[full]
    assert TB.resolve_name("_root_." + full, index) == index[full]


def test_separate_visibility_modifiers_and_sections_restore_namespace():
    source = (
        "namespace Problems.Example\n"
        "private\n@[simp]\ntheorem hidden : True := by trivial\n"
        "private section\n"
        "theorem also_hidden : True := by trivial\n"
        "public section\n"
        "theorem visible_inside : True := by trivial\n"
        "end\nend\n"
        "protected\ntheorem visible : True := by trivial\n"
        "end Problems.Example\n"
        "theorem outside : True := by trivial\n")
    assert TB.source_declarations(source) == [
        ("Problems.Example.visible_inside", 8),
        ("Problems.Example.visible", 12), ("outside", 14)]


def test_character_and_raw_string_literals_do_not_hide_or_invent_declarations():
    source = (
        "def quote : Char := '\"'\n"
        "def quoted : Char := '\\\"'\n"
        "def raw := r##\"a \" quoted string\n"
        "namespace Imaginary\n"
        "theorem invented : True := by trivial\n"
        "\"##\n"
        "theorem actual' : True := by trivial\n")
    assert TB.source_declarations(source) == [
        ("quote", 1), ("quoted", 2), ("raw", 3), ("actual'", 7)]


def test_import_closure_handles_multiple_modules_and_root_declarations(tmp_path, monkeypatch):
    folder = tmp_path / "formal/Problems"
    folder.mkdir(parents=True)
    (folder / "One.lean").write_text("import Problems.Three\n", encoding="utf-8")
    (folder / "Two.lean").write_text(
        "namespace Problems.Two\ntheorem target : True := by trivial\nend Problems.Two\n",
        encoding="utf-8")
    (folder / "Three.lean").write_text("-- no dependencies\n", encoding="utf-8")
    barrel = folder / "Paper.lean"
    barrel.write_text(
        "  import Problems.One Problems.Two -- Problems.Unused\n"
        "namespace Problems.Paper\ntheorem local_result : True := by trivial\n"
        "end Problems.Paper\n", encoding="utf-8")
    paper = tmp_path / "paper.md"
    paper.write_text("`Problems.Two.target` `Problems.Paper.local_result`", encoding="utf-8")
    monkeypatch.setattr(TB, "ROOT", tmp_path)
    monkeypatch.setattr(TB, "PAPER_A_ROOT", barrel)
    assert TB.reachable_module_names(barrel) == {
        "Problems.Paper", "Problems.One", "Problems.Two", "Problems.Three"}
    assert all(row["declared"] and row["reachable"] for row in TB.audit(paper, barrel))



def test_regular_lean_identifier_tokens_are_not_truncated():
    source = """namespace Problems.α₁
 theorem A₁ : True := by trivial
 theorem getLast?_append_cons : True := by trivial
 theorem replicate_odd_getLast? : True := by trivial
 theorem rotateItinerary_getElem? : True := by trivial
 theorem bang!_step'(x : Nat) : x = x := rfl
 theorem Greek.β₂.{u} : True := by trivial
end Problems.α₁
"""
    expected = ["A₁", "getLast?_append_cons", "replicate_odd_getLast?",
                "rotateItinerary_getElem?", "bang!_step'", "Greek.β₂"]
    assert [name for name, _ in TB.source_declarations(source)] == [
        "Problems.α₁." + name for name in expected]
    assert TB.identifier_tokens("A₁ getLast?_append_cons f!_next α.β₂") == [
        "A₁", "getLast?_append_cons", "f!_next", "α.β₂"]


@pytest.mark.parametrize("name", ["brokenλ", "broken漢", "broken..part", "broken.", "«escaped name»"])
def test_unsupported_or_invalid_header_is_not_indexed_as_a_valid_prefix(name):
    assert TB.source_declarations(f"theorem {name} : True := by trivial") == []


def test_the_four_observed_juggler_names_have_exact_source_identities():
    names = {
        "LocalizedKernel": ("A₁", "A"),
        "EvenCountThree": ("getLast?_append_cons", "getLast"),
        "CyclePosition": ("rotateItinerary_getElem?", "rotateItinerary_getElem"),
    }
    for module, (actual, truncated) in names.items():
        source = (ROOT / "formal/Problems/Juggler" / f"{module}.lean").read_text(encoding="utf-8")
        declared = {name for name, _ in TB.source_declarations(source)}
        assert "Problems.Juggler." + actual in declared
        assert "Problems.Juggler." + truncated not in declared
    source = (ROOT / "formal/Problems/Juggler/EvenCountThree.lean").read_text(encoding="utf-8")
    declared = {name for name, _ in TB.source_declarations(source)}
    assert "Problems.Juggler.replicate_odd_getLast?" in declared
    assert "Problems.Juggler.replicate_odd_getLast" not in declared


def test_unicode_and_question_mark_citations_resolve_without_shorter_aliases(tmp_path, monkeypatch):
    folder = tmp_path / "formal/Problems"
    folder.mkdir(parents=True)
    module = folder / "Cells.lean"
    module.write_text("namespace Problems.Cells\n"
                      "theorem A₁ : True := by trivial\n"
                      "theorem getLast?_append_cons : True := by trivial\n"
                      "end Problems.Cells\n", encoding="utf-8")
    barrel = folder / "Paper.lean"
    barrel.write_text("import Problems.Cells\n", encoding="utf-8")
    paper = tmp_path / "paper.md"
    paper.write_text("`A₁` `Cells.getLast?_append_cons` `Cells.getLast?_missing` "
                     "`Problems.Cells.A`", encoding="utf-8")
    monkeypatch.setattr(TB, "ROOT", tmp_path)
    monkeypatch.setattr(TB, "PAPER_A_ROOT", barrel)
    rows = {row["name"]: row for row in TB.audit(paper, barrel)}
    assert set(rows) == {"A₁", "Cells.getLast?_append_cons", "Cells.getLast?_missing", "Problems.Cells.A"}
    assert rows["A₁"]["qualified_name"] == "Problems.Cells.A₁"
    assert rows["Cells.getLast?_append_cons"]["reachable"]
    assert not rows["Cells.getLast?_missing"]["declared"]
    assert not rows["Problems.Cells.A"]["declared"]


def test_reference_context_uses_the_same_namespace_and_visibility_stack():
    source = ("namespace Problems.α₁\nprivate section\n"
              "theorem hidden : True := by trivial\nend\n"
              "namespace Inner\ntheorem visible : True := by trivial\nend Inner\n"
              "theorem next? : True := by trivial\nend Problems.α₁\n")
    contexts = {line: (namespace, private) for line, _, namespace, private in TB.scoped_source_commands(source)}
    assert contexts == {3: ("Problems.α₁", True), 6: ("Problems.α₁.Inner", False),
                        8: ("Problems.α₁", False)}


def test_punctuation_then_apostrophes_are_identifier_rest_not_a_character_literal():
    source = "theorem f?'x' : True := by trivial\n" + "theorem g!'y' : True := by trivial\n"
    assert TB.source_declarations(source) == [("f?'x'", 1), ("g!'y'", 2)]
    assert TB.identifier_tokens(source)[1] == "f?'x'"


@pytest.mark.parametrize("scope", ["namespace «escaped namespace»", "namespace Invalidλ", "end «escaped namespace»"])
def test_unsupported_scope_cannot_misqualify_a_child(scope):
    with pytest.raises(ValueError, match="Unsupported Lean scope"):
        TB.source_declarations(scope + "\ntheorem child : True := by trivial\n")
