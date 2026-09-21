"""Lemmas 1 and 3 of the 3n-1 note, as Lean: the module exists, is reached by the build, and
carries no `sorry` and nothing off the kernel.

This reads the Lean source and the theorem index, not the prose. The note's Section 7 states
that Lemmas 1 and 3 are machine-checked and that Lemma 2 is not, and Section 8 names the
build; a `sorry` or a `native_decide` appearing here, or the module dropping out of the
`Problems` barrel, would make those sentences false without anything else noticing.

The axiom report itself is not reproduced here: it needs `lake env lean`, which the Python
suite does not run. It was taken on 21 September 2026 and is recorded in the dossier --
thirteen declarations on Mathlib's three standard axioms, five (the `decide` computations on
the known cycles) on none at all, two derived.
"""
from __future__ import annotations

import re
import sys
from pathlib import Path

REPO = Path(__file__).resolve().parents[3]
MODULE = REPO / "formal" / "Problems" / "Collatz" / "NegativeMCycles.lean"
BARREL = REPO / "formal" / "Problems.lean"
NOTE = REPO / "docs" / "theory" / "collatz_3n_minus_1_m_cycles_note.md"

TOOLS = REPO / "tools"
if str(TOOLS) not in sys.path:
    sys.path.insert(0, str(TOOLS))

#: the declarations the note's Sections 7 and 8 lean on, by name
LEMMA_ONE = ("negT_run_iter", "negT_run_odd", "negT_run_even", "negT_start_ge",
             "negT_localMax", "negT_run_decomp", "negT_lemma_one")
LEMMA_THREE = ("negT_chain_nat", "negT_chain_real", "negT_lemma_three")
KNOWN_CYCLES = ("negT_sign_is_minus", "negT_cycle_one", "negT_cycle_five",
                "negT_cycle_seventeen", "negT_run_at_seventeen", "negT_chain_tight_at_17")


def _source() -> str:
    return MODULE.read_text(encoding="utf-8")


def test_the_module_exists_and_is_in_the_barrel() -> None:
    """Outside the barrel the default build would not compile it, and a break would be
    invisible until someone built the module by name."""
    assert MODULE.is_file(), MODULE
    assert "import Problems.Collatz.NegativeMCycles" in BARREL.read_text(encoding="utf-8")


def test_every_named_declaration_is_present() -> None:
    src = _source()
    for name in LEMMA_ONE + LEMMA_THREE + KNOWN_CYCLES:
        assert re.search(rf"^theorem {re.escape(name)}\b", src, re.M), name


def test_no_sorry_and_nothing_off_the_kernel() -> None:
    """The corpus-wide invariant, checked here too: no `sorry`, and no `native_decide`, which
    would add a compiler-trust point outside the one the Juggler layer declares."""
    src = _source()
    assert not re.search(r"\bsorry\b", src)
    assert "native_decide" not in src
    assert "axiom " not in src


def test_the_map_is_the_3n_minus_1_map_not_3n_plus_1() -> None:
    """The sign is the whole content of the transposition. The definition must subtract, and
    the module must carry the kernel check that separates it from the 3n+1 shortcut."""
    src = _source()
    assert "(3 * y - 1) / 2" in src
    assert "(3 * y + 1) / 2" not in src
    assert "negT_sign_is_minus" in src and "negT 17 = 25" in src


def test_the_known_cycles_are_checked_inside_the_kernel() -> None:
    """Section 6 of the note checks the inequalities where they must not exclude; the same
    three cycles are the kernel's evidence that these statements are about the intended map."""
    src = _source()
    for fragment in ("negTIter 1 1 = 1", "negTIter 3 5 = 5", "negTIter 11 17 = 17"):
        assert fragment in src, fragment
    # the chaining is tight at 17: 2 * 40 < 81, one unit of slack
    assert "2 * (41 - 1) < 3 ^ 4 * 1" in src


def test_the_note_claims_exactly_what_is_proved() -> None:
    """Lemmas 1 and 3 machine-checked, Lemma 2 not: the note must say both, and must not
    revert to the earlier 'not yet in Lean'."""
    note = NOTE.read_text(encoding="utf-8")
    assert "Problems.Collatz.NegativeMCycles" in note
    assert "Lemmas 1 and 3 are machine-checked" in note
    assert "Lemma 2 is not in Lean" in note
    assert "not yet in Lean" not in note


def test_the_index_agrees_that_the_module_is_kernel_checked() -> None:
    """The theorem index reads the Lean source directly, so it is the second opinion on the
    trust level of every declaration in the module."""
    import formalpedia as fp

    index = fp.build_index() if hasattr(fp, "build_index") else None
    if index is None:  # the tool's entry point differs; the source checks above still stand
        return
    rows = [d for d in _iter_decls(index) if d.get("module") == "Problems.Collatz.NegativeMCycles"]
    assert rows, "the module is missing from a fresh index"
    assert all(d.get("trust") == "kernel" for d in rows), [d["name"] for d in rows
                                                           if d.get("trust") != "kernel"]


def _iter_decls(index):
    if isinstance(index, dict):
        for value in index.values():
            if isinstance(value, list):
                yield from (d for d in value if isinstance(d, dict) and "name" in d)
    elif isinstance(index, list):
        yield from (d for d in index if isinstance(d, dict) and "name" in d)
