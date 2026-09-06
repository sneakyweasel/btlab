"""The theorem index, and the two invariants it exists to keep honest.

The corpus is sorry-free and all but a named handful is kernel-checked.  Both facts are
asserted in the manuscripts, so both are worth a test that reads the Lean rather than the
prose: Paper A's Section 1.2 states the trust boundary positively, and a new
``native_decide`` slipping in anywhere would make that sentence false.
"""

from __future__ import annotations

import sys
from pathlib import Path

REPO = Path(__file__).resolve().parents[2]
TOOLS = REPO / "tools"
if str(TOOLS) not in sys.path:
    sys.path.insert(0, str(TOOLS))

import formalpedia as fp

JUGGLER_COMPILER_TRUST = {
    "greedy_eq_ostro_below_window",
    "window_digit_scan",
}
"""The two Ostrowski scans Paper A names as the only proofs off the kernel in its layer."""


def test_the_index_covers_the_libraries_and_not_the_build_output() -> None:
    paths = fp.sources()
    assert paths, "no Lean sources found"
    assert not any(".lake" in p.parts for p in paths)


def test_every_declaration_carries_its_location_and_trust() -> None:
    index = fp.build()
    assert index["totals"]["declarations"] > 3000
    for d in index["declarations"]:
        assert d["name"] and d["module"] and d["file"]
        assert d["line"] >= 1
        assert d["trust"] in {"kernel", "compiler", "open"}


def test_the_corpus_carries_no_sorry() -> None:
    index = fp.build()
    open_ = [d["name"] for d in index["declarations"] if d["trust"] == "open"]
    assert open_ == [], open_


def test_the_juggler_layer_keeps_only_the_two_named_scans_off_the_kernel() -> None:
    index = fp.build()
    found = {
        d["name"]
        for d in index["declarations"]
        if d["trust"] == "compiler" and d["module"].startswith("Problems.Juggler")
    }
    assert found == JUGGLER_COMPILER_TRUST, found


def test_a_docstring_belongs_to_the_declaration_it_sits_above() -> None:
    """Regression: reaching backwards for any earlier ``/--`` gave one paragraph to many."""
    text = "/-- First. -/\ntheorem a : True := trivial\n\ntheorem b : True := trivial\n"
    assert fp._docstring(text, text.index("theorem a")) == "First."
    assert fp._docstring(text, text.index("theorem b")) == ""


def test_dependents_reverses_the_import_graph() -> None:
    index = fp.build()
    rev = fp.dependents(index)
    for target, importers in rev.items():
        for name in importers:
            assert target in index["modules"][name]["imports"]


def test_impact_of_a_leaf_is_a_superset_of_its_direct_importers() -> None:
    index = fp.build()
    rev = fp.dependents(index)
    for module in list(index["modules"])[:40]:
        assert set(rev.get(module, [])) <= set(fp.transitive(rev, module))
