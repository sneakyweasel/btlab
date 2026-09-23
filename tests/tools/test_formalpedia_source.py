"""Formalpedia source regressions; live corpus snapshots are isolated by conftest."""
from __future__ import annotations


from formalpedia_core import (
    identities as fp_identities,
    source as fp_source,
    workspace as fp_workspace,
)


def test_the_index_covers_the_libraries_and_not_the_build_output() -> None:
    paths = fp_source.sources()
    assert paths, "no Lean sources found"
    assert not any(".lake" in p.parts for p in paths)


def test_every_declaration_carries_its_location_and_trust(corpus_index) -> None:
    index = corpus_index
    assert index["totals"]["declarations"] > 3000
    for d in index["declarations"]:
        assert d["name"] and d["module"] and d["file"]
        assert d["line"] >= 1
        assert d["trust"] in {"kernel", "compiler", "open"}


def test_a_docstring_belongs_to_the_declaration_it_sits_above() -> None:
    """Regression: reaching backwards for any earlier ``/--`` gave one paragraph to many."""
    text = "/-- First. -/\ntheorem a : True := trivial\n\ntheorem b : True := trivial\n"
    assert fp_source._docstring(text, text.index("theorem a")) == "First."
    assert fp_source._docstring(text, text.index("theorem b")) == ""


def test_declares_requires_the_name_to_end_at_the_match() -> None:
    """The corpus names helper lemmas by extending their main theorem, so 519 of 4,528 names
    are a proper prefix of another. A substring check cannot tell them apart; this one can."""
    text = (
        "theorem power_bound_compensated_contracts_follows (h : True) : True := trivial\n"
    )
    assert not fp_source.declares(text, "power_bound_compensated_contracts")
    assert fp_source.declares(text, "power_bound_compensated_contracts_follows")


def test_declares_finds_a_real_declaration_in_the_corpus() -> None:
    path = fp_workspace.ROOT / "formal" / "Problems" / "Juggler" / "CycleFinance.lean"
    text = path.read_text(encoding="utf-8")
    assert fp_source.declares(text, "cycleMin_finance")
    assert not fp_source.declares(text, "cycleMin_financ")
    assert not fp_source.declares(text, "cycleMin_finance_extra_suffix")


def test_the_index_holds_the_declarations_written_with_an_attribute(corpus_index) -> None:
    """``@[simp] theorem foo`` is a declaration, and 70 in ``formal/`` are written that way.

    The pattern had no room for ``@[...]`` in front of the keyword, so all 70 were absent
    from the index outright -- not mislabelled, not mis-filed, simply not there. A missing
    declaration is the quietest failure this index has: ``jev-propose`` cannot offer it,
    ``jev-coverage`` cannot score it, and both ledger gates that look a row's ``decl`` up
    here ``continue`` when the name is absent, so a row naming one would be checked by
    nothing at all while every gate stayed green.
    """
    decls = {(d["file"], d["name"]) for d in corpus_index["declarations"]}
    for rel, name in (
        ("formal/Problems/Collatz/NegativeMCycles.lean", "negTIter_zero"),
        ("formal/Problems/Collatz/NegativeMCycles.lean", "negTIter_succ"),
    ):
        source = (fp_workspace.ROOT / rel).read_text(encoding="utf-8")
        assert f"@[simp] theorem {name}" in source, f"{name} is no longer written this way"
        assert (rel, name) in decls, f"{name} is declared in {rel} and the index omits it"


def test_no_declaration_in_the_index_is_prose_from_a_comment(corpus_index) -> None:
    """A wrapped docstring line is not a declaration, and six of them were indexed as one.

    ``formal/`` writes long docstrings, and when one wraps so that ``theorem``, ``lemma`` or
    ``instance`` lands at column 0 the pattern reads the next English word as a name. That
    put declarations called ``of``, ``at``, ``needs`` and ``nothing`` in the index, with a
    kind, a line and a trust level, indistinguishable from real ones to everything
    downstream. The ``^`` anchor was the only thing holding this back, which is why comments
    are blanked before the scan rather than indentation simply being allowed: permitting an
    indented declaration without blanking first adds a seventh, ``beats``, from the module
    docstring of ``FateTaoReduction.lean``.
    """
    names = {d["name"] for d in corpus_index["declarations"]}
    for word in ("of", "at", "needs", "nothing", "beats"):
        assert word not in names, f"{word!r} is English prose, not a declaration"


def test_the_declaration_pattern_reads_lean_and_not_prose_about_it() -> None:
    """The pattern, against the three forms it missed and the one it must keep missing."""
    sample = (
        "/-- A docstring whose line wraps so that a keyword lands at column 0, the way\n"
        "the contagion\n"
        "theorem beats a bound; and again, indented, so the\n"
        "  lemma pretends to be a declaration. -/\n"
        "@[simp] theorem tagged_thing : True := trivial\n"
        "section Inner\n"
        "  theorem indented_thing : True := trivial\n"
        "end Inner\n"
        "-- a line comment mentioning theorem commented_thing\n"
        "private noncomputable def modified_thing : Nat := 0\n"
    )
    found = {m.group("name") for m in fp_source.DECL.finditer(fp_source.blank_comments(sample))}
    assert found == {"tagged_thing", "indented_thing", "modified_thing"}, found


def test_a_docstring_above_an_attribute_declaration_still_reaches_it() -> None:
    """The scan runs on blanked text and the docstring is sliced from the original at the
    offset it reports, reading backwards from the match. The match now opens at the start of
    the line rather than at the keyword, so an attribute must not come between the two.

    None of the 70 in ``formal/`` carries prose today -- ``@[simp]`` lemmas here are written
    without it -- so asserting this on the corpus would pass without exercising anything.
    """
    text = (
        "/-- Negating a trit twice returns it. -/\n"
        "@[simp] theorem negate_negate : True := trivial\n"
    )
    hits = list(fp_source.DECL.finditer(fp_source.blank_comments(text)))
    assert [m.group("name") for m in hits] == ["negate_negate"]
    assert fp_source._docstring(text, hits[0].start()) == "Negating a trit twice returns it."


def test_blanking_comments_moves_no_byte_and_keeps_every_line() -> None:
    """Offsets have to survive it: the scan runs on the blanked text and the docstring and
    trust of each declaration are sliced from the original at the same positions. A blanker
    that shortened the text would report every line number after the first comment wrong."""
    for path in fp_source.sources():
        text = path.read_text(encoding="utf-8")
        blanked = fp_source.blank_comments(text)
        assert len(blanked) == len(text), path
        assert blanked.count("\n") == text.count("\n"), path


def test_declares_reads_the_forms_a_declaration_is_actually_written_in() -> None:
    """``declares`` guards deletions, so a form it cannot read reports a live theorem gone.

    It took a bare keyword with no room for either an attribute or a modifier, so
    ``@[simp] theorem foo`` and ``private theorem foo`` both answered False -- the answer
    that means "this theorem is no longer here".
    """
    assert fp_source.declares("@[simp] theorem tagged_thing : True := trivial\n", "tagged_thing")
    assert fp_source.declares("private theorem hidden_thing : True := trivial\n", "hidden_thing")
    assert fp_source.declares("theorem plain_thing : True := trivial\n", "plain_thing")
    assert fp_source.declares("  theorem indented_thing : True := trivial\n", "indented_thing")
    # And still answers False for a name that is not declared, which is the point of it.
    assert not fp_source.declares("@[simp] theorem tagged_thing : True := trivial\n", "tagged")
    assert not fp_source.declares("theorem plain_thing : True := trivial\n", "plain_thing_more")


def test_the_prefix_collision_surface_is_real_and_measured(corpus_index) -> None:
    """If this ever drops to zero the `declares` boundary stops mattering and can go."""
    names = {d["name"] for d in corpus_index["declarations"]}
    ordered = sorted(names)
    shadowed = {n for n, following in zip(ordered, ordered[1:]) if following.startswith(n)}
    assert len(shadowed) > 100, len(shadowed)


def test_signature_returns_the_statement_without_the_proof(corpus_index) -> None:
    index = corpus_index
    decl = next(d for d in index["declarations"] if d["name"] == "cycleMin_finance")
    sig = fp_identities.signature(decl)
    assert sig.startswith("theorem cycleMin_finance")
    assert ":=" not in sig and "by" not in sig.split("\n")[-1]
