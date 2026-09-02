"""Juggler Lean layers are one-way, Engine copies are gone, and no sorry."""

from __future__ import annotations

import re

from research.juggler_sequence.lean_paths import (
    DELETED_ENGINE,
    JUGGLER_DIR,
    JUGGLER_PAPER_BARREL,
    LAYERS,
    PAPER_MODULES,
    engine_juggler_gone,
    has_named,
    juggler_sources,
    juggler_text,
)

LAYER_RANK = {name: i for i, name in enumerate(LAYERS)}
IMPORT_RE = re.compile(r"^import Problems\.Juggler\.(\w+)", re.M)
INCOMPLETE = ("sorry", "admit", "axiom")

BOXED = (
    "HasFiniteStop",
    "HasFiniteCoeffStop",
    "FiniteCoeffStopConjecture",
    "DescentCertificate",
    "FiniteProgress",
    "MinimalNonTerm",
    "MinimalImpliesCoeffStop",
    "AboveAnchor",
    "follows_iff_itinerary",
    "coeffStop_implies_stop",
)

FORBIDDEN_ENGINE_NAMES = (
    "Problems.Engine.FloorPower",
    "Problems.Engine.Progress",
    "Problems.Engine.MinimalNonTerm",
    "Problems.Engine.RepeatedOE",
    "Problems.Engine.OddRunFinancing",
    "Problems.Engine.OddOddFrontier",
    "Problems.Engine.ResidualChain",
    "Problems.Engine.ResidualPath",
    "Problems.Engine.RepeatedBlock",
    "Problems.Engine.CycleItinerary",
    "Problems.Engine.CycleDiophantine",
)


def test_engine_juggler_files_are_gone():
    assert engine_juggler_gone()
    for path in DELETED_ENGINE:
        assert not path.is_file(), path


def test_layers_exist_and_are_sorry_free():
    assert JUGGLER_DIR.is_dir()
    text = juggler_text()
    for token in INCOMPLETE:
        assert token not in text, token
    for name, path in LAYERS.items():
        assert path.is_file(), name
        body = path.read_text(encoding="utf-8")
        for token in INCOMPLETE:
            assert token not in body, f"{name} contains {token}"


def test_imports_are_one_way():
    for name, path in LAYERS.items():
        body = path.read_text(encoding="utf-8")
        for match in IMPORT_RE.finditer(body):
            dep = match.group(1)
            assert dep in LAYER_RANK, f"{name} imports unknown {dep}"
            assert LAYER_RANK[dep] < LAYER_RANK[name], f"{name} imports {dep}"


def test_boxed_implication_is_first_class():
    text = juggler_text()
    for name in BOXED:
        assert has_named(text, name), name
    assert "theorem juggler_reaches_one" not in text
    assert "theorem all_finiteProgress" not in text


def test_paper_barrel_is_the_named_review_object():
    assert JUGGLER_PAPER_BARREL.is_file()
    body = JUGGLER_PAPER_BARREL.read_text(encoding="utf-8")
    for token in INCOMPLETE:
        assert token not in body, token
    imported = IMPORT_RE.findall(body)
    assert imported == list(PAPER_MODULES)
    assert "laboratory target, not a claim" in body
    assert "lake build Problems.JugglerPaper" in body
    assert "no_cycle_itinerary_oooeoe" in body
    assert "no_cycle_itinerary_ooooee" in body
    assert "no_cycle_itinerary_length_six" not in body


def test_no_engine_juggler_names_in_live_sources():
    for path in juggler_sources():
        body = path.read_text(encoding="utf-8")
        assert "Problems.Engine" not in body, path.name
        for name in FORBIDDEN_ENGINE_NAMES:
            assert name not in body, f"{path.name} mentions {name}"
