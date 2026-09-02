"""Run-type survivor lattice. Not a halt test."""

from __future__ import annotations

from pathlib import Path

from research.juggler_sequence.cycle_finance import o_min_and_theta, sha256_int_list
from research.juggler_sequence.cycle_run_extremum import survivor_lengths
from research.juggler_sequence.lean_paths import (
    JUGGLER_PAPER_BARREL,
    RUN_SURVIVOR_LATTICE,
    has_named,
)

REPO = Path(__file__).resolve().parents[3]
NOTE = REPO / "docs" / "theory" / "juggler_finite_dynamics_note.md"

LSTAR, OSTAR = 25781, 16266
LSTEP, OSTEP = 1054, 665


def lattice_point(a: int, b: int) -> tuple[int, int]:
    return a * LSTAR + b * LSTEP, a * OSTAR + b * OSTEP


def test_basis_is_unimodular():
    assert LSTAR * OSTEP - LSTEP * OSTAR == 1
    assert 3**665 > 2**1054 >= 3**664
    assert o_min_and_theta(LSTEP)[0] == OSTEP


def test_seeds_and_families_match_the_99():
    assert lattice_point(2, -1) == (50508, 31867)
    assert lattice_point(3, -1) == (76289, 48133)
    family1 = [lattice_point(1, b) for b in range(0, 29)]
    family2 = [lattice_point(2, b) for b in range(-1, 46)]
    family3 = [lattice_point(3, b) for b in range(-1, 22)]
    deaths = [lattice_point(1, b) for b in range(29, 71)]
    assert len(family1) == 29
    assert len(family2) == 47
    assert len(family3) == 23
    assert len(deaths) == 42
    survivors = survivor_lengths()
    assert len(survivors) == 99
    assert {L for L, _o in family1 + family2 + family3} == set(survivors)
    assert sha256_int_list(survivors) == (
        "9e2098923ccb39933630b116133a3fc2ddaf98ace4eb76dbab9b5ab9f6e604e6"
    )
    for length, odd_count in family1 + family2 + family3 + deaths:
        assert o_min_and_theta(length)[0] == odd_count


def test_lean_and_paper_name_the_lattice():
    lean = RUN_SURVIVOR_LATTICE.read_text(encoding="utf-8")
    paper = JUGGLER_PAPER_BARREL.read_text(encoding="utf-8")
    note = NOTE.read_text(encoding="utf-8")
    assert has_named(lean, "run_survivor_unimodular")
    assert has_named(lean, "run_survivor_seed_F2")
    assert has_named(lean, "run_survivor_seed_F3")
    assert has_named(lean, "three_pow_step_gt_two_pow_step")
    assert has_named(lean, "runSurvivors")
    assert "sorry" not in lean
    assert "admit" not in lean
    assert "import Problems.Juggler.RunSurvivorLattice" in paper
    assert "Theorem 4.7" in note
    assert "Theorem 4.8" in note
    assert "Proposition 4.9" in note
    assert "run_survivor_unimodular" in note
    assert r"\mathcal E_{\mathrm{run}}" in note
    assert "99" in note
    assert "theorem no_cycle_itinerary_any_length" not in note
    assert "theorem juggler_reaches_one" not in note
