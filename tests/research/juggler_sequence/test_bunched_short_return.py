"""Exact short-cluster return sets. Not a halt, interval, or Z5 test."""

from __future__ import annotations

import json

from research.juggler_sequence.bunched_short_return import (
    CLASS_PARK,
    FORBIDDEN_THEOREMS,
    LEAN_THEOREMS,
    N_CYCLEMIN,
    N_ODD_SQ,
    ODD_SQUARE_HITS_500,
    SHORT_PAIRS,
    classify,
    even_preimages,
    lean_api_present,
    odd_preimages,
    odd_square_cell,
    render_markdown,
    return_set,
    short_tail,
    write_artifacts,
)
from research.juggler_sequence.cycle_itinerary import follows_itinerary, image_after
from research.juggler_sequence.power_itineraries import ANTI_OVERCLAIM, floor_power


def test_short_tails_and_even_inverse():
    assert SHORT_PAIRS == (
        (0, 0),
        (1, 0),
        (2, 0),
        (3, 0),
        (0, 1),
        (1, 1),
        (2, 1),
    )
    assert short_tail(0, 0) == "EE"
    assert short_tail(3, 0) == "OOOEE"
    assert short_tail(0, 1) == "EOE"
    assert short_tail(2, 1) == "OOEOE"
    ev13 = even_preimages(13)
    assert ev13 == list(range(170, 196, 2))
    assert 169 not in ev13
    assert even_preimages(12)[0] == 144
    assert even_preimages(12) != [144]


def test_odd_square_hits_are_exact_and_complete_through_cutoff():
    assert len(ODD_SQUARE_HITS_500) == 12
    for n, z in ODD_SQUARE_HITS_500:
        assert z % 2 == 1
        assert floor_power(z) == n * n
        row = odd_square_cell(n)
        assert row["odd_preimages"] == [z]
        assert row["integer_width"] == 1
    assert odd_preimages(13 * 13) == []
    assert odd_square_cell(12)["empty"] is True
    assert ODD_SQUARE_HITS_500[-1] == (343, 2401)
    assert N_ODD_SQ == 500


def test_return_set_is_exact_forward_preimage():
    cases = (
        (12, 0, 0),
        (12, 0, 1),
        (12, 1, 1),
        (6, 2, 1),
        (13, 1, 0),
    )
    expected = {
        (12, 0, 0): 2041,
        (12, 0, 1): 29,
        (12, 1, 1): 2,
        (6, 2, 1): 1,
        (13, 1, 0): 23,
    }
    for n, b, c in cases:
        states = return_set(n, b, c)
        assert len(states) == expected[(n, b, c)]
        tail = short_tail(b, c)
        for y in states[:12]:
            assert y >= n
            assert follows_itinerary(y, tail)
            assert image_after(y, tail) == n
    assert return_set(12, 1, 1) == [91, 93]
    assert return_set(6, 2, 1) == [9]
    assert return_set(12, 3, 0) == []
    assert return_set(13, 2, 0) == []


def test_probe_and_classify_park():
    payload = write_artifacts()
    scan = payload["scan"]
    lean = payload["lean"]
    decision = classify(scan, lean)
    assert decision["classification"] == CLASS_PARK
    inverse = scan["inverse"]
    assert inverse["even_singleton_n2"] is False
    assert inverse["odd_sq_odd_hits"] == 12
    assert inverse["odd_sq_empty"] == 477
    assert inverse["odd_sq_even_blocked"] == 10
    assert inverse["odd_sq_hits_match_table"] is True
    assert inverse["last_odd_empty_layers"] == 15
    assert inverse["last_odd_max"] == 2
    assert inverse["cycle_last_even_ne_odd_sq"] is True
    counts = { (row["b"], row["c"]): row for row in scan["counts"]["rows"] }
    assert counts[(0, 0)]["count_at_12"] == 2041
    assert counts[(0, 0)]["count_at_13"] == 2379
    assert counts[(1, 1)]["count_at_12"] == 2
    assert counts[(2, 1)]["first_n"] == 6
    assert counts[(2, 1)]["max_count"] == 1
    assert "0,0" in scan["counts"]["abundant"]
    cycles = scan["cyclemin"]
    assert cycles["n_max"] == N_CYCLEMIN
    assert cycles["landing_count"] == 1
    assert cycles["landings"][0]["n"] == 37
    assert cycles["follows"] == 0
    assert cycles["exact_count"] == 0
    assert scan["length_eleven_census"] is False
    assert scan["z5_cells"] is False
    assert scan["four_even_assembler"] is False
    assert scan["interval_census"] is False


def test_lean_api_without_halt_or_z5():
    lean = lean_api_present()
    assert lean["sorry_free"] is True
    for name in LEAN_THEOREMS:
        assert lean[name] is True, name
    for name in FORBIDDEN_THEOREMS:
        assert lean[f"has_{name}"] is False, name
    assert lean["not_in_paper_barrel"] is True
    assert lean["no_global_termination_theorem"] is True
    assert lean["FloorPower_not_rewritten"] is True


def test_classify_render_and_artifacts():
    from research.juggler_sequence.bunched_short_return import JSON_PATH

    payload = write_artifacts()
    text = render_markdown(payload)
    assert CLASS_PARK in text
    assert "n^2" in text
    assert "last-odd" in text or "last-even" in text
    assert JSON_PATH.is_file()
    data = json.loads(JSON_PATH.read_text(encoding="utf-8"))
    assert data["experiment"] == "juggler_bunched_short_return"
    assert data["decision"]["classification"] == CLASS_PARK
    assert data["anti_overclaim"]["cycles_impossible"] is False
    assert data["engine_control_layer_modified"] is False
    assert dict(ANTI_OVERCLAIM)["global_termination"] is False


def test_dossier_boundary():
    from pathlib import Path

    repo = Path(__file__).resolve().parents[3]
    dossier = (repo / "docs" / "problems" / "juggler_bunched_short_return.md").read_text(
        encoding="utf-8"
    )
    front = (repo / "docs" / "problems" / "juggler_bunched_short_front.md").read_text(
        encoding="utf-8"
    )
    note = (repo / "docs" / "theory" / "juggler_finite_dynamics_note.md").read_text(
        encoding="utf-8"
    )
    assert "## Branch budget" in dossier
    assert "## Decision" in dossier
    assert "PARK" in dossier
    assert "R_{b,c}" in dossier or "R_{b,c}(n)" in dossier
    assert "interval" in dossier.lower()
    assert "juggler_bunched_short_return" in front
    assert "theorem no_cycle_itinerary_length_eleven" not in note
    assert "theorem no_cycleMin_four_even" not in note
    assert "theorem no_juggler_cycle" not in note
