"""Predecessor cells for bunched-short last clusters. Not a halt or Z5 test."""

from __future__ import annotations

import json

from research.juggler_sequence.bunched_last_cluster import family_word
from research.juggler_sequence.bunched_short_front import (
    CLASS_PARK,
    FORBIDDEN_THEOREMS,
    LEAN_THEOREMS,
    N_CUTOFF,
    SHORT_PAIRS,
    cell_rank,
    classify,
    classify_suffix,
    even_landing_suffixes,
    known_n12_returns,
    lean_api_present,
    net_expanding,
    net_exponent,
    pred_type,
    render_markdown,
    reroot_row,
    reroot_scan,
    run_probe,
    short_tail,
    write_artifacts,
)
from research.juggler_sequence.power_itineraries import ANTI_OVERCLAIM


def test_short_pairs_and_31_exponent():
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
    assert short_tail(2, 1) == "OOEOE"
    assert net_exponent(3, 1) == (81, 64)
    expanding = [(b, c) for b in range(4) for c in range(2) if net_expanding(b, c)]
    assert expanding == [(3, 1)]
    assert (3, 1) not in SHORT_PAIRS
    assert pred_type(0) == "a0"
    assert pred_type(1) == "a1"
    assert pred_type(2) == "a_ge2"


def test_cell_rank_and_reroot_lemma():
    assert cell_rank(13, 13) == 0
    assert cell_rank(16, 81) == 0
    assert cell_rank(100, 129) == 0
    word = family_word(5, 0, 0)
    assert word == "OOOOOEEE"
    suffixes = even_landing_suffixes(word)
    assert "EEE"[1:] in suffixes or "EE" in suffixes
    row = reroot_row(word)
    assert row["forbidden_count"] == 0
    assert classify_suffix((5, 0, 0)) == "not_excluded_suffix"
    assert classify_suffix((6, 0, 0)) == "last_three_even_bunched"
    assert classify_suffix((4, 0)) == "last_two_even_ee"
    assert classify_suffix((3, 1)) == "last_two_even_eoe"
    scan = reroot_scan()
    assert scan["short_spec_forbidden_total"] == 0
    assert scan["window_forbidden"] == 0
    assert scan["concatenation_unavoidable"] is False


def test_known_returns_are_predecessor_infeasible():
    rows = known_n12_returns()
    assert len(rows) == 18
    assert any(row["y3"] == 129 and row["n"] == 100 for row in rows)
    assert any(row["y3"] == 81 and row["n"] == 16 for row in rows)
    even_n = sum(1 for row in rows if row["n"] % 2 == 0)
    assert even_n == 11


def test_probe_and_classify_park():
    scan = run_probe()
    lean = lean_api_present()
    decision = classify(scan, lean)
    assert decision["classification"] == CLASS_PARK
    assert scan["reroot"]["short_spec_forbidden_total"] == 0
    assert scan["reroot"]["window_forbidden"] == 0
    assert scan["cells"]["missing_31_is_unique_expanding"] is True
    assert scan["cells"]["q_does_not_obstruct_short"] is True
    assert scan["cells"]["overshoots"] == 0
    assert scan["census_a"]["count"] == 18
    assert scan["census_a"]["even_n"] == 11
    assert scan["census_a"]["cyclemin_feasible"] == 0
    assert scan["census_b"]["survivor_count"] == 4
    assert scan["census_b"]["cycle_count"] == 0
    assert scan["census_b"]["shared_geometry"] is False
    assert scan["census_b"]["all_leaks_s_gt_n"] is True
    assert scan["census_b"]["all_leaks_c0"] is True
    assert scan["census_b"]["cluster_count"] == 4
    assert all(row["overflow_eq_s_ge_succ"] for row in scan["census_b"]["leak_geometry"])
    assert scan["length_eleven_census"] is False
    assert scan["z5_cells"] is False
    assert scan["four_even_assembler"] is False
    assert scan["leftover_suffix_retest"] is False
    assert scan["n_cutoff"] == N_CUTOFF


def test_lean_api_without_halt_or_z5():
    lean = lean_api_present()
    assert lean["sorry_free"] is True
    for name in LEAN_THEOREMS:
        assert lean[name] is True, name
    for name in FORBIDDEN_THEOREMS:
        assert lean[f"has_{name}"] is False, name
    assert lean["not_in_paper_barrel"] is True
    assert lean["no_global_termination_theorem"] is True


def test_classify_render_and_artifacts():
    payload = write_artifacts()
    text = render_markdown(payload)
    assert CLASS_PARK in text
    assert "OOOOOEEE" in text
    assert "(3,1)" in text
    from research.juggler_sequence.bunched_short_front import JSON_PATH

    assert JSON_PATH.is_file()
    data = json.loads(JSON_PATH.read_text(encoding="utf-8"))
    assert data["experiment"] == "juggler_bunched_short_front"
    assert data["decision"]["classification"] == CLASS_PARK
    assert data["anti_overclaim"]["cycles_impossible"] is False
    assert data["scan"]["census_a"]["cyclemin_feasible"] == 0
    assert data["scan"]["census_b"]["cycle_count"] == 0
    assert dict(ANTI_OVERCLAIM)["global_termination"] is False


def test_dossier_boundary():
    from pathlib import Path

    repo = Path(__file__).resolve().parents[3]
    dossier = (repo / "docs" / "problems" / "juggler_bunched_short_front.md").read_text(
        encoding="utf-8"
    )
    parked = (repo / "docs" / "problems" / "juggler_bunched_short.md").read_text(
        encoding="utf-8"
    )
    note = (repo / "docs" / "theory" / "juggler_finite_dynamics_note.md").read_text(
        encoding="utf-8"
    )
    assert "## Branch budget" in dossier
    assert "## Decision" in dossier
    assert "PARK" in dossier
    assert "predecessor" in dossier.lower()
    assert "juggler_bunched_short_front" in parked
    assert "theorem no_cycle_itinerary_length_eleven" not in note
    assert "theorem no_cycleMin_four_even" not in note
    assert "theorem no_juggler_cycle" not in note
