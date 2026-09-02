"""Cycle finance inequality. Not a halt test, not a no-cycle-of-any-length test."""

from __future__ import annotations

import json
from pathlib import Path

from research.juggler_sequence.cycle_finance import (
    CLASS_CLOSED,
    CLASS_GREEN,
    CLASS_INCOMPLETE,
    CLASS_PARK,
    ELIAHOU_LEAN_PERIOD,
    ELIAHOU_TABLE_CUTOFF,
    EXISTING_LEAN,
    EXPECTED_LEAN_KILL,
    FORBIDDEN_NEW_API,
    FORBIDDEN_THEOREMS,
    LEAN_FLOOR,
    PUBLISHED_FLOOR,
    TEST_FLOOR,
    adversarial_valley_count,
    census_cross_check,
    classify,
    eliahou_exceptions,
    eliahou_leftover,
    eliahou_packaging,
    eliahou_table_holds,
    finance_rows,
    first_odd_image,
    lean_api_present,
    n_max_from_bound,
    orbit_slack,
    parity_excludes,
    parity_n_max,
    parity_rhs,
    parity_survives_floor,
    prefix_weight_row,
    probe_payload,
    render_markdown,
    sha256_int_list,
    verify_floor,
    weight_excludes,
    weight_rhs,
)

REPO = Path(__file__).resolve().parents[3]


def test_finance_rows_exact_small_values():
    rows = finance_rows(12)
    by_length = {row["L"]: row for row in rows}
    # L=1: o=1, theta=1/3, B=3.6 -> n_max=3.
    assert by_length[1]["o"] == 1
    assert by_length[1]["n_max"] == 3
    # L=3 is the first near-tight length (2^3=8 vs 3^2=9).
    assert by_length[3]["o"] == 2
    assert by_length[3]["record"] is True
    assert by_length[3]["n_max"] == 13
    # L=12: gap 3^8 - 2^12 = 2465.
    assert by_length[12]["o"] == 8
    assert 12 <= by_length[12]["n_max"] <= 15
    # o is always minimal admissible: 3^o > 2^L > 3^(o-1).
    for row in rows:
        assert 3 ** row["o"] > 2 ** row["L"]
        assert 3 ** (row["o"] - 1) <= 2 ** row["L"]


def test_n_max_from_bound_monotone():
    values = [n_max_from_bound(b) for b in (0.1, 3.6, 32.4, 1000.0)]
    assert values == sorted(values)
    assert values[0] == 1
    assert values[1] >= 3


def test_census_cross_check_matches_lean_census():
    census = census_cross_check(finance_rows(8))
    assert census["matches_expected"] is True
    assert tuple(census["killed_by_lean_floor"]) == EXPECTED_LEAN_KILL
    assert tuple(census["census_only_lengths"]) == (3, 6)
    for length in census["killed_by_lean_floor"]:
        assert census["n_max_by_length"][length] <= LEAN_FLOOR


def test_verify_floor_descent_induction():
    result = verify_floor(300, progress=False, workers=1)
    assert result["verified"] is True
    assert result["failures"] == []
    assert result["max_first_passage_steps"] >= 1
    assert result["workers"] == 1


def test_orbit_slack_bounds_hold():
    for seed in (25, 37, 365):
        row = orbit_slack(seed)
        assert row["step_bound_ok"] is True
        assert row["defect_bound_ok"] is True
        assert row["reached_one"] is True
        assert row["identity_rel_err"] < 1e-9
        assert row["worst_margin"] is None or row["worst_margin"] > 0.0
        assert row["tightness"] is None or row["tightness"] < 1.0


def test_probe_and_classify_vocabulary():
    payload = probe_payload()
    assert payload["experiment"] == "juggler_cycle_finance"
    assert payload["engine_control_layer_modified"] is False
    assert payload["decision"]["classification"] in {
        CLASS_GREEN,
        CLASS_PARK,
        CLASS_CLOSED,
        CLASS_INCOMPLETE,
    }
    assert payload["decision"]["classification"] not in {
        CLASS_CLOSED,
        CLASS_INCOMPLETE,
    }
    assert payload["anti_overclaim"]["halt_theorem"] is False
    assert payload["anti_overclaim"]["no_cycle_all_lengths"] is False
    assert payload["scan"]["eliahou"]["table_holds"] is True
    assert payload["scan"]["eliahou"]["lean_period"] == ELIAHOU_LEAN_PERIOD
    text = render_markdown(payload)
    assert "Eliahou leftover" in text
    assert "Not a halt theorem" in text
    lean = lean_api_present()
    assert classify(payload["scan"], lean)["classification"] == payload[
        "decision"
    ]["classification"]


def test_lean_api_finance_layer():
    lean = lean_api_present()
    assert lean["sorry_free"] is True
    for name in EXISTING_LEAN:
        assert lean[name] is True, name
    for name in FORBIDDEN_THEOREMS:
        assert lean[f"has_{name}"] is False, name
    for name in FORBIDDEN_NEW_API:
        assert lean[f"has_api_{name}"] is False, name
    assert lean["cycle_finance_present"] is True
    assert lean["no_extra_finance_file"] is True
    assert lean["cycle_finance_in_paper_barrel"] is True
    assert lean["not_in_paper_barrel"] is True


def test_science_summary_is_green():
    summary = json.loads(
        (
            REPO / "data" / "research" / "juggler" / "cycle_finance" / "summary.json"
        ).read_text(encoding="utf-8")
    )
    assert summary["classification"] == CLASS_GREEN
    assert summary["floor_verified"] is True
    assert summary["floor"] == 2_000_000
    assert summary["contiguous_prefix"] >= 25780
    assert summary["exception_count"] == 166


def test_eliahou_leftover_covers_survivors():
    rows = finance_rows(400)
    floor = TEST_FLOOR
    exceptions = eliahou_exceptions(rows, floor)
    leftover = eliahou_packaging(rows, floor, cutoff=400)
    assert leftover["table_holds"] is True
    assert leftover["lean_period"] == ELIAHOU_LEAN_PERIOD
    assert eliahou_table_holds(rows, floor, exceptions, cutoff=400)
    for row in rows:
        length = row["L"]
        survives = row["n_max"] > floor
        if survives:
            assert eliahou_leftover(length, exceptions, cutoff=400)
        if length < 400 and length != ELIAHOU_LEAN_PERIOD and length not in exceptions:
            assert survives is False


def test_eliahou_instance_matches_science_table():
    exceptions = json.loads(
        (
            REPO / "data" / "research" / "juggler" / "cycle_finance" / "exceptions.json"
        ).read_text(encoding="utf-8")
    )
    published = next(item for item in exceptions if item["floor"] == 1_000_000)
    science = next(item for item in exceptions if item["floor"] == 2_000_000)
    published_lengths = published["lengths"]
    lengths = science["lengths"]
    assert published["count"] == 397
    assert published["first_exception"] == 1054
    assert published["contiguous_prefix"] == 1053
    assert science["count"] == 166
    assert science["first_exception"] == 25781
    assert science["contiguous_prefix"] == 25780
    assert science["truncated"] is False
    assert ELIAHOU_LEAN_PERIOD not in lengths
    assert 19 not in lengths
    assert 1054 not in lengths
    assert 25781 in lengths
    assert 50508 in lengths
    assert eliahou_leftover(ELIAHOU_LEAN_PERIOD, lengths)
    assert eliahou_leftover(1054, published_lengths)
    assert not eliahou_leftover(1054, lengths)
    assert eliahou_leftover(25781, lengths)
    assert eliahou_leftover(ELIAHOU_TABLE_CUTOFF, lengths)
    assert not eliahou_leftover(19, lengths)
    assert not eliahou_leftover(30, lengths)
    assert not eliahou_leftover(38, lengths)
    assert not eliahou_leftover(57, lengths)
    assert not eliahou_leftover(76, lengths)
    assert not eliahou_leftover(1053, lengths)
    assert not eliahou_leftover(25780, lengths)


def test_parity_length_only_ingredients():
    assert first_odd_image(12) == 41
    assert first_odd_image(10**6 + 1) == 1_000_001_500
    assert adversarial_valley_count(1054, 665) == 389
    assert adversarial_valley_count(25781, 16266) == 9515
    row = next(item for item in finance_rows(1054) if item["L"] == 1054)
    assert row["o"] == 665
    assert parity_n_max(1054, 665, row["theta"]) == 788014
    assert parity_excludes(1054, 665, row["theta"], PUBLISHED_FLOOR)
    assert not parity_survives_floor(1054, 665, row["theta"], PUBLISHED_FLOOR)


def test_parity_table_pins_first_survivor():
    payload = json.loads(
        (
            REPO / "data" / "research" / "juggler" / "cycle_finance"
            / "exceptions_parity.json"
        ).read_text(encoding="utf-8")
    )
    assert payload["floor"] == PUBLISHED_FLOOR
    assert payload["first_exception"] == 25781
    assert payload["contiguous_prefix"] == 25780
    assert payload["count"] == 141
    assert payload["uncertain_count"] == 0
    assert payload["uncertain"] == []
    assert payload["certified_first_survivor_25781"] is True
    assert payload["lengths"][0] == 25781
    assert payload["lengths"][-1] == 99561
    assert 1054 not in payload["lengths"]
    assert 25780 not in payload["lengths"]
    assert payload["spotlight"]["1054"]["n_max"] == 788014
    assert payload["spotlight"]["25781"]["n_max"] == 26254995
    assert payload["sha256_lengths"] == (
        "dd71aa1527656ba51cb031bafa5497f7bfdbbc43151ffba2c595793326bf7944"
    )
    assert sha256_int_list(payload["lengths"]) == payload["sha256_lengths"]


PREFIX_WEIGHT_LATER_VALLEY_KILLS = [
    81643,
    82697,
    83751,
    84805,
    85859,
    86913,
    87967,
    89021,
    90075,
    91129,
    92183,
    93237,
    94291,
    95345,
    96399,
    97453,
    98507,
    99561,
]


def test_prefix_weight_25781_does_not_exclude():
    row = prefix_weight_row(25781)
    assert row["o"] == 16266
    assert row["e"] == 9515
    assert not row["parity_excludes"]
    assert not row["weight_P_ge_1_excludes"]
    assert not row["weight_later_valley_9_8_excludes"]
    assert row["weight_P_ge_1_ge_parity"]
    assert row["weight_P_ge_1_rhs"] >= row["parity_rhs"]
    start = PUBLISHED_FLOOR + 1
    assert weight_rhs(start, 25781, 16266, later_valley_p=1.0) >= parity_rhs(
        start, 25781, 16266
    )
    assert not weight_excludes(
        25781, 16266, row["theta"], PUBLISHED_FLOOR, later_valley_p=1.0
    )
    assert not weight_excludes(
        25781, 16266, row["theta"], PUBLISHED_FLOOR, later_valley_p=9.0 / 8.0
    )


def test_prefix_weight_scan_pins_no_certified_exclusion():
    payload = json.loads(
        (
            REPO / "data" / "research" / "juggler" / "cycle_finance"
            / "prefix_weights.json"
        ).read_text(encoding="utf-8")
    )
    assert payload["leftover_count"] == 141
    assert payload["floor"] == PUBLISHED_FLOOR
    assert payload["n"] == PUBLISHED_FLOOR + 1
    assert payload["killed_by_parity"] == []
    assert payload["killed_by_weight_P_ge_1"] == []
    assert payload["weight_P_ge_1_weaker_failures"] == []
    assert payload["certified_no_leftover_excluded"] is True
    assert payload["killed_by_weight_later_valley_9_8"] == (
        PREFIX_WEIGHT_LATER_VALLEY_KILLS
    )
    assert payload["no_leftover_excluded"] is False
    spot = payload["spotlight_25781"]
    assert spot["L"] == 25781
    assert not spot["parity_excludes"]
    assert not spot["weight_P_ge_1_excludes"]
    assert not spot["weight_later_valley_9_8_excludes"]
    assert spot["weight_P_ge_1_ge_parity"]
    assert 25781 not in payload["killed_by_weight_later_valley_9_8"]
    assert PREFIX_WEIGHT_LATER_VALLEY_KILLS == [
        81643 + 1054 * k for k in range(18)
    ]


def test_crude_table_unchanged_at_published_floor():
    exceptions = json.loads(
        (
            REPO / "data" / "research" / "juggler" / "cycle_finance"
            / "exceptions.json"
        ).read_text(encoding="utf-8")
    )
    published = next(item for item in exceptions if item["floor"] == 1_000_000)
    assert published["count"] == 397
    assert published["first_exception"] == 1054
    assert published["contiguous_prefix"] == 1053


def test_dossier_boundary():
    dossier = (
        REPO / "docs" / "problems" / "juggler_cycle_finance.md"
    ).read_text(encoding="utf-8")
    note = (
        REPO / "docs" / "theory" / "juggler_cycle_finance_note.md"
    ).read_text(encoding="utf-8")
    paper = (REPO / "formal" / "Problems" / "JugglerPaper.lean").read_text(
        encoding="utf-8"
    )
    assert "## Branch budget" in dossier
    assert "## Decision" in dossier
    assert "## Publication assessment" in dossier
    assert "**PROMOTE**" in dossier
    assert "cycle_itinerary_formally_expanding" in dossier
    assert "simons-de-weger-2005-collatz-m-cycles" in dossier
    assert "cycle_itinerary_eliahou_leftover" in dossier
    assert "cycle_itinerary_length_eighty_four_m_ge_three_or_ge_eighty_five" in dossier
    assert "juggler_cycle_finance_note.md" in dossier
    assert "theorem no_cycle_itinerary_any_length" not in dossier
    assert "import Problems.Juggler.CycleFinance" in paper
    assert "import Problems.Juggler.CycleHeightFinance" not in paper
    assert "cycleMin_finance" in note
    assert "Length-only parity finance" in dossier
    assert "Prefix-weight comparison" in dossier
    assert "prefix_weights.json" in dossier
    assert "budget_opt.json" in dossier
    assert "run_extremum.json" in dossier
    assert "juggler_cycle_prefix_weight_leftover_killer" in note
    assert "juggler_cycle_run_extremum_leftover_killer" in note
    assert "juggler_cycle_fourier_leftover_killer" in note
    assert "juggler_cycle_closure_leftover_killer" in note
    assert "juggler_cycle_conditioned_closure_leftover_killer" in note
    assert "juggler_cycle_ordered_excursion_leftover_killer" in note
    assert "juggler_cycle_defect_correlation_leftover_killer" in note
    assert "juggler_cycle_loss_persistence_leftover_killer" in note
    assert "juggler_cycle_budget_opt.md" in note
    assert "25780" in note
    assert "cycle_itinerary_length_eighty_four_or_ge_eighty_five" in note
    assert "cycle_itinerary_length_eighty_four_m_ge_three_or_ge_eighty_five" in note
    assert "not a halt theorem" in note.lower()
    assert "JugglerPaper" in note or "Paper A" in note
    assert "not a second manuscript" in note or "absorbed into Paper A" in note
    assert "cycleMin_finance_inv_sum" in paper
    assert "4.4c" in paper


def test_paper_finance_hierarchy():
    text = (
        REPO / "docs" / "theory" / "juggler_finite_dynamics_note.md"
    ).read_text(encoding="utf-8")
    assert "**Hierarchy of forms.**" in text
    assert "cycleMin_finance_inv_sum" in text
    assert "**Corollary 4.4c (inv-sum).**" in text
    assert "not an artifact of that majorant" in text
    assert "6/5 parity form" not in text
    assert "in the conservative $6/5$ form" not in text
    assert r"in the conservative \(6/5\) form" not in text
    assert "**Roles.**" in text
    assert "To the best of our knowledge" in text
    assert "systematic literature search remains" not in text
    assert "The computation supplies the endpoint" in text
