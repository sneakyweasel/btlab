"""Descent-floor sensitivity. Not a halt test."""

from __future__ import annotations

from research.juggler_sequence.cycle_budget_opt import budget_n_max
from research.juggler_sequence.cycle_finance import (
    BIT_CAP,
    EPS_CONST,
    PUBLISHED_FLOOR,
    o_min_and_theta,
    parity_excludes,
    parity_n_max,
    verify_floor,
)
from research.juggler_sequence.cycle_floor_sensitivity import (
    BASELINE_PREFIX,
    classify,
    recompute_period_bound,
    scan_layer,
    spotlight_thresholds,
    verify_floor_certified,
)


def test_bit_cap_is_at_least_one_hundred_million():
    assert BIT_CAP >= 100_000_000


def test_published_parity_cutoff_is_25780():
    scan = scan_layer(PUBLISHED_FLOOR, l_max=30_000, layer="parity")
    assert scan["contiguous_prefix"] == BASELINE_PREFIX
    assert scan["first_exception"] == 25781
    assert scan["uncertain_count"] == 0


def test_parity_n_max_25781_matches_implemented_table():
    odd_count, theta = o_min_and_theta(25781)
    assert parity_n_max(25781, odd_count, theta) == 26_254_995
    assert not parity_excludes(25781, odd_count, theta, PUBLISHED_FLOOR)
    assert parity_excludes(25781, odd_count, theta, 26_254_995)


def test_runpack_does_not_kill_25781_at_published_floor():
    odd_count, theta = o_min_and_theta(25781)
    assert budget_n_max(25781, odd_count, theta, const=EPS_CONST) > PUBLISHED_FLOOR


def test_spotlight_separates_layers():
    rows = {row["L"]: row for row in spotlight_thresholds((25781, 50508))}
    left = rows[25781]
    assert left["n_max_parity_1"] < left["n_max_parity_6_5"] < left["n_max_crude_6_5"]
    assert left["n_max_runpack_6_5"] <= left["n_max_parity_6_5"]
    assert rows[50508]["n_max_parity_6_5"] > left["n_max_parity_6_5"]


def test_verify_floor_certified_small_window(tmp_path):
    cert = verify_floor_certified(
        300,
        progress=False,
        workers=1,
        resume=False,
        out_dir=tmp_path,
    )
    assert cert["verified"] is True
    assert cert["N0"] == 300
    assert cert["starting_values"] == 300
    assert cert["odds_walked"] == 149
    assert cert["total_first_passage_steps"] >= 1
    assert cert["max_stopping_time"] >= 1
    assert cert["exact_integer"] is True
    assert cert["floating_point_used_for_certification"] is False
    assert cert["halt_theorem"] is False
    assert len(cert["sha256_chunks"]) == 64
    assert (tmp_path / "certificate.json").is_file()
    baseline = verify_floor(300, progress=False, workers=1)
    assert baseline["verified"] is True
    assert baseline["bit_cap"] >= 100_000_000


def test_ten_million_does_not_raise_the_parity_cutoff():
    scan = scan_layer(10**7, l_max=30_000, layer="parity")
    assert scan["contiguous_prefix"] == BASELINE_PREFIX
    assert scan["first_exception"] == 25781


def test_parity_threshold_of_25781_jumps_to_50507():
    scan = scan_layer(26_254_995, l_max=51_000, layer="parity")
    assert scan["contiguous_prefix"] == 50507
    assert scan["first_exception"] == 50508
    assert scan["uncertain_count"] == 0


def test_one_hundred_million_still_stops_at_50507():
    scan = scan_layer(10**8, l_max=51_000, layer="parity")
    assert scan["contiguous_prefix"] == 50507
    assert scan["first_exception"] == 50508


def test_recompute_period_bound_at_published_floor():
    bound = recompute_period_bound(PUBLISHED_FLOOR, l_max=30_000)
    assert bound["L_star"] == 25780
    assert bound["first_survivor"] == 25781
    assert bound["not_a_termination_proof"] is True


def test_walk_until_descent_small_odd_is_exact():
    from research.juggler_sequence.cycle_floor_hard_seeds import walk_until_descent

    row = walk_until_descent(25, bit_cap=10_000, progress_every=0)
    assert row["ok"] is True
    assert row["exact_integer"] is True
    assert row["floating_point_used"] is False
    assert row["landing"] < 25
    assert row["steps"] >= 1


def test_committed_certificate_is_verified_at_26254995():
    import json
    from pathlib import Path

    base = Path("data/research/juggler/cycle_finance/floor_verify/N26254995")
    cert = json.loads((base / "certificate.json").read_text(encoding="utf-8"))
    assert cert["N0"] == 26_254_995
    assert cert["verified"] is True
    assert cert["step_failures"] == []
    assert cert["bit_failures"] == []
    assert cert["other_failures"] == []
    assert cert["unresolved"] == []
    assert cert["odds_walked"] == 13_127_497
    assert cert["exact_integer"] is True
    assert cert["floating_point_used_for_certification"] is False
    assert cert["halt_theorem"] is False
    resolved = {row["n"] for row in cert["hard_seed_resolutions"]}
    assert resolved == {7_110_201, 13_184_021, 13_782_577}
    assert all(row["ok"] for row in cert["hard_seed_resolutions"])
    assert cert["max_bits"] == 298_912_128
    assert cert["max_bits_seed"] == 7_110_201


def test_committed_certificate_is_verified_at_350000000():
    import json
    from pathlib import Path

    base = Path("data/research/juggler/cycle_finance/floor_verify/N350000000")
    cert = json.loads((base / "certificate.json").read_text(encoding="utf-8"))
    assert cert["N0"] == 350_000_000
    assert cert["n_from"] == 162_849_449
    assert cert["verified"] is True
    assert cert["step_failures"] == []
    assert cert["bit_failures"] == []
    assert cert["other_failures"] == []
    assert cert["unresolved"] == []
    assert cert["chunk_count"] == 749
    assert cert["odds_walked"] == 93_575_276
    assert cert["exact_integer"] is True
    assert cert["floating_point_used_for_certification"] is False
    assert cert["halt_theorem"] is False
    assert cert["no_cycle_all_lengths"] is False
    resolved = {row["n"] for row in cert["hard_seed_resolutions"]}
    assert resolved == {172_376_627, 240_154_767}
    assert all(row["ok"] for row in cert["hard_seed_resolutions"])
    assert cert["max_stopping_time"] == 466
    assert cert["hardest_seed"] == 198_424_189
    assert cert["max_bits"] == 1_493_770_145
    assert cert["max_bits_seed"] == 172_376_627
    assert cert["bit_cap"] == 3_000_000_000
    assert (
        cert["sha256_chunks"]
        == "c57f5ccc9bce980f478dafec00c449050a5e217a4f0f3e100916c41dacbe7472"
    )
    assert (
        cert["sha256_resolved_seeds"]
        == "ea4ab9b18e76c6f45e114071c45bf6ce3cf271a59d25ce1c8145ba7402b15fe7"
    )


def test_committed_period_bound_is_50507():
    import json
    from pathlib import Path

    summary = json.loads(
        Path(
            "data/research/juggler/cycle_finance/floor_sensitivity/summary.json"
        ).read_text(encoding="utf-8")
    )
    bound = summary["period_bound"]
    assert bound["floor"] == 26_254_995
    assert bound["L_star"] == 50_507
    assert bound["first_survivor"] == 50_508
    assert bound["parity_survivors"] == 19
    assert bound["not_a_termination_proof"] is True
    assert summary["certificate"]["verified"] is True


def test_classify_asks_to_compute_before_a_verified_jump():
    table = {
        "cheapest_floor_with_gain": {
            "floor": 26_254_995,
            "L_max": 50507,
            "gain_over_25780": 24727,
        }
    }
    decision = classify(table, None)
    assert decision["recommendation"] == "COMPUTE FURTHER"
    assert "DESCENT_FLOOR" in decision["classification"]
