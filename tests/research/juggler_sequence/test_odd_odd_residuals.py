"""Odd-odd residual admissibility. Not an engine-control or halt test."""

from __future__ import annotations

from research.juggler_sequence.odd_odd_residuals import (
    CLASS_COMPLEX,
    CLASS_COUNTER,
    FORBIDDEN_ENGINES,
    HARD_PROBES,
    LEAN_NEW,
    classify,
    continuation_depth,
    lean_api_present,
    odd_odd_starts,
    odd_prefix_defects,
    render_markdown,
    run_probe,
    step_record,
    walk_odd_odd,
)
from research.juggler_sequence.power_itineraries import ANTI_OVERCLAIM, floor_power
from research.juggler_sequence.progress_coverage import is_odd_odd
from research.juggler_sequence.residual_chain import residual_chain


def test_hard_probes_are_odd_odd():
    for n in HARD_PROBES:
        assert is_odd_odd(n)


def test_nine_is_auto_fp_not_persistent():
    row = step_record(9)
    assert row is not None
    assert row["a"] == 2
    assert row["b"] == 1
    assert row["y"] == 11
    assert row["y_odd_odd"] is False
    assert row["persistent"] is False
    assert row["exact_odd_prefix"] is False
    assert row["nonextremal"] is True


def test_thirty_seven_persistent_then_descent():
    chain = walk_odd_odd(37)
    assert chain[0]["x"] == 37
    assert chain[0]["a"] == 4
    assert chain[0]["b"] == 1
    assert chain[0]["y"] == 9317
    assert chain[0]["persistent"] is True
    assert chain[0]["y_odd_odd"] is True
    assert chain[0]["nonextremal"] is True
    assert chain[0]["another_nonextremal_odd_odd"] is True
    assert chain[1]["x"] == 9317
    assert chain[1]["a"] == 3
    assert chain[1]["b"] == 2
    assert chain[1]["y"] == 2233
    assert 2233 < 9317
    assert 2233 > 37
    assert chain[1]["y_odd_odd"] is True
    assert chain[1]["persistent"] is False
    assert chain[1]["y_gt_x"] is False


def test_sixty_nine_persistent_then_odd_odd_descent():
    chain = walk_odd_odd(69)
    assert chain[0]["y"] == 117
    assert chain[0]["persistent"] is True
    assert chain[1]["x"] == 117
    assert chain[1]["y"] == 3
    assert chain[1]["y_odd_odd"] is True
    assert chain[1]["y_gt_x"] is False


def test_seventy_seven_auto_fp_then_odd_odd_landing():
    chain = residual_chain(77)
    assert chain[0]["y"] == 1523
    assert chain[0]["y_odd_odd"] is False
    assert chain[1]["y"] == 243
    assert chain[1]["y_odd_odd"] is True
    assert 243 < 1523
    assert 243 > 77


def test_window_walks_every_odd_odd_start():
    starts = odd_odd_starts()
    assert starts == [3, 5, 9, 25, 33, 35, 37, 39, 43, 45, 49, 53, 55, 59, 69, 73, 75, 77]
    scan = run_probe()
    assert [item["n"] for item in scan["window"]] == starts
    for item in scan["window"]:
        assert item["chain"]
        assert item["chain"][0]["x"] == item["n"]


def test_no_exact_first_odd_prefix_in_window():
    scan = run_probe()
    assert scan["census"]["first_exact_odd_prefix"] == 0
    for item in scan["window"]:
        first = item["chain"][0]
        assert first["exact_odd_prefix"] is False
        assert first["nonextremal"] is True
        assert any(defect > 0 for defect in odd_prefix_defects(first["x"], first["a"]))


def test_successor_exists_after_thirty_seven_but_intervals_grow():
    chain = walk_odd_odd(37)
    assert chain[0]["another_nonextremal_odd_odd"] is True
    assert chain[1]["another_nonextremal_odd_odd"] is False
    assert chain[0]["even_preimage_width"] == 18635
    assert chain[1]["even_preimage_width"] == 44567460015
    assert chain[1]["even_preimage_width"] > chain[0]["even_preimage_width"]
    assert chain[1]["last_odd_cell_width"] > chain[0]["last_odd_cell_width"]


def test_valuation_not_monotone_on_thirty_seven():
    chain = walk_odd_odd(37)
    assert chain[0]["v2_z"] == 2
    assert chain[1]["v2_z"] == 5
    assert chain[2]["v2_z"] == 1


def test_scalar_monotonicity_fails():
    scan = run_probe()
    census = scan["census"]
    assert {"x": 53, "y": 9} in census["y_gt_x_failures"]
    assert {"x": 9317, "y": 2233} in census["y_gt_x_failures"]
    assert census["smallest_y_lt_x"] == {"x": 53, "y": 9}
    assert census["smallest_persist_descent"] == {"x": 69, "mid": 117, "y": 3}


def test_depth_is_horizon_not_L():
    scan = run_probe()
    assert scan["explicit_L"] is False
    assert scan["census"]["search_horizon_is_not_L"] is True
    assert scan["census"]["max_nonextremal_depth"] == 2
    assert continuation_depth(walk_odd_odd(37)) == 2


def test_lean_gate_adds_no_file():
    lean = lean_api_present()
    assert lean["sorry_free"] is True
    assert lean["ResidualStep"] is True
    assert lean["PersistentOddResidual"] is True
    assert lean["OddOddResidual_absent"] is True
    assert lean["no_global_termination_theorem"] is True
    assert lean["no_forbidden_engine"] is True
    assert lean["CycleItinerary_not_rewritten"] is True
    assert lean["FloorPower_not_rewritten"] is True
    assert not LEAN_NEW.is_file()
    from research.juggler_sequence.odd_odd_residuals import RESIDUAL_PATH

    src = RESIDUAL_PATH.read_text(encoding="utf-8")
    assert "sorry" not in src
    assert "admit" not in src
    assert "def ResidualStep" in src
    assert "oddOddAdmissibility" not in src
    for name in FORBIDDEN_ENGINES:
        assert name not in src


def test_classify_complex():
    scan = run_probe()
    lean = lean_api_present()
    decision = classify(scan["census"], lean)
    assert decision["classification"] == CLASS_COMPLEX
    assert CLASS_COUNTER in decision["secondary"]
    text = render_markdown(
        {
            "decision": decision,
            "scan": scan,
            "lean": lean,
            "engine_control_layer_modified": False,
            "algorithm_version": "odd-odd-residual-v1",
            "anti_overclaim": {
                **dict(ANTI_OVERCLAIM),
                "scalar_must_grow": False,
                "search_horizon_is_L": False,
            },
        }
    )
    assert CLASS_COMPLEX in text
    assert "search_horizon_is_L" in text
    assert scan["basin"] == [1]
    assert scan["remainder_dynamics"] is False


def test_committed_artifacts_schema():
    import json

    from research.juggler_sequence.odd_odd_residuals import DATA_DIR, JSON_PATH

    assert JSON_PATH.is_file()
    data = json.loads(JSON_PATH.read_text(encoding="utf-8"))
    assert data["experiment"] == "juggler_odd_odd_residual"
    assert data["engine_control_layer_modified"] is False
    assert data["decision"]["classification"] == CLASS_COMPLEX
    assert data["anti_overclaim"]["scalar_must_grow"] is False
    assert data["anti_overclaim"]["search_horizon_is_L"] is False
    assert data["anti_overclaim"]["global_termination"] is False
    assert data["lean"]["OddOddResidual_absent"] is True
    assert data["scan"]["explicit_L"] is False
    manifest = json.loads((DATA_DIR / "manifest.json").read_text(encoding="utf-8"))
    assert manifest["completed"] is True
    assert manifest["classification"] == CLASS_COMPLEX
    assert (DATA_DIR / "summaries" / "phase0.json").is_file()
    assert (DATA_DIR / "analysis" / "counterexamples.json").is_file()


def test_cli_init_resume_status(tmp_path):
    from research.juggler_sequence.odd_odd_residuals import init, resume, status

    root = tmp_path / "odd_odd_residuals"
    init(root)
    assert (root / "search_config.json").is_file()
    assert status(root)["completed"] is False
    payload = resume(root)
    assert payload is not None
    assert payload["decision"]["classification"] == CLASS_COMPLEX
    assert resume(root) is None
    assert status(root)["completed"] is True


def test_floor_power_unchanged():
    assert floor_power(1) == 1
    assert floor_power(9) == 27
    assert floor_power(37) == 225
    assert floor_power(77) == 675
