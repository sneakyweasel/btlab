"""Prefix-NC arithmetic admissibility. Not an engine-control or halt test."""

from __future__ import annotations

from research.juggler_sequence.compensated_contraction import follows_itinerary
from research.juggler_sequence.equality_language import is_monochrome
from research.juggler_sequence.near_extremal_prefixes import prefix_noncontracting
from research.juggler_sequence.power_itineraries import ANTI_OVERCLAIM, floor_power
from research.juggler_sequence.prefix_nc_admissibility import (
    CLASS_COMPLEX,
    FORBIDDEN_ENGINES,
    KNOWN_WITNESSES,
    LEAN_NEW,
    Ival,
    classify,
    lean_api_present,
    mixed_prefix_nc,
    pullback_word,
    render_markdown,
    run_probe,
    word_payload,
)


def test_ooe_fiber_of_six_is_five():
    back = pullback_word("OOE", Ival(6, 6, 0))
    assert back["empty"] is False
    assert back["truncated"] is False
    assert back["min_start"] == 5
    assert back["max_start"] == 5
    assert follows_itinerary(5, "OOE")


def test_known_witnesses_realize_mixed_prefix_nc():
    for word, n in KNOWN_WITNESSES:
        assert prefix_noncontracting(word)
        assert not is_monochrome(word)
        assert n is not None
        assert follows_itinerary(n, word)


def test_thirty_seven_and_one_seventy_three():
    assert follows_itinerary(37, "OOOOEOOOEE")
    assert follows_itinerary(173, "OOEOOOOOOO")
    assert follows_itinerary(2127, "OOOOEOOOOEE")


def test_all_mixed_k8_realized_in_forward_window():
    scan = run_probe()
    assert scan["census"]["mixed_count"] == 43
    assert scan["census"]["realized_forward"] == 43
    assert scan["census"]["unrealized_in_forward"] == 0
    assert scan["census"]["unrealizable_mixed"] is False
    assert scan["explicit_L"] is False
    assert scan["residual_step_extended"] is False
    assert len(mixed_prefix_nc()) == 43


def test_empty_small_image_is_not_unrealizable():
    scan = run_probe()
    assert scan["census"]["empty_over_image"] >= 1
    assert scan["census"]["empty_law"] is False
    row = word_payload("OOEOOOOOOO", Ival(1, 24, None), known_n=173)
    assert row["empty_over_image"] is True
    assert row["realizable"] is True
    assert row["minimum_start"] == 173


def test_lean_gate_adds_no_file():
    lean = lean_api_present()
    assert lean["sorry_free"] is True
    assert lean["PrefixNCAdmissibility_absent"] is True
    assert lean["floorPower_odd_eq_iff_cube_interval"] is True
    assert lean["odd_preimage_unique"] is True
    assert lean["ResidualStep_not_extended"] is True
    assert lean["no_global_termination_theorem"] is True
    assert not LEAN_NEW.is_file()
    from research.juggler_sequence.prefix_nc_admissibility import RESIDUAL_PATH

    src = RESIDUAL_PATH.read_text(encoding="utf-8")
    assert "sorry" not in src
    assert "admit" not in src
    assert "prefix_nc_admissible" not in src
    assert "escape_admissible" not in src
    for name in FORBIDDEN_ENGINES:
        if name == "ResidualStep":
            continue
        assert name not in src


def test_classify_complex():
    scan = run_probe()
    lean = lean_api_present()
    decision = classify(scan, lean)
    assert decision["classification"] == CLASS_COMPLEX
    text = render_markdown(
        {
            "decision": decision,
            "scan": scan,
            "lean": lean,
            "engine_control_layer_modified": False,
            "algorithm_version": "prefix-nc-admissibility-v1",
            "anti_overclaim": {
                **dict(ANTI_OVERCLAIM),
                "search_horizon_is_L": False,
                "prefix_nc_words_unrealizable": False,
            },
        }
    )
    assert CLASS_COMPLEX in text
    assert "search_horizon_is_L" in text
    assert scan["basin"] == [1]


def test_committed_artifacts_schema():
    import json

    from research.juggler_sequence.prefix_nc_admissibility import DATA_DIR, JSON_PATH

    assert JSON_PATH.is_file()
    data = json.loads(JSON_PATH.read_text(encoding="utf-8"))
    assert data["experiment"] == "juggler_prefix_nc_admissibility"
    assert data["engine_control_layer_modified"] is False
    assert data["decision"]["classification"] == CLASS_COMPLEX
    assert data["anti_overclaim"]["search_horizon_is_L"] is False
    assert data["anti_overclaim"]["global_termination"] is False
    assert data["lean"]["PrefixNCAdmissibility_absent"] is True
    assert data["scan"]["explicit_L"] is False
    assert data["scan"]["residual_step_extended"] is False
    manifest = json.loads((DATA_DIR / "manifest.json").read_text(encoding="utf-8"))
    assert manifest["completed"] is True
    assert manifest["classification"] == CLASS_COMPLEX
    assert (DATA_DIR / "summaries" / "phase0.json").is_file()
    assert (DATA_DIR / "words" / "OOOOEOOOEE.json").is_file()


def test_cli_init_resume_status(tmp_path):
    from research.juggler_sequence.prefix_nc_admissibility import init, resume, status

    root = tmp_path / "prefix_nc_admissibility"
    init(root)
    assert (root / "config.json").is_file()
    assert status(root)["completed"] is False
    payload = resume(root)
    assert payload is not None
    assert payload["decision"]["classification"] == CLASS_COMPLEX
    assert resume(root) is None
    assert status(root)["completed"] is True


def test_floor_power_unchanged():
    assert floor_power(1) == 1
    assert floor_power(5) == 11
    assert floor_power(37) == 225
