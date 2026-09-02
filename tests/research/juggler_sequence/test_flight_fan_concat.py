"""Fast checks for the fan-block concatenability glue probe."""

from __future__ import annotations

import json

from research.juggler_sequence.flight_divergent_structure import trajectory
from research.juggler_sequence.flight_fan_concat import (
    CLASS_NO_GLUE,
    JSON_PATH,
    classify_orbit,
    hug_letters,
)
from research.juggler_sequence.flight_return_quantization import (
    LOG2_3,
    return_set,
    theta_p,
)


def test_hug19_is_prefix_min_positive_defect() -> None:
    word = hug_letters(19)
    assert word == "OOEOOEOOEOEOOEOOEOE"
    assert word.count("O") == 12
    assert abs(theta_p(19) - (12 * LOG2_3 - 19)) < 1e-12
    assert 0.0195 < theta_p(19) < 0.0196


def test_r05_starts_at_nineteen() -> None:
    assert return_set(250, 0.05)[:2] == [19, 38]


def test_classify_orbit_small_has_no_glue() -> None:
    r05 = frozenset(return_set(250, 0.05))
    row = classify_orbit(trajectory(37), r05)
    for event in row["events"]:
        assert event["glue_19_to_19"] is False
        assert event["glue_19_to_r05"] is False
        if event["p"] == 38:
            assert event["factors_19_19"] is False


def test_artifact_certifies_no_glue() -> None:
    summary = json.loads(JSON_PATH.read_text(encoding="utf-8"))
    assert summary["classification"] == CLASS_NO_GLUE
    assert summary["hug19"] == "OOEOOEOOEOEOOEOOEOE"
    wt = summary["window"]["tally"]
    assert wt["n19"] == 44
    assert wt["n38"] == 7
    assert wt["hug19"] == 0
    assert wt["hug38"] == 0
    assert wt["odd_counts_19"] == [12]
    assert wt["odd_counts_38"] == [24]
    assert wt["glue_19_to_19"] == 0
    assert wt["glue_19_to_38"] == 0
    assert wt["glue_19_to_r05"] == 0
    assert wt["factors_19_19"] == 0
    assert wt["end_odd_19"] == 17
    assert wt["tail_record_19"] == 44
    assert wt["next_len_zero_19"] == 27
    assert wt["next_len_ge19_19"] == 1
    assert wt["min_hamming_19"] == 2
    assert wt["long_tails_19"] == [{"n": 761, "next_segment_len": 41}]
    ft = summary["flyers"]["tally"]
    assert ft["n19"] == 8
    assert ft["n38"] == 6
    assert ft["glue_19_to_19"] == 0
    assert ft["factors_19_19"] == 0
    assert ft["next_len_ge19_19"] == 1
    assert ft["long_tails_19"] == [{"n": 1245741, "next_segment_len": 118}]
    anti = summary["anti_overclaim"]
    assert anti["halt_theorem"] is False
    assert anti["divergence_excluded"] is False
    assert anti["infinite_fan_sequence_constructed"] is False
    assert anti["paper_a_modified"] is False
    assert anti["n_window_raised"] is False
    assert anti["cf_fan_census"] is False
