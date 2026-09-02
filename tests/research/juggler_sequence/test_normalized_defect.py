"""Normalized relative slack. Not a termination test."""

from __future__ import annotations

from research.juggler_sequence.global_defect import (
    follows_itinerary,
    global_defect,
    image_after,
    itinerary_word,
)
from research.juggler_sequence.lean_paths import juggler_text
from research.juggler_sequence.normalized_defect import (
    LEAN_THEOREMS,
    concat_product_holds,
    defect_ratio,
    identity_census,
    lean_api_present,
    odd_even_word,
    one_plus_slack,
    one_step_holds,
    persistent_census,
    prefix_ratio_census,
    slack_den,
    slack_num,
    surplus_vs_image_scan,
)


def test_identity_and_concat_on_short_words():
    report = identity_census(n_max=40, k_max=4)
    assert report["identity_fail"] == 0
    assert report["concat_fail"] == 0
    assert report["step_fail"] == 0
    assert report["q_mono_fail"] == 0
    assert report["checked"] > 0


def test_one_plus_slack_is_the_identity_ratio():
    n, word = 13, itinerary_word(13, 4)
    num, den = one_plus_slack(n, word)
    assert num == den + global_defect(n, word)
    assert concat_product_holds(n, word[:2], word[2:])
    assert one_step_holds(n, word[:-1], word[-1])


def test_surplus_ratio_is_the_endpoint_comparison():
    report = surplus_vs_image_scan(n_max=60, k_max=4)
    assert report["fail"] == 0
    assert report["checked"] > 0
    assert defect_ratio(9, "O") is None or defect_ratio(9, "O")[0] == 0
    assert follows_itinerary(69, "OOE")
    pair = defect_ratio(69, "OOE")
    assert pair is not None
    assert pair[0] < pair[1]
    assert image_after(69, "OOE") > 69


def test_persistent_window_has_small_R_and_q_reset():
    report = persistent_census()
    assert report["skipped"] == 0
    assert report["persistent_rows"] >= 2
    assert report["min_persistent_R"] is not None
    assert 0 < report["min_persistent_R"] < 0.02
    assert report["min_persistent_R_row"]["x"] == 69
    assert report["min_persistent_R_row"]["word"] == "OOE"
    assert report["q_decreases"] >= 1
    assert report["min_eta_odd_odd"] == 0.0


def test_running_R_can_decrease_when_surplus_grows():
    report = prefix_ratio_census(n_max=20, k_max=6)
    assert report["decreases"] >= 1
    assert any(row["R_uv"] < row["R_u"] for row in report["examples"])


def test_residual_block_word_matches_excursion():
    word = odd_even_word(2, 1)
    assert word == "OOE"
    assert slack_num(69, word) == 69 ** (3 ** 2)
    assert slack_den(69, word) == image_after(69, word) ** (2 ** 3)


def test_lean_api_and_sorry_free():
    lean = lean_api_present()
    assert lean["sorry_free"]
    text = juggler_text()
    assert "sorry" not in text
    assert "admit" not in text
    for name in LEAN_THEOREMS:
        assert lean[name], name
    assert "import Problems.Juggler.NormalizedDefect" in text
