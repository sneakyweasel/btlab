"""2-adic landing remainder. Not a termination test."""

from __future__ import annotations

from research.juggler_sequence.landing_valuation import (
    LEAN_THEOREMS,
    LIFT_COUNTEREXAMPLE,
    PE_CHAIN,
    classification_holds,
    compare_populations,
    landing_remainder,
    landing_row,
    landing_valuation,
    lean_api_present,
    v2,
    valuation_census,
)
from research.juggler_sequence.lean_paths import juggler_text
from research.juggler_sequence.power_itineraries import floor_power
from research.juggler_sequence.progress_coverage import is_odd_odd


def test_mod_eight_classification_is_exact():
    for y in (3, 5, 7, 9, 33, 365, 763, 1749):
        row = landing_row(y)
        assert row is not None
        assert row["odd_odd"] == is_odd_odd(y)
        if row["odd_odd"]:
            assert row["rho"] == landing_remainder(y)
            assert row["rho_eq_y_minus_1_mod8"]
            assert row["class_ok"]
            assert classification_holds(y, row["rho"], row["v2"])


def test_y_mod_sixteen_does_not_force_higher_valuation():
    y = LIFT_COUNTEREXAMPLE["y"]
    row = landing_row(y)
    assert row is not None
    assert row["T"] == LIFT_COUNTEREXAMPLE["T"]
    assert row["rho"] == LIFT_COUNTEREXAMPLE["rho"]
    assert row["v2"] == LIFT_COUNTEREXAMPLE["v2"]
    assert row["y_mod16"] == LIFT_COUNTEREXAMPLE["y_mod16"]
    assert landing_valuation(y) == 3


def test_census_obeys_residue_law_and_does_not_predict_next_parity():
    report = valuation_census(n_max=400)
    assert report["odd_odd"] >= 80
    assert report["class_fail"] == 0
    assert report["rho_mod_fail"] == 0
    assert report["exact_squares"] >= 1
    assert report["lift16_v2_three"] >= 1
    assert 1 in report["v2_hist"]
    assert 2 in report["v2_hist"]
    assert any(v >= 3 for v in report["v2_hist"])
    assert report["v2_by_mod8"][3] == {1: report["v2_by_mod8"][3][1]}
    assert report["v2_by_mod8"][5] == {2: report["v2_by_mod8"][5][2]}
    assert report["v2_by_mod8"][7] == {1: report["v2_by_mod8"][7][1]}
    assert set(report["v2_by_mod8"][1]) <= {-1, 3, 4, 5, 6, 7, 8, 9, 10, 11}
    assert report["mixed_next_parity"] >= 3


def test_pe_history_does_not_change_the_valuation_law():
    report = compare_populations(n_max=400)
    pe = report["pe"]
    assert pe["endpoints"] >= 10
    assert pe["class_fail"] == 0
    assert pe["mod8_classes"] == [1, 3, 5, 7]
    assert pe["v2_one"] >= 1
    assert report["pe_only_keys"] == []
    assert pe["next_word_splits_v2"] >= 1
    assert pe["all_v2_one_runs"] >= 1
    assert pe["nondecreasing_runs"] < pe["runs_ge2"]


def test_365_pe_chain_has_valuation_one_and_is_not_monotone():
    xs = [PE_CHAIN["x"]]
    x = PE_CHAIN["x"]
    vals = []
    for _ in range(3):
        x = floor_power(floor_power(floor_power(x)))
        xs.append(x)
        row = landing_row(x)
        assert row is not None
        vals.append(row["v2"])
    assert tuple(xs[1:]) == PE_CHAIN["ys"]
    assert tuple(vals) == PE_CHAIN["v2"]
    assert 1 in vals
    assert vals != sorted(vals)


def test_zero_remainder_is_an_odd_square():
    row = landing_row(9)
    assert row is not None
    assert row["rho"] == 0
    assert v2(0) == -1
    assert row["y_mod8"] == 1


def test_lean_api_and_sorry_free():
    lean = lean_api_present()
    assert lean["sorry_free"]
    text = juggler_text()
    assert "sorry" not in text
    assert "admit" not in text
    for name in LEAN_THEOREMS:
        assert lean[name], name
    assert "import Problems.Juggler.LandingValuation" in text
