"""The elementary ladder is downstream-inert past V_5.

The load-bearing test is :func:`test_generic_rung_reproduces_the_audited_coefficients`.
Everything else in this module reads off a generic formula for ``V_k``; if that
formula did not reproduce the hand-audited coefficients of ``V_2 .. V_6``, the
whole report would be about a different family.
"""

from __future__ import annotations

import pytest

from research.juggler_sequence.fate_contagion import RECURSIONS, lambda_root
from research.juggler_sequence.vk_ladder_ceiling import (
    AUDITED_MAX_K,
    CENSUS_RESOLUTION,
    continuous_consumer,
    downstream_constants,
    family_limit_by_series,
    family_limit_closed_form,
    geometric_ratio,
    ladder_report,
    ladder_rows,
    last_effective_rung,
    vk_recursion,
    vk_term,
)

AUDITED = {
    3: "block_third_plus_oeoee_v3",
    4: "block_third_plus_oeoee_v4",
    5: "block_third_plus_oeoee_v5",
    6: "block_third_plus_oeoee_v6",
}


@pytest.mark.parametrize("k,name", sorted(AUDITED.items()))
def test_generic_rung_reproduces_the_audited_coefficients(k: int, name: str) -> None:
    """``3^-(k+1)`` at ``(1/2)(3/4)^k`` is the coefficient the notes audited."""

    generic = vk_recursion(k)
    official = RECURSIONS[name]
    assert len(generic) == len(official)
    for (c_g, e_g), (c_o, e_o) in zip(generic, official):
        assert c_g == pytest.approx(c_o, rel=1e-12)
        assert e_g == pytest.approx(e_o, rel=1e-12)


def test_v2_starts_the_family_and_v1_is_rejected() -> None:
    assert vk_term(2) == pytest.approx((1.0 / 27.0, 9.0 / 32.0), rel=1e-12)
    with pytest.raises(ValueError):
        vk_term(1)


def test_closed_form_limit_agrees_with_the_summed_series() -> None:
    """Theorem 5's collapse ``x + y/3 = 1`` against the geometric tail, summed."""

    assert family_limit_closed_form() == pytest.approx(family_limit_by_series(), abs=1e-12)
    assert family_limit_closed_form() == pytest.approx(0.4927, abs=5e-5)


def test_limit_is_above_every_truncation_but_only_just() -> None:
    lam_inf = family_limit_closed_form()
    rows = ladder_rows(12)
    assert all(row["lambda"] < lam_inf for row in rows)
    at_audited = next(r for r in rows if r["k"] == AUDITED_MAX_K)
    # the entire remaining infinite ladder is worth under 1e-4 in lambda
    assert 0.0 < lam_inf - at_audited["lambda"] < 1e-4


def test_residual_shrinks_by_the_predicted_geometric_ratio() -> None:
    geom = geometric_ratio()
    assert geom["settled_ratio"] == pytest.approx(geom["predicted_ratio_y_over_3"], rel=1e-5)
    # read where the gap is still above the double-precision floor, not at k_max
    assert geom["settled_ratio_read_at_k"] < 24


def test_last_effective_rung_is_v5_and_v4_still_differs() -> None:
    """V_5 reaches the family's constants; V_4 does not.  So V_6 bought nothing."""

    k = last_effective_rung()
    assert k == 5
    limit = downstream_constants(family_limit_closed_form())
    keys = [key for key in limit if key.startswith("least_")]
    by_k = {row["k"]: row for row in ladder_rows(12)}
    assert all(by_k[k][key] == limit[key] for key in keys)
    assert any(by_k[k - 1][key] != limit[key] for key in keys)


def test_no_remaining_rung_moves_a_discrete_constant() -> None:
    report = ladder_report()
    assert report["constants_unchanged_at_limit"]
    assert report["ladder_is_downstream_inert"]
    limit = report["family_limit_constants"]
    assert limit["least_chernoff_C"] == 19
    assert limit["least_azuma_C_0.5"] == 19
    assert limit["least_azuma_C_0.55"] == 41


def test_cheapest_threshold_is_far_out_of_the_ladders_reach() -> None:
    """The nearest discrete threshold needs orders of magnitude more than remains."""

    report = ladder_report()
    assert all(gap > 0.0 for gap in report["shortfall_to_thresholds"].values())
    assert report["shortfall_over_residual"] > 100.0


def test_the_one_continuous_consumer_moves_below_census_resolution() -> None:
    """``failure_margin`` does depend on the rate continuously -- by nothing readable."""

    cont = continuous_consumer()
    assert cont["below_census_resolution"]
    assert cont["largest_gain"]["gain"] > 0.0
    assert cont["largest_gain_over_resolution"] < 1e-2
    assert cont["census_resolution"] == CENSUS_RESOLUTION


def test_official_lambda_starstar_is_the_v6_truncation() -> None:
    assert lambda_root(vk_recursion(AUDITED_MAX_K)) == pytest.approx(
        lambda_root(RECURSIONS["block_third_plus_oeoee_v6"]), abs=1e-15
    )
