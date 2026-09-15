"""DK sharpness Phase 0. Not a halt test and not an envelope edit."""

from __future__ import annotations

import json
import math
from pathlib import Path

from research.juggler_sequence.cycle_walk_sharpness import (
    representative_log_n,
)

DOSSIER = Path("docs/problems/juggler_cycle_walk_sharpness.md")
CONJECTURE = Path("conjectures/active/juggler_walk_excess_arch.json")
ARTIFACT = Path("data/research/juggler/cycle_walk_sharpness/summary.json")


def test_representative_base():
    assert math.isclose(representative_log_n(), 17.0826, abs_tol=1e-3)


def test_sharpness_artifact():
    payload = json.loads(ARTIFACT.read_text(encoding="utf-8"))
    rep = payload["report"]
    assert -0.3 < rep["excess_min"] < 0.0
    assert 4.9 < rep["max_abs_excess"] < 5.0
    assert rep["window_max_ratio_to_2s"] < 0.5
    assert rep["overall_max_ratio_to_2s"] < 0.5
    # Saturation: the 1054-tower dominates, later levels add little.
    running = rep["running_max_abs_at"]
    assert running["301993"] < 1.1 * running["24727"]
    # The three structural laws fail.
    assert abs(rep["alt_fit_window"]["pearson_r"]) < 0.5
    assert rep["digit_fit"]["r_squared"] < 0.5
    assert rep["collapse_fails"] is True
    # Arch shape along the 1054-tower.
    tower = rep["towers"]["1054"]
    assert tower[11] > 2.9
    assert abs(tower[23]) < 0.1
    assert payload["leftover_cross_check"]["max_abs_diff"] < 1e-3
    assert payload["classification"]["label"] == "WALK_SHARPNESS_BOUNDED"


def test_anti_overclaim_and_dossier_headings():
    dossier = DOSSIER.read_text(encoding="utf-8")
    for heading in (
        "## Problem",
        "## Exact statement",
        "## Current literature",
        "## Branch budget",
        "## Decision",
        "## Publication assessment",
    ):
        assert heading in dossier
    decision = dossier.split("## Decision", 1)[1].split("## ", 1)[0]
    assert "PARK" in decision
    assert "not claimed" in dossier
    record = json.loads(CONJECTURE.read_text(encoding="utf-8"))
    assert record["id"] == "juggler_walk_excess_arch"
    assert record["status"] == "COMPUTATIONALLY_SUPPORTED"
    assert record["not_a_halt_theorem"] is True
    payload = json.loads(ARTIFACT.read_text(encoding="utf-8"))
    assert payload["no_new_kills"] is True
    assert payload["envelope_unchanged"] is True
    assert payload["not_a_halt_theorem"] is True
    assert payload["no_cycle_all_lengths"] is False
    assert payload["not_a_uniform_ratio_theorem"] is True


def test_the_excess_census_is_one_sided_only_inside_its_own_range() -> None:
    """The PARK's headline "one-sided window-bounded excess" is census-bounded.

    The recorded census runs L < 301994 = q_13(theta) and reports e in
    (-0.2775, 4.9696].  Extended fivefold:

      * the MAXIMUM is unchanged, 4.96958, and is attained at L = 238541, inside
        the recorded range -- the upper saturation the envelope actually depends on
        is confirmed five times further out, so no kill and no period bound moves;
      * the MINIMUM drops 7.6x, to -2.10047 at L = 1359007, so the excess is
        two-sided beyond the census and the "one-sided" reading does not survive.

    Not numerics: C_* converges to 0.047941275456 and a 256x quadrature refinement
    moves the minimum by 3e-4.
    """
    import numpy as np

    from research.juggler_sequence.cycle_walk_sharpness import (
        excess_curve,
        representative_log_n,
        LIMIT,
    )

    log_n = representative_log_n()
    inside = excess_curve(log_n, limit=LIMIT)["excess"]
    assert abs(inside.min() - (-0.27750)) < 1e-4, inside.min()
    assert abs(inside.max() - 4.96958) < 1e-4, inside.max()

    out = excess_curve(log_n, limit=1_500_000)["excess"]
    assert abs(out.max() - inside.max()) < 1e-9          # upper bound saturates
    assert int(out.argmax()) + 1 == 238541
    assert out.min() < -2.10, out.min()                  # lower bound does not
    assert out.min() / inside.min() > 7.0, (out.min(), inside.min())
    assert int(np.argmin(out)) + 1 == 1359007


def test_digit_profiles_refuses_a_limit_its_continued_fraction_cannot_carry() -> None:
    """s(L) beyond the CF's reach is inflated, and inflation flatters |e|/2s.

    digit_profiles expands L greedily over the CF's denominators.  Past the largest
    one the greedy digit exceeds its partial-quotient bound and s(L) is too big --
    at L = 780239, a real kill length, a CF stopping at 176251 gives s = 6 against a
    true s = 3.  The envelope reads |e| / 2s, so an inflated s UNDERSTATES the ratio:
    the error runs toward the safe-looking conclusion, which is why this refuses
    rather than warns.
    """
    import pytest

    from research.juggler_sequence.cycle_walk_sharpness import digit_profiles, LIMIT
    from research.juggler_sequence.cycle_walk_ostrowski import certified_theta_cf

    cf = certified_theta_cf()
    assert max(cf["denominators"]) == 176251

    # the shipped census is exactly at the validity boundary and still works
    assert digit_profiles(cf, limit=LIMIT)["s"].max() == 37

    with pytest.raises(ValueError, match="exceeds its partial quotient"):
        digit_profiles(cf, limit=500_000)
