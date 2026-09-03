"""Fair-coin suffix DP and the two direct-attack identities for P_θ / M_{θ,q}."""

from __future__ import annotations

import math
from pathlib import Path

from research.juggler_sequence.pressure_direct import (
    Q_CRIT,
    cylinder_image_stats,
    reset_worst_case_q,
    walsh_generating_function_budget,
)
from research.juggler_sequence.tao_reduction import (
    LOG2_3,
    fair_tilted_live,
    fair_tilted_live_suffix_odd_mass,
    p_of_C,
    scale_L,
    theta_of_C,
)

DOSSIER = Path(__file__).resolve().parents[3] / "docs" / "problems" / "juggler_pressure_direct.md"
SUMMARY = Path(__file__).resolve().parents[3] / "data" / "research" / "juggler" / "pressure_direct" / "summary.json"


def test_theta_19_matches_census_value() -> None:
    assert abs(theta_of_C(19) - 0.396) < 5e-3
    assert 0.59 < p_of_C(19) < 0.61
    assert abs(Q_CRIT - math.log(2.0) / math.log(3.0)) < 1e-12


def test_suffix_mass_matches_brute_force() -> None:
    L, t, theta, k = 1.3, 8, 0.5, 3
    num = 0.0
    den = 0.0
    for bits in range(2 ** (t - 1)):
        o, live, run = 1, True, 1
        for s in range(2, t + 1):
            bit = (bits >> (s - 2)) & 1
            if bit:
                o += 1
                run += 1
            else:
                run = 0
            if o * LOG2_3 - s <= -L:
                live = False
                break
        if live:
            wt = math.exp(theta * o) / 2 ** (t - 1)
            den += wt
            if run >= k:
                num += wt
    assert den > 0
    assert abs(fair_tilted_live_suffix_odd_mass(L, t, theta, k) - num / den) < 1e-12


def test_suffix_mass_edge_cases() -> None:
    L = 1.3
    assert fair_tilted_live_suffix_odd_mass(L, 3, 0.4, 4) == 0.0  # t < k
    # t = k = 1: the unique odd-start word is O
    assert fair_tilted_live_suffix_odd_mass(2.0, 1, 0.4, 1) == 1.0
    # tilt θ = 0 reduces the denominator to the odd-start live probability
    assert fair_tilted_live(L, 8, 0.0) > 0
    mu1 = fair_tilted_live_suffix_odd_mass(L, 8, 0.0, 1)
    assert 0.0 < mu1 < 1.0


def test_reset_worst_case_q_is_half_plus_half_mu() -> None:
    assert reset_worst_case_q(0.0) == 0.5
    assert abs(reset_worst_case_q(0.26) - 0.63) < 1e-12
    assert reset_worst_case_q(0.18) < p_of_C(19)


def test_high_walk_E_image_is_sparse() -> None:
    # OOOE at y = 10^5: u = 3 log2 3 - 4 > 0, last letter E.  Image is sparse
    # in its landing range (not a dyadic interval).  Paper B does not apply.
    row = cylinder_image_stats(10**5, (1, 1, 1, 0))
    assert row["ends_E"] and row["high_walk"] and row["members"] > 0
    assert row["density"] is not None and row["density"] < 0.05
    # OEE is contracted (u < 0); the image can fill a short landing interval.
    contracted = cylinder_image_stats(10**5, (1, 0, 0))
    assert contracted["ends_E"] and not contracted["high_walk"]
    assert contracted["density"] is not None and contracted["density"] > 0.2


def test_walsh_tail_is_exponential_in_d() -> None:
    theta = theta_of_C(19)
    budget = walsh_generating_function_budget(49, theta, k0=4)
    assert budget["log_full_over_d"] > 0.15  # log(1+ρ) ≈ 0.179
    assert budget["log_partial"] < budget["log_full"]
    # fixed-order partial is polynomial in d, hence o(d) in the exponent as d → ∞
    small = walsh_generating_function_budget(8, theta, k0=4)
    assert small["partial_k0"] < small["full_1_plus_rho_pow_d"]


def test_tao_depth_suffix_dp_runs() -> None:
    L = scale_L(12 * math.log(10.0), 350_000_000)
    d = math.ceil(19 * L)
    mu4 = fair_tilted_live_suffix_odd_mass(L, d, theta_of_C(19), 4)
    assert 0.0 <= mu4 <= 1.0


def test_dossier_headings_and_close() -> None:
    dossier = DOSSIER.read_text(encoding="utf-8")
    for heading in (
        "## Problem",
        "## Exact statement",
        "## Current literature",
        "## Branch budget",
        "## Balanced-ternary formulation",
        "## Why BT may be relevant",
        "## Candidate operations / invariants",
        "## Experiments",
        "## Conjectures",
        "## Counterexamples",
        "## Formalization",
        "## Results",
        "## Open questions",
        "## Decision",
        "## Publication assessment",
    ):
        assert heading in dossier
    decision = dossier.split("## Decision", 1)[1].split("## ", 1)[0]
    assert "CLOSE" in decision


def test_summary_artifact_exists() -> None:
    assert SUMMARY.is_file()
    import json

    data = json.loads(SUMMARY.read_text(encoding="utf-8"))
    assert data["classification"]["decision"] == "CLOSE"
    assert data["classification"]["reset_is_H_q_at_unbounded_depth"] is True
    assert data["classification"]["S_sampling_is_S_fairness"] is True
