"""Location-free transfer-weight inequalities do not force four-step contraction."""

from __future__ import annotations

import json
import math
from pathlib import Path

from research.juggler_sequence.tao_reduction import N0_LEAN, theta_of_C
from research.juggler_sequence.transfer_weight_invariant import (
    collect_oooo_starts,
    fair_coin_five_word_shares,
    four_word,
    inequalities_meet_onesided_cut,
    integer_cbrt_ceil,
    integer_cbrt_floor_lt,
    location_free_mu_bound,
    oe_ancestor_count,
    oe_preimage_span,
    onesided_cut_holds,
    onesided_excess,
    oooo_relabel_witness,
    tilt_constants,
)

DOSSIER = (
    Path(__file__).resolve().parents[3]
    / "docs"
    / "problems"
    / "juggler_transfer_weight_invariant.md"
)
SUMMARY = (
    Path(__file__).resolve().parents[3]
    / "data"
    / "research"
    / "juggler"
    / "transfer_weight_invariant"
    / "summary.json"
)


def test_tilt_19_matches_tao_constants() -> None:
    c = tilt_constants()
    assert abs(c["theta"] - theta_of_C(19)) < 1e-15
    assert 0.39 < c["theta"] < 0.40
    assert abs(c["a"] - 0.5 * (1.0 + c["x"])) < 1e-15
    assert abs(c["a4"] - c["a"] ** 4) < 1e-15
    assert abs(c["coef_mu4"] - (c["r4"] - c["r2"])) < 1e-15
    assert abs(c["rhs"] - (1.0 - c["r2"])) < 1e-15
    # Plan arithmetic: 1.12 μ4 + 0.45 μ3 < 0.074
    assert 1.11 < c["coef_mu4"] < 1.12
    assert 0.44 < c["coef_mu3"] < 0.46
    assert 0.074 < c["rhs"] < 0.076
    assert 2.04 < c["r4"] < 2.05


def test_fair_coin_misses_onesided_cut() -> None:
    c = tilt_constants()
    mu4, mu3 = fair_coin_five_word_shares()
    assert mu4 == 1.0 / 16.0
    assert mu3 == 0.25
    assert onesided_excess(mu4, mu3, c) > 0.1
    assert not onesided_cut_holds(mu4, mu3, c)
    # Exact fair-coin moment is exactly a^4: sixteen words, each 1/16.
    moment = sum(c["x"] ** bin(k).count("1") for k in range(16)) / 16.0
    assert abs(moment - c["a4"]) < 1e-12


def test_location_free_bounds_do_not_meet_cut() -> None:
    c = tilt_constants()
    assert location_free_mu_bound(1.0, 1.0, None)["best"] == 1.0
    assert location_free_mu_bound(0.2, 0.2, 5)["best"] == 1.0
    assert not inequalities_meet_onesided_cut(1.0, 1.0, None, c)
    assert not inequalities_meet_onesided_cut(0.2, 0.2, 5, c)
    # Even a tiny max-atom is useless without a bound on n_S.
    assert not inequalities_meet_onesided_cut(1e-6, 1e-6, None, c)


def test_integer_cbrt_helpers() -> None:
    assert integer_cbrt_ceil(1) == 1
    assert integer_cbrt_ceil(8) == 2
    assert integer_cbrt_ceil(9) == 3
    assert integer_cbrt_floor_lt(8) == 1
    assert integer_cbrt_floor_lt(9) == 2
    assert integer_cbrt_ceil(10**12) ** 3 >= 10**12
    assert (integer_cbrt_ceil(10**12) - 1) ** 3 < 10**12


def test_oooo_relabel_saturates_concentration() -> None:
    starts = collect_oooo_starts(5, N0_LEAN, 20_000)
    assert starts == [265, 271, 289, 293, 309]
    witness = oooo_relabel_witness(starts, N0_LEAN)
    assert witness["injective"] and witness["all_oooo"]
    assert abs(witness["mass_ratio"] - witness["x4"]) < 1e-12
    assert abs(witness["energy_before"] - witness["energy_after"]) < 1e-12
    assert abs(witness["max_atom_before"] - witness["max_atom_after"]) < 1e-12
    assert witness["ancestry_before"] == witness["ancestry_after"] == [1, 1, 1, 1, 1]
    assert witness["positive_share"] == 1.0
    assert witness["onesided_cut"] is False
    assert witness["location_free_meets_cut"] is False
    assert 2.04 < witness["x4_over_a4"] < 2.05


def test_oe_span_grows_and_favorable_count_grows() -> None:
    spans = [oe_preimage_span(m) for m in (10, 100, 1_000, 10_000, 100_000)]
    assert spans == [3, 6, 14, 29, 62]
    assert all(spans[i] < spans[i + 1] for i in range(len(spans) - 1))
    # Separated favorable targets from the probe: OOOO / OOOE / OOEO.
    assert four_word(2001, N0_LEAN)[0] == "OOOO"
    assert four_word(20001, N0_LEAN)[0] == "OOOE"
    assert four_word(200001, N0_LEAN)[0] == "OOEO"
    counts = [oe_ancestor_count(m) for m in (2001, 20001, 200001)]
    assert counts == [3, 9, 21]
    assert counts[-1] > counts[0]


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


def test_summary_artifact_classifies_close() -> None:
    assert SUMMARY.is_file()
    data = json.loads(SUMMARY.read_text(encoding="utf-8"))
    assert data["classification"]["decision"] == "CLOSE"
    assert data["classification"]["oooo_profile_is_relabel"] is True
    assert data["classification"]["oe_span_unbounded"] is True
    assert data["classification"]["location_free_bounds_miss_cut"] is True
    assert data["classification"]["fair_coin_misses_onesided_cut"] is True
    assert data["pushforward"]["max_ratio4"] < 1.0
    assert data["N0"] == N0_LEAN
    assert math.isclose(data["tilt"]["theta"], theta_of_C(19), rel_tol=0, abs_tol=1e-15)
