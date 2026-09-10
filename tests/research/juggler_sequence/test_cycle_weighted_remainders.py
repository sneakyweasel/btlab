"""Regression controls for a real-cell relaxation, never an actual cycle."""
from fractions import Fraction
import json

import pytest

from research.juggler_sequence import cycle_weighted_remainders as probe
from research.juggler_sequence.lean_paths import DATA_ROOT


def test_archive_replays_exactly():
    record = json.loads((DATA_ROOT/"cycle_weighted_remainders/summary.json").read_bytes())
    assert probe.report() == record


def test_rational_controls_have_exact_cells_but_violate_odd_spacing():
    for m, length, e in probe.FIXED_GRIDS:
        states = probe.rational_grid(m, length)
        probe.verify_real_cells(states, e)
        for i, x in enumerate(states):
            y = states[(i+e) % length]
            n = 3 if i < length-e else 1
            assert y*y < x**n < (y+1)**2
        assert states[0] == m
        assert states[1]-m < 2
        assert any(x.denominator != 1 for x in states)


def test_exact_cell_validator_rejects_altered_integer_cycle():
    # Archived branch-offset control: the middle edge is J(5)=11, not 10.
    with pytest.raises(ValueError, match="unit cell"):
        probe.verify_real_cells(list(map(Fraction, (3, 5, 10))), 1)


def test_nonconstant_weights_have_opposite_linear_variations():
    length, e = 11, 4
    edges = probe.common_edges(length, e)
    weights = [Fraction(1, i+1) for i in edges]
    beta = probe.incidence_coefficients(length, e, weights)
    assert sum(beta) == 0 and min(beta) < 0 < max(beta)
    for sign in (1, -1):
        direction = [sign*x for x in beta]
        variation = probe.solve_defect_variation(direction, e)
        assert variation[0] == 0
        realized = [variation[i]-variation[(i+e) % length] for i in range(length)]
        assert realized == direction
        weighted = sum(w*(realized[i+1]-realized[i]) for i, w in zip(edges, weights))
        assert weighted == sign*sum(x*x for x in beta)


def test_parity_carry_identity_keeps_the_boundary_terms():
    length, e, o = 11, 4, 7
    edges = probe.common_edges(length, e)
    weights = [Fraction(1, i+1) for i in edges]
    beta = probe.incidence_coefficients(length, e, weights)
    carries = [Fraction(i*i+2) for i in range(length)]
    remainders = [2*k+int(i >= o-e) for i, k in enumerate(carries)]
    direct = sum(w*(remainders[i+1]-remainders[i]) for i, w in zip(edges, weights))
    baseline = weights[edges.index(o-e-1)]
    assert direct == baseline+2*sum(b*k for b, k in zip(beta, carries))
    assert {i for i, b in enumerate(beta) if b < 0} == {0, o}


def test_report_does_not_promote_real_cells_to_actual_cycles():
    report = probe.report()
    assert report["decision"] == "CLOSE"
    assert not any(report[key] for key in (
        "source_search", "orbit_search", "larger_floor", "no_cycle_proved",
        "new_actual_cycle_bound", "new_lean_or_paper_claim",
    ))
    assert sum(c["strict_real_cells_checked"] for c in report["controls"]) == 95
    assert all(not c["integer_floor_cycle_asserted"]
               and not c["all_actual_cycle_constraints_asserted"]
               for c in report["controls"])
