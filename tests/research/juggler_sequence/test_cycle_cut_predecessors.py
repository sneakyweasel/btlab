"""Exact controls for open guarded paths with two opposite loss signs."""
from fractions import Fraction
import json
from math import isqrt

import pytest

from research.juggler_sequence import cycle_cut_predecessors as probe
from research.juggler_sequence.lean_paths import DATA_ROOT


def test_fixed_archive_replays():
    expected = json.loads((DATA_ROOT/"cycle_cut_predecessors/summary.json").read_bytes())
    assert probe.report() == expected


def test_every_displayed_edge_is_an_actual_juggler_step():
    for r in probe.FIXED_PARAMETERS:
        data = probe.family(r)
        assert len(data["edges"]) == 8
        for edge in data["edges"]:
            x, y = edge["source"], edge["target"]
            assert isqrt(x**(3 if x % 2 else 1)) == y
            assert edge["square_remainder"] >= 0 and edge["upper_margin"] > 0


def test_upper_faces_change_predecessor_by_two_with_shared_anchors():
    for r in probe.FIXED_PARAMETERS:
        data = probe.family(r)
        assert data["b_high"]-data["b_low"] == 2
        assert data["s_high"]-data["s_low"] == 3*r**4+5
        assert isqrt(data["s_high"]) == isqrt(data["s_low"]) == data["minimum"]
        assert data["minimum"]**2 < data["s_low"] < data["s_high"] < (data["minimum"]+1)**2


def test_negative_sign_has_independent_exact_power_certificates():
    for r in probe.FIXED_PARAMETERS:
        data = probe.family(r)
        # e_EO(s_low)<1/8 and e_OE(h)>7/8, with no floating-point radicals.
        assert 8**4*data["s_low"]**3 < (8*data["q"]+1)**4
        assert 64*data["maximum"] > (8*data["t"]+7)**2
        bound = data["negative_loss_upper_bound"]
        assert Fraction(bound["numerator"], bound["denominator"]) < -Fraction(3, 4)


def test_positive_sign_has_independent_exact_power_certificates():
    for r in probe.FIXED_PARAMETERS:
        data = probe.family(r)
        # e_EO(s_high)>2r and e_OE(h)<1 imply Delta_high>2r-1.
        assert data["s_high"]**3 > (data["q"]+2*r)**4
        assert data["h"]**3 < (data["t"]+1)**4
        bound = data["positive_loss_lower_bound"]
        assert Fraction(bound["numerator"], bound["denominator"]) > 2*r-1


def test_exact_ceilings_and_noncube_alignment():
    for r in probe.FIXED_PARAMETERS:
        data = probe.family(r)
        m, b = data["minimum"], data["b_low"]
        assert (b-1)**3 < m**4 < b**3
        for z, a in ((data["h"], data["a"]),
                     (data["s_low"], data["b_low"]),
                     (data["s_high"], data["b_high"])):
            assert (a-1)**3 < z*z <= a**3 < (z+1)**2
            assert probe.ceil_cuberoot(z*z) == a and a % 2 == 1
        assert r**6 < m < (r*r+1)**3


def test_large_control_meets_prior_height_cutoffs():
    data = probe.family(2**32+3)
    assert all(data["cutoffs_active"].values())
    assert data["cube_deficit"] > 2*data["minimum"]**2
    assert all(data["checks"].values())


def test_uniform_polynomial_certificates_match_exact_cells():
    certificates = probe.coefficient_certificates()
    assert len(certificates) == 25
    for r in probe.FIXED_PARAMETERS:
        data = probe.family(r)
        values = {
            name: sum(coefficient*r**power for power, coefficient in terms.items())
            for name, terms in probe.POSITIVITY_POLYNOMIALS.items()
        }
        names = ("a", "h", "M", "b_low", "b_high", "s_low", "s_high")
        for name, edge in zip(names, data["edges"][:-1]):
            assert values[name+"_lower"] == edge["square_remainder"]
            assert values[name+"_upper"] == edge["upper_margin"]
        q_edge = data["edges"][-1]
        assert values["q_lower_scaled"] == 64*q_edge["square_remainder"]
        assert values["q_upper_scaled"] == 64*q_edge["upper_margin"]
        assert values["height_margin"] == data["cube_deficit"]-2*data["minimum"]**2
        assert values["left_loss_margin"] == 64*data["maximum"]-(8*data["t"]+7)**2
        assert all(value > 0 for value in values.values())


def test_scope_and_parameter_domain_are_explicit():
    for r in (3, 66, 68):
        with pytest.raises(ValueError):
            probe.family(r)
    data = probe.report()
    assert data["decision"] == "CLOSE"
    assert not any(data[k] for k in (
        "source_search", "orbit_search", "raised_floor",
        "new_actual_cycle_bound", "no_cycle_proved", "new_lean_or_paper_claim",
    ))
    assert all(not c["periodic_orbit_asserted"] and not c["full_return_seam_asserted"]
               for c in data["controls"])
