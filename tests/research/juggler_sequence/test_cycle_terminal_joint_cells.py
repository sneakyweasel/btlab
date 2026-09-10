"""Exact bounded controls for the two local obstructions, not cycle tests."""
import json
from fractions import Fraction
from math import isqrt

from research.juggler_sequence import cycle_terminal_joint_cells as probe
from research.juggler_sequence.lean_paths import DATA_ROOT


def test_fixed_report_matches_archive():
    expected = json.loads((DATA_ROOT/"cycle_terminal_joint_cells/summary.json").read_bytes())
    assert probe.report() == expected


def test_all_mixed_edges_use_the_actual_branch():
    for r, _ in probe.FIXED_PARAMETERS:
        d = probe.mixed_cells(r)
        for x, y in [(d["h"], d["maximum"]), (d["maximum"], d["t"]),
                     (d["s_low"], d["minimum"]), (d["s_high"], d["minimum"]),
                     (d["minimum"], d["q"])]:
            assert isqrt(x**(3 if x % 2 else 1)) == y


def test_mixed_remainder_identities_and_height_margin():
    for r, _ in probe.FIXED_PARAMETERS:
        d = probe.mixed_cells(r)
        K = r*r-1
        assert 4*(d["h"]**3-d["maximum"]**2) == 3*K*K+4
        assert 4*(d["maximum"]-d["t"]**2) == 4*r**3+9*r*r-6*r-11
        assert 4*((d["t"]+1)**2-d["maximum"]) == 4*r**3-9*r*r-6*r+11
        assert d["cube_deficit"] > 2*d["minimum"]**2


def test_sign_certificates_at_the_later_cutoff():
    d = probe.mixed_cells(2**64+1)
    assert all(d["cutoffs_active"].values())
    assert all(d["checks"].values())
    r = d["r"]
    margin = d["negative_certificate_margin"]
    assert Fraction(margin["numerator"], margin["denominator"]) > 0
    lower = d["positive_loss_lower_bound"]
    assert Fraction(lower["numerator"], lower["denominator"]) > r


def test_even_face_coefficients_and_guards():
    for _, a in probe.FIXED_PARAMETERS:
        rows = probe.even_cells(a)["faces"]
        coefficients = []
        for row in rows:
            x, y = row["x"], row["y"]
            p, q = row["outputs"]
            assert x % 2 == y % 2 == 0 and p % 2 == q % 2 == 1
            assert p*p <= x < (p+1)**2 and q*q <= y < (q+1)**2
            coefficients.append(Fraction(q*q-p*p, y-x))
        assert coefficients == [Fraction(2, 3), 2-Fraction(4, a+3)]


def test_local_examples_do_not_claim_cycle_closure():
    d = probe.report()
    assert d["decision"] == "PARK"
    assert d["scope"]["parameter_pairs"] == 3
    assert not any(d[key] for key in
                   ("new_cycle_restriction", "full_joint_cell_comparison_proved",
                    "no_cycle_proved", "new_lean_or_paper_claim"))
    assert all(not entry[k]["periodic_closure_asserted"]
               for entry in d["controls"] for k in ("mixed", "even"))
