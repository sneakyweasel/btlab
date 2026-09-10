"""Exact tests of three open guarded rectangles and their symbolic proof data."""
from fractions import Fraction
from math import comb, isqrt

import pytest

from research.juggler_sequence import cycle_return_seam as probe


@pytest.fixture(scope="module")
def report():
    return probe.report()


@pytest.fixture(scope="module")
def polynomials():
    return probe.positivity_polynomials()


def _fraction(record):
    return Fraction(record["numerator"], record["denominator"])


def _actual_word(source, word):
    for branch in word:
        assert source % 2 == (branch == "O")
        source = isqrt(source**(3 if source % 2 else 1))
    return source


def test_three_fixed_controls_have_twelve_distinct_actual_edges(report):
    expected = (2**32+65, 2**40+65, 2**64+65)
    assert probe.FIXED_PARAMETERS == expected
    assert report["fixed_parameters"] == list(expected)
    assert tuple(row["u"] for row in report["controls"]) == expected
    for row in report["controls"]:
        assert row["r"] == row["u"]**4+2
        assert len(row["edges"]) == 12
        assert len({(e["source"], e["target"]) for e in row["edges"]}) == 12
        for edge in row["edges"]:
            x, y = edge["source"], edge["target"]
            actual_exponent = 3 if x % 2 else 1
            assert edge["branch"] == ("O" if x % 2 else "E")
            assert isqrt(x**actual_exponent) == y
            assert edge["square_remainder"] == x**actual_exponent-y*y > 0
            assert edge["upper_margin"] == (y+1)**2-x**actual_exponent > 0


def test_alternative_faces_share_the_complete_guarded_rectangle(report):
    for row in report["controls"]:
        m, a, t, q, w, z = (row[key] for key in
                            ("minimum", "a", "t", "q", "w", "z"))
        assert row["b_high"]-row["b_low"] == 2
        assert row["s_high"]-row["s_low"] == 3*row["r"]**4+5
        assert _actual_word(a, "OOE") == t
        assert _actual_word(t, "OE") == w
        assert _actual_word(m, "OOE") == _actual_word(q, "OE") == z
        assert _actual_word(a, "OOEOE") == w
        for bkey, skey in (("b_low", "s_low"), ("b_high", "s_high")):
            b, s = row[bkey], row[skey]
            assert _actual_word(b, "O") == s
            assert _actual_word(b, "OE") == m
            assert _actual_word(b, "OEOOE") == z
        assert not row["both_faces_in_one_cycle_asserted"]


def test_opposite_losses_have_independent_integer_power_certificates(report):
    for row in report["controls"]:
        r, q, t, h, M = (row[key] for key in ("r", "q", "t", "h", "maximum"))
        # e_EO(s_low)<1/8 and e_OE(h)>7/8, independently of stored loss flags.
        assert 8**4*row["s_low"]**3 < (8*q+1)**4
        assert 64*M > (8*t+7)**2
        assert _fraction(row["negative_loss_upper_bound"]) < -Fraction(3, 4)
        # e_EO(s_high)>2r while e_OE(h)<1 proves the other strict sign.
        assert row["s_high"]**3 > (q+2*r)**4
        assert h**3 < (t+1)**4
        assert _fraction(row["positive_loss_lower_bound"]) > 2*r-1


def test_all_fifteen_polynomials_equal_direct_margins_at_fixed_controls(report, polynomials):
    assert len(polynomials) == 15
    for row in report["controls"]:
        m, M, a, t, q, Ht, Hq, w, z = (row[key] for key in
            ("minimum", "maximum", "a", "t", "q", "H_t", "H_q", "w", "z"))
        direct = {
            "t_lower": t**3-Ht**2, "t_upper": (Ht+1)**2-t**3,
            "q_lower": q**3-Hq**2, "q_upper": (Hq+1)**2-q**3,
            "H_t_lower": Ht-w*w, "H_t_upper": (w+1)**2-Ht,
            "H_q_lower": Hq-z*z, "H_q_upper": (z+1)**2-Hq,
            "w_minus_m": w-m, "z_minus_w": z-w, "a_minus_z": a-z,
            "H_t_minus_m_squared": Ht-m*m,
            "H_t_minus_s_high": Ht-row["s_high"],
            "H_q_minus_H_t": Hq-Ht, "M_minus_H_q": M-Hq,
        }
        assert set(polynomials) == set(direct)
        for name, poly in polynomials.items():
            value = sum((coefficient*row["u"]**degree
                         for degree, coefficient in poly.items()), Fraction(0))
            assert value == direct[name] > 0


def test_modular_table_and_symbolic_residue_class_periodicity(report):
    expected = {
        "H_t": (1096, 28, 840, 0), "H_q": (1352, 20, 584, 0),
        "w": (1605, 31, 1541, 1), "z": (629, 15, 1589, 1),
    }
    certificates = {row["output"]: row for row in report["congruence_certificates"]}
    assert set(certificates) == set(expected)
    for name, wanted in expected.items():
        record = certificates[name]
        actual = tuple(record[key] for key in (
            "numerator_at_one_mod_2048", "derivative_at_one_mod_32",
            "numerator_at_65_mod_2048", "output_parity"))
        assert actual == wanted
        degree = probe.DEGREES[name]
        terms = [(degree-4*j, coefficient)
                 for j, coefficient in enumerate(probe.NUMERATOR_COEFFICIENTS[name])]
        at_65 = sum(c*pow(65, p, 2048) for p, c in terms) % 2048
        assert at_65 == wanted[2] == (wanted[0]+64*wanted[1]) % 2048
        assert (at_65-probe.SHIFTS[name]) % 2048 == 1024*wanted[3]
        # Coefficients of k^j in N(65+2048k)-N(65): no new source evaluation.
        for j in range(1, degree+1):
            coefficient = sum(c*comb(p, j)*65**(p-j)*2048**j
                              for p, c in terms if p >= j)
            assert coefficient % 2048 == 0
        # The terms beyond the derivative in the 1+64 lift vanish modulo 2048.
        for p, c in terms:
            assert all((c*comb(p, j)*64**j) % 2048 == 0 for j in range(2, p+1))


def test_uniform_dominance_and_the_written_simple_budgets(report, polynomials):
    records = {row["polynomial"]: row for row in report["uniform_coefficient_certificates"]}
    assert set(records) == set(polynomials)
    expected_leads = {
        "t_lower": (54, Fraction(105, 64)), "t_upper": (54, Fraction(23, 64)),
        "q_lower": (54, Fraction(73, 64)), "q_upper": (54, Fraction(55, 64)),
        "H_t_lower": (27, Fraction(517, 512)), "H_t_upper": (27, Fraction(507, 512)),
        "H_q_lower": (27, Fraction(565, 512)), "H_q_upper": (27, Fraction(459, 512)),
    }
    for name, poly in polynomials.items():
        degree, record = max(poly), records[name]
        negatives = {p: -c for p, c in poly.items() if c < 0}
        budget = sum((c/Fraction((2**32)**(degree-p))
                      for p, c in negatives.items()), Fraction(0))
        assert record["degree"] == degree
        assert _fraction(record["leading_coefficient"]) == poly[degree] > 0
        assert _fraction(record["negative_to_leading_ratio"]) == budget/poly[degree] < Fraction(1, 2)
        assert record["positive_for_every_u_at_least"] == 2**32
        assert {int(p): Fraction(c) for p, c in record["coefficients"].items()} == poly
        assert _fraction(record["negative_coefficient_sum"]) == sum(negatives.values(), Fraction(0))
        assert record["largest_negative_degree"] == max(negatives, default=None)
        if name in expected_leads:
            assert (degree, poly[degree]) == expected_leads[name]
        else:
            assert sum(negatives.values(), Fraction(0)) < 2**22
            assert max(negatives, default=-1) <= degree-3
    for name in ("t_lower", "q_lower"):
        assert records[name]["largest_negative_degree"] is None
    for name in ("t_upper", "q_upper"):
        assert records[name]["largest_negative_degree"] <= 52
        assert _fraction(records[name]["negative_coefficient_sum"]) < 2**35
    for name, bound in (("H_t_lower", 2), ("H_q_lower", 1)):
        assert records[name]["largest_negative_degree"] == 0
        assert _fraction(records[name]["negative_coefficient_sum"]) < bound
    for name in ("H_t_upper", "H_q_upper"):
        assert records[name]["largest_negative_degree"] <= 26
        assert _fraction(records[name]["negative_coefficient_sum"]) < 2**18


def test_exact_gap_identity_and_dc_lr_ab_scalar_bounds(report):
    outputs = probe.output_polynomials()
    gap_poly = {p: outputs["z"].get(p, 0)-outputs["w"].get(p, 0)
                for p in set(outputs["z"]) | set(outputs["w"])}
    gap_poly = {p: c for p, c in gap_poly.items() if c}
    assert gap_poly == {11: Fraction(27, 8), 7: Fraction(297, 16),
                        3: Fraction(1863, 64), 0: -Fraction(3, 64)}
    gamma, rho = Fraction(243, 256), Fraction(3**41, 2**65)
    sigma = Fraction(13, 128)+1-rho
    assert 0 < sigma < Fraction(1, 8) < Fraction(11, 24)
    assert Fraction(57344, 59049) < 1  # Even the sharper DC leading coefficient.
    assert Fraction(7609, 20480)/(gamma*gamma*rho) < 1
    for row in report["controls"]:
        u, r, m, d, a = (row[key] for key in ("u", "r", "minimum", "gap", "a"))
        assert d == row["z"]-row["w"] and d % 2 == 0 and d >= 8
        assert 64*d == 216*u**11+1188*u**7+1863*u**3-3
        assert 16*r**11 < d**4 < 256*r**11
        assert d**24 > m**11
        # Integer-power certificates stronger than the cited DC/LR lower bounds.
        assert d**128 > m**13 and d**8 > m
        for b in (row["b_low"], row["b_high"]):
            assert (32*d)**32*m**5 < (27*(b-a))**32
            assert d <= b-a-2


def test_full_numerical_order_seam_cells_and_height_margin(report):
    for row in report["controls"]:
        m, M = row["minimum"], row["maximum"]
        ordered = [m, row["w"], row["z"], row["a"], row["b_low"], row["b_high"],
                   row["t"], row["q"], row["h"], m*m, row["s_low"], row["s_high"],
                   row["H_t"], row["H_q"], M, m**3]
        assert all(x < y for x, y in zip(ordered, ordered[1:]))
        assert all(row[key] % 2 == 1 for key in
                   ("minimum", "w", "z", "a", "b_low", "b_high", "t", "q", "h"))
        assert all(row[key] % 2 == 0 for key in ("s_low", "s_high", "H_t", "H_q", "maximum"))
        assert m > 2**768 and M < m**3-2*m*m
        assert row["t"]**3+2 <= (row["w"]*(row["w"]+2))**2
        assert row["q"]**3+2 <= (row["z"]*(row["z"]+2))**2
        assert M+2 <= (row["t"]+1)**2
        assert row["z"]**8 <= m**9
        deficit = m**3-M
        assert (2*deficit)**128 > m**253
        assert (2*deficit)**64 > m**127


def test_parameter_domain_and_open_rectangle_scope(report):
    for invalid in (-1, 65, 2**32, 2**32+64):
        with pytest.raises(ValueError, match="at least 2\\^32.*65 modulo 2048"):
            probe.family(invalid)
    assert report["decision"] == "CLOSE"
    assert report["proof_owner"] == "docs/problems/juggler_cycle_return_seam.md"
    assert not any(report[key] for key in (
        "source_search", "orbit_search", "raised_floor", "new_actual_cycle_bound",
        "no_cycle_proved", "new_lean_or_paper_claim"))
    for row in report["controls"]:
        assert row["guarded_original_rectangle_asserted"]
        assert not row["both_faces_in_one_cycle_asserted"]
        assert not row["cycle_adjacency_asserted"] and not row["periodic_orbit_asserted"]
