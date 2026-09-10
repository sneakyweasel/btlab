"""Exact polynomial certificates for an infinite guarded return-seam family.

The two predecessor faces are alternatives. These open paths do not supply
a common periodic set, rank adjacency, or the remaining selected transfers.
Only three fixed parameters are evaluated; there is no parameter census.
"""
from __future__ import annotations

from fractions import Fraction
import json
from math import isqrt

from research.juggler_sequence.cycle_cut_predecessors import (
    coefficient_certificates as predecessor_certificates,
    family as predecessor_family,
    fraction_record,
)
from research.juggler_sequence.lean_paths import DATA_ROOT

MINIMUM_PARAMETER = 2**32
FIXED_PARAMETERS = (2**32+65, 2**40+65, 2**64+65)
NUMERATOR_COEFFICIENTS = {
    "H_t": (1024, 27648, 345600, 2649600, 13910400, 52859520,
            149768640, 320932800, 521529624, 637558728, 574337844,
            366609348, 154023975, 36239049),
    "H_q": (1024, 27648, 345600, 2649600, 13917312, 52990848,
            150878016, 326410560, 538994520, 674986824, 628592724,
            418520196, 184637853, 45676467),
    "w": (1024, 13824, 79488, 251712, 471960, 519156, 302841),
    "z": (1024, 13824, 79488, 251712, 475416, 538164, 332649),
}
SHIFTS = {"H_t": 840, "H_q": 584, "w": 517, "z": 565}
DEGREES = {"H_t": 54, "H_q": 54, "w": 27, "z": 27}
Poly = dict[int, Fraction]


def _add(*terms: Poly) -> Poly:
    result: Poly = {}
    for term in terms:
        for degree, value in term.items():
            result[degree] = result.get(degree, Fraction(0))+value
    return {degree: value for degree, value in result.items() if value}


def _scale(poly: Poly, coefficient: int | Fraction) -> Poly:
    return {degree: value*coefficient for degree, value in poly.items()
            if value*coefficient}


def _subtract(left: Poly, right: Poly) -> Poly:
    return _add(left, _scale(right, -1))


def _multiply(left: Poly, right: Poly) -> Poly:
    result: Poly = {}
    for i, a in left.items():
        for j, b in right.items():
            result[i+j] = result.get(i+j, Fraction(0))+a*b
    return {degree: value for degree, value in result.items() if value}


def _power(poly: Poly, exponent: int) -> Poly:
    result = {0: Fraction(1)}
    for _ in range(exponent):
        result = _multiply(result, poly)
    return result


def evaluate(poly: Poly, parameter: int) -> Fraction:
    return sum((value*parameter**degree for degree, value in poly.items()),
               Fraction(0))


def output_polynomials() -> dict[str, Poly]:
    return {
        name: {**{DEGREES[name]-4*j: Fraction(value, 1024)
                  for j, value in enumerate(coefficients)},
               0: -Fraction(SHIFTS[name], 1024)}
        for name, coefficients in NUMERATOR_COEFFICIENTS.items()
    }


def positivity_polynomials() -> dict[str, Poly]:
    """Re-expand defining expressions over Q; no stored margin table."""
    r = {4: Fraction(1), 0: Fraction(2)}
    constant = lambda value: {0: Fraction(value)}
    m = _add(_power(r, 6), _scale(_power(r, 2), 3), constant(-3))
    a = _add(_power(r, 8), constant(8))
    t = _add(_power(r, 9), _scale(r, 9), constant(-1))
    q = _add(_power(r, 9), _scale(_power(r, 5), Fraction(9, 2)),
             _scale(_power(r, 3), -Fraction(9, 2)),
             _scale(r, Fraction(27, 8)), constant(-Fraction(1, 8)))
    M = _add(_power(r, 18), _scale(_power(r, 10), 18),
             _scale(_power(r, 2), 54), constant(-1))
    s_high = _add(_power(m, 2), _scale(_power(r, 2), 6),
                 _scale(_power(r, 4), 3), constant(4))
    p = output_polynomials()
    result = {}
    for source_name, source, target_name in (
        ("t", t, "H_t"), ("q", q, "H_q"),
        ("H_t", p["H_t"], "w"), ("H_q", p["H_q"], "z"),
    ):
        radicand = _power(source, 3 if source_name in ("t", "q") else 1)
        target = p[target_name]
        result[source_name+"_lower"] = _subtract(radicand, _power(target, 2))
        result[source_name+"_upper"] = _subtract(
            _power(_add(target, constant(1)), 2), radicand)
    for name, left, right in (
        ("w_minus_m", p["w"], m), ("z_minus_w", p["z"], p["w"]),
        ("a_minus_z", a, p["z"]), ("H_t_minus_m_squared", p["H_t"], _power(m, 2)),
        ("H_t_minus_s_high", p["H_t"], s_high),
        ("H_q_minus_H_t", p["H_q"], p["H_t"]),
        ("M_minus_H_q", M, p["H_q"]),
    ):
        result[name] = _subtract(left, right)
    return result


def coefficient_certificates() -> list[dict]:
    records = []
    for name, poly in positivity_polynomials().items():
        degree = max(poly)
        leading = poly[degree]
        negative = {power: -value for power, value in poly.items() if value < 0}
        budget = sum((value/Fraction(MINIMUM_PARAMETER**(degree-power))
                      for power, value in negative.items()), Fraction(0))
        assert leading > 0 and 0 <= budget/leading < Fraction(1, 2)
        records.append({
            "polynomial": name, "degree": degree,
            "leading_coefficient": fraction_record(leading),
            "negative_coefficient_sum": fraction_record(sum(negative.values(), Fraction(0))),
            "largest_negative_degree": max(negative, default=None),
            "negative_to_leading_ratio": fraction_record(budget/leading),
            "positive_for_every_u_at_least": MINIMUM_PARAMETER,
            "coefficients": {str(power): str(value) for power, value in sorted(poly.items())},
        })
    return records


def congruence_certificates() -> list[dict]:
    records = []
    for name, coefficients in NUMERATOR_COEFFICIENTS.items():
        degree = DEGREES[name]
        residue_one = sum(coefficients) % 2048
        derivative = sum(value*(degree-4*j)
                         for j, value in enumerate(coefficients)) % 32
        residue = sum(value*pow(65, degree-4*j, 2048)
                      for j, value in enumerate(coefficients)) % 2048
        assert residue == (residue_one+64*derivative) % 2048
        parity = int(name in ("w", "z"))
        assert (residue-SHIFTS[name]) % 2048 == 1024*parity
        records.append({"output": name, "numerator_at_one_mod_2048": residue_one,
                        "derivative_at_one_mod_32": derivative,
                        "numerator_at_65_mod_2048": residue, "output_parity": parity})
    return records


def family(u: int) -> dict:
    if u < MINIMUM_PARAMETER or u % 2048 != 65:
        raise ValueError("u must be at least 2^32 and congruent to 65 modulo 2048")
    r = u**4+2
    base = predecessor_family(r)
    values = {name: evaluate(poly, u) for name, poly in output_polynomials().items()}
    assert all(value.denominator == 1 for value in values.values())
    H_t, H_q, w, z = (int(values[name]) for name in ("H_t", "H_q", "w", "z"))
    m, M, a, t, q = (base[name] for name in ("minimum", "maximum", "a", "t", "q"))
    edges = list(base["edges"])
    for branch, source, target in (("O", t, H_t), ("E", H_t, w),
                                   ("O", q, H_q), ("E", H_q, z)):
        radicand = source**(3 if branch == "O" else 1)
        remainder = radicand-target*target
        assert source % 2 == int(branch == "O")
        assert isqrt(radicand) == target and 0 < remainder < 2*target+1
        edges.append({"branch": branch, "source": source, "target": target,
                      "square_remainder": remainder, "upper_margin": 2*target+1-remainder,
                      "actual_guard": True})
    d = z-w
    checks = {
        "all_inherited_checks": all(base["checks"].values()),
        "minimum_above_both_cutoffs": m > 2**768,
        "new_even_peaks_and_odd_endpoints": H_t % 2 == H_q % 2 == 0 and w % 2 == z % 2 == 1,
        "full_anchor_order": m < w < z < a < base["b_low"] < base["b_high"] < t < q
                             < base["h"] < m*m < base["s_low"] < base["s_high"]
                             < H_t < H_q < M < m**3,
        "exact_gap_polynomial": 64*d == 216*u**11+1188*u**7+1863*u**3-3,
        "gap_lower_r_power": d**4 > 16*r**11,
        "gap_upper_r_power": d**4 < 256*r**11,
        "gap_above_m_power": d**24 > m**11,
        "gap_even_at_least_eight": d >= 8 and d % 2 == 0,
        "mixed_gap_upper_without_allowance": (32*d)**32*m**5 < (27*(base["b_low"]-a))**32,
        "gap_below_predecessor_gap": d <= base["b_low"]-a-2,
        "seam_t_upper": t**3+2 <= (w*(w+2))**2,
        "seam_q_upper": q**3+2 <= (z*(z+2))**2,
        "seam_M_upper": M+2 <= (t+1)**2,
        "seam_minimum_power": z**8 <= m**9,
    }
    assert all(checks.values()), checks
    return {"u": u, "r": r, "minimum": m, "maximum": M,
            "a": a, "h": base["h"], "t": t, "q": q,
            "b_low": base["b_low"], "b_high": base["b_high"],
            "s_low": base["s_low"], "s_high": base["s_high"],
            "H_t": H_t, "H_q": H_q, "w": w, "z": z, "gap": d,
            "minimum_bits": m.bit_length(), "gap_bits": d.bit_length(),
            "edges": edges, "checks": checks,
            "inherited_checks": base["checks"],
            "negative_loss_upper_bound": base["negative_loss_upper_bound"],
            "positive_loss_lower_bound": base["positive_loss_lower_bound"],
            "both_faces_in_one_cycle_asserted": False,
            "guarded_original_rectangle_asserted": True,
            "cycle_adjacency_asserted": False, "periodic_orbit_asserted": False}


def report() -> dict:
    return {
        "decision": "CLOSE",
        "scope": "finite initialized return-seam cells do not force a mixed-loss sign",
        "parameter_domain": "u>=2^32, u=65 mod2048, r=u^4+2",
        "fixed_parameters": list(FIXED_PARAMETERS),
        "congruence_certificates": congruence_certificates(),
        "uniform_coefficient_certificates": coefficient_certificates(),
        "inherited_coefficient_certificates": predecessor_certificates(),
        "controls": [family(u) for u in FIXED_PARAMETERS],
        "source_search": False, "orbit_search": False, "raised_floor": False,
        "new_actual_cycle_bound": False, "no_cycle_proved": False,
        "new_lean_or_paper_claim": False,
        "proof_owner": "docs/problems/juggler_cycle_return_seam.md",
        "proof_status": "AI-assisted written proof with exact polynomial replay; not Lean or independent human review",
    }


def main() -> None:
    data = report()
    destination = DATA_ROOT/"cycle_return_seam/summary.json"
    destination.parent.mkdir(parents=True, exist_ok=True)
    destination.write_text(json.dumps(data, indent=2)+"\n", encoding="utf-8")
    print(json.dumps({"decision": data["decision"],
                      "fixed_parameters": data["fixed_parameters"],
                      "actual_edges_checked": sum(len(row["edges"]) for row in data["controls"]),
                      "uniform_new_polynomials": len(data["uniform_coefficient_certificates"]),
                      "new_actual_cycle_bound": False}, indent=2))


if __name__ == "__main__":
    main()
