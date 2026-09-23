"""Independent finite enumerations and mathematical invariants of the MCP paper audits."""
from fractions import Fraction as F
from itertools import product
import json
from pathlib import Path
import sys

import pytest

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "tools"))
from arb_paper_audit_core.beatty import exact_survivor_counts, finite_profile_integral_parts
from arb_paper_audit_core.client import Bounds
from arb_paper_audit_core.paper_a import DENOMINATORS, continued_fraction_denominators, digit_sum
from arb_paper_audit_core.paper_d import floor_sum, upper_window_candidates


def report(paper):
    programme = "collatz" if paper in ("d", "e") else "juggler"
    return json.loads((ROOT / f"data/research/{programme}/arb_paper_audit/{paper}.json").read_text())


def test_floor_sum_against_direct_integer_sum():
    for n, modulus, a, b in product(range(9), range(1, 10), range(12), range(6)):
        assert floor_sum(n, modulus, a, b) == sum((a*i+b)//modulus for i in range(n))


@pytest.mark.parametrize("n,a,modulus,width", [(200, 117, 257, 17), (0, 2, 5, 1),
    (1000, 2, 9, 8), (63, 0, 7, 3), (70, 14, 7, 2), (500, 11, 13, 1)])
def test_upper_window_enumeration_includes_boundaries(n, a, modulus, width):
    assert upper_window_candidates(n, a, modulus, width) == [
        k for k in range(1, n+1) if (k*a)%modulus >= modulus-width]


def test_widening_lower_rotation_interval_cannot_omit_real_hits():
    # Exhaustive small rational analogue of the actual irrational enclosure argument.
    for x, epsilon, maximum in product((F(37, 101), F(5, 13), F(103, 127)),
                                       (F(1, 20), F(1, 10)), (20, 60)):
        scale = 2**12
        a = (x*scale).__floor__()
        width = (epsilon*scale).__ceil__()+maximum
        candidates = upper_window_candidates(maximum, a, scale, width)
        actual = [k for k in range(1, maximum+1)
                  if 0 < (k*x).__ceil__()-k*x < epsilon]
        assert set(actual) <= set(candidates)


def test_integer_survivor_recurrence_against_all_words():
    counts = exact_survivor_counts(12)
    for n in range(13):
        total = 0
        for word in product((0, 1), repeat=n):
            total += all(3**sum(word[:j]) > 2**j for j in range(1, n+1))
        assert counts[n] == total


@pytest.mark.parametrize("lo,hi", [(F(-1,3), F(1,7)), (F(-2), F(-2)),
                                   (F(1,10**60), F(1,10**59)), (F(10**40),F(10**40+1))])
def test_decimal_boxes_are_outward_and_fit_mcp(lo, hi):
    values = Bounds(lo,hi).box()
    assert F(values[0]) <= lo <= hi <= F(values[1])
    assert all(len(value) <= 128 for value in values)


def test_profile_cells_cover_every_phase_and_reject_uncertain_order():
    atoms = [{"phase": Bounds(F(3,4),F(3,4)), "weight": Bounds(F(2),F(2))},
             {"phase": Bounds(F(1,4),F(1,4)), "weight": Bounds(F(1),F(1))}]
    parts = finite_profile_integral_parts(atoms)
    assert [(w.lo,h.lo) for w,h in parts] == [(F(1,4),F(1)),(F(1,2),F(2)),(F(1,4),F(4))]
    atoms[0]["phase"] = Bounds(F(0),F(1))
    with pytest.raises(ArithmeticError):
        finite_profile_integral_parts(atoms)


@pytest.mark.parametrize("paper", ["a", "b", "c", "d", "e", "beatty"])
def test_saved_mcp_evidence_has_no_unknown_or_failed_computation(paper):
    data = report(paper)
    assert data["paper_unchanged_during_run"]
    assert data["mcp_call_count"] == len(data["checks"]) > 0
    for call in data["checks"].values():
        result = call["result"]
        assert result.get("status") != "unresolved"
        assert result["backend"]["python_flint"]
        assert "src/research_engine/arb_expressions.py" in result["source_sha256"]
        if call["tool"] == "arb_evaluate":
            bounds = Bounds.read(result["enclosure"])
            assert bounds.lo <= bounds.hi
        elif call["tool"] in ("arb_compare", "arb_paper_c_rate"):
            assert type(result["holds"]) is bool
        elif call["tool"] == "arb_production_root":
            bounds = Bounds.read(result["root"])
            assert 0 <= bounds.hi-bounds.lo <= F(1,10**24)


def test_paper_a_exhaustive_counts_and_new_cutoff():
    data = report("a")
    summary = data["summary"]
    for row in summary["floor_audits"]:
        assert sum(row[k] for k in ("crude_exclusions","parity_exclusions","walk_exclusions"))+1 == row["lengths_checked"]
        assert row["not_excluded"] == [row["lengths_checked"]]
    beta = Bounds.read(data["checks"]["beta"]["result"]["enclosure"])
    assert continued_fraction_denominators(beta, DENOMINATORS[-1]) == DENOMINATORS
    cutoff = summary["upper_cell"]["least_integer_excluded_by_scalar_bound"]
    lam = Bounds.read(summary["upper_cell"]["lambda"])
    at = Bounds.read(data["checks"][f"upper_cell_charge_{cutoff}"]["result"]["enclosure"])
    before = Bounds.read(data["checks"][f"upper_cell_charge_{cutoff-1}"]["result"]["enclosure"])
    assert at.hi < lam.lo <= lam.hi < before.lo
    assert cutoff == 487011720 < 520000000


def test_paper_d_all_lengths_are_covered_by_negative_witnesses():
    data = report("d")["summary"]
    sieve = data["sieve"]
    assert upper_window_candidates(sieve["maximum_length"],int(sieve["rotation_numerator"]),
                                   int(sieve["scale"]),int(sieve["window_width"])) == sieve["candidates"]
    assert data["differences_from_recorded_table"] == []
    for row in data["rows"][:61]:
        assert row["survivors"] == []
        assert len(row["witnesses"]) == row["admissible_count"]
        assert len({w["K"] for w in row["witnesses"]}) == row["admissible_count"]
        assert all(F(w["margin_bits"]["upper"]) < 0 for w in row["witnesses"])
    assert data["rows"][61]["admissible_count"] == 120
    assert [s["K"] for s in data["rows"][61]["survivors"]] == [83130157078217]
    assert len(data["rows"][61]["survivors"][0]["all_valley_branches"]) == 62


def test_paper_e_stronger_exponent_has_an_exact_integer_certificate():
    assert 5059**25000 > 2**423 * 5000**25000
    gamma = Bounds.read(report("e")["summary"]["growth_exponent"])
    assert F(21,25) < F(423,500) < gamma.lo < gamma.hi < F("0.846208")


def test_paper_b_printed_rounding_is_certified():
    for item in report("b")["summary"]["constants"].values():
        center = F(item["printed"])
        radius = F(1, 2*10**len(item["printed"].split(".")[1]))
        bounds = Bounds.read(item["enclosure"])
        assert center-radius <= bounds.lo <= bounds.hi <= center+radius
        assert item["rounding_agrees"]


def test_paper_c_checks_both_sides_of_each_recorded_boundary():
    data = report("c")
    assert len(data["summary"]["roots"]) == 12
    for kind, table in data["summary"]["rate_boundaries"].items():
        for q, depth in table.items():
            for C, expected in ((depth-1, False), (depth, True)):
                check = data["checks"][f"{kind}_{q}_{C}"]
                assert check["arguments"]["C"] == C
                assert check["result"]["holds"] is expected


def test_beatty_tail_and_moment_use_the_total_mass_not_a_fitted_tail():
    data = report("beatty")["summary"]
    mass = Bounds(F(0),F(0))
    for atom in data["atoms"]:
        weight = Bounds.read(atom["weight"])
        assert weight.lo > 0
        mass = mass+weight
    total = Bounds.read(data["total_mass"])
    tail = Bounds.read(data["certified_remaining_mass"])
    assert tail == total-mass and tail.lo > 0
    head = Bounds.read(data["finite_head_moment"])
    moment = Bounds.read(data["full_two_thirds_moment"])
    assert moment.lo == head.lo
    assert moment.hi == head.hi+F(2,3)*tail.hi
    assert len(data["atoms"]) == 256
    assert data["atoms"][0]["count"] == "1"
