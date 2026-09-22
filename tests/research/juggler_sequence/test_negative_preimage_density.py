"""Residue-model symmetry, exact tree splits, and the missing height correction."""
from __future__ import annotations

import json
from pathlib import Path
import re
from math import log2
from fractions import Fraction

import pytest

import research.juggler_sequence.negative_preimage_density as npd


def test_signed_grid_uses_the_same_exact_table_as_the_kernel_proof() -> None:
    path = Path(__file__).resolve().parents[3] / "formal/Problems/Collatz/PreimageGrid.lean"
    text = path.read_text(encoding="utf-8")
    table = text.split("def table : List ℕ :=", 1)[1].split("def rung", 1)[0]
    assert tuple(map(int, re.findall(r"\d+", table))) == npd.GRID_RUNGS
    assert 2 ** 291 * 8193 ** 498 < 12288 ** 498
    for t in range(150):
        assert npd.grid_cap(t + 100) == 4 * npd.grid_cap(t)
        assert 8193 * npd.grid_cap(t + 29) <= 12288 * npd.grid_cap(t)
        assert 16386 * npd.grid_cap(t) <= 12288 * npd.grid_cap(t + 21)


def test_signed_grid_cutoffs_and_measure_on_fertile_integer_roots() -> None:
    for a in (*range(4096, 4300, 3), 1_000_000, 10 ** 30):
        assert a % 3 == 1
        b = (2 * a + 1) // 3
        for t in range(50):
            assert npd.grid_cap(t + 129) * b <= npd.grid_cap(t + 100) * a
            assert npd.grid_cap(t + 79) * (2 * b) <= npd.grid_cap(t + 100) * a
            parent = npd.grid_measure(t + 100, a)
            assert npd.grid_measure(t, 4 * a) + 4 <= parent
            assert npd.grid_measure(t + 79, 2 * b) + 3 <= parent
            assert npd.grid_measure(t + 129, b) + 1 <= parent


def test_signed_grid_requires_a_boundary_argument() -> None:
    # The pointwise cutoff fails at a small nonperiodic root; the new theorem
    # does not silently replace the original false homogeneous comparison.
    assert npd.grid_cap(129) * 13 > npd.grid_cap(100) * 19
    # The threshold alone is not a backward-closed domain for induction.
    assert npd.g_minus(2731) == 4096 and 2731 < 4096
    with pytest.raises(ValueError):
        npd.grid_cap(-1)
    with pytest.raises(ValueError):
        npd.grid_measure(0, 0)


def test_actual_capped_subtrees_satisfy_both_signed_split_bounds() -> None:
    # Small common cutoffs exercise genuine trees, independently of the grid
    # algebra. These roots all reach the known cycles without returning.
    for a in range(4096, 4114, 3):
        seen = set()
        n = a
        while n not in seen:
            seen.add(n)
            n = npd.g_minus(n)
        assert n != a
        b = (2 * a + 1) // 3
        for cutoff in (4 * a, 9 * a):
            parent = npd.truncated_tree(npd.preimages_minus, a, cutoff)
            even = npd.truncated_tree(npd.preimages_minus, 4 * a, cutoff)
            odd = npd.truncated_tree(npd.preimages_minus, b, cutoff)
            doubled = npd.truncated_tree(npd.preimages_minus, 2 * b, cutoff)
            assert even + odd <= parent
            assert even + doubled <= parent


def test_the_fertile_classes_are_the_ones_with_an_odd_preimage() -> None:
    """3x+1 gains an odd preimage exactly at 2 mod 3, and 3n-1 exactly at 1 mod 3. The two
    classes are negatives of each other mod 3, which is the whole transposition in miniature.
    """
    for z in range(2, 3000):
        assert (len(npd.preimages_plus(z)) == 2) == (z % 3 == 2), z
        assert (len(npd.preimages_minus(z)) == 2) == (z % 3 == 1), z
    assert npd.PLUS.fertile == 2 and npd.MINUS.fertile == 1
    assert (-npd.PLUS.fertile) % 3 == npd.MINUS.fertile


def test_shifted_height_controls_guarded_two_step_ancestor_paths() -> None:
    """Exercise the Lean block example on actual paths, including cycle roots.

    The O branch is available only when integral. Counting every formal
    binary word would be wrong even though its real height bound holds.
    """
    used_odd = skipped_odd = 0
    for root in range(1, 81):
        frontier = [(root, Fraction(1), root)]
        for _ in range(8):
            following = []
            for parent, factor, path_max in frontier:
                predecessors = npd.preimages_minus(parent)
                skipped_odd += len(predecessors) == 1
                for middle in predecessors:
                    child = 2 * middle
                    assert npd.g_minus(npd.g_minus(child)) == parent
                    odd_branch = middle % 2 == 1
                    used_odd += odd_branch
                    next_factor = factor * (Fraction(4, 3) if odd_branch else 4)
                    next_max = max(path_max, middle, child)
                    assert child + 2 <= next_factor * (root + 2)
                    assert next_max + 2 <= next_factor * (root + 2)
                    following.append((child, next_factor, next_max))
            frontier = following
    assert used_odd > 0 and skipped_odd > 0


def test_the_odd_preimage_is_odd_and_lands_where_the_trichotomy_says() -> None:
    """For 3n-1 with a = 1 mod 3, c = (2a+1)/3 is an odd integer, and a mod 9 decides whether
    c is fertile (1 mod 9), dead (4 mod 9) or needs doubling (7 mod 9)."""
    seen = set()
    for a in range(1, 4000):
        if a % 3 != 1:
            continue
        c = (2 * a + 1) // 3
        assert 3 * c == 2 * a + 1 and c % 2 == 1, a
        seen.add((a % 9, c % 3))
    assert seen == {(1, 1), (4, 0), (7, 2)}, seen


def test_negation_carries_one_inequality_system_onto_the_other() -> None:
    """Finite exact check: m -> -m mod 3^k is a bijection of the fertile
    classes carrying every production index and every lambda exponent across. Checked over
    all 3^(k-1) classes for k up to 9, which is 6561 classes at the top."""
    for k in range(2, 10):
        rep = npd.negation_is_an_isomorphism(k)
        assert rep["bijection_holds"], (k, rep["mismatches"])
        assert rep["classes"] == 3 ** (k - 1)


def test_identity_and_doubling_do_not_supply_the_negation_relabelling() -> None:
    """Known-bad input: the identity relabelling must NOT carry one system onto the other,
    or the test above would pass for a reason that has nothing to do with negation."""
    k = 4
    p = 3 ** k
    same = [m for m in npd.PLUS.classes(k) if m % 3 == npd.MINUS.fertile]
    assert same == [], "the fertile classes must be disjoint, so identity cannot be a map"
    # and doubling, the other obvious candidate, sends fertile to fertile but breaks a term
    broken = 0
    for m in npd.PLUS.classes(k):
        mm = (2 * m) % p
        if mm % 3 != npd.MINUS.fertile:
            broken += 1
            continue
        four, odd = npd.PLUS.production(m, k)
        four_m, odd_m = npd.MINUS.production(mm, k)
        if four_m != (2 * four) % p or (odd is None) != (odd_m is None):
            broken += 1
    assert broken > 0, "doubling must fail somewhere"


def test_the_two_systems_solve_to_the_same_exponent() -> None:
    """Independent confirmation of the bijection: solve both and compare. The solver is a
    Collatz-Wielandt iteration, not a linear program; a scipy linear program written from
    the same inequalities gave 0.4366, 0.6113, 0.6891, 0.7336, 0.7608, 0.7826 and 0.8032
    for k = 2 to 8, which these reproduce."""
    expected = {2: 0.4366, 3: 0.6113, 4: 0.6891, 5: 0.7336}
    for k, gamma in expected.items():
        lp, lm = npd.best_lambda(npd.PLUS, k), npd.best_lambda(npd.MINUS, k)
        assert abs(lp - lm) < 1e-7, (k, lp, lm)
        assert round(log2(lp), 4) == gamma, (k, log2(lp))


def test_the_published_exponents_are_this_solver_truncated() -> None:
    """Krasikov 1989 obtained 0.43 from k = 2 and Krasikov-Lagarias 0.84 from k = 11.
    A published exponent is a valid lower bound, so it is the computed value truncated
    downward, not rounded: 0.4366 gives 0.43 and 0.8418 gives 0.84. Reproducing both is what
    checks the model's numerical calibration. It neither certifies an untested
    solver run nor establishes a minus-map counting theorem."""
    gamma2 = log2(npd.best_lambda(npd.PLUS, 2))
    assert int(gamma2 * 100) / 100 == npd.PUBLISHED["krasikov_1989_k2"], gamma2
    k11 = npd.HIGH_K[11]
    assert int(k11 * 100) / 100 == npd.PUBLISHED["krasikov_lagarias_2003_k11"], k11
    assert npd.HIGH_K[9] < npd.HIGH_K[10] < npd.HIGH_K[11], npd.HIGH_K


def test_feasibility_is_an_interval_in_lambda() -> None:
    """One production carries the exponent alpha - 1 > 0 and so grows with lambda, so
    monotonicity is not free and the bisection needs it checked."""
    assert npd.feasibility_is_an_interval(npd.PLUS, 3)
    assert npd.feasibility_is_an_interval(npd.MINUS, 3)


def test_the_backward_tree_splits_exactly_for_3n_minus_1() -> None:
    """pi*_a(x) = 2 + pi*_4a(x) + pi*_c(x) with c = (2a+1)/3, for every fertile a below 400
    that is not on a cycle."""
    rep = npd.split_identity_report()
    assert rep["checked"] >= 350
    assert rep["failures"] == 0, rep["examples"]
    assert rep["plus_preimage_expression_nonintegral"] == rep["checked"]


def test_known_cycle_members_expose_the_noncycle_hypothesis() -> None:
    """The known cycle census exposes failure of the unrestricted tree split.

    The fifteen members are from three known cycles, not an exhaustive theorem.
    """
    assert npd.cycle_members_break_the_identity() > 0
    cycles = npd.negative_cycle_members()
    assert len(cycles) == 15
    assert {1, 5, 7, 10, 17} <= cycles


def test_small_root_orbits_form_a_finite_closed_barrier() -> None:
    report = npd.small_root_barrier_report()
    assert report["contains_all_small_starts"]
    assert report["forward_closed"]
    assert report["all_states_below_barrier"]
    assert report["closed_union_size"] == 6418
    assert report["max_steps_to_seed"] == 114
    assert report["longest_start"] == 3975
    assert report["max_height"] == 417718
    # A superficially plausible smaller barrier is false.
    assert (1 << 18) < report["max_height"] < (1 << 19)
    n = report["height_witness_start"]
    for _ in range(114):
        if n == report["max_height"]:
            break
        n = npd.g_minus(n)
    assert n == 417718


def test_strict_grid_certificate_all_integer_inequalities() -> None:
    certificate = json.loads(npd.GRID_CERTIFICATE_PATH.read_text(encoding="utf-8"))
    report = npd.verify_grid_certificate(certificate)
    assert report["inequalities_checked"] == 177147
    assert report["all_integer_inequalities_hold"]
    assert report["failed_residues"] == []
    assert report["minimum_weight"] == 7307142888
    assert report["maximum_weight"] == 10**12
    assert report["rate_strictly_above_21_over_25"]
    # The theorem's rate comparison is an integer inequality, independent
    # of the floating-point diagnostic field in the stored artifact.
    certificate["exponent"] = -999
    assert npd.verify_grid_certificate(certificate) == report


def test_strict_grid_verifier_rejects_corrupted_positive_weights() -> None:
    certificate = json.loads(npd.GRID_CERTIFICATE_PATH.read_text(encoding="utf-8"))
    # Residue 4 has only the 4a production. Giving it maximal weight makes
    # its inequality impossible because the rate is strictly greater than one.
    certificate["weights"][1] = certificate["maximum"]
    report = npd.verify_grid_certificate(certificate)
    assert not report["all_integer_inequalities_hold"]
    assert 4 in report["failed_residues"]
    certificate["weights"][1] = 0
    with pytest.raises(ValueError, match="positive integer"):
        npd.verify_grid_certificate(certificate)
    certificate["weights"].pop()
    with pytest.raises(ValueError, match="dimensions"):
        npd.verify_grid_certificate(certificate)


@pytest.mark.parametrize("k", [2, 3, 4, 12])
def test_signed_grid_productions_balance_the_whole_weight_table(k: int) -> None:
    """Use actual predecessor residues, independently of Lean's index formulas."""
    modulus, size = 3**k, 3 ** (k - 1)
    if k == 12:
        certificate = json.loads(npd.GRID_CERTIFICATE_PATH.read_text(encoding="utf-8"))
        weights = certificate["weights"]
    else:
        weights = [(i * i + 17 * i + 13) % 97 + 1 for i in range(size)]
    third = size // 3
    lift_sum = sum(min(weights[j + r * third] for r in range(3)) for j in range(third))
    assert 3 * lift_sum <= sum(weights)
    for sign, fertile, odd_class, doubled_class in [(1, 2, 8, 2), (-1, 1, 1, 7)]:
        four_sum = odd_sum = doubled_sum = 0
        for m in range(fertile, modulus, 3):
            four_sum += weights[((4 * m) % modulus - fertile) // 3]
            if m % 9 not in (odd_class, doubled_class):
                continue
            numerator = 2 * m - sign if m % 9 == odd_class else 4 * m - 2 * sign
            assert numerator % 3 == 0
            child = (numerator // 3) % size
            minimum = min(weights[(child + r * size - fertile) // 3] for r in range(3))
            if m % 9 == odd_class:
                odd_sum += minimum
            else:
                doubled_sum += minimum
        assert four_sum == sum(weights)
        assert odd_sum == doubled_sum == lift_sum
    if k == 12:
        p, q, total = certificate["p"], certificate["q"], sum(weights)
        assert total * p**100 * q**29 <= total * q**129 + (p**129 + p**79 * q**50) * lift_sum


def test_strict_grid_mean_ceiling_uses_exact_integer_bounds() -> None:
    for p, q in [(5069, 5000), (507, 500)]:
        assert 3 * q**129 + p**129 + p**79 * q**50 < 3 * p**100 * q**29
    assert 5069**50 < 2 * 5000**50
    assert 2 * 500**50 < 507**50
    assert 5069**5000 < 2**99 * 5000**5000


def test_the_recorded_payload_matches_a_fresh_run() -> None:
    fresh = npd.probe_payload(k_lp=4, k_bijection=5)
    assert fresh["bijection_holds_every_k"]
    assert fresh["classification"]["label"] == npd.CLASS_SIGNED_GRID_DENSITY
    stored = json.loads(npd.JSON_PATH.read_text(encoding="utf-8"))
    assert stored["classification"]["label"] == npd.CLASS_SIGNED_GRID_DENSITY
    assert stored["classification"]["established_minus_exponent"] == 0.84
    assert fresh["height_comparison"] == stored["height_comparison"]
    assert fresh["small_root_barrier"] == stored["small_root_barrier"]
    assert fresh["grid_certificate"] == stored["grid_certificate"]
    assert stored["bijection_holds_every_k"] is True
    assert stored["split_identity"]["failures"] == 0
    for k in ("2", "3", "4"):
        assert stored["exponents"][k]["agree_to_1e_7"] is True
        assert abs(stored["exponents"][k]["gamma_3x_plus_1"]
                   - fresh["exponents"][k]["gamma_3x_plus_1"]) < 1e-6


@pytest.mark.parametrize("seed", [1, 5, 17])
def test_the_three_cycles_are_the_ones_paper_d_names(seed: int) -> None:
    z, path = seed, []
    while z not in path:
        path.append(z)
        z = npd.g_minus(z)
    cyc = path[path.index(z):]
    assert len(cyc) in (1, 3, 11), (seed, cyc)


def test_signed_height_comparisons_have_opposite_directions() -> None:
    for a in range(1, 301):
        if a % 3 == 1:
            c = (2 * a + 1) // 3
            assert npd.g_minus(c) == a
            assert Fraction(c) > Fraction(2 * a, 3)
            for x in (4 * a, 11 * a + 7):
                nominal_ratio = Fraction(x, a) * Fraction(3, 2)
                assert Fraction(x, c) == nominal_ratio / (1 + Fraction(1, 2 * a))
                assert nominal_ratio * c > x
        elif a % 3 == 2:
            c = (2 * a - 1) // 3
            assert npd.t_plus(c) == a
            assert Fraction(c) < Fraction(2 * a, 3)


def test_nominal_budget_includes_an_actual_excluded_ancestor() -> None:
    # Independent forward enumeration checks the backward BFS at both cutoffs.
    def count_forward(a: int, cutoff: int) -> int:
        total = 0
        for n in range(1, cutoff + 1):
            seen = set()
            while 1 <= n <= cutoff and n not in seen:
                if n == a:
                    total += 1
                    break
                seen.add(n)
                n = npd.g_minus(n)
        return total

    row = npd.height_comparison_report()
    assert row["nominal_child_cutoff"] == "4017/38"
    assert row["correction_factor"] == "39/38"
    assert row["actual_child_count"] == count_forward(13, 103) == 12
    assert row["nominal_child_count"] == count_forward(13, 105) == 13
    path = row["ancestor_path"]
    assert all(npd.g_minus(a) == b for a, b in zip(path, path[1:]))
    assert row["cutoff"] < path[0] <= Fraction(row["nominal_child_cutoff"])
    assert npd.truncated_tree(npd.preimages_minus, 13, 12) == 0
    assert npd.truncated_tree(npd.preimages_minus, 0, 12) == 0
