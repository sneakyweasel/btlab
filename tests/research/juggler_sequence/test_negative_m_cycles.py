"""m-cycles of the 3x-1 map: the identities are exact, the cycles that exist pass, and the
table at the verified floor excludes a recorded range of m."""

from __future__ import annotations

import json
from fractions import Fraction

import pytest
from mpmath import mp, mpf, log

from research.juggler_sequence import negative_m_cycles as nm
from research.juggler_sequence.lean_paths import BRANCHES_ROOT


def test_dossier_exists() -> None:
    assert (BRANCHES_ROOT / "juggler_negative_m_cycles.md").is_file()


def test_run_identity_and_run_length_are_exact() -> None:
    """``g^k(y) - 1 = (3/2)^k (y - 1)`` along the run and the run has exactly ``v_2(y-1)``
    odd steps, on every odd ``3 ≤ y < 4000``; the reciprocal sum of a run is at most
    ``1/(y - 1)``."""
    res = nm.run_identity_checks(4000)
    assert res["checked"] == 1999
    assert res["bound_holds"]
    assert res["worst_recip_times_u"] < 1


def test_cycle_equation_is_exact_on_the_three_cycles() -> None:
    """``3^o prod (1 - 1/(3y)) = 2^K`` over the odd elements, in exact rationals."""
    for cycle in nm.CYCLES:
        assert nm.cycle_data(cycle)["cycle_equation_holds"], cycle
    d17 = nm.cycle_data(nm.CYCLES[2])
    assert (d17["K"], d17["o"], d17["m"]) == (11, 7, 2)
    assert d17["minima"] == [17, 41]
    assert d17["runs"] == {17: 4, 41: 3}
    d5 = nm.cycle_data(nm.CYCLES[1])
    assert (d5["K"], d5["o"], d5["m"]) == (3, 2, 1)


def test_negative_lemma_eight_is_tight_at_the_known_minima() -> None:
    """``y ≥ 2^a + 1`` with ``a = v_2(y - 1)``, with equality at 5 and 17."""
    assert nm.run_length(5) == 2 and 5 == 2**2 + 1
    assert nm.run_length(17) == 4 and 17 == 2**4 + 1
    assert nm.run_length(41) == 3 and 41 >= 2**3 + 1


def test_chaining_is_sharp_on_the_seventeen_cycle() -> None:
    """``u' < u^delta / 2`` between successive local minima: 16 -> 40 against 40.5."""
    with mp.workdps(30):
        d = log(3) / log(2)
        assert 40 < 16 ** d / 2 < 40.6
        assert 16 < 40 ** d / 2


def test_the_cycles_that_exist_pass_the_template() -> None:
    """The inequalities the exclusion rests on hold on the real cycles, with the floor set
    at their own least element; the tower bound is met with room, the cycle equation exactly."""
    for c in nm.known_cycles_survive():
        assert c["cycle_equation_holds"], c
        assert c["o_matches_ceil"], c
        assert c["finance_holds"], c
        assert c["tower_holds"], c


def test_rhin_ceiling_is_a_genuine_ceiling() -> None:
    """Beyond ``K3(m)`` the chaining beats ``2 e^{6.1256} m K^{13.3}``; just below it does
    not. Checked at m = 1, 5, 20."""
    with mp.workdps(30):
        c0 = 2 * mp.e ** (nm.RHIN_EXPONENT * nm.RHIN_OFFSET)
        for m in (1, 5, 20):
            K = nm.K3(m)
            assert 2 ** nm.log2_xmin_lower(K, m) >= c0 * m * mpf(K) ** nm.RHIN_EXPONENT
            assert 2 ** nm.log2_xmin_lower(max(K // 2, 2), m) < c0 * m * mpf(max(K // 2, 2)) ** nm.RHIN_EXPONENT


def test_admissible_lengths_are_exactly_the_expanding_near_convergents() -> None:
    """The walk agrees with a direct scan at a coarse ``eps``."""
    with mp.workdps(60):
        eps = mpf("0.002")
        got = nm.admissible_lengths(eps, 20000)
        x = nm._x()
        want = [K for K in range(1, 20001) if 1 - nm.frac(K * x) < eps]
        assert got == want
        assert 11 in want or 11 not in got  # the 17-cycle length 11 sits at Lambda = log(2187/2048)


def test_table_at_the_floor_excludes_the_recorded_range() -> None:
    """At ``2^44`` the tables exclude every m up to the recorded value, and the archived
    summary agrees with a fresh computation of the first rows."""
    data = json.loads(nm.JSON_PATH.read_text(encoding="utf-8"))
    at = data["tables"]["2^44"]
    M = at["excluded_through"]
    assert M >= 20, M
    assert data["classification"]["excluded_through_at_floor"] == M
    for r in at["rows"][:3]:
        fresh = nm.row(r["m"], 2**44)
        assert fresh["excluded"] == r["excluded"]
        assert fresh["K3_rhin_ceiling"] == r["K3_rhin_ceiling"]
        assert fresh["K0_least_admissible"] == r["K0_least_admissible"]


def test_a_higher_floor_excludes_at_least_as_much() -> None:
    data = json.loads(nm.JSON_PATH.read_text(encoding="utf-8"))
    ms = [data["tables"][lbl]["excluded_through"] for lbl in ("2^40", "2^44", "2^48", "2^60", "2^68")]
    assert ms == sorted(ms), ms


def test_m_free_survivor_at_the_floor_is_the_recorded_period() -> None:
    data = json.loads(nm.JSON_PATH.read_text(encoding="utf-8"))
    first = data["m_free_survivors_at_floor"][0]
    assert (first["K"], first["o"]) == (16483927, 10400200)
