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
    """From ``K3(m)`` on the chaining beats ``2 e^{13.3 RHIN_OFFSET} m K^{13.3}`` (``2 m K^{13.3}``
    with the offset at zero); at ``K3(m) - 1`` it does not, so the ceiling is the least integer
    of its definition and not one more (the rounding the first version had). Checked at
    m = 1, 5, 20, 49."""
    with mp.workdps(40):
        c0 = 2 * mp.e ** (nm.RHIN_EXPONENT * nm.RHIN_OFFSET)
        for m in (1, 5, 20, 49):
            K = nm.K3(m)
            assert 2 ** nm.log2_xmin_lower(K, m) >= c0 * m * mpf(K) ** nm.RHIN_EXPONENT
            assert 2 ** nm.log2_xmin_lower(K - 1, m) < c0 * m * mpf(K - 1) ** nm.RHIN_EXPONENT
            assert 2 ** nm.log2_xmin_lower(max(K // 2, 2), m) < c0 * m * mpf(max(K // 2, 2)) ** nm.RHIN_EXPONENT
        assert nm.K3(1) == 155 and nm.K3(49) == 9921719447060


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
    """At the floor ``2^FLOOR_LOG2`` (51 since the GPU sweep of 21 September 2026) the tables
    exclude every m up to the recorded value, and the archived
    summary agrees with a fresh computation of the first rows."""
    data = json.loads(nm.JSON_PATH.read_text(encoding="utf-8"))
    at = data["tables"][f"2^{nm.FLOOR_LOG2}"]
    M = at["excluded_through"]
    assert M >= 20, M
    assert data["classification"]["excluded_through_at_floor"] == M
    for r in at["rows"][:3]:
        fresh = nm.row(r["m"], 2**nm.FLOOR_LOG2)
        assert fresh["excluded"] == r["excluded"]
        assert fresh["K3_rhin_ceiling"] == r["K3_rhin_ceiling"]
        assert fresh["K0_least_admissible"] == r["K0_least_admissible"]


def test_a_higher_floor_excludes_at_least_as_much() -> None:
    """The ladder, as archived: 2^44 to 2^48 give 49, 2^49 gives 54, 2^50 56, 2^51 58, 2^56 63,
    2^60 68, 2^68 82 (the rows at 2^49 to 2^51 were also sieved independently on 21 September
    2026, with the same answers)."""
    data = json.loads(nm.JSON_PATH.read_text(encoding="utf-8"))
    labels = ("2^40", "2^44", "2^48", "2^49", "2^50", "2^51", "2^56", "2^60", "2^68")
    ms = [data["tables"][lbl]["excluded_through"] for lbl in labels]
    assert ms == sorted(ms), ms
    assert dict(zip(labels, ms)) == {"2^40": 44, "2^44": 49, "2^48": 49, "2^49": 54, "2^50": 56, "2^51": 58,
                                     "2^56": 63, "2^60": 68, "2^68": 82}, ms


def test_m_free_survivor_at_the_floor_is_the_recorded_period() -> None:
    """The m-free period bound: 16483927 at 2^44 (Paper A, Remark 5.20), 85137581 at 2^51."""
    from research.juggler_sequence.collatz_finance_mirror import negative_cycle_survivors

    data = json.loads(nm.JSON_PATH.read_text(encoding="utf-8"))
    first = data["m_free_survivors_at_floor"][0]
    assert data["floor_log2"] == nm.FLOOR_LOG2 == 51
    assert (first["K"], first["o"]) == (85137581, 53715833)
    at44 = negative_cycle_survivors(mpf(2**44), 20_000_000)[0]
    assert (at44["K"], at44["o"]) == (16483927, 10400200)


def test_the_theorem_at_the_new_floor_and_the_old_one() -> None:
    """2^51 excludes m <= 58 (no admissible length through m = 52, chaining through 58, the
    closest 9.8 bits at K = 64789416887513); 2^44 still reads 49 in the same tables."""
    data = json.loads(nm.JSON_PATH.read_text(encoding="utf-8"))
    t51 = {r["m"]: r for r in data["tables"]["2^51"]["rows"]}
    assert data["tables"]["2^51"]["excluded_through"] == 58 == data["classification"]["excluded_through_at_floor"]
    assert all(t51[m]["admissible_count"] == 0 for m in range(1, 53))
    assert [t51[m]["admissible_count"] for m in range(53, 60)] == [1, 2, 4, 6, 10, 16, 27]
    assert round(t51[58]["closest_slack_bits"], 1) == -9.8 and t51[58]["K0_least_admissible"] == 64789416887513
    assert [s["K"] for s in t51[59]["survivors"]] == [64789416887513, 83130157078217]
    assert data["tables"]["2^44"]["excluded_through"] == 49


def test_the_four_lengths_at_m_50_die_at_the_recorded_floors() -> None:
    """They are the output of the template's last step, not its input: Lemma 2's
    x_min - 1 < m / Lambda removes them at floors 2^44.01, 2^44.57, 2^45.48 and 2^48.58."""
    data = json.loads(nm.JSON_PATH.read_text(encoding="utf-8"))
    r50 = next(r for r in data["tables"]["2^44"]["rows"] if r["m"] == 50)
    with mp.workdps(40):
        kills = [round(float(log(mpf(50) / mpf(s["Lambda"]) + 1, 2)), 2) for s in r50["survivors"]]
    assert kills == [44.01, 44.57, 45.48, 48.58], kills


def test_the_valley_refinement_spares_the_cycles_that_exist() -> None:
    """The known-bad input for the refinement, and the reason to believe it.

    ``valley_cap`` keeps the floor, the chaining and the odd-step count as one system instead
    of relaxing them separately. Set the floor at a real cycle's own least element and the cap
    must still leave room for that cycle's Lambda, or the refinement is excluding the truth.
    Checked on (5, 7, 10) and on the eleven-element cycle at 17."""
    with mp.workdps(60):
        for K, o, m, xmin in ((3, 2, 1, 5), (11, 7, 2, 17)):
            lam = o * log(3) - K * log(2)
            cap = nm.valley_cap(m, o, xmin)
            assert lam < cap, (K, float(lam), float(cap))
            assert not nm.valley_excluded(m, K, xmin)


def test_the_valley_refinement_closes_three_more_values_of_m() -> None:
    """At the verified floor the refinement reaches m <= 61 where the separate relaxations
    reach 58: the two lengths open at m = 59 and 60, and the four at 61, all fall. One length
    survives at m = 62. The cap is never weaker than Lemma 2's m/(X0 - 1)."""
    data = json.loads(nm.JSON_PATH.read_text(encoding="utf-8"))
    v = data["valley_refinement"]
    assert v["excluded_through"] == 61 and v["first_open_m"] == 62
    assert data["classification"]["excluded_through_at_floor"] == 58
    rows = {r["m"]: r for r in v["rows"]}
    assert rows[59]["survivors_before"] == 2 and rows[59]["survivors_after"] == []
    assert rows[61]["survivors_before"] == 4 and rows[61]["survivors_after"] == []
    assert rows[62]["survivors_after"] == [83130157078217]
    with mp.workdps(60):
        X0 = 2 ** nm.FLOOR_LOG2
        for m in (10, 40, 58, 59, 62):
            o = next(s["o"] for r in data["tables"]["2^51"]["rows"] if r["m"] >= 59
                     for s in r["survivors"])
            assert nm.valley_cap(m, o, X0) <= mpf(m) / (X0 - 1) * (1 + mpf("1e-9"))


def test_herchers_two_m_free_refinements_do_not_reach() -> None:
    """Hercher 2023 read from the source on 21 September 2026, and both refinements measured
    against what this side needs. Neither reaches, and this pins why.

    Corollary 29 tracks residue classes modulo powers of two so that a verified floor does the
    work of a larger one: on his side 1536 * 2^60 does the work of 3781 * 2^60, a factor 2.46,
    or 1.30 bits. Closing even the first open value here, m = 59, needs Lemma 2's bound to
    tighten by 4.18 bits. Short by more than an order of magnitude.

    Theorem 27 replaces the m-dependent bound by an m-free one, Lambda < (1/4) * o / X0 in the
    normalisation of this side. That is 0.23 bits tighter than the laboratory's own constant,
    which is proved in Lean (neg_cycle_finance: 2 (y-1)(3^o - 2^K) <= (K-o) 3^o, i.e.
    Lambda <~ (1/2) * (K-o) / (y-1)). The m-free period bound does not move under it: the
    surviving lengths are near-convergents of log2/log3 and sit far apart, so a seventeen per
    cent change of the window does not remove the least one.
    """
    data = json.loads(nm.JSON_PATH.read_text(encoding="utf-8"))
    rows = {r["m"]: r for r in data["tables"]["2^51"]["rows"]}
    with mp.workdps(50):
        X0 = mpf(2) ** 51
        needed = {m: float(log(max(mpf(m) / mpf(s["Lambda"]) + 1 for s in rows[m]["survivors"]) / X0, 2))
                  for m in range(59, 64)}
        assert 4.17 < needed[59] < 4.19, needed[59]
        assert all(4.1 < v < 4.3 for v in needed.values()), needed
        hercher_bits = float(log(mpf(3781) / 1536, 2))
        assert 1.29 < hercher_bits < 1.31, hercher_bits
        assert needed[59] > 3 * hercher_bits, "if this ever fails, the transposition is worth trying"
        # the two m-free constants, per unit of total cycle length
        x = log(2) / log(3)
        lab, herch = mpf("0.5") * (1 - x), mpf("0.25") * x
        assert 1.16 < float(lab / herch) < 1.18, float(lab / herch)
        assert float(log(lab / herch, 2)) < 0.25


def test_contracting_walk_agrees_with_a_direct_scan_and_differs_from_the_other_side() -> None:
    """The walk mirrored to the 3n+1 side lists exactly the K with frac(Kx) < eps; the known-bad
    input is the expanding-side list, which it must not reproduce."""
    with mp.workdps(60):
        x = log(2) / log(3)
        eps = mpf(1) / 700
        kmax = 60_000
        contracting = [K for K in range(1, kmax + 1) if (K * x) - mp.floor(K * x) < eps]
        expanding = [K for K in range(1, kmax + 1) if 1 - ((K * x) - mp.floor(K * x)) < eps]
        assert nm.contracting_lengths(eps, kmax) == contracting
        assert nm.contracting_lengths(eps, kmax) != expanding
        assert nm.admissible_lengths(eps, kmax) == expanding


def test_simons_de_weger_lemma_18_is_reproduced_on_their_side() -> None:
    """Their Section 7 lattice lists the admissible (K, L) pairs and tests each against
    Corollary 5 and Lemma 7; the same enumerate-and-test on the 3n+1 side at their floor
    301 * 2^50 returns their Lemma 18: none for 64 <= m <= 68, and their five pairs at
    69 <= m <= 72 with their killing floors to rounding (they round up). The run also lists the
    double of their second pair at m = 72, which their table does not carry."""
    data = json.loads(nm.JSON_PATH.read_text(encoding="utf-8"))
    rep = data["sdw_lemma18_reproduction"]
    assert rep["floor"] == 301 * 2 ** 50
    assert rep["none_for_64_to_68"] and rep["their_pairs_all_found"]
    for m, entries in rep["killing_floors"].items():
        for pair, theirs, ours in entries:
            assert theirs - 1 < ours <= theirs, (m, pair, theirs, ours)
    assert rep["extra_pairs"] == {"72": [[2 * 11985484530117643, 2 * 7011059003092348]]}
    fresh = nm.row_positive(69, 301 * 2 ** 50)
    assert [(s["o"], s["L"]) for s in fresh["survivors"]] == [(5750934602875680, 3364081086781987)]
    assert 576 < fresh["survivors"][0]["falls_when_X0_over_2_50"] <= 577
