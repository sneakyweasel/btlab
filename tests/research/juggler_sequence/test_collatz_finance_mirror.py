"""Paper A's finance transposed to Collatz reproduces the published Collatz period bounds.

The bridge's cycle claim -- that the two problems share the linear form and part only at how
words attach to integers -- gets numbers here: the same inequality, read with `x_min` in place
of `n log n`, gives Eliahou's lattice at `2^40` and Hercher's bound at `2^68`.
"""

from __future__ import annotations

import json

import pytest
from mpmath import mp, mpf, log

from research.juggler_sequence.collatz_finance_mirror import (
    BARINA_LENGTH,
    CLASS_MIRROR,
    ELIAHOU_GENERATORS,
    HERCHER_LENGTH,
    HERCHER_ODD,
    HERCHER_THEOREM_27,
    HUG_INTEGRAL,
    JSON_PATH,
    brute_force_collatz_survivors,
    collatz_bound,
    collatz_survivors,
    convergent_sides,
    eliahou_decomposition,
    even_charge,
    height_bound_holds,
    hug_sum,
    hug_sup,
    juggler_bound,
    juggler_survivors,
    lambda_collatz,
    lambda_juggler,
    nlogn,
    shortcut_orbit,
    walk_charge_bound,
    word_const,
)
from research.juggler_sequence.lean_paths import BRANCHES_ROOT
from research.juggler_sequence.paper_a_audit import survivors as paper_a_survivors


def test_dossier_exists() -> None:
    assert (BRANCHES_ROOT / "juggler_collatz_finance_mirror.md").is_file()


def test_the_two_gaps_are_mirror_images() -> None:
    """`Lambda_J(L) = log 3 - Lambda_C(L)` for every length, exactly.

    Collatz needs `2^K > 3^p`, Juggler needs `3^o > 2^L`; with `p = floor(K x)` and
    `o = ceil(L x)` the two gaps are `log 3 * frac` and `log 3 * (1 - frac)`.
    """
    with mp.workdps(60):
        for K in (1, 19, 84, 1054, 25781, 301994, 17087915, 85137581):
            p, lc = lambda_collatz(K)
            o, lj = lambda_juggler(K)
            assert o == p + 1
            assert abs(lc + lj - log(3)) < mpf(10) ** -50
            assert lc > 0 and lj > 0


def test_convergents_alternate_sides_by_exact_integer_comparison() -> None:
    """Odd-index denominators are Juggler-admissible (`3^p > 2^q`), even-index Collatz-admissible.

    Every laboratory cycle length is on the Juggler side; Eliahou's `301994` and `17087915` are
    on the Collatz side, and `85137581` -- the third generator -- is on the Juggler side, which
    is why it enters Eliahou's lattice only with a coefficient that keeps the sum positive.
    """
    rows = convergent_sides(terms=20, exact_below=2 * 10**7)
    by_q = {r["q"]: r for r in rows}
    for q in (19, 84, 1054, 50508, 176251, 16785921, 85137581):
        assert by_q[q]["side"] == "juggler", q
    for q in (8, 65, 485, 24727, 125743, 301994, 17087915):
        assert by_q[q]["side"] == "collatz", q
    assert all(r["method"] == "integers" for r in rows if r["q"] <= 2 * 10**7)
    sides = [r["side"] for r in rows if r["q"] >= 3]
    assert all(a != b for a, b in zip(sides, sides[1:]))


def test_collatz_finance_at_two_forty_is_eliahou_1993() -> None:
    """Smallest survivor `17087915`; every survivor in `301994 a + 17087915 b + 85137581 c` with
    `b >= 1`, `a c = 0`; and every pure multiple of `301994` is excluded -- the three statements
    of Eliahou's theorem, from Paper A's inequality with `x_min` in place of `n log n`."""
    with mp.workdps(80):
        two40 = mpf(2) ** 40
        surv = collatz_survivors(two40, 4 * 10**8)
    assert surv[0]["K"] == 17087915 and surv[0]["p"] == 10781274
    assert all(eliahou_decomposition(r["K"]) is not None for r in surv[:400])
    assert all(collatz_bound(301994 * a) < two40 for a in range(1, 57))
    assert eliahou_decomposition(17087915 + 3 * 85137581) == (0, 1, 3)


def test_the_walk_agrees_with_brute_force() -> None:
    """The three-gap enumeration is checked against a float-filtered exhaustive scan."""
    with mp.workdps(80):
        two40 = mpf(2) ** 40
        walk = [r["K"] for r in collatz_survivors(two40, 3 * 10**7)]
    brute = brute_force_collatz_survivors(float(two40), 3 * 10**7)
    assert walk == brute
    assert walk[0] == 17087915


def test_collatz_finance_at_two_sixty_eight_is_hercher_2018() -> None:
    """Smallest survivor `114208327604` with `72057431991` odd steps at both `695 * 2^60` and
    `2^68`; at `2^71` the second survivor is Barina's `217976794617`."""
    with mp.workdps(80):
        s_h = collatz_survivors(695 * mpf(2) ** 60, 4 * 10**11)
        s68 = collatz_survivors(mpf(2) ** 68, 4 * 10**11)
        s71 = collatz_survivors(mpf(2) ** 71, 10**12)
    assert (s_h[0]["K"], s_h[0]["p"]) == (HERCHER_LENGTH, HERCHER_ODD)
    assert (s68[0]["K"], s68[0]["p"]) == (HERCHER_LENGTH, HERCHER_ODD)
    assert [r["K"] for r in s71[:2]] == [HERCHER_LENGTH, BARINA_LENGTH]
    assert sum(ELIAHOU_GENERATORS) == 102527490


def test_juggler_finance_is_weaker_than_paper_a_certified_comparison() -> None:
    """Constant-1 finance leaves `1054` first at `10^6` and `50508` first at `3.5e8`.

    Paper A's certified comparison (Lemma 4.4b: evens charged at `n^2`, climb interiors at
    `n^(3/2)`) is sharper and leaves `25781` and `176251` instead -- the printed Theorem 4.6
    and Corollary 5.11 finance floors -- so the plain inequality used on the Collatz side is
    the weaker of the two Juggler forms, and every constant-1 survivor list contains Paper A's.
    """
    j6 = [r["L"] for r in juggler_survivors(10**6, 2 * 10**5)]
    j35 = [r["L"] for r in juggler_survivors(350_000_000, 2 * 10**5)]
    assert j6[:3] == [1054, 2108, 3162]
    assert j35[0] == 50508 and 176251 in j35
    assert 25781 not in j35 and 25781 in j6
    assert paper_a_survivors(10**6, 30_000)[0] == 25781
    assert paper_a_survivors(350_000_000, 200_000)[0] == 176251
    assert set(paper_a_survivors(350_000_000, 200_000)) <= set(j35)


def test_juggler_has_no_steiner_theorem_in_finance() -> None:
    """The 1-cycle length `9809721694` survives Theorem 4.4 at `N_0 = 3.5e8` by ten orders."""
    with mp.workdps(80):
        assert juggler_bound(9809721694) > 10**19 > nlogn(350_000_000)


def test_the_even_step_charge_identities_hold_on_orbits() -> None:
    """`2^d (C^d x + 1) = 3^o (x + 1) + evenCharge w` and `wordConst w + 2^d = 3^o + evenCharge w`,
    the natural-number identities of `CollatzBridge.lean`, re-checked in Python on orbits."""
    for x0 in (1, 3, 7, 27, 97, 871, 6171, 77031, 2**20 + 1, 2**40 + 3):
        for d in (1, 2, 3, 5, 17, 40, 90):
            word, states = shortcut_orbit(x0, d)
            o = sum(word)
            assert 2**d * (states[d] + 1) == 3**o * (x0 + 1) + even_charge(word)
            assert word_const(word) + 2**d == 3**o + even_charge(word)
            assert 3**o * (x0 + 1) <= 2**d * (states[d] + 1)
    assert even_charge([1, 0]) == 2 and 2 * 2**2 == 2 * 3 + even_charge([1, 0])


def test_the_hug_word_constant_is_effective_and_below_hercher() -> None:
    """`H(p)/p -> 1/(2 log 2) = 0.72135`, and it is below Hercher's `3/4` for every `p >= 100`.

    Hercher 2023 Theorem 27 bounds the same sum, over the odd cycle elements of `1/x`, by
    `(3/4) K/X_0`; the transposed walk charge gives `(H(p) + N_delta(p))/(x_0 + 1 - 2^delta)`,
    effective and independent of `m`, with `N_delta(p) <= p delta + 151` and `delta` of order
    `K/x_0`. Any nontrivial cycle has `p > 7.2e10`, so the comparison is between uniform bounds.
    """
    assert abs(hug_sum(111202) / 111202 - HUG_INTEGRAL) < 5e-6
    assert abs(hug_sum(10781274) / 10781274 - HUG_INTEGRAL) < 1e-7
    sup100, _ = hug_sup(100, 2_000_000)
    assert HUG_INTEGRAL < sup100 < 0.73 < HERCHER_THEOREM_27
    for x0 in (27, 97, 871, 6171, 77031, 2**31 + 1):
        r = height_bound_holds(x0)
        assert r["violations"] == 0 and r["odd_sum_le_H_plus_N"], x0


def test_the_walk_charge_does_not_move_the_published_survivors() -> None:
    """Scaling the majorant by `0.7213` leaves `114208327604` the smallest survivor at both
    `2^68` and `2^71`: the constant is worth `4%` on Theorem 27 and nothing on the period."""
    with mp.workdps(80):
        s68 = collatz_survivors(mpf(2) ** 68, 4 * 10**11, charge=HUG_INTEGRAL)
        s71 = collatz_survivors(mpf(2) ** 71, 10**12, charge=HUG_INTEGRAL)
        margin = walk_charge_bound(HERCHER_LENGTH) / mpf(2) ** 71
    assert s68[0]["K"] == HERCHER_LENGTH and s71[0]["K"] == HERCHER_LENGTH
    assert 1.3 < float(margin) < 1.4


def test_committed_artifact_records_the_mirror_and_its_limits() -> None:
    data = json.loads(JSON_PATH.read_text(encoding="utf-8"))
    assert data["decision"]["classification"] == CLASS_MIRROR
    c = data["collatz"]
    assert c["floor_2_40"]["smallest"] == 17087915
    assert c["floor_2_40"]["all_in_eliahou_lattice"] is True
    assert c["floor_2_40"]["brute_force_agrees"] is True
    assert c["floor_2_68"]["smallest"] == HERCHER_LENGTH
    assert c["floor_2_71"]["first_two"] == [HERCHER_LENGTH, BARINA_LENGTH]
    assert data["juggler"]["floor_3_5e8"]["smallest"] == 50508
    assert "No cycle of any length" in data["anti_overclaim"]
    assert data["identities"]["mirror_residual"] < 1e-40
    w = data["walk_charge"]
    assert w["constant"] < w["hercher_theorem_27"] < w["trivial"]
    assert w["remark_28_threshold_units_2_60"]["walk_charge"] == 2728
    assert w["smallest_survivor_with_walk_charge"] == {"2^68": HERCHER_LENGTH, "2^71": HERCHER_LENGTH}
    assert w["integer_identities_hold"] is True
    assert w["effective"]["sup_hug_average_p_ge_100"] < HERCHER_THEOREM_27
    assert all(r["violations"] == 0 for r in w["effective"]["orbit_prefix_checks"].values())
