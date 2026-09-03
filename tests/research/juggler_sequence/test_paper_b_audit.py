"""Paper B audit probe: exact identities, standing estimates, exponent bookkeeping (fast subset)."""

from __future__ import annotations

import random

from research.juggler_sequence import paper_b_audit as A


def test_exact_identities_hold_on_a_small_census() -> None:
    census = A.identity_census(seed=3, samples_per_range=6)
    assert census["all_identities_hold"], census["failures"]
    # the master identity and the double-gap identity were checked on every sample
    assert census["checks"]["L5.1ii-iv.master_identity"] == census["samples"]
    assert census["checks"]["L5.1ii-iv.double_gap"] == census["samples"]


def test_lemma_4_3_remainder_is_one_signed_and_bounded() -> None:
    rng = random.Random(5)
    for _ in range(50):
        n = rng.randrange(10**6, 2 * 10**6) | 1
        r = A.check_lemma_4_3(n, rng.randint(1, 5))
        assert r["E_nonneg"] and r["E_le_bound"] and r["E_le_coarse"] and r["gap_identity"]


def test_lemma_3_9_constant() -> None:
    # the proof needs the l^infinity (row-sum) norm of the inverse: 232; the printed 288 is the l^1 norm,
    # so c7 = 1/288 <= 1/232 remains a valid (non-sharp) constant
    assert A.lemma_3_9_operator_norm() == 232.0
    assert A.lemma_3_9_l1_norm() == 288.0
    inv = A._lemma_3_9_inverse()
    assert [[int(x) for x in row] for row in inv] == [[10, 68, 32], [-24, -144, -64], [15, 76, 32]]


def test_exponent_bookkeeping_all_pass() -> None:
    checks = A.exponent_checks()
    assert len(checks) >= 70
    assert all(c["ok"] for c in checks), [c["check"] for c in checks if not c["ok"]]


def test_standing_estimates_contain_observed_values() -> None:
    s = A.standing_estimates(10**6, seed=2, samples=30)
    assert s["all_ok"], s["verdict"]


def test_cell_inventory_matches_printed_bounds() -> None:
    c = A.cell_inventory(20_000, 1)
    assert c["ok"], c
