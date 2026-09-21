"""Terras 1976 Theorem 1.14 is this laboratory's survivor recursion.

Run 21 September 2026, the open obligation left by that day's reading of the
ICM scan (Acta Arith. 30 (1976) 241-252, p. 245).

WHAT TERRAS HAS.

  Def 1.12  gamma = ln2/ln3. A word (e_0,...,e_{k-1}) in {0,1}^k is ADMISSIBLE
            when e_0+...+e_{i-1} > i*gamma on the initial truncations, ACTIVE
            when that also holds at i = k, TERMINAL when admissible and not
            active.
  Def 1.13  n(a,k) = the number of admissible words of length k with a zeros,
            named the MODIFIED BINOMIAL COEFFICIENT.
            c(a,k) = 1 if a < k(1-gamma), else 0.
  Thm 1.14  n(0,1) = 1, n(1,1) = 0, and
                c(a,k) n(a,k) + c(a-1,k) n(a-1,k) = n(a,k+1).

The gate is the whole content: a < k(1-gamma) is (k-a) > k*gamma, i.e. the
word is still active. So (11) is Pascal restricted to the surviving words, and
his admissibility condition e_0+...+e_{i-1} > i*gamma is, in integers,
3^ones > 2^i -- this laboratory's no-contracting-prefix condition verbatim.

WHAT THIS FILE ESTABLISHES.

  1. Theorem 1.14 reproduces the admissible table exactly (its one deviation
     from brute force is the base cell n(1,1), which Terras sets to 0; c(1,1)
     is 0 too, so the cell never propagates and the choice is inert).
  2. word_counts(k)[k-a] -- Paper B's joint (length, weight) table -- is the
     ACTIVE part of n(a,k). The joint table is Terras's, 1976.
  3. N_k is his active row sum and M_k his terminal row sum.
  4. sum_a n(a,k) = 2 N_(k-1). This DERIVES the offset that
     test_terras_table_a.py measured against Table A: F(k) = sum_a n(a,k)/2^k
     = N_(k-1)/2^(k-1), because admissible splits as active plus terminal and
     N_k + M_k = 2 N_(k-1).

CONSEQUENCE FOR THE DEPOSITED PAPER B. Its subsection "This recursion is not
new" credits Zarubin's A076227 formula of 11 August 2019, Winkler's of
12 September 2017, and equation (48) of the September Hikawa. All three state
the one-index form N_k = 2 N_(k-1) - M_k. That form follows from Theorem 1.14
by summing over a and splitting the row into its active and terminal parts --
item 4 below. The antecedent is therefore 1976, in a paper the manuscript
already cites as its reference [4], and forty-one years older than the earliest
credit in that paragraph. Nothing in the subsection was claimed as new, so this
changes an attribution and not a claim.
"""

from __future__ import annotations

from itertools import product

import pytest

from research.juggler_sequence.certificate_increment import survivor_counts
from research.juggler_sequence.paper_b_prefix_count import word_counts

KMAX = 16


def _survives(ones: int, i: int) -> bool:
    """Terras's e_0+...+e_{i-1} > i*gamma, in exact integers."""
    return 3 ** ones > 2 ** i


def _brute(kmax: int) -> tuple[dict, dict, dict]:
    active: dict[tuple[int, int], int] = {}
    terminal: dict[tuple[int, int], int] = {}
    for k in range(1, kmax + 1):
        for word in product((0, 1), repeat=k):
            ones = 0
            if any(
                not _survives(ones := ones + word[i - 1], i) for i in range(1, k)
            ):
                continue
            total = sum(word)
            key = (k - total, k)
            bucket = active if _survives(total, k) else terminal
            bucket[key] = bucket.get(key, 0) + 1
    admissible = dict(active)
    for key, val in terminal.items():
        admissible[key] = admissible.get(key, 0) + val
    return active, terminal, admissible


def _terras(kmax: int) -> dict[tuple[int, int], int]:
    """n(a,k) from Theorem 1.14 and its own initialization."""
    n: dict[tuple[int, int], int] = {(0, 1): 1, (1, 1): 0}
    gate = lambda a, k: 1 if 3 ** (k - a) > 2 ** k else 0  # noqa: E731
    for k in range(1, kmax):
        for a in range(0, k + 2):
            val = gate(a, k) * n.get((a, k), 0) + gate(a - 1, k) * n.get((a - 1, k), 0)
            if val:
                n[(a, k + 1)] = val
    return n


@pytest.fixture(scope="module")
def tables():
    active, terminal, admissible = _brute(KMAX)
    surv, minimal = survivor_counts(KMAX + 1)
    return active, terminal, admissible, _terras(KMAX), surv, minimal


def test_theorem_1_14_reproduces_the_admissible_table(tables) -> None:
    _active, _terminal, admissible, terras, _s, _m = tables
    deviations = [
        (a, k)
        for k in range(1, KMAX + 1)
        for a in range(0, k + 1)
        if terras.get((a, k), 0) != admissible.get((a, k), 0)
    ]
    # The only deviation is the base cell Terras initializes to 0.
    assert deviations == [(1, 1)]


def test_the_inert_base_cell_cannot_propagate() -> None:
    """n(1,1) is gated out, so Terras's choice of 0 there changes nothing."""
    assert not 3 ** (1 - 1) > 2 ** 1


@pytest.mark.parametrize("k", range(1, 13))
def test_the_joint_table_is_terras_modified_binomial_coefficients(tables, k: int) -> None:
    """word_counts(k)[k-a] is the ACTIVE part of n(a,k). Paper B's joint table, 1976."""
    active, _t, _adm, _terras, _s, _m = tables
    counts = word_counts(k)
    for a in range(0, k + 1):
        assert active.get((a, k), 0) == counts[k - a], (a, k)


@pytest.mark.parametrize("k", range(1, KMAX + 1))
def test_N_and_M_are_the_active_and_terminal_row_sums(tables, k: int) -> None:
    active, terminal, _adm, _terras, surv, minimal = tables
    assert sum(v for (_a, kk), v in active.items() if kk == k) == surv[k]
    assert sum(v for (_a, kk), v in terminal.items() if kk == k) == minimal[k]


@pytest.mark.parametrize("k", range(2, KMAX + 1))
def test_row_sum_is_twice_the_previous_survivor_count(tables, k: int) -> None:
    """sum_a n(a,k) = 2 N_(k-1): the Table A offset, derived rather than fitted."""
    _a, _t, admissible, _terras, surv, _m = tables
    assert sum(v for (_aa, kk), v in admissible.items() if kk == k) == 2 * surv[k - 1]


def test_the_gate_is_load_bearing(tables) -> None:
    """Control: strip the gate and the recursion counts all 2^k words instead.

    Without this the file is green for nothing -- it would read as though any
    Pascal recursion reproduced the survivor counts, which is the claim the
    prior-art table makes against the toolkit's ungated W[k][d].
    """
    _a, _t, _adm, _terras, surv, _m = tables
    rows = {0: {0: 1}}
    for k in range(0, KMAX):
        nxt: dict[int, int] = {}
        for d, c in rows[k].items():
            nxt[d] = nxt.get(d, 0) + c
            nxt[d + 1] = nxt.get(d + 1, 0) + c
        rows[k + 1] = nxt
    for k in range(1, KMAX + 1):
        assert sum(rows[k].values()) == 2 ** k
        assert sum(rows[k].values()) != surv[k]
