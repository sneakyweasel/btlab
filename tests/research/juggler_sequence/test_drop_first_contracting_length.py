"""The Juggler dropping time is the first contracting length of its own parity word.

Run 21 September 2026 for the OEIS comments on A094778 and A094683, the Juggler side
of `J-juggler-is-collatz-one-exponential-up`, and for the attempt to prove the
equality that followed (see the probe's docstring for the theorem and its limit).

WHAT IS PROVED.

  Contracting prefix => drop: `power_bound_contracts` (Envelope.lean, kernel), the
  Lean form of Paper B's Proposition 2.1. So the dropping time is AT MOST the first
  contracting length `tau`, which lies in A020914 (the letter that contracts is
  even, so `2^(tau-1) < 3^o < 2^tau`).

  Drop criterion (human proof, probe docstring item 2): an uncertified drop at `k`
  needs `sum_{j<k} 1/(rho_j x_j) >= (1 - 1/rho_k) ln m`; hence (item 3) an excursion
  with `O` odd letters and `2 O / m > (1 - 2^{-delta(O)}) ln m`, `delta(O)` the
  least `||o log2 3||` for `o <= O`. `o_min` tabulates the least such `O`.

  Refined bound (item 4): under the bootstrap `2 O / m <= ln 2`, `x_j >= (m/2)^{rho_j}`
  and a run-by-run sum give `S <= (1 + 2/m)(sum_{o<O} (2/m)^{2^{f_o}} + 2/m^2)` with
  `f_o = {o log2 3}` exact, so the admissible `O` at each `m` are a finite computation:
  the least is 16266 at `10^6`, 31867 at `10^7`, 111202 at `10^8`, and they cluster
  at the dangerous denominators plus multiples of 665.

  This is the mirror of the Collatz situation, where Terras's coefficient stopping
  time is AT MOST the dropping time and equality for `x >= 2` is his open
  Conjecture 2.9 (A126241).

WHAT THIS FILE ESTABLISHES.

  1. Dropping time == tau(word) for every odd start below 20000; the probe took it to
     every odd start below 10^6, the five starts past 400000 digits included.
  2. The identity `d_i <= rho_i S_i` holds numerically along sample excursions, the
     retained fraction of the ideal margin is in (0, 1], and the loss-accounting
     ratio is the recorded 0.408 at m = 5 and below 0.02 at the near-miss starts.
  3. The convergents of log2 3 come out right and `o_min` reproduces the table:
     665 at 10^6, 16758 at 10^8, 190537 at 10^10.
  4. The first 101 terms of A094778 as printed by the OEIS are reproduced.
  5. The comparison is sensitive: with the odd branch weakened to isqrt(x^3) - x,
     early drops appear at once.
  6. tau is computed by scanning prefixes, not read off the length.

WHAT IS NOT CLAIMED. Equality in general: no instance of an uncertified drop is
known, and none can be reached, since it needs at least 665 odd steps for m >= 10^6.
"""
from __future__ import annotations

from math import isqrt

import pytest

from research.juggler_sequence.drop_first_contracting_length import (
    a020914,
    analyse_start,
    convergents_log2_3,
    delta,
    first_contracting_length,
    frac_parts_log2_3,
    gmp_sweep,
    o_min,
    refined_scan,
    rhin_delta_lower_bound,
    study,
)
from research.juggler_sequence.lean_paths import BRANCHES_ROOT

# A094778(n) for n = 0..100 as printed by the OEIS (Jason Earls, Jun 10 2004):
# the dropping time of 2n+1, with a(0) = 0 for the fixed point 1.
_A094778_TEXT = (
    "0,5,4,2,5,2,2,2,2,2,2,2,5,2,2,2,4,4,15,5,2,4,4,2,5,2,4,4,2,5,2,2,2,2,"
    "7,2,4,5,10,2,7,2,4,7,8,2,2,5,5,8,5,13,8,2,7,8,13,10,4,2,4,2,4,4,8,4,"
    "4,2,5,2,2,2,2,2,2,4,2,5,5,2,2,24,10,2,4,2,26,5,2,2,4,10,2,5,2,4,70,4,5,5,5"
)
A094778 = [int(t) for t in _A094778_TEXT.split(",")]

LIMIT = 20_000


def test_dossier_exists() -> None:
    assert (BRANCHES_ROOT / "juggler_drop_first_contracting_length.md").is_file()


def test_dropping_time_is_first_contracting_length_and_lies_in_a020914() -> None:
    lengths = {a020914(n) for n in range(400)}
    early = []
    for m in range(3, LIMIT, 2):
        res = analyse_start(m)
        if res["tau"] != res["dropping_time"]:
            early.append((m, res["dropping_time"], res["tau"]))
        assert res["dropping_time"] in lengths, (m, res["dropping_time"])
        assert res["identity_violations"] == 0, m
    assert early == []


def test_even_starts_drop_at_once() -> None:
    for m in (2, 4, 10, 96, 1024):
        res = analyse_start(m)
        assert res["dropping_time"] == 1 and res["tau"] == 1 and res["word"] == "E"


def test_margin_accounting_on_recorded_starts() -> None:
    # m = 5 and m = 3 are where the loss bound uses most of the slack; m = 9 keeps
    # the least of the ideal margin; 491 and 4229 sit at the near misses o = 12, 53.
    res = analyse_start(5)
    assert abs(res["max_loss_ratio"] - 0.40795) < 1e-4
    res = analyse_start(9)
    assert abs(res["min_retained"] - 0.73063) < 1e-4
    for m in (3, 9, 37, 265, 491, 4229, 48443):
        res = analyse_start(m)
        assert res["identity_violations"] == 0
        assert res["tau"] == res["dropping_time"]
        if res["min_retained"] is not None:
            assert 0.0 < res["min_retained"] <= 1.0
            assert res["max_loss_ratio"] < 0.5
    assert analyse_start(491)["max_loss_ratio"] < 0.02
    assert analyse_start(4229)["max_loss_ratio"] < 0.02
    big = analyse_start(48443)
    assert big["dropping_time"] == 149 and int(big["peak_bits"] * 0.30103) == 972462


def test_convergents_are_certified_and_leave_mpmath_precision_alone() -> None:
    # The mpmath version set mp.dps = 80 for the whole process, and 80 digits stop
    # resolving partial quotients near q ~ 1e40.
    from mpmath import mp

    saved = mp.dps
    mp.dps = 15
    try:
        rows = convergents_log2_3(10**60)
        assert mp.dps == 15
    finally:
        mp.dps = saved
    assert rows[-1]["q"] > 10**60 >= rows[-2]["q"]
    dists = [row["dist"] for row in rows[1:]]
    assert all(later < earlier for earlier, later in zip(dists, dists[1:]))
    assert [row["above"] for row in rows[:4]] == [True, False, True, False]


def test_convergents_and_o_min_table() -> None:
    conv = convergents_log2_3(10**7)
    qs = [row["q"] for row in conv]
    assert qs[:11] == [1, 1, 2, 5, 12, 41, 53, 306, 665, 15601, 31867]
    above = {row["q"] for row in conv if row["above"]}
    assert {12, 53, 665, 31867, 111202} <= above
    assert {5, 41, 306, 15601, 79335, 190537}.isdisjoint(above)
    assert abs(delta(664, conv) - 1.475e-3) < 1e-5
    assert abs(delta(665, conv) - 6.298e-5) < 1e-7
    assert o_min(10**4, conv) == 97
    assert o_min(10**6, conv) == 665
    assert o_min(10**8, conv) == 16758
    assert o_min(10**10, conv) == 190537
    # o_min is monotone in m over the table
    vals = [o_min(10**e, conv) for e in range(4, 13)]
    assert vals == sorted(vals)
    # the Rhin tail is weaker than every tabulated distance, as it must be
    assert rhin_delta_lower_bound(665) < delta(665, conv)


def test_first_terms_of_a094778_reproduce() -> None:
    assert len(A094778) == 101
    for n, expected in enumerate(A094778):
        if n == 0:
            continue  # the fixed point 1 never drops; the OEIS sets a(0) = 0
        assert analyse_start(2 * n + 1)["dropping_time"] == expected, (n, 2 * n + 1)


def test_tau_scans_prefixes_not_length() -> None:
    assert first_contracting_length([1, 0, 0, 0]) == 2  # O E: 3 < 4 already at t = 2
    assert first_contracting_length([1, 1, 0, 0, 0]) == 4  # 9 > 8 at t = 3, 9 < 16 at t = 4
    assert first_contracting_length([1, 1, 1]) is None
    assert first_contracting_length([]) is None


def test_control_a_leakier_odd_branch_drops_early() -> None:
    """The comparison must be able to fail: weaken the odd floor and it does."""

    def leaky(v: int) -> int:
        return isqrt(v) if v % 2 == 0 else isqrt(v**3) - v

    early = 0
    for m in range(3, 2001, 2):
        v, word = m, []
        while v >= m and len(word) < 500:
            word.append(v % 2)
            v = leaky(v)
        if first_contracting_length(word) != len(word):
            early += 1
    assert early > 0


def test_refined_bound_lifts_the_frontier() -> None:
    fr = frac_parts_log2_3(40_000)
    assert abs(fr[53] - 3.0125e-3) < 1e-6
    assert abs(fr[665] - 6.298e-5) < 1e-7
    assert abs(fr[16266] - 3.673e-5) < 1e-7  # the semiconvergent 665 + 15601, above side
    r6 = refined_scan(10**6, 40_000, fr)
    assert r6["least_admissible"] == 16266
    assert r6["first_admissible"][:3] == [16266, 16931, 17596]  # 16266 + 665 j
    r7 = refined_scan(10**7, 40_000, fr)
    assert r7["least_admissible"] == 31867
    conv = convergents_log2_3(10**7)
    assert o_min(10**6, conv) == 665 < r6["least_admissible"]
    # monotone in m: what is excluded at 10^6 stays excluded at 10^7
    assert r7["admissible_count"] <= r6["admissible_count"]


def test_near_drop_shortfall_is_recorded() -> None:
    # 9 -> 27 -> 140 -> 11 -> 36 -> 6: the even step to 11 lands with rho = 9/8, ideal
    # 9^(9/8) = 11.84, so the near-drop sits 0.84 units below its ideal.
    res = analyse_start(9)
    assert res["word"] == "OOEOE" and res["near_drops"] == 1 and res["arg_shortfall"] == 3
    assert 0.8 < res["max_shortfall_units"] < 0.9
    assert 0.06 < res["max_shortfall_rel"] < 0.08


def test_gmp_backend_agrees_with_python_integers() -> None:
    """The GMP path is an independent implementation of the same check; on a shared
    range it must agree on every drop it reports and on the extremes."""
    pytest.importorskip("gmpy2")
    py = study(6000, cap_bits=None, start=3)
    gmp = gmp_sweep(6000, start=3, cap_bits=0)  # cap 0: list every start with its peak
    assert gmp["early_drops"] == [] == py["early_drops"]
    assert gmp["odd_starts"] == py["odd_starts"] == 2999
    assert gmp["largest_excursion_bits_m"] == py["largest_excursion_bits_m"]
    assert gmp["longest_dropping_time_m"] == py["longest_dropping_time_m"]
    by_m = {row["m"]: row for row in gmp["capped_then_run_uncapped"]}
    for m in (37, 173, 193, 2183, 4229):
        res = analyse_start(m)
        assert by_m[m]["dropping_time"] == res["dropping_time"] == by_m[m]["tau"]
        assert by_m[m]["odd_letters"] == res["odd_letters"]
        assert by_m[m]["digits"] == int(res["peak_bits"] * 0.30103)


def test_study_reports_no_early_drop_and_the_new_fields() -> None:
    s = study(4000)
    assert s["early_drops"] == [] and s["identity_violations"] == 0
    assert s["odd_starts"] == 1999 and s["near_drops_total"] > 0
    assert sum(s["near_drop_shortfall_units_histogram"]) <= s["odd_starts"]
    assert s["largest_near_drop_shortfall"][0][0] >= 0.0
