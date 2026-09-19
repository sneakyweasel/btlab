"""The Juggler/Collatz bridge: verified both ways, and the audit it forces."""

from __future__ import annotations

import json
import math

import pytest

from research.juggler_sequence.collatz_bridge import (
    CLASS_BRIDGE,
    collatz_is_proposition_j_at_delta_one,
    density_exponent,
    good_set_wiener_norm,
    walsh_conversion_penalty,
    JSON_PATH,
    STEP_EVEN,
    STEP_ODD,
    big_log,
    collatz,
    collatz_reachable,
    juggler,
    loglog_increments,
    parity_map_is_bijective,
    parity_word,
    probe_payload,
    undecided_classes,
)
from research.juggler_sequence.jump_spectrum import survivor_counts


def test_the_two_walks_have_the_same_steps() -> None:
    """`log(3/2)` and `-log 2`, on `log x` for Collatz and `log log n` for Juggler."""
    assert STEP_ODD == pytest.approx(math.log(1.5), abs=1e-15)
    assert STEP_EVEN == pytest.approx(-math.log(2.0), abs=1e-15)
    # the drift is the same too, which is why both have the same survival rate
    assert 0.5 * (STEP_ODD + STEP_EVEN) == pytest.approx(0.5 * math.log(0.75), abs=1e-15)


def test_juggler_increments_hit_those_steps_from_a_large_seed() -> None:
    """The floor costs `O(1)` in `n`, so the agreement is only as good as `n` is large.

    At `n = 7` the error is a percent; from twenty-one digits it is at the last bit.
    Asserting both keeps the size condition visible instead of implied.
    """
    small = loglog_increments(7, steps=2, floor=3)
    assert small and max(abs(m - t) for _, m, t in small) > 1e-3

    large = loglog_increments(10**20 + 1, steps=2)
    assert len(large) == 2
    assert max(abs(m - t) for _, m, t in large) < 1e-14


def test_big_log_survives_values_past_the_float_range() -> None:
    """Juggler values are doubly exponential, so `float(n)` is not an option.

    A seed can still descend -- `10^20 + 1` reaches eight digits in three steps -- so
    the guard is tested on a value chosen to be large rather than on an orbit.
    """
    n = 10**400
    with pytest.raises(OverflowError):
        float(n)
    assert big_log(n) == pytest.approx(400 * math.log(10), rel=1e-12)
    assert big_log(7) == pytest.approx(math.log(7), rel=1e-15)


def test_the_parity_map_is_bijective_which_juggler_has_no_analogue_of() -> None:
    """Terras. This is the asymmetry: Collatz's word statistics are free, Juggler's
    are Hypothesis FD."""
    for depth in (4, 6, 8):
        assert parity_map_is_bijective(depth), depth
    assert parity_word(1, 4) == (1, 0, 1, 0)   # 1 -> 2 -> 1 -> 2
    assert collatz(7) == 11 and collatz(8) == 4


def test_the_survivor_count_is_the_undecided_collatz_class_count() -> None:
    """Checked by running Collatz, not by quoting OEIS.

    A class whose word has already dropped gives every member the same stopping time;
    a class whose word never drops does not. The second kind is counted by `N_d`.
    """
    counts = survivor_counts(10)
    for depth in range(4, 11):
        assert undecided_classes(depth) == counts[depth], depth
    assert [counts[d] for d in range(4, 11)] == [3, 4, 8, 13, 19, 38, 64]


def test_the_audit_separates_shared_results_from_juggler_ones() -> None:
    """Results that use only word densities belong to Collatz too.

    This is the uncomfortable half of the identification and the reason it is recorded:
    a Juggler-shaped wording does not make a claim Juggler-specific.
    """
    assert collatz_reachable("the survivor count recursion N_(d+1) + M_(d+1) = 2 N_d")
    assert collatz_reachable("the jump spectrum amplitude a_1")
    assert collatz_reachable("the certificate word count at each barrier")
    assert not collatz_reachable("Hypothesis FD gives equidistribution of parity words")
    assert not collatz_reachable("the Weyl differencing kernel bound")


def test_committed_artifact_records_the_bridge_and_its_limits() -> None:
    data = json.loads(JSON_PATH.read_text(encoding="utf-8"))
    assert data["decision"]["classification"] == CLASS_BRIDGE
    assert data["shared_count"]["agree"] is True
    assert data["shared_walk"]["worst_increment_error"] < 1e-8
    text = data["anti_overclaim"]
    assert "not an equivalence and not a conjugacy" in text
    assert "moves no bound in either problem" in text
    assert "not an easier Collatz" in text


def test_a_cheap_run_reaches_the_same_answer() -> None:
    payload = probe_payload(max_depth=7)
    assert payload["decision"]["classification"] == CLASS_BRIDGE
    assert payload["shared_count"]["agree"] is True


def test_proposition_j_on_collatz_is_terras() -> None:
    """The calibration. `E_d(N) = O(1)` is the `delta = 1` case, and it gives Terras.

    If this ever stops holding, the claim that FD buys Juggler exactly Collatz-parity
    stops holding with it, and the roadmap it implies goes too.
    """
    terras = collatz_is_proposition_j_at_delta_one()
    assert terras["delta"] == 1.0
    assert terras["density_exponent"] == pytest.approx(0.050044, abs=1e-6)
    assert terras["non_descenders"] == pytest.approx(0.949956, abs=1e-6)


def test_fd_buys_a_delta_fraction_of_that() -> None:
    """The density exponent is linear in `delta`, so FD is a fraction of Terras."""
    full = density_exponent(1.0)
    for delta in (1.0, 0.5, 1 / 24, 1 / 96):
        assert density_exponent(delta) == pytest.approx(delta * full, rel=1e-12)
    # reaching even N^0.99 needs delta near 1/5, far past what is proved at depth four
    assert density_exponent(1 / 96) < 0.01 < density_exponent(0.2)


def test_the_union_bound_costs_twenty_times_the_exponent_work() -> None:
    """Where Proposition J's loss sits.

    Combining the `N_d` word classes better is worth about `20x`; improving the
    exponent from `1/96` to `1/72` is worth `1.33x`. A direct estimate at the printed
    exponent beats a union bound at `delta = 1/5`.
    """
    union = density_exponent(1.0, "union")
    sqrt_ = density_exponent(1.0, "sqrt")
    direct = density_exponent(1.0, "direct")
    assert union < sqrt_ < direct
    assert sqrt_ / union == pytest.approx(1.90, abs=0.02)
    assert direct / union == pytest.approx(19.98, abs=0.05)
    assert direct / union > 96 / 72 * 10, "the combination step must dominate"
    assert density_exponent(1 / 96, "direct") > density_exponent(0.2, "union")
    with pytest.raises(ValueError):
        density_exponent(0.5, "wishful")


def test_the_wiener_norm_comes_from_the_library_not_from_new_code() -> None:
    """`bad_set_spectrum(d, 0.0)` has computed this since the Paper C collision branch.

    A fresh transform was written for it anyway -- the fifth duplication in a week. The
    guard is that the library path keeps reproducing the values, so nobody writes a
    sixth.
    """
    for depth, expected in ((8, 2.906250), (12, 6.316406),
                            (16, 17.114990), (20, 44.315536)):
        assert good_set_wiener_norm(depth) == pytest.approx(expected, abs=1e-5), depth


def test_the_walsh_route_is_worse_under_the_hypothesis_we_actually_have() -> None:
    """The decisive fact, and the reason `J-proposition-j-loss-is-the-union-bound` fell.

    `E_d <= max_(S != 0)|W_S| <= 2^d E_d`, both ends attained. A Walsh estimate needs the
    second bound; Proposition J supplies the first. The conversion costs `2^d`, so the
    route loses by a factor growing like `1.44^d` instead of winning by 20.
    """
    counts = survivor_counts(20)
    penalties = {d: walsh_conversion_penalty(counts, d) for d in (12, 16, 20)}
    assert penalties[12] == pytest.approx(114.5, rel=0.02)
    assert penalties[20] == pytest.approx(1700.4, rel=0.02)
    for d in (12, 16, 20):
        assert penalties[d] > 1.0, "the route must be recorded as losing, not winning"
    growth = (penalties[20] / penalties[12]) ** (1 / 8)
    assert growth == pytest.approx(1.40, abs=0.03), "penalty grows like (gamma/theta)^d"


def test_parseval_caps_the_gain_so_the_direct_reading_was_never_available() -> None:
    """`||ghat||_1 <= sqrt(N_d)` is a theorem, so `gamma <= sqrt(2 theta)` and the
    `direct` column of the old table was unreachable from the start."""
    counts = survivor_counts(20)
    for d in (8, 12, 16, 20):
        assert good_set_wiener_norm(d) <= counts[d] ** 0.5 + 1e-9, d
    assert density_exponent(1.0, "sqrt") < density_exponent(1.0, "direct")


def test_the_free_step_lemma_holds_in_the_direction_it_is_proved() -> None:
    """At a free step the Wiener norm does not move, and the proof is one line:
    `Good_d = Good_(d-1) x {0,1}`, so `ghat_d(S,1) = 0` and the L1 norm is unchanged.

    The converse is FALSE and the test says so: `d = 5` is not free -- `N_5 = 4` against
    `2 N_4 = 6` -- yet the norm still does not move. So a repeated value is evidence of
    a free step and not proof of one, and an earlier wording here claiming the lemma
    accounts for "every repeated value" was too strong.
    """
    counts = survivor_counts(22)
    unexplained = []
    for d in range(3, 23):
        free = counts[d] == 2 * counts[d - 1]
        same = abs(good_set_wiener_norm(d) - good_set_wiener_norm(d - 1)) < 1e-12
        if free:
            assert same, f"d={d}: free step must leave the Wiener norm exactly unchanged"
        elif same:
            unexplained.append(d)
    assert unexplained == [5], f"the only non-free plateau should be d=5, got {unexplained}"


def test_winklers_sandwich_holds_on_the_laboratory_counts() -> None:
    """A Collatz-side import: Winkler's 2026 rational-Catalan bounds on A100982 hold on `M_d`.

    `(1/n) C(m_n - 1, n - 1) <= M_{A020914(n)} <= (1/n) C(m_n, n - 1)` for every order checked,
    with equality exactly at his record minima and maxima of `{n log2 3}` -- the one-sided
    convergents. It confirms, from the Collatz literature, the Sturmian structure this laboratory
    reads on the same words, and it pins `M` only to a factor `2.7`: nothing about the
    `d^(-3/2)` or the prefactor follows from it.
    """
    from research.juggler_sequence.collatz_bridge import winkler_sandwich

    w = winkler_sandwich(2213)
    assert w["holds"] and w["lengths_are_a020914"] and w["nonzero_lengths"] == 2214
    assert w["a100982_head"] == [1, 1, 2, 3, 7, 12, 30, 85, 173, 476, 961, 2652]
    assert w["lower_equality"] == [1, 2, 7, 12, 53, 359, 665]
    assert w["upper_equality"] == [1, 3, 5, 17, 29, 41, 94, 147, 200, 253, 306, 971, 1636]
    assert w["lower_matches_record_minima"] and w["upper_matches_record_maxima"]
