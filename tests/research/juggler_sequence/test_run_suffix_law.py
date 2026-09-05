"""The run-suffix law and the two envelopes it is built from.

The law's claim is that Section 3's eleven hand-proved exclusions are one inequality.  That is
checkable in two independent ways, and both are here: the arithmetic claim (the law's threshold
equals the threshold the paper prints, for every suffix the paper treats) and the dynamical
claim (the forward and backward envelopes really do bound real Juggler trajectories).

The second is the one that would catch an error in the derivation, so it is tested against
actual orbits rather than against the algebra that produced it.
"""

from __future__ import annotations

import math
import random

import pytest

from research.juggler_sequence import run_suffix_law as R


def J(x: int) -> int:
    return math.isqrt(x) if x % 2 == 0 else math.isqrt(x ** 3)


def orbit(n: int, steps: int) -> tuple[list[int], str]:
    """States and realized parity word of ``steps`` Juggler steps from ``n``."""
    states, word = [n], []
    x = n
    for _ in range(steps):
        word.append("E" if x % 2 == 0 else "O")
        x = J(x)
        states.append(x)
        if x <= 1:
            break
    return states, "".join(word)


# --- the arithmetic claim: one inequality, ten evaluations ---


@pytest.mark.parametrize("suffix,printed,source", R.RECOVERIES)
def test_law_reproduces_the_printed_threshold(suffix: str, printed: int, source: str) -> None:
    """Every threshold in Section 3 is the least ``a`` with ``(3/2)^a > 2^s/3^l``.

    Nine of the ten agree exactly.  The tenth is a strengthening, not a disagreement: for the
    suffix ``E`` the paper's Lemma 3.4(v) excludes ``a >= 3`` and sends ``a = 2`` (the word
    ``OOE``) to the census of Theorem 3.6, while the law excludes ``a >= 2`` outright once
    ``n >= 1032``.
    """
    law = R.least_run(suffix)
    if suffix == "E":
        assert law == 2 < printed
    else:
        assert law == printed, (suffix, printed, law, source)


@pytest.mark.parametrize("suffix,printed,_source", R.RECOVERIES)
def test_every_recovery_is_live_at_the_certified_floor(
    suffix: str, printed: int, _source: str
) -> None:
    """The law needs ``n`` above a threshold; all ten thresholds are far below the floor."""
    law = R.least_run(suffix)
    thr = R.threshold(law, suffix)
    assert thr is not None and thr < R.LAB_FLOOR, (suffix, thr)
    assert R.excluded(law, suffix, R.LAB_FLOOR)
    assert not R.excluded(law - 1, suffix, R.LAB_FLOOR), "one step below must survive"


def test_law_thresholds_beat_the_ones_the_paper_prints() -> None:
    """Where Section 3 states an ``n`` threshold, the law's is smaller.

    Theorem 3.12 runs its algebra from ``n >= 256`` and Theorem 3.14 from ``n >= 128``; the law
    reaches the same conclusions from 205 and 73.  The sharpening comes from carrying the
    backward exponent exactly (``2^s/3^l``) instead of rounding it up to the next power of two.
    """
    assert R.threshold(4, "EE") == 205 < 256
    assert R.threshold(6, "EEE") == 73 < 128
    # Theorem 3.16 rounds (n+1)^(32/9) up to (n+1)^4 and then needs n >= 256
    assert R.suffix_exponent("EOOEE") < 4
    assert R.threshold(4, "EOOEE") == 45 < 256


def test_the_law_extends_past_the_suffixes_the_paper_treats() -> None:
    """Arithmetically the inequality does not stop at three even letters."""
    for suffix, expected in (("EEEE", 7), ("EEEEE", 9), ("EOEEE", 6), ("EOOEEE", 5),
                             ("EEEOE", 6), ("EOEOEE", 5)):
        assert R.least_run(suffix) == expected, suffix


def test_crude_law_runs_out_of_constant_at_the_fourth_even_letter() -> None:
    """Theorem 3.26 buys the crossing against a factor 4 per unit of expansion.

    That costs a margin ``ln 4 / ln n``, 0.0811 at the certified floor.  The trailing blocks
    ``O^2E``, ``O^4E^2`` and ``O^6E^3`` have margins 0.111, 0.210 and 0.298 and clear it;
    ``O^7E^4`` has margin 0.0636 and does not.  That margin is theta at ``(o, L) = (7, 11)``,
    the semiconvergent 11/7 of log_2 3.  Lemma 3.28 removes the constant entirely, which is
    why Theorem 3.31 is not stopped there.
    """
    assert abs(R.floor_constant() - 0.08115) < 1e-5
    for r, expected_a in ((1, 2), (2, 4), (3, 6)):
        a = R.least_run("E" * r)
        assert a == expected_a
        assert R.margin(a, "E" * r) > R.floor_constant()
        assert R.excluded_exact(a, "E" * r, R.LAB_FLOOR)
    assert R.least_run("EEEE") == 7
    assert R.margin(7, "EEEE") < R.floor_constant()
    assert not R.excluded_exact(7, "EEEE", R.LAB_FLOOR)
    assert R.threshold_exact(7, "EEEE") == 828_484_409
    assert abs(1 - 2 ** 11 / 3 ** 7 - R.margin(7, "EEEE")) < 1e-12


# --- the sharp envelope ---


def test_sharp_exponents_match_the_lean_module() -> None:
    """``O7EEEEGap.lean`` runs this chain at a = 7 and lands on 6177 and 3990."""
    assert R.sharp_exponents(7) == (6177, 3990)
    for a in range(1, 16):
        X, Y = R.sharp_exponents(a)
        assert X == 3 * (3 ** a - 2 ** a) and Y == 2 * 3 ** a - 3 * 2 ** a
        assert X - Y == 3 ** a                       # the whole margin of the law
        if a > 1:
            Xp, Yp = R.sharp_exponents(a - 1)
            assert X == 3 * Xp + 3 * 2 ** (a - 1)    # the recurrence of Lemma 3.28
            assert Y == 3 * Yp + 3 * 2 ** (a - 1)
    assert R.sharp_exponents(1) == (3, 0)            # the odd one-step preimage


def test_sharp_envelope_holds_on_real_minimum_based_runs() -> None:
    """Lemma 3.28 against actual orbits, in exact integer arithmetic."""
    checked = 0
    for n in range(3, 30_000, 2):
        x = n
        for a in range(1, 9):
            if x % 2 == 0:
                break
            x = J(x)
            if x < n:                                 # not minimum-based past here
                break
            X, Y = R.sharp_exponents(a)
            assert n ** X < (n + 1) ** Y * (x + 1) ** (2 ** a), (n, a)
            checked += 1
    assert checked > 5000, checked


@pytest.mark.parametrize("suffix,sharp", list(zip(
    [s for s, _p, _x in R.RECOVERIES], [7, 6, 6, 5, 5, 5, 5, 5, 5, 5])))
def test_sharp_thresholds_are_corollary_3_30(suffix: str, sharp: int) -> None:
    a = R.least_run(suffix)
    assert R.threshold_sharp(a, suffix) == sharp
    assert R.threshold_sharp(a, suffix) <= R.threshold_exact(a, suffix)


def test_every_small_start_reaches_one() -> None:
    """A cycle minimum is at least 300, which is what makes the thresholds free."""
    for n in range(2, 300):
        x = n
        for _ in range(2000):
            x = J(x)
            if x == 1:
                break
        assert x == 1, n


@pytest.mark.parametrize("e,words,closed_at,binding", [
    (3, 16, 16, (2, 3, 1)),
    (4, 186, 16, (2, 1, 3, 1)),
    (5, 2037, 16, (2, 0, 3, 3, 1)),
    (6, 25353, 16, (2, 0, 0, 5, 3, 1)),
])
def test_theorem_3_31_closure(e: int, words: int, closed_at: int, binding: tuple) -> None:
    """Every minimum-based canonical form with ``e`` even letters is closed.

    The enumeration is complete rather than truncated: ``run_bound`` is the law applied at
    that run with the later runs empty, which is the worst case because odd letters only
    shrink the backward envelope.
    """
    r = R.closure(e)
    assert r["words"] == words
    assert r["still_open"] == []
    assert r["closed_at"] == closed_at
    assert r["binding_word"] == binding
    assert r["run_bounds"] == [R.least_run("E" * (e - i)) - 1 for i in range(e)]


@pytest.mark.slow
def test_theorem_3_31_closure_at_seven_even_letters() -> None:
    """The case that carries Theorem 3.31 to ``e >= 8``: 325452 forms, closed at n >= 64."""
    r = R.closure(7)
    assert r["run_bounds"] == [11, 10, 8, 6, 5, 3, 1]
    assert r["words"] == 325_452
    assert r["still_open"] == []
    assert r["closed_at"] == 64
    assert r["binding_word"] == (2, 2, 2, 1, 2, 2, 1)


def test_period_bounds_that_follow_from_the_even_count() -> None:
    """Each further even letter buys log 3 / log(3/2) in period: 11, 14, 17, 19, 22."""
    got = [min(L for L in range(2, 40) if 2 ** L < 3 ** (L - e)) for e in (4, 5, 6, 7, 8)]
    assert got == [11, 14, 17, 19, 22]


# --- the dynamical claim: the envelopes bound real orbits ---


@pytest.mark.parametrize("a", [1, 2, 3, 4, 5, 6])
def test_forward_envelope_holds_on_real_odd_runs(a: int) -> None:
    """``J^a(n) >= 4 (n/4)^((3/2)^a)`` -- Lemma 3.10 in closed form.

    Checked in exact integer arithmetic by clearing the exponents: the closed form is
    equivalent to ``n^(3^a) <= 2^(e_a) J^a(n)^(2^a)``, which is what Lemma 3.10 states.
    """
    e_a = 2 * (3 ** a - 2 ** a)
    checked = 0
    for n in range(3, 40_000, 2):
        states, word = orbit(n, a)
        if word != "O" * a:
            continue                      # n does not realize O^a
        assert n ** (3 ** a) <= 2 ** e_a * states[a] ** (2 ** a), (n, a)
        checked += 1
    assert checked > 100, checked


def test_forward_closed_form_is_exactly_lemma_3_10() -> None:
    """The closed form and the paper's statement are the same inequality, not a weakening."""
    for a in range(0, 9):
        e_a = 2 * (3 ** a - 2 ** a)
        # 4 (n/4)^P raised to 2^a is n^(3^a) / 2^(e_a): compare the exponents of 4
        assert 2 ** a - 3 ** a == -e_a // 2, a
        assert R.forward_exponent(a) * 2 ** a == 3 ** a


@pytest.mark.parametrize("seed", [0, 1, 2, 3, 4])
def test_backward_envelope_holds_on_real_orbits(seed: int) -> None:
    """The state entering a suffix is below the exact integer envelope of that suffix.

    Lemma 3.9 is the pure-even case.  Its induction does not use evenness, so the bound runs
    backward through any suffix; the test walks real orbits and checks every cut.
    """
    rng = random.Random(seed)
    checked = 0
    for _ in range(60):
        n = rng.randrange(3, 10 ** 6, 2)
        states, word = orbit(n, 7)
        if len(word) < 7:
            continue
        for cut in range(1, 8):
            suffix = word[len(word) - cut:]
            end = states[len(word)]
            assert states[len(word) - cut] < R.exact_backward_envelope(suffix, end), (
                n, word, cut)
            checked += 1
    assert checked > 200, checked


def test_backward_envelope_matches_lemma_3_9_on_even_runs() -> None:
    """For a pure even suffix the exact envelope is precisely ``(n+1)^(2^r)``."""
    for n in (12, 1000, 26254995):
        for r in range(1, 5):
            assert R.exact_backward_envelope("E" * r, n) == (n + 1) ** (2 ** r)


def test_backward_envelope_exponent_agrees_with_the_fraction() -> None:
    """The exact bound sits above ``(n+1)^(2^s/3^l)``, and the gap closes as ``n`` grows.

    This is what "no slop accumulates" means quantitatively.  Each backward odd letter rounds a
    cube root up by at most one, so the excess is additive in the state, not multiplicative in
    the exponent: read as an exponent of ``n+1`` it decays like a power of ``n``.  For the
    worst of the ten suffixes it is 7e-5 at ``n = 10^3`` and exactly zero by ``n = 10^12``.
    """
    for suffix, _p, _s in R.RECOVERIES:
        want = float(R.suffix_exponent(suffix))
        excess = []
        for n in (10 ** 3, 10 ** 5, 10 ** 7, 10 ** 9):
            got = math.log(R.exact_backward_envelope(suffix, n)) / math.log(n + 1)
            assert got >= want, (suffix, n, got, want)      # still an upper bound
            excess.append(got - want)
        assert excess == sorted(excess, reverse=True), (suffix, excess)
        assert excess[-1] < 1e-9, (suffix, excess)


# --- the two envelopes together are consistent with the map having no small cycle ---


def test_no_minimum_based_return_on_the_words_the_law_excludes() -> None:
    """Direct evidence: search real orbits for any of the excluded words closing a cycle."""
    for suffix, _printed, _source in R.RECOVERIES:
        a = R.least_run(suffix)
        word = "O" * a + suffix
        for n in range(3, 60_000, 2):
            states, realized = orbit(n, len(word))
            if realized != word:
                continue
            assert states[-1] != n or min(states[:-1]) < n, (n, word)
