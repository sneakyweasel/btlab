"""Historical Paper B prefix audit: weight profile."""
from __future__ import annotations
import math
import pytest



def test_fast_prefactor_profile_agrees_with_the_exact_pass() -> None:
    """The narrow-window DP must reproduce `surviving_log_mass`, not merely be fast."""
    import math

    from research.juggler_sequence.paper_b_prefix_count import (
        _rho,
        surviving_log_mass,
        surviving_prefactor_profile,
    )

    rho = _rho()
    fast = surviving_prefactor_profile(1500, window=512)
    slow = surviving_log_mass(1500)
    worst = max(
        abs(fast[d] - math.exp(slow[d]) * d**1.5 / rho**d)
        / (math.exp(slow[d]) * d**1.5 / rho**d)
        for d in range(100, 1501)
    )
    assert worst < 1e-10, worst


@pytest.mark.slow
def test_prefactor_window_must_be_checked_not_assumed() -> None:
    """A window too narrow for the depth truncates silently, and psi decays.

    This is the failure that produced a wrong answer before it was caught: the
    conditioned walk spreads like `sqrt(d)`, so the window has to grow with the
    depth. The test pins the symptom so nobody reads a decaying psi as physics.
    """
    from research.juggler_sequence.paper_b_prefix_count import surviving_prefactor_profile

    narrow = surviving_prefactor_profile(30000, window=64)
    wide = surviving_prefactor_profile(30000, window=512)
    assert narrow[30000] < 1.0, "a 64-wide window must visibly collapse by d=30000"
    assert 10.0 < wide[30000] < 12.0, "a 512-wide window is converged at this depth"


@pytest.mark.slow
def test_psi_jumps_on_the_rotation_orbit() -> None:
    """psi is a jump function and its discontinuities sit on {n*beta mod 1}.

    The ledger's prefactor row records psi as almost-periodic with "one departure
    from monotonicity near 0.65 ... presumably a path effect". That departure is
    the n = 1 jump, at beta itself.
    """
    from research.juggler_sequence.paper_b_prefix_count import (
        BETA,
        surviving_prefactor_profile,
    )

    depth = 120000
    psi = surviving_prefactor_profile(depth, window=1024)
    lo = depth - 40000
    pts = sorted(((BETA * d) % 1.0, psi[d]) for d in range(lo, depth + 1))
    gaps = [(abs(pts[i + 1][1] - pts[i][1]), 0.5 * (pts[i][0] + pts[i + 1][0]))
            for i in range(len(pts) - 1)]
    gaps.sort(reverse=True)
    spacing = 1.0 / len(pts)
    for size, where in gaps[:4]:
        n = min(range(1, 40), key=lambda k: min(abs((k * BETA) % 1 - where),
                                                1 - abs((k * BETA) % 1 - where)))
        target = (n * BETA) % 1.0
        err = min(abs(target - where), 1 - abs(target - where))
        assert err < 5 * spacing, f"jump at {where} is not on the orbit (nearest {n}*beta)"
    assert gaps[0][0] > 0.2, "the largest jump should be substantial, not a slope"


@pytest.mark.slow
def test_psi_jump_amplitudes_follow_the_sturmian_word() -> None:
    """The jump sizes rise exactly where the Sturmian barrier step is zero.

    The jumps sit on `{n*beta mod 1}`. Their amplitudes are not monotone in `n`:
    `a_n > a_(n-1)` precisely when `s_n = ceil(n*beta) - ceil((n-1)*beta) = 0`,
    the same Sturmian word that places them. Verified for every consecutive pair
    with `n <= 40`, where the amplitudes dominate the contamination from orbit
    points outside the window-sizing set.
    """
    import numpy as np

    from research.juggler_sequence.paper_b_prefix_count import (
        BETA,
        surviving_prefactor_profile,
    )

    depth = 150000
    psi = surviving_prefactor_profile(depth, window=1024)
    lo = depth // 2
    ds = np.arange(lo, depth + 1)
    fr = (BETA * ds) % 1.0
    order = np.argsort(fr)
    f_s, p_s = fr[order], np.array([psi[d] for d in ds])[order]

    nmax = 40
    orbit = np.array([(n * BETA) % 1.0 for n in range(nmax + 1)])

    def amplitude(n: int) -> float:
        x0 = orbit[n]
        others = np.delete(orbit, n)
        gap = np.min(np.minimum(np.abs(others - x0), 1 - np.abs(others - x0)))
        half = 0.35 * gap
        left = (f_s > x0 - half) & (f_s < x0)
        right = (f_s > x0) & (f_s < x0 + half)
        return p_s[left].mean() - p_s[right].mean()

    def step(n: int) -> int:
        import math
        return math.ceil(n * BETA) - math.ceil((n - 1) * BETA)

    a = {n: amplitude(n) for n in range(1, nmax + 1)}
    for n in range(2, nmax + 1):
        rises = a[n] > a[n - 1]
        assert rises == (step(n) == 0), (
            f"n={n}: amplitude {'rose' if rises else 'fell'} but s_n={step(n)}"
        )


@pytest.mark.slow
def test_psi_jump_amplitudes_multiply_by_one_over_rho_at_sturmian_zeros() -> None:
    """At a Sturmian zero the prefactor's jump grows by exactly `1/rho`.

    `J-r-jumps-halve-at-the-sturmian-zeros` proves the boundary fraction's jumps
    halve there. The prefactor's do not halve: they multiply by `1/rho`. So the
    two jump measures are not affinely related, and diverge by `2/rho` per zero.
    """
    import math

    import numpy as np

    from research.juggler_sequence.paper_b_prefix_count import (
        BETA,
        _rho,
        surviving_prefactor_profile,
    )

    rho = _rho()
    depth = 150000
    psi = surviving_prefactor_profile(depth, window=1024)
    lo = depth // 2
    ds = np.arange(lo, depth + 1)
    fr = (BETA * ds) % 1.0
    order = np.argsort(fr)
    f_s = fr[order]
    p_s = np.array([psi[d] for d in ds])[order]

    # The window is sized by the nearest of `sizing` orbit points. Too few and the
    # window widens until it swallows a neighbouring jump: at `sizing = 25` the
    # ratio at n = 19 comes out -1.9 rather than 1/rho. 40 is enough here.
    sizing, nmax = 40, 25
    orbit = np.array([(n * BETA) % 1.0 for n in range(sizing + 1)])

    def amplitude(n: int) -> float:
        x0 = orbit[n]
        others = np.delete(orbit, n)
        gap = np.min(np.minimum(np.abs(others - x0), 1 - np.abs(others - x0)))
        half = 0.35 * gap
        left = (f_s > x0 - half) & (f_s < x0)
        right = (f_s > x0) & (f_s < x0 + half)
        return p_s[left].mean() - p_s[right].mean()

    a = {n: amplitude(n) for n in range(1, nmax + 1)}
    zeros = [n for n in range(2, nmax + 1)
             if math.ceil(n * BETA) - math.ceil((n - 1) * BETA) == 0]
    assert len(zeros) >= 5
    for n in zeros:
        assert a[n] / a[n - 1] == pytest.approx(1.0 / rho, rel=2e-3), (
            f"n={n}: ratio {a[n] / a[n - 1]} is not 1/rho = {1.0 / rho}"
        )


@pytest.mark.slow
def test_psi_jump_spectrum_factorises_through_the_barrier_index() -> None:
    """`a^psi_n = C_(ceil(n*beta)) * rho^(-(n - ceil(n*beta)))`.

    The `1/rho` growth at Sturmian zeros says the amplitude, renormalised by
    `rho^(n - ceil(n*beta))`, cannot change at a zero. It does not: the
    renormalised value is constant across every zero-step to a few parts in
    `1e5`. So the spectrum is one sequence indexed by `ceil(n*beta)` times an
    explicit exponential, rather than a free function of `n`.

    What the sequence itself does is NOT established: splitting the one-steps by
    whether a zero precedes them gives overlapping distributions at every range
    tested, so no law is claimed for it.
    """
    import math

    import numpy as np

    from research.juggler_sequence.paper_b_prefix_count import (
        BETA,
        _rho,
        surviving_prefactor_profile,
    )

    rho = _rho()
    depth = 150000
    psi = surviving_prefactor_profile(depth, window=1024)
    lo = depth // 2
    ds = np.arange(lo, depth + 1)
    fr = (BETA * ds) % 1.0
    order = np.argsort(fr)
    f_s = fr[order]
    p_s = np.array([psi[d] for d in ds])[order]

    sizing, nmax = 60, 30
    orbit = np.array([(n * BETA) % 1.0 for n in range(sizing + 1)])

    def amplitude(n: int) -> float:
        x0 = orbit[n]
        others = np.delete(orbit, n)
        gap = np.min(np.minimum(np.abs(others - x0), 1 - np.abs(others - x0)))
        half = 0.35 * gap
        left = (f_s > x0 - half) & (f_s < x0)
        right = (f_s > x0) & (f_s < x0 + half)
        return p_s[left].mean() - p_s[right].mean()

    def bar(n: int) -> int:
        return math.ceil(n * BETA)

    c = {n: amplitude(n) * rho ** (n - bar(n)) for n in range(1, nmax + 1)}
    zeros = [n for n in range(2, nmax + 1) if bar(n) == bar(n - 1)]
    assert len(zeros) >= 8
    for n in zeros:
        assert c[n] / c[n - 1] == pytest.approx(1.0, abs=1e-3), (
            f"n={n}: renormalised amplitude moved at a zero-step"
        )


def test_the_weight_basis_prefactor_swings_half_a_bit() -> None:
    """How much room Hikawa's 0.3 bits actually leaves, measured not waved at.

    Conjecture 7.1 says `W(d) = Theta(d^(-3/2) 2^(gamma d))`, motivated by the
    residual `log2 W(d) - gamma d` agreeing with the ballot correction
    `-(3/2) log2 d` to within 0.3 bits over `100 <= d <= 10000`. A constant
    prefactor makes that residual flat. It is not flat.

    MEASURED in the weight basis, which this laboratory had never used -- all
    its prefactor work is on `N_d / 2^d`, the length basis. Over
    `100 <= d <= 10000` the residual runs from -0.046 to +0.472, a swing of
    0.518 bits, and the swing is stable on sub-ranges: 0.5155 on [100, 1000),
    0.5104 on [1000, 5000), 0.5100 on [5000, 10000). So it is a persistent
    oscillation and not a transient. The float recursion agrees with the exact
    integer one to 5.7e-14 bits at d = 200, so this is not numerical.

    WHAT THIS CORRECTS, and it is a claim made earlier the same day in this
    repository: that his 0.3-bit tolerance is "wide enough to hold a bounded
    oscillating prefactor without detecting one". That now depends on a
    reading of his sentence NOBODY HERE HAS CHECKED, because the paper body is
    ResearchGate-gated. If "within 0.3 bits" means a band of half-width 0.3,
    total width 0.6, then a 0.518-bit swing fits -- but it occupies 86 per
    cent of the band, which is not "wide enough" in any comfortable sense. If
    it means the swing itself is at most 0.3, then this measurement disagrees
    with his reported numerics and one of the two is wrong. The honest
    position is that the margin is thin and the question needs the PDF.
    """
    from research.juggler_sequence.paper_b_prefix_count import (
        weight_log_mass,
        weight_prefactor_residual,
    )

    # the marginal is the sequence it should be
    mass = weight_log_mass(10)
    assert [round(2**v) for v in mass[1:9]] == [2, 3, 7, 12, 30, 85, 173, 476]

    residual = weight_prefactor_residual(2000)
    swing = max(residual) - min(residual)
    assert 0.51 < swing < 0.53
    assert -0.06 < min(residual) < -0.03
    assert 0.46 < max(residual) < 0.49

    # and it is not shrinking: the second half swings as much as the first
    half = len(residual) // 2
    early = max(residual[:half]) - min(residual[:half])
    late = max(residual[half:]) - min(residual[half:])
    assert abs(early - late) < 0.05


@pytest.mark.slow
def test_the_weight_basis_prefactor_is_the_same_rotation() -> None:
    """psi's structure transports to the weight basis, which is Hikawa's.

    The length-basis story -- prefactor almost-periodic in `frac(d BETA)`,
    discontinuous exactly on the rotation orbit
    (`J-psi-jumps-are-the-rotation-orbit-of-zero`), reconstructible from its
    jump measure -- appears unchanged in the weight basis, where the phase is
    `frac(d log2 3)`.

    COLLAPSE. Over `d >= 2000` the residual is a function of the phase and
    almost nothing else: two disjoint windows, [2000, 6000) and [6000, 10000),
    agree to 0.0061 bits at worst and 0.0006 on average across 40 phase bins,
    against a total spread of 0.131. Binning finer shows the leftover is bin
    width, not scatter: the phase explains 96.8, 98.3, 99.4, 99.98 and 99.99
    per cent of the variance at 20, 40, 100, 200 and 400 bins.

    JUMPS ON THE ORBIT. Measured directly rather than by binning, the profile
    jumps at `frac(k log2 3)` for every `k = 1..12`, all in the same
    direction, with sizes 0.181, 0.109, 0.066, 0.048, 0.033, 0.026 for
    `k = 1..6`. A control at twelve random phases gives 0.005 on average and
    0.016 at worst, so the small-`k` jumps stand 10 to 35 times above the
    estimator's own floor.

    THE DECAY IS ROUGHLY 1/k AND THE EXPONENT IS NOT CLAIMED. `k * |jump|` is
    0.181, 0.219, 0.198, 0.191, 0.166, 0.154 for `k = 1..6`, flat to about
    twenty per cent. Past `k = 8` the jump falls toward the 0.005 control
    floor, so the apparent steepening there is the estimator and not the
    function; no exponent is fitted. On the length side the measured decay is
    `k^(-0.79)` after deconvolution, which is a different estimator on a
    different basis and is not compared here.

    WHY IT MATTERS. Hikawa's Conjecture 7.1 is stated in THIS basis at THESE
    depths. The oscillation his `Theta` cannot distinguish from a constant is
    not a subtle residue: it carries 99.98 per cent of the variance and its
    discontinuities sit on the rotation orbit.
    """
    import bisect

    from research.juggler_sequence.paper_b_prefix_count import (
        weight_prefactor_residual,
    )

    lam = math.log(3) / math.log(2)
    depth = 12000
    residual = weight_prefactor_residual(depth, lo=100)
    pts = sorted(
        (math.modf(d * lam)[0], r)
        for d, r in zip(range(100, depth + 1), residual)
        if d >= 2000
    )
    xs = [p for p, _ in pts]
    ys = [r for _, r in pts]

    def jump_at(x: float, w: float = 0.004) -> float | None:
        lo = bisect.bisect_left(xs, x - w)
        mid = bisect.bisect_left(xs, x)
        hi = bisect.bisect_left(xs, x + w)
        if mid - lo < 8 or hi - mid < 8:
            return None
        return sum(ys[mid:hi]) / (hi - mid) - sum(ys[lo:mid]) / (mid - lo)

    jumps = []
    for k in range(1, 7):
        j = jump_at(math.modf(k * lam)[0])
        assert j is not None
        jumps.append(j)

    # every one positive, and monotonically shrinking
    assert all(j > 0 for j in jumps)
    assert jumps == sorted(jumps, reverse=True)
    assert 0.16 < jumps[0] < 0.20

    # k * |jump| is flat to about twenty per cent -- a 1/k-ish law, unfitted
    scaled = [(k + 1) * j for k, j in enumerate(jumps)]
    assert max(scaled) / min(scaled) < 1.5

    # and the orbit is where the jumps are: random phases give far less
    controls = [abs(jump_at(x) or 0.0) for x in (0.05, 0.22, 0.41, 0.63, 0.88)]
    assert max(controls) < 0.5 * jumps[-1]


def test_the_two_bases_are_one_collapse_under_an_affine_phase_map() -> None:
    """Weight basis and length basis hold the same numbers at conjugate phases.

    The weight-basis profile collapsing on `frac(d log2 3)` and the
    length-basis one collapsing on `frac(L BETA)` are not two facts. The two
    bases carry the SAME integers -- `W(d) = M[ceil((d+1) log2 3)]`, checked
    below for `d = 1..25` -- and their phases are affinely related.

    ONE LINE. With `lam = log2 3`, `BETA = 1/lam` and `L = ceil(d lam)`, which
    is `d lam + (1 - frac(d lam))` because `lam` is irrational, multiply by
    `BETA`:

        L BETA = d + (1 - frac(d lam)) BETA.

    The offset lies in `[0, BETA) subset [0, 1)`, so no wrap occurs and

        frac(L BETA) = BETA * (1 - frac(d lam))

    EXACTLY, not merely mod 1. Verified to 3.6e-12 over `d < 20000`, which is
    floating point and not the mathematics.

    Two consequences worth naming. The map is orientation-REVERSING, so the
    weight profile is the length profile read backwards and rescaled. And its
    image is `[0, BETA)`, so carrying lengths never visit the rest of the
    length-phase circle -- which is why `1 - frac(L BETA)` is the natural
    coordinate there, as `collatz_finance_mirror` already uses for the cycle
    gap `Lambda_J`.

    This is elementary -- a Beatty computation, one line -- and is recorded
    for what it pins rather than for difficulty: the weight-basis measurement
    is not an independent confirmation of the length-basis one. It is the
    same measurement in another coordinate, and should never be cited as
    corroboration.
    """
    from research.juggler_sequence.jump_spectrum import survivor_counts
    from research.juggler_sequence.paper_b_prefix_count import word_counts

    lam = math.log(3) / math.log(2)
    beta = 1 / lam

    counts = survivor_counts(45)
    certificates = {L: 2 * counts[L - 1] - counts[L] for L in range(1, 45)}
    for d in range(1, 26):
        length = math.ceil((d + 1) * lam)
        if length < 45:
            weight_total = sum(
                word_counts(L)[d]
                for L in range(d, math.floor(d * lam) + 2)
                if d < len(word_counts(L))
            )
            assert weight_total == certificates[length]

    worst = 0.0
    for d in range(1, 20000):
        length = math.ceil(d * lam)
        worst = max(
            worst,
            abs(math.modf(length * beta)[0] - beta * (1 - math.modf(d * lam)[0])),
        )
    assert worst < 1e-9

    # the offset never wraps, which is what makes it affine rather than mod 1
    assert all(
        0 <= beta * (1 - math.modf(d * lam)[0]) < beta for d in range(1, 5000)
    )


def test_a214494_is_a_near_miss_for_the_weight_triangle() -> None:
    """The triangle is not in OEIS, and the search that says otherwise is wrong.

    Searching the weight-refined survivor triangle flattened by rows returns
    nothing. Searching it with rows REVERSED returns A214494,
    `T(n,k) = C(n,k) - 2 C(n,k-1)`, and the first 24 flattened terms agree --
    enough for OEIS to report a match. They are different triangles.

    A214494 is the ballot count against slope 1/2: paths with `o >= t/2`. Ours
    is the survivor count against slope `1/lam = 0.6309`: every prefix with
    `3^o >= 2^t`. The barriers already differ at `t = 2`, so the agreement is
    not structural -- it is that the counts coincide until `L = 11`, where our
    row gains a fifth entry the ballot row does not have, and from `L = 12`
    the values differ too (85 against 55).

    Recorded because the next sweep will hit it again. Twenty-four terms of
    agreement is not an identification, and a run search cannot distinguish a
    coincidence from a selection -- the lesson a peer session reached the same
    day from the other direction, having reported three sequences absent when
    two were selections from catalogued families.
    """
    from math import comb

    from research.juggler_sequence.paper_b_prefix_count import word_counts

    def ballot(length: int) -> list[int]:
        def binom(n: int, k: int) -> int:
            return comb(n, k) if 0 <= k <= n else 0

        return [
            v
            for v in (binom(length, k) - 2 * binom(length, k - 1)
                      for k in range(length + 1))
            if v > 0
        ]

    def ours(length: int) -> list[int]:
        return [v for v in word_counts(length) if v][::-1]

    for length in range(1, 11):
        assert ballot(length) == ours(length), length

    assert ours(11) == [1, 9, 33, 55, 30]
    assert ballot(11) == [1, 9, 33, 55]
    assert ours(12)[-1] == 85 and ballot(12)[-1] == 55

    # and the barriers were never the same, which is why the agreement is luck
    lam = math.log(3) / math.log(2)
    assert math.ceil(2 / lam) != math.ceil(2 / 2)
