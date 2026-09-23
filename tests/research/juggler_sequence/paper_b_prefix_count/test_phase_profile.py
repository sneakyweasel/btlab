"""Historical Paper B prefix audit: phase profile."""
from __future__ import annotations
import math
import pytest
from research.juggler_sequence import paper_b_prefix_count as B

from .helpers import (
    BETA_,
    _theta,
)


@pytest.mark.slow
def test_the_meander_prefactor_is_not_a_constant_but_a_function_of_the_offset() -> None:
    """N_d/2^d ~ C rho^d d^(-3/2) is FALSE: C is almost periodic, not constant.

    In the o coordinate the event is o_t >= t*BETA for all t <= d -- a simple walk on the
    integers against a line of IRRATIONAL slope.  The step distribution is non-lattice
    (log(3/2)/log2 is irrational), but at each fixed d the endpoint
    S_d = o log3 - d log2 lies on a lattice of spacing log3 whose offset -d log2 mod log3
    equidistributes.  The barrier sits at 0, so what the asymptotic sees is the gap from
    the barrier to the lowest available state, 1 - frac(d*BETA), and the prefactor is a
    function of that, not a number.

    Measured on the exact profile: binning c_d = (N_d/2^d)/(rho^d d^(-3/2)) by
    frac(d*BETA) collapses it -- within-bin scatter 0.065 against an across-bin range
    0.628, a 9.7x signal -- and the SHAPE is identical across disjoint depth windows
    (per-bin differences have sd 0.002) while only the LEVEL drifts, by +0.287, +0.124,
    +0.054 as the window doubles.  That drift is the 1+o(1); the shape is psi.

    The sign is the mechanism's, not a fit: larger frac(d*BETA) means a smaller gap above
    the barrier, hence more survivors, hence larger c.  psi rises from 10.37 at offset
    0.05 to 11.00 at 0.95.

    Consequences.  The previously recorded constant 10.90 is one sample of psi, and the
    recorded band 10.566..11.063 is psi's range -- explained rather than noted.  The
    d^(-3/2) exponent is unaffected.

    THE TWO BANDS ARE NOT INTERCHANGEABLE, and quoting the wrong one has already cost a
    peer session a recheck.  10.37..11.00 is the BINNED shape: bin means against
    frac(d*BETA), which is psi itself, a factor 1.0608.  10.566..11.063 is a RAW per-depth
    range over a window, which also carries the within-bin scatter of 0.065 and the level
    drift of +0.287, +0.124, +0.054 as the window doubles, and is a factor 1.047.  Anything
    comparing psi's oscillation against an external bound wants the first: Paper B's
    Section 6 and J-survivor-count-is-the-certificate-tail quote 1.06 and the resulting
    factor 28 against Winkler's envelope of 2.7095, where the raw band would give 36.  Both
    verdicts are the same, but the numbers are not the same number.
    """
    import statistics

    rho = B.chernoff_rate()
    depth = 4000
    prof = B.surviving_log_mass(depth)
    c = {d: math.exp(prof[d] - d * math.log(rho) + 1.5 * math.log(d))
         for d in range(500, depth)}
    frac = {d: (d * BETA_) % 1.0 for d in c}

    def binned(lo: int, hi: int) -> list[float]:
        out = []
        for k in range(10):
            vals = [c[d] for d in c if lo <= d < hi and k / 10 <= frac[d] < (k + 1) / 10]
            out.append(statistics.fmean(vals))
        return out

    windows = [binned(1000, 2000), binned(2000, 3000), binned(3000, 4000)]

    # it does not converge: consecutive depths keep a fixed spread
    for centre in (1000, 2000, 3900):
        run = [c[d] for d in range(centre, centre + 20)]
        assert max(run) / min(run) > 1.05, (centre, max(run) / min(run))

    # it collapses onto a function of the offset
    last = windows[-1]
    scatter = statistics.fmean([
        statistics.pstdev([c[d] for d in c
                           if 3000 <= d < 4000 and k / 10 <= frac[d] < (k + 1) / 10])
        for k in range(10)])
    assert (max(last) - min(last)) / scatter > 8.0, (max(last) - min(last), scatter)

    # the shape is stable; only the level drifts, and the drift is shrinking
    shifts = []
    for a, b in zip(windows, windows[1:]):
        diff = [y - x for x, y in zip(a, b)]
        assert statistics.pstdev(diff) < 0.01, diff      # same shape
        shifts.append(statistics.fmean(diff))
    assert all(s > 0 for s in shifts) and shifts[0] > 2 * shifts[-1], shifts

    # psi is increasing in the offset, as the shrinking barrier gap predicts
    assert last[0] < last[-1]
    assert abs(last[0] - 10.37) < 0.05 and abs(last[-1] - 11.00) < 0.05, last


def test_the_mean_zero_tilt_is_bernoulli_beta_and_rho_is_its_closed_form() -> None:
    """The reduction behind psi, and an identity that was recorded as a coincidence.

    Steps Y = X - BETA with X ~ Bernoulli(1/2), so
    Lam(l) = -l*BETA + log((e^l + 1)/2).  Lam'(l) = -BETA + e^l/(e^l+1) vanishes exactly
    at l* = log(BETA/(1-BETA)), where the tilted coin is Bernoulli(BETA) -- so BETA is the
    threshold for a structural reason, not by fitting.

    Then rho = exp(Lam(l*)) = exp(-l* BETA)/(2(1-BETA)) = BETA^(-BETA) (1-BETA)^(BETA-1)/2,
    which IS theta(BETA).  J-theorem-six-one-threshold-is-slack recorded theta(p) = rho as
    agreeing to 1.1e-16; it is an algebraic identity, proved in
    Problems.Juggler.PaperBTilt.rho_closed_form.
    """
    lam = math.log(BETA_ / (1 - BETA_))
    assert math.isclose(lam, 0.536207535136, rel_tol=1e-11), lam

    # the mean-zero condition, and the tilted law
    assert abs(-BETA_ + math.exp(lam) / (math.exp(lam) + 1)) < 1e-15
    assert math.isclose(math.exp(lam) / (math.exp(lam) + 1), BETA_, rel_tol=1e-15)

    rho = B.chernoff_rate()
    assert math.isclose(math.exp(-lam * BETA_) / (2 * (1 - BETA_)), rho, rel_tol=1e-15)
    assert math.isclose(BETA_ ** (-BETA_) * (1 - BETA_) ** (BETA_ - 1) / 2, rho, rel_tol=1e-15)
    assert math.isclose(_theta(BETA_), rho, rel_tol=1e-15)


def test_the_change_of_measure_is_exact_and_the_gap_is_the_phase() -> None:
    """N_d/2^d = rho^d E~[e^(-l* S_d); S_t >= 0], and min S_d = 1 - frac(d*BETA).

    The second half is what puts frac(d*BETA) into the asymptotic: on the event the
    endpoint is S_d = m_d + (1 - frac(d*BETA)) with m_d = o_d - ceil(d*BETA) a NONNEGATIVE
    INTEGER, so the walk cannot end closer to the barrier than that gap.  Hence the exact
    factorisation N_d/2^d = rho^d e^(-l*(1-frac(d*BETA))) G(d) with G integer-indexed.
    """
    lam = math.log(BETA_ / (1 - BETA_))
    rho = B.chernoff_rate()

    for d in (50, 200, 500):
        mass = {0: 1.0}
        for t in range(1, d + 1):
            nxt: dict[int, float] = {}
            for o, m in mass.items():
                nxt[o + 1] = nxt.get(o + 1, 0.0) + BETA_ * m
                nxt[o] = nxt.get(o, 0.0) + (1 - BETA_) * m
            mass = {o: m for o, m in nxt.items() if o >= t * BETA_}
        tilted = sum(m * math.exp(-lam * (o - d * BETA_)) for o, m in mass.items())
        assert math.isclose(B.non_contracting(d) / 2 ** d, rho ** d * tilted, rel_tol=1e-12), d

        # the gap, and that it is attained
        gap = math.ceil(d * BETA_) - d * BETA_
        assert math.isclose(gap, 1 - (d * BETA_) % 1.0, rel_tol=1e-12)
        assert math.isclose(min(o - d * BETA_ for o in mass), gap, rel_tol=1e-12)


@pytest.mark.slow
def test_the_six_percent_wobble_is_two_competing_sixty_percent_effects() -> None:
    """psi = e^(-l*(1-phi)) * h(phi), and the two factors nearly cancel.

    The explicit phase factor rises by e^(0.9 l*) = 1.620 across the circle.  psi rises by
    only 1.061.  So h -- the integer-indexed part, whose existence is the open local limit
    theorem -- must FALL by 1.527, and it does.  The small observed oscillation is the
    residue of two large opposed ones: a wider barrier gap costs e^(-l*(1-phi)) in the tilt
    and buys survival room in h.

    That is why stripping the elementary factor does not make the problem easier: it
    exchanges a 6% oscillation for a 53% one.
    """
    import statistics

    lam = math.log(BETA_ / (1 - BETA_))
    rho = B.chernoff_rate()
    depth = 4000
    prof = B.surviving_log_mass(depth)
    ds = range(3000, depth)
    c = {d: math.exp(prof[d] - d * math.log(rho) + 1.5 * math.log(d)) for d in ds}
    phi = {d: (d * BETA_) % 1.0 for d in ds}
    h = {d: c[d] * math.exp(lam * (1 - phi[d])) for d in ds}

    def binned(v: dict[int, float]) -> list[float]:
        return [statistics.fmean([v[d] for d in ds if k / 10 <= phi[d] < (k + 1) / 10])
                for k in range(10)]

    P, H = binned(c), binned(h)
    assert math.isclose(max(P) / min(P), 1.0606, rel_tol=5e-3), max(P) / min(P)
    assert math.isclose(math.exp(lam * 0.9), 1.6203, rel_tol=1e-3)
    assert math.isclose(max(H) / min(H), 1.527, rel_tol=5e-3), max(H) / min(H)
    assert P[0] < P[-1] and H[0] > H[-1]            # they move in opposite directions


@pytest.mark.slow
def test_psi_is_bounded_variation_not_analytic_so_no_power_series_exists() -> None:
    """Can a Taylor series help? No -- psi is not even C^1. Fourier is the right tool.

    Estimated from two disjoint depth windows (the only honest test, since the samples
    phi_d = frac(d*BETA) are a rotation orbit), every mode to k = 24 is real: the windows
    agree to ~2e-5 while the coefficients run 5e-4 to 9e-3.

    After deconvolving the bin box filter, |psi_hat(k)| ~ k^(-0.79) -- the signature of a
    function of bounded variation with a jump, not of an analytic one.  A power series in
    the phase therefore does not exist, and a Fourier truncation at K leaves O(1/K).

    THE NAIVE SMALL-DIVISOR SCALING IS REFUTED.  If the Ostrowski small divisors drove the
    spectrum then |psi_hat(k)| * ||k BETA|| would be flatter than |psi_hat(k)|.  It is
    worse: the spread rises from 18.8x to 153.5x.  What survives is weaker -- after
    dividing out the 1/k envelope the modulation peaks exactly on BETA's Ostrowski
    lattice, the five largest k|psi_hat(k)| sitting at k = 19, 8, 11, 16, 24 = q_4, q_3,
    3+8, 2*8, 3*8, while the five smallest, k = 4, 7, 12, 15, are not such combinations.

    A CAUTION THIS TEST EXISTS TO PIN.  Estimating psi_hat by averaging over the orbit
    itself fails exactly at k near a convergent denominator, because ||q_j BETA|| is tiny
    and the factor barely turns: at k = 84 it completes ~10 turns over d = 500..6000 and
    reports 0.34, three times the k = 1 coefficient.  That is not an estimate.  Bin first.
    """
    import cmath
    import statistics

    rho = B.chernoff_rate()
    depth = 12000
    prof = B.surviving_log_mass(depth)
    nb = 64

    def spectrum(lo: int, hi: int) -> list[complex]:
        vals: list[list[float]] = [[] for _ in range(nb)]
        for d in range(lo, hi):
            c = math.exp(prof[d] - d * math.log(rho) + 1.5 * math.log(d))
            vals[min(nb - 1, int(((d * BETA_) % 1.0) * nb))].append(c)
        grid = [statistics.fmean(v) for v in vals]
        mean = statistics.fmean(grid)
        grid = [g / mean for g in grid]
        return [sum(grid[j] * cmath.exp(-2j * math.pi * k * j / nb) for j in range(nb)) / nb
                for k in range(25)]

    A, C = spectrum(2000, 6000), spectrum(6000, 12000)
    for k in range(1, 25):                       # every mode is resolved, not noise
        assert abs(abs(A[k]) - abs(C[k])) < 0.3 * max(abs(A[k]), abs(C[k])), k

    def sinc(k: int) -> float:
        t = math.pi * k / nb
        return 1.0 if k == 0 else math.sin(t) / t

    coef = [abs(A[k]) / sinc(k) for k in range(25)]
    ks = list(range(1, 25))
    slope = statistics.fmean(
        [(math.log(coef[b]) - math.log(coef[a])) / (math.log(b) - math.log(a))
         for a in ks for b in ks if b > a + 8])
    assert -1.05 < slope < -0.6, slope           # BV/jump, not analytic

    # the 1/k envelope explains most of it: spread 15.1x falls to 5.2x, a factor 2.9
    raw = [coef[k] for k in ks]
    times_k = [k * coef[k] for k in ks]
    flattening = (max(raw) / min(raw)) / (max(times_k) / min(times_k))
    assert flattening > 2.5, (flattening, max(raw) / min(raw), max(times_k) / min(times_k))

    # and multiplying by ||k BETA|| makes it worse, not better
    def nrm(k: int) -> float:
        return abs(((k * BETA_ + 0.5) % 1.0) - 0.5)
    div = [coef[k] * nrm(k) for k in ks]
    assert max(div) / min(div) > max(raw) / min(raw), (max(div) / min(div), max(raw) / min(raw))

    # the surviving peaks sit on BETA's Ostrowski lattice: every one of the top five is
    # q_3 = 8 or q_4 = 19 or a small combination of them with q_2 = 3.  Which five varies
    # slightly with the window -- 16 = 2*8 and 22 = 3+19 trade places -- so the stable
    # claim is membership in that set, not the exact ordering.
    lattice = {8, 11, 16, 19, 22, 24}          # q3, q2+q3, 2q3, q4, q2+q4, 3q3
    for spec in (A, C):
        cf = [abs(spec[k]) / sinc(k) for k in range(25)]
        top = sorted(ks, key=lambda k: -k * cf[k])[:5]
        assert set(top) <= lattice, top
        bottom = sorted(ks, key=lambda k: k * cf[k])[:5]
        assert not (set(bottom) & lattice), bottom


@pytest.mark.slow
def test_psis_jumps_are_the_rotation_orbit_of_zero() -> None:
    """The second jump is at BETA, and it is one of a cascade at every k*BETA.

    MECHANISM, exact.  The Sturmian barrier increment is b_t = 1 iff phi_t >= 1 - BETA,
    and phi_(d-1-k) = phi_d - (k+1) BETA.  The set {phi : phi - (k+1)BETA mod 1 >= 1-BETA}
    is an arc whose endpoints are k*BETA and (k+1)*BETA.  So the barrier step k+1 from the
    end switches at k*BETA, and over all k the jump set of psi is exactly the forward
    rotation orbit {k*BETA mod 1 : k >= 0} -- countable, dense, and summable.

    That is what makes psi BV rather than smooth, and it explains both earlier readings at
    once: jumps give the 1/k Fourier decay, and a jump set which IS a rotation orbit gives
    the Ostrowski peaks, since the transform of the jump measure is sum_k a_k e^(-2pi i j k
    BETA).

    Measured at 512 bins over 20001 depths, the nine largest jumps land on k*BETA for
    k = 0..8 with no exception, each within 0.0006 of its target.  Sizes decay roughly
    geometrically and are all NEGATIVE: psi drops crossing each k*BETA upward and recovers
    between, a sawtooth on the orbit.  From k = 8 on the jumps fall to the level at which a
    window comparison also picks up psi's local slope, so they are not individually
    resolved and the test does not claim them.
    """
    import numpy as np

    rho = B.chernoff_rate()
    depth = 12000
    prof = B.surviving_log_mass(depth)
    d = np.arange(4000, depth)
    c = np.array([math.exp(prof[i] - i * math.log(rho) + 1.5 * math.log(i)) for i in d])
    c = c / c.mean()
    x = (d * BETA_) % 1.0

    def jump(loc: float, w: float = 0.02) -> float:
        lo = c[((x - (loc - w)) % 1.0) < w]
        hi = c[((x - loc) % 1.0) < w]
        return float(hi.mean() - lo.mean())

    sizes = [jump((k * BETA_) % 1.0) for k in range(8)]
    assert all(s < 0 for s in sizes), sizes                 # every jump is downward
    assert sizes[0] < -0.055, sizes[0]                      # the one at 0 is the largest
    assert abs(sizes[0]) > 3 * abs(sizes[4]), sizes         # and they decay
    assert all(abs(a) > abs(b) / 1.15 for a, b in zip(sizes, sizes[1:]))   # near-monotone

    # the locations really are the orbit: bin finely and check the top jumps land on it
    nb = 256
    grid = np.array([c[np.clip((x * nb).astype(int), 0, nb - 1) == k].mean()
                     for k in range(nb)])
    grid /= grid.mean()
    step = np.roll(grid, -1) - grid
    top = np.argsort(np.abs(step))[::-1][:6]
    orbit = [(k * BETA_) % 1.0 for k in range(12)]
    for i in top:
        loc = (i + 1) / nb
        near = min(min(abs(o - loc), 1 - abs(o - loc)) for o in orbit)
        assert near < 2.0 / nb, (loc, near)
