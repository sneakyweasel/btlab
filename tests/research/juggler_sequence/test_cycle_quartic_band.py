"""Fixed exact controls for the written quartic-band theorem.

The open paths below are actual guarded Juggler paths, not cycles.
The finite permutations are abstract controls, not floor realizations.
These tests do not replace the universal proof in the canonical dossier.
"""
from math import gcd, isqrt

import pytest


def _ceil_root(n, degree):
    """Integer bisection, with no floating-point cutoffs."""
    lo, hi = 0, 1 << ((n.bit_length() + degree - 1) // degree)
    while hi - lo > 1:
        mid = (lo + hi) // 2
        if mid**degree < n:
            lo = mid
        else:
            hi = mid
    return hi


def _step(n):
    return isqrt(n**3 if n % 2 else n)


def _cycle_count(permutation):
    unseen = set(range(len(permutation)))
    count = 0
    while unseen:
        count += 1
        point = min(unseen)
        while point in unseen:
            unseen.remove(point)
            point = permutation[point]
    return count


@pytest.mark.parametrize("t", [3, 65, 65537])
def test_guarded_local_inversion_at_fixed_scales(t):
    m = t**5
    k = _ceil_root(m**4, 3)
    x, xp = t**8 + 8, t**8 + 10
    u, up = t**12 + 12*t**4, t**12 + 15*t**4
    n = t**18 + 18*t**10 + 54*t**2
    v, z = n - 1, t**9 + 9*t - 1
    paths = [(x, u, v, z), (xp, up, t**6, t**9)]
    assert [[a % 2 for a in path] for path in paths] == [
        [1, 1, 0, 1], [1, 0, 1, 1]]
    for path in paths:
        assert all(m <= a < m**4 for a in path)
        assert k <= path[0] < m**2
        assert k <= path[-1] < m**2
        assert all(not k <= a < m**2 for a in path[1:-1])
        for a, b in zip(path, path[1:]):
            assert _step(a) == b
            radicand = a**3 if a % 2 else a
            assert b*b <= radicand < (b+1)**2
    assert m < t**6 < k <= x < xp < m**2 < u < up < m**3 < v < m**4
    assert x < z and xp < t**9 < z
    assert z - t**9 == 9*t - 1
    # These open first returns grow and reverse order; they do not close.
    assert all(path[-1] not in (x, xp) for path in paths)
    for j in (4, 5):
        a, b = t**8 + 2*j, t**12 + 3*t**4*j
        assert a**3 - b*b == 3*t**8*j*j + 8*j**3 > 0
        assert (b+1)**2 - a**3 == (
            2*t**12 + 6*t**4*j + 1 - 3*t**8*j*j - 8*j**3) > 0
    assert n*n - u**3 == 216*t**12 + 2916*t**4 > 0
    assert u**3 - v*v == 2*n - 1 - 216*t**12 - 2916*t**4 > 0
    assert v - z*z == 2*t**9 + 18*t - 27*t*t - 2 > 0
    assert (z+1)**2 - v == 27*t*t + 1 > 0
    # The oriented shuffle allowance is respected even at the largest scale.
    ell = _ceil_root(k**4, 3)
    assert x < xp < ell
    assert (xp-x)**4 < 16*ell


@pytest.mark.parametrize("m", [9, 17, 65, 350000001, 10**100 + 1])
def test_exact_lower_floor_margin_and_section_cuts(m):
    q = isqrt(m**3)
    k, ell = _ceil_root(m**4, 3), _ceil_root(_ceil_root(m**4, 3)**4, 3)
    assert (q-1)**3 > (m+1)**4
    assert m < k < q < ell < m*m
    assert (k-1)**3 < m**4 <= k**3
    assert (ell-1)**3 < k**4 <= ell**3
    d = _ceil_root(ell, 4)
    assert (d-1)**4 < ell <= d**4
    # At the two exact adjacent cut cells, OE changes from below k to >=k.
    assert isqrt(isqrt((ell-1)**3)) < k
    assert isqrt(isqrt(ell**3)) >= k
    four_odd = m
    for _ in range(4):
        four_odd = isqrt(four_odd**3)
    assert four_odd > m**4


@pytest.mark.parametrize("e,r,pi,expected_cycles", [
    (8, 6, (0, 2, 1, 3, 4, 5), 1),
    (12, 9, (2, 0, 1, 3, 4, 5, 6, 7, 8), 1),
    (10, 7, (0, 1, 2, 3, 4, 5, 6), 1),
    (12, 9, (1, 0, 2, 3, 4, 5, 6, 7, 8), 2),
])
def test_rotation_composition_and_primitive_inversion_obstruction(
        e, r, pi, expected_cycles):
    assert sorted(pi) == list(range(r))
    s = e-r
    tau = pi + tuple(range(r, e))
    rotation = tuple((i+s) % e for i in range(e))
    sigma = tuple(s+pi[i] if i < r else i-r for i in range(e))
    # Composition is on the input side: R_s after tau.
    assert sigma == tuple(rotation[tau[i]] for i in range(e))
    inversions = sum(pi[i] > pi[j] for i in range(r) for j in range(i+1, r))
    d = gcd(e, s)
    assert d == gcd(3*r + 2*s, 2*r + s)
    assert _cycle_count(rotation) == d
    assert _cycle_count(sigma) == expected_cycles
    assert abs(d - expected_cycles) <= inversions
    assert (inversions - (d - expected_cycles)) % 2 == 0
    if expected_cycles == 1:
        assert d-1 <= inversions
        assert (inversions-d+1) % 2 == 0
    else:
        assert inversions < d-1

@pytest.mark.parametrize("t", [3, 65, 65537])
def test_quartic_inversion_shares_exact_oe_cell(t):
    """Existing open paths share one cell; no cyclic membership is inferred."""
    x, y = t**8 + 8, t**8 + 10
    h, s = _step(x), _step(y)
    valley = t**6
    b_x = isqrt(isqrt(x**3))
    b_y = isqrt(isqrt(y**3))
    assert b_x == b_y == valley
    # B at x is only prescribed: h is odd, so its E guard would fail.
    assert h % 2 == 1 and s % 2 == 0
    assert _step(s) == valley
    assert valley**2 < h < s < (valley + 1)**2

    lower = _ceil_root(valley**4, 3)
    upper = _ceil_root((valley + 1)**4, 3) - 1
    assert lower <= x < y <= upper
    assert (lower - 1)**3 < valley**4 <= lower**3
    assert upper**3 < (valley + 1)**4 <= (upper + 1)**3
    # Check both adjacent changes of the exact integer fiber, without a scan.
    assert isqrt(isqrt((lower - 1)**3)) < valley
    assert isqrt(isqrt(lower**3)) == valley
    assert isqrt(isqrt(upper**3)) == valley
    assert isqrt(isqrt((upper + 1)**3)) > valley

    peak = _step(h)
    f_image, g_image = _step(peak), _step(valley)
    assert peak % 2 == 0
    assert f_image == t**9 + 9*t - 1 > t**9 == g_image
    assert f_image % 2 == g_image % 2 == 1
    # The shared cell and odd endpoint spacing retain the exact peak threshold.
    assert h**3 >= ((g_image + 2)**2 + 1)**2


def test_old_quartic_budget_allows_a_repeated_g_crossing():
    """A fixed primitive abstract permutation fails the new shared-cell rule."""
    e, r, s = 12, 9, 3
    pi = (2, 0, 1, 3, 4, 5, 6, 7, 8)
    labels = ("F",) + ("G",) * (r - 1)
    pairs = tuple((i, j) for i in range(r) for j in range(i + 1, r)
                  if pi[i] > pi[j])
    assert pairs == ((0, 1), (0, 2))
    assert all(labels[i] == "F" and labels[j] == "G" for i, j in pairs)
    inversions, c = len(pairs), labels.count("F")
    d = gcd(e, s)
    assert (inversions, c, d) == (2, 1, 3)
    tau = pi + tuple(range(r, e))
    sigma = tuple((tau[i] + s) % e for i in range(e))
    assert sorted(sigma) == list(range(e))
    assert _cycle_count(sigma) == 1
    # Old Q3 permits this with D=2, including its parity and gcd conditions.
    old_d = 2
    assert d - 1 <= inversions <= min(c, r - c) * old_d
    assert (inversions - (d - 1)) % 2 == 0
    assert max(abs(pi[i] - i) for i in range(r)) <= old_d
    # It needs one F to cross two different G sources, which a cycle cannot do.
    assert pi[0] - 0 == 2
    assert inversions > c


@pytest.mark.parametrize("pi,prefixes,expected_connected,expected_cycles", [
    ((1, 0, 2, 4, 3, 5, 6, 7, 8), ((0, 1), (3, 4)), False, 3),
    ((1, 0, 2, 3, 5, 4, 6, 7, 8), ((0, 1), (4, 5)), True, 1),
    ((1, 2, 0, 3, 4, 5, 6, 7, 8), ((0, 2),), True, 1),
])
def test_quartic_cell_prefix_residue_connectivity(
        pi, prefixes, expected_connected, expected_cycles):
    """Fixed abstract cell assignments; none is an asserted floor realization."""
    e, r, s = 12, 9, 3
    d = gcd(e, s)
    assert sorted(pi) == list(range(r))
    participating_f = set()
    g_ranks = set()
    for first, last in prefixes:
        assert first < last
        assert not participating_f.intersection(range(first, last + 1))
        participating_f.update(range(first, last))
        g_ranks.add(last)
        assert tuple(pi[i] for i in range(first, last)) == tuple(
            range(first + 1, last + 1))
        assert pi[last] == first
    assert all(pi[i] == i for i in range(r)
               if i not in participating_f and i not in g_ranks)
    active = tuple(i for i in range(r) if pi[i] == i + 1)
    assert set(active) == participating_f
    inversions = sum(pi[i] > pi[j] for i in range(r)
                     for j in range(i + 1, r))
    assert inversions == len(participating_f) == d - 1 == 2
    assert (inversions - (d - 1)) % 2 == 0

    # Residue graph: each active source cut joins consecutive rotation classes.
    neighbors = [set() for _ in range(d)]
    for cut in active:
        left, right = cut % d, (cut + 1) % d
        neighbors[left].add(right)
        neighbors[right].add(left)
    reached, pending = {0}, [0]
    while pending:
        for vertex in neighbors[pending.pop()]:
            if vertex not in reached:
                reached.add(vertex)
                pending.append(vertex)
    connected = len(reached) == d
    assert connected is expected_connected
    assert connected == (len({i % d for i in active}) == d - 1)

    tau = pi + tuple(range(r, e))
    rotation = tuple((i + s) % e for i in range(e))
    sigma = tuple(rotation[tau[i]] for i in range(e))
    assert sorted(sigma) == list(range(e))
    assert _cycle_count(rotation) == d
    assert _cycle_count(sigma) == expected_cycles
    # At exactly d-1 active cuts the connected graph is the spanning-tree case.
    assert connected == (_cycle_count(sigma) == 1)

@pytest.mark.parametrize("u", [3, 65, 65537])
def test_existing_open_pair_can_have_its_minimum_in_the_shared_cell(u):
    """The same open paths meet the minimum cells without giving a cycle."""
    m, k = u**6, u**8
    a, b = u**8 + 8, u**8 + 10
    h, p = u**12 + 12*u**4, u**12 + 15*u**4
    peak = u**18 + 18*u**10 + 54*u*u - 1
    w, t = u**9, u**9 + 9*u - 1
    paths = [(a, h, peak, t), (b, p, m, w)]
    states = set().union(*paths)
    assert min(states) == m and max(states) == peak
    assert m**3 <= peak < m**4
    assert k == _ceil_root(m**4, 3)
    assert k <= a < b < _ceil_root((m+1)**4, 3)
    assert isqrt(isqrt(a**3)) == isqrt(isqrt(b**3)) == m
    for path in paths:
        assert all(_step(x) == y for x, y in zip(path, path[1:]))
        assert k <= path[0] < m*m and k <= path[-1] < m*m
        assert all(not k <= x < m*m for x in path[1:-1])
    assert t > w and a < b
    assert t not in (a, b) and w not in (a, b)


def test_old_minimum_control_fails_the_maximum_extension_guard():
    """Only u=3 is checked; prescribed roots must not become actual E edges."""
    a, h, peak, t = 6569, 532413, 388483856, 19709
    b, p, m, w = 6571, 532656, 729, 19683
    assert tuple(_step(x) for x in (a, h, peak)) == (h, peak, t)
    assert tuple(_step(x) for x in (b, p, m)) == (p, m, w)
    p_w, p_t = _step(w), _step(t)
    assert (p_w, p_t) == (2761448, 2766921)
    assert p_w % 2 == 0 and p_t % 2 == 1
    for source, target in ((w, p_w), (t, p_t)):
        assert target**2 <= source**3 < (target+1)**2
    prescribed_w, prescribed_t = isqrt(p_w), isqrt(p_t)
    assert (prescribed_w, prescribed_t) == (1661, 1663)
    assert m < prescribed_w < prescribed_t < a < b < w < t
    assert prescribed_t < 6561
    assert _step(p_w) == prescribed_w
    assert _step(p_t) != prescribed_t
    assert p_t > h and _step(p_t) > peak

@pytest.mark.parametrize(
    "e,r,pi,prefixes,expected_cycle,expected_collapse",
    [
        (12, 9, (1, 2, 0, 3, 4, 5, 6, 7, 8), ((0, 2),),
         (0, 3, 6, 9), 0),
        (7, 5, (1, 0, 2, 4, 3), ((0, 1), (3, 4)),
         (0, 2, 4, 5), 1),
    ],
)
def test_fixed_quartic_auxiliary_components(
        e, r, pi, prefixes, expected_cycle, expected_collapse):
    """Two fixed abstract maps, not floor realizations or numerical cycle bounds."""
    s = e - r
    assert sorted(pi) == list(range(r))
    tau = pi + tuple(range(r, e))
    sigma = tuple((tau[i] + s) % e for i in range(e))
    assert sorted(sigma) == list(range(e))
    assert _cycle_count(sigma) == 1
    assert all(sigma[i] > i for i in range(r))
    assert all(sigma[i] < i for i in range(r, e))

    collapse = list(range(e))
    f_sources, g_partners = set(), {}
    for first, last in prefixes:
        assert first < last
        for i in range(first, last):
            f_sources.add(i)
            g_partners[i] = last
            assert pi[i] == i + 1
        assert pi[last] == first
        for i in range(first, last + 1):
            collapse[i] = first
    assert len(f_sources) == 2
    auxiliary = tuple((collapse[i] + s) % e for i in range(e))
    periodic = set(expected_cycle)
    assert len(periodic) == len(expected_cycle)
    assert tuple(auxiliary[i] for i in expected_cycle) == (
        expected_cycle[1:] + expected_cycle[:1])
    # Replay only these two listed finite maps; every remaining rank enters
    # their displayed component. Do not pass a nonpermutation to _cycle_count.
    for source in range(e):
        point = source
        for _ in range(e):
            if point in periodic:
                break
            point = auxiliary[point]
        assert point in periodic

    periodic_f = periodic.intersection(f_sources)
    assert periodic_f == {0}
    partner = g_partners[0]
    assert partner not in periodic
    assert auxiliary[partner] == auxiliary[0]
    point = partner
    for _ in range(len(expected_cycle)):
        point = auxiliary[point]
    assert point == 0

    q = len(expected_cycle)
    p = sum(i >= r for i in expected_cycle)
    charge = sum(i - collapse[i] for i in expected_cycle)
    assert (q, p, charge) == (4, 1, expected_collapse)
    assert charge == s*q - e*p
    d = gcd(e, s)
    assert charge % d == 0
    active_residues = {i % d for i in f_sources}
    if expected_collapse == 0:
        assert d == 3 and active_residues == {0, 1}
        assert periodic == {i for i in range(e) if i % d == 0}
    else:
        assert d == 1 and active_residues == {0}
        assert charge >= d

    # Exact exponent calibration e*lambda = q*Lambda + charge*log(3/2).
    period, odd = 3*r + 2*s, 2*r + s
    lifted_period, lifted_odd = 3*q - p, 2*q - p
    assert e*lifted_odd == q*odd + charge
    assert e*lifted_period == q*period + charge


def test_auxiliary_surplus_rejects_the_fixed_coprime_abstract_control():
    """An allowed rank control fails the actual-block loss budget, exactly."""
    period, odd, even = 19, 12, 7
    lifted_period, lifted_odd, lifted_even = 11, 7, 4
    assert gcd(period, odd) == 1
    assert period == odd + even
    assert lifted_period == lifted_odd + lifted_even
    # Both logarithmic surpluses are positive, without floating point.
    assert 3**odd > 2**period
    assert 3**lifted_odd > 2**lifted_period
    # Original surplus is smaller: their ratio is 3**5 / 2**8 < 1.
    assert odd - lifted_odd == 5 and period - lifted_period == 8
    assert 3**5 < 2**8
    assert 3**odd * 2**lifted_period < 3**lifted_odd * 2**period
    # This is exactly (even-1)*Lambda <= log(3/2), not a float estimate.
    exponent = even - 1
    assert 2 * 3**(odd*exponent) <= 3 * 2**(period*exponent)
    # The abstract control has c_0=0, so this comparison prevents an actual
    # realization under the theorem. It makes no claim about numerical floors.


def test_archived_s3_cycle_has_one_wrong_high_guard():
    """The old threshold cycle is outside m>=16 and is not a Juggler cycle."""
    m, states = 3, (3, 5, 11)
    assert m < 16
    threshold_images = tuple(
        isqrt(n**3) if n < m*m else isqrt(n) for n in states)
    assert threshold_images == states[1:] + states[:1]
    assert all(m <= n < m**3 for n in states)
    wrong = tuple(n for n in states if (n % 2 == 1) != (n < m*m))
    assert wrong == (11,)
    assert _step(3) == 5 and _step(5) == 11
    assert _step(11) == 36 != 3
    assert 11 - 3**2 == 2
    assert 3**2 > 2**3

@pytest.mark.parametrize("t", [3, 65, 65537])
def test_fixed_late_g_partner_has_actual_guards_and_negative_net_shift(t):
    """Three fixed open paths, not cycles or a scan for periodic behavior."""
    m, k = t**6, t**8
    y, x = t**8 + 6, t**8 + 8
    p, h = t**12 + 9*t**4, t**12 + 12*t**4
    peak = t**18 + 18*t**10 + 54*t**2 - 1
    f, g = t**9 + 9*t - 1, t**9
    paths = ((y, p, m, g), (x, h, peak, f))
    assert tuple(tuple(a % 2 for a in path) for path in paths) == (
        (1, 0, 1, 1), (1, 1, 0, 1))
    states = set().union(*paths)
    assert min(states) == m and max(states) == peak
    assert m**3 < peak < m**4
    for path in paths:
        assert k <= path[0] < m*m and k <= path[-1] < m*m
        assert all(not k <= a < m*m for a in path[1:-1])
        assert all(_step(a) == b for a, b in zip(path, path[1:]))
    assert k <= y < x < _ceil_root((m+1)**4, 3)
    assert isqrt(isqrt(y**3)) == isqrt(isqrt(x**3)) == m
    assert y**3 - p*p == 27*t**8 + 216 > 0
    assert (p+1)**2 - y**3 == t**8*(2*t**4 - 27) + 18*t**4 - 215 > 0
    assert (m+1)**2 - p == t**4*(2*t*t - 9) + 1 > 0
    assert m*m < p < h < (m+1)**2
    assert y**3 >= (m*m + 1)**2 and x**3 < (m+1)**4
    # Exact form of delta_F(x) + log(log y / log x) < 0;
    # the late replacement shift exceeds this F tower's own defect.
    assert x**9 > f**8 > y**9
    assert all(path[-1] not in (x, y) for path in paths)


def test_full_cell_collapse_can_have_only_a_late_periodic_f():
    """One fixed abstract map separates inversion cuts from all cell cuts."""
    e, r, s = 12, 9, 3
    pi = (1, 0, 2, 3, 5, 4, 6, 7, 8)
    sigma = tuple((i+s) % e for i in pi + tuple(range(r, e)))
    expected_sigma = (0, 4, 8, 11, 2, 5, 7, 10, 1, 3, 6, 9)
    assert tuple(sigma[i] for i in expected_sigma) == (
        expected_sigma[1:] + expected_sigma[:1])
    assert _cycle_count(sigma) == 1
    cells = ((0, 1, 2), (4, 5, 6))  # F, G, late F in each cell.
    f_sources, partners, collapse_cuts = set(), {}, set()
    collapse = list(range(e))
    for first, g_rank, last in cells:
        f_sources.update((first, last))
        partners.update({first: g_rank, last: g_rank})
        collapse_cuts.update(range(first, last))
        for i in range(first, last + 1):
            collapse[i] = first
    inversion_cuts = {i for i in range(r) if pi[i] == i+1}
    assert inversion_cuts == {0, 4}
    assert inversion_cuts < collapse_cuts == {0, 1, 4, 5}
    assert len(f_sources) == len(collapse_cuts) == 4
    assert len(f_sources) - len(inversion_cuts) == 2
    d = gcd(e, s)
    assert {i % d for i in inversion_cuts} == {0, 1}
    assert {i % d for i in collapse_cuts} == {0, 1, 2}

    auxiliary = tuple((collapse[i]+s) % e for i in range(e))
    component = (3, 6, 7, 10, 1)
    periodic = set(component)
    assert tuple(auxiliary[i] for i in component) == component[1:] + component[:1]
    for source in range(e):
        point = source
        for _ in range(e):
            if point in periodic:
                break
            point = auxiliary[point]
        assert point in periodic
    for mapping in (sigma, auxiliary):
        assert all(mapping[i] > i for i in range(r))
        assert all(mapping[i] < i for i in range(r, e))
    periodic_f = periodic & f_sources
    assert periodic_f == {6}
    assert partners[6] == 5 < 6
    assert 5 not in periodic and auxiliary[5] == auxiliary[6]
    assert all(sigma[i] not in set(auxiliary) for i in f_sources)
    n, p = len(component), sum(i >= r for i in component)
    displacement = sum(i-collapse[i] for i in component)
    assert (n, p, displacement) == (5, 1, 3)
    assert displacement == s*n-e*p
    assert len(periodic_f) <= displacement
    assert e-n == 7 >= len(f_sources)
    # Integer calibration of the logarithmic component surplus.
    period, odd = 3*r+2*s, 2*r+s
    assert e*(2*n-p) == n*odd+displacement
    assert e*(3*n-p) == n*period+displacement


def test_fixed_counts_meet_a_rational_sufficient_covered_cell_condition():
    """Arithmetic feasibility only; these small counts are not a cycle claim."""
    m, even, odd, period = 729, 7, 12, 19
    assert gcd(period, odd) == 1 and period == odd + even
    assert 3**odd > 2**period and m > even
    # eta(m)<1/m and exp(e/m)<1/(1-e/m), since m>=3 and 0<e/m<1.
    # This exact rational comparison therefore suffices for
    # (e-1)*Lambda + e*eta(m) < log(3/2), without floating-point logs.
    assert 2*m*3**(odd*(even-1)) <= 3*(m-even)*2**(period*(even-1))

@pytest.mark.parametrize(
    "collapse,covered_f,uncovered_f,partners,component,expected_n_p_delta",
    [
        ((0, 0, 2, 2, 4, 5, 6), {1}, {3}, {1: 0, 3: 2},
         (1, 2, 4, 6), (4, 1, 1)),
        ((0, 0, 0, 3, 4, 5, 6), {1}, {2}, {1: 0, 2: 0},
         (2,), (1, 0, 2)),
    ],
)
def test_predecessor_projection_distinguishes_transient_and_periodic_holes(
        collapse, covered_f, uncovered_f, partners, component,
        expected_n_p_delta):
    """Two fixed abstract maps; neither asserts an integer-floor realization."""
    e, r, s = 7, 5, 2
    sigma = tuple((i+s) % e for i in range(e))
    assert gcd(e, s) == 1 and _cycle_count(sigma) == 1
    assert all(sigma[i] > i for i in range(r))
    assert all(sigma[i] < i for i in range(r, e))
    # The first control also has G rank 2; the second instead has G rank 3.
    g_sources = set(range(r)) - (covered_f | uncovered_f)
    assert 0 in g_sources
    assert all(partner in g_sources for partner in partners.values())
    auxiliary = tuple((i+s) % e for i in collapse)
    periodic = set(component)
    assert tuple(auxiliary[i] for i in component) == component[1:] + component[:1]
    for source in range(e):
        point = source
        for _ in range(e):
            if point in periodic:
                break
            point = auxiliary[point]
        assert point in periodic
    assert all(auxiliary[i] == sigma[i] for i in g_sources | set(range(r, e)))
    f_sources = covered_f | uncovered_f
    assert all(sigma[i] not in set(auxiliary) for i in f_sources)
    assert all(auxiliary[i] == auxiliary[partners[i]] for i in f_sources)
    n, p = len(component), sum(i >= r for i in component)
    charge = sum(i-collapse[i] for i in component)
    assert (n, p, charge) == expected_n_p_delta
    assert charge == s*n-e*p > 0
    negative_f = periodic & f_sources
    assert all(partners[i] < i for i in negative_f)
    assert sum(i-collapse[i] for i in negative_f) <= charge
    assert all(partners[i] not in periodic for i in negative_f)
    assert e-n >= len(f_sources)
    odd, period = 2*r+s, 3*r+2*s
    assert (odd, period) == (12, 19)
    assert e*(2*n-p) == n*odd+charge
    assert e*(3*n-p) == n*period+charge
    if n > 1:
        # Global uncovered existence holds, but no periodic point is uncovered.
        # Q55 excludes an actual realization under the existing m=729 condition.
        assert periodic & uncovered_f == set()
        assert negative_f == {1} <= covered_f
        assert all(auxiliary[i] > i for i in range(r))
    else:
        # Projection is allowed to have a lower fixed point: no growth premise.
        assert periodic == uncovered_f == {2}
        assert auxiliary[2] == 2 and sigma[2] > 2

def test_sorted_quartic_envelope_keeps_positive_redistributed_defects():
    """Fixed e=12 abstract prefix control, with rational potentials only."""
    from fractions import Fraction as F

    e, r, s = 12, 9, 3
    pi = (1, 0, 2, 3, 5, 4, 6, 7, 8, 9, 10, 11)
    circumference, b = F(1), F(1, 2)

    def z(i):
        return F(i, e)

    actual = tuple(z(i)+b-z(s+pi[i]) for i in range(e))
    redistributed = tuple(z(i)+b-z(s+i) for i in range(e))
    assert all(loss > 0 for loss in actual)
    assert all(loss > 0 for loss in redistributed)
    assert actual != redistributed
    assert sorted(s+pi[i] for i in range(r)) == list(range(s, e))
    for i in range(r):
        bound = z(i)+b
        assert all(z(s+pi[j]) <= bound for j in range(i+1))
        assert z(s+i) <= bound
    assert sum(actual) == sum(redistributed) == e*b-s*circumference
    gaps = tuple(z(i+1)-z(i) for i in range(e))
    for i in range(e):
        assert gaps[(i+s) % e]-gaps[i] == (
            redistributed[i]-redistributed[(i+1) % e])


def test_nonconstant_transport_control_preserves_every_lifted_witness():
    """Exact coefficients in A and Lambda; no integer-floor realization."""
    from fractions import Fraction as F

    # A coefficient pair denotes a*A+b*Lambda. The existing integer
    # comparisons prove 0<Lambda<A at these same fixed counts.
    def add(x, y):
        return tuple(a+b for a, b in zip(x, y))

    def sub(x, y):
        return tuple(a-b for a, b in zip(x, y))

    def scale(c, x):
        return tuple(c*a for a in x)

    zero, A, surplus = (F(0), F(0)), (F(1), F(0)), (F(0), F(1))
    e, r, s = 7, 5, 2
    assert 2**19 < 3**12 and 2*3**12 < 3*2**19
    sigma = tuple((i+s) % e for i in range(e))
    collapse = (0, 0, 0, 3, 4, 5, 6)
    projected = tuple((a+s) % e for a in collapse)
    assert _cycle_count(sigma) == 1
    assert projected[2] == 2 and all(projected[i] != i for i in range(e) if i != 2)
    f_sources, g_sources = {1, 2}, {0, 3, 4}
    assert f_sources | g_sources == set(range(r))

    def h(i):
        return scale(F(1, 100), surplus) if i % e == 2 else zero

    def z(i):
        return add(scale(F(i, e), A), h(i))

    b = (F(s, e), F(1, e))
    loss = tuple(add(scale(F(1, e), surplus), sub(h(i), h(i+s)))
                 for i in range(e))
    assert len(set(loss)) == 3
    assert all(a == 0 and l > 0 for a, l in loss)
    total = zero
    for i in range(e):
        total = add(total, loss[i])
        assert z(i+s) == sub(add(z(i), b), loss[i])
        assert sub(z(i+e), z(i)) == A
    assert total == surplus
    gap = tuple(sub(z(i+1), z(i)) for i in range(e))
    # Every gap >=A/7-Lambda/100>0; pairwise gap oscillation <=Lambda.
    assert all(a == F(1, 7) and abs(l) <= F(1, 100) for a, l in gap)
    assert max(g[1] for g in gap)-min(g[1] for g in gap) <= 1
    for i in range(e):
        assert sub(gap[(i+s) % e], gap[i]) == sub(loss[i], loss[(i+1) % e])

    tau = (F(1, 7), F(-3, 7))
    visited = []
    rank = 0
    for _ in range(e):
        visited.append(rank % e)
        normalized = scale(F(1, 2), sub(z(rank+2), z(rank)))
        margin = sub(normalized, tau)
        assert margin[0] == 0 and margin[1] > 0
        rank += s
    assert len(set(visited)) == e
    source = sub(z(2), z(0))
    target = sub(z(4), z(2))
    assert source == add(target, sub(loss[2], loss[0]))

@pytest.mark.parametrize("t", [3, 65, 65537])
def test_separated_minimum_g_and_f_paths_at_fixed_scales(t):
    """Exact open paths with distinct cells and certified gap comparisons."""
    m = t**6 - 4
    y, x = t**8 - 4*t*t - 2, t**8 + 8
    h = t**12 - 6*t**6 - 3*t**4 + 6
    q = t**9 - 6*t**3
    hx = t**12 + 12*t**4
    p, f = t**18 + 18*t**10 + 54*t*t - 1, t**9 + 9*t - 1
    g_path, f_path = (y, h, m, q), (x, hx, p, f)
    assert tuple(n % 2 for n in g_path) == (1, 0, 1, 1)
    assert tuple(n % 2 for n in f_path) == (1, 1, 0, 1)
    assert all(_step(a) == b for path in (g_path, f_path)
               for a, b in zip(path, path[1:]))
    assert y**3-h*h == 12*t**10+3*t**8+8*t**6-60*t**4-48*t*t-44 > 0
    assert (h+1)**2-y**3 == 2*t**12-12*t**10-3*t**8-20*t**6+54*t**4+48*t*t+57 > 0
    assert h-m*m == 2*t**6-3*t**4-10 > 0
    assert (m+1)**2-h == 3*t**4+3 > 0
    assert m**3-q*q == 12*t**6-64 > 0
    assert (q+1)**2-m**3 == 2*t**9-12*t**6-12*t**3+65 > 0
    section = (y, x, q, f)
    assert tuple(sorted(section)) == section
    assert all(m**4 <= a**3 and a < m*m for a in section)
    assert all(not (m**4 <= a**3 and a < m*m) for a in (h, m, hx, p))
    assert min(g_path+f_path) == m and max(g_path+f_path) == p
    assert m**3 < p < m**4
    valleys = tuple(isqrt(isqrt(a**3)) for a in section)
    assert valleys[0] == m and valleys[1] == t**6
    assert tuple(sorted(set(valleys))) == valleys
    assert valleys[1] not in set(g_path+f_path)
    ghost = isqrt(valleys[1]**3)
    assert q < ghost == t**9 < f and ghost not in section
    # Integer sufficient comparisons for all three ordinary log-log gaps
    # >eta(m); the written proof uses the decreasing derivative 1/(a log a).
    assert 3*m >= 2*t**6 and m >= t**5
    assert 3*x <= 4*t**8 and x <= t**9
    assert 3*f <= 4*t**9 and f <= t**10
    assert y >= t**7 and q-x > t**8
    assert (x-y)*m*5 > x*9
    assert (q-x)*m*5 > q*9
    assert (f-q)*m*5 > f*10
    # The wrap is >=log(21/20)>1/21>eta(m); these powers verify its anchors.
    assert y**3 >= t**21 and f*f <= t**20
    assert m >= 725
    # The tempting uncorrected G source has a wrong first-image parity.
    bad_y = t**8-4*t*t
    assert _step(bad_y) == t**12-6*t**6+6
    assert _step(bad_y) % 2 == 1
    # No outgoing return edge from q or f is asserted.


def test_small_endpoint_equality_keeps_full_local_f_guards():
    """A small local equality; it does not satisfy the large-minimum premise."""
    path = (9, 27, 140, 11)
    assert tuple(n % 2 for n in path) == (1, 1, 0, 1)
    assert all(_step(a) == b for a, b in zip(path, path[1:]))
    valley = isqrt(path[1])
    assert valley == 5 and isqrt(valley**3) == path[-1]
    assert path[1] >= valley**2+2
    assert path[1]**3 < (isqrt(valley**3)+1)**4
    assert _ceil_root(valley**4, 3) == path[0]


def test_fixed_ghost_matching_localizes_reentry_and_detects_nonclosure():
    """Abstract target matching at existing counts, not actual F endpoints."""
    # The O-values are exact. The assigned targets test only finite matching;
    # no H-source array or guarded F realization is claimed for this control.
    e, r, s, m = 7, 5, 2, 729
    valleys = (m, m+1, m+2, m+6, m+8)
    images = tuple(isqrt(v**3) for v in valleys)
    targets = (images[0], images[2], images[2]+2, images[3], images[4])
    assert tuple(sorted(set(images))) == images
    assert tuple(sorted(set(targets))) == targets
    assert e == r+s and len(targets) == r
    strict = {i for i in range(r) if images[i] < targets[i]}
    assert strict == {1, 2}
    assert all(images[i] <= targets[i] for i in range(r))
    assert all(targets[i-1] <= images[i] <= targets[i] for i in range(1, r))
    assert images[1] not in targets
    assert images[2] == targets[1] and images[2] < targets[2]
    assert valleys[2] == valleys[1]+1 <= 2*m
    assert targets[1] == isqrt((valleys[1]+1)**3)
    # Adding all valleys fails closure because the next O-image list is not
    # the selected target list. Equality of the two sorted lists would suffice.
    assert set(images) != set(targets)
    assert sum(w not in targets for w in images) == 1


@pytest.mark.parametrize("t", [2**16+9, 2**32+9, 2**64+9])
def test_unbounded_guarded_endpoint_equality_at_fixed_scales(t):
    """Replay the uniform polynomial family; these open paths are not cycles."""
    v = t**6-3*t*t+6
    x = t**8-4*t**4+8*t*t+2
    h = t**12-6*t**8+12*t**6+9*t**4-24*t*t+21
    twice_p = (2*(t**18-9*t**14+18*t**12+27*t**10-90*t**8
                  +108*t**4+81)+117*t**6-297*t*t)
    eight_q = 8*t**9-36*t**5+72*t**3+27*t-7
    assert t >= 8192 and t % 16 == 9
    assert twice_p % 4 == 0 and eight_q % 16 == 8
    p, q = twice_p//2, eight_q//8
    assert tuple(a % 2 for a in (x,h,p,q,v)) == (1,1,0,1,0)
    path = (x,h,p,q)
    assert all(_step(a) == b for a,b in zip(path,path[1:]))
    assert isqrt(h) == v and isqrt(v**3) == q
    assert v > 350000000
    assert h-v*v == 12*t*t-15 > 0
    assert (v+1)**2-h == 2*t**6-18*t*t+28 > 0
    assert x**3-h*h == (2*t**12-24*t**10+87*t**8+56*t**6
                        -618*t**4+1104*t*t-433) > 0
    assert (h+1)**2-x**3 == (24*t**10-99*t**8-32*t**6+636*t**4
                             -1152*t*t+476) > 0
    assert all(lo > 0 and hi > 0 for lo,hi in (
        (h**3-p*p,(p+1)**2-h**3),
        (p-q*q,(q+1)**2-p),
        (v**3-q*q,(q+1)**2-v**3)))
    assert _ceil_root(v**4,3) == x
    # This actual F tower's coupled OE pair uses h -> p -> q.
    # Its E target q differs from the even auxiliary valley v.
    R, Q = h**3-p*p, p-q*q
    assert R % 2 == Q % 2 == 1 and (R >= 3 or Q >= 3)
    assert h**3 >= (q*q+1)**2+3


def test_minimal_e_remainder_is_realized_by_an_actual_open_pair():
    """A finite local control, with no large-minimum or periodicity claim."""
    x,p,v = 847,24650,157
    assert tuple(a % 2 for a in (x,p,v)) == (1,0,1)
    assert _step(x) == p and _step(p) == v
    assert x**3-p*p == 22923
    assert (p+1)**2-x**3 == 26378
    assert p-v*v == 1 and (v+1)**2-p == 314


def _fixed_cubic_terminal_coefficients():
    """A word/rank control at existing counts, not integer cycle states."""
    L,e = 19,7
    o = L-e
    u = pow(e,-1,L)
    vlen = L-u
    odd = tuple((n*e) % L < o for n in range(L))
    pairs = tuple((n,(n+1) % L) for n in range(L)
                  if odd[n] and not odd[(n+1) % L])
    assert u == 11 and vlen == 8 and gcd(e,L) == 1
    assert pairs == ((1,2),(4,5),(7,8),(9,10),(12,13),(15,16),(17,18))
    P = tuple(int(u <= n < L-1)-int(0 <= n < vlen-1) for n in range(L))
    mixed = tuple(int(n in (L-1,0))-int(n in (vlen-1,vlen)) for n in range(L))
    Q = tuple(int(1 <= n < u)-int(vlen+1 <= n < L) for n in range(L))
    return L,pairs,(P,mixed,Q)


def test_fixed_terminal_pair_boundaries_and_exact_cancellation():
    L,pairs,(P,mixed,Q) = _fixed_cubic_terminal_coefficients()
    assert [pair for pair in pairs if P[pair[0]] != P[pair[1]]] == [(17,18)]
    assert [pair for pair in pairs if mixed[pair[0]] != mixed[pair[1]]] == [(17,18)]
    assert all(Q[a] == Q[b] for a,b in pairs)
    assert [(c[17],c[18]) for c in (P,mixed,Q)] == [(1,0),(0,1),(-1,-1)]
    assert all(P[n]+mixed[n]+Q[n] == 0 for n in range(L))
    assert all((c[a],c[b]) not in ((1,-1),(-1,1))
               for c in (P,mixed,Q) for a,b in pairs)


def test_cut_pair_bounds_attain_extrema_in_fixed_relaxation():
    """Exact finite LP control; no floor-cell attainability is asserted."""
    from itertools import product

    L,pairs,coefficients = _fixed_cubic_terminal_coefficients()
    k = tuple(range(1,len(pairs)+1))
    D = tuple(3*a for a in k)
    free = 17
    old = sum(D)+free
    measured = [[None,None] for _ in coefficients]
    # Enumerate endpoint allocations covering every extremum in the
    # stated nonnegative residual relaxation. Each mandatory pair
    # remainder chooses a leg, and free mass chooses a single edge.
    # This list can also include nonvertices of that relaxation.
    for bits in product((0,1),repeat=len(pairs)):
        base = [0]*L
        for j,(a,b) in enumerate(pairs):
            base[a] += k[j]
            base[(a,b)[bits[j]]] += D[j]-k[j]
        for edge in range(L):
            residual = base.copy()
            residual[edge] += free
            assert sum(residual) == old
            for i,c in enumerate(coefficients):
                value = sum(a*b for a,b in zip(c,residual))
                lo,hi = measured[i]
                measured[i] = [value if lo is None else min(lo,value),
                               value if hi is None else max(hi,value)]
    for i,c in enumerate(coefficients):
        pair_lo = sum(min(c[a],c[b])*D[j] for j,(a,b) in enumerate(pairs))-free
        pair_hi = sum(max(c[a],c[b])*D[j] for j,(a,b) in enumerate(pairs))+free
        lo = sum(c[a]*k[j]+min(c[a],c[b])*(D[j]-k[j])
                 for j,(a,b) in enumerate(pairs))-free
        hi = sum(c[a]*k[j]+max(c[a],c[b])*(D[j]-k[j])
                 for j,(a,b) in enumerate(pairs))+free
        assert measured[i] == [lo,hi]
        assert -old < pair_lo <= lo <= hi <= pair_hi < old
        assert lo-pair_lo == (k[-1] if i == 0 else 0)
        assert pair_hi-hi == (k[-1] if i == 1 else 0)
