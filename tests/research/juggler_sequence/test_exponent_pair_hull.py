"""The two-monomial exponent-pair functional: process barrier and hull minimum.

All arithmetic exact (fractions).  Companion to
tests/research/juggler_sequence/test_bi_resonance_limit.py, which answers the
same boxed question for the Bombieri-Iwaniec method only.  Here the answer is
extended to *every* exponent pair and *every* A/B derivation:

  Theorem 1   phi(A(p, q)) >= 3/4 for every exponent pair (p, q), with
              equality only at the (non-pair) conjecture point (0, 1/2).
  Theorem 2   phi(B(A(p, q))) >= 13/16, same equality case.
  Cor. 3      an exponent pair with phi < 3/4 -- in particular any pair
              answering the boxed question phi < 2/3 -- is primitive:
              neither it nor its B-image is the A-image of an exponent pair.
  Theorem 4   the closure of the published pairs under A, B and convex
              combination has min phi = 95/112 exactly, at Bourgain's pair.
  Theorem 5   every exponent pair has mu(1/2) <= (p + q - 1/2)/2, so
              phi < 2/3 forces mu(1/2) < 1/12 and phi < 3/4 forces < 1/8:
              the line is strictly past the subconvexity record 13/84.

Theorem 4 is certified, not searched: A is the projective map
[x:y:w] -> [x : x+y+w : 2x+2w] with denominator 2(p+1)w > 0 on the region and
B is affine, so both carry a polytope to the polytope on the images of its
vertices.  It therefore suffices to exhibit one rational polytope containing
the seeds whose vertex images all lie inside it.
"""

from __future__ import annotations

from fractions import Fraction as F
from pathlib import Path

EXPORT_NOTE = Path("docs/theory/exponent_pair_two_monomial.md")

HALF = F(1, 2)
DENSITY = F(2, 3)  # the sub-density target for phi = (5/4)p + q
A_FLOOR = F(3, 4)  # Theorem 1
BA_FLOOR = F(13, 16)  # Theorem 2
C_FLOOR = F(91, 96)  # Theorem 6
D_FLOOR = F(27, 32)  # Theorem 7
HULL_MIN = F(95, 112)  # Theorem 4
RECORD_MU = F(13, 84)  # Bourgain's subconvexity exponent

# 2023--2025 published pairs, and the Sargos D-image of Bourgain.
# None of these is in the Theorem-4 seed list; all have phi > 95/112.
NEW_PAIRS: dict[str, tuple[F, F]] = {
    "trudgian_yang_2023_a": (F(715, 10238), F(7955, 10238)),
    "trudgian_yang_2023_b": (F(4742, 38463), F(35731, 51284)),
    "tao_trudgian_yang_2025_a": (F(89, 1282), F(997, 1282)),
    "tao_trudgian_yang_2025_b": (F(652397, 9713986), F(7599781, 9713986)),
    "tao_trudgian_yang_2025_c": (F(10769, 351096), F(609317, 702192)),
    "tao_trudgian_yang_2025_d": (F(89, 3478), F(15327, 17390)),
    "sargos_d_bourgain": (F(18, 199), F(593, 796)),
    "trudgian_yang_2023_c": (F(2779, 38033), F(58699, 76066)),
    "sargos_ad_bourgain": (F(9, 217), F(1461, 1736)),
    "cushing_2025_a": (F(311, 4822), F(3799, 4822)),
    "cushing_2025_b": (F(80219, 1298878), F(515638, 649439)),
}

# The published pairs.  (0, 1) is the trivial seed; the other four are the
# Bombieri-Iwaniec line, in the order of the achieved chain.
SEEDS: dict[str, tuple[F, F]] = {
    "trivial": (F(0), F(1)),
    "bombieri_iwaniec_1986": (F(9, 56), F(9, 56) + HALF),
    "huxley_1993": (F(89, 570), F(89, 570) + HALF),
    "huxley_2005": (F(32, 205), F(269, 410)),
    "bourgain_2017": (F(13, 84), F(55, 84)),
}
CONJECTURE_POINT = (F(0), HALF)  # (0, 1/2): not an exponent pair


def phi(p: F, q: F) -> F:
    """The T_j block functional: exponent pair (p, q) gives M^{(5/4)p+q}."""
    return F(5, 4) * p + q


def transform_a(p: F, q: F) -> tuple[F, F]:
    d = 2 * p + 2
    return p / d, (p + q + 1) / d


def transform_b(p: F, q: F) -> tuple[F, F]:
    return q - HALF, p + HALF


def transform_c(p: F, q: F) -> tuple[F, F]:
    d = 12 * (1 + 4 * p)
    return p / d, (11 * (1 + 4 * p) + q) / d


def transform_d(p: F, q: F) -> tuple[F, F]:
    d = 8 * (5 * p + 3 * q + 2)
    return (5 * p + q + 2) / d, (29 * p + 21 * q + 10) / d


def mu_half(p: F, q: F) -> F:
    """The zeta exponent an exponent pair yields: mu(1/2) <= (p+q-1/2)/2."""
    return (p + q - HALF) / 2


def normalised_pairs(steps: int = 24):
    """A grid of normalised exponent pairs 0 <= p <= 1/2 <= q <= 1."""
    for i in range(steps + 1):
        for j in range(steps + 1):
            yield F(i, 2 * steps), HALF + F(j, 2 * steps)


# --------------------------------------------------------------------------
# Theorem 1 / Theorem 2: the process barriers.
# --------------------------------------------------------------------------


def test_a_image_identity_and_floor():
    # phi(A) = (9p + 4q + 4)/(8(p+1)); deficiency form ((1-q) - p/4)/(2p+2).
    for p, q in normalised_pairs():
        ap, aq = transform_a(p, q)
        assert phi(ap, aq) == (9 * p + 4 * q + 4) / (8 * (p + 1))
        assert 1 - phi(ap, aq) == ((1 - q) - p / 4) / (2 * p + 2)
        assert phi(ap, aq) >= A_FLOOR


def test_a_floor_is_attained_only_at_the_conjecture_point():
    assert phi(*transform_a(*CONJECTURE_POINT)) == A_FLOOR
    # At q = 1/2 the excess is exactly 3p/(8(p+1)), so p > 0 is strict.
    for i in range(1, 25):
        p = F(i, 48)
        assert phi(*transform_a(p, HALF)) - A_FLOOR == 3 * p / (8 * (p + 1))
        assert phi(*transform_a(p, HALF)) > A_FLOOR
    # and q > 1/2 is strict too (the functional is increasing in q).
    for j in range(1, 25):
        assert phi(*transform_a(F(0), HALF + F(j, 48))) > A_FLOOR


def test_ba_image_identity_and_floor():
    for p, q in normalised_pairs():
        bap, baq = transform_b(*transform_a(p, q))
        assert phi(bap, baq) == (8 * p + 5 * q + 4) / (8 * (p + 1))
        assert phi(bap, baq) >= BA_FLOOR
    assert phi(*transform_b(*transform_a(*CONJECTURE_POINT))) == BA_FLOOR
    for i in range(1, 25):
        p = F(i, 48)
        excess = phi(*transform_b(*transform_a(p, HALF))) - BA_FLOOR
        assert excess == 3 * p / (16 * (p + 1))
        assert excess > 0


def test_both_floors_clear_the_density_line():
    # This is the whole point: no process image can reach phi < 2/3.
    assert C_FLOOR > D_FLOOR > BA_FLOOR > A_FLOOR > DENSITY
    # The D-floor is one part in 224 below the hull minimum, but it is
    # attained only at the conjecture point.
    assert HULL_MIN - D_FLOOR == F(1, 224)


def test_c_image_identity_and_floor():
    for p, q in normalised_pairs():
        cp, cq = transform_c(p, q)
        assert phi(cp, cq) == (F(181, 4) * p + q + 11) / (12 * (1 + 4 * p))
        assert phi(cp, cq) >= C_FLOOR
    assert phi(*transform_c(HALF, HALF)) == C_FLOOR
    # Equality only at the trivial pair (1/2, 1/2): any smaller p or
    # larger q is strict.
    for i in range(0, 24):
        p = F(i, 48)
        assert phi(*transform_c(p, HALF)) > C_FLOOR or p == HALF
    for j in range(1, 25):
        assert phi(*transform_c(HALF, HALF + F(j, 48))) > C_FLOOR


def test_d_image_identity_and_floor():
    for p, q in normalised_pairs():
        dp, dq = transform_d(p, q)
        assert phi(dp, dq) == (141 * p + 89 * q + 50) / (32 * (5 * p + 3 * q + 2))
        assert phi(dp, dq) - D_FLOOR == (3 * p + 4 * q - 2) / (
            16 * (5 * p + 3 * q + 2)
        )
        assert phi(dp, dq) >= D_FLOOR
    assert phi(*transform_d(*CONJECTURE_POINT)) == D_FLOOR
    for i in range(1, 25):
        p = F(i, 48)
        assert phi(*transform_d(p, HALF)) > D_FLOOR
    for j in range(1, 25):
        assert phi(*transform_d(F(0), HALF + F(j, 48))) > D_FLOOR


def test_sargos_d_of_bourgain_matches_the_named_image():
    assert transform_d(*SEEDS["bourgain_2017"]) == NEW_PAIRS["sargos_d_bourgain"]
    assert transform_a(*NEW_PAIRS["sargos_d_bourgain"]) == NEW_PAIRS["sargos_ad_bourgain"]


# --------------------------------------------------------------------------
# Corollary 3: a solution must be primitive.
# --------------------------------------------------------------------------


def test_b_is_an_involution():
    for p, q in normalised_pairs():
        assert transform_b(*transform_b(p, q)) == (p, q)


def test_a_sub_density_pair_is_not_a_process_image():
    # Any (p, q) with phi < 3/4 is neither A(x) nor B(A(y)) for exponent
    # pairs x, y.  B being an involution, that is exactly the statement that
    # neither it nor its B-image lies in the image of A.
    a_images = {transform_a(*x) for x in normalised_pairs()}
    targets = [pq for pq in normalised_pairs() if phi(*pq) < A_FLOOR]
    assert targets  # the region below the floor is non-empty
    for pq in targets:
        assert pq not in a_images
        assert transform_b(*pq) not in a_images


# --------------------------------------------------------------------------
# Theorem 4: the certified hull minimum.
# --------------------------------------------------------------------------

TAIL = F(1, 10**4)  # the exactly A-invariant corner box at (0, 1)


def _cross(o, a, b):
    return (a[0] - o[0]) * (b[1] - o[1]) - (a[1] - o[1]) * (b[0] - o[0])


def _hull(points):
    """Exact monotone-chain convex hull, counter-clockwise."""
    pts = sorted(set(points))
    lower, upper = [], []
    for pt in pts:
        while len(lower) >= 2 and _cross(lower[-2], lower[-1], pt) <= 0:
            lower.pop()
        lower.append(pt)
    for pt in reversed(pts):
        while len(upper) >= 2 and _cross(upper[-2], upper[-1], pt) <= 0:
            upper.pop()
        upper.append(pt)
    return lower[:-1] + upper[:-1]


def _inside(vertices, z):
    n = len(vertices)
    return all(_cross(vertices[i], vertices[(i + 1) % n], z) >= 0 for i in range(n))


def _closure(depth: int):
    seen = set(SEEDS.values())
    frontier = list(seen)
    for _ in range(depth):
        nxt = []
        for pair in frontier:
            for image in (transform_a(*pair), transform_b(*pair)):
                if image not in seen:
                    seen.add(image)
                    nxt.append(image)
        frontier = nxt
        if not frontier:
            break
    return seen


def _tail_box():
    return [(F(0), 1 - TAIL), (TAIL, 1 - TAIL), (F(0), F(1)), (TAIL, F(1))]


def certified_polytope(depth: int = 14):
    """A rational polytope containing the whole A/B/convex closure."""
    tail = _tail_box()
    points = _closure(depth) | set(tail) | {transform_b(*c) for c in tail}
    return _hull(points)


def test_tail_box_is_exactly_a_invariant():
    tail = _tail_box()
    for corner in tail:
        ap, aq = transform_a(*corner)
        assert 0 <= ap <= TAIL and 1 - TAIL <= aq <= 1
    # phi >= q >= 1 - TAIL on the box, and stays above the minimum on B(box).
    assert min(phi(*c) for c in tail) >= HULL_MIN
    assert min(phi(*transform_b(*c)) for c in tail) >= HULL_MIN


def test_polytope_is_ab_invariant_and_contains_the_seeds():
    vertices = certified_polytope()
    for vertex in vertices:
        assert _inside(vertices, transform_a(*vertex))
        assert _inside(vertices, transform_b(*vertex))
    for pair in SEEDS.values():
        assert _inside(vertices, pair)


def test_hull_minimum_is_exactly_95_over_112():
    vertices = certified_polytope()
    smallest = min(phi(*v) for v in vertices)
    assert smallest == HULL_MIN
    assert [v for v in vertices if phi(*v) == smallest] == [SEEDS["bourgain_2017"]]
    # the deep closure really does sit inside the certificate
    for pair in _closure(16):
        assert _inside(vertices, pair)
    assert HULL_MIN > A_FLOOR > DENSITY


# --------------------------------------------------------------------------
# Theorem 5: the price of the line in the zeta normalisation.
# --------------------------------------------------------------------------


def test_zeta_exponent_of_the_recorded_pairs():
    assert mu_half(*SEEDS["bourgain_2017"]) == RECORD_MU
    assert mu_half(*SEEDS["huxley_2005"]) == F(32, 205)
    assert mu_half(*SEEDS["huxley_1993"]) == F(89, 570)
    assert mu_half(*SEEDS["bombieri_iwaniec_1986"]) == F(9, 56)
    assert mu_half(*SEEDS["trivial"]) == F(1, 4)
    # p + q is B-invariant, which is what makes the bound universal.
    for p, q in normalised_pairs():
        assert sum(transform_b(p, q)) == p + q


def test_sub_density_forces_a_new_subconvexity_record():
    # phi < c and p >= 0 give p + q < c - p/4, hence mu(1/2) < (c-1/2)/2 - p/8.
    seen_density = seen_floor = False
    for p, q in normalised_pairs(steps=40):
        value = phi(p, q)
        if value < DENSITY:
            assert mu_half(p, q) < F(1, 12) - p / 8 <= F(1, 12) < RECORD_MU
            seen_density = True
        if value < A_FLOOR:
            assert mu_half(p, q) < F(1, 8) < RECORD_MU
            seen_floor = True
    assert seen_density and seen_floor
    # the factor in the exponent that the line asks for over the record
    assert RECORD_MU / F(1, 12) == F(13, 7)


def test_export_note_records_the_barrier():
    text = EXPORT_NOTE.read_text(encoding="utf-8")
    assert "95/112" in text
    assert "3/4" in text
    assert "91/96" in text
    assert "27/32" in text
    assert "tao-trudgian-yang-2025-exponent-pairs" in text
    assert "cushing-2025-exponent-pairs" in text
    assert "311/4822" in text


def test_2023_2025_pairs_do_not_beat_bourgain():
    for name, pair in NEW_PAIRS.items():
        value = phi(*pair)
        assert value > HULL_MIN, name
        assert value > DENSITY, name
    assert phi(*NEW_PAIRS["trudgian_yang_2023_a"]) == F(35395, 40952)
    assert phi(*NEW_PAIRS["trudgian_yang_2023_b"]) == F(130903, 153852)
    assert phi(*NEW_PAIRS["tao_trudgian_yang_2025_a"]) == F(4433, 5128)
    assert min(phi(*pair) for pair in NEW_PAIRS.values()) == F(130903, 153852)
    assert phi(*NEW_PAIRS["cushing_2025_a"]) == F(16751, 19288)
    assert phi(*NEW_PAIRS["cushing_2025_b"]) == F(238221, 273448)
    assert phi(*NEW_PAIRS["trudgian_yang_2023_c"]) == F(131293, 152132)
    for pair in NEW_PAIRS.values():
        assert phi(*transform_b(*pair)) > HULL_MIN


# --------------------------------------------------------------------------
# Theorem 9 / tame companion: leftover threshold and p/2+q.
# --------------------------------------------------------------------------

TAME_HULL_MIN = F(275, 388)  # (1/2)p + q at B(A(Bourgain))
TAME_BOURGAIN = F(41, 56)  # the same functional at the Bourgain seed
TAME_GAP = F(49, 1164)  # TAME_HULL_MIN - 2/3
TAME_A_FLOOR = F(3, 4)
TAME_BA_FLOOR = F(5, 8)
TAME_C_FLOOR = F(15, 16)
TAME_D_FLOOR = F(87, 112)
TAME_BA_CRIT = F(31, 12)  # min of 4p+3q on named pairs


def phi_tame(p: F, q: F) -> F:
    """PS inversion of v^{3/2}: exponent pair (p, q) gives M^{p/2+q}."""
    return p / 2 + q


def leftover_exponent(alpha: F, beta: F) -> F:
    """Exponent of the uniform leftover bound n^{alpha(beta-1)}."""
    return alpha * (beta - 1)


def ba_bourgain() -> tuple[F, F]:
    return transform_b(*transform_a(*SEEDS["bourgain_2017"]))


def heath_brown_2017(m: int) -> tuple[F, F]:
    """ANTEDB Theorem 5.17: (p_m, q_m) for integer m >= 3."""
    p = F(2, (m - 1) ** 2 * (m + 2))
    q = 1 - F(3 * m - 2, m * (m - 1) * (m + 2))
    return p, q


def test_heath_brown_2017_sequence_misses_both_lines():
    assert heath_brown_2017(3) == (F(1, 10), F(23, 30))
    for m in range(3, 16):
        pair = heath_brown_2017(m)
        assert phi(*pair) > HULL_MIN
        assert phi_tame(*pair) > TAME_HULL_MIN
        assert 4 * pair[0] + 3 * pair[1] > TAME_BA_CRIT


def test_leftover_threshold_is_outer_exponent_one():
    # Theorem 9: leftover -> 0 iff beta < 1 (alpha > 0).
    assert leftover_exponent(F(3, 2), F(3, 4)) == F(-3, 8)  # decaying axis
    assert leftover_exponent(F(3, 2), F(3, 2)) == F(3, 4)  # tame axis
    assert leftover_exponent(F(3, 2), F(9, 4)) == F(15, 8)  # boxed axis
    assert leftover_exponent(F(3, 2), F(1)) == 0
    for beta in (F(1, 4), F(1, 2), F(3, 4), F(99, 100)):
        assert leftover_exponent(F(3, 2), beta) < 0
    for beta in (F(101, 100), F(3, 2), F(9, 4), F(3)):
        assert leftover_exponent(F(3, 2), beta) > 0


def test_sublinear_leftover_vanishes_on_a_sample():
    # alpha = 3/2, beta = 1/2: leftover is ≍ n^{-3/4}.
    import math

    for n in (10**4, 10**5, 10**6):
        v = math.isqrt(n**3)  # floor(n^{3/2})
        leftover = abs(math.sqrt(v) - n**0.75)
        assert leftover < 2 * n ** (-0.75)


def _frac_n32(n: int) -> float:
    """Exact-identity float for {n^{3/2}} = (n^3 - v^2)/(n^{3/2} + v)."""
    import math

    v = math.isqrt(n**3)
    return (n**3 - v * v) / (n**1.5 + v)


def test_superlinear_leftover_vanishes_on_perfect_squares():
    # Theorem 9 is a uniform threshold, not a pointwise size: n = 100^2
    # makes n^{3/2} an integer, so leftover is exactly 0 even for beta = 3/2.
    import math

    n = 10**4
    v = math.isqrt(n**3)
    assert v * v == n**3
    assert abs(v**1.5 - n**2.25) == 0.0


def test_superlinear_leftover_grows_when_frac_is_bounded():
    import math

    samples = []
    for start, stop in (
        (10**4, 10**4 + 400),
        (4 * 10**4, 4 * 10**4 + 400),
        (10**5, 10**5 + 400),
    ):
        found = next((n for n in range(start, stop) if _frac_n32(n) > 0.25), None)
        assert found is not None
        samples.append(found)
    leftovers = []
    for n in samples:
        v = math.isqrt(n**3)
        leftover = abs(v**1.5 - n**2.25)
        assert leftover > 0.2 * n**0.75
        leftovers.append(leftover)
    assert leftovers[-1] > leftovers[0]


def test_tame_functional_hull_minimum_is_275_over_388():
    vertices = certified_polytope()
    smallest = min(phi_tame(*v) for v in vertices)
    assert smallest == TAME_HULL_MIN
    assert [v for v in vertices if phi_tame(*v) == smallest] == [ba_bourgain()]
    assert TAME_HULL_MIN - DENSITY == TAME_GAP
    assert phi_tame(*SEEDS["bourgain_2017"]) == TAME_BOURGAIN
    assert TAME_BOURGAIN > TAME_HULL_MIN
    for pair in NEW_PAIRS.values():
        assert phi_tame(*pair) > TAME_HULL_MIN


def test_tame_process_identities_and_floors():
    assert TAME_BA_FLOOR < DENSITY < TAME_A_FLOOR < TAME_D_FLOOR < TAME_C_FLOOR
    for p, q in normalised_pairs():
        ap, aq = transform_a(p, q)
        assert phi_tame(ap, aq) == (3 * p + 2 * q + 2) / (4 * p + 4)
        assert phi_tame(ap, aq) >= TAME_A_FLOOR
        bap, baq = transform_b(ap, aq)
        assert (bap, baq) == (q / (2 * p + 2), (2 * p + 1) / (2 * p + 2))
        assert phi_tame(bap, baq) == (4 * p + q + 2) / (4 * p + 4)
        assert phi_tame(bap, baq) >= TAME_BA_FLOOR
        cp, cq = transform_c(p, q)
        assert phi_tame(cp, cq) == (89 * p + 2 * q + 22) / (24 * (1 + 4 * p))
        assert phi_tame(cp, cq) >= TAME_C_FLOOR
        dp, dq = transform_d(p, q)
        assert phi_tame(dp, dq) == (63 * p + 43 * q + 22) / (16 * (5 * p + 3 * q + 2))
        assert phi_tame(dp, dq) >= TAME_D_FLOOR
    assert phi_tame(*transform_a(HALF, HALF)) == TAME_A_FLOOR
    assert phi_tame(*transform_b(*transform_a(*CONJECTURE_POINT))) == TAME_BA_FLOOR
    assert phi_tame(*transform_c(HALF, HALF)) == TAME_C_FLOOR
    assert phi_tame(*transform_d(*CONJECTURE_POINT)) == TAME_D_FLOOR
    for i in range(1, 25):
        p = F(i, 48)
        assert phi_tame(*transform_b(*transform_a(p, HALF))) > TAME_BA_FLOOR
        assert phi_tame(*transform_d(p, HALF)) > TAME_D_FLOOR


def test_no_named_pair_crosses_the_tame_ba_line():
    def crit(p: F, q: F) -> F:
        return 4 * p + 3 * q

    assert crit(*SEEDS["bourgain_2017"]) == TAME_BA_CRIT
    assert crit(*NEW_PAIRS["trudgian_yang_2023_b"]) == TAME_BA_CRIT
    for name, pair in {**SEEDS, **NEW_PAIRS}.items():
        assert crit(*pair) >= TAME_BA_CRIT, name
        assert crit(*pair) > 2, name
        assert phi_tame(*transform_b(*transform_a(*pair))) >= TAME_HULL_MIN, name


def test_export_note_records_the_leftover_threshold():
    text = EXPORT_NOTE.read_text(encoding="utf-8")
    assert "leftover threshold" in text
    assert "275/388" in text
    assert "49/1164" in text
    assert "41/56" in text
    assert "5/8" in text
    assert "87/112" in text
    assert "15/16" in text
    assert "4p+3q" in text
