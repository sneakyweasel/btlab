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
HULL_MIN = F(95, 112)  # Theorem 4
RECORD_MU = F(13, 84)  # Bourgain's subconvexity exponent

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
    assert BA_FLOOR > A_FLOOR > DENSITY


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
