"""Paper B prefix counts: word geometry."""
from __future__ import annotations
from fractions import Fraction




def iterate_exponents(w: str) -> list[Fraction]:
    """Exponents of ``J^1(n), ..., J^{|w|}(n)`` in ``P`` for a start ``n ~ P`` with word ``w``.

    ``e_0 = 1`` and ``e_t = (3/2)e_{t-1}`` or ``(1/2)e_{t-1}`` as letter ``t`` is ``O`` or ``E``.
    """
    e, out = Fraction(1), []
    for c in w:
        e = e * (Fraction(3, 2) if c == "O" else Fraction(1, 2))
        out.append(e)
    return out


def phase_exponents(w: str) -> list[Fraction]:
    """The sawtooth phases a length-``|w|`` word needs: ``e_1, ..., e_{|w|-1}``.

    Letter ``t`` constrains the parity of ``J^{t-1}``, so a word of length ``d`` needs the waves
    at ``e_1`` through ``e_{d-1}``; the first letter is ``n`` itself, carried by ``n = 2r+1``.
    """
    return iterate_exponents(w)[:len(w) - 1]


def theta_coefficients(w: str, t: int) -> list[Fraction]:
    """Exponents ``gamma_s = e_{t-1} - e_s`` of the floor defects in letter ``t``'s linearized wave.

    Letter ``t`` constrains the parity of ``J^{t-1}``, so its wave sits at ``alpha = e_{t-1}``;
    linearizing in the earlier defects ``theta_s`` gives each a coefficient of size ``n^gamma_s``.
    The formula reproduces the paper's own constants: at the fifth letter of ``OOEO*`` it returns
    3/16, -9/16, 9/16 -- the ``C``, the discarded remainder, and the ``B`` of that proof -- and at
    the fourth letter of ``OOO*`` it returns the ``W ~ k n^{9/8}`` of Section 3.4.
    """
    e = iterate_exponents(w)
    alpha = e[t - 2]
    return [alpha - e[s] for s in range(t - 2)]


def drift_blocked(w: str, t: int) -> list[Fraction]:
    """Defect coefficients of letter ``t`` that admit no drift-1 interval, i.e. ``gamma_s > 1``.

    A coefficient ``n^gamma`` has derivative ``n^(gamma-1)``, so it moves by less than one between
    consecutive integers exactly below the threshold.  Above it, Theorem 4.8's shifted window has
    no interval to run on and the letter needs a kernel theorem: two such at ``OOO*``'s fourth
    letter (closed by Theorem 5.3), three at ``OOOO*``'s fifth (open, Conjecture 7.3).
    """
    return [g for g in theta_coefficients(w, t) if g > 1]


def step_exponents(w: str) -> list[Fraction]:
    """The per-letter maps: ``3/2`` after an odd letter, ``1/2`` after an even."""
    return [Fraction(3, 2) if c == "O" else Fraction(1, 2) for c in w]


def defect_coefficient(w: str, t: int, s: int) -> tuple[Fraction, Fraction]:
    """``(constant, exponent)`` of ``theta_s`` in letter ``t``'s phase, the constant in units of k.

    Letter ``t``'s wave is ``e(k J^{t-1}/2)``, and ``J^{t-1}`` depends on ``theta_s`` through the
    chain, so the coefficient is ``(k/2) * prod_{q=s+1}^{t-1} p_q`` at exponent ``e_{t-1} - e_s``.
    That reproduces all three constants the paper names: Theorem 5.3's own kernel monomial
    ``(3k/4)n^{9/8}``, and Theorem 6.3's ``C = (9k/16)n^{3/16}`` and ``B = (3k/4)v^{1/4}``.
    """
    p = step_exponents(w)
    const = Fraction(1, 2)
    for q in range(s + 1, t):
        const *= p[q - 1]
    e = iterate_exponents(w)
    return const, e[t - 2] - e[s - 1]


def defect_level(s: int) -> int:
    """The paper's level for ``theta_s``: its argument carries ``s-1`` floors inside.

    ``theta_2 = {floor(n^{3/2})^{3/2}}`` is the level-2 floor defect of Section 4, and the
    ``OOOO*`` kernel of Conjecture 7.3 rides ``theta_3`` and is called level-3 there.
    """
    return s


DRIFT_THRESHOLD = Fraction(1)            # above this, no drift-1 interval exists


STOP_THRESHOLD = Fraction(9, 4)          # above this, Conjecture 7.3 says every method stops


def deepest_blocked(w: str, t: int) -> tuple[int, Fraction, Fraction, str] | None:
    """The deepest defect of letter ``t`` above the drift threshold: the kernel level required.

    Returns ``(s, constant, exponent, species)`` or ``None``.  The shallower defects are not free,
    but they are the ones earlier theorems already resolve, so it is the deepest that names the
    kernel.  This reproduces the paper's own vocabulary on every case it settles: ``OOEO*``'s
    fifth letter has none and is proved by drift-1 windows alone; ``OOO*``'s fourth returns level
    2 with the monomial ``(3k/4)n^{9/8}``, which is Theorem 5.3's statement verbatim; ``OOOO*``'s
    fifth returns level 3 with ``(3k/4)n^{27/16}``, whose derivative ``k n^{11/16}`` is the
    ``varrho' ~ kP^{11/16}`` that Conjecture 7.3 quotes.
    """
    prof = blocked_profile(w, t)
    if not prof:
        return None
    s, _, species = max(prof, key=lambda r: r[0])
    const, exponent = defect_coefficient(w, t, s)
    return s, const, exponent, species


def branch_run_exponent(base_exponent: Fraction) -> Fraction:
    """Length exponent of the runs on which the branch floor is constant: ``2 - e``.

    A level-``L`` kernel takes its branch decomposition from ``floor(Delta_1 J^{L-1})``, whose
    argument sits at scale exponent ``e = e_{L-1}``.  That difference has derivative ``~ h P^{e-1}``,
    so the floor is constant on runs of length ``~ P^{2-e}/h``.  At level 2, ``e = 3/2`` gives the
    ``P^{1/2}/h`` runs of Lemma 5.1(iii); at level 3, ``e = 9/4`` gives a negative exponent, which
    is Conjecture 7.3's complaint that ``v`` jumps by ``~ n^{5/4}`` per step and the branch
    decomposition has no analogue there.
    """
    return 2 - Fraction(base_exponent)


def has_branch_runs(base_exponent: Fraction) -> bool:
    """Do runs of length ``> 1`` exist?  Equivalently ``e < 2``."""
    return branch_run_exponent(base_exponent) > 0


def composed_map(w: str, t: int, s: int) -> Fraction:
    """``E = prod_{q=s+1}^{t-1} p_q``: the power map carrying ``J^s`` to letter ``t``'s wave.

    Composing power maps composes to a single power, so the wave is ``(J^s)^E`` before flooring.
    Every kernel the paper forms has ``E = 3/2`` -- its defect sits exactly one letter below its
    wave, which is the shape of Lemma 5.1(i), ``c theta = (k/2)(Z^{3/2} - floor(Z)^{3/2})``.
    """
    out = Fraction(1)
    for q in range(s + 1, t):
        out *= step_exponents(w)[q - 1]
    return out


def linearisation_safe(w: str, t: int) -> bool:
    """Is the kernel's own defect safe to linearise, i.e. is ``E < 2``?

    The second-order term sits at ``e_{t-1} - 2 e_s``, and ``E = e_{t-1}/e_s``, so it is negligible
    exactly when ``E < 2``.  Positive second-order exponents at defects the kernel keeps *exact*
    are harmless -- they are never expanded -- so only the deepest blocked one is tested here.
    """
    deep = deepest_blocked(w, t)
    return True if deep is None else composed_map(w, t, deep[0]) < 2


def second_order_exponent(w: str, t: int, s: int) -> Fraction:
    """Exponent of the squared-defect term: ``e_{t-1} - 2 e_s``, negative when negligible."""
    e = iterate_exponents(w)
    return e[t - 2] - 2 * e[s - 1]


def branch_base(w: str, t: int) -> Fraction | None:
    """Scale exponent of the object letter ``t``'s kernel would branch on, or ``None`` if unblocked.

    The kernel rides the deepest blocked defect ``theta_{s*}``, and its branches come from
    ``floor(Delta_1 J^{s*-1})``, so the base sits at ``e_{s*-1}`` (and at ``1`` when ``s* = 1``,
    where the base is ``n`` itself and the difference is constant).
    """
    deep = deepest_blocked(w, t)
    if deep is None:
        return None
    s = deep[0]
    return iterate_exponents(w)[s - 2] if s >= 2 else Fraction(1)


def coefficient_sensitivity(w: str, t: int) -> list[tuple[int, Fraction]]:
    """How much the kernel's own coefficient moves with the floors kept exact inside it.

    The defects shallower than the kernel's are not expanded at all -- their floors stay exact in
    the kernel's argument -- so the only question is whether the coefficient can still be written
    as a monomial in ``n``.  Its sensitivity to ``theta_s`` has exponent ``(e_{t-1} - e_{s*}) - e_s``
    for the deepest blocked ``s*``, and a negative value means the monomial is exact to within
    ``o(1)``.  Theorem 5.3 returns ``-3/8``, which is why its statement can fix
    ``c(n) = (3k/4)n^{9/8}``; the level-3 kernel of Conjecture 7.3 returns ``+3/16`` and cannot.
    """
    deep = deepest_blocked(w, t)
    if deep is None:
        return []
    s_deep, _, coeff_exponent, _ = deep
    e = iterate_exponents(w)
    return [(s, coeff_exponent - e[s - 1]) for s in range(1, s_deep)]


def coefficient_is_monomial(w: str, t: int) -> bool:
    """Is every inner sensitivity negative, so the kernel weight is a clean monomial in ``n``?"""
    return all(x < 0 for _, x in coefficient_sensitivity(w, t))


def beyond_methods(w: str, t: int) -> list[Fraction]:
    """Defect coefficients above ``9/4``, the exponent past which Conjecture 7.3 says every
    method of the paper stops -- it names ``kn^{45/16}`` as the family that crosses it.
    """
    return [c for c in theta_coefficients(w, t) if c > STOP_THRESHOLD]


def defect_species(w: str, s: int) -> str:
    """Which floor produced ``theta_s``: ``"3/2"`` after an odd letter, ``"sqrt"`` after an even.

    Theorem 5.3's kernel is built for a 3/2-power defect -- its statement fixes the monomial
    ``c(n) = (3k/4)n^{9/8}`` riding ``theta_2`` -- and the square-root defect ``theta_w = {v^{1/2}}``
    of Theorem 6.3 is handled there only by drift-1 windows, never by a kernel.  So the species of
    a blocked coefficient decides whether an existing theorem is even the right shape.
    """
    return "3/2" if w[s - 1] == "O" else "sqrt"


def blocked_profile(w: str, t: int) -> list[tuple[int, Fraction, str]]:
    """``(s, coefficient exponent, species)`` for each defect of letter ``t`` above the threshold.

    ``OOO*``'s fourth letter and ``OOOO*``'s fifth are blocked only on 3/2-defects, which is why
    Theorem 5.3 and Conjecture 7.3 are the right shapes for them.  ``OOOEOEE`` is blocked on one
    3/2-defect at 33/32; ``OOEOOEE`` is blocked on a square-root defect at 45/32, for which the
    paper has no kernel theorem of any level.
    """
    return [(s, c, defect_species(w, s))
            for s, c in enumerate(theta_coefficients(w, t), start=1) if c > 1]


def wave_count(w: str) -> int:
    """Sawtooth waves to expand: one per letter after the first."""
    return len(w) - 1
