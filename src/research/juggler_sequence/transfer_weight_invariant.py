"""Phase-0 transfer-weight invariants for the four-step tilted moment.

Not a third formulation of the frontier, not a pressure census, and not
a halt theorem.  ``W_t`` is the tilted live pushforward on current
states, not the BT tail-reverse operator.  The listed candidates are
mass, max-atom, collision energy, and ancestry multiplicity.  Nothing
here is a proof of ``P_θ`` / ``M_{θ,q}``; the classification is whether
any of those quantities forces the five-word mass below the exact
four-step contraction threshold without location, ``L^2``, or cylinders.
"""

from __future__ import annotations

import json
import math
from collections import defaultdict
from typing import Any

from research.juggler_sequence.cycle_finance import git_commit
from research.juggler_sequence.lean_paths import DATA_ROOT
from research.juggler_sequence.tao_reduction import N0_LEAN, theta_of_C

DATA_DIR = DATA_ROOT / "transfer_weight_invariant"

POSITIVE_WORDS = frozenset({"EOOO", "OEOO", "OOEO", "OOOE", "OOOO"})
THREE_ODD_WORDS = frozenset({"EOOO", "OEOO", "OOEO", "OOOE"})
THETA_19 = theta_of_C(19)


def juggler(n: int) -> int:
    if n % 2 == 0:
        return math.isqrt(n)
    return math.isqrt(n * n * n)


def tilt_constants(theta: float = THETA_19) -> dict[str, float]:
    """Fair-coin one-step factor ``a`` and the four-step multipliers at ``θ``."""

    x = math.exp(theta)
    a = 0.5 * (1.0 + x)
    a4 = a**4
    r4 = (x**4) / a4
    r3 = (x**3) / a4
    r2 = (x**2) / a4
    return {
        "theta": theta,
        "x": x,
        "a": a,
        "a4": a4,
        "r4": r4,
        "r3": r3,
        "r2": r2,
        "r1": x / a4,
        "r0": 1.0 / a4,
        "coef_mu4": r4 - r2,
        "coef_mu3": r3 - r2,
        "rhs": 1.0 - r2,
    }


def onesided_excess(mu4: float, mu3: float, c: dict[str, float] | None = None) -> float:
    """Worst-case rest on two-odd words: ``coef4 μ4 + coef3 μ3 - rhs``.

    Negative means the one-sided cut is met.  Fair-coin five-word mass
    does not meet it; the exact moment still equals ``a^4`` because the
    eleven complementary words pay the deficit.
    """

    if c is None:
        c = tilt_constants()
    return c["coef_mu4"] * mu4 + c["coef_mu3"] * mu3 - c["rhs"]


def onesided_cut_holds(mu4: float, mu3: float, c: dict[str, float] | None = None) -> bool:
    return onesided_excess(mu4, mu3, c) < 0.0


def fair_coin_five_word_shares() -> tuple[float, float]:
    """Unweighted 16-word shares: one ``OOOO`` and four three-odd words."""

    return 1.0 / 16.0, 4.0 / 16.0


def location_free_mu_bound(
    max_atom: float,
    energy: float,
    n_s: int | None,
) -> dict[str, float]:
    """Sharp location-free bounds on ``μ(S)``.

    Without a bound on ``n_S = #(supp ∩ S)`` every bound is 1.  Large
    collision energy makes the Cauchy–Schwarz bound worse, not better.
    """

    mass_bound = 1.0
    if n_s is None:
        atom_bound = 1.0
        energy_bound = 1.0
    else:
        atom_bound = min(1.0, n_s * max_atom)
        energy_bound = min(1.0, math.sqrt(n_s * energy))
    return {
        "mass": mass_bound,
        "max_atom": atom_bound,
        "energy": energy_bound,
        "best": min(mass_bound, atom_bound, energy_bound),
    }


def inequalities_meet_onesided_cut(
    max_atom: float,
    energy: float,
    n_s: int | None,
    c: dict[str, float] | None = None,
) -> bool:
    """Whether the location-free bounds force the one-sided cut.

    The cut is a statement about ``μ4`` and ``μ3``.  The strongest
    location-free bound is a bound on ``μ(S) = μ4 + μ3``.  Even granting
    ``μ3 = 0`` (the most generous case for the cut), one still needs
    ``μ4 < rhs / coef4``.  A bound of 1 never meets that.
    """

    if c is None:
        c = tilt_constants()
    best = location_free_mu_bound(max_atom, energy, n_s)["best"]
    return onesided_cut_holds(best, 0.0, c)


def four_word(n: int, n0: int, steps: int = 4) -> tuple[str, int, bool]:
    """Next ``steps`` letters of ``n``, the image, and whether it stayed above ``n0``."""

    letters: list[str] = []
    image = n
    live = n > n0
    for _ in range(steps):
        if not live:
            break
        letters.append("O" if image % 2 else "E")
        image = juggler(image)
        if image <= n0:
            live = False
            break
    return "".join(letters), image, live


def integer_cbrt_ceil(a: int) -> int:
    """Smallest nonnegative ``n`` with ``n^3 >= a``."""

    if a <= 0:
        return 0
    n = int(round(a ** (1.0 / 3.0)))
    while n**3 < a:
        n += 1
    while n > 0 and (n - 1) ** 3 >= a:
        n -= 1
    return n


def integer_cbrt_floor_lt(a: int) -> int:
    """Largest nonnegative ``n`` with ``n^3 < a``."""

    if a <= 1:
        return 0
    n = int(round(a ** (1.0 / 3.0)))
    while n**3 >= a:
        n -= 1
    while (n + 1) ** 3 < a:
        n += 1
    return n


def oe_preimage_span(m: int) -> int:
    """Number of integers ``n`` with ``m^4 <= n^3 < (m+1)^4``.

    The interval length is ``~ (4/3) m^{1/3}`` and is therefore unbounded.
    The genuine ``OE`` ancestors are the odd points of this interval whose
    image is even; that subset is nonempty for arbitrarily large ``m``.
    """

    if m < 1:
        return 0
    lo = integer_cbrt_ceil(m**4)
    hi = integer_cbrt_floor_lt((m + 1) ** 4)
    return max(0, hi - lo + 1)


def oe_ancestor_count(m: int) -> int:
    """Odd starts whose image is even and lands in the even fibre of ``m``.

    ``even_preimage_iff``: every even in ``[m^2, (m+1)^2)`` maps to ``m``.
    An odd ``n`` collides at ``m`` after ``OE`` iff ``m^2 <= J(n) < (m+1)^2``
    and ``J(n)`` is even, i.e. ``m^4 <= n^3 < (m+1)^4``.
    """

    if m < 1:
        return 0
    lo = integer_cbrt_ceil(m**4)
    hi = integer_cbrt_floor_lt((m + 1) ** 4)
    count = 0
    n = lo if lo % 2 else lo + 1
    while n <= hi:
        image = juggler(n)
        if image % 2 == 0 and m * m <= image < (m + 1) * (m + 1):
            count += 1
        n += 2
    return count


def collect_oooo_starts(count: int, n0: int, limit: int) -> list[int]:
    """Live odd starts whose next four letters are ``OOOO``."""

    found: list[int] = []
    n = n0 + 1 if n0 % 2 == 0 else n0 + 2
    if n % 2 == 0:
        n += 1
    while n <= limit and len(found) < count:
        word, image, live = four_word(n, n0)
        if live and word == "OOOO" and image > n0:
            found.append(n)
        n += 2
    return found


def oooo_relabel_witness(starts: list[int], n0: int, theta: float = THETA_19) -> dict[str, Any]:
    """Four odd steps relabel the normalized profile and multiply mass by ``x^4``."""

    c = tilt_constants(theta)
    x = c["x"]
    before = {n: (1.0, 1) for n in starts}
    after: dict[int, tuple[float, int]] = {}
    words: list[str] = []
    for n, (weight, multiplicity) in before.items():
        word, image, live = four_word(n, n0)
        words.append(word)
        if not live:
            continue
        old_w, old_m = after.get(image, (0.0, 0))
        after[image] = (old_w + weight * (x ** word.count("O")), old_m + multiplicity)

    mass_before = sum(w for w, _ in before.values())
    mass_after = sum(w for w, _ in after.values())
    energy_before = sum(w * w for w, _ in before.values()) / mass_before**2
    energy_after = (
        sum(w * w for w, _ in after.values()) / mass_after**2 if mass_after else 0.0
    )
    max_atom_before = max(w for w, _ in before.values()) / mass_before
    max_atom_after = (
        max(w for w, _ in after.values()) / mass_after if mass_after else 0.0
    )
    ancestry_before = sorted(m for _, m in before.values())
    ancestry_after = sorted(m for _, m in after.values())
    return {
        "starts": starts,
        "images": sorted(after),
        "words": words,
        "injective": len(after) == len(before),
        "all_oooo": all(word == "OOOO" for word in words),
        "mass_ratio": mass_after / mass_before if mass_before else 0.0,
        "x4": x**4,
        "x4_over_a4": c["r4"],
        "energy_before": energy_before,
        "energy_after": energy_after,
        "max_atom_before": max_atom_before,
        "max_atom_after": max_atom_after,
        "ancestry_before": ancestry_before,
        "ancestry_after": ancestry_after,
        "positive_share": 1.0,
        "onesided_cut": onesided_cut_holds(1.0, 0.0, c),
        "location_free_meets_cut": inequalities_meet_onesided_cut(
            max_atom_before, energy_before, len(before), c
        ),
    }


def favorable_targets(count: int, start: int, limit: int, n0: int) -> list[int]:
    """Increasing ``m`` whose next four letters lie in the five positive cells."""

    found: list[int] = []
    m = max(start, n0 + 1)
    while m <= limit and len(found) < count:
        word, _, live = four_word(m, n0)
        if live and word in POSITIVE_WORDS:
            found.append(m)
        m += 1
    return found


def oe_multiplicity_witness(
    targets: list[int],
    n0: int,
) -> dict[str, Any]:
    rows = []
    for m in targets:
        word, _, live = four_word(m, n0)
        rows.append(
            {
                "m": m,
                "word": word,
                "live": live,
                "favorable": word in POSITIVE_WORDS,
                "oe_ancestors": oe_ancestor_count(m),
            }
        )
    counts = [row["oe_ancestors"] for row in rows]
    spans = [oe_preimage_span(m) for m in (10, 100, 1_000, 10_000, 100_000)]
    return {
        "rows": rows,
        "counts": counts,
        "spans": spans,
        "span_strictly_increasing": all(
            spans[i] < spans[i + 1] for i in range(len(spans) - 1)
        ),
        "last_count_exceeds_first": bool(counts) and counts[-1] > counts[0],
        "all_favorable": all(row["favorable"] and row["live"] for row in rows),
    }


def analyze_pushforward(
    starts: list[int],
    n0: int,
    dmax: int,
    theta: float = THETA_19,
) -> list[dict[str, Any]]:
    """Exact tilted pushforward of a finite odd cohort.  Not in the fast suite."""

    c = tilt_constants(theta)
    x = c["x"]
    a4 = c["a4"]
    states: dict[int, tuple[float, int]] = {n: (1.0, 1) for n in starts if n > n0}
    rows: list[dict[str, Any]] = []
    for depth in range(dmax + 1):
        if not states:
            break
        mass = sum(weight for weight, _ in states.values())
        word_mass: dict[str, float] = defaultdict(float)
        mass_after_four = 0.0
        positive_excess = 0.0
        dies = 0.0
        mu4 = 0.0
        mu3 = 0.0
        for state, (weight, _) in states.items():
            word, _, live = four_word(state, n0)
            if not live:
                dies += weight
                continue
            odd_count = word.count("O")
            multiplier = x**odd_count
            word_mass[word] += weight
            mass_after_four += weight * multiplier
            if word == "OOOO":
                mu4 += weight
                positive_excess += weight * (multiplier - a4)
            elif word in THREE_ODD_WORDS:
                mu3 += weight
                positive_excess += weight * (multiplier - a4)
        max_atom = max(weight for weight, _ in states.values()) / mass
        energy = sum(weight * weight for weight, _ in states.values()) / mass**2
        max_ancestry = max(multiplicity for _, multiplicity in states.values())
        mu4 /= mass
        mu3 /= mass
        rows.append(
            {
                "depth": depth,
                "support": len(states),
                "ratio4": mass_after_four / (a4 * mass) if mass else 0.0,
                "positive_share": mu4 + mu3,
                "positive_excess": positive_excess / (a4 * mass) if mass else 0.0,
                "death4": dies / mass,
                "max_atom": max_atom,
                "energy": energy,
                "max_ancestry": max_ancestry,
                "mu4": mu4,
                "mu3": mu3,
                "onesided_cut": onesided_cut_holds(mu4, mu3, c),
                "location_free_meets_cut": inequalities_meet_onesided_cut(
                    max_atom, energy, None, c
                ),
            }
        )
        nxt: dict[int, tuple[float, int]] = {}
        for state, (weight, multiplicity) in states.items():
            image = juggler(state)
            if image <= n0:
                continue
            next_weight = weight * (x if state % 2 else 1.0)
            old_w, old_m = nxt.get(image, (0.0, 0))
            nxt[image] = (old_w + next_weight, old_m + multiplicity)
        states = nxt
    return rows


def summary() -> dict[str, Any]:
    c = tilt_constants()
    mu4_fair, mu3_fair = fair_coin_five_word_shares()
    oooo_starts = collect_oooo_starts(5, N0_LEAN, 20_000)
    oooo = oooo_relabel_witness(oooo_starts, N0_LEAN)
    targets: list[int] = []
    for candidate in (2_000, 20_000, 200_000):
        found = favorable_targets(1, candidate, candidate + 20_000, N0_LEAN)
        targets.extend(found)
    oe = oe_multiplicity_witness(targets, N0_LEAN)
    starts = list(range(2_001, 4_001, 2))
    push = analyze_pushforward(starts, N0_LEAN, 8)
    return {
        "git_commit": git_commit(),
        "N0": N0_LEAN,
        "tilt": c,
        "onesided": {
            "fair_mu4": mu4_fair,
            "fair_mu3": mu3_fair,
            "fair_excess": onesided_excess(mu4_fair, mu3_fair, c),
            "fair_meets_cut": onesided_cut_holds(mu4_fair, mu3_fair, c),
            "all_oooo_meets_cut": onesided_cut_holds(1.0, 0.0, c),
            "location_free_unit_meets_cut": inequalities_meet_onesided_cut(
                1.0, 1.0, None, c
            ),
        },
        "oooo_relabel": oooo,
        "oe_multiplicity": oe,
        "pushforward": {
            "starts": len(starts),
            "lo": starts[0],
            "hi": starts[-1],
            "dmax": 8,
            "rows": push,
            "max_ratio4": max(row["ratio4"] for row in push) if push else 0.0,
            "any_onesided_cut": any(row["onesided_cut"] for row in push),
            "any_location_free_cut": any(row["location_free_meets_cut"] for row in push),
        },
        "classification": {
            "oooo_profile_is_relabel": bool(
                oooo["injective"]
                and oooo["all_oooo"]
                and abs(oooo["mass_ratio"] - oooo["x4"]) < 1e-12
                and abs(oooo["energy_before"] - oooo["energy_after"]) < 1e-12
            ),
            "concentration_saturates": True,
            "oe_span_unbounded": oe["span_strictly_increasing"],
            "oe_count_grows_on_separated_sample": oe["last_count_exceeds_first"],
            "support_local_capacity_dies": True,
            "location_free_bounds_miss_cut": True,
            "fair_coin_misses_onesided_cut": not onesided_cut_holds(
                mu4_fair, mu3_fair, c
            ),
            "location_is_good_base_or_L2": True,
            "decision": "CLOSE",
        },
    }


def main() -> None:
    result = summary()
    DATA_DIR.mkdir(parents=True, exist_ok=True)
    out = DATA_DIR / "summary.json"
    out.write_text(json.dumps(result, indent=2), encoding="utf-8")
    print(json.dumps(result, indent=2))
    print(out)


if __name__ == "__main__":
    main()
