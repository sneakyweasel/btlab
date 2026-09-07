"""Factor complexity of the odd-branch parity sequence.

``a(k) = floor((2k+1)^{3/2}) mod 2`` is the parity of the odd-step image of the odd start
``2k+1``: the second letter of its itinerary, hence the depth-one frontier parity over odd
starts.  If that sequence were *automatic* (finite-state in some numeration system) its
factor complexity ``p(L)``, the number of distinct length-``L`` windows, would be ``O(L)``
(Cobham; Allouche--Shallit 2003, Chapter 10), and questions about frontier parity words
would be decidable by the laboratory's automatic-sequence tooling (Walnut, Ostrowski
automata).  It is not automatic.

* **Measured** (``N = 3 000 000``): ``p(L) = 2^L`` exactly for ``L <= 6``, then ``126, 229,
  390, 618, 932, 1354, ...`` up to ``17453`` at ``L = 22``.  ``log p(L)/L`` falls from
  ``0.693`` to ``0.444`` while ``log p(L)/log L`` is ``3.16`` at ``L = 22``: polynomial-looking
  growth, far below ``2^L``, with the local exponent not yet settled.
* **Mechanism.**  On a window of length ``L`` the phase ``f(k+j) = (2k+2j+1)^{3/2}`` equals
  ``f(k) + j f'(k)`` plus a curvature term in ``[0, 1.5 L^2 / sqrt(2k+1)]``.  So for large
  ``k`` a window is the equal-interval coding of a rotation with slope ``f'(k) mod 2``, and
  ``(f(k), f'(k)) mod 2`` is jointly equidistributed (Weyl's criterion with Boshernitzan
  1994: ``a f + b f'`` is a Hardy function of polynomial growth, logarithmically far from
  every rational polynomial).  Hence **every** interior rotation word of every length occurs
  with positive lower density: ``p(L) >= R(L)``, the number of interior equal-interval
  rotation words, and ``R(L) >= sum_{r odd, 2r+2 <= L} (2r+1) ~ L^2/8`` through the periodic
  words ``(0^r 1^{r+1})``, which are pairwise distinct across odd ``r``.  Quadratic growth is
  enough: not automatic, not Sturmian, not the coding of any single rotation.
* **Checked.**  Every interior rotation word and every periodic-family word of length
  ``<= 22`` occurs among the first ``3 000 000`` terms.  ``R(L)`` is a vanishing fraction of
  ``p(L)`` (``356`` of ``1354`` at ``L = 12``); the excess is curvature words, contributed
  mostly by early positions.  The control ``floor(k sqrt 2) mod 2`` has ``p(L) = 2L``.
* **Lean.**  ``ParityComplexity.lean`` pins the finite part by kernel computation: the
  words of length ``3, 4, 5, 6`` are exhausted at exactly ``18, 48, 169, 574`` terms.

Negative knowledge: no finite-automaton or Ostrowski-automatic decision procedure can settle
frontier-parity questions for the Juggler map, at depth one already.
"""

from __future__ import annotations

import json
from fractions import Fraction
from math import isqrt, log, sqrt
from typing import Any

from research.juggler_sequence.lean_paths import DATA_ROOT

ARTIFACT = DATA_ROOT / "parity_complexity" / "summary.json"
DEFAULT_N = 1_000_000
MAX_L = 22
#: first index at which every binary word of length L has occurred (Lean, kernel-checked)
LEAN_SATURATION = {3: 18, 4: 48, 5: 169, 6: 574}
#: factor counts p(L), L = 1..22, among the first 3 000 000 terms (census run)
REFERENCE_3M = (2, 4, 8, 16, 32, 64, 126, 229, 390, 618, 932, 1354, 1885, 2586, 3469,
                4551, 5885, 7525, 9450, 11719, 14367, 17453)


def odd_cube_parity(n: int) -> list[int]:
    """``a(k) = floor((2k+1)^{3/2}) mod 2`` for ``k = 0 .. n-1``."""
    return [isqrt((2 * k + 1) ** 3) & 1 for k in range(n)]


def juggler_second_letter(m: int) -> int:
    """Parity of the odd-step image of the odd integer ``m``: the same letter, from the map."""
    if m % 2 == 0:
        raise ValueError("odd start expected")
    return isqrt(m ** 3) & 1


def beatty_parity(n: int) -> list[int]:
    """``floor(k sqrt 2) mod 2``, exact: the equal-interval coding of one rotation."""
    return [isqrt(2 * k * k) & 1 for k in range(n)]


def factor_set(seq: list[int], L: int, start: int = 0) -> set[tuple[int, ...]]:
    """Distinct windows of length ``L`` beginning at positions ``>= start``."""
    return {tuple(seq[i:i + L]) for i in range(start, len(seq) - L + 1)}


def factor_complexity(seq: list[int], L: int, start: int = 0) -> int:
    return len(factor_set(seq, L, start))


def saturation_index(seq: list[int], L: int) -> int | None:
    """Least ``n`` such that the first ``n`` letters contain every binary word of length ``L``."""
    seen: set[tuple[int, ...]] = set()
    for i in range(len(seq) - L + 1):
        seen.add(tuple(seq[i:i + L]))
        if len(seen) == 2 ** L:
            return i + L
    return None


def curvature_bound(k: int, L: int) -> float:
    """``1.5 L^2 / sqrt(2k+1)``: the quadratic Taylor remainder of ``(2k+2j+1)^{3/2}`` over a
    window, ``f'' = 3 (2k+1)^{-1/2}`` being positive and decreasing."""
    return 1.5 * L * L / sqrt(2 * k + 1)


def rotation_words(L: int) -> set[tuple[int, ...]]:
    """Interior equal-interval rotation words: codings ``j -> [ {y + j beta} >= 1/2 ]``.

    The word is constant on the open cells of the line arrangement ``y + j beta = m/2`` in
    the ``(y, beta)`` torus.  Two breakpoints ``m/2 - j beta`` coincide only at ``beta``
    rational with denominator ``<= 2(L-1)``, so the cyclic order of breakpoints, and with it
    the set of words, is constant on each open interval of the Farey sequence of order
    ``2L``.  Sampling ``beta`` at Farey midpoints and ``y`` between consecutive breakpoints
    therefore visits every open cell.  Exact rationals throughout.
    """
    order = 2 * L
    farey = sorted({Fraction(a, b) for b in range(1, order + 1) for a in range(b)})
    farey.append(Fraction(1))
    words: set[tuple[int, ...]] = set()
    for lo, hi in zip(farey, farey[1:]):
        beta = (lo + hi) / 2
        breaks = sorted({(Fraction(m, 2) - j * beta) % 1 for j in range(L) for m in (0, 1)})
        for i, b in enumerate(breaks):
            nxt = breaks[i + 1] if i + 1 < len(breaks) else breaks[0] + 1
            y = ((b + nxt) / 2) % 1
            words.add(tuple(int((y + j * beta) % 1 >= Fraction(1, 2)) for j in range(L)))
    return words


def periodic_family(L: int) -> set[tuple[int, ...]]:
    """Shifts of ``(0^r 1^{r+1})`` for odd ``r`` with ``2r+2 <= L``.

    Each is an interior rotation word (slope ``1/(2r+1)``, generic phase).  A window of
    length ``>= 2r+2`` contains a complete run, of length ``r`` or ``r+1``, which recovers
    ``r``; so words with different odd ``r`` are distinct, and the ``2r+1`` shifts of a
    primitive period are distinct.  Hence ``len == periodic_family_count(L)``.
    """
    words: set[tuple[int, ...]] = set()
    r = 1
    while 2 * r + 2 <= L:
        base = [0] * r + [1] * (r + 1)
        period = 2 * r + 1
        for s in range(period):
            words.add(tuple(base[(s + j) % period] for j in range(L)))
        r += 2
    return words


def periodic_family_count(L: int) -> int:
    """``sum (2r+1)`` over odd ``r`` with ``2r+2 <= L``; asymptotically ``L^2/8``."""
    return sum(2 * r + 1 for r in range(1, (L - 2) // 2 + 1, 2))


def growth_exponent(counts: dict[int, int], lo: int, hi: int) -> float:
    """Local log-log slope of ``L -> counts[L]`` between ``lo`` and ``hi``."""
    return log(counts[hi] / counts[lo]) / log(hi / lo)


def joint_phase_uniformity(n: int, bins: int = 10) -> dict[str, float]:
    """Least and greatest cell mass of ``(f(k), f'(k)) mod 2`` on a ``bins x bins`` grid,
    normalised so that uniform is ``1``."""
    counts = [[0] * bins for _ in range(bins)]
    for k in range(n):
        u = sqrt(2 * k + 1)
        y = (u ** 3) % 2.0
        b = (3 * u) % 2.0
        counts[int(y / 2 * bins)][int(b / 2 * bins)] += 1
    flat = [c for row in counts for c in row]
    scale = bins * bins / n
    return {"min": min(flat) * scale, "max": max(flat) * scale}


def summary(n: int = DEFAULT_N, max_L: int = MAX_L) -> dict[str, Any]:
    seq = odd_cube_parity(n)
    control = beatty_parity(n)
    table: list[dict[str, Any]] = []
    counts: dict[int, int] = {}
    for L in range(1, max_L + 1):
        fs = factor_set(seq, L)
        p = len(fs)
        counts[L] = p
        rot = rotation_words(L)
        fam = periodic_family(L)
        table.append({
            "L": L,
            "p": p,
            "full": 2 ** L,
            "saturated": p == 2 ** L,
            "log_p_over_L": log(p) / L,
            "rotation_words": len(rot),
            "rotation_words_missing": len(rot - fs),
            "periodic_family": len(fam),
            "periodic_family_missing": len(fam - fs),
            "periodic_family_count_formula": periodic_family_count(L),
            "control_p": factor_complexity(control, L),
        })
    sat = {L: saturation_index(seq, L) for L in range(1, 8)}
    rot_ok = [row["L"] for row in table if row["rotation_words_missing"] == 0]
    fam_ok = [row["L"] for row in table if row["periodic_family_missing"] == 0]
    unsat = [L for L in counts if counts[L] < 2 ** L]
    sens_L = min(12, max_L)
    return {
        "sequence": "a(k) = floor((2k+1)^{3/2}) mod 2, k = 0 .. N-1",
        "N": n,
        "max_L": max_L,
        "table": table,
        "saturation_index": sat,
        "lean_saturation": LEAN_SATURATION,
        "saturation_matches_lean": all(sat[L] == LEAN_SATURATION[L] for L in LEAN_SATURATION),
        "first_unsaturated_length": unsat[0] if unsat else None,
        "log_p_over_L_at_max_L": log(counts[max_L]) / max_L,
        "log_p_over_log_L_at_max_L": log(counts[max_L]) / log(max_L),
        "local_exponent_half_to_max": growth_exponent(counts, max_L // 2, max_L),
        "rotation_local_exponent_half_to_max": growth_exponent(
            {row["L"]: row["rotation_words"] for row in table}, max_L // 2, max_L),
        "reference_3M": list(REFERENCE_3M),
        "rotation_words_all_present_up_to": max(rot_ok) if rot_ok else 0,
        "periodic_family_all_present_up_to": max(fam_ok) if fam_ok else 0,
        "control_is_two_L": all(row["control_p"] == 2 * row["L"] for row in table),
        "prefix_sensitivity": {
            "L": sens_L,
            "from_start": counts[sens_L],
            "from_1000": factor_complexity(seq, sens_L, 1000) if n > 1000 else None,
            "from_100000": factor_complexity(seq, sens_L, 100_000) if n > 100_000 else None,
        },
        "joint_phase_uniformity": joint_phase_uniformity(min(n, 300_000)),
        "curvature_bound": {
            "k=1000,L=12": curvature_bound(1000, 12),
            "k=100000,L=12": curvature_bound(100_000, 12),
            "k=1000000,L=22": curvature_bound(1_000_000, 22),
        },
        "automatic_excluded": True,
        "verdict": (
            "p(L) >= R(L) >= L^2/8 - O(L) by Taylor + joint equidistribution "
            "(Boshernitzan 1994); automatic sequences have p(L) = O(L) (Cobham), so the "
            "depth-one frontier parity over odd starts is not automatic in any numeration. "
            "The finite part (exhaustion at 18, 48, 169, 574) is kernel-checked in Lean."
        ),
    }


def main() -> None:
    s = summary()
    ARTIFACT.parent.mkdir(parents=True, exist_ok=True)
    ARTIFACT.write_text(json.dumps(s, indent=2) + "\n", encoding="utf-8")
    print(f"N = {s['N']}; first unsaturated length {s['first_unsaturated_length']}; "
          f"exhaustion indices match Lean: {s['saturation_matches_lean']}")
    print(f"{'L':>3} {'p(L)':>7} {'2^L':>8} {'R(L)':>6} {'fam':>4} {'ctrl':>5} {'logp/L':>7}")
    for row in s["table"]:
        print(f"{row['L']:3} {row['p']:7} {row['full']:8} {row['rotation_words']:6} "
              f"{row['periodic_family']:4} {row['control_p']:5} {row['log_p_over_L']:7.4f}")
    print(f"log p / log L at L={s['max_L']}: {s['log_p_over_log_L_at_max_L']:.3f}; "
          f"local exponent {s['local_exponent_half_to_max']:.2f} "
          f"(rotation words alone {s['rotation_local_exponent_half_to_max']:.2f})")
    print(f"rotation words all present up to L = {s['rotation_words_all_present_up_to']}; "
          f"periodic family up to L = {s['periodic_family_all_present_up_to']}; "
          f"control is 2L: {s['control_is_two_L']}")
    ps = s["prefix_sensitivity"]
    print(f"p({ps['L']}) from start / from 1000 / from 100000: "
          f"{ps['from_start']} / {ps['from_1000']} / {ps['from_100000']}")
    u = s["joint_phase_uniformity"]
    print(f"joint phase (f, f') mod 2 on a 10x10 grid: min {u['min']:.3f}, max {u['max']:.3f}")
    print(f"wrote {ARTIFACT}")


if __name__ == "__main__":
    main()
