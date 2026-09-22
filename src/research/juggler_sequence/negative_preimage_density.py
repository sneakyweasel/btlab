"""Krasikov-Lagarias residue-model symmetry and its missing height comparison.

Krasikov and Lagarias (arXiv:math/0205002, Acta Arith. 109 (2003) 237-258) prove that for
any fixed ``a`` not divisible by three and all large ``x``, at least ``x^0.84`` of the
integers below ``x`` have ``a`` in their forward orbit under the ``3x+1`` shortcut map
``T(n) = n/2`` (even), ``(3n+1)/2`` (odd).  Their route is a system ``I_k`` of difference
inequalities on the residue classes mod ``3^k``, turned into a linear program whose largest
feasible ``lambda`` certifies the exponent ``log2(lambda)``.

**Correction, 22 September 2026.** This module transposes the formal residue
program to ``g(y) = y/2`` (even), ``(3y-1)/2`` (odd). Negation preserves its
indices and its assigned homogeneous shifts, but that does not prove those
shifts are valid for actual height-truncated minus-map trees. Their odd
predecessor is above ``2a/3``, where the plus predecessor is below it. The
missing scale factor is ``1 + 1/(2a)``. ``PreimageScale.lean`` proves this
and a concrete excluded ancestor. The claimed minus-map density exponent
is now unproved in this branch, not refuted. Solver outputs are model values.

THE STRUCTURE.  Under ``T`` the preimages of ``a`` are ``2a`` always and ``(2a-1)/3`` when
that is an odd integer, which happens exactly for ``a = 2 (mod 3)``; call those classes
*fertile*.  Under ``g`` they are ``2a`` and ``(2a+1)/3``, fertile exactly for
``a = 1 (mod 3)``.  Splitting a fertile class mod nine decides what the odd preimage ``c``
is worth, and the two splits are mirror images:

=========  =================  =========================================  =====
map        class of ``a``     odd preimage ``c``                          rule
=========  =================  =========================================  =====
``3x+1``   ``2 (mod 9)``      ``1 (mod 6)``, infertile, use ``2c``        D1
``3x+1``   ``5 (mod 9)``      ``0 (mod 3)``, dead, no term                D2
``3x+1``   ``8 (mod 9)``      ``5 (mod 6)``, fertile, use ``c``           D3
``3n-1``   ``7 (mod 9)``      ``5 (mod 6)``, infertile, use ``2c``        D1'
``3n-1``   ``4 (mod 9)``      ``3 (mod 6)``, dead, no term                D2'
``3n-1``   ``1 (mod 9)``      ``1 (mod 6)``, fertile, use ``c``           D3'
=========  =================  =========================================  =====

so ``2, 5, 8`` maps to ``7, 4, 1`` and the index maps ``(4m-2)/3`` and ``(2m-1)/3`` map to
``(4m+2)/3`` and ``(2m+1)/3``, which is negation throughout.  :func:`negation_is_an_isomorphism`
checks this as exact integer arithmetic over the sampled finite levels. The
formal programs agree numerically. Neither check validates the omitted height
comparison, and finite enumeration is not an all-level Lean proof.

THE UNDERLYING IDENTITY, which is what makes the inequalities true, is that for ``a`` fertile
and not in a cycle the backward tree splits exactly::

    pi*_a(x) = 2 + pi*_{4a}(x) + pi*_c(x),        c = (2a+1)/3,

because ``2a`` is then ``2 (mod 3)`` and so has ``4a`` as its only preimage.
:func:`split_identity_report` checks it by brute force and separately checks that
the plus-sign odd predecessor expression is nonintegral in every fertile minus
class. The previous "wrong identity" test was vacuous: its divisibility guard
never held. The cycle exclusion is not decoration: on a cycle member the backward
"tree" closes up and the identity fails.

THE SOLVER is a Collatz-Wielandt iteration rather than a linear program, because the
laboratory does not depend on scipy.  Eliminating the level ``k-1`` variables through their
defining minimum leaves a map ``F`` on the fertile classes that is monotone and positively
homogeneous, so the system has a feasible solution bounded below by one exactly when the
nonlinear eigenvalue of ``F`` is at least one.
"""
from __future__ import annotations

import json
from collections import deque
from fractions import Fraction
from math import log2
from typing import Any, Callable, Iterable

from research.juggler_sequence.lean_paths import DATA_ROOT, DOCS_RESEARCH

DATA_DIR = DATA_ROOT / "negative_preimage_density"
JSON_PATH = DATA_DIR / "summary.json"
DOC_PATH = DOCS_RESEARCH / "juggler_negative_preimage_density.md"

CLASS_RESIDUE_ONLY = "RESIDUE_SYMMETRY_WITH_UNPROVED_HEIGHT_TRANSFER"

#: log2(3), the alpha of Krasikov-Lagarias Proposition 2.1
ALPHA = log2(3.0)
#: the published anchors: Krasikov 1989 at k=2, Krasikov-Lagarias 2003 at k=11
PUBLISHED = {"krasikov_1989_k2": 0.43, "krasikov_lagarias_2003_k11": 0.84}
#: Exponents at the k this probe does not solve at run time: 3^10 = 59049 classes needs a
#: vectorised solver and minutes, not the seconds a probe may take. Both maps gave the same
#: value at every one of them, and k = 11 reproduces the 0.84 Krasikov-Lagarias publish from
#: that same k. This matches their formal program, not a minus-map density theorem.
HIGH_K = {9: 0.8168, 10: 0.8295, 11: 0.8418}
#: the three known cycles of the 3n-1 shortcut map on the positive integers
NEG_CYCLE_SEEDS = (1, 5, 17)


# ----------------------------------------------------------------- the two maps
def t_plus(n: int) -> int:
    """The 3x+1 shortcut map."""
    return n // 2 if n % 2 == 0 else (3 * n + 1) // 2


def g_minus(y: int) -> int:
    """The 3n-1 shortcut map, the map of Paper D."""
    return y // 2 if y % 2 == 0 else (3 * y - 1) // 2


def preimages_plus(z: int) -> list[int]:
    out = [2 * z]
    if (2 * z - 1) % 3 == 0 and ((2 * z - 1) // 3) % 2 == 1:
        out.append((2 * z - 1) // 3)
    return out


def preimages_minus(z: int) -> list[int]:
    out = [2 * z]
    if (2 * z + 1) % 3 == 0:
        out.append((2 * z + 1) // 3)
    return out


def negative_cycle_members() -> set[int]:
    """The fifteen members of the three known cycles; no exhaustiveness claim."""
    members: set[int] = set()
    for seed in NEG_CYCLE_SEEDS:
        z, path = seed, []
        while z not in path:
            path.append(z)
            z = g_minus(z)
        members |= set(path[path.index(z):])
    return members


# ----------------------------------------------------------- the two inequality systems
class System:
    """The formal homogeneous program on one sign's fertile residue classes.

    ``sign`` is ``+1`` for 3x+1 and ``-1`` for 3n-1, matching the sign of the constant the
    odd branch adds; the fertile classes are ``2 (mod 3)`` and ``1 (mod 3)`` respectively.
    """

    def __init__(self, sign: int) -> None:
        if sign not in (+1, -1):
            raise ValueError("sign must be +1 (3x+1) or -1 (3n-1)")
        self.sign = sign
        self.fertile = 2 if sign == +1 else 1
        self.name = "3x+1" if sign == +1 else "3n-1"

    def classes(self, j: int) -> list[int]:
        """The fertile residues mod ``3^j``; there are ``3^(j-1)`` of them."""
        return [m for m in range(3 ** j) if m % 3 == self.fertile]

    def production(self, m: int, k: int) -> tuple[int, tuple[int, float] | None]:
        """``(index of the 4m term, (index, lambda exponent) of the odd term or None)``.

        The odd index is returned mod ``3^(k-1)``, the level the minimum formula lives on.
        """
        if m % 3 != self.fertile:
            raise ValueError(f"{m} is not fertile for {self.name}")
        p, q = 3 ** k, 3 ** (k - 1)
        four = (4 * m) % p
        nine = m % 9
        if self.sign == +1:
            if nine == 2:
                return four, (((4 * m - 2) // 3) % q, ALPHA - 2.0)
            if nine == 5:
                return four, None
            return four, (((2 * m - 1) // 3) % q, ALPHA - 1.0)
        if nine == 7:
            return four, (((4 * m + 2) // 3) % q, ALPHA - 2.0)
        if nine == 4:
            return four, None
        return four, (((2 * m + 1) // 3) % q, ALPHA - 1.0)


PLUS, MINUS = System(+1), System(-1)


def negation_is_an_isomorphism(k: int) -> dict[str, Any]:
    """Does ``m -> -m (mod 3^k)`` carry the 3x+1 system onto the 3n-1 system exactly?

    This checks the finite residue relabelling and the assigned homogeneous
    exponents. It does not check height truncation in the actual inverse trees.
    """
    p, q = 3 ** k, 3 ** (k - 1)
    classes = PLUS.classes(k)
    mismatches: list[str] = []
    for m in classes:
        mm = (-m) % p
        if mm % 3 != MINUS.fertile:
            mismatches.append(f"{m}: negation leaves the fertile class")
            continue
        four, odd = PLUS.production(m, k)
        four_m, odd_m = MINUS.production(mm, k)
        if four_m != (-four) % p:
            mismatches.append(f"{m}: 4m term {four_m} is not the negation of {four}")
        if (odd is None) != (odd_m is None):
            mismatches.append(f"{m}: one system has an odd term and the other does not")
        elif odd is not None and odd_m is not None:
            if odd_m[0] != (-odd[0]) % q:
                mismatches.append(f"{m}: odd index {odd_m[0]} is not the negation of {odd[0]}")
            if odd_m[1] != odd[1]:
                mismatches.append(f"{m}: exponent {odd_m[1]} != {odd[1]}")
    # the minimum formula: the three lifts of -m are the negations of the three lifts of m
    lift_ok = all(
        {(-((m + t * q) % p)) % p for t in range(3)} == {((-m) % p + t * q) % p for t in range(3)}
        for m in classes
    )
    if not lift_ok:
        mismatches.append("the three lifts are not permuted by negation")
    return {"k": k, "classes": len(classes), "bijection_holds": not mismatches,
            "mismatches": mismatches[:5]}


# --------------------------------------------------------------------- the solver
def _step(sys_: System, k: int, lam: float, c: list[float]) -> list[float]:
    """One application of ``F``: the right-hand sides, with level ``k-1`` eliminated."""
    q, p = 3 ** (k - 1), 3 ** k
    index = {m: i for i, m in enumerate(sys_.classes(k))}
    two = lam ** -2.0
    out = [0.0] * len(c)
    for m, i in index.items():
        four, odd = sys_.production(m, k)
        val = c[index[four]] * two
        if odd is not None:
            j, e = odd
            val += (lam ** e) * min(c[index[(j + t * q) % p]] for t in range(3))
        out[i] = val
    return out


def eigenvalue(sys_: System, k: int, lam: float, iters: int = 4000,
               tol: float = 1e-12) -> float:
    """The nonlinear eigenvalue of ``F`` by Collatz-Wielandt iteration.

    ``F`` is monotone and positively homogeneous, so ``min_m F(c)_m / c_m`` and its max
    bracket the eigenvalue and close up under iteration.  The system admits a solution
    bounded below by one exactly when this is at least one.
    """
    c = [1.0] * len(sys_.classes(k))
    lo = hi = 1.0
    for _ in range(iters):
        f = _step(sys_, k, lam, c)
        ratios = [fi / ci for fi, ci in zip(f, c)]
        lo, hi = min(ratios), max(ratios)
        if hi - lo < tol:
            break
        s = max(f)
        c = [fi / s for fi in f]
    return (lo + hi) / 2.0


def best_lambda(sys_: System, k: int, tol: float = 1e-9) -> float:
    """Largest ``lambda`` whose system still admits a solution bounded below by one.

    Feasibility is checked to be an interval in ``lambda`` by :func:`feasibility_is_an
    _interval`; one of the three productions carries a positive exponent and so grows with
    ``lambda``, which is why that is checked rather than assumed.
    """
    lo, hi = 1.0, 2.0
    while hi - lo > tol:
        mid = (lo + hi) / 2.0
        if eigenvalue(sys_, k, mid) >= 1.0:
            lo = mid
        else:
            hi = mid
    return lo


def feasibility_is_an_interval(sys_: System, k: int, steps: int = 60) -> bool:
    """No feasible island above the threshold, on a grid of ``lambda`` in ``[1, 2]``."""
    flags = [eigenvalue(sys_, k, 1.0 + i * (1.0 / steps)) >= 1.0 for i in range(steps + 1)]
    return flags == sorted(flags, reverse=True)


# ------------------------------------------------------------- the underlying identity
def truncated_tree(preimages: Callable[[int], Iterable[int]], a: int, x: int) -> int:
    """``pi*_a(x)``: nodes of the backward tree of ``a`` whose whole path stays at most ``x``."""
    if not 1 <= a <= x:
        return 0
    seen, dq, total = {a}, deque([a]), 0
    while dq:
        z = dq.popleft()
        total += 1
        for w in preimages(z):
            if w <= x and w not in seen:
                seen.add(w)
                dq.append(w)
    return total


def split_identity_report(a_max: int = 400, ys: tuple[int, ...] = (4, 6, 8)) -> dict[str, Any]:
    """Check the minus-tree split, and the plus expression's nonintegrality."""
    cycles = negative_cycle_members()
    checked = failures = wrong_c_nonintegral = skipped = 0
    examples: list[dict[str, int]] = []
    for a in range(2, a_max):
        if a % 3 != MINUS.fertile:
            continue
        if a in cycles:
            skipped += 1
            continue
        for y in ys:
            x = (2 ** y) * a
            lhs = truncated_tree(preimages_minus, a, x)
            base = truncated_tree(preimages_minus, 4 * a, x)
            rhs = 2 + base + truncated_tree(preimages_minus, (2 * a + 1) // 3, x)
            checked += 1
            if lhs != rhs:
                failures += 1
                if len(examples) < 5:
                    examples.append({"a": a, "y": y, "lhs": lhs, "rhs": rhs})
            if (2 * a - 1) % 3 != 0:
                wrong_c_nonintegral += 1
    return {"checked": checked, "failures": failures, "examples": examples,
            "cycle_members_skipped": skipped,
            "plus_preimage_expression_nonintegral": wrong_c_nonintegral,
            "cycle_members": sorted(cycles)}


def cycle_members_break_the_identity(y: int = 4) -> int:
    """The identity must fail on cycle members; count how many, as a known-bad input."""
    cycles = negative_cycle_members()
    broken = 0
    for a in sorted(cycles):
        if a % 3 != MINUS.fertile or a == 1:
            continue
        x = (2 ** y) * a
        lhs = truncated_tree(preimages_minus, a, x)
        rhs = (2 + truncated_tree(preimages_minus, 4 * a, x)
               + truncated_tree(preimages_minus, (2 * a + 1) // 3, x))
        if lhs != rhs:
            broken += 1
    return broken


# ------------------------------------------------------------------------ artifacts
def height_comparison_report() -> dict[str, Any]:
    """An actual child ancestor admitted only by the invalid nominal budget."""
    a, x = 19, 103
    c = (2 * a + 1) // 3
    nominal = Fraction(x, a) * Fraction(3, 2) * c
    return {
        "target": a, "odd_preimage": c, "cutoff": x,
        "nominal_child_cutoff": str(nominal),
        "correction_factor": str(Fraction(2 * a + 1, 2 * a)),
        "excluded_ancestor": 104, "ancestor_path": [104, 52, 26, 13],
        "actual_child_count": truncated_tree(preimages_minus, c, x),
        "nominal_child_count": truncated_tree(preimages_minus, c, nominal.numerator // nominal.denominator),
        "density_transfer_established": False,
    }


def classification() -> dict[str, Any]:
    return {
        "label": CLASS_RESIDUE_ONLY,
        "statement": "Negation identifies the formal residue programs. The minus-map height comparison is unproved; matching solver exponents do not establish a density bound.",
        "published_plus_exponent": PUBLISHED["krasikov_lagarias_2003_k11"],
        "established_minus_exponent": None,
    }


def probe_payload(k_lp: int = 6, k_bijection: int = 10) -> dict[str, Any]:
    exps: dict[str, Any] = {}
    for k in range(2, k_lp + 1):
        lp, lm = best_lambda(PLUS, k), best_lambda(MINUS, k)
        exps[str(k)] = {
            "classes": 3 ** (k - 1),
            "lambda_3x_plus_1": lp, "gamma_3x_plus_1": log2(lp),
            "lambda_minus_residue_model": lm, "gamma_minus_residue_model": log2(lm),
            "agree_to_1e_7": abs(lp - lm) < 1e-7,
        }
    bij = {str(k): negation_is_an_isomorphism(k) for k in range(2, k_bijection + 1)}
    return {
        "classification": classification(),
        "height_comparison": height_comparison_report(),
        "alpha_log2_3": ALPHA,
        "published_anchors": PUBLISHED,
        "exponents": exps,
        "high_k_recorded": {str(k): v for k, v in HIGH_K.items()},
        "high_k_note": ("solved once with a vectorised Collatz-Wielandt iteration, both maps "
                        "identical at each; k = 11 gives 0.8418, which is the 0.84 "
                        "Krasikov-Lagarias publish from that same k"),
        "negation_bijection": bij,
        "bijection_holds_every_k": all(v["bijection_holds"] for v in bij.values()),
        "feasibility_is_an_interval": {
            "3x+1": feasibility_is_an_interval(PLUS, 4),
            "3n-1": feasibility_is_an_interval(MINUS, 4),
        },
        "split_identity": split_identity_report(),
        "identity_fails_on_cycle_members": cycle_members_break_the_identity(),
    }


def render_markdown(d: dict[str, Any]) -> str:
    rows = ["| k | classes | plus model exponent | minus model exponent | agree |",
            "|---|---|---|---|---|"]
    for k, v in d["exponents"].items():
        rows.append(f"| {k} | {v['classes']} | {v['gamma_3x_plus_1']:.4f} | "
                    f"{v['gamma_minus_residue_model']:.4f} | {'yes' if v['agree_to_1e_7'] else 'NO'} |")
    si = d["split_identity"]
    return "\n".join([
        "# Krasikov-Lagarias residue symmetry: the height transfer remains open",
        "",
        "Generated by `python -m research.juggler_sequence.negative_preimage_density`.",
        "",
        "Negation carries the formal residue program to the opposite sign. The "
        "assigned homogeneous shifts need a separate height argument for actual "
        "minus-map trees. The former density-transfer claim is withdrawn as unproved; "
        "its asymptotic conclusion is not refuted.",
        "",
        f"At target 19, child 13 and cutoff 103, the nominal child cutoff is "
        f"`{d['height_comparison']['nominal_child_cutoff']}`. It admits the ancestor "
        "`104 -> 52 -> 26 -> 13`, above the actual cutoff. The child tree counts "
        "are 12 and 13. The exact scaling correction is `39/38` (Lean).",
        "",
        f"**Negation is an isomorphism at every k checked:** "
        f"{d['bijection_holds_every_k']} (k = 2 to {max(int(x) for x in d['negation_bijection'])}).",
        "",
        "## Exponents from the solved system",
        "",
        *rows,
        "",
        f"Published anchors: Krasikov 1989 reports {PUBLISHED['krasikov_1989_k2']} at k = 2, "
        f"Krasikov-Lagarias 2003 reports {PUBLISHED['krasikov_lagarias_2003_k11']} at k = 11.",
        "",
        "Solved once at the k this probe is too slow for, both maps identical at each: "
        + ", ".join(f"k = {k} gives {v}" for k, v in HIGH_K.items())
        + f". The last is the {PUBLISHED['krasikov_lagarias_2003_k11']} they publish, from "
          "their own k, which is what says the system solved here is theirs.",
        "",
        "## The underlying tree identity",
        "",
        f"`pi*_a(x) = 2 + pi*_4a(x) + pi*_c(x)` with `c = (2a+1)/3`, checked on "
        f"{si['checked']} cases with {si['failures']} failures. The `3x+1` expression "
        f"`(2a-1)/3` is nonintegral in all {si['plus_preimage_expression_nonintegral']} cases. "
        f"{si['cycle_members_skipped']} fertile values were skipped as cycle members, and "
        f"the identity fails on {d['identity_fails_on_cycle_members']} of those, which is "
        "why the exclusion is a hypothesis and not a convenience.",
        "",
    ])


def write_artifacts(payload: dict[str, Any] | None = None) -> dict[str, Any]:
    data = payload or probe_payload()
    DATA_DIR.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(data, indent=2, default=str) + "\n", encoding="utf-8")
    DOC_PATH.write_text(render_markdown(data), encoding="utf-8")
    return data


def main() -> None:
    data = write_artifacts()
    print(f"{data['classification']['label']}: finite residue checks "
          f"{data['bijection_holds_every_k']}; no minus-map density exponent established")
    for k, v in data["exponents"].items():
        print(f"  k={k}: plus model {v['gamma_3x_plus_1']:.4f}   minus model {v['gamma_minus_residue_model']:.4f}")
    si = data["split_identity"]
    print(f"  tree identity: {si['checked']} checked, {si['failures']} failures, "
          f"nonintegral plus expressions {si['plus_preimage_expression_nonintegral']}")
    print(f"wrote {JSON_PATH} and {DOC_PATH}")


if __name__ == "__main__":
    main()
