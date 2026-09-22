"""Exact bookkeeping and finite orbit checks for effective OOE modular returns.

The universal analytic proof is in the accompanying note. This program checks
its scalar arithmetic and finite construction, not the exponential-sum theorem.
"""
from __future__ import annotations

import json
from fractions import Fraction as Q
from math import isqrt, prod

from research.juggler_sequence.lean_paths import DATA_ROOT

OUTPUT = DATA_ROOT / "effective_modular_return" / "summary.json"


def _positive_modulus(modulus: int) -> None:
    if modulus < 1:
        raise ValueError("modulus must be positive")


def selected_parameter(modulus: int, t: int) -> bool:
    """The exact thresholded ReturnParameter(2,1,M,t) predicate."""
    _positive_modulus(modulus)
    if t < 0:
        raise ValueError("parameter must be nonnegative")
    s = 1 + 2 * modulus * t
    u = isqrt(s**9)
    v = isqrt(u)
    return s >= 16 and u % 2 == 0 and v % (2 * modulus) == 1


def actual_orbit(modulus: int, t: int) -> tuple[int, ...]:
    """Independent actual Juggler iteration, without prescribing its branches."""
    _positive_modulus(modulus)
    if t < 0:
        raise ValueError("parameter must be nonnegative")
    n = (1 + 2 * modulus * t) ** 2
    states = [n]
    for _ in range(3):
        n = isqrt(n**3 if n % 2 else n)
        states.append(n)
    return tuple(states)


def arithmetic_checks() -> dict[str, bool]:
    """Rational certificates for constants and exponents used in the note."""
    falling = lambda p, k: prod(p - j for j in range(k))
    checks = {
        "high_fifth_derivative": falling(Q(9, 2), 5) == Q(945, 32),
        "low_fifth_derivative": falling(Q(9, 4), 5) == Q(945, 1024),
        "low_third_derivative": falling(Q(9, 4), 3) == Q(45, 64),
        "relative_fifth_coefficient": falling(Q(9, 4), 5) / falling(Q(9, 2), 5) == Q(1, 32),
        "high_lower_endpoint": 945**2 > 400**2 * 5,
        "high_upper_endpoint": 2835**2 < 2400**2 * 2,
        "low_lower_endpoint": Q(45, 8)**4 > 5**3,
        "low_upper_endpoint": Q(45, 32)**4 < 2**3,
        "high_fourier_constants": 6 < 2**16 and 3600 < 2**30 and 22 < 32,
        "low_fourier_constants": 4 <= 2**4 and 8 <= 2**6 and 2 <= 2**4,
        "low_to_common_exponents": Q(1, 6) - Q(1, 30) == Q(2, 15)
            and Q(1, 15) - Q(1, 8) == -Q(7, 120) <= -Q(1, 60),
        "modulus_enlargement": Q(3, 20) <= Q(1, 4) and Q(5, 24) <= Q(1, 4),
        "dyadic_ratio": Q(59, 60) > Q(3, 4) and 2**3 > Q(3, 2)**4,
        "initial_segment_constant": 2 * 32 + 16 <= 128,
        "smoothing_balance": Q(1, 32) / 2 == Q(1, 64)
            and Q(1, 60) - Q(1, 32) / 30 == Q(1, 64),
        "logarithm_critical_point": Q(2, 48 + 208) == Q(1, 128),
        "logarithm_maximum": 1 + Q(13, 8) + Q(13, 8)**2 / 2
            + Q(13, 8)**3 / 6 > 4 and (3 + Q(208, 16))**2 / 4 == 64,
        "counting_constant": 5 + 128 * 64 + 8 < 2**14,
        "counting_exponent": Q(63, 64) + Q(1, 128) == Q(127, 128),
        "witness_parameter_exponents": 2176 == 128 * (14 + 3)
            and Q(160, 128) == 1 + Q(1, 4),
        "witness_main_term_margin": Q(2**14, 2**17) == Q(1, 8) < Q(1, 4),
        "witness_start_exponents": 4354 == 2 * 2176 + 2 and 322 == 2 * 160 + 2,
    }
    return checks


def witness_bounds(modulus: int) -> tuple[int, int]:
    """The written theorem's strict bounds on t and n; no search is run."""
    _positive_modulus(modulus)
    return (2**2176 * modulus**160, 2**4354 * modulus**322)


def finite_summary(moduli: tuple[int, ...] = (1, 2, 3, 4, 8, 16, 31, 64),
                   cutoff: int = 4096) -> dict:
    if cutoff < 1:
        raise ValueError("cutoff must be positive")
    checks = arithmetic_checks()
    if not all(checks.values()):
        raise AssertionError({name: ok for name, ok in checks.items() if not ok})
    rows = []
    for modulus in moduli:
        _positive_modulus(modulus)
        hits = []
        for t in range(cutoff):
            selected = selected_parameter(modulus, t)
            states = actual_orbit(modulus, t)
            actual = (1 + 2 * modulus * t >= 16
                      and tuple(n % 2 for n in states[:3]) == (1, 1, 0)
                      and min(states) == states[0] and states[-1] > states[0]
                      and states[0] % (2 * modulus) == states[-1] % (2 * modulus) == 1)
            if selected != actual:
                raise AssertionError((modulus, t, states, selected, actual))
            if selected:
                hits.append(t)
        rows.append({"M": modulus, "T": cutoff, "count": len(hits),
                     "main_term": str(Q(cutoff, 4 * modulus)),
                     "first_t": hits[0] if hits else None,
                     "first_orbit": list(actual_orbit(modulus, hits[0])) if hits else None})
    return {"schema": 1, "claim": "J-effective-ooe-modular-return",
            "scope": "Exact scalar bookkeeping and finite actual-orbit checks; not an analytic proof",
            "arithmetic_checks": checks, "samples": rows,
            "error_bound": "2^14 * M^(1/4) * T^(127/128)",
            "strict_first_parameter_bound": "2^2176 * M^160",
            "strict_first_start_bound": "2^4354 * M^322",
            "analytic_status": "Written proof using Arias de Reyna Theorem 11; not Lean formalized",
            "finite_error_comparison": "Bound is vacuous at these sample sizes; no experimental rate claim"}


def main() -> None:
    report = finite_summary()
    OUTPUT.parent.mkdir(parents=True, exist_ok=True)
    OUTPUT.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(f"{len(report['arithmetic_checks'])} exact arithmetic checks; "
          f"{sum(r['T'] for r in report['samples'])} actual prefixes checked")
    print(OUTPUT)


if __name__ == "__main__":
    main()
