"""Audit of the V_3 = OEOEOEE Section 12 constants.

Companion to docs/theory/juggler_oeoee_production.md Section 9 and 12.
One row per displayed estimate, recomputed from the OEOEE toolkit T1--T5
at the V_3 scales.  A script check confirms consistency of what is printed;
it is not a proof.

T1 (Vaaler) is Paper B Lemma 3.5 and is cited, not re-derived.
Lemma 6, Lemma 7 and Proposition 9 are already EXACT; this module audits
the four-case constants of Proposition 8 so that +1/81 at scale 27/128
is a theorem.

Not a halt theorem.  Run ``python -m research.juggler_sequence.v3_audit``.
"""

from __future__ import annotations

import json
import math
from fractions import Fraction as Fr
from math import isqrt
from pathlib import Path
from typing import Any

from research.juggler_sequence.cycle_finance import git_commit

REPO_ROOT = Path(__file__).resolve().parents[3]
DATA_DIR = REPO_ROOT / "data" / "research" / "juggler" / "v3_audit"
NOTE = REPO_ROOT / "docs" / "theory" / "juggler_oeoee_production.md"

CLASS_CONSISTENT = "V3_AUDIT_CONSISTENT"
CLASS_FALSIFIED = "V3_AUDIT_FALSIFIED"

# Printed Section 12 constants (the audit target).
PRINTED = {
    "y_coeff": Fr(64, 27),
    "l1_coeff": Fr(32, 9),
    "l2_coeff": Fr(8, 3),
    "case1_leading": Fr(256, 27),
    "case1_log": 9.06,
    "case1_R_coeff": 48.0,
    "case1_R": 0.222,
    "case1_assembled": 21.4,
    "case1_over_Y": 9.0,
    "case2_prefactor": 13.1,
    "case2_S": 0.320,
    "case2_assembled": 14.8,
    "case2_over_Y": 6.3,
    "case4_over_Y": 6.3,
    "assembly": 400.0,
}


def _row(
    name: str,
    printed: float,
    computed: float,
    ok: bool,
    kind: str,
    note: str = "",
) -> dict[str, Any]:
    return {
        "name": name,
        "printed": float(printed),
        "computed": float(computed),
        "abs_error": abs(float(printed) - float(computed)),
        "ok": bool(ok),
        "kind": kind,
        "note": note,
    }


def integer_root(base: int, k: int) -> int:
    """Largest r >= 0 with r^k <= base."""

    if base <= 0:
        return 0
    if base == 1:
        return 1
    lo, hi = 1, 1
    while hi**k <= base:
        hi *= 2
        if hi > base:
            hi = base
            break
    while lo + 1 < hi:
        mid = (lo + hi) // 2
        if mid**k <= base:
            lo = mid
        else:
            hi = mid
    return lo


def fiber_bounds(m_prime: int) -> tuple[int, int]:
    """Integer n-range of J(m') = [m'^{128/27}, (m'+1)^{128/27})."""

    lo_pow = m_prime**128
    lo = integer_root(lo_pow, 27)
    if lo**27 < lo_pow:
        lo += 1
    hi_pow = (m_prime + 1) ** 128
    hi = integer_root(hi_pow - 1, 27)
    return lo, hi


def J(n: int) -> int:
    return isqrt(n) if n % 2 == 0 else isqrt(n**3)


def word7(n: int) -> str:
    letters, x = [], n
    for _ in range(7):
        letters.append("O" if x % 2 else "E")
        x = J(x)
    return "".join(letters)


# ---------------------------------------------------------------------------
# 12.2 sizes
# ---------------------------------------------------------------------------


def sizes_Y() -> dict[str, Any]:
    """Y >= (64/27) m'^{101/27} - 1 by MVT on the odd count of J(m')."""

    ok = True
    for mp in (4, 6, 8, 12, 16):
        a, b = fiber_bounds(mp)
        Y = (b - (a | 1)) // 2 + 1
        bound = (64 / 27) * mp ** (101 / 27) - 1
        if Y < bound - 1.0:
            ok = False
    return _row(
        "12.2 Y lower bound 64/27 m'^{101/27}-1",
        float(PRINTED["y_coeff"]),
        64 / 27,
        ok,
        "script",
        "odd count of [m'^{128/27}, (m'+1)^{128/27}) against the MVT lower bound",
    )


def sizes_L1() -> dict[str, Any]:
    """L1 = (32/9) xi^{23/9} for xi in (m', m'+1): w1-range of the fiber."""

    # w1 in [m'^{32/9}, (m'+1)^{32/9}); real length (32/9) xi^{23/9}
    ok = True
    for mp in range(2, 80):
        real = (mp + 1) ** (32 / 9) - mp ** (32 / 9)
        lo = (32 / 9) * mp ** (23 / 9)
        hi = (32 / 9) * (mp + 1) ** (23 / 9)
        if real + 1e-9 < lo or real - 1e-9 > hi:
            ok = False
            break
    return _row(
        "12.2 L1 envelope 32/9 m'^{23/9}",
        float(PRINTED["l1_coeff"]),
        32 / 9,
        ok,
        "hand",
        "MVT on [m'^{32/9}, (m'+1)^{32/9})",
    )


def sizes_L2() -> dict[str, Any]:
    """L2 is the V_2 w-interval: (8/3) xi^{5/3} on [m'^{8/3}, (m'+1)^{8/3})."""

    ok = True
    for mp in range(2, 80):
        real = (mp + 1) ** (8 / 3) - mp ** (8 / 3)
        lo = (8 / 3) * mp ** (5 / 3)
        hi = (8 / 3) * (mp + 1) ** (5 / 3)
        if real + 1e-9 < lo or real - 1e-9 > hi:
            ok = False
            break
    return _row(
        "12.2 L2 envelope 8/3 m'^{5/3} (same as V_2 L)",
        float(PRINTED["l2_coeff"]),
        8 / 3,
        ok,
        "hand",
        "w2-fiber of V_3 is the w-fiber of V_2",
    )


def t4_step_ratio_v3(m_prime: int = 16) -> dict[str, Any]:
    """Case 1 steps of alpha_q(w1) = q w1^{-1/3} on K1 vary by (1+1/m')^{32/27}."""

    ratio = (1 + 1 / m_prime) ** (32 / 27)
    implied = 2.0 * (ratio + 1.0)
    # m' >= 16: ratio <= 1.08, implied <= 4.16; the Case 1 pad 48 vs 37.93 covers 4 -> 5
    ok = implied <= 5.0
    return _row(
        f"T4 Case 1 step ratio at m'={m_prime}",
        4.0,
        implied,
        ok,
        "hand",
        f"step ratio {ratio:.5f}; abstract T4 needs steps ~ d, pad covers 4->5",
    )


# ---------------------------------------------------------------------------
# Case 1: psi_1 present (Half B at the w1 layer)
# ---------------------------------------------------------------------------


def case1_leading() -> dict[str, Any]:
    """4 * (32q/9) * (2/3) = 256q/27."""

    derived = 4 * Fr(32, 9) * Fr(2, 3)
    printed = PRINTED["case1_leading"]
    return _row(
        "Case 1 leading 256/27",
        float(printed),
        float(derived),
        derived == printed,
        "hand",
        "4 V_q omega_smooth, V_q <= (32q/9)(m'+1)^{37/27}, omega ~ (2/3) m'^{32/27}",
    )


def case1_log_coeff() -> dict[str, Any]:
    """8/pi * 32/9 = 256/(9 pi) = 9.055..."""

    derived = 256.0 / (9.0 * math.pi)
    printed = PRINTED["case1_log"]
    return _row(
        "Case 1 log coefficient 9.06",
        printed,
        derived,
        derived <= printed + 0.01 and derived > 9.04,
        "hand",
        "8/(pi d_q) * V_q = (8/pi) m'^{32/27}/q * (32q/9) m'^{37/27}",
    )


def case1_vaaler_and_balance() -> list[dict[str, Any]]:
    """Both signs: 4*(256/27)=1024/27=37.93 <= 48; R = 0.222 m'^{16/27}."""

    both = 4 * float(Fr(256, 27))
    r_coeff = math.sqrt((64 / 27) / 48.0)
    assembled = 48.0 * r_coeff + (64 / 27) / r_coeff
    over_y = assembled / (64 / 27)
    return [
        _row(
            "Case 1 Vaaler R coefficient 48",
            PRINTED["case1_R_coeff"],
            both,
            both <= PRINTED["case1_R_coeff"],
            "hand",
            "sum_{0<|q|<=R} (2/|q|)*(256/27)|q| = (1024/27) R = 37.93 R; pad 48",
        ),
        _row(
            "Case 1 R = 0.222 m'^{16/27}",
            PRINTED["case1_R"],
            r_coeff,
            abs(r_coeff - PRINTED["case1_R"]) < 5e-3,
            "hand",
            "sqrt((64/27)/48) = 0.2222...",
        ),
        _row(
            "Case 1 assembled 21.4 m'^{85/27}",
            PRINTED["case1_assembled"],
            assembled,
            assembled <= PRINTED["case1_assembled"] + 0.05,
            "hand",
            "48 R + (64/27)/R at the printed R",
        ),
        _row(
            "Case 1 over Y is 9.0",
            PRINTED["case1_over_Y"],
            over_y,
            over_y <= PRINTED["case1_over_Y"] + 0.05,
            "hand",
            "21.34 / (64/27) = 9.00; saves m'^{-16/27} = P^{-1/8}",
        ),
    ]


# ---------------------------------------------------------------------------
# Case 2: Lambda_2 present, psi_1 absent (balanced |S_q| at the w1-in-w2 layer)
# ---------------------------------------------------------------------------


def case2_prefactor() -> dict[str, Any]:
    """2.26 * (1/2) * sqrt(8/3) * (2/3) * 2 * 2 * (8/3) = 13.12."""

    # T3 leading without omega: 2.26 * (lambda L) * lambda^{-1/2}
    #   = 2.26 * (s/2) * sqrt(8/(3s)) = 2.26*(1/2)*sqrt(8/3) sqrt(s)
    # times omega (2/3), Vaaler 2/s, harmonic 2 sqrt(S), times L2 = 8/3 m'^{5/3}
    t3 = 2.26 * 0.5 * math.sqrt(8 / 3)
    derived = t3 * (2 / 3) * 2 * 2 * (8 / 3)
    printed = PRINTED["case2_prefactor"]
    return _row(
        "Case 2 prefactor 13.1",
        printed,
        derived,
        abs(derived - printed) < 0.05,
        "hand",
        "T3 * omega * Vaaler 2/s * 2 sqrt(S) * L2; saves P^{-1/8} after balance",
    )


def case2_balance() -> list[dict[str, Any]]:
    """S = 0.320 m'^{16/27} balances 13.1 sqrt(S) m'^{77/27} against Y/S."""

    s_coeff = ((64 / 27) / 13.1) ** (2 / 3)
    main = 13.1 * math.sqrt(s_coeff)
    trunc = (64 / 27) / s_coeff
    assembled = main + trunc
    over_y = assembled / (64 / 27)
    return [
        _row(
            "Case 2 S = 0.320 m'^{16/27}",
            PRINTED["case2_S"],
            s_coeff,
            abs(s_coeff - PRINTED["case2_S"]) < 8e-3,
            "hand",
            "((64/27)/13.1)^{2/3} = 0.320...",
        ),
        _row(
            "Case 2 assembled 14.8 m'^{85/27}",
            PRINTED["case2_assembled"],
            assembled,
            assembled <= PRINTED["case2_assembled"] + 0.1,
            "hand",
            "13.1 sqrt(S) + (64/27)/S",
        ),
        _row(
            "Case 2 over Y is 6.3",
            PRINTED["case2_over_Y"],
            over_y,
            over_y <= PRINTED["case2_over_Y"] + 0.1,
            "hand",
            "saves m'^{-16/27} = P^{-1/8}, not binding",
        ),
    ]


# ---------------------------------------------------------------------------
# Case 4: only w2-factors (Half A verbatim, weight-rescaled)
# ---------------------------------------------------------------------------


def case4_half_a() -> dict[str, Any]:
    """Weight ratio (4/3) m'^{32/27} times V_2 Half A 11.2 m'^{19/9}."""

    # V_2 Half A error 11.2 m'^{19/9}; times (4/3) m'^{32/27} is 14.933 m'^{89/27}
    # over Y: 14.933 / (64/27) = 6.300
    error = 11.2 * (4 / 3)
    # this is the coefficient of m'^{89/27}; convert to over-Y at m'^{-4/9}
    over_y = error / (64 / 27)
    return _row(
        "Case 4 over Y is 6.3 (Half A transferred)",
        PRINTED["case4_over_Y"],
        over_y,
        abs(over_y - PRINTED["case4_over_Y"]) < 0.05,
        "hand",
        "w2-fiber is V_2's w-fiber; weight ratio (4/3) m'^{32/27}; binding P^{-3/32}",
    )


def binding_saving() -> dict[str, Any]:
    """Binding is Case 4: P^{-3/32} = m'^{-4/9}."""

    ok = Fr(128, 27) * Fr(3, 32) == Fr(4, 9)
    ok = ok and Fr(1, 6) * Fr(3, 4) ** 2 == Fr(3, 32)
    return _row(
        "binding saving P^{-3/32} = m'^{-4/9}",
        3 / 32,
        3 / 32,
        ok,
        "hand",
        "Section 11 law for k=3; a positive power",
    )


def bookkeeping() -> dict[str, Any]:
    net = (Fr(1, 3) - Fr(2, 9)) * Fr(1, 9)
    ok = net == Fr(1, 81)
    return _row(
        "Prop 9 net gain 1/81",
        float(Fr(1, 81)),
        float(net),
        ok,
        "hand",
        "(1/3 - 2/9) c_2 with c_2 = 1/9, at scale rho_3 = 27/128",
    )


def assembly() -> dict[str, Any]:
    """32 Case-1 + 16 Case-2 treated at the binding power, plus 8 Case-4."""

    # crudely put the P^{-1/8} cases at the binding power (worst-case)
    crude = 32 * PRINTED["case1_over_Y"] + 16 * PRINTED["case2_over_Y"] + 8 * PRINTED["case4_over_Y"]
    # at m' >= 16 the extra factor m'^{-4/27} <= 16^{-4/27} = 2^{-16/27} ~ 0.663
    # so 32*9.0*0.663 + 16*6.3*0.663 + 8*6.3 ~ 191 + 67 + 50 = 308 <= 400
    factor = 16 ** (-4 / 27)
    at_16 = (
        32 * PRINTED["case1_over_Y"] * factor
        + 16 * PRINTED["case2_over_Y"] * factor
        + 8 * PRINTED["case4_over_Y"]
    )
    printed = PRINTED["assembly"]
    ok = at_16 <= printed and crude > printed
    return _row(
        "12.5 assembly 400 for m' >= 16",
        printed,
        at_16,
        at_16 <= printed,
        "hand",
        f"crude all-at-binding {crude:.1f}; at m'>=16 with m'^{{-4/27}} factor {at_16:.1f} <= 400",
    )


# ---------------------------------------------------------------------------
# Envelope
# ---------------------------------------------------------------------------


def v3_count(m_prime: int) -> tuple[int, int]:
    """Exact (Y, |O|) on the V_3 fiber, odds only."""

    a, b = fiber_bounds(m_prime)
    Y = hits = 0
    n = a | 1
    if n < a:
        n += 2
    while n <= b:
        Y += 1
        if word7(n) == "OEOEOEE":
            hits += 1
        n += 2
    return Y, hits


def envelope_rows() -> list[dict[str, Any]]:
    rows = []
    for mp in (12, 16, 20):
        Y, hits = v3_count(mp)
        err = abs(64 * hits - Y)
        bound = 400.0 * Y * mp ** (-4 / 9) * (1 + math.log(mp)) ** 2
        denom = Y * mp ** (-4 / 9)
        ratio = err / denom if denom else 0.0
        rows.append(
            _row(
                f"envelope m'={mp}",
                400.0,
                ratio,
                err <= bound and ratio < 2.0,
                "script",
                f"Y={Y} 64|O|-Y={64 * hits - Y} ratio={ratio:.4f}",
            )
        )
    return rows


def root_if_promoted() -> dict[str, Any]:
    from research.juggler_sequence.fate_contagion import lambda_root

    rec = [
        (1.0, 0.5),
        (1 / 9, 3 / 8),
        (2 / 9, 0.75),
        (1 / 27, 9 / 32),
        (1 / 81, 27 / 128),
    ]
    lam = lambda_root(rec)
    return _row(
        "four-plus-V3 root 0.4891",
        0.4891,
        lam,
        abs(lam - 0.4891) < 5e-4,
        "script",
        "pairing + OEOEE + V_3; 1-lambda = 0.5109, least C still 19",
    )


def all_checks() -> list[dict[str, Any]]:
    return [
        sizes_Y(),
        sizes_L1(),
        sizes_L2(),
        t4_step_ratio_v3(16),
        t4_step_ratio_v3(60),
        case1_leading(),
        case1_log_coeff(),
        *case1_vaaler_and_balance(),
        case2_prefactor(),
        *case2_balance(),
        case4_half_a(),
        binding_saving(),
        bookkeeping(),
        assembly(),
        root_if_promoted(),
        *envelope_rows(),
    ]


def summary() -> dict[str, Any]:
    checks = all_checks()
    failures = [c for c in checks if not c["ok"]]
    return {
        "git_commit": git_commit(),
        "note": str(NOTE.relative_to(REPO_ROOT)).replace("\\", "/"),
        "checks": checks,
        "classification": {
            "name": CLASS_CONSISTENT if not failures else CLASS_FALSIFIED,
            "total_checks": len(checks),
            "failures": len(failures),
            "failing_names": [c["name"] for c in failures],
            "all_printed_constants_recompute": not failures,
            "power_saving": "P^{-3/32}",
            "net_gain": "1/81",
            "lambda_root_if_promoted": 0.4891,
            "required_rate_if_promoted": 0.5109,
            "least_C_if_promoted": 19,
        },
    }


def main() -> None:
    result = summary()
    DATA_DIR.mkdir(parents=True, exist_ok=True)
    out = DATA_DIR / "summary.json"
    out.write_text(json.dumps(result, indent=2), encoding="utf-8")
    print(json.dumps(result["classification"], indent=2))
    print(out)


if __name__ == "__main__":
    main()
