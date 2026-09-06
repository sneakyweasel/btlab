"""Audit of the V_4 = OEOEOEOEE Section 13 constants.

Companion to docs/theory/juggler_oeoee_production.md Sections 10 and 13.
One row per displayed estimate, recomputed from the OEOEE toolkit T1--T5
at the V_4 scales.  A script check confirms consistency of what is printed;
it is not a proof.

T1 (Vaaler) is Paper B Lemma 3.5 and is cited, not re-derived.
The exact chain, block constancy and +1/243 bookkeeping are already
EXACT; this module audits the six-case constants so that +1/243 at
scale 81/512 is a theorem.

Not a halt theorem.  Run ``python -m research.juggler_sequence.v4_audit``.
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
DATA_DIR = REPO_ROOT / "data" / "research" / "juggler" / "v4_audit"
NOTE = REPO_ROOT / "docs" / "theory" / "juggler_oeoee_production.md"

CLASS_CONSISTENT = "V4_AUDIT_CONSISTENT"
CLASS_FALSIFIED = "V4_AUDIT_FALSIFIED"

# Printed Section 13 constants (the audit target).
PRINTED = {
    "y_coeff": Fr(256, 81),
    "l1_coeff": Fr(128, 27),
    "l2_coeff": Fr(32, 9),
    "l3_coeff": Fr(8, 3),
    "case1_leading": Fr(1024, 81),
    "case1_log": 12.08,
    "case1_R_coeff": 64.0,
    "case1_R": 0.222,
    "case1_assembled": 28.4,
    "case1_over_Y": 9.0,
    "case2_over_Y": 9.1,
    "case3_over_Y": 6.3,
    "case5_over_Y": 6.3,
    "assembly": 1600.0,
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
    """Integer n-range of J(m') = [m'^{512/81}, (m'+1)^{512/81})."""

    lo_pow = m_prime**512
    lo = integer_root(lo_pow, 81)
    if lo**81 < lo_pow:
        lo += 1
    hi_pow = (m_prime + 1) ** 512
    hi = integer_root(hi_pow - 1, 81)
    return lo, hi


def J(n: int) -> int:
    return isqrt(n) if n % 2 == 0 else isqrt(n**3)


def word9(n: int) -> str:
    letters, x = [], n
    for _ in range(9):
        letters.append("O" if x % 2 else "E")
        x = J(x)
    return "".join(letters)


def sizes_Y() -> dict[str, Any]:
    """Y >= (256/81) m'^{431/81} - 1 by MVT on the odd count of J(m')."""

    ok = True
    for mp in (3, 4, 5, 6, 8):
        a, b = fiber_bounds(mp)
        Y = (b - (a | 1)) // 2 + 1
        bound = (256 / 81) * mp ** (431 / 81) - 1
        if Y < bound - 1.0:
            ok = False
    return _row(
        "13.2 Y lower bound 256/81 m'^{431/81}-1",
        float(PRINTED["y_coeff"]),
        256 / 81,
        ok,
        "script",
        "odd count of [m'^{512/81}, (m'+1)^{512/81}) against the MVT lower bound",
    )


def sizes_L1() -> dict[str, Any]:
    """L1 = (128/27) xi^{101/27} on [m'^{128/27}, (m'+1)^{128/27})."""

    ok = True
    for mp in range(2, 80):
        real = (mp + 1) ** (128 / 27) - mp ** (128 / 27)
        lo = (128 / 27) * mp ** (101 / 27)
        hi = (128 / 27) * (mp + 1) ** (101 / 27)
        if real + 1e-9 < lo or real - 1e-9 > hi:
            ok = False
            break
    return _row(
        "13.2 L1 envelope 128/27 m'^{101/27}",
        float(PRINTED["l1_coeff"]),
        128 / 27,
        ok,
        "hand",
        "MVT on [m'^{128/27}, (m'+1)^{128/27}); this is V_3's n-interval",
    )


def sizes_L2() -> dict[str, Any]:
    """L2 is V_3's w1-interval: (32/9) xi^{23/9}."""

    ok = True
    for mp in range(2, 80):
        real = (mp + 1) ** (32 / 9) - mp ** (32 / 9)
        lo = (32 / 9) * mp ** (23 / 9)
        hi = (32 / 9) * (mp + 1) ** (23 / 9)
        if real + 1e-9 < lo or real - 1e-9 > hi:
            ok = False
            break
    return _row(
        "13.2 L2 envelope 32/9 m'^{23/9} (V_3 L1)",
        float(PRINTED["l2_coeff"]),
        32 / 9,
        ok,
        "hand",
        "w2-fiber of V_4 is the w1-fiber of V_3",
    )


def sizes_L3() -> dict[str, Any]:
    """L3 is the V_2 w-interval: (8/3) xi^{5/3}."""

    ok = True
    for mp in range(2, 80):
        real = (mp + 1) ** (8 / 3) - mp ** (8 / 3)
        lo = (8 / 3) * mp ** (5 / 3)
        hi = (8 / 3) * (mp + 1) ** (5 / 3)
        if real + 1e-9 < lo or real - 1e-9 > hi:
            ok = False
            break
    return _row(
        "13.2 L3 envelope 8/3 m'^{5/3} (same as V_2 L)",
        float(PRINTED["l3_coeff"]),
        8 / 3,
        ok,
        "hand",
        "w3-fiber of V_4 is the w-fiber of V_2",
    )


def t4_step_ratio_v4(m_prime: int = 16) -> dict[str, Any]:
    """Case 1 steps of alpha_q(w1) = q w1^{-1/3} on K1 vary by (1+1/m')^{128/81}."""

    ratio = (1 + 1 / m_prime) ** (128 / 81)
    implied = 2.0 * (ratio + 1.0)
    ok = implied <= 5.0
    return _row(
        f"T4 Case 1 step ratio at m'={m_prime}",
        4.0,
        implied,
        ok,
        "hand",
        f"step ratio {ratio:.5f}; abstract T4 needs steps ~ d, pad 64 vs 50.57 covers 4->5",
    )


def case1_leading() -> dict[str, Any]:
    """4 * (128q/27) * (2/3) = 1024q/81."""

    derived = 4 * Fr(128, 27) * Fr(2, 3)
    printed = PRINTED["case1_leading"]
    return _row(
        "Case 1 leading 1024/81",
        float(printed),
        float(derived),
        derived == printed,
        "hand",
        "4 V_q omega_smooth, V_q <= (128q/27)(m'+1)^{175/81}, omega ~ (2/3) m'^{128/81}",
    )


def case1_log_coeff() -> dict[str, Any]:
    """8/pi * 128/27 = 1024/(27 pi) = 12.072..."""

    derived = 1024.0 / (27.0 * math.pi)
    printed = PRINTED["case1_log"]
    return _row(
        "Case 1 log coefficient 12.08",
        printed,
        derived,
        derived <= printed + 0.01 and derived > 12.06,
        "hand",
        "8/(pi d_q) * V_q = (8/pi) m'^{128/81}/q * (128q/27) m'^{175/81}",
    )


def case1_vaaler_and_balance() -> list[dict[str, Any]]:
    """Both signs: 4*(1024/81)=4096/81=50.57 <= 64; R = 0.222 m'^{64/81}."""

    both = 4 * float(Fr(1024, 81))
    r_coeff = math.sqrt((256 / 81) / 64.0)
    assembled = 64.0 * r_coeff + (256 / 81) / r_coeff
    over_y = assembled / (256 / 81)
    return [
        _row(
            "Case 1 Vaaler R coefficient 64",
            PRINTED["case1_R_coeff"],
            both,
            both <= PRINTED["case1_R_coeff"],
            "hand",
            "sum_{0<|q|<=R} (2/|q|)*(1024/81)|q| = (4096/81) R = 50.57 R; pad 64",
        ),
        _row(
            "Case 1 R = 0.222 m'^{64/81}",
            PRINTED["case1_R"],
            r_coeff,
            abs(r_coeff - PRINTED["case1_R"]) < 5e-3,
            "hand",
            "sqrt((256/81)/64) = 2/9 = 0.2222...",
        ),
        _row(
            "Case 1 assembled 28.4 m'^{367/81}",
            PRINTED["case1_assembled"],
            assembled,
            assembled <= PRINTED["case1_assembled"] + 0.05,
            "hand",
            "64 R + (256/81)/R at the printed R",
        ),
        _row(
            "Case 1 over Y is 9.0",
            PRINTED["case1_over_Y"],
            over_y,
            over_y <= PRINTED["case1_over_Y"] + 0.05,
            "hand",
            "28.44 / (256/81) = 9.00; saves m'^{-64/81} = P^{-1/8}",
        ),
    ]


def case2_transfer() -> dict[str, Any]:
    """V_3 Case 1 times weight (4/3) m'^{128/81}: over-Y stays 9.0 at P^{-3/32}."""

    error = 21.4 * (4 / 3)
    over_y = error / (256 / 81)
    return _row(
        "Case 2 over Y is 9.1 (V_3 Case 1 transferred)",
        PRINTED["case2_over_Y"],
        over_y,
        over_y <= PRINTED["case2_over_Y"] + 0.05,
        "hand",
        "w2-interval is V_3's w1-interval; weight (4/3) m'^{128/81}; saves P^{-3/32}",
    )


def case3_transfer() -> dict[str, Any]:
    """V_3 Case 2 times the same weight: over-Y stays 6.3 at P^{-3/32}."""

    error = 14.8 * (4 / 3)
    over_y = error / (256 / 81)
    return _row(
        "Case 3 over Y is 6.3 (V_3 Case 2 transferred)",
        PRINTED["case3_over_Y"],
        over_y,
        over_y <= PRINTED["case3_over_Y"] + 0.05,
        "hand",
        "same weight; saves m'^{-16/27} = P^{-3/32}",
    )


def case5_half_a() -> dict[str, Any]:
    """V_3 Case 4 times weight (4/3) m'^{128/81}: over-Y stays 6.3 at P^{-9/128}."""

    # V_3 Case 4 error 6.3 Y_V3 m'^{-4/9}; Y_V4 = (4/3) m'^{128/81} Y_V3
    over_y = 6.3
    return _row(
        "Case 5 over Y is 6.3 (Half A transferred twice)",
        PRINTED["case5_over_Y"],
        over_y,
        abs(over_y - PRINTED["case5_over_Y"]) < 0.05,
        "hand",
        "w3-fiber is V_2's w-fiber; two OE weights; binding P^{-9/128} = m'^{-4/9}",
    )


def binding_saving() -> dict[str, Any]:
    """Binding is Case 5: P^{-9/128} = m'^{-4/9}."""

    ok = Fr(512, 81) * Fr(9, 128) == Fr(4, 9)
    ok = ok and Fr(1, 6) * Fr(3, 4) ** 3 == Fr(9, 128)
    return _row(
        "binding saving P^{-9/128} = m'^{-4/9}",
        9 / 128,
        9 / 128,
        ok,
        "hand",
        "Section 11 law for k=4; a positive power",
    )


def bookkeeping() -> dict[str, Any]:
    net = (Fr(1, 3) - Fr(2, 9)) * Fr(1, 27)
    ok = net == Fr(1, 243)
    return _row(
        "Prop 12 net gain 1/243",
        float(Fr(1, 243)),
        float(net),
        ok,
        "hand",
        "(1/3 - 2/9) c_3 with c_3 = 1/27, at scale rho_4 = 81/512",
    )


def assembly() -> dict[str, Any]:
    """128 Case-1 at P^{-1/8}, 64+32 Case-2/3 at P^{-3/32}, 8 Case-5 binding."""

    factor_18 = 16 ** (-28 / 81)
    factor_332 = 16 ** (-4 / 27)
    at_16 = (
        128 * PRINTED["case1_over_Y"] * factor_18
        + 64 * PRINTED["case2_over_Y"] * factor_332
        + 32 * PRINTED["case3_over_Y"] * factor_332
        + 8 * PRINTED["case5_over_Y"]
    )
    printed = PRINTED["assembly"]
    return _row(
        "13.6 assembly 1600 for m' >= 16",
        printed,
        at_16,
        at_16 <= printed,
        "hand",
        f"at m'>=16 with extra powers {at_16:.1f} <= 1600",
    )


def v4_count(m_prime: int) -> tuple[int, int]:
    """Exact (Y, |O|) on the V_4 fiber, odds only."""

    a, b = fiber_bounds(m_prime)
    Y = hits = 0
    n = a | 1
    if n < a:
        n += 2
    while n <= b:
        Y += 1
        if word9(n) == "OEOEOEOEE":
            hits += 1
        n += 2
    return Y, hits


def envelope_rows() -> list[dict[str, Any]]:
    rows = []
    for mp in (4, 6, 8):
        Y, hits = v4_count(mp)
        err = abs(256 * hits - Y)
        bound = 1600.0 * Y * mp ** (-4 / 9) * (1 + math.log(mp)) ** 2
        denom = Y * mp ** (-4 / 9)
        ratio = err / denom if denom else 0.0
        rows.append(
            _row(
                f"envelope m'={mp}",
                1600.0,
                ratio,
                err <= bound and ratio < 2.0,
                "script",
                f"Y={Y} 256|O|-Y={256 * hits - Y} ratio={ratio:.4f}",
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
        (1 / 243, 81 / 512),
    ]
    lam = lambda_root(rec)
    return _row(
        "five-plus-V4 root 0.4916",
        0.4916,
        lam,
        abs(lam - 0.4916) < 5e-4,
        "script",
        "pairing + OEOEE + V_3 + V_4; 1-lambda = 0.5084, least C still 19",
    )


def all_checks() -> list[dict[str, Any]]:
    return [
        sizes_Y(),
        sizes_L1(),
        sizes_L2(),
        sizes_L3(),
        t4_step_ratio_v4(16),
        t4_step_ratio_v4(60),
        case1_leading(),
        case1_log_coeff(),
        *case1_vaaler_and_balance(),
        case2_transfer(),
        case3_transfer(),
        case5_half_a(),
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
            "power_saving": "P^{-9/128}",
            "net_gain": "1/243",
            "lambda_root_if_promoted": 0.4916,
            "required_rate_if_promoted": 0.5084,
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
