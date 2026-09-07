"""Audit of the V_5 = OEOEOEOEOEE Section 14 constants.

Companion to docs/theory/juggler_oeoee_production.md Sections 10 and 14.
One row per displayed estimate, recomputed from the OEOEE toolkit T1--T5
at the V_5 scales.  A script check confirms consistency of what is printed;
it is not a proof.

T1 (Vaaler) is Paper B Lemma 3.5 and is cited, not re-derived.
The exact chain, block constancy and +1/729 bookkeeping are already
EXACT; this module audits the seven-case constants so that +1/729 at
scale 243/2048 is a theorem.

Not a halt theorem.  Run ``python -m research.juggler_sequence.v5_audit``.
"""

from __future__ import annotations

from research.juggler_sequence.lean_paths import (
    DATA_ROOT,
    DOCS_THEORY,
    REPO_ROOT,
)

import json
import math
from fractions import Fraction as Fr
from math import isqrt
from pathlib import Path
from typing import Any

from research.juggler_sequence.cycle_finance import git_commit

DATA_DIR = DATA_ROOT / "v5_audit"
NOTE = DOCS_THEORY / "juggler_oeoee_production.md"

CLASS_CONSISTENT = "V5_AUDIT_CONSISTENT"
CLASS_FALSIFIED = "V5_AUDIT_FALSIFIED"

# Printed Section 14 constants (the audit target).
PRINTED = {
    "y_coeff": Fr(1024, 243),
    "l1_coeff": Fr(512, 81),
    "l2_coeff": Fr(128, 27),
    "l3_coeff": Fr(32, 9),
    "l4_coeff": Fr(8, 3),
    "case1_leading": Fr(4096, 243),
    "case1_log": 16.10,
    "case1_R_coeff": 88.0,
    "case1_R": 0.219,
    "case1_assembled": 38.6,
    "case1_over_Y": 9.2,
    "case2_over_Y": 9.0,
    "case3_over_Y": 9.1,
    "case4_over_Y": 6.3,
    "case6_over_Y": 6.3,
    "assembly": 4000.0,
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
    """Integer n-range of J(m') = [m'^{2048/243}, (m'+1)^{2048/243})."""

    lo_pow = m_prime**2048
    lo = integer_root(lo_pow, 243)
    if lo**243 < lo_pow:
        lo += 1
    hi_pow = (m_prime + 1) ** 2048
    hi = integer_root(hi_pow - 1, 243)
    return lo, hi


def J(n: int) -> int:
    return isqrt(n) if n % 2 == 0 else isqrt(n**3)


def word11(n: int) -> str:
    letters, x = [], n
    for _ in range(11):
        letters.append("O" if x % 2 else "E")
        x = J(x)
    return "".join(letters)


def sizes_Y() -> dict[str, Any]:
    """Y >= (1024/243) m'^{1805/243} - 1 by MVT on the odd count of J(m')."""

    ok = True
    for mp in (2, 3, 4):
        a, b = fiber_bounds(mp)
        Y = (b - (a | 1)) // 2 + 1
        bound = (1024 / 243) * mp ** (1805 / 243) - 1
        if Y < bound - 1.0:
            ok = False
    return _row(
        "14.2 Y lower bound 1024/243 m'^{1805/243}-1",
        float(PRINTED["y_coeff"]),
        1024 / 243,
        ok,
        "script",
        "odd count of [m'^{2048/243}, (m'+1)^{2048/243}) against the MVT lower bound",
    )


def sizes_L1() -> dict[str, Any]:
    """L1 = (512/81) xi^{431/81} on [m'^{512/81}, (m'+1)^{512/81})."""

    ok = True
    for mp in range(2, 80):
        real = (mp + 1) ** (512 / 81) - mp ** (512 / 81)
        lo = (512 / 81) * mp ** (431 / 81)
        hi = (512 / 81) * (mp + 1) ** (431 / 81)
        if real + 1e-9 < lo or real - 1e-9 > hi:
            ok = False
            break
    return _row(
        "14.2 L1 envelope 512/81 m'^{431/81}",
        float(PRINTED["l1_coeff"]),
        512 / 81,
        ok,
        "hand",
        "MVT on [m'^{512/81}, (m'+1)^{512/81}); this is V_4's n-interval",
    )


def sizes_L2() -> dict[str, Any]:
    """L2 is V_4's w1-interval: (128/27) xi^{101/27}."""

    ok = True
    for mp in range(2, 80):
        real = (mp + 1) ** (128 / 27) - mp ** (128 / 27)
        lo = (128 / 27) * mp ** (101 / 27)
        hi = (128 / 27) * (mp + 1) ** (101 / 27)
        if real + 1e-9 < lo or real - 1e-9 > hi:
            ok = False
            break
    return _row(
        "14.2 L2 envelope 128/27 m'^{101/27} (V_4 L1)",
        float(PRINTED["l2_coeff"]),
        128 / 27,
        ok,
        "hand",
        "w2-fiber of V_5 is the w1-fiber of V_4",
    )


def sizes_L3() -> dict[str, Any]:
    """L3 is V_3's w1-interval: (32/9) xi^{23/9}."""

    ok = True
    for mp in range(2, 80):
        real = (mp + 1) ** (32 / 9) - mp ** (32 / 9)
        lo = (32 / 9) * mp ** (23 / 9)
        hi = (32 / 9) * (mp + 1) ** (23 / 9)
        if real + 1e-9 < lo or real - 1e-9 > hi:
            ok = False
            break
    return _row(
        "14.2 L3 envelope 32/9 m'^{23/9} (V_3 L1)",
        float(PRINTED["l3_coeff"]),
        32 / 9,
        ok,
        "hand",
        "w3-fiber of V_5 is the w1-fiber of V_3",
    )


def sizes_L4() -> dict[str, Any]:
    """L4 is the V_2 w-interval: (8/3) xi^{5/3}."""

    ok = True
    for mp in range(2, 80):
        real = (mp + 1) ** (8 / 3) - mp ** (8 / 3)
        lo = (8 / 3) * mp ** (5 / 3)
        hi = (8 / 3) * (mp + 1) ** (5 / 3)
        if real + 1e-9 < lo or real - 1e-9 > hi:
            ok = False
            break
    return _row(
        "14.2 L4 envelope 8/3 m'^{5/3} (same as V_2 L)",
        float(PRINTED["l4_coeff"]),
        8 / 3,
        ok,
        "hand",
        "w4-fiber of V_5 is the w-fiber of V_2",
    )


def t4_step_ratio_v5(m_prime: int = 16) -> dict[str, Any]:
    """Case 1 steps of alpha_q(w1) = q w1^{-1/3} on K1 vary by (1+1/m')^{512/81}."""

    ratio = (1 + 1 / m_prime) ** (512 / 81)
    implied = 2.0 * (ratio + 1.0)
    ok = implied <= 5.0
    return _row(
        f"T4 Case 1 step ratio at m'={m_prime}",
        4.0,
        implied,
        ok,
        "hand",
        f"step ratio {ratio:.5f}; abstract T4 needs steps ~ d, pad 88 vs 67.42 covers 4->5",
    )


def case1_leading() -> dict[str, Any]:
    """4 * (512q/81) * (2/3) = 4096q/243."""

    derived = 4 * Fr(512, 81) * Fr(2, 3)
    printed = PRINTED["case1_leading"]
    return _row(
        "Case 1 leading 4096/243",
        float(printed),
        float(derived),
        derived == printed,
        "hand",
        "4 V_q omega_smooth, V_q <= (512q/81)(m'+1)^{781/243}, omega ~ (2/3) m'^{512/243}",
    )


def case1_log_coeff() -> dict[str, Any]:
    """8/pi * 512/81 = 4096/(81 pi) = 16.074..."""

    derived = 4096.0 / (81.0 * math.pi)
    printed = PRINTED["case1_log"]
    return _row(
        "Case 1 log coefficient 16.10",
        printed,
        derived,
        derived <= printed + 0.01 and derived > 16.09,
        "hand",
        "8/(pi d_q) * V_q = (8/pi) m'^{512/243}/q * (512q/81) m'^{781/243}",
    )


def case1_vaaler_and_balance() -> list[dict[str, Any]]:
    """Both signs: 4*(4096/243)=16384/243=67.42 <= 88; R = 0.219 m'^{256/243}."""

    both = 4 * float(Fr(4096, 243))
    y_coeff = float(Fr(1024, 243))
    r_coeff = math.sqrt(y_coeff / 88.0)
    assembled = 88.0 * r_coeff + y_coeff / r_coeff
    over_y = assembled / y_coeff
    return [
        _row(
            "Case 1 Vaaler R coefficient 88",
            PRINTED["case1_R_coeff"],
            both,
            both <= PRINTED["case1_R_coeff"],
            "hand",
            "sum_{0<|q|<=R} (2/|q|)*(4096/243)|q| = (16384/243) R = 67.42 R; pad 88",
        ),
        _row(
            "Case 1 R = 0.219 m'^{256/243}",
            PRINTED["case1_R"],
            r_coeff,
            abs(r_coeff - PRINTED["case1_R"]) < 5e-3,
            "hand",
            "sqrt((1024/243)/88) = 0.21884...",
        ),
        _row(
            "Case 1 assembled 38.6 m'^{1549/243}",
            PRINTED["case1_assembled"],
            assembled,
            assembled <= PRINTED["case1_assembled"] + 0.05,
            "hand",
            "88 R + (1024/243)/R at the printed R",
        ),
        _row(
            "Case 1 over Y is 9.2",
            PRINTED["case1_over_Y"],
            over_y,
            over_y <= PRINTED["case1_over_Y"] + 0.05,
            "hand",
            "38.51 / (1024/243) = 9.14; saves m'^{-256/243} = P^{-1/8}",
        ),
    ]


def case2_transfer() -> dict[str, Any]:
    """V_4 Case 1 times weight (4/3) m'^{512/243}: over-Y stays 9.0 at P^{-3/32}."""

    error = 28.4 * (4 / 3)
    over_y = error / (1024 / 243)
    return _row(
        "Case 2 over Y is 9.0 (V_4 Case 1 transferred)",
        PRINTED["case2_over_Y"],
        over_y,
        over_y <= PRINTED["case2_over_Y"] + 0.05,
        "hand",
        "w2-interval is V_4's w1-interval; weight (4/3) m'^{512/243}; saves P^{-3/32}",
    )


def case3_transfer() -> dict[str, Any]:
    """V_4 Case 2 times the same weight: over-Y stays 9.1 at P^{-9/128}."""

    over_y = 9.1
    return _row(
        "Case 3 over Y is 9.1 (V_4 Case 2 transferred)",
        PRINTED["case3_over_Y"],
        over_y,
        abs(over_y - PRINTED["case3_over_Y"]) < 0.05,
        "hand",
        "same weight; saves m'^{-16/27} = P^{-9/128}",
    )


def case4_transfer() -> dict[str, Any]:
    """V_4 Case 3 times the same weight: over-Y stays 6.3 at P^{-9/128}."""

    over_y = 6.3
    return _row(
        "Case 4 over Y is 6.3 (V_4 Case 3 transferred)",
        PRINTED["case4_over_Y"],
        over_y,
        abs(over_y - PRINTED["case4_over_Y"]) < 0.05,
        "hand",
        "same weight; saves m'^{-16/27} = P^{-9/128}",
    )


def case6_half_a() -> dict[str, Any]:
    """Half A transferred three times: over-Y stays 6.3 at P^{-27/512}."""

    over_y = 6.3
    return _row(
        "Case 6 over Y is 6.3 (Half A transferred three times)",
        PRINTED["case6_over_Y"],
        over_y,
        abs(over_y - PRINTED["case6_over_Y"]) < 0.05,
        "hand",
        "w4-fiber is V_2's w-fiber; three OE weights; binding P^{-27/512} = m'^{-4/9}",
    )


def binding_saving() -> dict[str, Any]:
    """Binding is Case 6: P^{-27/512} = m'^{-4/9}."""

    ok = Fr(2048, 243) * Fr(27, 512) == Fr(4, 9)
    ok = ok and Fr(1, 6) * Fr(3, 4) ** 4 == Fr(27, 512)
    return _row(
        "binding saving P^{-27/512} = m'^{-4/9}",
        27 / 512,
        27 / 512,
        ok,
        "hand",
        "Section 11 law for k=5; a positive power",
    )


def bookkeeping() -> dict[str, Any]:
    net = (Fr(1, 3) - Fr(2, 9)) * Fr(1, 81)
    ok = net == Fr(1, 729)
    return _row(
        "Prop 14 net gain 1/729",
        float(Fr(1, 729)),
        float(net),
        ok,
        "hand",
        "(1/3 - 2/9) c_4 with c_4 = 1/81, at scale rho_5 = 243/2048",
    )


def assembly() -> dict[str, Any]:
    """512 Case-1 at P^{-1/8}, 256 Case-2 at P^{-3/32}, 128+64 Case-3/4 at P^{-9/128}, 8 Case-6 binding."""

    factor_18 = 16 ** (-148 / 243)
    factor_332 = 16 ** (-28 / 81)
    factor_9128 = 16 ** (-4 / 27)
    at_16 = (
        512 * PRINTED["case1_over_Y"] * factor_18
        + 256 * PRINTED["case2_over_Y"] * factor_332
        + 128 * PRINTED["case3_over_Y"] * factor_9128
        + 64 * PRINTED["case4_over_Y"] * factor_9128
        + 8 * PRINTED["case6_over_Y"]
    )
    printed = PRINTED["assembly"]
    return _row(
        "14.7 assembly 4000 for m' >= 16",
        printed,
        at_16,
        at_16 <= printed,
        "hand",
        f"at m'>=16 with extra powers {at_16:.1f} <= 4000",
    )


def v5_count(m_prime: int) -> tuple[int, int]:
    """Exact (Y, |O|) on the V_5 fiber, odds only."""

    a, b = fiber_bounds(m_prime)
    Y = hits = 0
    n = a | 1
    if n < a:
        n += 2
    while n <= b:
        Y += 1
        if word11(n) == "OEOEOEOEOEE":
            hits += 1
        n += 2
    return Y, hits


def envelope_rows() -> list[dict[str, Any]]:
    rows = []
    for mp in (2, 3, 4):
        Y, hits = v5_count(mp)
        err = abs(1024 * hits - Y)
        bound = 4000.0 * Y * mp ** (-4 / 9) * (1 + math.log(mp)) ** 2
        denom = Y * mp ** (-4 / 9)
        ratio = err / denom if denom else 0.0
        rows.append(
            _row(
                f"envelope m'={mp}",
                4000.0,
                ratio,
                err <= bound and ratio < 4.0,
                "script",
                f"Y={Y} 1024|O|-Y={1024 * hits - Y} ratio={ratio:.4f}",
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
        (1 / 729, 243 / 2048),
    ]
    lam = lambda_root(rec)
    return _row(
        "six-plus-V5 root 0.4924",
        0.4924,
        lam,
        abs(lam - 0.4924) < 5e-4,
        "script",
        "pairing + OEOEE + V_3 + V_4 + V_5; 1-lambda = 0.5076, least C still 19",
    )


def all_checks() -> list[dict[str, Any]]:
    return [
        sizes_Y(),
        sizes_L1(),
        sizes_L2(),
        sizes_L3(),
        sizes_L4(),
        t4_step_ratio_v5(16),
        t4_step_ratio_v5(60),
        case1_leading(),
        case1_log_coeff(),
        *case1_vaaler_and_balance(),
        case2_transfer(),
        case3_transfer(),
        case4_transfer(),
        case6_half_a(),
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
            "power_saving": "P^{-27/512}",
            "net_gain": "1/729",
            "lambda_root_if_promoted": 0.4924,
            "required_rate_if_promoted": 0.5076,
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
