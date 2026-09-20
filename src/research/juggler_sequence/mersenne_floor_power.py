"""The floor power of a base-2 repunit is exact, and it is a binary pattern.

Two days of this session put the Juggler's arithmetic on the perfect-power locus, where the floor
is not charged at all. This probe does the opposite: it computes the floor charge exactly on a
family that is *never* a perfect power.

**LEMMA 8 IN BASE TWO.** `x = -1 mod 2^a` says the low `a` bits of `x` are all 1, so Hercher's
odd-run length `v_2(x+1)` is the number of TRAILING ONE-BITS of `x`, and the floor `x >= 2^a - 1`
is attained exactly when every bit is 1 -- at the base-2 repunits `M_a = 2^a - 1`. The landing
point is the base-3 repdigit: `M_a = (1^a)_2` maps in exactly `a` shortcut steps to
`3^a - 1 = (2^a)_3`, all ones in binary to all twos in ternary, and the continuation is
lifting-the-exponent, exactly `v_2(3^a - 1)` halvings, which is `1` for odd `a` and `2 + v_2(a)`
for even `a`. So the Mersenne word opens `O^a E^1` or `O^a E^(2 + v_2(a))`.

**THE PRIMALITY IS DECORATIVE, AND IT DOES NOT CROSS THE BRIDGE.** The floor is attained at
`2^a - 1` for every `a`, prime or not: `15 = 3*5`, `63 = 7*9`, `255`, `511 = 7*73` all have
`run = a`. What is structural is `u = x + 1 = 2^a`, the least value with `v_2(u) >= a`; "Mersenne"
is just `u - 1`, an artifact of that coordinate. Under the exponential bridge of
`J-lemma-eight-is-the-exponent-valuation` the extremal transports to the EXPONENT `e = 2^r` --
binary `1` followed by `r` zeros, one single one-bit, not a repunit. The all-ones pattern is
coordinate-dependent and does not survive the transport, so the Mersenne appearance carries no
prime content in either problem.

**THE NEW PART: THE JUGGLER FLOOR AT A REPUNIT IS CLOSED FORM.** For even `a >= 2`,

    floor((2^a - 1)^(3/2)) = 2^(3a/2) - 3 * 2^(a/2 - 1),   binary  1^(a-1) 0 1 0^(a/2 - 1),

so the floor charge against the top of the cell is exactly `3 * 2^(a/2 - 1)`. The proof is one
Taylor expansion: `(1 - x)^(3/2) = 1 - (3/2)x + (3/8)x^2 + ...` at `x = 2^(-a)` gives
`2^(3a/2) - 3*2^(a/2-1) + delta` with `delta = (3/8) 2^(-a/2) (1 + o(1))`, and for even `a` both
leading terms are integers while `delta` lies in `(0,1)`, so the floor is the stated integer.

For ODD `a` the leading term `2^(3a/2)` is irrational and the value becomes a Beatty value,

    floor((2^a - 1)^(3/2)) = floor(sqrt 2 * K),   K = 2^((3a-1)/2) - 3 * 2^((a-3)/2),

whose binary digits are binary digits of `sqrt 2`. That is the same 2-adic-to-Archimedean seam the
exponent bridge found at the end of an exact even tower, now appearing off the perfect-power locus.

**WHY THE FAMILY IS THE RIGHT CONTRAST.** By Catalan, proved by Mihailescu, `2^a - c^k = 1` has no
solution with `c, k >= 2`, so `M_a` is never a perfect power for `a >= 2` and `exactRun(M_a) = 0`:
Mersenne numbers are maximally INEXACT starts. The repository's only closed-form exact-image
theorems -- `floorPower_of_even_sq`, `floorPower_of_odd_sq`, the `pow_two_depth` family -- all live
on the perfect-power locus. This is the first exact floor-power value here that does not, which is
the point: the floor charge is not intrinsically unknowable away from perfect powers, only
unknowable generically.

No bound moves, no cycle is touched, `N_0` is unchanged, and the family has density zero.
"""

from __future__ import annotations

import json
from math import isqrt
from typing import Any

from research.juggler_sequence.lean_paths import DATA_ROOT, DOCS_RESEARCH

DATA_DIR = DATA_ROOT / "mersenne_floor_power"
JSON_PATH = DATA_DIR / "summary.json"
DOC_PATH = DOCS_RESEARCH / "juggler_mersenne_floor_power.md"

CLASS_MERSENNE = "REPUNIT_FLOOR_POWER_IS_CLOSED_FORM"

#: exponents tested for the closed forms
EVEN_RANGE = tuple(range(2, 402, 2))
ODD_RANGE = tuple(range(3, 201, 2))
#: exponents tested for the run law and the base-3 landing
RUN_RANGE = tuple(range(1, 120))
#: exponents whose binary pattern is checked letter by letter
BIT_RANGE = tuple(range(2, 42, 2))


def floor_power(n: int) -> int:
    """The Juggler step."""
    return isqrt(n) if n % 2 == 0 else isqrt(n * n * n)


def shortcut(x: int) -> int:
    """The Collatz shortcut map."""
    return x // 2 if x % 2 == 0 else (3 * x + 1) // 2


def v2(m: int) -> int:
    return (m & -m).bit_length() - 1


def mersenne(a: int) -> int:
    return 2**a - 1


def trailing_ones(x: int) -> int:
    bits = bin(x)[2:]
    return len(bits) - len(bits.rstrip("1"))


def base3(n: int) -> str:
    digits = []
    while n:
        digits.append(n % 3)
        n //= 3
    return "".join(str(d) for d in reversed(digits)) or "0"


def repunit_closed_form(a: int) -> int:
    """`2^(3a/2) - 3 * 2^(a/2 - 1)` for even `a`."""
    if a % 2:
        raise ValueError("even a only")
    return 2 ** (3 * a // 2) - 3 * 2 ** (a // 2 - 1)


def repunit_beatty_multiplier(a: int) -> int:
    """`K = 2^((3a-1)/2) - 3 * 2^((a-3)/2)` for odd `a >= 3`."""
    if a % 2 == 0 or a < 3:
        raise ValueError("odd a >= 3 only")
    return 2 ** ((3 * a - 1) // 2) - 3 * 2 ** ((a - 3) // 2)


def bit_pattern(a: int) -> str:
    """`1^(a-1) 0 1 0^(a/2 - 1)` for even `a`."""
    return "1" * (a - 1) + "0" + "1" + "0" * (a // 2 - 1)


def even_closed_form(exponents: tuple[int, ...] = EVEN_RANGE) -> dict[str, Any]:
    mismatches = [a for a in exponents if floor_power(mersenne(a)) != repunit_closed_form(a)]
    bit_fails = [a for a in BIT_RANGE if bin(floor_power(mersenne(a)))[2:] != bit_pattern(a)]
    return {
        "identity": "floor((2^a - 1)^(3/2)) = 2^(3a/2) - 3*2^(a/2 - 1), even a",
        "bits": "1^(a-1) 0 1 0^(a/2 - 1)",
        "max_exponent": exponents[-1],
        "tested": len(exponents),
        "mismatches": mismatches,
        "bit_mismatches": bit_fails,
        "holds": not mismatches and not bit_fails,
        "charge": "top of cell 2^(3a/2) minus the image is exactly 3*2^(a/2 - 1)",
    }


def odd_beatty_form(exponents: tuple[int, ...] = ODD_RANGE) -> dict[str, Any]:
    mismatches = []
    for a in exponents:
        k = repunit_beatty_multiplier(a)
        if floor_power(mersenne(a)) != isqrt(2 * k * k):
            mismatches.append(a)
    return {
        "identity": "floor((2^a - 1)^(3/2)) = floor(sqrt 2 * K), K = 2^((3a-1)/2) - 3*2^((a-3)/2), odd a",
        "max_exponent": exponents[-1],
        "tested": len(exponents),
        "mismatches": mismatches,
        "holds": not mismatches,
        "seam": "the digits are binary digits of sqrt 2 -- the same hand-over the exponent bridge "
        "found at the end of an exact even tower, here off the perfect-power locus",
    }


def base_two_run_law(exponents: tuple[int, ...] = RUN_RANGE, scan: int = 300_000) -> dict[str, Any]:
    """`run(x)` is the trailing-one count; the floor is attained exactly at the repunits."""
    run_fails = [x for x in range(1, scan, 2) if v2(x + 1) != trailing_ones(x)]
    attainers = [x for x in range(1, 4096) if v2(x + 1) == len(bin(x)[2:])]
    landing_fails = []
    for a in exponents:
        y = mersenne(a)
        for _ in range(a):
            y = shortcut(y)
        if y != 3**a - 1 or v2(mersenne(a) + 1) != a:
            landing_fails.append(a)
    lte_fails = [
        a for a in exponents
        if v2(3**a - 1) != (1 if a % 2 else 2 + v2(a))
    ]
    return {
        "run_is_trailing_ones": not run_fails,
        "scan": scan,
        "run_failures": run_fails[:8],
        "floor_attained_only_at_repunits": attainers,
        "landing": "M_a = (1^a)_2 maps in a steps to 3^a - 1 = (2^a)_3",
        "landing_failures": landing_fails,
        "landing_holds": not landing_fails,
        "continuation": "exactly v_2(3^a - 1) halvings follow: 1 for odd a, 2 + v_2(a) for even a",
        "continuation_failures": lte_fails,
        "continuation_holds": not lte_fails,
        "base3_landings": {str(a): base3(3**a - 1) for a in (2, 3, 4, 5, 6)},
    }


def primality_is_decorative(exponents: tuple[int, ...] = RUN_RANGE) -> dict[str, Any]:
    """The floor is attained for every `a`; and `M_a` is never a perfect power for `a >= 2`."""
    composite_a = [a for a in exponents if a > 1 and any(a % d == 0 for d in range(2, a))]
    attained_at_composite = all(v2(mersenne(a) + 1) == a for a in composite_a)
    perfect_power_hits = []
    for a in range(2, 200):
        m = mersenne(a)
        for k in range(2, m.bit_length() + 1):
            root = round(m ** (1.0 / k)) if m < 10**300 else 0
            for cand in (root - 1, root, root + 1):
                if cand > 1 and cand**k == m:
                    perfect_power_hits.append((a, k))
    return {
        "attained_at_composite_a": attained_at_composite,
        "composite_a_tested": len(composite_a),
        "mersenne_is_never_a_perfect_power": not perfect_power_hits,
        "perfect_power_hits": perfect_power_hits,
        "reason": "Catalan, proved by Mihailescu: 2^a - c^k = 1 has no solution with c,k >= 2",
        "consequence": "exactRun(M_a) = 0 for a >= 2: the repunits are maximally inexact starts",
        "bridge": "the extremal object is u = x+1 = 2^a; under the exponential bridge it transports "
        "to the exponent e = 2^r, one one-bit, not a repunit, so the all-ones pattern is "
        "coordinate-dependent and carries no prime content",
    }


def run_closed_form(exponents: tuple[int, ...] = RUN_RANGE) -> dict[str, Any]:
    """The WHOLE Mersenne run in closed form, not just its endpoints.

    `T(2^n - 1) = (3(2^n - 1) + 1)/2 = 3 * 2^(n-1) - 1`, and inductively
    `T^j(2^n - 1) = 3^j * 2^(n-j) - 1` for `0 <= j <= n`, which at `j = n` is the repdigit
    `3^n - 1`. In binary that is `3^j * 2^(n-j) - 1 = (3^j - 1) 2^(n-j) + (2^(n-j) - 1)`: the bits
    of `3^j - 1` followed by exactly `n - j` ones. So the trailing-one block shrinks by exactly one
    per step and its length is the number of steps REMAINING -- Lemma 8's countdown, visible.
    """
    value_fails, bit_fails, run_fails = [], [], []
    for n in exponents:
        x = mersenne(n)
        for j in range(n + 1):
            if x != 3**j * 2 ** (n - j) - 1:
                value_fails.append((n, j))
                break
            if n < 40:
                expect = (bin(3**j - 1)[2:] if j else "") + "1" * (n - j)
                if bin(x)[2:] != expect.lstrip("0"):
                    bit_fails.append((n, j))
                if v2(x + 1) != n - j:
                    run_fails.append((n, j))
            if j < n:
                x = shortcut(x)
    return {
        "identity": "T^j(2^n - 1) = 3^j * 2^(n-j) - 1 for 0 <= j <= n",
        "binary": "bits of 3^j - 1 followed by exactly n - j ones",
        "countdown": "the trailing-one block is the number of steps remaining, so Lemma 8's "
        "countdown is visible in base two at every step of the run, not only at its ends",
        "max_exponent": exponents[-1],
        "value_failures": value_fails,
        "bit_failures": bit_fails,
        "run_failures": run_fails,
        "holds": not value_fails and not bit_fails and not run_fails,
        "example_n_4": [bin(3**j * 2 ** (4 - j) - 1)[2:] for j in range(5)],
    }


def is_squarefree(m: int) -> bool:
    d = 2
    while d * d <= m:
        if m % (d * d) == 0:
            return False
        while m % d == 0:
            m //= d
        d += 1
    return True


def squarefree_is_stronger_than_needed(limit: int = 60) -> dict[str, Any]:
    """We need `not a perfect power`, which is a theorem; squarefreeness is open and also false.

    MathWorld records that all known `M_p` with `p` prime are squarefree while Guy (1994) believes
    some are not, so squarefreeness of Mersenne numbers is open. It is also strictly stronger than
    what `exactRun(M_a) = 0` needs: squarefree implies not a perfect power, and the converse fails.
    At composite indices squarefreeness already fails outright -- `M_6 = 63 = 3^2 * 7` -- while
    Catalan still gives `not a perfect power` for every `a >= 2`. So the Juggler statement rests on
    a theorem and not on an open conjecture, and it covers indices the conjecture does not reach.
    """
    not_squarefree = [a for a in range(1, limit) if not is_squarefree(mersenne(a))]
    return {
        "open_conjecture": "all known M_p with p prime are squarefree; Guy (1994) believes some "
        "are not -- so squarefreeness of Mersenne numbers is OPEN",
        "what_we_need": "not a perfect power, which Catalan (mihailescu-2004-catalan) gives "
        "unconditionally for every a >= 2",
        "implication_direction": "squarefree => not a perfect power; the converse is false",
        "squarefreeness_already_fails_at": not_squarefree[:12],
        "witness": {"a": 6, "M_a": 63, "factorisation": "3^2 * 7",
                    "squarefree": is_squarefree(63),
                    "perfect_power": False},
        "conclusion": "the squarefree route would fail at a = 6 and is open where it does not; "
        "Catalan covers every index, so the weaker property is the right tool",
    }


def numerology_kills() -> dict[str, Any]:
    """Two Mersenne coincidences that look like content and are not."""
    fermat = [1, 3]
    for _ in range(12):
        fermat.append(3 * fermat[-1] - 2 * fermat[-2])
    return {
        "fermat_polynomial_coefficients": {
            "observation": "the Mersenne numbers are a Fermat polynomial at x = 1 and satisfy "
            "F_n = 3 F_(n-1) - 2 F_(n-2), whose coefficients are 3 and 2 -- the same 3 and 2 as "
            "the Collatz odd step",
            "recurrence_reproduces_mersenne": fermat[:10] == [2**k - 1 for k in range(1, 11)],
            "verdict": "NUMEROLOGY. The characteristic polynomial is (t-1)(t-2) = t^2 - 3t + 2 "
            "because 2^n - 1 is a combination of 1^n and 2^n, so the 3 is the trace 1 + 2 and the "
            "2 is the determinant 1 * 2. Neither is the 3 of 3x + 1.",
        },
        "a020914_length": {
            "observation": "the run ends at 3^n - 1, whose binary length is floor(n log2 3) + 1 = "
            "A020914(n), the laboratory's distinguished word length",
            "verdict": "RESTATEMENT. A020914(n) is by definition the binary length of 3^n, so this "
            "says only that the endpoint is 3^n - 1. The Mersenne word length n + v_2(3^n - 1) is "
            "unrelated to A020914(n): at n = 3 it is 4 against 5, at n = 5 it is 6 against 8.",
        },
        "cunningham": {
            "observation": "M_n is the Cunningham number C^-(2,n), a one-base object",
            "consequence": "the cycle gap 3^o - 2^K is NOT a Cunningham number -- two bases and "
            "two independently moving exponents -- which is the precise reason classical "
            "primitive-divisor theory (Zsigmondy, Bang, Carmichael) does not reach it. A citable "
            "reason rather than a guess.",
        },
    }


def probe_payload() -> dict[str, Any]:
    even = even_closed_form()
    odd = odd_beatty_form()
    base2 = base_two_run_law()
    prime = primality_is_decorative()
    run = run_closed_form(exponents=tuple(range(1, 200)))
    squarefree = squarefree_is_stronger_than_needed()
    kills = numerology_kills()
    green = (
        even["holds"] and odd["holds"] and base2["run_is_trailing_ones"]
        and base2["landing_holds"] and base2["continuation_holds"]
        and prime["attained_at_composite_a"] and prime["mersenne_is_never_a_perfect_power"]
        and run["holds"] and kills["fermat_polynomial_coefficients"]["recurrence_reproduces_mersenne"]
    )
    return {
        "run_closed_form": run,
        "squarefree_versus_catalan": squarefree,
        "numerology": kills,
        "even_closed_form": even,
        "odd_beatty_form": odd,
        "base_two_run_law": base2,
        "primality": prime,
        "decision": {
            "classification": CLASS_MERSENNE if green else "REPUNIT_FLOOR_POWER_FAILED",
            "branch": "CLOSE",
            "green": green,
        },
        "anti_overclaim": (
            "One family of density zero. No bound moves, no cycle is touched, N_0 is unchanged, "
            "and nothing here is a halt theorem. The base-2 reading of Lemma 8 and the "
            "repunit-to-repdigit landing are elementary restatements of the congruence and are "
            "recorded as such; the closed forms are new to this repository, where every other "
            "exact floor-power value sits on the perfect-power locus. The Mersenne name carries "
            "primality, the mathematics does not: the bound is attained at 2^a - 1 for every a."
        ),
    }


def render_markdown(data: dict[str, Any]) -> str:
    even, odd = data["even_closed_form"], data["odd_beatty_form"]
    base2, prime = data["base_two_run_law"], data["primality"]
    lines = [
        "# The floor power of a base-2 repunit",
        "",
        f"Status: **{data['decision']['classification']}**",
        "",
        "Generated by `python -m research.juggler_sequence.mersenne_floor_power`.",
        "",
        "## Closed forms",
        "",
        f"- even `a`: `{even['identity']}`, bits `{even['bits']}` -- "
        f"checked to `a = {even['max_exponent']}`: `{even['holds']}`",
        f"- odd `a`: `{odd['identity']}` -- checked to `a = {odd['max_exponent']}`: `{odd['holds']}`",
        f"- {even['charge']}",
        f"- {odd['seam']}",
        "",
        "## The whole run, in closed form",
        "",
        f"- `{data['run_closed_form']['identity']}` -- checked to "
        f"`n = {data['run_closed_form']['max_exponent']}`: `{data['run_closed_form']['holds']}`",
        f"- in binary: {data['run_closed_form']['binary']}",
        f"- {data['run_closed_form']['countdown']}",
        f"- `n = 4`: `{data['run_closed_form']['example_n_4']}`",
        "",
        "## Squarefree is stronger than we need",
        "",
        f"- {data['squarefree_versus_catalan']['open_conjecture']}",
        f"- what we need: {data['squarefree_versus_catalan']['what_we_need']}",
        f"- squarefreeness already fails at "
        f"`{data['squarefree_versus_catalan']['squarefreeness_already_fails_at']}`",
        f"- {data['squarefree_versus_catalan']['conclusion']}",
        "",
        "## Two coincidences that are not content",
        "",
        f"- Fermat-polynomial coefficients: "
        f"{data['numerology']['fermat_polynomial_coefficients']['verdict']}",
        f"- A020914 length: {data['numerology']['a020914_length']['verdict']}",
        f"- Cunningham: {data['numerology']['cunningham']['consequence']}",
        "",
        "## Lemma 8 in base two",
        "",
        f"- `run(x)` is the trailing-one count of `x`, odd `x < {base2['scan']}`: "
        f"`{base2['run_is_trailing_ones']}`",
        f"- the floor is attained only at the repunits: `{base2['floor_attained_only_at_repunits']}`",
        f"- {base2['landing']} -- `{base2['landing_holds']}`",
        f"- {base2['continuation']} -- `{base2['continuation_holds']}`",
        "",
        "## The primality is decorative",
        "",
        f"- attained at composite `a` too: `{prime['attained_at_composite_a']}`",
        f"- `M_a` is never a perfect power for `a >= 2`: "
        f"`{prime['mersenne_is_never_a_perfect_power']}` ({prime['reason']})",
        f"- {prime['consequence']}",
        f"- {prime['bridge']}",
        "",
        "## What this does not say",
        "",
        data["anti_overclaim"],
        "",
    ]
    return "\n".join(lines)


def write_artifacts(payload: dict[str, Any] | None = None) -> dict[str, Any]:
    data = payload if payload is not None else probe_payload()
    DATA_DIR.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(data, indent=2) + "\n", encoding="utf-8")
    DOC_PATH.write_text(render_markdown(data), encoding="utf-8")
    return data


def main() -> None:
    data = write_artifacts()
    print(data["decision"]["classification"])
    print("even closed form:", data["even_closed_form"]["holds"])
    print("odd Beatty form:", data["odd_beatty_form"]["holds"])
    print("base-2 run law:", data["base_two_run_law"]["run_is_trailing_ones"],
          "| landing:", data["base_two_run_law"]["landing_holds"],
          "| LTE:", data["base_two_run_law"]["continuation_holds"])
    print("primality decorative:", data["primality"]["attained_at_composite_a"],
          "| never a perfect power:", data["primality"]["mersenne_is_never_a_perfect_power"])


if __name__ == "__main__":
    main()
