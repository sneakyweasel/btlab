"""Knight's cancellation transports to the Juggler and its residual is the state dependence.

`J-knight-is-sign-free-and-catalan-bounds-the-escapes` showed Knight's high-cycle contradiction is
sign-free, so it reaches the expanding side where the Juggler's cycle words live. The obvious next
question is whether it reaches the Juggler's own realizations. This probe answers it: the identity
transports exactly, and the cancellation fails for one identifiable reason.

**KNIGHT'S THREE PARTS.** (i) Two members of ONE cycle, `f(v_h)` and `f(v_h^R)`, because Cohn makes
the reverse of an aperiodic upper Christoffel word a rotation of it. (ii) An ADDITIVE cocycle: the
Bohm-Sontacchi charge `g` is a function of the WORD alone, so the split `v_h = 1u0`,
`v_h^R = 0u1` gives `g(v_h) = 2g(u) + 3^(x-1)` and `g(v_h^R) = 6g(u) + 2^(k-1)`, and the integer
combination `3f(v_h) - f(v_h^R) + 1` cancels the shared `g(u)`. (iii) The leftover
`2^(k-1)/(2^k - 3^x)` is not an integer because the gap is odd.

**THE MULTIPLICATIVE ANALOGUE, AND IT IS EXACT.** The Juggler has (i) for free -- Cohn is a fact
about words, so `v_h` and `v_h^R` are the same cycle read at two points -- and it has a cocycle, but
a multiplicative one, kernel-checked as `J-normalized-relative-slack`:
`1 + q_(uv) = (1+q_u)^(3^(#O(v))) (1+q_v)^(2^|u|)`, the first factor read at the start and the second
at the state after `u`. Expanding `w = O u E` from `n` and `w' = E u O` from `n'`, with `m = |u|` and
`p = #O(u)`:

    1 + q_w  = (1+q_O @ n )^(3^p)     (1+q_u @ J(n) )^2 (1+q_E @ t )^(2^(m+1))
    1 + q_w' = (1+q_E @ n')^(3^(p+1)) (1+q_u @ J(n'))^6 (1+q_O @ t')^(2^(m+1))

so the multiplicative analogue of `3f - f^R` is cube-and-divide, which cancels the shared middle
exponent exactly as Knight's does, `3*2 - 6 = 0`:

    (1+q_w)^3 / (1+q_w') = [endpoint terms] * ( (1+q_u @ J(n)) / (1+q_u @ J(n')) )^6.

**AND THAT RESIDUAL IS THE WHOLE STORY.** For Collatz the corresponding residual is identically 1,
because `g(u)` is word-determined and is literally the same integer in both expressions. For the
Juggler the middle word is read at `J(n)` along one rotation and at `J(n')` along the other, and
`1 + q` is a function of the word AND the state, so the two are different numbers. Verified: the
residual identity holds exactly on every realized `(OuE, EuO)` pair at length 6 found in `[2, 3e5)`,
and the two middle slacks coincide in none of them.

So Knight's method transports formally and dies at exactly the wall
`J-juggler-is-collatz-one-exponential-up` names: Collatz's word data is arithmetic and free (Terras),
the Juggler's is state-dependent and open (Hypothesis FD). The same dichotomy, met in a new place.

**WHAT IT LEAVES, SCOPED HONESTLY.** On a return the slack is `1 + q = n^(3^o - 2^L)`, so the
left-hand side becomes `(n^3/n')^G` with `G` the gap: a perfect `G`-th power. Hence a Juggler cycle
whose word is the Christoffel word AND whose two reverse-conjugate readings have equal middle slack
would force an explicit product of endpoint slacks to be a perfect `G`-th power, which is the
Catalan-flavoured obstruction Knight's parity step becomes under the exponential. Without that
equality there is no exclusion, and nothing here excludes any Juggler cycle. No floor moves.
"""

from __future__ import annotations

import json
from fractions import Fraction
from math import isqrt
from typing import Any

from research.juggler_sequence.lean_paths import DATA_ROOT, DOCS_RESEARCH

DATA_DIR = DATA_ROOT / "multiplicative_knight"
JSON_PATH = DATA_DIR / "summary.json"
DOC_PATH = DOCS_RESEARCH / "juggler_multiplicative_knight.md"

CLASS_RESIDUAL = "MULTIPLICATIVE_KNIGHT_RESIDUAL_IS_THE_STATE_DEPENDENCE"

#: word length whose (OuE, EuO) pairs are enumerated
PAIR_LENGTH = 6
#: search bound for the least start realizing each word
INDEX_BOUND = 300_000


def floor_power(n: int) -> int:
    return isqrt(n) if n % 2 == 0 else isqrt(n * n * n)


def word_of(n: int, length: int) -> str:
    letters = []
    for _ in range(length):
        letters.append("E" if n % 2 == 0 else "O")
        n = floor_power(n)
    return "".join(letters)


def slack(n: int, word: str) -> tuple[Fraction | None, int | None]:
    """`1 + q = n^(3^#O) / T_w(n)^(2^|w|)`, exact, or `None` if `w` is not realized at `n`."""
    odds, length, state = word.count("O"), len(word), n
    for letter in word:
        if (letter == "O") != (state % 2 == 1):
            return None, None
        state = floor_power(state)
    return Fraction(n ** (3**odds), state ** (2**length)), state


def word_index(length: int = PAIR_LENGTH, bound: int = INDEX_BOUND) -> dict[str, int]:
    """Least start realizing each word of the given length."""
    first: dict[str, int] = {}
    for n in range(2, bound):
        w = word_of(n, length)
        first.setdefault(w, n)
    return first


def concatenation_law(limit: int = 400, depth: int = 6) -> dict[str, Any]:
    """`1+q_uv = (1+q_u)^(3^#O(v)) (1+q_v)^(2^|u|)` -- the kernel-checked law, re-run."""
    fails = []
    checked = 0
    for n in range(2, limit):
        for k in range(1, depth + 1):
            w = word_of(n, k)
            total, _ = slack(n, w)
            if total is None:
                continue
            for split in range(1, k):
                u, v = w[:split], w[split:]
                qu, mid = slack(n, u)
                if qu is None:
                    continue
                qv, _ = slack(mid, v)
                if qv is None:
                    continue
                checked += 1
                if total != qu ** (3 ** v.count("O")) * qv ** (2 ** len(u)):
                    fails.append((n, w, split))
    return {"law": "1+q_uv = (1+q_u)^(3^#O(v)) (1+q_v)^(2^|u|)",
            "splits_checked": checked, "failures": fails[:6], "holds": not fails}


def residual(length: int = PAIR_LENGTH, bound: int = INDEX_BOUND) -> dict[str, Any]:
    """The cancellation residual is exactly the sixth power of the middle-slack ratio."""
    first = word_index(length, bound)
    fails, rows = [], []
    equal_middles = 0
    tested = 0
    for w, n in sorted(first.items()):
        if w[0] != "O" or w[-1] != "E":
            continue
        u = w[1:-1]
        m, p = len(u), u.count("O")
        mirror = "E" + u + "O"
        n2 = first.get(mirror)
        if n2 is None:
            continue
        q_w, _ = slack(n, w)
        q_m, _ = slack(n2, mirror)
        q_o_n, _ = slack(n, "O")
        q_u_n, _ = slack(floor_power(n), u)
        state = floor_power(n)
        for _ in u:
            state = floor_power(state)
        q_e_t, _ = slack(state, "E")
        q_e_n2, _ = slack(n2, "E")
        q_u_n2, _ = slack(floor_power(n2), u)
        state2 = floor_power(n2)
        for _ in u:
            state2 = floor_power(state2)
        q_o_t2, _ = slack(state2, "O")
        if None in (q_w, q_m, q_o_n, q_u_n, q_e_t, q_e_n2, q_u_n2, q_o_t2):
            continue
        endpoints = (q_o_n ** (3 ** (p + 1)) * q_e_t ** (3 * 2 ** (m + 1))) / (
            q_e_n2 ** (3 ** (p + 1)) * q_o_t2 ** (2 ** (m + 1))
        )
        resid = (q_u_n / q_u_n2) ** 6
        tested += 1
        if q_w**3 / q_m != endpoints * resid:
            fails.append((w, n, n2))
        if q_u_n == q_u_n2:
            equal_middles += 1
        if len(rows) < 6:
            rows.append({"word": w, "mirror": mirror, "start": n, "mirror_start": n2,
                         "middle_slack": str(q_u_n), "mirror_middle_slack": str(q_u_n2)})
    return {
        "identity": "(1+q_w)^3 / (1+q_w') = [endpoint terms] * "
                    "((1+q_u @ J(n)) / (1+q_u @ J(n')))^6",
        "length": length,
        "index_bound": bound,
        "distinct_words": len(first),
        "pairs_tested": tested,
        "failures": fails[:6],
        "holds": not fails,
        "pairs_with_equal_middle_slack": equal_middles,
        "knight_case_is_residual_one": "for Collatz the residual is identically 1 because g(u) is "
                                       "word-determined; here it is 1 in none of the pairs",
        "rows": rows,
    }


def per_start_residual(limit: int = 6000, bound: int = INDEX_BOUND,
                       length: int = PAIR_LENGTH) -> dict[str, Any]:
    """The same residual over every realizing START, not one per word: many more instances.

    `residual` takes the least start of each word, giving one pair per word. This enumerates every
    `n < limit` whose length-`length` word has the shape `O u E` and pairs it with the least start of
    `E u O`, so a single word contributes as many instances as it has starts in range.
    """
    first = word_index(length, bound)
    fails = 0
    tested = 0
    equal_middles = 0
    for n in range(2, limit):
        w = word_of(n, length)
        if len(w) != length or w[0] != "O" or w[-1] != "E":
            continue
        u = w[1:-1]
        m, p = len(u), u.count("O")
        n2 = first.get("E" + u + "O")
        if n2 is None:
            continue
        q_w, _ = slack(n, w)
        q_m, _ = slack(n2, "E" + u + "O")
        q_o_n, _ = slack(n, "O")
        q_u_n, _ = slack(floor_power(n), u)
        state = floor_power(n)
        for _ in u:
            state = floor_power(state)
        q_e_t, _ = slack(state, "E")
        q_e_n2, _ = slack(n2, "E")
        q_u_n2, _ = slack(floor_power(n2), u)
        state2 = floor_power(n2)
        for _ in u:
            state2 = floor_power(state2)
        q_o_t2, _ = slack(state2, "O")
        if None in (q_w, q_m, q_o_n, q_u_n, q_e_t, q_e_n2, q_u_n2, q_o_t2):
            continue
        endpoints = (q_o_n ** (3 ** (p + 1)) * q_e_t ** (3 * 2 ** (m + 1))) / (
            q_e_n2 ** (3 ** (p + 1)) * q_o_t2 ** (2 ** (m + 1))
        )
        tested += 1
        if q_w**3 / q_m != endpoints * (q_u_n / q_u_n2) ** 6:
            fails += 1
        if q_u_n == q_u_n2:
            equal_middles += 1
    return {
        "method": "every realizing start below the limit, paired with the least start of the mirror",
        "limit": limit,
        "instances_tested": tested,
        "failures": fails,
        "holds": fails == 0,
        "instances_with_equal_middle_slack": equal_middles,
    }


def probe_payload() -> dict[str, Any]:
    law = concatenation_law()
    res = residual()
    per_start = per_start_residual()
    green = (law["holds"] and res["holds"] and res["pairs_tested"] > 0
             and per_start["holds"] and per_start["instances_with_equal_middle_slack"] == 0)
    return {
        "knight_parts": {
            "i": "two members of one cycle, by Cohn's rotation of the reversed Christoffel word",
            "ii": "an ADDITIVE cocycle whose charge g(u) is word-determined, so it cancels",
            "iii": "the leftover 2^(k-1)/(2^k - 3^x) is not an integer, the gap being odd",
        },
        "concatenation_law": law,
        "residual": res,
        "per_start_residual": per_start,
        "diagnosis": (
            "Part (i) transports for free and part (ii) transports formally: the multiplicative "
            "cocycle gives cube-and-divide as the analogue of 3f - f^R, cancelling the shared middle "
            "exponent exactly. It fails on the numbers, not the algebra: 1 + q is a function of the "
            "word AND the state, and the middle word is read at J(n) along one rotation and J(n') "
            "along the other, so the residual is the sixth power of their ratio instead of 1. That "
            "is the wall J-juggler-is-collatz-one-exponential-up names -- Collatz's word data is "
            "arithmetic and free by Terras, the Juggler's is state-dependent and open by FD."
        ),
        "what_it_leaves": (
            "On a return 1 + q = n^(3^o - 2^L), so the left side is (n^3/n')^G with G the gap: a "
            "perfect G-th power. A Juggler cycle with the Christoffel word AND equal middle slacks "
            "at its two reverse-conjugate readings would force an explicit product of endpoint "
            "slacks to be a perfect G-th power, which is what Knight's parity step becomes under "
            "the exponential. Without that equality there is no exclusion."
        ),
        "decision": {
            "classification": CLASS_RESIDUAL if green else "MULTIPLICATIVE_KNIGHT_FAILED",
            "branch": "CLOSE",
            "green": green,
        },
        "anti_overclaim": (
            "No Juggler cycle is excluded, no floor is raised, N_0 is unchanged and Paper A is "
            "untouched. The transported identity is exact but its residual is not 1, so the method "
            "yields a conditional statement and not an exclusion. The condition -- equal middle "
            "slacks at the two readings -- is a strong Diophantine coincidence with no reason to "
            "hold and is not conjectured here either way."
        ),
    }


def render_markdown(data: dict[str, Any]) -> str:
    res = data["residual"]
    lines = [
        "# The multiplicative Knight, and why its cancellation does not close",
        "",
        f"Status: **{data['decision']['classification']}**",
        "",
        "Generated by `python -m research.juggler_sequence.multiplicative_knight`.",
        "",
        "## Knight's three parts",
        "",
        f"- (i) {data['knight_parts']['i']}",
        f"- (ii) {data['knight_parts']['ii']}",
        f"- (iii) {data['knight_parts']['iii']}",
        "",
        "## The transported identity",
        "",
        f"- concatenation law re-run on `{data['concatenation_law']['splits_checked']}` splits: "
        f"`{data['concatenation_law']['holds']}`",
        f"- `{res['identity']}`",
        f"- exact on `{res['pairs_tested']}` realized pairs at length `{res['length']}` "
        f"(from `{res['distinct_words']}` distinct words below `{res['index_bound']}`): "
        f"`{res['holds']}`",
        f"- pairs whose middle slacks coincide, i.e. Knight's case: "
        f"`{res['pairs_with_equal_middle_slack']}`",
        f"- over every realizing start below `{data['per_start_residual']['limit']}`: "
        f"`{data['per_start_residual']['instances_tested']}` instances, identity holds "
        f"`{data['per_start_residual']['holds']}`, residual equal to 1 in "
        f"`{data['per_start_residual']['instances_with_equal_middle_slack']}`",
        "",
        "| word | mirror | start | mirror start | middle slack | mirror middle slack |",
        "| --- | --- | --- | --- | --- | --- |",
    ]
    for r in res["rows"]:
        lines.append(
            f"| `{r['word']}` | `{r['mirror']}` | {r['start']} | {r['mirror_start']} "
            f"| `{r['middle_slack']}` | `{r['mirror_middle_slack']}` |"
        )
    lines += [
        "",
        "## Diagnosis",
        "",
        data["diagnosis"],
        "",
        "## What it leaves",
        "",
        data["what_it_leaves"],
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
    print("concatenation law:", data["concatenation_law"]["holds"])
    print("residual identity:", data["residual"]["holds"],
          "| pairs:", data["residual"]["pairs_tested"],
          "| residual = 1 in:", data["residual"]["pairs_with_equal_middle_slack"])


if __name__ == "__main__":
    main()
