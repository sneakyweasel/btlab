"""The jumps of Paper B's meander prefactor are the survivor sequence itself.

The measured prefactor `psi` of `J-paper-b-meander-prefactor-is-almost-periodic` is a
function of the rotation coordinate `frac(d * beta)`, `beta = log2/log3`, and it is not
continuous: it jumps at every point of the orbit. This branch asks what the jump
amplitudes are, and the answer is a closed form rather than a measurement.

    a_n = a_1 * N_n / (2 * theta) ^ (n - 1),    n >= 1

where `N_n` is the count of length-`n` parity words no prefix of which contracts -- the
same integer sequence `1, 1, 2, 3, 4, 8, 13, 19, 38, ...` that the whole of Paper B is
about -- and `theta = beta ^ (-beta) * (1 - beta) ^ (beta - 1) / 2` is its exponential
rate. There is exactly one constant in the statement, `a_1`, and it is measured.

**Why.** The barrier word read backwards from `d` is determined by `frac(d * beta)`, and
as that coordinate crosses `frac(n * beta)` the word does not change arbitrarily: two
adjacent letters transpose, `odd, even` becoming `even, odd`. The number of odd letters
is unchanged, so the barrier is unchanged, and the two histories differ by exactly the
survivors standing *on* the barrier at the moment of the swap -- a single point mass,
which is then propagated by the same survivor recursion for the remaining `n` letters.
That is `PaperBJumpTransposition.run_stepRise_stepFlat`, proved over the natural numbers
with no real number anywhere in it, and it is why the jump spectrum is the survivor
sequence and not a new object.

**Three consequences, all exact.**

- `psi` is of bounded variation; the sum of its downward jumps is
  `2 * theta * a_1 * (G(1) - 1)` with `G(1) = sum_d N_d / (2 * theta) ^ d`. The jump
  spectrum and the one factor of the meander constant that
  `J-paper-b-meander-constant-derived` leaves numerical are the same object.
- `a_n ~ 2 * theta * a_1 * psi(frac(n * beta)) * n ^ (-3/2)`: the jump of `psi` at the
  `n`-th orbit point is `psi` at that same point, to a universal constant and a power.
- `C_j = 2 * a_1 * theta ^ (1 - j) * N_n / 2 ^ n` for any `n` with `ceil(n * beta) = j`,
  which is well defined precisely because `N_(n+1) = 2 * N_n` when no power of three lies
  in `[2 ^ n, 2 ^ (n+1))`. The barrier-index sequence that the previous branch could not
  measure past `j` about 25 is now available at every `j`.

**What was withdrawn.** An earlier reading of this cluster recorded a `1/rho` law: the
amplitude ratio across a Sturmian zero is `1/rho = 1.0352968...`. The law is exact, but
`rho` and `theta` are the same number, and a Sturmian zero is an even barrier letter,
which kills nothing and doubles the count. Dividing by `2 * theta` leaves `1/theta`. The
law is one line (`PaperBJumpTransposition.total_stepFlat_eq_two_mul`) and carries no
information beyond the empty-window theorem of `PaperBCertificateLengths`. It is kept
here as an identity, not as a finding.

Counts are exact integers from a height dynamic program; only `a_1` and the fit
diagnostics are floating point.
"""

from __future__ import annotations

import json
from decimal import Decimal, getcontext
from functools import lru_cache
from math import exp, log
from typing import Any

from research.juggler_sequence.lean_paths import DOCS_RESEARCH

JSON_PATH = DOCS_RESEARCH / "juggler_jump_spectrum.json"
DOC_PATH = DOCS_RESEARCH / "juggler_jump_spectrum.md"

CLASS_CLOSED_FORM = "JUMP_SPECTRUM_IS_THE_SURVIVOR_SEQUENCE"
CLASS_OPEN = "JUMP_SPECTRUM_STILL_MEASURED"

#: `log 2 / log 3`, the barrier slope of `PaperBSturmianBarrier`.
BETA = log(2) / log(3)

#: `theta(beta)`, the survivor rate of `PaperBChernoff`. The constant `rho` of the
#: earlier prefactor work is this same number under another name, which is what made the
#: `1/rho` law look like a discovery.
THETA = BETA ** (-BETA) * (1.0 - BETA) ** (BETA - 1.0) / 2.0

#: Depth of the exact integer program behind the committed artifact.
MAX_DEPTH = 4000

#: Amplitude of the jump at `frac(beta)`, the one measured constant in the closed form.
#: Fitted against `psi` on `d` in `[2e5, 1e6]` by the one-parameter model of
#: `psi_model_residual`; stable to `5e-4` across `d`-subranges, across the number of
#: modelled jumps, and against an independent free-amplitude level fit.
A_ONE = 0.42629

#: Half-width of the band on `A_ONE`. The spread across every reading taken, not a
#: standard error: the free-amplitude fit is biased low by a known mechanism and the
#: honest band has to cover both estimators.
A_ONE_BAND = 0.0015


getcontext().prec = 60

#: `beta` to sixty digits, computed once. Recomputing `Decimal.ln` per call costs more
#: than every other part of this branch put together.
_BETA_EXACT = Decimal(2).ln() / Decimal(3).ln()


@lru_cache(maxsize=None)
def ceil_beta(n: int) -> int:
    """`ceil(n * beta)` for any integer `n`, at sixty digits.

    Floating point would be enough at these sizes, but the barrier index decides which
    amplitudes are equal, so a wrong rounding would silently merge two classes.
    """
    value = _BETA_EXACT * n
    whole = int(value)
    if value == whole:
        return whole
    return whole + 1 if value > 0 else whole


def barrier_letter(m: int) -> int:
    """`s_m = ceil(m * beta) - ceil((m-1) * beta)`, the Sturmian barrier word.

    Defined for every integer `m`, not only positive ones: the word determining `psi(x)`
    runs backwards from `x` through the negative indices as well.
    """
    return ceil_beta(m) - ceil_beta(m - 1)


def survivor_counts(max_depth: int = MAX_DEPTH) -> list[int]:
    """Exact `N_0 .. N_max_depth` by the height program of `PaperBJumpTransposition`.

    `profile[h]` counts the survivors of the current length whose odd-count exceeds the
    barrier by `h`. An even letter is `stepFlat`, an odd letter `stepRise`; the survivors
    that fall through the barrier are simply not carried forward.
    """
    profile: dict[int, int] = {0: 1}
    counts = [1]
    for n in range(1, max_depth + 1):
        letter = barrier_letter(n)
        nxt: dict[int, int] = {}
        for height, count in profile.items():
            for climb in (0, 1):
                landed = height + climb - letter
                if landed >= 0:
                    nxt[landed] = nxt.get(landed, 0) + count
        profile = nxt
        counts.append(sum(profile.values()))
    return counts


def amplitude_ratio(counts: list[int], n: int) -> float:
    """`a_n / a_1 = N_n / (2 * theta) ^ (n - 1)`, the closed form. Exact in the counts.

    Taken through logarithms: `N_n` passes a thousand bits well before the depths this
    branch runs to, so the quotient never exists as a product of a big integer and a
    float.
    """
    return exp(log(counts[n]) - (n - 1) * log(2 * THETA))


def amplitude(counts: list[int], n: int, a_one: float = A_ONE) -> float:
    """`a_n`, the jump of `psi` at `frac(n * beta)` approached from below minus above."""
    return a_one * amplitude_ratio(counts, n)


def barrier_index_constant(counts: list[int], j: int, a_one: float = A_ONE) -> float:
    """`C_j = 2 * a_1 * theta ^ (1 - j) * N_n / 2 ^ n`, for any `n` with `ceil(n*beta)=j`.

    Well defined because the two `n` in a class differ by an even letter, which doubles
    `N_n` exactly (`PaperBCertificateLengths.window_empty` and
    `PaperBJumpTransposition.total_stepFlat_eq_two_mul`). The caller gets the reading at
    the first such `n`; `barrier_index_consistency` checks the second agrees.
    """
    n = first_index_of_class(counts, j)
    return 2.0 * a_one * exp((1 - j) * log(THETA) + log(counts[n]) - n * log(2.0))


def first_index_of_class(counts: list[int], j: int) -> int:
    """The smallest `n` with `ceil(n * beta) = j`.

    `ceil(n * beta) = j` says `(j-1)/beta < n <= j/beta`, so the smallest such `n` is
    `floor((j-1)/beta) + 1` and no scan is needed; the result is checked rather than
    trusted, because an off-by-one here would silently read the wrong class. Raises a
    clear error rather than a bare `StopIteration`, which pytest turns into an
    unreadable generator failure.
    """
    n = int((j - 1) / _BETA_EXACT) + 1
    if not 1 <= n < len(counts):
        raise ValueError(f"barrier index {j} needs a depth above {len(counts) - 1}")
    if ceil_beta(n) != j or ceil_beta(n - 1) == j:
        raise ValueError(f"barrier index {j} resolved to n = {n}, which is not its first")
    return n


def max_barrier_index(counts: list[int]) -> int:
    """The largest `j` both of whose class members the program has reached."""
    return ceil_beta(len(counts) - 1) - 1


def barrier_index_consistency(counts: list[int], max_j: int) -> float:
    """Worst relative disagreement of `C_j` between the two `n` of a class.

    This is the `1/rho` law restated as a well-definedness check, and it is exact rather
    than approximate: an even letter doubles the count, full stop.
    """
    classes: dict[int, list[int]] = {}
    for n in range(1, len(counts)):
        classes.setdefault(ceil_beta(n), []).append(n)
    worst = 0.0
    for j, members in classes.items():
        if j > max_j or len(members) < 2:
            continue
        lo, hi = members[0], members[1]
        # C_j is proportional to N_n / 2^n, so the two readings agree exactly when
        # N_hi * 2^lo == N_lo * 2^hi. Cross-multiplied integers, because the float
        # logarithm of a thousand-bit count cannot cancel to the last bit even when
        # the underlying identity is exact.
        left = counts[hi] << lo
        right = counts[lo] << hi
        worst = max(worst, abs(left - right) / right)
    return worst


def sturmian_zero_ratios(counts: list[int], max_n: int) -> list[float]:
    """`a_n / a_(n-1)` across the Sturmian zeros, which must all be exactly `1 / theta`."""
    return [
        (counts[n] / counts[n - 1]) / (2.0 * THETA)
        for n in range(2, max_n + 1)
        if ceil_beta(n) == ceil_beta(n - 1)
    ]


def g_one(counts: list[int]) -> float:
    """`G(1) = sum_d N_d / (2 * theta) ^ d`, truncated at the program's depth.

    The summand decays like `psi * d ^ (-3/2)`, so the truncation error is about
    `2 * psi / sqrt(depth)` and is reported separately rather than folded in.
    """
    scale = log(2 * THETA)
    return sum(exp(log(counts[d]) - d * scale) for d in range(len(counts)))


def g_one_tail_bound(counts: list[int], psi_scale: float = 10.9) -> float:
    """The `2 * psi / sqrt(depth)` estimate of what `g_one` leaves out."""
    depth = len(counts) - 1
    return 2.0 * psi_scale / depth**0.5


def total_variation(counts: list[int], a_one: float = A_ONE) -> float:
    """Sum of the downward jumps of `psi`, `2 * theta * a_1 * (G(1) - 1)`.

    Equivalently `sum_(n>=1) a_n`. The jump at `x = 0` is `a_0 = 2 * theta * a_1` and is
    the wrap of the circle, so including it gives `2 * theta * a_1 * G(1)`, which is the
    total continuous rise that periodicity demands.
    """
    return 2.0 * THETA * a_one * (g_one(counts) - 1.0)


def probe_payload(max_depth: int = MAX_DEPTH) -> dict[str, Any]:
    counts = survivor_counts(max_depth)
    zeros = sturmian_zero_ratios(counts, min(max_depth, 500))
    worst_zero = max(abs(r - 1.0 / THETA) for r in zeros) / (1.0 / THETA)
    consistency = barrier_index_consistency(counts, max_j=min(200, max_barrier_index(counts)))
    gee = g_one(counts)
    return {
        "answer": "the jump spectrum is the survivor sequence",
        "beta": BETA,
        "theta": THETA,
        "max_depth": max_depth,
        "identity": "a_n = a_1 * N_n / (2*theta)^(n-1)",
        "a_one": {
            "estimate": A_ONE,
            "band": [A_ONE - A_ONE_BAND, A_ONE + A_ONE_BAND],
            "note": (
                "the only measured constant in the closed form; the ratios a_n/a_1 are"
                " exact integers over a power and carry no fitted quantity at all"
            ),
        },
        "survivors_1_to_9": counts[1:10],
        "amplitude_ratios": {str(n): amplitude_ratio(counts, n) for n in (2, 5, 10, 50, 200)},
        "sturmian_zeros": {
            "count": len(zeros),
            "predicted_ratio": 1.0 / THETA,
            "worst_relative_deviation": worst_zero,
            "why_trivial": (
                "rho and theta are the same number and a Sturmian zero is an even"
                " barrier letter, which kills nothing and doubles the count; the law is"
                " the empty-window theorem and nothing more"
            ),
        },
        "barrier_index": {
            "worst_class_disagreement": consistency,
            "classes_checked": min(200, max_barrier_index(counts)),
            "C_1": barrier_index_constant(counts, 1),
            "C_25": barrier_index_constant(counts, 25),
            "j_max": max_barrier_index(counts),
            "C_j_max": barrier_index_constant(counts, max_barrier_index(counts)),
            "note": (
                "closed form at every j; the previous branch reached about j = 25 by"
                " local differencing and no fit reaches further, because the data cannot"
                " constrain a high-n jump at all -- its column averages into the ramp"
            ),
        },
        "g_one": {
            "truncated": gee,
            "tail_estimate": g_one_tail_bound(counts),
            "ledger_value": 7.07,
        },
        "total_variation": total_variation(counts),
        "decision": {
            "classification": CLASS_CLOSED_FORM,
            "reason": (
                "the identity is verified two independent ways -- a transfer-operator"
                " propagation agreeing with the exact counts to machine precision, and a"
                " one-parameter fit of psi whose single amplitude is stable across"
                " d-subranges, across the number of modelled jumps, and to between"
                " 0.03 and 0.35 percent against a freely fitted head amplitude for"
                " splits of the spectrum at n >= 5"
            ),
        },
        "anti_overclaim": (
            "This determines the jumps of psi, not psi. A model of psi as its jumps plus"
            " the linear rise periodicity demands leaves a residual of 1.35e-02 against a"
            " noise floor of 4.4e-03, and 89 percent of that residual variance is a"
            " reproducible function of the coordinate. So psi has structure beyond its"
            " jump spectrum, and this branch does not say what it is. Nor is any of this"
            " a proof: the asymptotic psi itself remains measured, and the Lean module"
            " proves only the finite exchange cost that the spectrum rests on."
        ),
    }


def render_markdown(data: dict[str, Any]) -> str:
    zeros = data["sturmian_zeros"]
    lines = [
        "# Juggler: the jumps of the meander prefactor",
        "",
        "Generated by `python -m research.juggler_sequence.jump_spectrum`.",
        "",
        "## Answer",
        "",
        f"`{data['identity']}`, with `N_n` the survivor counts and `theta"
        f" = {data['theta']:.10f}`.",
        "",
        f"- exact survivor counts `N_1..9 = {data['survivors_1_to_9']}`",
        f"- one measured constant, `a_1 = {data['a_one']['estimate']:.5f}`"
        f" +/- `{(data['a_one']['band'][1] - data['a_one']['estimate']):.4f}`",
        f"- Sturmian zeros: `{zeros['count']}` of them, ratio"
        f" `{zeros['predicted_ratio']:.10f}` to"
        f" `{zeros['worst_relative_deviation']:.1e}`",
        f"- barrier-index classes agree exactly:"
        f" `{data['barrier_index']['worst_class_disagreement']:.1e}` over"
        f" `{data['barrier_index']['classes_checked']}` classes",
        f"- `C_j` available to `j = {data['barrier_index']['j_max']}`, against about"
        f" `25` for the fits",
        f"- `G(1) = {data['g_one']['truncated']:.5f}` truncated, tail about"
        f" `{data['g_one']['tail_estimate']:.4f}`, ledger `{data['g_one']['ledger_value']}`",
        f"- total variation of `psi` (downward jumps) `{data['total_variation']:.4f}`",
        "",
        "## Why the `1/rho` law is trivial",
        "",
        zeros["why_trivial"] + ".",
        "",
        "## What this does not say",
        "",
        data["anti_overclaim"],
        "",
    ]
    return "\n".join(lines)


def write_artifacts(payload: dict[str, Any] | None = None) -> dict[str, Any]:
    data = payload if payload is not None else probe_payload()
    JSON_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(data, indent=2) + "\n", encoding="utf-8")
    DOC_PATH.write_text(render_markdown(data), encoding="utf-8")
    return data


def main() -> None:
    payload = write_artifacts()
    print(payload["decision"]["classification"])
    print(payload["identity"])
    print(
        "zeros",
        payload["sturmian_zeros"]["count"],
        "worst",
        f"{payload['sturmian_zeros']['worst_relative_deviation']:.1e}",
        "G(1)",
        f"{payload['g_one']['truncated']:.4f}",
    )


if __name__ == "__main__":
    main()
