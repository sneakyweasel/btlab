"""Are the laboratory's imported classical results the strongest available?

Not a halt theorem, not new mathematics, not a Juggler construction. An
audit: for every external result the programme leans on, is the cited
version the sharpest one, and does anything imported for purpose X also
apply to a purpose Y that is still running on something weaker?

The branch exists because that failure mode was found twice in one day.
`cycle_wuwang_reduction` found Paper A Corollary 4.11 running on Rhin
while Wu-Wang sat in the repository, cited only as a fan-width cap --
worth a factor 2.795 in the exponent of a published corollary. A peer
session found twelve theorem-ledger rows sharing one defect, visible
only because the gate stops at the first failure. Two hits, neither
requiring any new mathematics.

**The transcendence chain has one clean statement.** Everything the
cycle side needs from transcendence enters through one quantity: a lower
bound on the linear form `Lambda = o log 3 - L log 2`. Through
`cycleMin_length_of_gap_power` that becomes `n log n <= (2/C) L^(p+1)`.
Writing `mu` for a proved irrationality measure of `log 2 / log 3`, the
conversion `|Lambda| = L log 3 |alpha - o/L|` gives `p + 1 = mu` exactly.
So:

    the closure-threshold exponent IS the irrationality measure of
    log 2 / log 3 that you can prove.

That identity makes the audit mechanical, and it explains the Dirichlet
floor recorded in `cycle_wuwang_reduction`: `mu >= 2` for every
irrational, so no Diophantine input ever takes the target below `L^2`.

**What the chain looks like once assembled.** Paper A prints `L^14.3`,
from Rhin's Proposition p. 160 equation (7) repackaged by Simons-de
Weger Lemma 12 with an explicit constant. Rhin's equation (8), on the
same page of the same paper, is quoted in the literature as
`mu(log 3 / log 2) <= 8.616`, which converts to `L^8.616`. So Paper A's
own citation contained a sharper statement one equation further down.
Wu-Wang then gives `L^5.1163051`, which is what the laboratory now uses.
The 8.616 row is recorded as UNVERIFIED: it is taken from a third-party
report and must be checked against Rhin before use, and whether its
constant is explicit is not established here.

**The Paper C concentration constants: two dead ends, measured.** The
audit's first target was `tao_reduction.azuma_exponent`, on the
reasoning that Azuma-Hoeffding uses only an increment range and is
lossy for two-valued increments, where the sharp bound is Chernoff-KL --
which the unbiased path in the same module already uses. Azuma is indeed
lossy, and it does not matter: the integer constants do not move. The
second target was the gap between the endpoint Chernoff bound and the
exact first-passage probability, which the module already computes by
DP. That gap is real at finite depth and vanishes, because a
negative-drift walk conditioned to stay above a level pays the same
exponential cost as one merely ending above it. Both are recorded so
that the direction is closed rather than re-proposed.

Probe: `python -m research.juggler_sequence.external_input_audit`.
"""

from __future__ import annotations

import json
import math
from typing import Any

from research.juggler_sequence.cycle_finance import DATA_DIR
from research.juggler_sequence.tao_reduction import (
    LOG2_3,
    REQUIRED_RATE,
    azuma_exponent,
    chernoff_exponent,
    kl_bernoulli,
    least_C,
    least_C_biased,
)

#: `log 2 / log 3`, the number every cycle-side Diophantine input measures.
ALPHA = math.log(2) / math.log(3)

#: Each row: proved irrationality measure of `log 2 / log 3`, the exponent
#: it puts on `L` in `n log n <= C L^mu`, whether the constant is explicit,
#: and whether the laboratory has verified it against the primary source.
TRANSCENDENCE_CHAIN: tuple[dict[str, Any], ...] = (
    {
        "source": "rhin-1987-pade-irrationality",
        "route": "Proposition p.160 eq.(7) via simons-de-weger Lemma 12",
        "mu": 14.3,
        "effective": True,
        "constant": "915 (printed in Paper A)",
        "verified_against_primary": True,
        "used_by": "Paper A Corollary 4.11 (deposited text)",
    },
    {
        "source": "rhin-1987-pade-irrationality",
        "route": "Proposition p.160 eq.(8), the ratio measure itself",
        "mu": 8.616,
        "effective": True,
        "constant": "not extracted here",
        "verified_against_primary": False,
        "used_by": "nothing -- never recorded in the laboratory",
    },
    {
        "source": "wu-wang-2014-irrationality-measure-log3",
        "route": "linear form at a=0, H=max(L,o)=L",
        "mu": 5.1163051,
        "effective": False,
        "constant": "C_eps implied, eps-asymptotic",
        "verified_against_primary": True,
        "used_by": "J-cyclemin-gap-power-transfer (cycle_wuwang_reduction)",
    },
    {
        "source": "bondareva-luchin-salikhov-2018-log3-irrationality",
        "route": "same shape, sharpened exponent",
        "mu": 5.116201,
        "effective": False,
        "constant": "implied",
        "verified_against_primary": True,
        "used_by": "recorded only; in the noise at 1e-4",
    },
    {
        "source": "Dirichlet",
        "route": "every irrational has mu >= 2",
        "mu": 2.0,
        "effective": True,
        "constant": "1",
        "verified_against_primary": True,
        "used_by": "the hard floor on the closure threshold",
    },
)


def closure_exponent(mu: float) -> float:
    """The exponent a minimum lower bound must beat, given a measure `mu`.

    `|Lambda| = L log 3 |alpha - o/L| >= c L^(1-mu)`, and
    `n log n <= 2 L / Lambda`, so `n log n <= (2/c) L^mu`. The closure
    threshold exponent equals `mu` exactly.
    """
    return mu


def linear_form_exponent(mu: float) -> float:
    """`p` in the budget `C L^(-p)` of `cycleMin_length_of_gap_power`."""
    return mu - 1.0


def transcendence_audit() -> list[dict[str, Any]]:
    """The chain, sorted strongest first, with what each would buy."""
    rows = []
    for row in TRANSCENDENCE_CHAIN:
        mu = row["mu"]
        rows.append(
            {
                **row,
                "linear_form_exponent_p": linear_form_exponent(mu),
                "closure_exponent": closure_exponent(mu),
                "period_exponent_in_n": 1.0 / mu,
            }
        )
    return sorted(rows, key=lambda r: r["mu"])


def transcendence_checks() -> list[dict[str, Any]]:
    best = min(r["mu"] for r in TRANSCENDENCE_CHAIN if r["source"] != "Dirichlet")
    in_use = next(
        r for r in TRANSCENDENCE_CHAIN if r["used_by"].startswith("J-cyclemin")
    )
    printed = next(r for r in TRANSCENDENCE_CHAIN if r["used_by"].startswith("Paper A"))
    unrecorded = [r for r in TRANSCENDENCE_CHAIN if r["used_by"].startswith("nothing")]
    return [
        {
            # Not an equality: BLS 2018 is sharper by 1.04e-4 and is deliberately
            # not imported (juggler_cycle_walk_fan_growth: "do not import them as
            # a new branch"). The audit records the residual rather than hiding it.
            "check": "the measure in use is within 1e-3 of the sharpest verified one",
            "ok": 0.0 <= in_use["mu"] - best < 1e-3,
            "value": in_use["mu"] - best,
        },
        {
            "check": "the sharper verified member is BLS 2018, knowingly unimported",
            "ok": min(
                (r for r in TRANSCENDENCE_CHAIN if r["verified_against_primary"] and r["mu"] > 2.0),
                key=lambda r: r["mu"],
            )["source"].startswith("bondareva"),
            "value": best,
        },
        {
            "check": "the deposited Paper A text is weaker than its own citation",
            "ok": printed["mu"] > 8.616,
            "value": printed["mu"] / 8.616,
        },
        {
            "check": "exactly one chain member is unrecorded in the laboratory",
            "ok": len(unrecorded) == 1,
            "value": len(unrecorded),
        },
        {
            "check": "the unrecorded member is not yet verified against the primary source",
            "ok": all(not r["verified_against_primary"] for r in unrecorded),
            "value": unrecorded[0]["source"],
        },
        {
            "check": "Dirichlet floors the closure exponent at 2",
            "ok": abs(closure_exponent(2.0) - 2.0) < 1e-12,
            "value": 2.0,
        },
    ]


def kl_exponent(C: float, q: float) -> float:
    """The sharp two-valued replacement for `azuma_exponent`.

    Under a per-step odd-share cap `q`, the odd count over `d = C L` steps is
    dominated by `Bin(d, q)`, and staying above `-L` forces an odd share of at
    least `p = (1 - 1/C)/log2(3)`. Chernoff-KL then gives `2^(-e L)` with
    `e = C KL(p || q) / ln 2`. At `q = 1/2` this reproduces
    `tao_reduction.chernoff_exponent` exactly.
    """
    p = (1.0 - 1.0 / C) / LOG2_3
    if p <= q:
        return 0.0
    if p >= 1.0:
        return math.inf
    return C * kl_bernoulli(p, q) / math.log(2.0)


def least_C_kl(q: float, rate: float = REQUIRED_RATE, cap: int = 100_000) -> int | None:
    C = 2
    while kl_exponent(C, q) <= rate:
        C += 1
        if C > cap:
            return None
    return C


def concentration_audit(qs: tuple[float, ...] = (0.5, 0.55, 0.6)) -> list[dict[str, Any]]:
    """Azuma against the sharp KL bound, and whether the integers move."""
    out = []
    for q in qs:
        a, k = least_C_biased(q), least_C_kl(q)
        out.append(
            {
                "q": q,
                "azuma_least_C": a,
                "kl_least_C": k,
                "moves": a != k,
                "azuma_exponent_at_azuma_C": azuma_exponent(a, q) if a else None,
                "kl_exponent_at_azuma_C": kl_exponent(a, q) if a else None,
            }
        )
    return out


def log2_bad(L: float, d: int) -> float:
    """Exact `log2 P(walk stays above -L for all t <= d)`, big-integer DP.

    `tao_reduction.bad_word_probability` divides by `2.0**d` and overflows
    past `d = 1023`; this returns the logarithm instead, so the asymptotics
    can actually be read.
    """
    counts = {0: 1}
    for t in range(1, d + 1):
        nxt: dict[int, int] = {}
        for o, c in counts.items():
            for o2 in (o, o + 1):
                if o2 * LOG2_3 - t > -L:
                    nxt[o2] = nxt.get(o2, 0) + c
        counts = nxt
        if not counts:
            return -math.inf
    total = sum(counts.values())
    bits = total.bit_length()
    shift = max(bits - 53, 0)
    return (bits - 53) + math.log2(total >> shift) - d if shift else math.log2(total) - d


def first_passage_gap(C: int = 18, Ls: tuple[int, ...] = (20, 40, 80)) -> list[dict[str, Any]]:
    """Exact first-passage exponent against the endpoint Chernoff bound.

    The excess is positive at every finite depth and shrinks: a
    negative-drift walk conditioned to stay above a level pays the same
    exponential cost as one merely ending above it, so the Chernoff rate is
    the true rate and the finite-depth surplus is `O(log L / L)`. If the
    excess times `L` were bounded the surplus would be `O(1/L)`; it grows
    slowly instead, which is the logarithm.
    """
    bound = chernoff_exponent(C)
    rows = []
    for L in Ls:
        e = -log2_bad(L, int(C * L)) / L
        rows.append(
            {
                "C": C,
                "L": L,
                "exact_exponent": e,
                "chernoff_bound": bound,
                "excess": e - bound,
                "excess_times_L": (e - bound) * L,
            }
        )
    return rows


def report() -> dict[str, Any]:
    chain = transcendence_audit()
    checks = transcendence_checks()
    conc = concentration_audit()
    passage = first_passage_gap()
    return {
        "alpha": ALPHA,
        "transcendence_chain": chain,
        "transcendence_checks": checks,
        "concentration": conc,
        "first_passage": passage,
        "all_transcendence_checks_ok": all(c["ok"] for c in checks),
        "sharpest_verified_mu": min(
            r["mu"] for r in chain if r["verified_against_primary"] and r["mu"] > 2.0
        ),
        "unverified_candidate_mu": min(
            (r["mu"] for r in chain if not r["verified_against_primary"]), default=None
        ),
        "concentration_constants_move": any(r["moves"] for r in conc[:2]),
        "first_passage_excess_shrinks": all(
            passage[i]["excess"] > passage[i + 1]["excess"] for i in range(len(passage) - 1)
        ),
        "is_halt_theorem": False,
        "new_mathematics": False,
    }


def write_artifacts(payload: dict[str, Any] | None = None) -> dict[str, Any]:
    data = payload if payload is not None else report()
    DATA_DIR.mkdir(parents=True, exist_ok=True)
    (DATA_DIR / "external_input_audit.json").write_text(
        json.dumps(data, indent=2) + "\n", encoding="utf-8"
    )
    return data


def main() -> None:
    data = write_artifacts()
    print("transcendence chain (mu = closure exponent = irrationality measure of log2/log3):")
    for row in data["transcendence_chain"]:
        flag = "" if row["verified_against_primary"] else "  [UNVERIFIED]"
        print(
            f"  mu={row['mu']:<10} L>>n^{row['period_exponent_in_n']:.4f}  "
            f"{row['source']}{flag}"
        )
    print(
        f"\nsharpest verified mu = {data['sharpest_verified_mu']}; "
        f"unverified candidate = {data['unverified_candidate_mu']} "
        "(Rhin eq.(8), never recorded here)"
    )
    print("\nPaper C concentration constants:")
    for row in data["concentration"]:
        print(
            f"  q={row['q']}: Azuma C={row['azuma_least_C']}  KL C={row['kl_least_C']}  "
            f"moves={row['moves']}"
        )
    print(
        "first-passage excess over Chernoff shrinks: "
        f"{data['first_passage_excess_shrinks']}"
    )


if __name__ == "__main__":
    main()
