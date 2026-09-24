"""The Juggler dropping time and the first contracting length of its own parity word.

Question. Let `J(x) = isqrt(x)` for even `x` and `isqrt(x^3)` for odd `x` (A094683).
For a start `m >= 2` let `w` be the parity word of its orbit and `tau(w)` the first
length `t` at which `3^o_t < 2^t`, `o_t` counting the odd letters among the first
`t`. `power_bound_contracts` (Envelope.lean, kernel) gives `J^tau(m) < m`, so the
dropping time is at most `tau`. Can the floors make it strictly smaller -- an
UNCERTIFIED drop, at a prefix that is still non-contracting? Not a halt theorem.

What this probe establishes.

1. THE EXACT LOSS IDENTITY. With `rho_i = 3^{o_i} / 2^i` and `xi_i = m^{rho_i}` the
   floor-free chain, the deficit `d_i = ln xi_i - ln x_i` obeys

       d_{i+1} = p_i d_i + eta_i,    eta_i = ln(x_i^{p_i} / x_{i+1}) in [0, ln(1 + 1/x_{i+1})),

   `p_i in {3/2, 1/2}`, because `x_{i+1} <= x_i^{p_i} < x_{i+1} + 1`. Unrolled,
   `d_k <= rho_k * sum_{j<=k} ln(1 + 1/x_j) / rho_j`.

2. THE DROP CRITERION (theorem, human proof). If the prefix of length `k` is
   non-contracting, no drop happened before `k`, and `x_k <= m - 1`, then

       S_{k-1} := sum_{j=1}^{k-1} 1 / (rho_j x_j)  >=  (1 - 1/rho_k) ln m.

   Proof: the `j = k` term of the unrolled bound is `ln(x_k + 1) - ln x_k`; move it to
   the left, where `ln(x_k + 1) <= ln m`, and divide by `rho_k`.

3. THE CRUDE EXCURSION BOUND (corollary). `x_j >= m` for `j < k`, and
   `sum_{j<k} 1/rho_j < 2 O` because each odd count `o` contributes a run of indices
   whose reciprocals `2^j / 3^o` sum below `2 / rho` at the run's last index, where
   `rho > 1`. So `S_{k-1} < 2 O / m`. And `rho_k >= 2^{f_O}` with `f_O = {O log2 3}`,
   since `k <= floor(O log2 3)`; `f_O >= delta(O) := min_{o <= O} ||o log2 3||`. Hence an
   uncertified drop whose prefix has `O` odd letters needs

       2 O / m  >  (1 - 2^{-delta(O)}) ln m.

4. THE REFINED EXCURSION BOUND (corollary, human proof). If moreover `2 O / m <= ln 2`
   (so `S <= ln 2` by item 3), then `ln x_j = rho_j ln m - d_j >= rho_j (ln m - S)`
   gives `x_j >= (m/2)^{rho_j}`, hence `1/(rho_j x_j) <= (2/m)^{rho_j} / rho_j`. Within
   the run of an odd count `o` these terms grow with `j` by a factor at least `m/2`
   each step back from the last index, where `rho >= 2^{f_o}`; the run of `o = O` has
   `rho > 2`. So

       S_{k-1}  <=  (1 + 2/m) * ( sum_{o=1}^{O-1} (2/m)^{2^{f_o}}  +  2/m^2 ),

   and an uncertified drop with `O` odd letters needs this to exceed
   `(1 - 2^{-f_O}) ln m`. Both sides are monotone in `m` the right way, so a failure
   at `m = M` is a failure for every `m >= M`. The `f_o` are exact (integer
   arithmetic on a 50-digit `log2 3`), so the least admissible `O` at each `M` is a
   finite computation: `665` (crude) becomes `16266` at `M = 10^6`, and the admissible
   `O` below the next dangerous denominator vanish one range at a time.

5. THE NUMBERS. For every odd `m < 10^6` the drop is at `tau`, in exact integers, the
   five starts whose excursions pass 400000 digits included (chunk runs extend this;
   see the dossier). Along those excursions the floors keep at least 73% of the ideal
   margin (`m = 9`), at least 90% for `m >= 11`, and the loss-accounting bound never
   uses more than 1.8% of the slack for `m >= 11`. At the near-drops -- the even steps
   landing with `1 < rho < 2`, where a counterexample would have to happen -- the
   value sits below its ideal `m^{rho}` by a shortfall that is recorded in units; a
   drop needs a shortfall of about `0.69 f_O m ln m` units there.

6. WHAT IS NOT PROVED, AND WHY. A counterexample needs an excursion of `O_min(m)` odd
   letters ending at a denominator of a convergent of `log2 3` on the side
   `3^O > 2^p`, with the near-drop losses aligned. Nothing bounds the excursion; the
   heuristic probability of one that long is about `0.9659^{1.58 O}`. This is the
   mirror of Terras's Conjecture 2.9: there the `+1`s must never delay the drop, here
   the floors must never hasten it.
"""

from __future__ import annotations

import argparse
import json
import time
from math import exp, expm1, log
from typing import Any

from flint import arb, ctx
from mpmath import mp
from mpmath import floor as mpfloor
from mpmath import log as mplog

from research_engine.diophantine import convergents, partial_quotients_past

from research.juggler_sequence.collatz_bridge import juggler
from research.juggler_sequence.lean_paths import DATA_ROOT, DOCS_RESEARCH

DATA_DIR = DATA_ROOT / "drop_first_contracting_length"
JSON_PATH = DATA_DIR / "summary.json"
DOC_PATH = DOCS_RESEARCH / "juggler_drop_first_contracting_length.md"

LN2 = log(2.0)
LN3 = log(3.0)

# 400000 decimal digits: the cap beyond which a first pass defers a start to a second,
# uncapped pass. Below 10^6 five starts need it; the largest reaches 1909409 digits.
CAP_BITS = 1_330_000


def big_log(n: int) -> float:
    """Natural log of a positive integer of any size, from its top 53 bits."""
    bits = n.bit_length()
    if bits <= 53:
        return log(n)
    return (bits - 53) * LN2 + log(n >> (bits - 53))


def a020914(n: int) -> int:
    """A020914(n): the number of binary digits of 3^n, the only possible drop lengths."""
    return (3**n).bit_length()


def first_contracting_length(word: list[int]) -> int | None:
    """The least `t` with `3^ones(t) < 2^t`, or None when no prefix contracts."""
    ones = 0
    for t, letter in enumerate(word, start=1):
        ones += letter
        if 3**ones < 2**t:
            return t
    return None


class Capped(Exception):
    """The orbit of this start passed the digit cap before dropping."""


def analyse_start(m: int, cap_bits: int | None = None) -> dict[str, Any]:
    """Run the orbit of `m >= 2` to its first value below `m`, with the loss accounting.

    Returns the dropping time, the word, `tau(word)`, the peak size in bits, and, over
    the non-contracting prefixes, whether the identity `d_i <= rho_i S_i` ever failed
    numerically, the smallest retained fraction `ln(x_i/m) / ((rho_i - 1) ln m)` of the
    ideal margin at an even step that did not drop, the largest value of the
    loss-accounting bound `rho_i S_{i-1} / ((rho_i - 1) ln m)` there, and at the
    near-drops (even steps landing with `1 < rho_i < 2`) the largest shortfall
    `m^{rho_i} - x_i` in units and relative to the ideal.
    """
    if m < 2:
        raise ValueError("starts are m >= 2")
    lm = big_log(m)
    v, i, o = m, 0, 0
    word: list[int] = []
    partial = 0.0  # S_{i-1}: sum over j < i of 1/(rho_j x_j)
    peak_bits = m.bit_length()
    min_retained: float | None = None
    arg_retained: int | None = None
    max_loss_ratio: float | None = None
    arg_loss: int | None = None
    near_drops = 0
    max_shortfall_units: float | None = None
    max_shortfall_rel: float | None = None
    arg_shortfall: int | None = None
    violations = 0
    while True:
        bit = v % 2
        word.append(bit)
        o += bit
        nxt = juggler(v)
        i += 1
        if nxt < m:
            break
        if cap_bits is not None and nxt.bit_length() > cap_bits:
            raise Capped(m)
        v = nxt
        peak_bits = max(peak_bits, v.bit_length())
        lam = o * LN3 - i * LN2  # ln rho_i, positive: the prefix is non-contracting
        rho = exp(lam)
        rho_minus_one = expm1(lam)
        lx = big_log(v)
        deficit = rho * lm - lx
        term = exp(-lam - lx)  # 1/(rho_i x_i)
        if deficit > rho * (partial + term) * (1 + 1e-9) + 1e-9:
            violations += 1
        if bit == 0:
            retained = (lx - lm) / (rho_minus_one * lm)
            if min_retained is None or retained < min_retained:
                min_retained, arg_retained = retained, i
            ratio = partial * rho / (rho_minus_one * lm)
            if max_loss_ratio is None or ratio > max_loss_ratio:
                max_loss_ratio, arg_loss = ratio, i
            if rho < 2.0:
                near_drops += 1
                ideal = exp(rho * lm)  # below m^2, safe as a float
                units = ideal - v
                rel = -expm1(-deficit)  # 1 - x_i / ideal
                if max_shortfall_units is None or units > max_shortfall_units:
                    max_shortfall_units, max_shortfall_rel, arg_shortfall = units, rel, i
        partial += term
    return {
        "m": m,
        "dropping_time": i,
        "tau": first_contracting_length(word),
        "odd_letters": o,
        "peak_bits": peak_bits,
        "word": "".join("O" if b else "E" for b in word),
        "min_retained": min_retained,
        "arg_retained": arg_retained,
        "max_loss_ratio": max_loss_ratio,
        "arg_loss": arg_loss,
        "near_drops": near_drops,
        "max_shortfall_units": max_shortfall_units,
        "max_shortfall_rel": max_shortfall_rel,
        "arg_shortfall": arg_shortfall,
        "identity_violations": violations,
    }


def study(limit: int, cap_bits: int | None = CAP_BITS, start: int = 3) -> dict[str, Any]:
    """Every odd start in `[start, limit)`; starts that pass the cap are re-run without one."""
    t0 = time.time()
    early: list[dict[str, Any]] = []
    capped: list[int] = []
    worst_retained: list[list[Any]] = []
    worst_loss: list[list[Any]] = []
    worst_shortfall: list[list[Any]] = []
    shortfall_hist = [0] * 11  # units 0-1, 1-2, ..., 9-10, >= 10
    violations = 0
    checked = 0
    near_drop_total = 0
    biggest = [0, 0]
    longest = [0, 0]

    def absorb(res: dict[str, Any]) -> None:
        nonlocal violations, checked, near_drop_total
        checked += 1
        violations += res["identity_violations"]
        near_drop_total += res["near_drops"]
        if res["tau"] != res["dropping_time"]:
            early.append({k: res[k] for k in ("m", "dropping_time", "tau", "word")})
        if res["peak_bits"] > biggest[0]:
            biggest[:] = [res["peak_bits"], res["m"]]
        if res["dropping_time"] > longest[0]:
            longest[:] = [res["dropping_time"], res["m"]]
        if res["min_retained"] is not None:
            worst_retained.append(
                [res["min_retained"], res["m"], res["arg_retained"], res["dropping_time"], res["odd_letters"]]
            )
            worst_retained.sort()
            del worst_retained[10:]
            worst_loss.append(
                [res["max_loss_ratio"], res["m"], res["arg_loss"], res["dropping_time"], res["odd_letters"]]
            )
            worst_loss.sort(reverse=True)
            del worst_loss[10:]
        if res["max_shortfall_units"] is not None:
            u = res["max_shortfall_units"]
            shortfall_hist[min(10, int(u))] += 1
            worst_shortfall.append([u, res["max_shortfall_rel"], res["m"], res["arg_shortfall"], res["odd_letters"]])
            worst_shortfall.sort(reverse=True)
            del worst_shortfall[10:]

    first = start if start % 2 == 1 else start + 1
    for m in range(first, limit, 2):
        try:
            absorb(analyse_start(m, cap_bits))
        except Capped:
            capped.append(m)
    uncapped: list[dict[str, Any]] = []
    for m in capped:
        res = analyse_start(m, None)
        absorb(res)
        uncapped.append(
            {
                "m": m,
                "dropping_time": res["dropping_time"],
                "tau": res["tau"],
                "odd_letters": res["odd_letters"],
                "digits": int(res["peak_bits"] * 0.30103),
            }
        )
    return {
        "start": first,
        "limit": limit,
        "odd_starts": checked,
        "seconds": round(time.time() - t0, 1),
        "early_drops": early,
        "identity_violations": violations,
        "capped_then_run_uncapped": uncapped,
        "largest_excursion_bits_m": biggest,
        "longest_dropping_time_m": longest,
        "smallest_retained_fraction": worst_retained,
        "largest_loss_ratio": worst_loss,
        "near_drops_total": near_drop_total,
        "near_drop_shortfall_units_histogram": shortfall_hist,
        "largest_near_drop_shortfall": worst_shortfall,
    }


def gmp_sweep(limit: int, start: int = 3, cap_bits: int = CAP_BITS) -> dict[str, Any]:
    """The dropping-time check alone, on GMP integers through gmpy2.

    An independent implementation of the equality check with no loss accounting,
    for ranges whose excursions run to tens of millions of digits, where Python's
    Karatsuba-only integers stall. Returns the chunk format of `study`, with
    `identity_violations` None and the loss statistics empty; starts whose peak
    passes `cap_bits` are listed under `capped_then_run_uncapped` for the merge.
    """
    try:
        from gmpy2 import isqrt as gmp_isqrt
        from gmpy2 import mpz
    except ImportError as exc:  # pragma: no cover - environment without gmpy2
        raise RuntimeError("gmpy2 is not installed") from exc
    t0 = time.time()
    first = start if start % 2 == 1 else start + 1
    early: list[dict[str, Any]] = []
    big: list[dict[str, Any]] = []
    checked = 0
    biggest = [0, 0]
    longest = [0, 0]
    one = mpz(1)
    for m in range(first, limit, 2):
        v = mpz(m)
        k, o, tau, peak = 0, 0, None, 0
        pow3 = one
        letters: list[int] = []
        while v >= m:
            bit = int(v & 1)
            letters.append(bit)
            if bit:
                o += 1
                pow3 *= 3
                v = gmp_isqrt(v * v * v)
            else:
                v = gmp_isqrt(v)
            k += 1
            if tau is None and pow3 < (one << k):
                tau = k
            b = v.bit_length()
            if b > peak:
                peak = b
        checked += 1
        if tau != k:
            early.append({"m": m, "dropping_time": k, "tau": tau, "word": "".join("O" if x else "E" for x in letters)})
        if peak > biggest[0]:
            biggest[:] = [peak, m]
        if k > longest[0]:
            longest[:] = [k, m]
        if peak > cap_bits:
            big.append({"m": m, "dropping_time": k, "tau": tau, "odd_letters": o, "digits": int(peak * 0.30103)})
    return {
        "backend": "gmpy2 (GMP): the dropping-time check only, loss accounting not measured",
        "start": first,
        "limit": limit,
        "odd_starts": checked,
        "seconds": round(time.time() - t0, 1),
        "early_drops": early,
        "identity_violations": None,
        "capped_then_run_uncapped": big,
        "largest_excursion_bits_m": biggest,
        "longest_dropping_time_m": longest,
        "smallest_retained_fraction": [],
        "largest_loss_ratio": [],
        "near_drops_total": 0,
        "near_drop_shortfall_units_histogram": [0] * 11,
        "largest_near_drop_shortfall": [],
    }


def convergents_log2_3(q_max: int) -> list[dict[str, Any]]:
    """Convergents `p/q` of `log2 3` with `q` up to the first past `q_max`.

    `dist` is `||q log2 3||`; `above` says `3^q > 2^p`, the side on which a word can end
    with a tiny slack `(1 - 2^{-f_O}) ln m`.
    """
    expansion = partial_quotients_past(_log2_3, q_max)
    if not expansion.complete:
        raise ArithmeticError(expansion.reason or "Partial quotients of log2 3 not certified")
    a = list(expansion.quotients)
    fractions = convergents(a)
    rows = []
    # |q alpha - p| ~ 1/q: 2 log2(q) bits cancel, and 96 more leave the double exact.
    with ctx.workprec(2 * fractions[-1][1].bit_length() + 96):
        alpha = _log2_3()
        for n, (p, q) in enumerate(fractions):
            signed = q * alpha - p
            if not (signed > 0 or signed < 0):
                raise ArithmeticError(f"Side of convergent {p}/{q} not certified")
            rows.append({"q": q, "p": p, "a": a[n], "dist": float(abs(signed)), "above": bool(signed > 0)})
    return rows


def _log2_3() -> arb:
    return arb(3).log() / arb(2).log()


def delta(O: int, conv: list[dict[str, Any]]) -> float:
    """`min_{1 <= o <= O} ||o log2 3||`, attained at the largest convergent denominator `<= O`."""
    best = None
    for row in conv:
        if row["q"] <= O:
            best = row["dist"]
    if best is None:
        raise ValueError("O must be at least 1")
    return best


def o_min(m: int, conv: list[dict[str, Any]]) -> int | None:
    """The least `O` compatible with the crude bound `2 O / m > (1 - 2^{-delta(O)}) ln m`.

    None means every admissible `O` lies past the last convergent supplied.
    """
    lnm = big_log(m)
    best = None
    for n in range(len(conv) - 1):
        qn, qn1, dist = conv[n]["q"], conv[n + 1]["q"], conv[n]["dist"]
        need = (m * lnm / 2.0) * (1.0 - 2.0 ** (-dist))
        lo = max(qn, int(need) + 1)
        if lo < qn1 and (best is None or lo < best):
            best = lo
    return best


def rhin_delta_lower_bound(O: int) -> float:
    """`delta(O) >= (2 O)^{-13.3} / ln 2` from Rhin's `|Lambda| >= H^{-13.3}`, `H = p <= 2 O`."""
    return (2.0 * O) ** (-13.3) / LN2


def frac_parts_log2_3(o_max: int) -> list[float]:
    """`f_o = {o log2 3}` for `o = 0..o_max`, exact to far below double precision.

    `log2 3` is taken to 50 digits as `P / 10^50`; the fractional part of `o P / 10^50`
    is then integer arithmetic, with an error below `o / 10^50`.
    """
    mp.dps = 70
    scale = 10**50
    p = int(mpfloor(mplog(3) / mplog(2) * scale))
    return [((o * p) % scale) / scale for o in range(o_max + 1)]


def refined_scan(m: int, o_max: int, fracs: list[float]) -> dict[str, Any]:
    """The refined bound at `m` for `O = 1..o_max`: which `O` are still admissible.

    Admissible means `(1 - 2^{-f_O}) ln m <= (1 + 2/m) (sum_{o<O} (2/m)^{2^{f_o}} + 2/m^2)`,
    checked only while the bootstrap `2 O / m <= ln 2` holds. Returns the least admissible
    `O`, their count, the first few, and the largest `O` the bootstrap allows.
    """
    lnm = big_log(m)
    two_over_m = 2.0 / m
    running = 0.0
    least = None
    admissible: list[int] = []
    count = 0
    bootstrap_max = int(m * LN2 / 2.0)
    top = min(o_max, bootstrap_max)
    for O in range(1, top + 1):
        rhs = (1.0 + two_over_m) * (running + 2.0 / (m * m))
        lhs = -expm1(-fracs[O] * LN2) * lnm  # (1 - 2^{-f_O}) ln m
        if lhs <= rhs:
            count += 1
            if least is None:
                least = O
            if len(admissible) < 12:
                admissible.append(O)
        running += two_over_m ** (2.0 ** fracs[O])
    return {
        "m": m,
        "o_max_scanned": top,
        "bootstrap_max": bootstrap_max,
        "least_admissible": least,
        "admissible_count": count,
        "first_admissible": admissible,
    }


def run(limit: int = 1_000_000, q_max: int = 10**13, refined_o_max: int = 300_000) -> dict[str, Any]:
    conv = convergents_log2_3(q_max)
    table = {}
    for e in range(4, 25, 2):
        table[f"1e{e}"] = o_min(10**e, conv)
    fracs = frac_parts_log2_3(refined_o_max)
    refined = {}
    for e in (6, 7, 8, 10, 12):
        refined[f"1e{e}"] = refined_scan(10**e, refined_o_max, fracs)
    return {
        "study": study(limit),
        "convergents": conv,
        "o_min": table,
        "refined": refined,
        "rhin_tail_example": {"O": 10**13, "delta_lower_bound": rhin_delta_lower_bound(10**13)},
    }


def render_markdown(data: dict[str, Any]) -> str:
    s = data["study"]
    lines = [
        "# The Juggler drop is the first contracting length, as far as loss accounting reaches",
        "",
        "Generated by `python -m research.juggler_sequence.drop_first_contracting_length`.",
        "",
        "## The theorem",
        "",
        "- exact identity: `d_{i+1} = p_i d_i + eta_i`, `0 <= eta_i < ln(1 + 1/x_{i+1})`, so `d_k <= rho_k sum_{j<=k} ln(1+1/x_j)/rho_j`",
        "- drop criterion: an uncertified drop at `k` forces `sum_{j<k} 1/(rho_j x_j) >= (1 - 1/rho_k) ln m`",
        "- crude excursion bound: with `O` odd letters it forces `2 O / m > (1 - 2^{-delta(O)}) ln m`, `delta(O) = min_{o<=O} ||o log2 3||`",
        "- refined excursion bound (`2 O / m <= ln 2`): it forces `(1 - 2^{-f_O}) ln m <= (1 + 2/m)(sum_{o<O} (2/m)^{2^{f_o}} + 2/m^2)`, `f_o = {o log2 3}`",
        "",
        "## The computation",
        "",
        f"- odd starts in `[{s['start']}, {s['limit']})`: `{s['odd_starts']}`, `{s['seconds']}` s; early drops: `{s['early_drops']}`",
        f"- numerical failures of the identity `d_i <= rho_i S_i`: `{s['identity_violations']}`",
        f"- starts past the 400000-digit cap, run without it (m, drop, tau, O, digits): `{[(u['m'], u['dropping_time'], u['tau'], u['odd_letters'], u['digits']) for u in s['capped_then_run_uncapped']]}`",
        f"- largest excursion: `{int(s['largest_excursion_bits_m'][0] * 0.30103)}` digits at `m = {s['largest_excursion_bits_m'][1]}`; longest dropping time `{s['longest_dropping_time_m'][0]}` at `m = {s['longest_dropping_time_m'][1]}`",
        f"- smallest retained fraction of the ideal margin (fraction, m, step, drop, O): `{[(round(r[0], 4), *r[1:]) for r in s['smallest_retained_fraction'][:6]]}`",
        f"- largest loss-accounting bound over slack (ratio, m, step, drop, O): `{[(round(r[0], 4), *r[1:]) for r in s['largest_loss_ratio'][:6]]}`",
        f"- near-drops (even steps landing with `1 < rho < 2`): `{s['near_drops_total']}`; shortfall below the ideal in units, histogram by unit up to 10+: `{s['near_drop_shortfall_units_histogram']}`",
        f"- largest near-drop shortfall (units, relative, m, step, O): `{[(round(r[0], 2), round(r[1], 6), *r[2:]) for r in s['largest_near_drop_shortfall'][:6]]}`",
        "",
        "## The near misses of `log2 3`",
        "",
        "Convergent denominators on the dangerous side, `3^q > 2^p`:",
        "",
    ]
    for row in data["convergents"]:
        if row["above"] and row["q"] > 1:
            lines.append(f"- `q = {row['q']}`, `p = {row['p']}`, `||q log2 3|| = {row['dist']:.3e}`")
    lines += [
        "",
        "## The least excursion an uncertified drop would need",
        "",
        "Crude bound (`x_i >= m` only), odd letters `O_min(m)`; `None` means past the last convergent supplied:",
        "",
    ]
    for key, val in data["o_min"].items():
        lines.append(f"- `m = {key}`: `O >= {val}`")
    lines += ["", "Refined bound, scanned to `O = {}`; the least admissible `O`, how many are admissible in the scan, the first few:".format(
        max(r["o_max_scanned"] for r in data["refined"].values())), ""]
    for key, r in data["refined"].items():
        lines.append(
            f"- `m = {key}`: least `O = {r['least_admissible']}`, admissible count `{r['admissible_count']}` of `{r['o_max_scanned']}`, first `{r['first_admissible']}`"
        )
    lines += [
        "",
        "## What is not proved",
        "",
        "- the equality for all `m`: it needs an excursion of `O_min(m)` odd letters ending at a dangerous denominator with the losses aligned; nothing bounds the excursion, and the situation mirrors Terras's Conjecture 2.9",
        "",
    ]
    return "\n".join(lines)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--limit", type=int, default=1_000_000)
    parser.add_argument("--start", type=int, default=None, help="chunk mode: sweep [start, limit) and write only its JSON")
    parser.add_argument(
        "--backend",
        choices=("python", "gmp"),
        default="python",
        help="chunk mode only: python integers with the loss accounting, or gmpy2 for the dropping-time check alone",
    )
    parser.add_argument("--q-max", type=int, default=10**13)
    parser.add_argument("--refined-o-max", type=int, default=300_000)
    args = parser.parse_args()
    DATA_DIR.mkdir(parents=True, exist_ok=True)
    if args.start is not None:
        data = gmp_sweep(args.limit, start=args.start) if args.backend == "gmp" else study(args.limit, start=args.start)
        path = DATA_DIR / f"sweep_{args.start}_{args.limit}.json"
        path.write_text(json.dumps(data, indent=1) + "\n", encoding="utf-8")
        print(
            f"chunk [{data['start']}, {data['limit']}) on {args.backend}: {data['odd_starts']} starts, early drops {len(data['early_drops'])}, "
            f"identity violations {data['identity_violations']}, past the cap {len(data['capped_then_run_uncapped'])}, {data['seconds']} s"
        )
        return
    data = run(args.limit, args.q_max, args.refined_o_max)
    JSON_PATH.write_text(json.dumps(data, indent=1) + "\n", encoding="utf-8")
    DOC_PATH.write_text(render_markdown(data), encoding="utf-8")
    s = data["study"]
    refined_least = {k: v["least_admissible"] for k, v in data["refined"].items()}
    print(
        f"odd starts below {s['limit']}: {s['odd_starts']}, early drops {len(s['early_drops'])}, "
        f"identity violations {s['identity_violations']}, {s['seconds']} s; o_min: {data['o_min']}; "
        f"refined least: {refined_least}"
    )


if __name__ == "__main__":
    main()
