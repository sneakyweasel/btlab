"""Paper D: certified ceilings, exhaustive rational-window enumeration and witnesses.

The floor-sum sieve widens a certified lower rational approximation to the
rotation. It can add candidates but cannot omit an admissible length.
Float calculations rank valley witnesses only; every accepted witness is Arb checked.
"""
from __future__ import annotations

from fractions import Fraction as F
import json
from pathlib import Path

from arb_paper_audit_core.client import Bounds, constants

ROOT = Path(__file__).resolve().parents[2]
FLOOR = 2**51


def floor_sum(n, modulus, a, b):
    """sum(floor((a*i+b)/modulus), i=0..n-1), for nonnegative integer inputs."""
    if min(n, a, b) < 0 or modulus <= 0:
        raise ValueError("Nonnegative inputs and positive modulus required")
    total = 0
    while True:
        qa, a = divmod(a, modulus)
        qb, b = divmod(b, modulus)
        total += n*(n-1)//2*qa + n*qb
        y = a*n+b
        if y < modulus:
            return total
        n, b = divmod(y, modulus)
        modulus, a = a, modulus


def upper_window_candidates(n, a, modulus, width):
    """All 1<=k<=n with (k*a mod modulus)>=modulus-width; exact and exhaustive."""
    if not 0 < width < modulus:
        raise ValueError("Window width must lie strictly between zero and the modulus")
    def count(k):
        return floor_sum(k+1, modulus, a, width)-floor_sum(k+1, modulus, a, 0)
    result = []
    def collect(lo, hi, before, through):
        if through == before:
            return
        if lo == hi:
            result.append(lo)
            return
        mid = (lo+hi)//2
        left_count = count(mid)
        collect(lo, mid, before, left_count)
        collect(mid+1, hi, left_count, through)
    if n > 0:
        collect(1, n, 0, count(n))
    return result


def below(x, y):
    if x.hi < y.lo:
        return True
    if x.lo > y.hi:
        return False
    raise ArithmeticError("Unresolved strict comparison")


async def paper_d(a):
    c = await constants(a)
    data = json.loads((ROOT / "data/research/juggler/negative_m_cycles/summary.json").read_text())
    saved = {row["m"]: row for row in data["tables"]["2^51"]["rows"]}
    towers, ceilings, changes = {}, {}, []
    for m in range(1, 63):
        tower = await a.evaluate(f"B_{m}", f"(d**{m}-1)/(d-1)", {"d": c["delta"].box()})
        towers[m] = tower
        variables = {"d": c["delta"].box(), "b": tower.box(), "m": str(m)}
        expression = "(K/d+(b-m)/(d-1))/b-13.3*log(K)/log(2)-log(2*m)/log(2)"
        K = saved[m]["K3_rhin_ceiling"]
        values = {}
        async def ceiling_sign(k):
            if k not in values:
                values[k] = await a.evaluate(f"ceiling_{m}_{k}", expression, {**variables, "K": str(k)})
            value = values[k]
            if value.lo > 0:
                return 1
            if value.hi < 0:
                return -1
            raise ArithmeticError("Ceiling sign unresolved")
        original = K
        for _ in range(100):
            if await ceiling_sign(K) < 0:
                K += 1
            elif await ceiling_sign(K-1) > 0:
                K -= 1
            else:
                break
        else:
            raise ArithmeticError("Stored ceiling is not locally repairable")
        await a.compare(f"ceiling_derivative_{m}", "1/(d*b)-13.3/(K*log(2))", "0",
                        variables={**variables, "K": str(K-1)})
        ceilings[m] = K
        if original != K:
            changes.append({"m": m, "stored": original, "certified": K})
    beta = await a.evaluate("sieve_rotation", "log(2)/log(3)", bits=512)
    scale = 2**256
    approx = (beta.lo*scale).__floor__()
    if approx != (beta.hi*scale).__floor__():
        raise ArithmeticError("256-bit rotation rational not certified")
    maximum = ceilings[62]-1
    eps = await a.evaluate("sieve_window", f"62/(({FLOOR}-1)*log(3))", bits=512)
    width = (eps.hi*scale).__ceil__() + maximum
    candidates = upper_window_candidates(maximum, approx, scale, width)
    lambdas = {}
    odds = {}
    for K in candidates:
        o = K*approx//scale+1
        lam = await a.evaluate(f"lambda_{K}", f"{o}*log(3)-{K}*log(2)")
        if lam.hi < 0:  # widening may straddle the following integer; it is not admissible
            continue
        if lam.lo <= 0 or lam.hi >= c["ln3"].lo:
            raise ArithmeticError("Odd count is not certified by 0 < Lambda < log(3)")
        odds[K], lambdas[K] = o, lam
    L0 = await a.evaluate("floor_log2", f"log({FLOOR}-1)/log(2)")
    rows = []
    for m in range(1, 63):
        threshold = Bounds(F(m, FLOOR-1), F(m, FLOOR-1))
        admissible = [K for K in candidates if K < ceilings[m] and K in lambdas
                      and below(lambdas[K], threshold)]
        witnesses, survivors = [], []
        for K in admissible:
            lam, o = lambdas[K], odds[K]
            variables = {"d": c["delta"].box(), "b": towers[m].box(), "m": str(m),
                         "K": str(K), "lam": lam.box()}
            chain = await a.evaluate(f"chain_margin_{m}_{K}",
                     "log(m/lam)/log(2)-(K/d+(b-m)/(d-1))/b", variables)
            if chain.hi < 0:
                witnesses.append({"K": K, "method": "chaining", "margin_bits": chain.as_dict()})
                continue
            if chain.lo <= 0:
                raise ArithmeticError("Chaining margin unresolved")
            # Rank candidate r values using floats; numerical ranking proves nothing.
            d = float(c["delta"].lo)
            def estimate(r):
                g = m-r-1
                bg = d*(d**g-1)/(d-1)
                t = (o+(bg-g)/(d-1))/(r+1+bg)
                return r/(FLOOR-1)+(m-r)*2.0**(-max(0, t))
            chosen = None
            branch_checks = []
            for r in sorted(range(m), key=estimate):
                if F(r, FLOOR-1) > lam.hi:
                    branch_checks.append({"r": r, "reason": "constant_part_exceeds_lambda"})
                    continue
                g = m-r-1
                bg = f"d*(d**{g}-1)/(d-1)"
                Tr = await a.evaluate(f"threshold_{m}_{K}_{r}",
                    f"(o+(({bg})-{g})/(d-1))/({r+1}+({bg}))",
                    {"d": c["delta"].box(), "o": str(o)})
                if Tr.hi < L0.lo:
                    branch_checks.append({"r": r, "reason": "threshold_below_floor"})
                    continue
                if Tr.lo <= L0.hi:
                    raise ArithmeticError("Valley threshold eligibility unresolved")
                # A rational threshold strictly below T_(r+1) yields R(T)<=r.
                t = min(F(128), F((Tr.lo*10**40).__floor__()-1, 10**40))
                if not L0.hi < t < Tr.lo:
                    raise ArithmeticError("No certified rational valley threshold")
                margin = await a.evaluate(f"valley_margin_{m}_{K}_{r}",
                    f"log(({r}/({FLOOR}-1)+{m-r}*2**(-T))/lam)/log(2)",
                    {"T": str(t), "lam": lam.box()})
                if margin.hi < 0:
                    chosen = {"K": K, "method": "valley", "r": r,
                              "rational_threshold": str(t), "threshold_enclosure": Tr.as_dict(),
                              "margin_bits": margin.as_dict()}
                    break
                # To call a candidate a survivor of the *optimized* test, check the
                # breakpoint itself, not only our slightly weaker rational threshold.
                exact_margin = await a.evaluate(f"valley_limit_{m}_{K}_{r}",
                    f"log(({r}/({FLOOR}-1)+{m-r}*2**(-T))/lam)/log(2)",
                    {"T": Tr.box(), "lam": lam.box()})
                if exact_margin.lo <= 0:
                    raise ArithmeticError("Optimized valley branch needs a stronger witness")
                branch_checks.append({"r": r, "reason": "positive_breakpoint_margin",
                                      "margin_bits": exact_margin.as_dict()})
            if chosen:
                witnesses.append(chosen)
            else:
                survivors.append({"K": K, "o": o, "chain_margin_bits": chain.as_dict(),
                                  "all_valley_branches": branch_checks})
        if len(admissible) != saved[m]["admissible_count"]:
            changes.append({"m": m, "stored_count": saved[m]["admissible_count"],
                            "certified_count": len(admissible)})
        rows.append({"m": m, "ceiling": ceilings[m], "admissible_count": len(admissible),
                     "witnesses": witnesses, "survivors": survivors})
        if m >= 53:
            print(f"D: m={m}, {len(admissible)} admissible, {len(survivors)} surviving", flush=True)
    if any(row["survivors"] for row in rows[:61]):
        raise ArithmeticError("Paper D exclusion through 61 failed")
    if [s["K"] for s in rows[61]["survivors"]] != [83130157078217]:
        raise ArithmeticError("Paper D m=62 frontier changed")
    killing = await a.evaluate("open_length_killing_floor", "log(62/lam+1)/log(2)",
                              {"lam": lambdas[83130157078217].box()})
    return {"floor_assumed": FLOOR, "ceilings": ceilings, "rows": rows,
            "sieve": {"scale": str(scale), "rotation_numerator": str(approx),
                      "window_width": str(width), "maximum_length": maximum,
                      "candidate_count": len(candidates), "candidates": candidates,
                      "completeness": "x is in [a/S,(a+1)/S]; E>=epsilon_upper*S+Kmax. Every true upper-window hit is in the widened rational window, exhaustively enumerated by floor sums."},
            "differences_from_recorded_table": changes, "m62_killing_floor_log2": killing.as_dict(),
            "progress": "Replaces point-value trust with interval-certified ceilings and exclusion witnesses for every admissible length through m=61; m=62 still survives the optimized tests.",
            "not_certified": "The 2^51 descent campaign and external Rhin theorem are inputs, not re-proved. Higher-floor tables are outside this run."}
