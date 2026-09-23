"""Paper A's rational screening and Arb replacement of its interval comparisons."""
from fractions import Fraction as F
from math import isqrt

from arb_paper_audit_core.client import Bounds, constants

DENOMINATORS = [1, 2, 3, 8, 19, 65, 84, 485, 1054, 24727, 50508, 125743, 176251, 301994]
FLOORS = [(10**6, 25781), (26254995, 176251), (162849448, 478245), (350000000, 780239)]


def continued_fraction_denominators(interval, maximum):
    lo, hi = interval.lo, interval.hi
    q0, q1, found = 1, 0, []
    while True:
        ai = lo.numerator // lo.denominator
        if ai != hi.numerator // hi.denominator:
            raise ArithmeticError("Continued-fraction digit unresolved")
        q0, q1 = q1, ai*q1+q0
        if q1 > maximum:
            return sorted(set(found))
        found.append(q1)
        lo, hi = 1/(hi-ai), 1/(lo-ai)


def digit_sum(n):
    total = 0
    for q in reversed(DENOMINATORS):
        b, n = divmod(n, q)
        total += b
    assert n == 0
    return total


def floor_fraction(x):
    return x.numerator // x.denominator


def positive_difference(x, y):
    if x.lo > y.hi:
        return True
    if x.hi < y.lo:
        return False
    raise ArithmeticError("Comparison unresolved; do not infer a failed exclusion")


async def paper_a(a):
    c = await constants(a)
    if continued_fraction_denominators(c["beta"], DENOMINATORS[-1]) != DENOMINATORS:
        raise ArithmeticError("Paper A denominator list disagrees with certified logarithms")
    scale = 10**50
    l2, h2 = floor_fraction(c["ln2"].lo*scale), -floor_fraction(-c["ln2"].hi*scale)
    l3, h3 = floor_fraction(c["ln3"].lo*scale), -floor_fraction(-c["ln3"].hi*scale)
    reports = []
    for N, cap in FLOORS:
        n = N+1
        ln = await a.evaluate(f"log_floor_{N}", f"log({n})")
        ln_lower = floor_fraction(ln.lo*scale)
        crude, parity, walk, alive, details = 0, 0, 0, [], []
        for L in range(1, cap+1):
            o = L*l2//h3+1
            if o != L*h2//l3+1:
                raise ArithmeticError(f"Unresolved odd count at L={L}")
            lam = o*l3-L*h2
            if lam <= 0:
                raise ArithmeticError(f"Unresolved expanding surplus at L={L}")
            if n*ln_lower*lam > L*scale*(scale+lam):
                crude += 1
                continue
            key = f"floor_{N}_L_{L}"
            variables = {"n": str(n), "o": str(o), "e": str(L-o),
                         "L": str(L), "t": str(isqrt(n**3))}
            theta = await a.evaluate(key+"_theta", "1-exp(L*log(2)-o*log(3))", variables)
            parity_bound = await a.evaluate(key+"_parity",
                "(6/5)*(e/(n*log(n))+(o-e)/(t*log(t))+e/(2*n**2*log(n)))", variables)
            if positive_difference(theta, parity_bound):
                parity += 1
                continue
            nu = await a.evaluate(key+"_nu", "log(n)-(21/20)*e/n-(7/10)*o/(n*sqrt(n))", variables)
            if nu.lo <= 0:
                raise ArithmeticError("Walk bound requires positive nu")
            walk_variables = {"v": nu.box(), "L": str(L), "s": str(digit_sum(L))}
            walk_bound = await a.evaluate(key+"_walk",
                "(6/5)*L/(exp(v)*v)*((1-2/v+6/v**2-24/v**3+120/v**4)/(log(3)*v)+2*s/L)",
                walk_variables)
            excludes = positive_difference(theta, walk_bound)
            if excludes:
                walk += 1
            else:
                alive.append(L)
            details.append({"length": L, "odd_count": o, "digit_sum": digit_sum(L),
                            "walk_excludes": excludes, "theta": theta.as_dict(),
                            "walk_bound": walk_bound.as_dict()})
        if alive != [cap]:
            raise ArithmeticError(f"Paper A frontier changed at floor {N}: {alive}")
        reports.append({"assumed_floor": N, "lengths_checked": cap, "crude_exclusions": crude,
                        "parity_exclusions": parity, "walk_exclusions": walk,
                        "not_excluded": alive, "walk_rows": details})
        print(f"A: floor {N}, first surviving length {cap}", flush=True)
    lam = await a.evaluate("upper_cell_lambda", "492276*log(3)-780239*log(2)")

    async def excludes(m):
        value = await a.evaluate(f"upper_cell_A_{m}", "log(m)*exp(-(1-1/780239)*lam)",
                                 {"m": str(m), "lam": lam.box()})
        charge = await a.evaluate(f"upper_cell_charge_{m}",
                                 "exp(-v)/v*(1+780239/(log(3)*(v+1)))", {"v": value.box()})
        return positive_difference(lam, charge)

    low, high = 350000000, 520000000
    if await excludes(low) or not await excludes(high):
        raise ArithmeticError("Upper-cell search endpoints do not straddle the cutoff")
    while high-low > 1:
        mid = (low+high)//2
        if await excludes(mid):
            high = mid
        else:
            low = mid
    return {"floor_audits": reports, "certified_cf_denominators": DENOMINATORS,
            "upper_cell": {"counts": {"L":780239,"o":492276,"e":287963},
                           "least_integer_excluded_by_scalar_bound": high,
                           "previous_integer_not_excluded_by_scalar_bound": low,
                           "rounded_upper_minimum": ((high+999999)//1000000)*1000000,
                           "lambda": lam.as_dict()},
            "progress": "Independent enclosure audit of four period floors; a sharper cubic-band minimum cutoff from the same monotone upper-cell inequality.",
            "not_certified": "The descent-floor campaign is assumed, not rerun. No exclusion of period 780239 or of cycles outside the cubic-band hypothesis."}
