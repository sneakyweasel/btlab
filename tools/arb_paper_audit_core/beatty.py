"""A computable full-tail enclosure from the proved positive total-mass identity."""
from fractions import Fraction as F

from arb_paper_audit_core.client import Bounds, constants

ORDERS = 256


def exact_survivor_counts(depth):
    """Count words with 3**ones > 2**length at every nonempty prefix, using integers."""
    profile, counts = {0: 1}, [1]
    threshold, power3 = 0, 1
    for n in range(1, depth+1):
        while power3 <= 2**n:
            threshold += 1
            power3 *= 3
        following = {}
        for ones, count in profile.items():
            for child in (ones, ones+1):
                if child >= threshold:
                    following[child] = following.get(child, 0)+count
        profile = following
        counts.append(sum(profile.values()))
    return counts


def finite_profile_integral_parts(atoms):
    """Return positive interval widths and cumulative heights on all finite jump cells."""
    ordered = sorted(atoms, key=lambda row: row["phase"].lo)
    previous = Bounds(F(0), F(0))
    height = Bounds(F(1), F(1))
    parts = []
    for row in ordered:
        width = row["phase"]-previous
        if width.lo <= 0:
            raise ArithmeticError("The phase ordering is not certified")
        parts.append((width, height))
        previous = row["phase"]
        height = height+row["weight"]
    last = Bounds(F(1), F(1))-previous
    if last.lo <= 0:
        raise ArithmeticError("Final phase is not below one")
    parts.append((last, height))
    return parts


async def beatty(a):
    c = await constants(a)
    depth = (3**ORDERS).bit_length()
    counts = exact_survivor_counts(depth)
    total_mass = await a.evaluate("total_atomic_mass", "1/(d-1)", {"d": c["delta"].box()})
    atoms, mass = [], Bounds(F(0), F(0))
    for r in range(1, ORDERS+1):
        m = (3**r).bit_length()-1
        count = 2*counts[m]-counts[m+1]
        if count <= 0:
            raise ArithmeticError("Nonpositive first-passage count")
        phase = await a.evaluate(f"phase_{r}", f"{r}*d-{m}", {"d": c["delta"].box()})
        weight = await a.evaluate(f"weight_{r}", f"c*p**{r}*(1-p)**{m-r}",
                                  {"c": str(count), "p": c["beta"].box()})
        if phase.lo <= 0 or phase.hi >= 1 or weight.lo <= 0:
            raise ArithmeticError("Phase or weight sign unresolved")
        atoms.append({"order": r, "m": m, "count": str(count), "phase": phase, "weight": weight})
        mass = mass+weight
    tail = total_mass-mass
    if tail.lo <= 0:
        raise ArithmeticError("Tail positivity not established")
    # Positivity plus the proved mass identity gives 0<=F-F_R<=tail everywhere.
    # For x>=1, d(x**(2/3))/dx <= 2/3, so the integral's missing part is <=2*tail/3.
    integral = Bounds(F(0), F(0))
    for i, (width, height) in enumerate(finite_profile_integral_parts(atoms)):
        value = await a.evaluate(f"moment_cell_{i}", "h**(2/3)", {"h": height.box()})
        integral = integral+width*value
    full_moment = Bounds(integral.lo, integral.hi+F(2, 3)*tail.hi)
    prefactor = await a.evaluate("content_prefactor", "3*(p**2/(pi*(1-p)))**(1/3)",
                                {"p": c["beta"].box()})
    content = prefactor*full_moment
    return {"orders": ORDERS, "exact_counts_through_depth": depth,
            "exact_counts": [str(n) for n in counts],
            "atoms": [{**{k:v for k,v in row.items() if k not in ("phase", "weight")},
                       "phase": row["phase"].as_dict(), "weight": row["weight"].as_dict()} for row in atoms],
            "partial_mass": mass.as_dict(), "total_mass": total_mass.as_dict(),
            "certified_remaining_mass": tail.as_dict(),
            "uniform_profile_error_upper": str(tail.hi),
            "finite_head_moment": integral.as_dict(), "full_two_thirds_moment": full_moment.as_dict(),
            "minkowski_content": content.as_dict(),
            "proof": "The established identity sum w_r=1/(alpha-1) and positivity give the full tail by subtraction. Since F_R>=1 and 0<=F-F_R<=tail, 0<=F^(2/3)-F_R^(2/3)<=2*tail/3 pointwise. Integrate each finite jump cell and use the proved content formula.",
            "progress": "First explicit interval for the full profile's two-thirds moment and Minkowski content, with a certified entire omitted tail; no asymptotic tail estimate is guessed.",
            "not_certified": "No rate for finite-depth convergence or tube-volume convergence, no Hausdorff dimension improvement, no new Lean interval certificate."}
