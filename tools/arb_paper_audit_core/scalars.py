"""Finite constants in Papers B, C and E, including rational growth headroom."""
from __future__ import annotations

import asyncio
from fractions import Fraction as F

from arb_paper_audit_core.client import Bounds, constants


async def paper_b(a):
    c = await constants(a)
    variables = {"p": c["beta"].box()}
    expressions = {
        "kl_sharp": "log(2)+p*log(p)+(1-p)*log(1-p)",
        "kl_convenient": "log(2)+((p+1/2)/2)*log((p+1/2)/2)+(1-(p+1/2)/2)*log(1-(p+1/2)/2)",
        "rho": "exp(-log(2)-p*log(p)-(1-p)*log(1-p))",
        "eta": "1+(p*log(p)+(1-p)*log(1-p))/log(2)",
        "oscillation_envelope": "1/(1-p)",
        "ladder_mean": "1/(log(p/(1-p))*sqrt(2*pi*p*(1-p)))",
        "first_jump": "1/(2*exp(-log(2)-p*log(p)-(1-p)*log(1-p))*sqrt(2*pi*p*(1-p)))",
    }
    rounded = {"kl_sharp": "0.0346881852", "kl_convenient": "0.0085959587",
               "rho": "0.9659065532", "eta": "0.0500444728",
               "oscillation_envelope": "2.7095112914", "ladder_mean": "1.541814521",
               "first_jump": "0.427956804"}
    results = {}
    for name, expression in expressions.items():
        value = await a.evaluate(name, expression, variables)
        printed = F(rounded[name])
        rounding = F(1, 2 * 10**len(rounded[name].split(".")[1]))
        results[name] = {"enclosure": value.as_dict(), "printed": rounded[name],
                         "rounding_agrees": printed-rounding <= value.lo <= value.hi <= printed+rounding}
    # A concrete conditional density instantiation, not a claim that FD is established.
    depths = {}
    for d in (100, 1000):
        expr = f"-log(2)+({d}-1)*(-log(2)-q*log(q)-(1-q)*log(1-q))"
        q = await a.evaluate(f"q_{d}", f"p-(1-p)/({d}-1)", variables)
        bound = await a.evaluate(f"log_density_{d}", expr, {"q": q.box()})
        depths[str(d)] = {"log_density_upper_bound": bound.as_dict(), "conditional_on": "FD at this depth"}
    return {"constants": results, "conditional_density_examples": depths,
            "progress": "Certified finite constants; 7/8, 127/128 and the open FD premise are unchanged."}


async def paper_c(a):
    models = (await a.call("models", "arb_paper_c_models", {}))["models"]
    roots = {}
    for name, terms in models.items():
        roots[name] = await a.call(f"root_{name}", "arb_production_root", {"terms": terms})
    await a.compare("OOEE_slack", "(1/2)**(5/8)+(33/100)*(3/4)**(5/8)+(11/100)*(9/16)**(5/8)", "1")
    # All earlier depths are covered by the existing canonical audit. Here certify both sides
    # of each reported boundary through MCP, without claiming this alone proves minimality.
    thresholds = {"Chernoff": {"1/2": 16, "11/20": 34, "3/5": 168, "31/50": 1135},
                  "Azuma": {"1/2": 16, "11/20": 34, "3/5": 175, "31/50": 1201}}
    for kind, table in thresholds.items():
        for q, depth in table.items():
            for C, holds in ((depth-1, False), (depth, True)):
                item = await a.call(f"{kind}_{q}_{C}", "arb_paper_c_rate",
                                    {"C": C, "q": q, "kind": kind, "exponent": "5/8"})
                if item["holds"] is not holds:
                    raise ArithmeticError("Paper C rate boundary changed")
    return {"roots": {k: v["root"] for k, v in roots.items()}, "rate_boundaries": thresholds,
            "progress": "Confirms sharper conditional constants already recorded by the Paper C audit.",
            "not_certified": "Production, cylinder, pressure hypotheses and global termination"}


async def paper_e(a):
    gamma = await a.evaluate("growth_exponent", "50*log(5059/5000)/log(2)")
    await a.compare("sharper_exponent", "50*log(5059/5000)/log(2)", "423/500")
    # Preserve an independent exact-integer certificate for the proposed rational exponent.
    integer_comparison = 5059**25000 > (2**423) * 5000**25000
    if not integer_comparison:
        raise ArithmeticError("Exact growth comparison failed")
    endpoint = F(5069, 5000)
    ceiling = await a.evaluate("published_ceiling_exponent", "50*log(5069/5000)/log(2)")
    await a.compare("fixed_grid_obstruction", "u**(-100)+(u**29+u**(-21))/3", "1", "<",
                    {"u": str(endpoint)})
    constants_to_check = {
        "fifth_derivative_lower": ("945/(4*sqrt(5))", "100", ">"),
        "fifth_derivative_upper": ("2835/(4*sqrt(2))", "600", "<"),
        "third_derivative_lower": ("45/(16*5**(3/4))", "1/2", ">"),
        "third_derivative_upper": ("45/(16*2**(3/4))", "2", "<"),
        "fifth_derivative_sum_constant": ("11*3600**(1/30)", "32", "<"),
    }
    for name, (left, right, relation) in constants_to_check.items():
        await a.compare(name, left, right, relation)
    return {"growth_exponent": gamma.as_dict(), "certified_rational_exponent": "423/500",
            "exact_integer_check": {"left": "5059^25000", "relation": ">",
                                    "right": "2^423 * 5000^25000", "holds": integer_comparison},
            "fixed_grid_ceiling_exponent": ceiling.as_dict(),
            "progress": "The existing growth certificate supports the stronger eventual lower exponent 423/500 = 0.846.",
            "proof_dependency": "Paper E Lemmas 5.3–5.4 and their positive fixed prefactor; "
                                "strict exponential advantage absorbs it exactly as in Theorem 5.1.",
            "not_certified": "No new certificate table, Lean exponent theorem, reciprocal-mass divergence or termination."}
