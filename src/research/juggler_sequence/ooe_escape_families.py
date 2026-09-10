"""Exact bounded OOE controls and fixed residue-family replays.

The finite checks do not prove the quantified family theorem or decide escape.
"""
from __future__ import annotations

import argparse
import json
from collections import Counter
from math import isqrt
from research.juggler_sequence.lean_paths import DATA_ROOT

START_MIN, START_MAX = 5, 20001
RETURN_CAP = 20
FAMILY_PARAMETERS = tuple(range(3, 32, 2))
FAMILY_RETURN_CAP = 12
OFFSETS = (-1, 1, -9)
RESIDUE_MODULI = (2, 6, 16, 48, 64)
RESIDUE_MULTIPLIERS = (1, 3)


def valuation(n):
    n = abs(n)
    return None if n == 0 else (n & -n).bit_length()-1


def validate(x):
    if x % 2 == 0:
        return dict(valid=False, reason='source_even', x=x)
    h = isqrt(x**3)
    if h % 2 == 0:
        return dict(valid=False, reason='second_O_source_even', x=x, h=h)
    p = isqrt(h**3)
    if p % 2:
        return dict(valid=False, reason='E_source_odd', x=x, h=h, p=p)
    z = isqrt(p)
    if z % 2 == 0:
        return dict(valid=False, reason='return_endpoint_even', x=x, h=h, p=p, z=z)
    return dict(valid=True, x=x, h=h, p=p, z=z)


def family_parameter(x):
    if x < 3**8+8:
        return None
    r = isqrt(isqrt(isqrt(x-8)))
    return r if r % 2 and r**8+8 == x else None


def follow(start, cap):
    x = start
    blocks = []
    for _ in range(cap):
        block = validate(x)
        if not block['valid']:
            return dict(start=start, validated_returns=len(blocks), blocks=blocks,
                        stop=block, return_cap=cap, cap_hit=False)
        blocks.append(block)
        x = block['z']
    return dict(start=start, validated_returns=len(blocks), blocks=blocks,
                stop=dict(reason='validated_return_cap', x=x),
                return_cap=cap, cap_hit=True)


def residue_counterexample(modulus: int, oddresidue: int, multiplier: int) -> dict:
    """Replay one exact odd source in a residue class whose first O image is even."""
    if any(not isinstance(value, int) or isinstance(value, bool)
           for value in (modulus, oddresidue, multiplier)):
        raise ValueError("modulus, oddresidue and multiplier must be integers")
    q, a, k = modulus, oddresidue, multiplier
    if q <= 0 or q % 2:
        raise ValueError("modulus must be positive and even")
    if not 0 < a < q or a % 2 == 0:
        raise ValueError("oddresidue must be odd and strictly between zero and modulus")
    if k < 1:
        raise ValueError("multiplier must be positive")
    t = 2*q*k
    x = t**8+a
    u = t**12+3*a*(t**4//2)
    lower = x**3-u*u
    upper = (u+1)**2-x**3
    assert lower == 3*a*a*(t**8//4)+a**3 > 0
    assert upper > 0 and isqrt(x**3) == u
    assert t >= 4 and 2*a < t and x % q == a
    assert x % 2 == 1 and u % 2 == 0
    return {
        "modulus": q, "oddresidue": a, "multiplier": k, "t": t,
        "source": x, "first_O_output": u,
        "O_lower_margin": lower, "O_upper_margin": upper,
        "source_residue": x % q, "source_odd": True,
        "first_O_output_even": True, "second_O_guard": False,
        "parameter_bounds": {"t_at_least_four": t >= 4, "twice_residue_below_t": 2*a < t},
        "actual_OOE_return_asserted": False,
        "periodic_orbit_asserted": False,
    }


def report() -> dict:
    """Return the fixed report without writing files or changing global state."""
    directions = {str(k): Counter() for k in OFFSETS}
    examples = {str(k): {d: [] for d in ('increase','equal','decrease')}
                for k in OFFSETS}
    stop_counts, length_counts = Counter(), Counter()
    unique_edges = set()
    longest = []
    total = 0
    for start in range(START_MIN, START_MAX+1, 2):
        trace = follow(start, RETURN_CAP)
        n = trace['validated_returns']
        stop_counts[trace['stop']['reason']] += 1
        length_counts[n] += 1
        if not longest or n > longest[0]['validated_returns']:
            longest = [trace]
        elif n == longest[0]['validated_returns'] and len(longest) < 8:
            longest.append(trace)
        for block in trace['blocks']:
            x, z = block['x'], block['z']
            total += 1
            unique_edges.add((x,z))
            for offset in OFFSETS:
                a, b = valuation(x+offset), valuation(z+offset)
                key = str(offset)
                if a is None or b is None:
                    directions[key]['skipped_zero'] += 1
                    continue
                direction = 'increase' if b>a else 'decrease' if b<a else 'equal'
                directions[key][direction] += 1
                if len(examples[key][direction]) < 4:
                    examples[key][direction].append(dict(**block, before=a, after=b))

    family = []
    for s in FAMILY_PARAMETERS:
        trace = follow(s**8+8, FAMILY_RETURN_CAP)
        assert trace['blocks'] and trace['blocks'][0]['z'] == s**9+9*s-1
        departure = None
        for j, block in enumerate(trace['blocks']):
            block['source_family_parameter'] = family_parameter(block['x'])
            block['endpoint_family_parameter'] = family_parameter(block['z'])
            if departure is None and block['endpoint_family_parameter'] is None:
                departure = j+1
        trace['parameter'] = s
        trace['departure_after_return'] = departure
        trace['validated_returns_after_departure'] = (
            None if departure is None else trace['validated_returns']-departure)
        family.append(trace)

    result = dict(
        scope='validated actual OOE returns with odd endpoint; no generic trajectory or escape claim',
        ordinary=dict(start_interval=[START_MIN,START_MAX], odd_starts=9999,
                      return_cap=RETURN_CAP, block_observations=total,
                      distinct_observed_edges=len(unique_edges),
                      length_counts={str(k): v for k, v in sorted(length_counts.items())},
                      cap_hits=stop_counts.get("validated_return_cap", 0),
                      stop_counts=dict(stop_counts), valuation_directions={k: dict(v) for k, v in directions.items()},
                      valuation_examples=examples, longest_traces=longest),
        family=dict(parameters=list(FAMILY_PARAMETERS), total_return_cap=FAMILY_RETURN_CAP,
                    explanation='cap includes the first known family block; no more than eleven post-departure blocks',
                    controls=family))
    result["residue_fixtures"] = [
        residue_counterexample(q, a, k)
        for q in RESIDUE_MODULI
        for a in sorted({1, q-1})
        for k in RESIDUE_MULTIPLIERS
    ]
    result["scope_flags"] = {
        "bounded_return_search": True,
        "generic_orbit_search": False,
        "escape_proved": False,
        "no_cycle_proved": False,
        "raised_floor": False,
        "finite_tests_prove_uniform_theorem": False,
    }
    return result


def main(argv: list[str] | None = None) -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--write", action="store_true", help="write the fixed canonical control record")
    args = parser.parse_args(argv)
    data = report()
    if args.write:
        destination = DATA_ROOT / "ooe_escape_families" / "controls.json"
        destination.parent.mkdir(parents=True, exist_ok=True)
        destination.write_text(json.dumps(data, indent=2)+"\n", encoding="utf-8")
    print(json.dumps({
        "odd_starts": data["ordinary"]["odd_starts"],
        "validated_block_observations": data["ordinary"]["block_observations"],
        "longest_validated_chain": data["ordinary"]["longest_traces"][0]["validated_returns"],
        "ordinary_cap_hits": data["ordinary"]["cap_hits"],
        "family_controls": len(data["family"]["controls"]),
        "residue_fixtures": len(data["residue_fixtures"]),
        "record_written": args.write,
        "escape_proved": False,
    }))


if __name__ == "__main__":
    main()
