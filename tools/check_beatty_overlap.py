"""Bounded Arb audit of Gamma-density interval overlaps.

Finite-profile energies are certified finite expressions, not estimates with
an unproved infinite-tail rate. Separate bounds enclose the true first N
intervals using the established positive total-mass identity. Neither bounds
the energy of all infinitely many intervals.
"""
from __future__ import annotations

import argparse
from fractions import Fraction
import hashlib
import json
import math
from pathlib import Path
import sys

import flint
from flint import arb, ctx

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "src"))

from arb_paper_audit_core.beatty import exact_survivor_counts
from research.experiments.provenance import write_manifest
from research_engine.intervals import ball, bounds, enclosure


def sweep_energy(intervals: list[tuple[arb, arb]], a: arb) -> dict:
    """Integrate multiplicity squared and density powers on certified cells."""
    if not intervals or not a > 0 or any(not (0 < lo < hi) for lo, hi in intervals):
        raise ArithmeticError("Need a positive scale and nonempty certified positive intervals")
    events = [(lo, 1) for lo, _ in intervals] + [(hi, -1) for _, hi in intervals]
    # Floats propose an order only; every comparison is subsequently certified.
    events.sort(key=lambda row: float(row[0]))
    previous = events[0][0]
    multiplicity = peak = 0
    energy, square, endpoint = arb(0), arb(0), arb(0)
    for index, (y, change) in enumerate(events):
        if index and not y > previous:
            raise ArithmeticError("Finite-profile event order is unresolved")
        energy += multiplicity**2 * (y-previous)
        square += (multiplicity/a)**2 * (1/previous-1/y)
        endpoint += (arb(multiplicity)/a)**ball("3/2") * 2 * (
            1/previous.sqrt()-1/y.sqrt())
        multiplicity += change
        peak = max(peak, multiplicity)
        previous = y
    if multiplicity != 0:
        raise ArithmeticError("Unbalanced interval sweep")
    return {"multiplicity_square_integral": enclosure(energy),
            "density_square_integral": enclosure(square),
            "density_three_halves_integral": enclosure(endpoint),
            "maximum_multiplicity": peak}


def overlap_bounds(boxes: list[tuple[int, int, int, int, int, int]],
                   scale: int) -> dict:
    """Enclose the whole ordered pair sum using exact integer endpoint boxes.

Each row is (Llo,Lhi,Ulo,Uhi,widthlo,widthhi), on a common exact grid.
Width bounds are retained separately: uncertainty in position does not
increase the length of an interval. Diagonal terms use these widths.
"""
    low = sum(row[4] for row in boxes)
    high = sum(row[5] for row in boxes)
    for i, (llo, lhi, ulo, uhi, wlo, whi) in enumerate(boxes):
        for j in range(i):
            jl, jlh, ju, juh, jw, jwh = boxes[j]
            low += 2 * max(0, min(wlo, jw, ulo-jlh, ju-lhi))
            high += 2 * max(0, min(whi, jwh, uhi-jl, juh-llo))
    return {"lower": str(Fraction(low, scale)),
            "upper": str(Fraction(high, scale))}


def compute(orders: int, bits: int = 256) -> dict:
    """Compute dyadic finite-profile models and enclose their true heads."""
    if not 16 <= orders <= 8192 or orders & (orders-1) or bits < 192:
        raise ValueError("Require a power-of-two order count 16..8192 and bits >= 192")
    depth = (3**orders).bit_length()
    counts = exact_survivor_counts(depth)
    digest = hashlib.sha256()
    for count in counts:
        digest.update((hex(count)+"\n").encode("ascii"))
    with ctx.workprec(bits):
        alpha = arb(3).log()/arb(2).log()
        beta = 1/alpha
        q, a = 1-beta, -(1-beta).log()
        atoms, power = [], 3
        for r in range(1, orders+1):
            m = power.bit_length()-1
            c = 2*counts[m]-counts[m+1]
            phase = r*alpha-m
            weight = arb(c)*beta**r*q**(m-r)
            if not (0 < phase < 1 and weight > 0):
                raise ArithmeticError("Unresolved atom sign")
            atoms.append((phase, weight, q**phase))
            power *= 3
        cutoffs = [2**k for k in range(4, orders.bit_length())]
        rows = []
        for cutoff in cutoffs:
            ordered = sorted(range(cutoff), key=lambda i: float(atoms[i][0]))
            height, previous = arb(1), arb(0)
            intervals = [None]*cutoff
            for i in ordered:
                phase, weight, tilt = atoms[i]
                if not phase > previous:
                    raise ArithmeticError("Phase ordering is unresolved")
                intervals[i] = (tilt*height, tilt*(height+weight))
                height += weight
                previous = phase
            tail = 1/q-height
            if not tail > 0:
                raise ArithmeticError("Remaining total mass sign is unresolved")
            energies = []
            # Compare identical chronological heads at several profile cutoffs.
            for head in cutoffs:
                if head > cutoff:
                    break
                item = {"head_orders": head, **sweep_energy(intervals[:head], a)}
                block = sweep_energy(intervals[head//2:head], a)
                block_mass = sum((hi-lo for lo, hi in intervals[head//2:head]), arb(0))
                block["interval_length_sum"] = enclosure(block_mass)
                item["last_dyadic_block"] = block
                if cutoff == orders:
                    scale = 2**80
                    boxes = []
                    for i, (lo, hi) in enumerate(intervals[:head]):
                        shift = atoms[i][2]*tail
                        width = atoms[i][2]*atoms[i][1]
                        boxes.append((
                            math.floor(bounds(lo)[0]*scale),
                            math.ceil(bounds(lo+shift)[1]*scale),
                            math.floor(bounds(hi)[0]*scale),
                            math.ceil(bounds(hi+shift)[1]*scale),
                            max(0, math.floor(bounds(width)[0]*scale)),
                            math.ceil(bounds(width)[1]*scale)))
                    item["true_head_overlap_energy"] = overlap_bounds(boxes, scale)
                    item["true_last_dyadic_block_energy"] = overlap_bounds(boxes[head//2:], scale)
                energies.append(item)
            rows.append({"profile_orders": cutoff, "remaining_mass": enclosure(tail),
                         "heads": energies})
        return {
            "scope": "Certified finite-profile integrals and enclosures of true finite-head "
                     "overlap energies. No bound on the infinite overlap sum; no L2 or "
                     "endpoint integrability theorem is established by this computation.",
            "orders": orders, "exact_count_depth": depth, "precision_bits": bits,
            "endpoint_grid_denominator": str(2**80),
            "counts_sha256_hex_lines": digest.hexdigest(), "models": rows,
            "true_head_bound": "For r<=M, L_r=L_(r,M)+q^delta_r t_r and "
                "U_r=U_(r,M)+q^delta_r t_r with 0<=t_r<=T_M. For two intervals "
                "their overlap is max(0,min(width_i,width_j,U_i-L_j,U_j-L_i)). "
                "Outward endpoint/width boxes enclose this expression; diagonal widths "
                "and twice every unordered pair give the ordered energy sum.",
        }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--orders", type=int, default=4096)
    parser.add_argument("--bits", type=int, default=256)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    result = compute(args.orders, args.bits)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2)+"\n", encoding="utf-8", newline="\n")
    write_manifest(args.output.with_suffix(".research.json"), programme="juggler",
                   research_id="juggler/winkler_phase_collapse", scope=result["scope"],
                   parameters={"orders": args.orders, "precision_bits": args.bits,
                               "python_flint": flint.__version__},
                   outputs=[args.output],
                   sources=[Path(__file__), ROOT / "tools/arb_paper_audit_core/beatty.py",
                            ROOT / "src/research_engine/intervals.py"],
                   command=["python", "tools/check_beatty_overlap.py", *sys.argv[1:]],
                   artifact_root=args.output.parent)
    print(json.dumps({"orders": args.orders, "output": str(args.output),
                      "finite_model_density_square": result["models"][-1]["heads"][-1]
                      ["density_square_integral"]["display"],
                      "scope": result["scope"]}, indent=2))


if __name__ == "__main__":
    main()
