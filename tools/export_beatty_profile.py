"""Export certified Beatty profile data for the React companion without plotting.

Counts are exact integers; Arb encloses phases, weights, tail mass and gap cores.
Only display coordinates are rounded. No finite-depth convergence rate is inferred.
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
from research_engine.intervals import bounds, enclosure


def compute(depth: int, sample_count: int, bits: int) -> dict:
    """Return drawing coordinates with outward tail and gap certificates."""
    if not 64 <= depth <= 20000 or sample_count < 1 or bits < 192:
        raise ValueError("Require depth 64..20000, positive sample count and at least 192 bits")
    counts = exact_survivor_counts(depth)
    digest = hashlib.sha256()
    for count in counts:
        digest.update((hex(count) + "\n").encode("ascii"))
    # Check the reused integer recurrence against the stored independent audit.
    reference = json.loads((ROOT / "data/research/juggler/arb_paper_audit/beatty.json")
                           .read_text(encoding="utf-8"))["summary"]
    for n, value in enumerate(reference["exact_counts"][:len(counts)]):
        if counts[n] != int(value):
            raise ArithmeticError(f"Integer audit mismatch at depth {n}")
    with ctx.workprec(bits):
        alpha = arb(3).log() / arb(2).log()
        beta, q = 1 / alpha, 1 - 1 / alpha
        envelope = 1 / q
        rows, power, r = [], 3, 1
        while (m := power.bit_length() - 1) + 1 < len(counts):
            count = 2 * counts[m] - counts[m + 1]
            if count <= 0:
                raise ArithmeticError(f"Nonpositive crossing count at order {r}")
            phase = r * alpha - m
            weight = arb(count) * beta**r * q**(m-r)
            ratio = arb(r * count) / arb(math.comb(m-1, r-1))
            if not (phase > 0 and phase < 1 and weight > 0):
                raise ArithmeticError("Unresolved phase or weight sign")
            rows.append({"order": r, "phase_ball": phase, "weight_ball": weight,
                         "ratio_ball": ratio})
            power *= 3
            r += 1
        ordered = sorted(rows, key=lambda row: float(row["phase_ball"]))
        previous, height = arb(0), arb(1)
        for row in ordered:
            if not row["phase_ball"] > previous:
                raise ArithmeticError("Phase order is not certified")
            row["left_ball"] = height
            height += row["weight_ball"]
            previous = row["phase_ball"]
        tail = envelope - height
        if not tail > 0:
            raise ArithmeticError("Tail positivity is unresolved")
        tail_upper = bounds(tail)[1]
        # A decimal ceiling, certified from an outward rational endpoint.
        ceiling = math.ceil(tail_upper * 10**6)
        tail_decimal = f"{ceiling // 10**6}.{ceiling % 10**6:06d}"
        if not tail_upper < Fraction(tail_decimal):
            raise ArithmeticError("Strict printed tail bound is unresolved")
        cores = []
        for row in ordered:
            lo = bounds(row["left_ball"] + tail)[1]
            hi = bounds(row["left_ball"] + row["weight_ball"])[0]
            if lo < hi:
                cores.append({"order": row["order"], "lower": str(lo), "upper": str(hi)})
        drawing = [{"order": row["order"], "phase": float(row["phase_ball"]),
                    "weight": float(row["weight_ball"]), "left": float(row["left_ball"]),
                    "ratio": float(row["ratio_ball"])} for row in ordered]
        largest_width = max(bounds(row[key])[1] - bounds(row[key])[0]
                            for row in ordered
                            for key in ("phase_ball", "weight_ball", "left_ball", "ratio_ball"))
        if largest_width >= Fraction(1, 10**40):
            raise ArithmeticError("Insufficient precision for drawing coordinates")
        return {
            "scope": "Exact integer counts; Arb enclosures using the proved positive mass identity; "
                     "rounded display coordinates. Not a finite-depth asymptotic-error certificate.",
            "depth": depth, "orders": len(rows), "precision_bits": bits,
            "sample_orders": [max(1, len(rows)-sample_count+1), len(rows)],
            "counts_sha256_hex_lines": digest.hexdigest(),
            "reference_counts_checked": min(len(counts), len(reference["exact_counts"])),
            "envelope": enclosure(envelope), "tail": enclosure(tail),
            "tail_strict_decimal_upper": tail_decimal,
            "maximum_coordinate_enclosure_width": str(largest_width),
            "certified_deleted_cores": cores, "drawing": drawing,
            "gap_certificate": "F_M(delta_r)<=F(delta_r)<=F_M(delta_r)+T_M; hence "
                "(upper(F_M(delta_r)+T_M),lower(F_M(delta_r)+w_r)) is inside the true open gap "
                "whenever nonempty. Gray value-axis regions are unresolved, not identified with K.",
        }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--depth", type=int, default=8000)
    parser.add_argument("--sample-count", type=int, default=1000)
    parser.add_argument("--bits", type=int, default=256)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    try:
        data = compute(args.depth, args.sample_count, args.bits)
    except ValueError as exc:
        parser.error(str(exc))
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(data, indent=2) + "\n", encoding="utf-8", newline="\n")
    write_manifest(args.output.with_suffix(".research.json"), programme="juggler",
                   research_id="juggler/winkler_phase_collapse", scope=data["scope"],
                   outputs=[args.output],
                   parameters={"depth": args.depth, "sample_count": args.sample_count,
                               "precision_bits": args.bits, "python_flint": flint.__version__},
                   command=["python", "tools/export_beatty_profile.py", *sys.argv[1:]],
                   inputs=[ROOT / "data/research/juggler/arb_paper_audit/beatty.json"],
                   sources=[Path(__file__), ROOT / "tools/arb_paper_audit_core/beatty.py"],
                   artifact_root=args.output.parent)
    print(json.dumps({"orders": data["orders"], "output": str(args.output),
                      "tail_upper": data["tail_strict_decimal_upper"],
                      "certified_gap_cores": len(data["certified_deleted_cores"])}, indent=2))


if __name__ == "__main__":
    main()
