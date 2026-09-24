"""Render the Beatty profile, exact count samples and certified deleted-gap cores.

Integer barriers and counts are exact. Arb encloses the phases, weights and
entire omitted mass using the proved total-mass identity. Only the drawing
uses floating-point coordinates. No finite-depth convergence rate is inferred.
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
import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.collections import LineCollection
from matplotlib.lines import Line2D
from matplotlib.patches import Patch, Rectangle

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "src"))

from arb_paper_audit_core.beatty import exact_survivor_counts
from research.experiments.provenance import write_manifest
from research_engine.intervals import bounds, enclosure


def compute(depth: int, sample_count: int, bits: int) -> dict:
    """Return drawing coordinates with outward tail and gap certificates."""
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


def draw(data: dict, out: Path) -> list[Path]:
    """Produce vector PDF/SVG and a high-resolution PNG with identical content."""
    plt.rcParams.update({"font.family": "DejaVu Serif", "font.size": 10,
                         "mathtext.fontset": "dejavuserif", "axes.spines.top": False,
                         "axes.spines.right": False, "pdf.fonttype": 42, "svg.fonttype": "none"})
    teal, orange, red, gray = "#146F84", "#BB7127", "#B94B3E", "#E6E8EB"
    fig = plt.figure(figsize=(7.4, 5.2))
    grid = fig.add_gridspec(1, 2, width_ratios=[4.6, 1], left=.10, right=.98,
                           bottom=.28, top=.90, wspace=.25)
    ax = fig.add_subplot(grid[0, 0])
    value = fig.add_subplot(grid[0, 1], sharey=ax)
    rows = data["drawing"]
    phases = [0] + [row["phase"] for row in rows] + [1]
    levels = [row["left"] for row in rows] + [rows[-1]["left"] + rows[-1]["weight"]]
    tail = float(Fraction(data["tail"]["upper"]))
    envelope = float(Fraction(data["envelope"]["upper"]))
    ax.stairs([h+tail for h in levels], phases, baseline=levels, fill=True,
              facecolor=teal, alpha=.15, linewidth=0, zorder=1)
    ax.add_collection(LineCollection([[(a, y), (b, y)]
                                      for a, b, y in zip(phases, phases[1:], levels)],
                                     color=teal, linewidth=1.15, zorder=3))
    sample = [row for row in rows if row["order"] >= data["sample_orders"][0]]
    ax.scatter([row["phase"] for row in sample], [row["ratio"] for row in sample],
               s=4, color=orange, alpha=.75, linewidths=0, zorder=2)
    for row in rows:
        if row["order"] <= 3:
            ax.plot(row["phase"], row["left"], "o", ms=4.5, color=teal, zorder=5)
            ax.plot(row["phase"], row["left"]+row["weight"], "o", ms=4.5,
                    mfc="white", mec=teal, mew=1.1, zorder=5)
    first = next(row for row in rows if row["order"] == 1)
    x, y, w = first["phase"], first["left"], first["weight"]
    ax.annotate("", xy=(x+.045, y+w), xytext=(x+.045, y),
                arrowprops={"arrowstyle": "<->", "color": "#555555", "lw": .8})
    ax.text(x+.066, y+w/2, r"$w_1=\beta$", va="center", fontsize=10)
    ax.annotate("left value included", xy=(x, y), xytext=(.66, y-.14), fontsize=8,
                color=teal, arrowprops={"arrowstyle": "-", "color": teal, "lw": .7})
    ax.set(xlim=(0, 1), ylim=(.97, envelope+.075), xlabel=r"Beatty phase $t=\delta_r$",
           ylabel=r"Profile value / normalized count $R_r^+$")
    ax.set_xticks([0, .2, .4, .6, .8, 1])
    ax.set_yticks([1, 1.25, 1.5, 1.75, 2, 2.25, 2.5, 2.75])
    ax.grid(axis="y", color="#DDE1E5", linewidth=.5, zorder=0)
    ax.set_title("(a) Phase profile and count samples", loc="left", fontsize=10.5, pad=12)
    value.set_title("(b) Value axis", loc="left", fontsize=10.5, pad=12)
    value.add_patch(Rectangle((.12, 1), .33, envelope-1, color=gray, linewidth=0))
    for core in data["certified_deleted_cores"]:
        # Round into the certified open interval even at the display boundary.
        lo = math.nextafter(float(Fraction(core["lower"])), math.inf)
        hi = math.nextafter(float(Fraction(core["upper"])), -math.inf)
        value.add_patch(Rectangle((.12, lo), .33, hi-lo, color=red, linewidth=0))
        if core["order"] in (1, 2, 3, 5):
            value.text(.52, (lo+hi)/2, rf"$r={core['order']}$", va="center", fontsize=9)
    for axis in (ax, value):
        axis.axhline(envelope, color="#777777", linewidth=.7, linestyle=(0, (3, 3)), zorder=0)
    value.text(.14, envelope+.035, r"$E=1/q$", fontsize=9, va="bottom")
    value.set_xlim(0, 1.12)
    value.set_xticks([])
    value.tick_params(axis="y", left=False, labelleft=False)
    value.spines["left"].set_visible(False)
    value.spines["bottom"].set_visible(False)
    fig.legend(handles=[Line2D([], [], color=teal, lw=1.5, label=r"Left-continuous $F_M$"),
                        Patch(facecolor=teal, alpha=.15, label=r"Band $[F_M,F_M+T_M]$"),
                        Line2D([], [], marker="o", color=orange, linestyle="", ms=3,
                               label=r"Exact rational $R_r^+$"),
                        Patch(facecolor=red, label="Certified gap interiors"),
                        Patch(facecolor=gray, label="Unresolved at this cutoff")],
               loc="lower center", bbox_to_anchor=(.52, .062), ncol=3, frameon=False,
               fontsize=8, columnspacing=1.6, handlelength=1.8)
    lo, hi = data["sample_orders"]
    fig.text(.5, .023, f"M = {data['orders']:,}    |    samples r = {lo:,} to {hi:,}    |    "
             rf"$0\leq F-F_M\leq T_M<{data['tail_strict_decimal_upper']}$",
             ha="center", fontsize=8, color="#444444")
    outputs = []
    for suffix in ("pdf", "svg", "png"):
        path = out / f"beatty_profile.{suffix}"
        fig.savefig(path, dpi=300, facecolor="white")
        outputs.append(path)
    plt.close(fig)
    return outputs


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--depth", type=int, default=8000)
    parser.add_argument("--sample-count", type=int, default=1000)
    parser.add_argument("--bits", type=int, default=256)
    parser.add_argument("--output-dir", type=Path, default=ROOT / "docs/theory/figures")
    args = parser.parse_args()
    if not 64 <= args.depth <= 20000 or not 1 <= args.sample_count or args.bits < 192:
        parser.error("Require depth 64..20000, positive sample count and at least 192 bits")
    out = args.output_dir.resolve()
    out.mkdir(parents=True, exist_ok=True)
    data = compute(args.depth, args.sample_count, args.bits)
    outputs = draw(data, out)
    report = out / "beatty_profile.json"
    report.write_text(json.dumps(data, indent=2) + "\n", encoding="utf-8", newline="\n")
    outputs.append(report)
    write_manifest(out / "beatty_profile.research.json", programme="juggler",
                   research_id="juggler/winkler_phase_collapse", scope=data["scope"], outputs=outputs,
                   parameters={"depth": args.depth, "sample_count": args.sample_count,
                               "precision_bits": args.bits, "python_flint": flint.__version__,
                               "matplotlib": matplotlib.__version__},
                   command=["python", "tools/render_beatty_profile.py", *sys.argv[1:]],
                   inputs=[ROOT / "data/research/juggler/arb_paper_audit/beatty.json"],
                   sources=[Path(__file__), ROOT / "tools/arb_paper_audit_core/beatty.py"],
                   artifact_root=out)
    print(json.dumps({"orders": data["orders"], "sample_orders": data["sample_orders"],
                      "tail_upper": data["tail_strict_decimal_upper"],
                      "certified_gap_cores": len(data["certified_deleted_cores"]),
                      "outputs": [str(path) for path in outputs]}, indent=2))


if __name__ == "__main__":
    main()
