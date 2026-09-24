"""Optionally render static paper figures from the certified React profile data.

The lab and React data exporter do not require matplotlib. This standalone
renderer requires a separately available matplotlib installation only when run.
It never computes or rewrites the certified numerical data.
"""
from __future__ import annotations

import argparse
from fractions import Fraction
import json
import math
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "src"))
from research.experiments.provenance import write_manifest


def draw(data: dict, out: Path) -> list[Path]:
    """Produce vector PDF/SVG and a high-resolution PNG with identical content."""
    import matplotlib
    matplotlib.use("Agg")
    import matplotlib.pyplot as plt
    from matplotlib.collections import LineCollection
    from matplotlib.lines import Line2D
    from matplotlib.patches import Patch, Rectangle

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
        if suffix == "svg":
            # Match Git's LF policy before the byte-exact manifest is written.
            text = path.read_text(encoding="utf-8")
            path.write_text("\n".join(line.rstrip() for line in text.splitlines()) + "\n",
                            encoding="utf-8", newline="\n")
        outputs.append(path)
    plt.close(fig)
    return outputs


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--input", type=Path,
                        default=ROOT / "data/research/juggler/winkler_phase_collapse/beatty_profile.json")
    parser.add_argument("--output-dir", type=Path, default=ROOT / "docs/theory/figures")
    args = parser.parse_args()
    data = json.loads(args.input.read_text(encoding="utf-8"))
    out = args.output_dir.resolve()
    out.mkdir(parents=True, exist_ok=True)
    outputs = draw(data, out)
    import matplotlib
    write_manifest(out / "beatty_profile.research.json", programme="juggler",
                   research_id="juggler/winkler_phase_collapse", scope=data["scope"], outputs=outputs,
                   parameters={"matplotlib": matplotlib.__version__},
                   command=["python", "tools/render_beatty_profile.py", *sys.argv[1:]],
                   inputs=[args.input], sources=[Path(__file__)], artifact_root=out)
    print(json.dumps({"outputs": [str(path) for path in outputs]}, indent=2))


if __name__ == "__main__":
    main()
