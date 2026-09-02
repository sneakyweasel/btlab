"""Render the paper's theorem-flow figure."""

from __future__ import annotations

from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parent))
from juggler_figure_style import DEFAULT_BOX, draw_edge, draw_frame, draw_node, new_axes, save

OUT = Path(__file__).with_name("juggler_frontier.png")

NODES = {
    "Words": ("Realized", "parity itineraries"),
    "Envelope": ("Power envelope", ""),
    "Contract": ("Exponent-gap", "contraction"),
    "Remainders": ("Local floor", "remainders"),
    "Defect": ("Exact global", "defect"),
    "Towers": ("Monochrome towers", "and composition"),
    "Preimages": ("One-step preimages", ""),
    "Cycles": ("Cycle restrictions", ""),
    "Excluded": ("No cycles of", "length \u2264 6"),
    "Discrepancy": ("Parity discrepancy", "+ kernel theorem"),
    "Certificates": ("One- to four-step", "certificates"),
    "Density": ("Certified class", "density 13/16"),
    "Kernel": ("Level-3 kernel", "(open)"),
    "Open": ("Open", "almost-all descent?"),
}

FRAMES = [
    ("Exact finite-itinerary calculus", 0.10, 6.70, 3.28, 5.70),
    ("Cycle consequences", 0.10, 9.35, 1.67, 3.17),
    ("Density corollaries and boundary", 0.10, 10.90, 0.08, 1.56),
]

POS = {
    "Words": (1.10, 5.05),
    "Envelope": (3.35, 5.05),
    "Contract": (5.60, 5.05),
    "Remainders": (1.10, 3.90),
    "Defect": (3.35, 3.90),
    "Towers": (5.60, 3.90),
    "Preimages": (1.10, 2.42),
    "Cycles": (5.60, 2.42),
    "Excluded": (8.20, 2.42),
    "Discrepancy": (1.10, 1.27),
    "Certificates": (1.10, 0.53),
    "Density": (3.65, 0.90),
    "Kernel": (6.20, 0.90),
    "Open": (8.75, 0.90),
}

BOX = {
    name: (1.82, 0.58)
    for name in NODES
}
BOX.update(
    {
        "Certificates": (2.02, 0.58),
        "Towers": (2.02, 0.58),
        "Excluded": (2.02, 0.58),
    }
)

EDGES = [
    ("Words", "Envelope", "h", 0.0),
    ("Envelope", "Contract", "h", 0.0),
    ("Remainders", "Defect", "h", 0.0),
    ("Defect", "Towers", "h", 0.0),
    ("Preimages", "Cycles", "h", 0.0),
    ("Cycles", "Excluded", "h", 0.0),
    ("Discrepancy", "Density", "d", -0.05),
    ("Certificates", "Density", "d", 0.05),
    ("Density", "Kernel", "h", 0.0),
    ("Kernel", "Open", "h", 0.0),
]

FIG_W = 11.0
FIG_H = 5.8


def box_size(name: str) -> tuple[float, float]:
    return BOX.get(name, DEFAULT_BOX)


def ports(src: str, dst: str, kind: str) -> tuple[tuple[float, float], tuple[float, float]]:
    x0, y0 = POS[src]
    x1, y1 = POS[dst]
    w0, h0 = box_size(src)
    w1, h1 = box_size(dst)
    if kind == "v":
        if y1 < y0:
            return (x0, y0 - h0 / 2), (x1, y1 + h1 / 2)
        return (x0, y0 + h0 / 2), (x1, y1 - h1 / 2)
    if kind == "h":
        if x1 > x0:
            return (x0 + w0 / 2, y0), (x1 - w1 / 2, y1)
        return (x0 - w0 / 2, y0), (x1 + w1 / 2, y1)
    if abs(x1 - x0) >= abs(y1 - y0):
        if x1 > x0:
            return (x0 + w0 / 2, y0), (x1 - w1 / 2, y1)
        return (x0 - w0 / 2, y0), (x1 + w1 / 2, y1)
    if y1 < y0:
        return (x0, y0 - h0 / 2), (x1, y1 + h1 / 2)
    return (x0, y0 + h0 / 2), (x1, y1 - h1 / 2)


def main() -> None:
    fig, ax = new_axes(FIG_W, FIG_H)
    for title, left, right, bottom, top in FRAMES:
        draw_frame(ax, title, left, right, bottom, top)
    for src, dst, kind, rad in EDGES:
        draw_edge(ax, *ports(src, dst, kind), rad=rad)
    for name, (x, y) in POS.items():
        title, subtitle = NODES[name]
        draw_node(ax, x, y, title, subtitle, size=box_size(name))
    save(fig, OUT)
    print(OUT)


if __name__ == "__main__":
    main()
