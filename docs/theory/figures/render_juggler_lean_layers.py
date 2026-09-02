"""Render the paper-central Juggler Lean import graph at print scale.

Mermaid-cli produces a readable screen SVG, but the five-column layout is too
wide for 11pt paper: labels shrink below 5pt. This renderer keeps the same
one-way module graph and writes a PNG with 8.5pt labels.
"""

from __future__ import annotations

from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parent))
from juggler_figure_style import DEFAULT_BOX, draw_edge, draw_frame, draw_node, new_axes, save

OUT = Path(__file__).with_name("juggler_lean_layers.png")

NODES = {
    "Dynamics": ("Dynamics", "floorPower"),
    "Iteration": ("Iteration", ""),
    "Termination": ("Termination", "ReachesOne"),
    "Itinerary": ("Itinerary", "follows, image"),
    "ItineraryStats": ("ItineraryStats", ""),
    "Envelope": ("Envelope", "power_bound_contracts"),
    "Equality": ("Equality", ""),
    "Defect": ("Defect", ""),
    "GlobalDefect": ("GlobalDefect", ""),
    "DefectLowerBound": ("DefectLowerBound", ""),
    "Preimages": ("Preimages", "even/odd one-step preimages"),
    "Drift": ("Drift", ""),
    "FirstPassage": ("FirstPassage", ""),
    "Certificates": ("Certificates", ""),
    "Progress": ("Progress", "FiniteProgress"),
    "Minimal": ("Minimal", ""),
    "Scale": ("Scale", ""),
    "Residuals": ("Residuals", ""),
    "Cycles": ("Cycles", ""),
    "Cylinders": ("PreimageCylinders", ""),
}

# Column frames: title, center x, (left, right, bottom, top)
FRAMES = [
    ("Dynamics", 1.00, 0.12, 1.88, 0.55, 4.28),
    ("Words", 3.15, 2.27, 4.03, 0.22, 4.28),
    ("Defect", 5.30, 4.42, 6.18, 0.22, 4.28),
    ("Progress", 7.45, 6.57, 8.33, 0.22, 4.28),
    ("Structure", 9.70, 8.62, 10.88, 0.22, 4.28),
]

# Node centers in figure inches.
POS = {
    "Dynamics": (1.00, 3.55),
    "Iteration": (1.00, 2.55),
    "Termination": (1.00, 1.55),
    "Itinerary": (3.15, 3.70),
    "ItineraryStats": (3.15, 2.70),
    "Envelope": (3.15, 1.70),
    "Equality": (3.15, 0.70),
    "Defect": (5.30, 3.70),
    "GlobalDefect": (5.30, 2.55),
    "DefectLowerBound": (5.30, 1.55),
    "Preimages": (5.30, 0.55),
    "Drift": (7.45, 3.70),
    "FirstPassage": (7.45, 2.70),
    "Certificates": (7.45, 1.70),
    "Progress": (7.45, 0.70),
    "Minimal": (9.70, 3.70),
    "Scale": (9.70, 2.70),
    "Residuals": (9.70, 1.70),
    "Cycles": (9.18, 0.55),
    "Cylinders": (10.22, 0.55),
}

# (src, dst, side, rad) with side in {v, h, d}
# v = vertical inside a column, h = left-to-right, d = routed diagonal
EDGES = [
    ("Dynamics", "Iteration", "v", 0.0),
    ("Iteration", "Termination", "v", 0.0),
    ("Termination", "Itinerary", "d", 0.12),
    ("Itinerary", "ItineraryStats", "v", 0.0),
    ("ItineraryStats", "Envelope", "v", 0.0),
    ("Envelope", "Equality", "v", 0.0),
    ("ItineraryStats", "Drift", "h", 0.0),
    ("Envelope", "FirstPassage", "h", 0.0),
    ("Equality", "Defect", "d", -0.18),
    ("Defect", "GlobalDefect", "v", 0.0),
    ("GlobalDefect", "DefectLowerBound", "v", 0.0),
    ("Defect", "Preimages", "d", 0.28),
    ("Drift", "FirstPassage", "v", 0.0),
    ("FirstPassage", "Certificates", "v", 0.0),
    ("Certificates", "Progress", "v", 0.0),
    ("Defect", "Certificates", "d", -0.15),
    ("GlobalDefect", "Minimal", "h", 0.08),
    ("Progress", "Minimal", "d", -0.22),
    ("Minimal", "Scale", "v", 0.0),
    ("Scale", "Residuals", "v", 0.0),
    ("DefectLowerBound", "Residuals", "h", 0.0),
    ("Residuals", "Cycles", "d", 0.05),
    ("Residuals", "Cylinders", "d", -0.05),
]

BOX = {
    "Cycles": (1.00, 0.50),
    "Cylinders": (1.08, 0.50),
}
DEFAULT_BOX = (1.68, 0.56)

FIG_W = 11.05
FIG_H = 4.70


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
    # diagonal: leave the nearer side
    if abs(x1 - x0) >= abs(y1 - y0):
        if x1 > x0:
            return (x0 + w0 / 2, y0), (x1 - w1 / 2, y1)
        return (x0 - w0 / 2, y0), (x1 + w1 / 2, y1)
    if y1 < y0:
        return (x0, y0 - h0 / 2), (x1, y1 + h1 / 2)
    return (x0, y0 + h0 / 2), (x1, y1 - h1 / 2)


def main() -> None:
    fig, ax = new_axes(FIG_W, FIG_H)
    for title, _x, left, right, bottom, top in FRAMES:
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
