"""Figures for Paper C (docs/theory/juggler_fate_almost_all_note.md).

Writes three PNG files to docs/theory/figures/ (the source of truth, next to this script) and
mirrors them to juggler_review/figures/:
  paper_c_productions.png   - the two exact productions (even block, OE fiber with its parity sweep)
  paper_c_decomposition.png - the first-letter decomposition of a two-way closed set on (sqrt x, x]
  paper_c_dependencies.png  - logical dependency map of the paper

Run:  python docs/theory/figures/render_paper_c_figures.py
"""

from __future__ import annotations

import math
import shutil
from pathlib import Path

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt  # noqa: E402
from matplotlib.patches import FancyArrowPatch, FancyBboxPatch  # noqa: E402

OUT = Path(__file__).resolve().parent
MIRROR = OUT.parents[2] / "juggler_review" / "figures"


def isqrt_floor_pow32(n: int) -> int:
    return math.isqrt(n * n * n)


def fig_productions() -> None:
    fig, axes = plt.subplots(2, 1, figsize=(8.2, 4.6))

    # (a) even block E(m): the even integers of [m^2, (m+1)^2) all map to m.
    ax = axes[0]
    m = 12
    lo, hi = m * m, (m + 1) ** 2
    xs = list(range(lo, hi))
    for x in xs:
        ax.plot([x], [0], marker="o", ms=5, color="tab:blue" if x % 2 == 0 else "0.75", zorder=3)
    ax.hlines(0, lo - 1, hi, color="0.5", lw=1)
    ax.annotate("", xy=((lo + hi) / 2, -0.55), xytext=((lo + hi) / 2, -0.12), arrowprops=dict(arrowstyle="->", lw=1.2))
    ax.text((lo + hi) / 2, -0.75, r"$J(n)=\lfloor\sqrt{n}\rfloor=m$ for every even $n$", ha="center", va="top", fontsize=9)
    ax.text(lo, 0.35, r"$m^2$", ha="center", fontsize=9)
    ax.text(hi, 0.35, r"$(m+1)^2$", ha="center", fontsize=9)
    ax.set_title(r"(a) Even block $E(m)$: the even integers of $[m^2,(m+1)^2)$ (blue) all have $J(n)=m$", fontsize=9.5, loc="left")
    ax.set_xlim(lo - 3, hi + 3)
    ax.set_ylim(-1.1, 0.7)
    ax.axis("off")

    # (b) OE fiber: odd n in [m^{4/3}, (m+1)^{4/3}) with the parity of floor(n^{3/2}); even (blue) means J(J(n)) = m.
    ax = axes[1]
    m = 100_000
    lo_f = math.ceil(m ** (4 / 3))
    hi_f = math.ceil((m + 1) ** (4 / 3))
    fiber = [n for n in range(lo_f, hi_f) if n % 2 == 1 and m**4 <= n**3 < (m + 1) ** 4]
    even = 0
    for n in fiber:
        k = isqrt_floor_pow32(n)
        is_even = k % 2 == 0
        even += is_even
        ax.plot([n], [0], marker="o", ms=5, color="tab:blue" if is_even else "tab:red", zorder=3)
    ax.hlines(0, fiber[0] - 1, fiber[-1] + 1, color="0.5", lw=1)
    ax.text(fiber[0], 0.35, r"$m^{4/3}$", ha="center", fontsize=9)
    ax.text(fiber[-1], 0.35, r"$(m+1)^{4/3}$", ha="center", fontsize=9)
    ax.text(
        (fiber[0] + fiber[-1]) / 2,
        -0.55,
        rf"$m=10^5$: $H_m={len(fiber)}$ odd $n$, $G_m={even}$ with $\lfloor n^{{3/2}}\rfloor$ even (blue): each of these has $J(J(n))=m$",
        ha="center",
        va="top",
        fontsize=9,
    )
    ax.set_title(
        r"(b) $OE$ fiber $\Phi(m)$: odd $n$ with $\lfloor n^{3/4}\rfloor=m$; the parity of $\lfloor n^{3/2}\rfloor$ sweeps along the fiber",
        fontsize=9.5,
        loc="left",
    )
    ax.set_xlim(fiber[0] - 3, fiber[-1] + 3)
    ax.set_ylim(-1.1, 0.7)
    ax.axis("off")

    fig.tight_layout()
    fig.savefig(OUT / "paper_c_productions.png", dpi=200)
    plt.close(fig)


def fig_decomposition() -> None:
    fig, ax = plt.subplots(figsize=(8.2, 3.2))
    ax.set_xlim(0, 10)
    ax.set_ylim(0, 4)
    ax.axis("off")

    # the target range (sqrt x, x] as a bar split by first letters
    y0, h = 2.6, 0.7
    parts = [
        (0.5, "even members\n$\\frac{1}{2}\\,\\varphi_A(t/2)$", "tab:blue"),
        (0.25, "$OE$-type odd\n$\\frac{1}{4}\\,\\varphi^{\\rm fib}_A(3t/4)$", "tab:green"),
        (0.25, "$OO$-type odd\n$\\frac{1}{4}\\,\\psi_A(t)$", "tab:red"),
    ]
    x = 1.0
    width = 8.0
    for frac, label, color in parts:
        w = width * frac
        ax.add_patch(FancyBboxPatch((x, y0), w, h, boxstyle="square,pad=0", fc=color, ec="black", alpha=0.35))
        ax.text(x + w / 2, y0 + h / 2, label, ha="center", va="center", fontsize=9)
        x += w
    ax.text(1.0, y0 + h + 0.15, r"$A\cap(\sqrt{x},\,x]$, log-density $\varphi_A(t)$, $t=\log x$", fontsize=9.5, va="bottom")

    # sources below
    srcs = [
        (1.0 + 8.0 * 0.25, r"$A\cap(x^{1/4},\sqrt{x}]$" + "\n" + r"$E$-blocks are intervals", "tab:blue"),
        (1.0 + 8.0 * 0.625, r"$A\cap(x^{3/8},x^{3/4}]$" + "\n" + r"$OE$ fibers, parity sweep", "tab:green"),
        (1.0 + 8.0 * 0.875, r"$A\cap S_{\rm odd}$ at $(x^{3/4},x^{3/2}]$" + "\n" + r"odd preimages: free term", "tab:red"),
    ]
    for cx, label, color in srcs:
        ax.add_patch(FancyBboxPatch((cx - 0.95, 0.5), 1.9, 0.9, boxstyle="round,pad=0.05", fc="white", ec=color, lw=1.5))
        ax.text(cx, 0.95, label, ha="center", va="center", fontsize=7.8)
        ax.add_patch(FancyArrowPatch((cx, 1.4), (cx, y0 - 0.05), arrowstyle="->", mutation_scale=12, color=color, lw=1.4))

    ax.text(
        5.0,
        0.1,
        r"(6.1): $\varphi_A(t)=\frac{1}{2}\varphi_A(t/2)+\frac{1}{4}\varphi^{\rm fib}_A(3t/4)+\frac{1}{4}\psi_A(t)+O(e^{-t/4}/t)$; descending sources on the left, ascending free term on the right",
        ha="center",
        va="center",
        fontsize=8.5,
    )
    fig.tight_layout()
    fig.savefig(OUT / "paper_c_decomposition.png", dpi=200)
    plt.close(fig)


def fig_dependencies() -> None:
    fig,ax=plt.subplots(figsize=(9.5,6.3));ax.set_xlim(0,10);ax.set_ylim(0,7);ax.axis('off')
    def box(x,y,w,h,text,fc):
     ax.add_patch(FancyBboxPatch((x,y),w,h,boxstyle='round,pad=0.06',facecolor=fc,edgecolor='#365267',linewidth=1))
     ax.text(x+w/2,y+h/2,text,ha='center',va='center',fontsize=9,color='#162b3b')
    def arrow(a,b):
     ax.add_patch(FancyArrowPatch(a,b,arrowstyle='-|>',mutation_scale=12,linewidth=1.2,color='#365267',shrinkA=3,shrinkB=3))
    box(.1,5.8,4.2,.9,'Exact inverse intervals and sweep\nBlock estimates; finite productions (Appendix D)','#e8f1f6')
    box(.1,4.1,4.2,.95,'Contagion (Theorem 1)\n'+r'$\lambda<\lambda^{**}\approx0.4926$','#e8f1f6')
    box(5.3,5.8,4.5,.9,'Unproved sufficient hypotheses\nBad cylinders H, one-sided Hq, or live pressure P','#fff1da')
    box(5.3,4.1,4.5,.95,'Time-bounded live count\nCase-dependent rate r (Theorems 8.3, 9.1, 9.2)','#fff1da')
    box(2.0,2.15,5.9,1.1,'Eventual-entry rate '+r'$e>1-\lambda^{**}\approx0.5074$'+'\n'+r'$\Longleftrightarrow$'+' Universal termination\n(Theorem 3; no stopping-time converse)','#edf4e8')
    box(.1,.25,4.45,1.0,'First-letter identity (6.1)\nNormalized infinite live limit (Proposition 10.1)','#f0edf7')
    box(5.25,.25,4.55,1.0,'Hypothesis L (Appendix C)\nConditional exponent '+r'$\lambda^{***}\approx0.5392$'+'\nSeparate improvement of the rate threshold','#f0edf7')
    arrow((2.2,5.8),(2.2,5.05));arrow((7.55,5.8),(7.55,5.05))
    arrow((2.2,4.1),(3.7,3.25));arrow((7.55,4.1),(6.25,3.25))
    ax.text(5,6.95,'Proved implications; the hypotheses in amber remain open',ha='center',va='top',fontsize=10,fontweight='bold',color='#162b3b')
    fig.tight_layout();fig.savefig(OUT/'paper_c_dependencies.png',dpi=220,bbox_inches='tight');plt.close(fig)
def main() -> None:
    OUT.mkdir(parents=True, exist_ok=True)
    fig_productions()
    fig_decomposition()
    fig_dependencies()
    MIRROR.mkdir(parents=True, exist_ok=True)
    for name in ("paper_c_productions.png", "paper_c_decomposition.png", "paper_c_dependencies.png"):
        shutil.copyfile(OUT / name, MIRROR / name)
        print(OUT / name)


if __name__ == "__main__":
    main()
