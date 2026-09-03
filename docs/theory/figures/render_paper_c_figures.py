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
    fig, ax = plt.subplots(figsize=(8.6, 5.6))
    ax.set_xlim(-0.35, 10.05)
    ax.set_ylim(0, 10)
    ax.axis("off")

    def box(x, y, w, h, text, fc="white", ec="black", fs=8.6, lw=1.2):
        ax.add_patch(FancyBboxPatch((x, y), w, h, boxstyle="round,pad=0.08", fc=fc, ec=ec, lw=lw))
        ax.text(x + w / 2, y + h / 2, text, ha="center", va="center", fontsize=fs)
        return (x + w / 2, y + h / 2, w, h)

    def arrow(a, b, dashed=False, color="black"):
        ax.add_patch(
            FancyArrowPatch(
                a, b, arrowstyle="->", mutation_scale=13, lw=1.2, color=color, linestyle="--" if dashed else "-", shrinkA=2, shrinkB=2
            )
        )

    lean = "#e8f0fe"
    human = "#fff4e0"
    cond = "#f3e8ff"
    obs = "#eeeeee"

    # Row 0: Lean layer
    box(0.2, 0.4, 2.2, 0.9, "Lean: fate classes closed,\ntrichotomy, exclusion (Lem. 2.1)", fc=lean, fs=8.2)
    box(2.7, 0.4, 2.2, 0.9, "Lean: even block, $OE$ fiber,\ncell identity (Lem. 3.1, 3.2)", fc=lean, fs=8.2)
    box(5.4, 0.4, 2.0, 0.9, "Lean: odd generation\n(Theorem 6.1)", fc=lean, fs=8.2)
    box(7.7, 0.4, 2.1, 0.9, "Lean: envelope descent\ninto the floor (Lem. 8.1)", fc=lean, fs=8.2)

    # Row 1: human lemmas and the exact decomposition
    box(0.0, 2.2, 2.0, 0.9, "exact first-letter\ndecomposition (6.1), Sec. 6.2", fc=human, fs=8.2)
    box(2.9, 2.2, 2.3, 0.9, "sweep lemma, fiber parity $\\geq 1/7$,\nblock average (Sec. 4)", fc=human, fs=8.2)

    # Row 2: the two engines
    box(1.6, 4.0, 3.6, 0.95, "Theorem 1: contagion (Sec. 5)\n$\\sum_{n\\in A,\\,n\\leq x}1/n\\gg(\\log x)^{\\lambda}$, $\\lambda<0.4050$", fc=human)
    box(5.6, 4.0, 4.2, 0.95, "Theorem 4: parity hypotheses $\\Rightarrow$ Tao-type bound\n$\\mathrm{H}(C,A)\\Leftarrow\\mathrm{H}_q\\Leftarrow\\mathrm{P}_\\theta\\Leftarrow\\mathrm{M}_{\\theta,q}$ (Sec. 8–9)", fc=human)

    # Row 3: the reformulation, the single frontier, the conditional appendix
    box(0.0, 5.8, 3.0, 0.95, "Theorem 5: $\\psi_F=$ live mass; duality;\ndepth budget (Sec. 10)", fc=human)
    box(3.6, 5.8, 3.8, 0.95, "Theorem 3: conjecture $\\Leftrightarrow$ Tao-type bound\n$\\#\\{n\\ \\mathrm{odd}\\in(y,2y]\\backslash R\\}\\leq y(\\log y)^{-e}$, $e>0.595$", fc=human)
    box(7.7, 5.8, 2.1, 0.95, "Appendix C: $\\lambda^{***}=0.4922$,\nconditional on Hypothesis L", fc=cond, fs=8.2)

    # Row 4
    box(4.4, 7.6, 2.2, 0.8, "Juggler conjecture\n(not proved)", fc="white", ec="black", lw=1.6)
    box(7.7, 7.6, 2.1, 0.8, "numerical observations\n(Sec. 11): no logical role", fc=obs, fs=8.2)

    # arrows (solid: unconditional dependence)
    arrow((2.3, 1.3), (2.6, 4.0))          # fate classes -> Theorem 1
    arrow((3.0, 1.3), (1.6, 2.2))          # cells -> exact decomposition
    arrow((3.9, 1.3), (4.0, 2.2))          # cells -> sweep/block
    arrow((4.0, 3.1), (3.9, 4.0))          # sweep/block -> Theorem 1
    arrow((8.75, 1.3), (8.75, 4.0))        # envelope -> Theorem 4
    arrow((5.45, 1.3), (5.45, 5.8))        # odd generation -> Theorem 3 (between the two engines)
    arrow((4.2, 4.95), (4.8, 5.8))         # Theorem 1 -> Theorem 3
    arrow((6.8, 4.95), (6.4, 5.8))         # Theorem 4 -> Theorem 3
    arrow((5.5, 6.75), (5.5, 7.6))         # Theorem 3 -> conjecture
    arrow((1.0, 3.1), (1.0, 5.8))          # exact decomposition -> Theorem 5
    arrow((5.9, 4.95), (2.9, 5.8), dashed=True)   # Theorem 4 (as hypothesis) -> Theorem 5
    arrow((8.75, 5.8), (8.75, 4.95), dashed=True, color="0.4")  # Appendix C -> constants of Theorem 4
    arrow((7.7, 6.3), (7.4, 6.3), dashed=True, color="0.4")     # Appendix C -> constants of Theorem 3

    ax.text(
        5.0,
        9.5,
        "Solid arrows: unconditional dependence. Dashed: the bound used as a hypothesis (Sec. 10), or the\nconditional constants of Appendix C (they improve the exponents of Theorems 1, 3, 4 but nothing else depends on them).",
        ha="center",
        va="center",
        fontsize=8.2,
    )
    fig.tight_layout()
    fig.savefig(OUT / "paper_c_dependencies.png", dpi=200)
    plt.close(fig)


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
