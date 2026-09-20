import Problems.Juggler.FateBlockLock
import Problems.Juggler.FateFiberParity

namespace Problems.Juggler

open Finset
open scoped Classical

namespace FiberParity

/-!
# The block lock on an `OE` fiber

`docs/theory/juggler_oe_poor_fiber_tail_note.md`, the step between Lemma 1 and
Lemma 2: `BlockLock.block_lock` is a statement about an arbitrary real sequence with
steps in `[a, a + η]`, and this file instantiates it on the fiber `Φ(m)`.

Two things are needed. The first is the parity bridge: `block_lock` counts the `j`
with `{x_j} < 1/2`, while the fiber's own count is `evenImageCount`, defined through
`Nat.sqrt (n^3) % 2 = 0`. Those agree by `cell_xval_even_iff` composed with
`Sweep.cell_modEq_zero_iff`, which is `evenImageCount_eq_fract`. The second is the
step interval, which is exactly `step_ge` and `step_le` of `FateFiberParity`: every
step of `x` along the fiber lies in `[A_m, A_m + ε_m]`. Lemma 4.2 uses the same two
bounds to feed the sweep; here they feed the block lock instead, which is why no
goodness hypothesis appears — `block_lock` has none.

What this does NOT do is choose `q`. That is Lemma 2, which picks `q` by Dirichlet's
approximation theorem and takes the contrapositive; it is not in this file. Here `q`,
`p` and `ρ` are given, and the conclusion is the note's (1.1) in un-divided form,
with `ρ` in place of `‖q α_m‖` and `ε_m` in place of `η_m`.

Not a halt theorem, and not a statement about any particular fiber being unbalanced:
it is an upper bound on how unbalanced one can be, given a rational approximation to
its step.
-/

/-- The fiber's even-image count, as a count of half-cells.

`evenImageCount` is defined by `Nat.sqrt (n^3) % 2 = 0`; `block_lock` counts
`Int.fract (x j) < 1/2`. The two agree termwise, by the cell identity. -/
theorem evenImageCount_eq_fract {m : ℕ} (hne : (oeFiber m).Nonempty) :
    evenImageCount m =
      #{j ∈ Finset.range (Hlen m hne) | Int.fract (xval (nseq m hne j)) < 1 / 2} := by
  have hbridge : ∀ j ∈ Finset.range (Hlen m hne),
      (Nat.sqrt ((nseq m hne j) ^ 3) % 2 = 0 ↔
        Int.fract (xval (nseq m hne j)) < 1 / 2) := by
    intro j _
    exact (cell_xval_even_iff (nseq m hne j)).symm.trans
      (Sweep.cell_modEq_zero_iff (xval (nseq m hne j)))
  rw [evenImageCount_eq' hne, Finset.filter_congr hbridge]

/-- **The block lock on a fiber.** For `m ≥ 1` and any rational approximation `p/q` to
the fiber's lower step `A_m`, with `|q A_m - p| ≤ ρ` and `gcd(p, q) = 1`,
\[
  \Bigl| G_m - \frac{H_m}{2} \Bigr|
    \le 4(\rho + q\,\varepsilon_m) H_m + \frac{5 H_m}{2q} + q .
\]
This is `BlockLock.block_lock` with `x = xval ∘ nseq`, `a = A_m` and `η = ε_m`; the
step interval is `step_ge` and `step_le`, and the count is matched by
`evenImageCount_eq_fract`. Dividing by `H_m` gives the note's (1.1). -/
theorem fiber_block_lock {m : ℕ} (hm : 1 ≤ m) (hne : (oeFiber m).Nonempty)
    {q : ℕ} (hq : 1 ≤ q) {ρ : ℝ} (hρ : 0 ≤ ρ) {p : ℤ}
    (hcop : Nat.Coprime p.natAbs q)
    (hpa : |(q : ℝ) * Am m - (p : ℝ)| ≤ ρ) :
    |(evenImageCount m : ℝ) - (Hlen m hne : ℝ) / 2|
      ≤ 4 * (ρ + (q : ℝ) * eps m) * (Hlen m hne : ℝ)
        + 5 * (Hlen m hne : ℝ) / (2 * (q : ℝ)) + (q : ℝ) := by
  have hsteps : ∀ j, j + 1 < Hlen m hne →
      Am m ≤ xval (nseq m hne (j + 1)) - xval (nseq m hne j) ∧
        xval (nseq m hne (j + 1)) - xval (nseq m hne j) ≤ Am m + eps m := by
    intro j hj
    exact ⟨step_ge hne (by omega), step_le hne hm hj⟩
  have hbl := BlockLock.block_lock (fun j => xval (nseq m hne j)) (Hlen m hne) q
    (Am m) (eps m) ρ p hq (eps_pos hm).le hρ hcop hsteps hpa
  rwa [evenImageCount_eq_fract hne]

end FiberParity

end Problems.Juggler
