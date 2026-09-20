import Mathlib.NumberTheory.DiophantineApproximation.Basic
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


/-! ### Dirichlet, in lowest terms -/

/-- **Dirichlet's approximation theorem, reduced.** For every real `ξ` and `n ≥ 1` there is a
fraction `p/q` in lowest terms with `1 ≤ q ≤ n` and `|q ξ - p| ≤ 1/(n+1)`.

Mathlib's `Real.exists_nat_abs_mul_sub_round_le` supplies `q` and `p = round (q ξ)` without
the coprimality, and `block_lock` needs it, since `gcd(p,q) = 1` is what makes the `q` points
`y + i p/q` a full `1/q`-grid rather than a coarser one. Dividing through by `g = gcd(p,q)`
costs nothing: `q/g ≤ q` and `|(q/g) ξ - p/g| = |q ξ - p| / g ≤ |q ξ - p|`, so both sides of
the conclusion only improve. The division is done multiplicatively, through the witnesses of
`g ∣ q` and `g ∣ p`, to keep integer-division casts out of it. -/
theorem exists_coprime_approx (ξ : ℝ) {n : ℕ} (hn : 0 < n) :
    ∃ (q : ℕ) (P : ℤ), 1 ≤ q ∧ q ≤ n ∧ Nat.Coprime P.natAbs q ∧
      |(q : ℝ) * ξ - (P : ℝ)| ≤ 1 / ((n : ℝ) + 1) := by
  obtain ⟨k, hk0, hkn, hk⟩ := Real.exists_nat_abs_mul_sub_round_le ξ hn
  set R : ℤ := round ((k : ℝ) * ξ) with hRdef
  set g : ℕ := Nat.gcd R.natAbs k with hgdef
  have hg0 : 0 < g := Nat.gcd_pos_of_pos_right _ hk0
  have hgk : g ∣ k := Nat.gcd_dvd_right _ _
  have hgR : (g : ℤ) ∣ R := Int.dvd_natAbs.mp (Int.natCast_dvd_natCast.mpr (Nat.gcd_dvd_left _ _))
  obtain ⟨k', hk'⟩ := hgk
  obtain ⟨R', hR'⟩ := hgR
  have hgR0 : (0 : ℝ) < (g : ℝ) := by exact_mod_cast hg0
  have hk'0 : 0 < k' := by
    rcases Nat.eq_zero_or_pos k' with h | h
    · rw [h, Nat.mul_zero] at hk'; omega
    · exact h
  -- the reduced pair is coprime
  have hcop : Nat.Coprime R'.natAbs k' := by
    have h := Nat.coprime_div_gcd_div_gcd (m := R.natAbs) (n := k) (by rw [← hgdef]; exact hg0)
    have hkq : k / g = k' := by rw [hk']; exact Nat.mul_div_cancel_left _ hg0
    have hRq : R.natAbs / g = R'.natAbs := by
      have : R.natAbs = g * R'.natAbs := by
        rw [hR', Int.natAbs_mul, Int.natAbs_natCast]
      rw [this]; exact Nat.mul_div_cancel_left _ hg0
    rw [← hgdef, hkq, hRq] at h
    exact h
  refine ⟨k', R', hk'0, ?_, hcop, ?_⟩
  · calc k' ≤ g * k' := Nat.le_mul_of_pos_left _ hg0
      _ = k := hk'.symm
      _ ≤ n := hkn
  · -- `g * ((k' ξ) - R') = k ξ - R`, so the reduced error is the old one divided by `g`
    have hexp : (g : ℝ) * ((k' : ℝ) * ξ - (R' : ℝ)) = (k : ℝ) * ξ - (R : ℝ) := by
      rw [hk', hR']
      push_cast
      ring
    have habs : (g : ℝ) * |(k' : ℝ) * ξ - (R' : ℝ)| = |(k : ℝ) * ξ - (R : ℝ)| := by
      rw [← hexp, abs_mul, abs_of_pos hgR0]
    have hg1 : (1 : ℝ) ≤ (g : ℝ) := by exact_mod_cast hg0
    nlinarith [abs_nonneg ((k' : ℝ) * ξ - (R' : ℝ)), hk, habs, hg1]

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
