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


/-! ### (F3): the step drift over a whole fiber is bounded -/

/-- **(F3) of the note.** `ε_m H_m ≤ 0.6769` for `m ≥ 10^6`: the total drift of the fiber's
step, `η_m H_m`, is bounded by an absolute constant well under one. Paper C's own form of
this carries `1.02 m^{-1/3}` for the step gap and lands at `0.6903`; Lean's `upper_step_le`
gives the sharper `ε_m = m^{-1/3}`, so the constant here is smaller and the note's `3.77`
keeps room.

It is the reason the block lock's `q/H` term has a bounded coefficient at all: without it,
`q η_m H_m` could grow with `m`. -/
theorem eps_mul_Hlen_le {m : ℕ} (hm : 10 ^ 6 ≤ m) (hne : (oeFiber m).Nonempty) :
    eps m * (Hlen m hne : ℝ) ≤ 0.6769 := by
  have hm1 : 1 ≤ m := by omega
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm1
  have hepos := eps_pos hm1
  have hle : (m : ℝ) + 1 ≤ 1.000001 * (m : ℝ) := by
    have h6 : (10 ^ 6 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    nlinarith
  have hstep : ((m : ℝ) + 1) ^ ((1 : ℝ) / 3)
      ≤ (1.000001 : ℝ) ^ ((1 : ℝ) / 3) * (m : ℝ) ^ ((1 : ℝ) / 3) := by
    calc ((m : ℝ) + 1) ^ ((1 : ℝ) / 3)
        ≤ (1.000001 * (m : ℝ)) ^ ((1 : ℝ) / 3) :=
          Real.rpow_le_rpow (by positivity) hle (by norm_num)
      _ = (1.000001 : ℝ) ^ ((1 : ℝ) / 3) * (m : ℝ) ^ ((1 : ℝ) / 3) :=
          Real.mul_rpow (by norm_num) hm0.le
  have hcube : (1.000001 : ℝ) ^ ((1 : ℝ) / 3) ≤ 1.0001 := by
    rw [Numerics.rpow_le_iff_pow (n := 3) (by norm_num) (by norm_num) (by norm_num)]
    norm_num
  have hkey : eps m * ((m : ℝ) + 1) ^ ((1 : ℝ) / 3) ≤ 1.0001 := by
    calc eps m * ((m : ℝ) + 1) ^ ((1 : ℝ) / 3)
        ≤ eps m * ((1.000001 : ℝ) ^ ((1 : ℝ) / 3) * (m : ℝ) ^ ((1 : ℝ) / 3)) :=
          mul_le_mul_of_nonneg_left hstep hepos.le
      _ = (1.000001 : ℝ) ^ ((1 : ℝ) / 3) * (eps m * (m : ℝ) ^ ((1 : ℝ) / 3)) := by ring
      _ = (1.000001 : ℝ) ^ ((1 : ℝ) / 3) := by rw [eps_mul_cbrt hm1]; ring
      _ ≤ 1.0001 := hcube
  have hcard : (Hlen m hne : ℝ) ≤ 2 / 3 * ((m : ℝ) + 1) ^ ((1 : ℝ) / 3) + 1 := by
    rw [Hlen_eq hne]
    exact oeFiber_card_le m
  have hmul := mul_le_mul_of_nonneg_left hcard hepos.le
  have heps := eps_le hm
  nlinarith [hmul, hkey, heps, hepos]

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


/-! ### Lemma 2: the lock -/

/-- **Lemma 2 (lock).** A fiber whose parity share misses `1/2` by `η₀` or more has `A_m`
within `32/(η₀ H_m)` of a rational with denominator at most `3.77/η₀`.

The note's proof, with Dirichlet in place of the continued fractions it first used: take
`θ = η₀/16` and `H₀ = ⌊θ H_m⌋`, get `q ≤ H₀` and `‖q A_m‖ ≤ 1/(H₀+1)` from
`exists_coprime_approx` (which also supplies the coprimality `block_lock` wants), and feed
them to `fiber_block_lock`. Of the three terms there, `4ρH ≤ 128/η₀` is at most `η₀H/10`
exactly when `H_m ≥ 1280/η₀²`, and `4qε_mH + q ≤ 3.71q` by (F3), which is at most
`0.232 η₀ H` because `q ≤ θH`. What is left is `0.668 η₀ ≤ 5/(2q)`. -/
theorem fiber_lock {m : ℕ} (hm : 10 ^ 6 ≤ m) (hne : (oeFiber m).Nonempty)
    {η₀ : ℝ} (hη0 : 0 < η₀) (hη1 : η₀ ≤ 1 / 2)
    (hH : 1280 / η₀ ^ 2 ≤ (Hlen m hne : ℝ))
    (hdev : η₀ * (Hlen m hne : ℝ) ≤ |(evenImageCount m : ℝ) - (Hlen m hne : ℝ) / 2|) :
    ∃ q : ℕ, 1 ≤ q ∧ (q : ℝ) ≤ 3.77 / η₀ ∧
      ∃ P : ℤ, |(q : ℝ) * Am m - (P : ℝ)| ≤ 32 / (η₀ * (Hlen m hne : ℝ)) := by
  have hm1 : 1 ≤ m := by omega
  set H : ℝ := (Hlen m hne : ℝ) with hHdef
  have h1280 : (0 : ℝ) < 1280 / η₀ ^ 2 := by positivity
  have hHpos : 0 < H := lt_of_lt_of_le h1280 hH
  -- `θ H ≥ 160`, so the Dirichlet parameter is a positive natural
  have hθH : (160 : ℝ) ≤ η₀ / 16 * H := by
    have : (1280 : ℝ) / η₀ ^ 2 ≤ H := hH
    have hsq : 0 < η₀ ^ 2 := by positivity
    rw [div_le_iff₀ hsq] at this
    nlinarith [hη0, hη1]
  set H0 : ℕ := ⌊η₀ / 16 * H⌋₊ with hH0def
  have hH0R : (H0 : ℝ) ≤ η₀ / 16 * H := Nat.floor_le (by linarith)
  have hH0lt : η₀ / 16 * H - 1 < (H0 : ℝ) := by
    have := Nat.lt_floor_add_one (η₀ / 16 * H)
    linarith
  have hH0pos : 0 < H0 := Nat.floor_pos.mpr (by linarith)
  have hH0half : η₀ / 16 * H / 2 ≤ (H0 : ℝ) := by linarith
  -- Dirichlet, in lowest terms
  obtain ⟨q, P, hq1, hqH0, hcop, happ⟩ := exists_coprime_approx (Am m) hH0pos
  have hq0R : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq1
  have hqH0R : (q : ℝ) ≤ (H0 : ℝ) := by exact_mod_cast hqH0
  have hH0R0 : (0 : ℝ) < (H0 : ℝ) := by exact_mod_cast hH0pos
  -- `ρ = 1/(H₀+1)` is at most `32/(η₀ H)`
  set ρ : ℝ := 1 / ((H0 : ℝ) + 1) with hρdef
  have hρ0 : 0 ≤ ρ := by positivity
  have hd1 : (0 : ℝ) < (H0 : ℝ) + 1 := by positivity
  have hρH : ρ * H ≤ 32 / η₀ := by
    rw [hρdef, div_mul_eq_mul_div, one_mul, div_le_div_iff₀ hd1 hη0]
    linarith [hH0half]
  have hρle : ρ ≤ 32 / (η₀ * H) := by
    rw [hρdef, div_le_div_iff₀ hd1 (by positivity : (0 : ℝ) < η₀ * H)]
    linarith [hH0half]
  refine ⟨q, hq1, ?_, P, le_trans happ hρle⟩
  -- the block lock, and the three terms
  have hbl := fiber_block_lock hm1 hne hq1 hρ0 hcop happ
  rw [← hHdef] at hbl
  have hchain : η₀ * H ≤ 4 * (ρ + (q : ℝ) * eps m) * H + 5 * H / (2 * (q : ℝ)) + (q : ℝ) :=
    le_trans hdev hbl
  -- term one: `4 ρ H ≤ η₀ H / 10`
  have hterm1 : 4 * ρ * H ≤ η₀ * H / 10 := by
    have h1 : ρ * H ≤ 32 / η₀ := hρH
    have h2 : (128 : ℝ) / η₀ ≤ η₀ * H / 10 := by
      rw [div_le_iff₀ hη0]
      have hsq : 0 < η₀ ^ 2 := by positivity
      have := hH
      rw [div_le_iff₀ hsq] at this
      nlinarith
    have h3 : 4 * (ρ * H) ≤ 128 / η₀ := by
      have h4 : (128 : ℝ) / η₀ = 4 * (32 / η₀) := by ring
      rw [h4]
      linarith [h1]
    linarith [h3, h2]
  -- term two: `4 q ε_m H + q ≤ 3.71 q`, by (F3)
  have hF3 := eps_mul_Hlen_le hm hne
  rw [← hHdef] at hF3
  have hterm2 : 4 * ((q : ℝ) * eps m) * H + (q : ℝ) ≤ 3.71 * (q : ℝ) := by
    nlinarith [hF3, hq0R, eps_pos hm1]
  -- and `3.71 q ≤ 0.232 η₀ H` because `q ≤ θ H`
  have hterm3 : 3.71 * (q : ℝ) ≤ 0.232 * (η₀ * H) := by
    have : (q : ℝ) ≤ η₀ / 16 * H := le_trans hqH0R hH0R
    nlinarith [this, hη0, hHpos]
  -- what is left
  have hleft : 0.668 * (η₀ * H) ≤ 5 * H / (2 * (q : ℝ)) := by nlinarith [hchain, hterm1, hterm2, hterm3]
  have hdiv : 0.668 * η₀ ≤ 5 / (2 * (q : ℝ)) := by
    have hrw : 5 * H / (2 * (q : ℝ)) = 5 / (2 * (q : ℝ)) * H := by ring
    rw [hrw] at hleft
    exact le_of_mul_le_mul_right (by linarith [hleft]) hHpos
  rw [le_div_iff₀ (by positivity)] at hdiv
  rw [le_div_iff₀ hη0]
  linarith [hdiv]

end FiberParity

end Problems.Juggler
