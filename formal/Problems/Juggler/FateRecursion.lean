import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace Problems.Juggler

open Finset

/-!
# The recursion lemma of the fate-contagion paper

Paper C (`docs/theory/juggler_fate_almost_all_note.md`), Lemma 5.1: a
functional inequality with vanishing errors,

  `g t ≥ Σ_i (c_i - η_i t) · g (e_i t) - η₀ t`   for all `t ≥ t₁`,

forces the power lower bound `g t ≥ K t^λ` for all `t ≥ e_min t₁`, where
`λ` is any exponent with `ζ := Σ_i c_i e_i^λ - 1 > 0`, the errors are
small against `ζ` (`Σ_i η_i t e_i^λ ≤ ζ/3` and `η₀ t ≤ (2ζ/3) c₀`), the
seed `g ≥ c₀ > 0` holds on `[e_min t₁, t₁]`, and `K = c₀ t₁^{-λ}`.

This is the analytic step that turns the three-source inequality (5.2)
into the logarithmic-density bound of Theorem 5.3, and the only step of
that proof that is a statement about an abstract function rather than
about the Juggler map. Nothing here mentions `floorPower`; the Juggler
content of Theorem 5.3 (the sources, their constants, the seed) stays a
human proof. Not a density theorem, not a halt theorem.

The proof is the paper's: on `[e_min t₁, t₁]` the bound is the seed;
if it holds on `[e_min t₁, T]` with `T ≥ t₁`, every `t ∈ (T, T/e_max]`
has all of `e_i t` inside the known range, and the inequality gives
`g t ≥ K t^λ (1 + 2ζ/3) - (2ζ/3) c₀ ≥ K t^λ` because `K t^λ ≥ K t₁^λ = c₀`.
Induction on the number of steps `t₁ e_max^{-N}` covers every `t`.
-/

/-- Paper C Lemma 5.1 (recursion lemma), with the range of the contraction
factors given by two bounds `emin ≤ e i ≤ emax` rather than by a finite
minimum and maximum. `K = c₀ * t₁ ^ (-λ)`. -/
theorem recursion_lemma {r : ℕ} (e c : Fin r → ℝ) (η : Fin r → ℝ → ℝ)
    (η₀ : ℝ → ℝ) (g : ℝ → ℝ) (lam t₁ c₀ emin emax : ℝ)
    (hlam : 0 < lam) (ht₁ : 0 < t₁) (hc₀ : 0 < c₀)
    (hemin : 0 < emin) (hemax : emax < 1)
    (he_lo : ∀ i, emin ≤ e i) (he_hi : ∀ i, e i ≤ emax)
    (hζ : 0 < ∑ i, c i * e i ^ lam - 1)
    (hη_lo : ∀ t, t₁ ≤ t → ∀ i, 0 ≤ η i t)
    (hη_hi : ∀ t, t₁ ≤ t → ∀ i, η i t ≤ c i)
    (hη₀ : ∀ t, t₁ ≤ t → η₀ t ≤ 2 * (∑ i, c i * e i ^ lam - 1) / 3 * c₀)
    (hηsum : ∀ t, t₁ ≤ t → ∑ i, η i t * e i ^ lam ≤ (∑ i, c i * e i ^ lam - 1) / 3)
    (hseed : ∀ t, emin * t₁ ≤ t → t ≤ t₁ → c₀ ≤ g t)
    (hrec : ∀ t, t₁ ≤ t → ∑ i, (c i - η i t) * g (e i * t) - η₀ t ≤ g t) :
    ∀ t, emin * t₁ ≤ t → c₀ * t₁ ^ (-lam) * t ^ lam ≤ g t := by
  -- if `r = 0` the sum is empty and `hζ` is false
  have hr : 0 < r := by
    rcases Nat.eq_zero_or_pos r with h | h
    · subst h
      simp at hζ
      linarith
    · exact h
  set ζ : ℝ := ∑ i, c i * e i ^ lam - 1 with hζdef
  set K : ℝ := c₀ * t₁ ^ (-lam) with hKdef
  have hK : 0 < K := mul_pos hc₀ (Real.rpow_pos_of_pos ht₁ _)
  have hemax0 : 0 < emax := lt_of_lt_of_le hemin (le_trans (he_lo ⟨0, hr⟩) (he_hi _))
  -- `K t₁^λ = c₀`
  have hKt₁ : K * t₁ ^ lam = c₀ := by
    rw [hKdef, mul_assoc, ← Real.rpow_add ht₁]
    simp
  -- the bound on one step from a known range
  have hstep : ∀ T, t₁ ≤ T →
      (∀ t, emin * t₁ ≤ t → t ≤ T → K * t ^ lam ≤ g t) →
      ∀ t, emin * t₁ ≤ t → t ≤ T / emax → K * t ^ lam ≤ g t := by
    intro T hT ih t ht0 htT
    by_cases hle : t ≤ T
    · exact ih t ht0 hle
    replace hle := not_le.mp hle
    have ht₁t : t₁ ≤ t := le_trans hT hle.le
    have htpos : 0 < t := lt_of_lt_of_le ht₁ ht₁t
    -- each `e i * t` lies in the known range
    have hin : ∀ i, K * (e i * t) ^ lam ≤ g (e i * t) := by
      intro i
      apply ih
      · calc emin * t₁ ≤ emin * t := by
              apply mul_le_mul_of_nonneg_left ht₁t hemin.le
          _ ≤ e i * t := mul_le_mul_of_nonneg_right (he_lo i) htpos.le
      · calc e i * t ≤ emax * t := mul_le_mul_of_nonneg_right (he_hi i) htpos.le
          _ ≤ T := by
              rw [le_div_iff₀ hemax0] at htT
              linarith
    have hei : ∀ i, 0 ≤ e i := fun i => le_trans hemin.le (he_lo i)
    have hcη : ∀ i, 0 ≤ c i - η i t := fun i => by
      have := hη_hi t ht₁t i
      linarith
    -- lower bound the sum
    have hsum : ∑ i, (c i - η i t) * (K * (e i ^ lam * t ^ lam)) ≤
        ∑ i, (c i - η i t) * g (e i * t) := by
      apply Finset.sum_le_sum
      intro i _
      apply mul_le_mul_of_nonneg_left _ (hcη i)
      rw [← Real.mul_rpow (hei i) htpos.le]
      exact hin i
    have hexpand : ∑ i, (c i - η i t) * (K * (e i ^ lam * t ^ lam)) =
        K * t ^ lam * (∑ i, c i * e i ^ lam - ∑ i, η i t * e i ^ lam) := by
      rw [mul_sub, Finset.mul_sum, Finset.mul_sum]
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring
    have hζ3 := hηsum t ht₁t
    have hη0 := hη₀ t ht₁t
    have hKt : c₀ ≤ K * t ^ lam := by
      rw [← hKt₁]
      apply mul_le_mul_of_nonneg_left _ hK.le
      exact Real.rpow_le_rpow ht₁.le ht₁t hlam.le
    have hKt0 : 0 ≤ K * t ^ lam := le_trans hc₀.le hKt
    have hrec' := hrec t ht₁t
    -- `K t^λ (1 + ζ - ζ/3) - (2ζ/3) c₀ ≥ K t^λ`
    have hsum_lo : K * t ^ lam * (1 + 2 * ζ / 3) ≤
        ∑ i, (c i - η i t) * (K * (e i ^ lam * t ^ lam)) := by
      rw [hexpand]
      apply mul_le_mul_of_nonneg_left _ hKt0
      rw [hζdef] at hζ3 ⊢
      linarith
    have hmain : K * t ^ lam ≤ K * t ^ lam * (1 + 2 * ζ / 3) - η₀ t := by
      have h1 : 2 * ζ / 3 * c₀ ≤ 2 * ζ / 3 * (K * t ^ lam) :=
        mul_le_mul_of_nonneg_left hKt (by positivity)
      nlinarith
    linarith
  -- induction on the number of steps
  have hN : ∀ N : ℕ, ∀ t, emin * t₁ ≤ t → t ≤ t₁ / emax ^ N → K * t ^ lam ≤ g t := by
    intro N
    induction N with
    | zero =>
        intro t ht0 ht1
        simp only [pow_zero, div_one] at ht1
        have htpos : 0 < t := lt_of_lt_of_le (mul_pos hemin ht₁) ht0
        calc K * t ^ lam ≤ K * t₁ ^ lam := by
              apply mul_le_mul_of_nonneg_left _ hK.le
              exact Real.rpow_le_rpow htpos.le ht1 hlam.le
          _ = c₀ := hKt₁
          _ ≤ g t := hseed t ht0 ht1
    | succ N ih =>
        have hTN : t₁ ≤ t₁ / emax ^ N := by
          rw [le_div_iff₀ (pow_pos hemax0 N)]
          have : emax ^ N ≤ 1 := pow_le_one₀ hemax0.le hemax.le
          nlinarith
        have := hstep (t₁ / emax ^ N) hTN ih
        intro t ht0 ht1
        apply this t ht0
        rw [pow_succ, ← div_div] at ht1
        exact ht1
  intro t ht0
  have htpos : 0 < t := lt_of_lt_of_le (mul_pos hemin ht₁) ht0
  obtain ⟨N, hN'⟩ := exists_pow_lt_of_lt_one (div_pos ht₁ htpos) hemax
  apply hN N t ht0
  rw [le_div_iff₀ (pow_pos hemax0 N)]
  rw [lt_div_iff₀ htpos] at hN'
  linarith

end Problems.Juggler
