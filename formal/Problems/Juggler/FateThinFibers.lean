import Mathlib.Algebra.Order.Field.GeomSum
import Problems.Juggler.FateFiberParity

namespace Problems.Juggler

open Finset
open scoped Classical

namespace FiberParity

/-!
# Thin fibers: Lemma 4.3 of the fate-contagion paper

Paper C (`docs/theory/juggler_fate_almost_all_note.md`), Lemma 4.3: for `u ≥ 10^6` at
most `63 u^{2/3}` of the `m ∈ (u, 2u]` are bad, and the bad `m > U` carry log-mass at most
`306 U^{-1/3}`.

The proof is the paper's count. `φ(m) = A_m = (3/2) m^{2/3}` increases by
`φ(m+1) - φ(m) ∈ [(m+1)^{-1/3}, m^{-1/3}]` (Bernoulli both ways, `Am_step_ge`,
`Am_step_le`). A bad `m > u` has `{φ(m)}` within `22 u^{-1/3}` of an integer or within
`2 u^{-1/3}` of `1/2`; after the shift `φ + 22 u^{-1/3}` the first arc is a single arc
`[0, 44 u^{-1/3})`, so badness is membership in one of two arcs of total width `48 u^{-1/3}`
(`bad_mem_arc`). On an arc of width `w`, a sequence increasing by at least `d` per step visits
at most `w/d + 1` points per integer window, and the number of windows met on `(u, 2u]` is at
most `φ(2u) - φ(u) + 2 ≤ 0.882 u^{2/3} + 2` (`arc_count_le`, the fibre-per-window count of
`FateSweep`). With `d = (2u)^{-1/3}`, sharper than the paper's `(3u)^{-1/3}`, the two arcs
give `w/d = 44 · 2^{1/3}` and `4 · 2^{1/3}`, and the total is
`(0.882 u^{2/3} + 2)(48 · 2^{1/3} + 2) ≤ 63 u^{2/3}` for `u ≥ 10^6` (`bad_count_le`). The
log-mass bound is the dyadic sum `Σ_i 63 (2^i U)^{-1/3} ≤ 63 U^{-1/3}/(1 - 2^{-1/3})`
(`bad_logMass_le`). Not a statement about good fibers; not a halt theorem.
-/

/-! ### The arc count -/

/-- A sequence increasing by at least `d` per step on `(u, v]` spans at least `(m' - m) d`
between two of its indices. -/
theorem span_ge_of_step {φ : ℕ → ℝ} {u v : ℕ} {d : ℝ}
    (hstep : ∀ m, u < m → m < v → d ≤ φ (m + 1) - φ m) :
    ∀ k m, u < m → m + k ≤ v → (k : ℝ) * d ≤ φ (m + k) - φ m := by
  intro k
  induction k with
  | zero => intro m _ _; simp
  | succ k ih =>
      intro m hm hk
      have h1 := ih m hm (by omega)
      have h2 := hstep (m + k) (by omega) (by omega)
      rw [← add_assoc]
      push_cast
      linarith

/-- **The arc count.** If `φ` increases by at least `d > 0` per step on `(u, v]`, the
indices `m ∈ (u, v]` with `{φ(m)} ∈ [c, c + w)` number at most
`(⌊φ(v)⌋ - ⌊φ(u+1)⌋ + 1)(w/d + 1)`: within one integer window the points are `d`-separated
inside an interval of length `w`. -/
theorem arc_count_le (φ : ℕ → ℝ) (u v : ℕ) (huv : u < v) (d c w : ℝ) (hd : 0 < d)
    (hw : 0 ≤ w) (hstep : ∀ m, u < m → m < v → d ≤ φ (m + 1) - φ m) :
    (#{m ∈ Finset.Ioc u v | c ≤ Int.fract (φ m) ∧ Int.fract (φ m) < c + w} : ℝ) ≤
      ((⌊φ v⌋ - ⌊φ (u + 1)⌋ + 1 : ℤ) : ℝ) * (w / d + 1) := by
  -- monotonicity on `(u, v]`
  have hmono : ∀ m m', u < m → m ≤ m' → m' ≤ v → φ m ≤ φ m' := by
    intro m m' hm hmm' hm'v
    have := span_ge_of_step hstep (m' - m) m hm (by omega)
    rw [Nat.add_sub_cancel' hmm'] at this
    have : (0 : ℝ) ≤ ((m' - m : ℕ) : ℝ) * d := by positivity
    linarith
  set S := {m ∈ Finset.Ioc u v | c ≤ Int.fract (φ m) ∧ Int.fract (φ m) < c + w} with hS
  set W := Finset.Icc ⌊φ (u + 1)⌋ ⌊φ v⌋ with hW
  have hmaps : ((S : Finset ℕ) : Set ℕ).MapsTo (fun m => ⌊φ m⌋) (W : Set ℤ) := by
    intro m hm
    rw [Finset.mem_coe, hS, Finset.mem_filter, Finset.mem_Ioc] at hm
    rw [Finset.mem_coe, hW, Finset.mem_Icc]
    exact ⟨Int.floor_le_floor (hmono _ _ (by omega) (by omega) hm.1.2),
      Int.floor_le_floor (hmono _ _ hm.1.1 hm.1.2 le_rfl)⟩
  have hfib := Finset.card_eq_sum_card_fiberwise hmaps
  -- each window holds at most `w/d + 1` of the points
  have hwin : ∀ k ∈ W, (#{m ∈ S | ⌊φ m⌋ = k} : ℝ) ≤ w / d + 1 := by
    intro k _
    set T := {m ∈ S | ⌊φ m⌋ = k} with hT
    by_cases hne : T.Nonempty
    · set m₀ := T.min' hne
      set m₁ := T.max' hne
      have h₀ : m₀ ∈ T := Finset.min'_mem _ hne
      have h₁ : m₁ ∈ T := Finset.max'_mem _ hne
      have h₀₁ : m₀ ≤ m₁ := Finset.min'_le _ _ h₁
      rw [hT, Finset.mem_filter, hS, Finset.mem_filter, Finset.mem_Ioc] at h₀ h₁
      have hsub : T ⊆ Finset.Icc m₀ m₁ := by
        intro m hm
        rw [Finset.mem_Icc]
        exact ⟨Finset.min'_le _ _ hm, Finset.le_max' _ _ hm⟩
      have hcard : T.card ≤ m₁ + 1 - m₀ := by
        have := Finset.card_le_card hsub
        rwa [Nat.card_Icc] at this
      -- `φ m₀ ≥ k + c` and `φ m₁ < k + c + w`
      have hlo : (k : ℝ) + c ≤ φ m₀ := by
        have := Int.floor_add_fract (φ m₀)
        rw [h₀.2] at this
        linarith [h₀.1.2.1]
      have hhi : φ m₁ < k + c + w := by
        have := Int.floor_add_fract (φ m₁)
        rw [h₁.2] at this
        linarith [h₁.1.2.2]
      have hspan := span_ge_of_step hstep (m₁ - m₀) m₀ h₀.1.1.1 (by omega)
      rw [Nat.add_sub_cancel' h₀₁] at hspan
      have hlt : ((m₁ - m₀ : ℕ) : ℝ) < w / d := by
        rw [lt_div_iff₀ hd]
        linarith
      have hcard' : (T.card : ℝ) ≤ ((m₁ - m₀ : ℕ) : ℝ) + 1 := by
        have : T.card ≤ (m₁ - m₀) + 1 := by omega
        exact_mod_cast this
      linarith
    · rw [Finset.not_nonempty_iff_eq_empty] at hne
      rw [hne]
      simp
      positivity
  have hsum : (S.card : ℝ) ≤ (W.card : ℝ) * (w / d + 1) := by
    rw [hfib]
    push_cast
    have := Finset.sum_le_card_nsmul W (fun k => (#{m ∈ S | ⌊φ m⌋ = k} : ℝ)) (w / d + 1) hwin
    rw [nsmul_eq_mul] at this
    exact this
  have hWcard : (W.card : ℝ) = ((⌊φ v⌋ - ⌊φ (u + 1)⌋ + 1 : ℤ) : ℝ) := by
    rw [hW, Int.card_Icc]
    have hle : ⌊φ (u + 1)⌋ ≤ ⌊φ v⌋ :=
      Int.floor_le_floor (hmono _ _ (by omega) (by omega) le_rfl)
    have : ((⌊φ v⌋ + 1 - ⌊φ (u + 1)⌋).toNat : ℤ) = ⌊φ v⌋ + 1 - ⌊φ (u + 1)⌋ :=
      Int.toNat_of_nonneg (by omega)
    have h2 : (((⌊φ v⌋ + 1 - ⌊φ (u + 1)⌋).toNat : ℕ) : ℝ) =
        (((⌊φ v⌋ + 1 - ⌊φ (u + 1)⌋).toNat : ℤ) : ℝ) := by norm_cast
    rw [h2, this]
    push_cast
    ring
  rw [hWcard] at hsum
  exact hsum

/-! ### The increments of `A_m` -/

theorem Am_step_le {m : ℕ} (hm : 1 ≤ m) : Am (m + 1) - Am m ≤ eps m := by
  unfold Am eps
  have := rpow_two_thirds_succ_le hm
  push_cast
  linarith

/-- Bernoulli, the other way: `(m+1)^{2/3} - m^{2/3} ≥ (2/3) (m+1)^{-1/3}`. -/
theorem Am_step_ge {m : ℕ} (hm : 1 ≤ m) : eps (m + 1) ≤ Am (m + 1) - Am m := by
  unfold Am eps
  push_cast
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  -- Bernoulli at `m + 1` with `h = -1`: `m^{2/3} ≤ (m+1)^{2/3} - (2/3)(m+1)^{-1/3}`
  have hb := Numerics.bernoulli_le (a := (m : ℝ) + 1) (h := -1) (p := (2 : ℝ) / 3)
    (q := -((1 : ℝ) / 3)) (by positivity) (by linarith) (by norm_num) (by norm_num) (by norm_num)
  rw [show (m : ℝ) + 1 + -1 = m by ring] at hb
  linarith

/-- `ε` is antitone: `eps m ≤ eps u` for `1 ≤ u ≤ m`. -/
theorem eps_antitone {u m : ℕ} (hu : 1 ≤ u) (hum : u ≤ m) : eps m ≤ eps u := by
  unfold eps
  exact Real.rpow_le_rpow_of_nonpos (by exact_mod_cast hu) (by exact_mod_cast hum) (by norm_num)

/-! ### Badness is membership in one of two arcs -/

/-- A bad `m > u ≥ 10^6` has `{A_m + 22 ε_u} < 44 ε_u` or `{A_m} ∈ [1/2 - 2ε_u, 1/2 + 2ε_u)`. -/
theorem bad_mem_arc {u m : ℕ} (hu : 10 ^ 6 ≤ u) (hm : u < m) (hbad : ¬ Good m) :
    Int.fract (Am m + 22 * eps u) < 44 * eps u ∨
      (1 / 2 - 2 * eps u ≤ Int.fract (Am m) ∧ Int.fract (Am m) < 1 / 2 + 2 * eps u) := by
  have hεu := eps_le hu
  have hεpos := eps_pos (m := u) (by omega)
  have hεm : eps m ≤ eps u := eps_antitone (by omega) hm.le
  have hεm0 := eps_pos (m := m) (by omega)
  set α := Int.fract (Am m) with hα
  have hα0 : 0 ≤ α := Int.fract_nonneg _
  have hα1 : α < 1 := Int.fract_lt_one _
  have hfloor : Am m - α = ⌊Am m⌋ := Int.self_sub_fract _
  unfold Good alpha at hbad
  rw [← hα] at hbad
  by_cases h1 : α < 22 * eps m
  · left
    -- `{A_m + 22ε_u} = α + 22ε_u`
    have : Int.fract (Am m + 22 * eps u) = α + 22 * eps u := by
      rw [Int.fract_eq_iff]
      refine ⟨by linarith, by linarith, ⌊Am m⌋, ?_⟩
      linarith
    rw [this]
    linarith
  by_cases h2 : 1 - 22 * eps m < α
  · left
    -- `{A_m + 22ε_u} = α + 22ε_u - 1`
    have : Int.fract (Am m + 22 * eps u) = α + 22 * eps u - 1 := by
      rw [Int.fract_eq_iff]
      refine ⟨by linarith, by linarith, ⌊Am m⌋ + 1, ?_⟩
      push_cast
      linarith
    rw [this]
    linarith
  · right
    push Not at h1 h2
    have h3 : ¬ (α ≤ 1 / 2 - 2 * eps m ∨ 1 / 2 + 2 * eps m ≤ α) := by
      intro h
      exact hbad ⟨h1, h2, h⟩
    push Not at h3
    constructor <;> linarith [h3.1, h3.2]

/-! ### Numerical constants -/

theorem two_rpow_third_le : (2 : ℝ) ^ ((1 : ℝ) / 3) ≤ 1.26 := by
  rw [Numerics.rpow_le_iff_pow (n := 3) (by norm_num) (by norm_num) (by norm_num)]
  norm_num

theorem two_rpow_two_thirds_le : (2 : ℝ) ^ ((2 : ℝ) / 3) ≤ 1.588 := by
  rw [Numerics.rpow_le_iff_pow (n := 3) (by norm_num) (by norm_num) (by norm_num)]
  norm_num

/-- `u^{2/3} ≥ 10^4` for `u ≥ 10^6`. -/
theorem rpow_two_thirds_ge {u : ℕ} (hu : 10 ^ 6 ≤ u) : (10000 : ℝ) ≤ (u : ℝ) ^ ((2 : ℝ) / 3) := by
  rw [Numerics.le_rpow_iff_pow (n := 3) (by positivity) (by norm_num) (by norm_num)]
  have h6 : (10 ^ 6 : ℝ) ≤ u := by exact_mod_cast hu
  norm_num
  exact le_trans (by norm_num) (pow_le_pow_left₀ (by norm_num) h6 2)

/-- `ε_u / ε_{2u} = 2^{1/3}`. -/
theorem eps_div_eps_double {u : ℕ} (hu : 1 ≤ u) : eps u / eps (2 * u) = (2 : ℝ) ^ ((1 : ℝ) / 3) := by
  unfold eps
  have hu0 : (0 : ℝ) < u := by exact_mod_cast hu
  push_cast
  rw [← Real.div_rpow hu0.le (by positivity)]
  rw [show (u : ℝ) / (2 * u) = 1 / 2 by rw [div_eq_iff (by positivity)]; ring]
  rw [Real.rpow_neg (by norm_num), one_div, Real.inv_rpow (by norm_num), inv_inv]

/-- `A_{2u} - A_u = (3/2)(2^{2/3} - 1) u^{2/3} ≤ 0.882 u^{2/3}`. -/
theorem Am_double_sub_le {u : ℕ} (hu : 1 ≤ u) :
    Am (2 * u) - Am u ≤ 0.882 * (u : ℝ) ^ ((2 : ℝ) / 3) := by
  unfold Am
  have hu0 : (0 : ℝ) ≤ u := by positivity
  push_cast
  rw [Real.mul_rpow (by norm_num) hu0]
  have h := two_rpow_two_thirds_le
  have hp : 0 ≤ (u : ℝ) ^ ((2 : ℝ) / 3) := Real.rpow_nonneg hu0 _
  nlinarith

/-! ### Lemma 4.3, first part: the count on `(u, 2u]` -/

/-- **Lemma 4.3, the count.** For `u ≥ 10^6`, at most `63 u^{2/3}` of the `m ∈ (u, 2u]`
are bad. -/
theorem bad_count_le {u : ℕ} (hu : 10 ^ 6 ≤ u) :
    (#{m ∈ Finset.Ioc u (2 * u) | ¬ Good m} : ℝ) ≤ 63 * (u : ℝ) ^ ((2 : ℝ) / 3) := by
  have hu1 : 1 ≤ u := by omega
  have hεu := eps_le hu
  have hεpos := eps_pos (m := u) hu1
  set ε := eps u with hε
  set d := eps (2 * u) with hd
  have hdpos : 0 < d := eps_pos (by omega)
  -- the increments on `(u, 2u)` are at least `d`
  have hstep : ∀ m, u < m → m < 2 * u → d ≤ Am (m + 1) - Am m := by
    intro m hm hm2
    refine le_trans ?_ (Am_step_ge (by omega))
    exact eps_antitone (by omega) (by omega)
  have hstep' : ∀ m, u < m → m < 2 * u → d ≤ (Am (m + 1) + 22 * ε) - (Am m + 22 * ε) := by
    intro m hm hm2
    have := hstep m hm hm2
    linarith
  -- the two arcs
  set B₁ := {m ∈ Finset.Ioc u (2 * u) | (0 : ℝ) ≤ Int.fract (Am m + 22 * ε) ∧
    Int.fract (Am m + 22 * ε) < 0 + 44 * ε} with hB₁
  set B₂ := {m ∈ Finset.Ioc u (2 * u) | 1 / 2 - 2 * ε ≤ Int.fract (Am m) ∧
    Int.fract (Am m) < 1 / 2 - 2 * ε + 4 * ε} with hB₂
  have hcover : {m ∈ Finset.Ioc u (2 * u) | ¬ Good m} ⊆ B₁ ∪ B₂ := by
    intro m hm
    rw [Finset.mem_filter, Finset.mem_Ioc] at hm
    rw [Finset.mem_union, hB₁, hB₂, Finset.mem_filter, Finset.mem_filter, Finset.mem_Ioc]
    rcases bad_mem_arc hu hm.1.1 hm.2 with h | h
    · rw [← hε] at h
      left; exact ⟨hm.1, Int.fract_nonneg _, by linarith⟩
    · rw [← hε] at h
      right; exact ⟨hm.1, h.1, by linarith [h.2]⟩
  have hcard : (#{m ∈ Finset.Ioc u (2 * u) | ¬ Good m} : ℝ) ≤ B₁.card + B₂.card := by
    have := le_trans (Finset.card_le_card hcover) (Finset.card_union_le _ _)
    exact_mod_cast this
  -- the arc counts
  have hA₁ := arc_count_le (fun m => Am m + 22 * ε) u (2 * u) (by omega) d 0 (44 * ε) hdpos
    (by positivity) hstep'
  have hA₂ := arc_count_le Am u (2 * u) (by omega) d (1 / 2 - 2 * ε) (4 * ε) hdpos
    (by positivity) hstep
  -- the number of windows, both sequences
  have hwin : ∀ ψ : ℕ → ℝ, ((∀ m, ψ m = Am m) ∨ (∀ m, ψ m = Am m + 22 * ε)) →
      ((⌊ψ (2 * u)⌋ - ⌊ψ (u + 1)⌋ + 1 : ℤ) : ℝ) ≤ 0.882 * (u : ℝ) ^ ((2 : ℝ) / 3) + 2 := by
    intro ψ hψ
    have hA : Am u ≤ Am (u + 1) := by
      have := Am_step_ge (m := u) hu1
      have := eps_pos (m := u + 1) (by omega)
      linarith
    have hdouble := Am_double_sub_le hu1
    have h1 : (⌊ψ (2 * u)⌋ : ℝ) ≤ ψ (2 * u) := Int.floor_le _
    have h2 : ψ (u + 1) < ⌊ψ (u + 1)⌋ + 1 := Int.lt_floor_add_one _
    have hdiff : ψ (2 * u) - ψ (u + 1) = Am (2 * u) - Am (u + 1) := by
      rcases hψ with h | h
      · rw [h, h]
      · rw [h, h]; ring
    push_cast
    linarith
  have hW₁ := hwin (fun m => Am m + 22 * ε) (Or.inr (fun m => rfl))
  have hW₂ := hwin Am (Or.inl (fun m => rfl))
  -- `w/d`: `44 ε / d = 44 · 2^{1/3} ≤ 55.44`, `4 ε / d ≤ 5.04`
  have hratio : ε / d = (2 : ℝ) ^ ((1 : ℝ) / 3) := eps_div_eps_double hu1
  have h2c := two_rpow_third_le
  have hr1 : 44 * ε / d + 1 ≤ 56.44 := by
    rw [show 44 * ε / d = 44 * (ε / d) by ring, hratio]; linarith
  have hr2 : 4 * ε / d + 1 ≤ 6.04 := by
    rw [show 4 * ε / d = 4 * (ε / d) by ring, hratio]; linarith
  have hu23 := rpow_two_thirds_ge hu
  have hW0 : (0 : ℝ) ≤ 0.882 * (u : ℝ) ^ ((2 : ℝ) / 3) + 2 := by positivity
  -- assemble
  have hB₁le : (B₁.card : ℝ) ≤ (0.882 * (u : ℝ) ^ ((2 : ℝ) / 3) + 2) * 56.44 := by
    refine le_trans hA₁ ?_
    have hpos : (0 : ℝ) ≤ 44 * ε / d + 1 := by positivity
    calc ((⌊(fun m => Am m + 22 * ε) (2 * u)⌋ - ⌊(fun m => Am m + 22 * ε) (u + 1)⌋ + 1 : ℤ) : ℝ)
          * (44 * ε / d + 1)
        ≤ (0.882 * (u : ℝ) ^ ((2 : ℝ) / 3) + 2) * (44 * ε / d + 1) :=
          mul_le_mul_of_nonneg_right hW₁ hpos
      _ ≤ (0.882 * (u : ℝ) ^ ((2 : ℝ) / 3) + 2) * 56.44 :=
          mul_le_mul_of_nonneg_left hr1 hW0
  have hB₂le : (B₂.card : ℝ) ≤ (0.882 * (u : ℝ) ^ ((2 : ℝ) / 3) + 2) * 6.04 := by
    refine le_trans hA₂ ?_
    have hpos : (0 : ℝ) ≤ 4 * ε / d + 1 := by positivity
    calc ((⌊Am (2 * u)⌋ - ⌊Am (u + 1)⌋ + 1 : ℤ) : ℝ) * (4 * ε / d + 1)
        ≤ (0.882 * (u : ℝ) ^ ((2 : ℝ) / 3) + 2) * (4 * ε / d + 1) :=
          mul_le_mul_of_nonneg_right hW₂ hpos
      _ ≤ (0.882 * (u : ℝ) ^ ((2 : ℝ) / 3) + 2) * 6.04 :=
          mul_le_mul_of_nonneg_left hr2 hW0
  -- `(0.882 u^{2/3} + 2) · 62.48 ≤ 63 u^{2/3}` for `u^{2/3} ≥ 10^4`
  nlinarith

/-! ### Lemma 4.3, second part: the log-mass of the bad fibers -/

/-- On one dyadic block `(u, 2u]`, `u ≥ 10^6`, the bad fibers carry log-mass at most
`63 u^{-1/3}`. -/
theorem bad_block_logMass_le {u : ℕ} (hu : 10 ^ 6 ≤ u) :
    (∑ m ∈ {m ∈ Finset.Ioc u (2 * u) | ¬ Good m}, (1 : ℝ) / m) ≤ 63 * eps u := by
  have hu0 : (0 : ℝ) < u := by exact_mod_cast (by omega : 0 < u)
  have hcount := bad_count_le hu
  have hterm : ∀ m ∈ {m ∈ Finset.Ioc u (2 * u) | ¬ Good m}, (1 : ℝ) / m ≤ 1 / u := by
    intro m hm
    rw [Finset.mem_filter, Finset.mem_Ioc] at hm
    exact one_div_le_one_div_of_le hu0 (by exact_mod_cast hm.1.1.le)
  have hsum := Finset.sum_le_card_nsmul _ _ _ hterm
  rw [nsmul_eq_mul] at hsum
  have heq : (u : ℝ) ^ ((2 : ℝ) / 3) * (1 / u) = eps u := by
    unfold eps
    rw [show (1 : ℝ) / u = (u : ℝ) ^ (-(1 : ℝ)) by rw [Real.rpow_neg_one, one_div],
      ← Real.rpow_add hu0]
    norm_num
  calc (∑ m ∈ {m ∈ Finset.Ioc u (2 * u) | ¬ Good m}, (1 : ℝ) / m)
      ≤ (#{m ∈ Finset.Ioc u (2 * u) | ¬ Good m} : ℝ) * (1 / u) := hsum
    _ ≤ 63 * (u : ℝ) ^ ((2 : ℝ) / 3) * (1 / u) :=
        mul_le_mul_of_nonneg_right hcount (by positivity)
    _ = 63 * eps u := by rw [mul_assoc, heq]

theorem Ioc_disjoint_next (a b c : ℕ) : Disjoint (Finset.Ioc a b) (Finset.Ioc b c) := by
  rw [Finset.disjoint_left]
  intro m h1 h2
  rw [Finset.mem_Ioc] at h1 h2
  omega

/-- The dyadic decomposition: the bad log-mass on `(U, 2^K U]` is at most
`Σ_{i < K} 63 ε(2^i U)`. -/
theorem bad_sum_dyadic_le {U : ℕ} (hU : 10 ^ 6 ≤ U) : ∀ K : ℕ,
    (∑ m ∈ {m ∈ Finset.Ioc U (2 ^ K * U) | ¬ Good m}, (1 : ℝ) / m) ≤
      ∑ i ∈ Finset.range K, 63 * eps (2 ^ i * U) := by
  intro K
  induction K with
  | zero => simp
  | succ K ih =>
      have hle1 : U ≤ 2 ^ K * U := Nat.le_mul_of_pos_left U (by positivity)
      have hle2 : 2 ^ K * U ≤ 2 ^ (K + 1) * U := by
        apply Nat.mul_le_mul_right
        exact Nat.pow_le_pow_right (by norm_num) (by omega)
      rw [← Finset.Ioc_union_Ioc_eq_Ioc hle1 hle2, Finset.filter_union,
        Finset.sum_union (Finset.disjoint_filter_filter (Ioc_disjoint_next _ _ _)),
        Finset.sum_range_succ]
      have hblock := bad_block_logMass_le (u := 2 ^ K * U) (by
        calc 10 ^ 6 ≤ U := hU
          _ ≤ 2 ^ K * U := hle1)
      rw [show 2 * (2 ^ K * U) = 2 ^ (K + 1) * U by ring] at hblock
      linarith

/-- `ε(2^i U) = (2^{-1/3})^i ε(U)`. -/
theorem eps_pow_two_mul {U : ℕ} (hU : 1 ≤ U) (i : ℕ) :
    eps (2 ^ i * U) = ((2 : ℝ) ^ (-((1 : ℝ) / 3))) ^ i * eps U := by
  unfold eps
  have hU0 : (0 : ℝ) < U := by exact_mod_cast hU
  push_cast
  rw [Real.mul_rpow (by positivity) hU0.le]
  congr 1
  rw [← Real.rpow_natCast (2 : ℝ) i, ← Real.rpow_mul (by norm_num),
    ← Real.rpow_natCast ((2 : ℝ) ^ (-((1 : ℝ) / 3))) i, ← Real.rpow_mul (by norm_num)]
  ring_nf

theorem two_rpow_neg_third_le : (2 : ℝ) ^ (-((1 : ℝ) / 3)) ≤ 0.794 := by
  rw [Numerics.rpow_le_iff_pow (n := 3) (by norm_num) (by norm_num) (by norm_num)]
  norm_num

/-- **Lemma 4.3, the log-mass.** For `U ≥ 10^6` and every `N`, the bad `m ∈ (U, N]` carry
log-mass at most `306 U^{-1/3}`. -/
theorem bad_logMass_le {U N : ℕ} (hU : 10 ^ 6 ≤ U) :
    (∑ m ∈ {m ∈ Finset.Ioc U N | ¬ Good m}, (1 : ℝ) / m) ≤ 306 * eps U := by
  have hU1 : 1 ≤ U := by omega
  -- cover `(U, N]` by `(U, 2^N U]`
  have hcov : {m ∈ Finset.Ioc U N | ¬ Good m} ⊆ {m ∈ Finset.Ioc U (2 ^ N * U) | ¬ Good m} := by
    apply Finset.filter_subset_filter
    apply Finset.Ioc_subset_Ioc_right
    calc N ≤ 2 ^ N := Nat.lt_two_pow_self.le
      _ ≤ 2 ^ N * U := Nat.le_mul_of_pos_right _ (by omega)
  have h1 := Finset.sum_le_sum_of_subset_of_nonneg hcov (fun m _ _ => by positivity :
    ∀ m ∈ {m ∈ Finset.Ioc U (2 ^ N * U) | ¬ Good m},
      m ∉ {m ∈ Finset.Ioc U N | ¬ Good m} → (0 : ℝ) ≤ 1 / m)
  have h2 := bad_sum_dyadic_le hU N
  -- the geometric series
  set r : ℝ := (2 : ℝ) ^ (-((1 : ℝ) / 3)) with hr
  have hr0 : 0 ≤ r := Real.rpow_nonneg (by norm_num) _
  have hr1 : r < 1 := by linarith [two_rpow_neg_third_le]
  have h3 : ∑ i ∈ Finset.range N, 63 * eps (2 ^ i * U) = 63 * eps U * ∑ i ∈ Finset.range N, r ^ i := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [eps_pow_two_mul hU1 i]
    ring
  have hgeom : ∑ i ∈ Finset.range N, r ^ i ≤ r ^ 0 / (1 - r) := by
    rw [Finset.range_eq_Ico]
    exact geom_sum_Ico_le_of_lt_one hr0 hr1
  have hε0 : 0 ≤ eps U := (eps_pos hU1).le
  have hr' := two_rpow_neg_third_le
  have hfrac : 63 / (1 - r) ≤ 306 := by
    rw [div_le_iff₀ (by linarith)]
    linarith
  calc (∑ m ∈ {m ∈ Finset.Ioc U N | ¬ Good m}, (1 : ℝ) / m)
      ≤ ∑ m ∈ {m ∈ Finset.Ioc U (2 ^ N * U) | ¬ Good m}, (1 : ℝ) / m := h1
    _ ≤ ∑ i ∈ Finset.range N, 63 * eps (2 ^ i * U) := h2
    _ = 63 * eps U * ∑ i ∈ Finset.range N, r ^ i := h3
    _ ≤ 63 * eps U * (r ^ 0 / (1 - r)) :=
        mul_le_mul_of_nonneg_left hgeom (by positivity)
    _ = eps U * (63 / (1 - r)) := by rw [pow_zero]; ring
    _ ≤ eps U * 306 := mul_le_mul_of_nonneg_left hfrac hε0
    _ = 306 * eps U := by ring

end FiberParity

end Problems.Juggler
