import Problems.Juggler.BeattySlopeDiophantineDim

/-!
# Equidistributed mass and the Diophantine dimension of the cluster set

An interval of phase length `ℓ` contains not only its first orbit point but
order `ℓ*q` of the first `q` orbit points, where `q` is the denominator of a
Dirichlet approximation. Under a uniform Diophantine lower bound of exponent
`τ` this makes its profile mass at least a constant times `ℓ^(1+τ/2)`, so the
distribution function is Hölder of exponent `2/(2+τ)`, better than the
`2/(3τ)` obtained from the first hit alone.

Consequently the complete cluster set at an irrational slope `α > 1` of
Diophantine class `ν` has Hausdorff dimension at least `2/(2+ν)`. For
`1 < ν < ∞` this exceeds `2/(3ν)`: the value `δ/ν` of the Denjoy-set
literature, with `δ = 2/3`, is not an upper bound for these sets.
-/

namespace Problems.Juggler.BeattySlope

open Filter Topology Set MeasureTheory BeattyPhase
open scoped NNReal ENNReal

/-- The profile increase across an open phase interval is at least the mass
of any finite family of atoms strictly inside it. -/
theorem jumpGap_mass_ge {phase w : ℕ → ℝ} (hw : Summable w)
    (hn : ∀ n, 0 ≤ w n) {c d : ℝ} (hcd : c < d) (S : Finset ℕ)
    (hS : ∀ n ∈ S, c < phase n ∧ phase n < d) :
    ∑ n ∈ S, w n ≤ jumpProfile phase w d - jumpProfileRight phase w c := by
  have hs (p : ℕ → Prop) [DecidablePred p] : Summable (fun n => if p n then w n else 0) :=
    hw.of_norm_bounded fun n => by
      split_ifs <;> simp [Real.norm_eq_abs, abs_of_nonneg (hn n), hn n]
  unfold jumpProfileRight jumpProfile
  rw [add_sub_add_left_eq_sub, ← (hs _).tsum_sub (hs _)]
  have hf : ∀ n, 0 ≤ (if phase n < d then w n else 0) - (if phase n ≤ c then w n else 0) := by
    intro n
    by_cases h1 : phase n ≤ c
    · simp [h1, lt_of_le_of_lt h1 hcd]
    · simp only [h1, if_false, sub_zero]
      split_ifs <;> simp [hn n]
  calc
    ∑ n ∈ S, w n = ∑ n ∈ S, ((if phase n < d then w n else 0) -
        (if phase n ≤ c then w n else 0)) := by
      apply Finset.sum_congr rfl
      intro n hnS
      simp [(hS n hnS).2, not_le_of_gt (hS n hnS).1]
    _ ≤ _ := Summable.sum_le_tsum S (fun n _ => hf n) ((hs _).sub (hs _))

/-- Splitting an interval of phase width `ℓ ≥ 10/q` into `⌊ℓq/5⌋` pieces
and hitting each piece gives at least `ℓq/10` distinct orbit indices below
the denominator `q` of a good rational approximation, all landing in it. -/
theorem rotation_many_hits {ξ a b : ℝ} (r : ℚ) (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1)
    (hwidth : 10 ≤ (r.den : ℝ)*(b-a)) (happrox : |ξ-(r : ℝ)| ≤ 1/(r.den : ℝ)^2) :
    ∃ S : Finset ℕ, (r.den : ℝ)*(b-a)/10 ≤ S.card ∧
      ∀ n ∈ S, 0 < n ∧ n < r.den ∧ Int.fract ((n : ℝ)*ξ) ∈ Ioo a b := by
  classical
  have hd : (0 : ℝ) < r.den := by exact_mod_cast r.pos
  set L := (r.den : ℝ)*(b-a) with hL
  set K := ⌊L/5⌋₊ with hK
  have hK1 : L/5 - 1 < K := by
    have := Nat.lt_floor_add_one (L/5)
    linarith
  have hKle : (K : ℝ) ≤ L/5 := Nat.floor_le (by positivity)
  have hKpos : (0 : ℝ) < K := by linarith
  set h := (b-a)/K with hh
  have hhpos : 0 < h := div_pos (sub_pos.2 hab) hKpos
  have hwid : 4 < (r.den : ℝ)*h := by
    have : (r.den : ℝ)*h = L/K := by rw [hh, hL]; ring
    rw [this, lt_div_iff₀ hKpos]
    linarith
  have hhit : ∀ i : Fin K, ∃ n : ℕ, 0 < n ∧ n < r.den ∧
      Int.fract ((n : ℝ)*ξ) ∈ Ioo (a + i*h) (a + (i+1)*h) := by
    intro i
    have hi : ((i : ℕ) : ℝ) + 1 ≤ K := by exact_mod_cast i.isLt
    apply rotation_hits_interval_of_rat_approx r (by positivity) _ (by nlinarith) happrox
    calc
      a + ((i : ℕ) + 1)*h ≤ a + K*h := by nlinarith
      _ = b := by rw [hh]; field_simp; ring
      _ ≤ 1 := hb
  choose f hf using hhit
  have hinj : Function.Injective f := by
    intro i j hij
    have h1 := (hf i).2.2
    have h2 := (hf j).2.2
    rw [hij] at h1
    have hlt1 : (i : ℝ) < (j : ℝ) + 1 := by
      have := lt_trans h1.1 h2.2
      have : (i : ℝ)*h < ((j : ℝ)+1)*h := by linarith
      exact lt_of_mul_lt_mul_right this hhpos.le
    have hlt2 : (j : ℝ) < (i : ℝ) + 1 := by
      have := lt_trans h2.1 h1.2
      have : (j : ℝ)*h < ((i : ℝ)+1)*h := by linarith
      exact lt_of_mul_lt_mul_right this hhpos.le
    have e1 : (i : ℕ) < (j : ℕ) + 1 := by exact_mod_cast hlt1
    have e2 : (j : ℕ) < (i : ℕ) + 1 := by exact_mod_cast hlt2
    exact Fin.ext (by omega)
  refine ⟨Finset.univ.image f, ?_, ?_⟩
  · rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
    linarith
  · intro n hn
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.1 hn
    refine ⟨(hf i).1, (hf i).2.1, ?_⟩
    have hi : ((i : ℕ) : ℝ) + 1 ≤ K := by exact_mod_cast i.isLt
    have hbnd : a + ((i : ℕ) + 1)*h ≤ b := by
      calc
        a + ((i : ℕ) + 1)*h ≤ a + K*h := by nlinarith
        _ = b := by rw [hh]; field_simp; ring
    have hi0 : (0 : ℝ) ≤ (i : ℕ) := Nat.cast_nonneg _
    exact ⟨by nlinarith [(hf i).2.2.1], by linarith [(hf i).2.2.2]⟩

section Passage

variable {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hβ : Irrational β)

include hβ0 hβ1 hβ

/-- Between two points whose distribution-function values differ, the gap
in the ratio variable is at least the mass of any finite family of atoms
whose phases lie strictly between those two values. -/
theorem passageCdf_sum_le {x y : ℝ}
    (huv : passageCdf hβ0 hβ1 hβ x < passageCdf hβ0 hβ1 hβ y) (S : Finset ℕ)
    (hS : ∀ n ∈ S, passagePhase β (n+1) ∈
      Ioo (passageCdf hβ0 hβ1 hβ x) (passageCdf hβ0 hβ1 hβ y)) :
    ∑ n ∈ S, passageJumpWeight β (n+1) ≤ y - x := by
  set u := passageCdf hβ0 hβ1 hβ x
  set v := passageCdf hβ0 hβ1 hβ y
  have hu := passageCdf_bounds hβ0 hβ1 hβ x
  have hv := passageCdf_bounds hβ0 hβ1 hβ y
  have hw : Summable (fun r => passageJumpWeight β (r+1)) :=
    (passage_jump_weights_hasSum hβ0 hβ1 hβ).summable
  have hn : ∀ n, 0 ≤ passageJumpWeight β (n+1) := fun n => passageJumpWeight_nonneg hβ0 hβ1 _
  have key : ∀ t ∈ Ioo u v, x < passageProfile β t ∧ passageProfile β t ≤ y := by
    intro t ht
    have ht01 : t ∈ Icc (0 : ℝ) 1 := ⟨hu.1.trans ht.1.le, ht.2.le.trans hv.2⟩
    constructor
    · by_contra h
      have hm := passageCdf_monotone hβ0 hβ1 hβ (le_of_not_gt h)
      rw [passageCdf_profile hβ0 hβ1 hβ ht01] at hm
      exact absurd ht.1 (not_lt_of_ge hm)
    · by_contra h
      have hm := passageCdf_monotone hβ0 hβ1 hβ (le_of_not_ge h)
      rw [passageCdf_profile hβ0 hβ1 hβ ht01] at hm
      exact absurd ht.2 (not_lt_of_ge hm)
  have hPv : jumpProfile (fun r => passagePhase β (r+1)) (fun r => passageJumpWeight β (r+1)) v
      ≤ y := by
    apply le_of_tendsto (jumpProfile_tendsto_left hw hn v)
    filter_upwards [Ioo_mem_nhdsLT huv] with t ht
    exact (key t ht).2
  have hxu : x ≤ jumpProfileRight (fun r => passagePhase β (r+1))
      (fun r => passageJumpWeight β (r+1)) u := by
    apply ge_of_tendsto (jumpProfile_tendsto_right hw hn u)
    filter_upwards [Ioo_mem_nhdsGT huv] with t ht
    exact (key t ht).1.le
  have hm := jumpGap_mass_ge hw hn huv S (fun n hnS => hS n hnS)
  linarith

/-- The equidistributed-mass estimate. Under `|q/β - p| ≥ c*q^(-τ)` for
all `q ≥ 1`, a distribution-function increment `ℓ` forces the squared ratio
increment to be at least `κ*ℓ^2*ℓ^τ`, so the increment is of order
`ℓ^(1+τ/2)`. -/
theorem passageCdf_mass_lower {c τ : ℝ} (hc : 0 < c) (hτ : 0 < τ)
    (hdio : DiophantineLowerBound (1/β) c τ) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ x y : ℝ,
      passageCdf hβ0 hβ1 hβ x < passageCdf hβ0 hβ1 hβ y →
      κ * ((passageCdf hβ0 hβ1 hβ y - passageCdf hβ0 hβ1 hβ x)^(2 : ℝ) *
        (passageCdf hβ0 hβ1 hβ y - passageCdf hβ0 hβ1 hβ x)^τ) ≤ (y - x)^(2 : ℝ) := by
  obtain ⟨a, B, ha, _, hwB⟩ := passageWeight_three_halves hβ0 hβ1 hβ
  refine ⟨(a/10)^2 / ((10 : ℝ)^τ * (1/c + 1)), by positivity, ?_⟩
  intro x y huv
  set u := passageCdf hβ0 hβ1 hβ x
  set v := passageCdf hβ0 hβ1 hβ y
  have hu := passageCdf_bounds hβ0 hβ1 hβ x
  have hv := passageCdf_bounds hβ0 hβ1 hβ y
  set ℓ := v - u with hℓ
  have hℓ0 : 0 < ℓ := sub_pos.2 huv
  have hℓ1 : ℓ ≤ 1 := by linarith [hu.1, hv.2]
  -- Dirichlet approximation at a level forcing a large denominator
  set Sr := (10/ℓ)^τ/c with hSr
  have hSr0 : 0 < Sr := by positivity
  set N := ⌈Sr⌉₊ with hN
  have hSN : Sr ≤ (N : ℝ) := Nat.le_ceil Sr
  have hN0 : 0 < N := by exact_mod_cast hSr0.trans_le hSN
  have hNS : (N : ℝ) ≤ Sr + 1 := (Nat.ceil_lt_add_one hSr0.le).le
  obtain ⟨r, hr, hrN⟩ := Real.exists_rat_abs_sub_le_and_den_le (1/β) hN0
  set D : ℝ := (r.den : ℝ) with hD
  have hDpos : (0 : ℝ) < D := by rw [hD]; exact_mod_cast r.pos
  have hDN : D ≤ N := by rw [hD]; exact_mod_cast hrN
  -- the Diophantine lower bound at the reduced denominator
  have hden : c * ((N : ℝ) + 1) ≤ D^τ := by
    have heq : D*(1/β) - (r.num : ℝ) = D*((1/β) - (r : ℝ)) := by
      rw [hD, Rat.cast_def]
      field_simp
    have hm : |D*(1/β) - (r.num : ℝ)| ≤ 1/((N : ℝ)+1) := by
      rw [heq, abs_mul, abs_of_pos hDpos]
      calc
        _ ≤ D*(1/(((N : ℝ)+1)*D)) := mul_le_mul_of_nonneg_left hr hDpos.le
        _ = _ := by field_simp
    have h := (hdio r.den r.pos r.num).trans
      (mul_le_mul_of_nonneg_left hm (Real.rpow_nonneg hDpos.le _))
    rw [← hD] at h
    exact (le_div_iff₀ (by positivity : 0 < (N : ℝ)+1)).1 (by simpa [div_eq_mul_inv] using h)
  have hpow : (10/ℓ)^τ < D^τ := by
    have hs : (10/ℓ)^τ ≤ c*(N : ℝ) := by
      have hs' := (div_le_iff₀ hc).1 hSN
      simpa only [mul_comm] using hs'
    nlinarith
  have hq : 10/ℓ < D := (Real.rpow_lt_rpow_iff (by positivity) hDpos.le hτ).1 hpow
  have hwidth : 10 ≤ D*(v-u) := by
    have := (div_lt_iff₀ hℓ0).1 hq
    rw [← hℓ]
    linarith
  have happ : |1/β - (r : ℝ)| ≤ 1/D^2 := by
    apply hr.trans
    apply one_div_le_one_div_of_le (by positivity)
    nlinarith
  obtain ⟨S, hcard, hS⟩ := rotation_many_hits r hu.1 huv hv.2 hwidth happ
  -- shift the indices to the zero-based weight sequence
  have hinj : Set.InjOn (fun n : ℕ => n - 1) (S : Set ℕ) := by
    intro m hm n hn hmn
    have h1 := (hS m hm).1
    have h2 := (hS n hn).1
    simp only at hmn
    omega
  set T := S.image (fun n : ℕ => n - 1)
  have hTcard : T.card = S.card := Finset.card_image_of_injOn hinj
  have hT : ∀ m ∈ T, passagePhase β (m+1) ∈ Ioo u v ∧ (m : ℝ) + 1 ≤ D := by
    intro m hm
    obtain ⟨n, hnS, rfl⟩ := Finset.mem_image.1 hm
    obtain ⟨hn0, hnD, hnI⟩ := hS n hnS
    have e : n - 1 + 1 = n := Nat.sub_add_cancel hn0
    refine ⟨?_, ?_⟩
    · rw [e, passagePhase_eq_fract hβ0, ← mul_one_div]
      exact hnI
    · have : ((n - 1 + 1 : ℕ) : ℝ) ≤ D := by rw [e, hD]; exact_mod_cast hnD.le
      exact_mod_cast this
  have hsum := passageCdf_sum_le hβ0 hβ1 hβ huv T (fun m hm => (hT m hm).1)
  -- each atom weighs at least `a/D^(3/2)`
  have hD32 : D^(3/2 : ℝ) = D * Real.sqrt D := by
    rw [Real.sqrt_eq_rpow, show (3/2 : ℝ) = 1 + 1/2 by norm_num,
      Real.rpow_add hDpos, Real.rpow_one]
  have hsD : 0 < Real.sqrt D := Real.sqrt_pos.2 hDpos
  have hlow : ∀ m ∈ T, a / (D * Real.sqrt D) ≤ passageJumpWeight β (m+1) := by
    intro m hm
    rw [← hD32]
    refine le_trans ?_ (hwB m).1
    apply div_le_div_of_nonneg_left ha.le (by positivity)
    exact Real.rpow_le_rpow (by positivity) (hT m hm).2 (by norm_num)
  have hcard' : D*ℓ/10 ≤ (T.card : ℝ) := by
    rw [hTcard]
    simpa [hℓ] using hcard
  have hmass : (D*ℓ/10) * (a / (D * Real.sqrt D)) ≤ y - x := by
    calc
      _ ≤ (T.card : ℝ) * (a / (D * Real.sqrt D)) :=
        mul_le_mul_of_nonneg_right hcard' (by positivity)
      _ = ∑ m ∈ T, a / (D * Real.sqrt D) := by simp
      _ ≤ _ := (Finset.sum_le_sum hlow).trans hsum
  have hsimp : (D*ℓ/10) * (a / (D * Real.sqrt D)) = (ℓ*a/10) / Real.sqrt D := by
    field_simp
  rw [hsimp] at hmass
  have hsq : ((ℓ*a/10) / Real.sqrt D)^2 ≤ (y - x)^2 :=
    pow_le_pow_left₀ (by positivity) hmass 2
  have hsq' : ((ℓ*a/10) / Real.sqrt D)^2 = (ℓ*a/10)^2 / D := by
    rw [div_pow, Real.sq_sqrt hDpos.le]
  rw [hsq'] at hsq
  -- the denominator is at most `(10/ℓ)^τ*(1/c+1)`
  have hbig : 1 ≤ (10/ℓ)^τ := Real.one_le_rpow (by rw [le_div_iff₀ hℓ0]; linarith) hτ.le
  have hDup : D ≤ (10/ℓ)^τ * (1/c + 1) := by
    have : Sr + 1 ≤ (10/ℓ)^τ * (1/c + 1) := by
      rw [hSr, mul_add, mul_one, mul_one_div]
      linarith
    linarith
  have hℓτ : 0 < ℓ^τ := Real.rpow_pos_of_pos hℓ0 τ
  have hdivpow : (10/ℓ)^τ = (10 : ℝ)^τ / ℓ^τ := Real.div_rpow (by norm_num) hℓ0.le τ
  have hfinal : (a/10)^2 / ((10 : ℝ)^τ * (1/c + 1)) * (ℓ^2 * ℓ^τ) ≤ (ℓ*a/10)^2 / D := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hDpos]
    calc
      (a/10)^2 * (ℓ^2 * ℓ^τ) / ((10 : ℝ)^τ * (1/c + 1)) * D
          ≤ (a/10)^2 * (ℓ^2 * ℓ^τ) / ((10 : ℝ)^τ * (1/c + 1)) *
            ((10/ℓ)^τ * (1/c + 1)) := mul_le_mul_of_nonneg_left hDup (by positivity)
      _ = (ℓ*a/10)^2 := by
        rw [hdivpow]
        field_simp
  have e2 : ∀ z : ℝ, z^(2 : ℝ) = z^2 := fun z => Real.rpow_two z
  rw [e2, e2]
  linarith

/-- A uniform Diophantine lower bound of exponent `τ` for `1/β` gives a
global Hölder bound of exponent `2/(2+τ)` for the distribution function. -/
theorem passageCdf_holder_sharp {c τ : ℝ} (hc : 0 < c) (hτ : 0 < τ)
    (hdio : DiophantineLowerBound (1/β) c τ) :
    ∃ C : ℝ≥0, HolderWith C ⟨(2 : ℝ)/(2+τ), by positivity⟩ (passageCdf hβ0 hβ1 hβ) := by
  obtain ⟨κ, hκ, hmass⟩ := passageCdf_mass_lower hβ0 hβ1 hβ hc hτ hdio
  let G := passageCdf hβ0 hβ1 hβ
  have hp : (0 : ℝ) < 2 + τ := by linarith
  let C : ℝ≥0 := ⟨(1/κ)^(1/(2+τ)), Real.rpow_nonneg (by positivity) _⟩
  have hc' (x y : ℝ) (hxy : x ≤ y) : G y - G x ≤ (C : ℝ)*(y-x)^((2 : ℝ)/(2+τ)) := by
    by_cases he : G x = G y
    · rw [he, sub_self]
      positivity
    have hlt : G x < G y := lt_of_le_of_ne (passageCdf_monotone hβ0 hβ1 hβ hxy) he
    have hℓ : 0 < G y - G x := sub_pos.2 hlt
    have h := hmass x y hlt
    have hyx : 0 ≤ y - x := sub_nonneg.2 hxy
    have hpow : (G y - G x)^(2+τ) ≤ (1/κ) * (y-x)^(2 : ℝ) := by
      rw [Real.rpow_add hℓ, one_div_mul_eq_div, le_div_iff₀ hκ]
      linarith
    have hr := Real.rpow_le_rpow (Real.rpow_nonneg hℓ.le _) hpow
      (by positivity : (0 : ℝ) ≤ 1/(2+τ))
    rw [← Real.rpow_mul hℓ.le, mul_one_div_cancel hp.ne', Real.rpow_one,
      Real.mul_rpow (by positivity) (Real.rpow_nonneg hyx _),
      ← Real.rpow_mul hyx] at hr
    change _ ≤ (1/κ)^(1/(2+τ)) * (y-x)^((2 : ℝ)/(2+τ))
    simpa [div_eq_mul_inv] using hr
  have hmono : Monotone G := passageCdf_monotone hβ0 hβ1 hβ
  refine ⟨C, ?_⟩
  intro x y
  have hd : dist (G x) (G y) ≤ (C : ℝ)*dist x y^((2 : ℝ)/(2+τ)) := by
    rcases le_total x y with hxy | hyx
    · rw [Real.dist_eq, Real.dist_eq, abs_of_nonpos (sub_nonpos.2 (hmono hxy)),
        abs_of_nonpos (sub_nonpos.2 hxy), neg_sub, neg_sub]
      exact hc' x y hxy
    · rw [Real.dist_eq, Real.dist_eq, abs_of_nonneg (sub_nonneg.2 (hmono hyx)),
        abs_of_nonneg (sub_nonneg.2 hyx)]
      exact hc' y x hyx
  change edist (G x) (G y) ≤ (C : ℝ≥0∞)*edist x y^((2 : ℝ)/(2+τ))
  simpa only [ENNReal.ofReal_mul C.coe_nonneg,
    ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_rpow_of_nonneg (dist_nonneg : 0 ≤ dist x y)
      (by positivity : 0 ≤ (2 : ℝ)/(2+τ)), ← edist_dist] using ENNReal.ofReal_le_ofReal hd

/-- A uniform Diophantine lower bound of exponent `τ` for `1/β` gives the
Hausdorff dimension lower bound `2/(2+τ)` for the family cluster set. -/
theorem passageCluster_dimH_ge_sharp {c τ : ℝ} (hc : 0 < c) (hτ : 0 < τ)
    (hdio : DiophantineLowerBound (1/β) c τ) :
    ENNReal.ofReal ((2 : ℝ)/(2+τ)) ≤ dimH (passageClusterSet β) := by
  obtain ⟨C, hC⟩ := passageCdf_holder_sharp hβ0 hβ1 hβ hc hτ hdio
  let r : ℝ≥0 := ⟨(2 : ℝ)/(2+τ), by positivity⟩
  have hr : 0 < r := by change (0 : ℝ) < (2 : ℝ)/(2+τ); positivity
  change HolderWith C r (passageCdf hβ0 hβ1 hβ) at hC
  have h := hC.dimH_image_le hr (passageClusterSet β)
  rw [passageCdf_image_cluster] at h
  have hI : dimH (Icc (0 : ℝ) 1) = 1 := by
    simpa only [segment_eq_Icc (by norm_num : (0 : ℝ) ≤ 1)] using
      (Real.dimH_segment (by norm_num : (0 : ℝ) ≠ 1))
  rw [hI] at h
  have hh' := (ENNReal.le_div_iff_mul_le (Or.inl (ENNReal.coe_ne_zero.2 hr.ne'))
    (Or.inl ENNReal.coe_ne_top)).1 h
  rw [one_mul, ← ENNReal.ofReal_coe_nnreal] at hh'
  exact hh'

end Passage

/-- At an irrational slope `α > 1` with `|q*α - p| ≥ c*q^(-τ)` for all
`q ≥ 1`, the complete cluster set has Hausdorff dimension at least
`2/(2+τ)`. -/
theorem cluster_dimH_ge_sharp {α c τ : ℝ} (hα1 : 1 < α) (hα : Irrational α)
    (hc : 0 < c) (hτ : 0 < τ) (hdio : DiophantineLowerBound α c τ) :
    ENNReal.ofReal ((2 : ℝ)/(2+τ)) ≤ dimH (passageClusterSet (1/α)) := by
  have hα0 : 0 < α := by linarith
  have hβ0 : 0 < 1/α := one_div_pos.mpr hα0
  have hβ1 : 1/α < 1 := (div_lt_one hα0).mpr hα1
  have hβ : Irrational (1/α) := by simpa using hα.inv
  exact passageCluster_dimH_ge_sharp hβ0 hβ1 hβ hc hτ (by rwa [one_div_one_div])

/-- If `α > 1` is irrational and satisfies a uniform Diophantine lower
bound at every exponent above `ν ≥ 0` (that is, its Diophantine class is at
most `ν`), the complete cluster set has Hausdorff dimension at least
`2/(2+ν)`. -/
theorem cluster_dimH_ge_class {α ν : ℝ} (hα1 : 1 < α) (hα : Irrational α) (hν : 0 ≤ ν)
    (hdio : ∀ τ : ℝ, ν < τ → ∃ c : ℝ, 0 < c ∧ DiophantineLowerBound α c τ) :
    ENNReal.ofReal ((2 : ℝ)/(2+ν)) ≤ dimH (passageClusterSet (1/α)) := by
  have hcont : ContinuousAt (fun τ : ℝ => ENNReal.ofReal ((2 : ℝ)/(2+τ))) ν :=
    ENNReal.continuous_ofReal.continuousAt.comp
      (continuousAt_const.div (continuousAt_const.add continuousAt_id) (by linarith))
  have hlim := hcont.tendsto.mono_left (nhdsWithin_le_nhds : 𝓝[>] ν ≤ 𝓝 ν)
  apply le_of_tendsto hlim
  filter_upwards [self_mem_nhdsWithin] with τ hτ
  obtain ⟨c, hc, hbound⟩ := hdio τ hτ
  have hτ0 : 0 < τ := lt_of_le_of_lt hν hτ
  exact cluster_dimH_ge_sharp hα1 hα hc hτ0 hbound

/-- The Denjoy value `2/(3ν)` is not an upper bound. If `1 < ν` and `α > 1`
is irrational with uniform Diophantine lower bounds at every exponent above
`ν`, then the Hausdorff dimension of the complete cluster set is strictly
larger than `2/(3ν)`. For `α` of Diophantine class exactly `ν`, the upper
bound `dimH ≤ 2/(3ν)` therefore fails even though `|q*α - p| ≤ q^(-μ)` has
arbitrarily large solutions for every `μ < ν`. -/
theorem cluster_dimH_gt_denjoy {α ν : ℝ} (hα1 : 1 < α) (hα : Irrational α) (hν : 1 < ν)
    (hdio : ∀ τ : ℝ, ν < τ → ∃ c : ℝ, 0 < c ∧ DiophantineLowerBound α c τ) :
    ENNReal.ofReal ((2 : ℝ)/(3*ν)) < dimH (passageClusterSet (1/α)) := by
  refine lt_of_lt_of_le ?_ (cluster_dimH_ge_class hα1 hα (by linarith) hdio)
  rw [ENNReal.ofReal_lt_ofReal_iff (by positivity)]
  exact div_lt_div_of_pos_left (by norm_num) (by linarith) (by linarith)

/-- The proved two-sided window at a single slope: a uniform lower bound
of exponent `τ` and approximations of exponent `μ > 1` with arbitrarily
large denominators place the dimension between `2/(2+τ)` and
`2/(2+√μ)`. -/
theorem cluster_dimH_window {α c τ μ : ℝ} (hα1 : 1 < α) (hα : Irrational α)
    (hc : 0 < c) (hτ : 0 < τ) (hdio : DiophantineLowerBound α c τ) (hμ : 1 < μ)
    (happ : ∀ Q : ℕ, ∃ q : ℕ, Q < q ∧ ∃ p : ℤ, |(q : ℝ) * α - p| ≤ (q : ℝ) ^ (-μ)) :
    ENNReal.ofReal ((2 : ℝ)/(2+τ)) ≤ dimH (passageClusterSet (1/α)) ∧
      dimH (passageClusterSet (1/α)) ≤ ENNReal.ofReal (2 / (2 + Real.sqrt μ)) :=
  ⟨cluster_dimH_ge_sharp hα1 hα hc hτ hdio, dio_exponent_dimH_le hα1 hα hμ happ⟩

end Problems.Juggler.BeattySlope
