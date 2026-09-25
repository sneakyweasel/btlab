import Problems.Juggler.BeattyGridTree
import Problems.Juggler.BeattySlopeExactDim

/-!
# Lower bounds for the atom mass of a phase interval

For the rotation profile with phases `φ k = fract((k+1)α)` and weights
`w k ≥ A (k+1)^(-3/2)`, the atom mass `F(v) - F⁺(u)` of a phase interval is
bounded below in three ways:

* by the weight of any single atom inside;
* by `(ℓQ/10) A Q^(-3/2)` when `ℓ = v - u ≥ 10/Q` for a reduced approximation
  `p/Q` with `|α - p/Q| ≤ 1/Q²` (many hits of index below `Q`);
* by `(ℓ/|θ| - 1) A (Kq + t)^(-3/2)` along a chain `{(mq+t)α} = b + mθ`,
  `m ≤ K`, crossing the interval.
-/

namespace Problems.Juggler.BeattySlope

open Filter Topology Set BeattyPhase

variable {φ w : ℕ → ℝ} {α A : ℝ}

/-- A single atom inside the interval. -/
theorem atom_le_inc (hw : Summable w) (hn : ∀ n, 0 ≤ w n) {u v : ℝ} {k : ℕ}
    (h1 : u < φ k) (h2 : φ k < v) :
    w k ≤ jumpProfile φ w v - jumpProfileRight φ w u := by
  have := jumpGap_mass_ge hw hn (h1.trans h2) {k} (by simpa using ⟨h1, h2⟩)
  simpa using this

/-- **Many hits.** At a reduced approximation `p/Q` with `|α - p/Q| ≤ 1/Q²`, an
interval of length `ℓ ≥ 10/Q` carries atom mass at least `(ℓQ/10) A Q^(-3/2)`. -/
theorem hits_le_inc (hw : Summable w) (hn : ∀ n, 0 ≤ w n) (hA : 0 ≤ A)
    (hwA : ∀ k : ℕ, A / ((k : ℝ) + 1) ^ (3/2 : ℝ) ≤ w k)
    (hfr : ∀ k : ℕ, φ k = Int.fract (((k : ℝ) + 1) * α)) {p : ℤ} {Q : ℕ} (hQ : 0 < Q)
    (hcop : Nat.Coprime p.natAbs Q) (happ : |α - p / Q| ≤ 1 / (Q : ℝ) ^ 2)
    {u v : ℝ} (hu : 0 ≤ u) (huv : u < v) (hv : v ≤ 1) (hwidth : 10 ≤ (Q : ℝ) * (v - u)) :
    (Q : ℝ) * (v - u) / 10 * (A / (Q : ℝ) ^ (3/2 : ℝ)) ≤
      jumpProfile φ w v - jumpProfileRight φ w u := by
  classical
  have hQR : (0 : ℝ) < Q := by exact_mod_cast hQ
  set r : ℚ := (p : ℚ) / (Q : ℤ)
  have hden : (r.den : ℤ) = Q := by
    have := Rat.den_div_eq_of_coprime (a := p) (b := (Q : ℤ)) (by exact_mod_cast hQ)
      (by simpa using hcop)
    exact this
  have hden' : (r.den : ℝ) = Q := by exact_mod_cast hden
  have hr : (r : ℝ) = p / Q := by simp [r]
  obtain ⟨S, hcard, hS⟩ := rotation_many_hits r hu huv hv (by rw [hden']; exact hwidth)
    (by rw [hden', hr]; exact happ)
  rw [hden'] at hcard
  have hSQ : ∀ n ∈ S, 0 < n ∧ n < Q := fun n hn => by
    obtain ⟨h0, h1, -⟩ := hS n hn
    have : (n : ℤ) < Q := by rw [← hden]; exact_mod_cast h1
    exact ⟨h0, by exact_mod_cast this⟩
  set S' := S.image (fun n => n - 1)
  have hinj : Set.InjOn (fun n => n - 1) (S : Set ℕ) := fun a ha b hb h => by
    have := (hSQ a ha).1; have := (hSQ b hb).1; simp only at h; omega
  have hcard' : S'.card = S.card := Finset.card_image_of_injOn hinj
  have hmem : ∀ k ∈ S', u < φ k ∧ φ k < v := by
    intro k hk
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.1 hk
    obtain ⟨h0, -, hin⟩ := hS n hn
    rw [hfr]
    have : ((n - 1 : ℕ) : ℝ) + 1 = n := by rw [Nat.cast_sub (by omega)]; push_cast; ring
    rw [this]; exact hin
  have hw' : ∀ k ∈ S', A / (Q : ℝ) ^ (3/2 : ℝ) ≤ w k := by
    intro k hk
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.1 hk
    obtain ⟨h0, h1⟩ := hSQ n hn
    refine le_trans ?_ (hwA _)
    apply div_le_div_of_nonneg_left hA (by positivity)
    apply Real.rpow_le_rpow (by positivity) _ (by norm_num)
    have : ((n - 1 : ℕ) : ℝ) + 1 = n := by rw [Nat.cast_sub (by omega)]; push_cast; ring
    rw [this]; exact_mod_cast h1.le
  calc (Q : ℝ) * (v - u) / 10 * (A / (Q : ℝ) ^ (3/2 : ℝ))
      ≤ (S'.card : ℝ) * (A / (Q : ℝ) ^ (3/2 : ℝ)) := by
        rw [hcard']; exact mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = ∑ k ∈ S', A / (Q : ℝ) ^ (3/2 : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ k ∈ S', w k := Finset.sum_le_sum hw'
    _ ≤ _ := jumpGap_mass_ge hw hn huv S' hmem

/-- Integers in an open interval: `(x, y)` with `0 ≤ x` contains at least
`y - x - 1` naturals below `⌈y⌉`. -/
theorem card_Ioo_nat_ge {x y : ℝ} (hx : 0 ≤ x) (hxy : x < y) :
    y - x - 1 ≤ ((Finset.Ioo ⌊x⌋₊ ⌈y⌉₊).card : ℝ) := by
  rw [Nat.card_Ioo]
  have h1 : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le hx
  have h2 : y ≤ (⌈y⌉₊ : ℝ) := Nat.le_ceil y
  have h3 : ⌊x⌋₊ ≤ ⌈y⌉₊ := by
    have : (⌊x⌋₊ : ℝ) ≤ ⌈y⌉₊ := by linarith
    exact_mod_cast this
  rcases Nat.eq_or_lt_of_le h3 with h | h
  · rw [h, Nat.sub_self, Nat.zero_sub, Nat.cast_zero]
    have : (⌊x⌋₊ : ℝ) = ⌈y⌉₊ := by exact_mod_cast h
    have hx1 : x < ⌊x⌋₊ + 1 := Nat.lt_floor_add_one x
    linarith
  · rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
    have hx1 : x < ⌊x⌋₊ + 1 := Nat.lt_floor_add_one x
    push_cast
    linarith

/-- **Chain.** Suppose `{(mq+t)α} = b + mθ` for every `m ≤ K`, and the interval
`(u, v)` lies between `b` and `b + Kθ`. Then its atom mass is at least
`((v-u)/|θ| - 1) A (Kq + t + 1)^(-3/2)`. -/
theorem chain_le_inc (hw : Summable w) (hn : ∀ n, 0 ≤ w n) (hA : 0 ≤ A)
    (hwA : ∀ k : ℕ, A / ((k : ℝ) + 1) ^ (3/2 : ℝ) ≤ w k)
    {q t K : ℕ} (ht : 1 ≤ t) {b θ : ℝ} (hθ : θ ≠ 0)
    (hchain : ∀ m, m ≤ K → φ (m * q + t - 1) = b + m * θ)
    {u v : ℝ} (huv : u < v)
    (hbetween : (0 < θ ∧ b ≤ u ∧ v ≤ b + K * θ) ∨ (θ < 0 ∧ b + K * θ ≤ u ∧ v ≤ b)) :
    ((v - u) / |θ| - 1) * (A / ((K : ℝ) * q + t) ^ (3/2 : ℝ)) ≤
      jumpProfile φ w v - jumpProfileRight φ w u := by
  classical
  -- the chain indices landing in `(u, v)`
  set x := if 0 < θ then (u - b) / θ else (v - b) / θ
  set y := if 0 < θ then (v - b) / θ else (u - b) / θ
  have hθa : 0 < |θ| := abs_pos.2 hθ
  have hxy : y - x = (v - u) / |θ| := by
    simp only [x, y]
    split_ifs with h
    · rw [abs_of_pos h]; ring
    · rw [abs_of_neg (lt_of_le_of_ne (not_lt.1 h) hθ)]; ring
  have hx0 : 0 ≤ x := by
    simp only [x]; split_ifs with h
    · rcases hbetween with ⟨-, h1, -⟩ | ⟨h', -, -⟩
      · exact div_nonneg (by linarith) h.le
      · exact absurd h' (not_lt.2 h.le)
    · rcases hbetween with ⟨h', -, -⟩ | ⟨hneg, -, h2⟩
      · exact absurd h' h
      · exact div_nonneg_of_nonpos (by linarith) hneg.le
  have hyK : y ≤ K := by
    simp only [y]; split_ifs with h
    · rcases hbetween with ⟨-, -, h2⟩ | ⟨h', -, -⟩
      · rw [div_le_iff₀ h]; linarith
      · exact absurd h' (not_lt.2 h.le)
    · rcases hbetween with ⟨h', -, -⟩ | ⟨hneg, h1, -⟩
      · exact absurd h' h
      · rw [div_le_iff_of_neg hneg]; linarith
  have hxy' : x < y := by rw [← sub_pos, hxy]; exact div_pos (by linarith) hθa
  set Sm := Finset.Ioo ⌊x⌋₊ ⌈y⌉₊
  have hmemS : ∀ m ∈ Sm, x < m ∧ (m : ℝ) < y := by
    intro m hm
    obtain ⟨h1, h2⟩ := Finset.mem_Ioo.1 hm
    constructor
    · have := Nat.lt_floor_add_one x
      have : ⌊x⌋₊ + 1 ≤ m := h1
      have : ((⌊x⌋₊ + 1 : ℕ) : ℝ) ≤ m := by exact_mod_cast this
      push_cast at this; linarith
    · exact (Nat.lt_ceil).1 h2
  have hmK : ∀ m ∈ Sm, m ≤ K := fun m hm => by
    have := (hmemS m hm).2
    have : (m : ℝ) < K := lt_of_lt_of_le this hyK
    exact_mod_cast this.le
  set S := Sm.image (fun m => m * q + t - 1)
  have hphase : ∀ m ∈ Sm, u < φ (m * q + t - 1) ∧ φ (m * q + t - 1) < v := by
    intro m hm
    rw [hchain m (hmK m hm)]
    obtain ⟨h1, h2⟩ := hmemS m hm
    simp only [x, y] at h1 h2
    split_ifs at h1 h2 with h
    · rw [div_lt_iff₀ h] at h1; rw [lt_div_iff₀ h] at h2
      constructor <;> linarith
    · have hneg : θ < 0 := lt_of_le_of_ne (not_lt.1 h) hθ
      rw [div_lt_iff_of_neg hneg] at h1; rw [lt_div_iff_of_neg hneg] at h2
      constructor <;> linarith
  have hinj : Set.InjOn (fun m => m * q + t - 1) (Sm : Set ℕ) := by
    intro a _ c _ h
    simp only at h
    by_contra hac
    rcases Nat.lt_or_gt_of_ne hac with hlt | hlt
    · -- distinct chain indices give distinct phases
      have e1 := hchain a (hmK a ‹_›)
      have e2 := hchain c (hmK c ‹_›)
      rw [h] at e1
      have : (a : ℝ) * θ = c * θ := by linarith
      have := mul_right_cancel₀ hθ this
      have : a = c := by exact_mod_cast this
      omega
    · have e1 := hchain a (hmK a ‹_›)
      have e2 := hchain c (hmK c ‹_›)
      rw [h] at e1
      have : (a : ℝ) * θ = c * θ := by linarith
      have := mul_right_cancel₀ hθ this
      have : a = c := by exact_mod_cast this
      omega
  have hcardS : S.card = Sm.card := Finset.card_image_of_injOn hinj
  have hwS : ∀ k ∈ S, A / ((K : ℝ) * q + t) ^ (3/2 : ℝ) ≤ w k := by
    intro k hk
    obtain ⟨m, hm, rfl⟩ := Finset.mem_image.1 hk
    refine le_trans ?_ (hwA _)
    apply div_le_div_of_nonneg_left hA (by positivity)
    apply Real.rpow_le_rpow (by positivity) _ (by norm_num)
    have hmK' := hmK m hm
    have h1 : 1 ≤ m * q + t := by omega
    have : ((m * q + t - 1 : ℕ) : ℝ) + 1 = m * q + t := by
      rw [Nat.cast_sub h1]; push_cast; ring
    rw [this]
    have : (m : ℝ) ≤ K := by exact_mod_cast hmK'
    nlinarith [Nat.cast_nonneg (α := ℝ) q]
  have hSin : ∀ k ∈ S, u < φ k ∧ φ k < v := by
    intro k hk
    obtain ⟨m, hm, rfl⟩ := Finset.mem_image.1 hk
    exact hphase m hm
  have hcount := card_Ioo_nat_ge hx0 hxy'
  rw [hxy] at hcount
  have hpos : 0 ≤ A / ((K : ℝ) * q + t) ^ (3/2 : ℝ) := by positivity
  calc ((v - u) / |θ| - 1) * (A / ((K : ℝ) * q + t) ^ (3/2 : ℝ))
      ≤ (S.card : ℝ) * (A / ((K : ℝ) * q + t) ^ (3/2 : ℝ)) := by
        rw [hcardS]; exact mul_le_mul_of_nonneg_right hcount hpos
    _ = ∑ k ∈ S, A / ((K : ℝ) * q + t) ^ (3/2 : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ k ∈ S, w k := Finset.sum_le_sum hwS
    _ ≤ _ := jumpGap_mass_ge hw hn huv S hSin

end Problems.Juggler.BeattySlope
