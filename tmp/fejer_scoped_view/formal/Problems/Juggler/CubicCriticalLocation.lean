import Problems.Juggler.CubicConstraintFusion

/-!
# Critical-event localization from rank ceilings

The rank path, integer gap ceilings, suffix costs, window hitting and pair
coverage are explicit inputs. Real scalar certification and extraction of
these inputs from a complete cubic cycle remain separate written arguments.
-/

namespace Problems.Juggler.CubicCriticalLocation

open scoped BigOperators

/-- A strict power ceiling bounds the binary valuation of a positive gap. -/
theorem valuation_le_of_lt_pow_succ {l H : ℕ}
    (hl : 0 < l) (hbound : l < 2 ^ (H + 1)) :
    padicValNat 2 l ≤ H := by
  by_contra hn
  have hdiv : 2 ^ (H + 1) ∣ l :=
    dvd_trans (pow_dvd_pow (2 : ℕ) (by omega)) pow_padicValNat_dvd
  exact (not_lt_of_ge (Nat.le_of_dvd hl hdiv)) hbound

/-- The first certified rank ceiling supplies a valuation bound of 25. -/
theorem valuation_le_twenty_five {l : ℕ}
    (hl : 0 < l) (hbound : l < 2 ^ 26) :
    padicValNat 2 l ≤ 25 :=
  valuation_le_of_lt_pow_succ hl hbound

/-- The second certified rank ceiling supplies a valuation bound of 19. -/
theorem valuation_le_nineteen {l : ℕ}
    (hl : 0 < l) (hbound : l < 2 ^ 20) :
    padicValNat 2 l ≤ 19 :=
  valuation_le_of_lt_pow_succ hl hbound

/-- The fixed-count lower valuation of the first gap in a suffix of `d` edges. -/
def suffixHeight (d : ℕ) : ℕ :=
  d + 1 + (d - 1) * 287963 / 780239

/-- Every three successive ranks meet the low interval at the fixed counts. -/
theorem three_rank_low {i : ℕ} (hi : i < 780239) :
    i < 287963 ∨ (i + 287963) % 780239 < 287963 ∨
      ((i + 287963) % 780239 + 287963) % 780239 < 287963 := by
  omega

/-- The upper portion of the low interval reaches the tiny interval in two steps. -/
theorem highlow_two_step_tiny {i : ℕ} (ha : 204313 ≤ i) (he : i < 287963) :
    ((i + 287963) % 780239 + 287963) % 780239 = i - 204313 ∧
      i - 204313 < 83650 := by
  omega

/-- A finite path with the two certified caps has at most twenty-one vertices. -/
theorem block_length_le_twenty_one (n : ℕ) (idx v : ℕ → ℕ)
    (hrank : ∀ t < n, idx t < 780239)
    (hnext : ∀ t, t + 1 < n → idx (t + 1) = (idx t + 287963) % 780239)
    (hsmall : ∀ t < n, idx t < 204313 → v t ≤ 25)
    (htiny : ∀ t < n, idx t < 83650 → v t ≤ 19)
    (hcost : ∀ t d, t + d < n → suffixHeight d ≤ v t) :
    n ≤ 21 := by
  by_contra hn
  have hnlarge : 22 ≤ n := by omega
  have hzero := hrank 0 (by omega)
  have hstep0 := hnext 0 (by omega)
  have hstep1 := hnext 1 (by omega)
  have hlow : ∃ t ≤ 2, idx t < 287963 := by
    rcases three_rank_low hzero with h | h | h
    · exact ⟨0, by omega, h⟩
    · exact ⟨1, by omega, by simpa only [Nat.zero_add, hstep0] using h⟩
    · refine ⟨2, by omega, ?_⟩
      simpa only [show 1 + 1 = 2 from rfl, hstep1, hstep0, Nat.zero_add] using h
  rcases hlow with ⟨t, ht, he⟩
  by_cases ha : idx t < 204313
  · have hupper := hsmall t (by omega) ha
    have hlower := hcost t 19 (by omega)
    norm_num [suffixHeight] at hlower
    omega
  · have hstep := hnext t (by omega)
    have hstep' : idx (t + 2) = (idx (t + 1) + 287963) % 780239 := by
      simpa only [Nat.add_assoc] using hnext (t + 1) (by omega)
    have htwo := highlow_two_step_tiny (by omega : 204313 ≤ idx t) he
    have htarget : idx (t + 2) < 83650 := by
      rw [hstep', hstep, htwo.1]
      exact htwo.2
    have hupper := htiny (t + 2) (by omega) htarget
    have hlower := hcost (t + 2) 15 (by omega)
    norm_num [suffixHeight] at hlower
    omega

/-- A bounded finite block cover of the fixed number of even gaps needs this many blocks. -/
theorem fixed_block_count_lower {ι : Type*} [Fintype ι] (length : ι → ℕ)
    (hsum : ∑ i, length i = 780237) (hbound : ∀ i, length i ≤ 21) :
    37155 ≤ Fintype.card ι := by
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hbound i)
  simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul] at hs
  rw [hsum] at hs
  omega

/-- The two additional noncritical corrections are retained as an explicit premise. -/
theorem fixed_nonzero_lower {C T : ℕ} (hC : 37155 ≤ C) (hfilter : C + 2 ≤ T) :
    37157 ≤ T := by
  omega

/-- The three-level support cover is retained as an explicit premise. -/
theorem fixed_deviation_lower {C S : ℕ} (hC : 37155 ≤ C) (hcover : C ≤ 1 + 2 * S) :
    18577 ≤ S := by
  omega

/-- Hitting each disjoint full-width block gives a cardinality lower bound. -/
theorem block_hits_card {S : Finset ℕ} {b n w : ℕ}
    (hit : ∀ j : Fin (n / w),
      ∃ i ∈ S, b + w * j.val ≤ i ∧ i < b + w * (j.val + 1)) :
    n / w ≤ S.card := by
  classical
  choose f hmem hlo hhi using hit
  have hinj : Function.Injective f := by
    intro j k heq
    apply Fin.ext
    by_contra hne
    have hcases : j.val + 1 ≤ k.val ∨ k.val + 1 ≤ j.val := by omega
    rcases hcases with hjk | hkj
    · have hmul := Nat.mul_le_mul_left w hjk
      have hj := hhi j
      have hk := hlo k
      omega
    · have hmul := Nat.mul_le_mul_left w hkj
      have hk := hhi k
      have hj := hlo j
      omega
  have hsub : (Finset.univ.image f) ⊆ S := by
    intro i hi
    rcases Finset.mem_image.mp hi with ⟨j, _, rfl⟩
    exact hmem j
  have hc := Finset.card_le_card hsub
  simpa only [Finset.card_image_of_injective _ hinj,
    Finset.card_univ, Fintype.card_fin] using hc

/-- Every complete width-w subwindow of an interval hits S. -/
theorem window_hits_card {S : Finset ℕ} {b n w : ℕ}
    (hit : ∀ j : ℕ, j + w ≤ n →
      ∃ i ∈ S, b + j ≤ i ∧ i < b + j + w) :
    n / w ≤ S.card := by
  apply block_hits_card
  intro j
  have hj : j.val + 1 ≤ n / w := by omega
  have hbound : w * j.val + w ≤ n := by
    calc
      w * j.val + w = w * (j.val + 1) := by ring
      _ ≤ w * (n / w) := Nat.mul_le_mul_left w hj
      _ ≤ n := Nat.mul_div_le n w
  obtain ⟨i, hi, hlo, hhi⟩ := hit (w * j.val) hbound
  exact ⟨i, hi, hlo, by simpa [Nat.mul_add, Nat.add_assoc] using hhi⟩

/-- The witnesses belong to the queried interval, so its filtered count suffices. -/
theorem window_hits_interval_card {S : Finset ℕ} {b n w : ℕ}
    (hit : ∀ j : ℕ, j + w ≤ n →
      ∃ i ∈ S, b + j ≤ i ∧ i < b + j + w) :
    n / w ≤ (S.filter fun i => b ≤ i ∧ i < b + n).card := by
  apply window_hits_card
  intro j hj
  obtain ⟨i, hi, hlo, hhi⟩ := hit j hj
  exact ⟨i, Finset.mem_filter.mpr ⟨hi, by omega⟩, hlo, hhi⟩

/-- The source-time R arc has length 301994. -/
theorem r_arc_critical_count {S : Finset ℕ} {b : ℕ}
    (hit : ∀ j : ℕ, j + 21 ≤ 301994 →
      ∃ i ∈ S, b + j ≤ i ∧ i < b + j + 21) :
    14380 ≤ S.card := by
  have h := window_hits_card hit
  norm_num at h
  exact h

/-- The fixed R-arc bound retains membership in the original time interval. -/
theorem r_arc_interval_critical_count {S : Finset ℕ}
    (hit : ∀ j : ℕ, j + 21 ≤ 301994 →
      ∃ i ∈ S, 478245 + j ≤ i ∧ i < 478245 + j + 21) :
    14380 ≤ (S.filter fun i => 478245 ≤ i ∧ i < 780239).card := by
  have h := window_hits_interval_card hit
  norm_num at h
  exact h

/-- An explicitly injective choice of a responsible deviation preserves count. -/
theorem injective_deviation_count {α β : Type*} [DecidableEq α] [DecidableEq β]
    {C : Finset α} {D : Finset β} (f : α → β)
    (hmem : ∀ i ∈ C, f i ∈ D)
    (hinj : Set.InjOn f (C : Set α)) :
    C.card ≤ D.card :=
  Finset.card_le_card_of_injOn f hmem hinj

/-- Disjoint pairs prevent one deviation from paying for two selected events. -/
theorem disjoint_pair_deviation_count {α β : Type*}
    [DecidableEq α] [DecidableEq β] {C : Finset α} {D : Finset β}
    (pair : α → Finset β)
    (hdisj : ∀ i ∈ C, ∀ j ∈ C, i ≠ j → Disjoint (pair i) (pair j))
    (hcover : ∀ i ∈ C, ∃ j ∈ D, j ∈ pair i) :
    C.card ≤ D.card := by
  classical
  have hex : ∀ i : C, ∃ j : D, j.val ∈ pair i.val := by
    intro i
    obtain ⟨j, hjD, hjP⟩ := hcover i.val i.property
    exact ⟨⟨j, hjD⟩, hjP⟩
  choose f hf using hex
  have hinj : Function.Injective f := by
    intro i j heq
    apply Subtype.ext
    by_contra hne
    have hd := Finset.disjoint_left.mp
      (hdisj i.val i.property j.val j.property hne)
    have hfj : (f i).val ∈ pair j.val := by simpa only [heq] using hf j
    exact hd (hf i) hfj
  simpa only [Fintype.card_coe] using Fintype.card_le_of_injective f hinj

/-- The localized critical count transfers through supplied disjoint pairs. -/
theorem r_arc_deviation_count {α : Type*} [DecidableEq α]
    {C : Finset ℕ} {D : Finset α} {b : ℕ}
    (hit : ∀ j : ℕ, j + 21 ≤ 301994 →
      ∃ i ∈ C, b + j ≤ i ∧ i < b + j + 21)
    (pair : ℕ → Finset α)
    (hdisj : ∀ i ∈ C, ∀ j ∈ C, i ≠ j → Disjoint (pair i) (pair j))
    (hcover : ∀ i ∈ C, ∃ j ∈ D, j ∈ pair i) :
    14380 ≤ D.card :=
  (r_arc_critical_count hit).trans
    (disjoint_pair_deviation_count pair hdisj hcover)

end Problems.Juggler.CubicCriticalLocation
