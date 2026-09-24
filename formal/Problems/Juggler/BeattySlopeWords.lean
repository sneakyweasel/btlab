import Problems.Juggler.PaperBCertificateRecursion
import Mathlib.NumberTheory.Real.Irrational

/-!
# Binary first passage at a real linear boundary

The boundary parameter is independent of the logarithmic Juggler slope.
Survival uses weak inequalities at every prefix; for an irrational parameter
these are strict at every positive time. The one-step partition is valid even
for rational parameters and includes the empty surviving word.
-/

namespace Problems.Juggler.BeattySlope

open Finset

/-- Every prefix has at least `β` times its length many odd letters. -/
def Survives (β : ℝ) (w : List Branch) : Prop :=
  ∀ k : ℕ, k ≤ w.length → β * k ≤ (oddCount (w.take k) : ℝ)

/-- The endpoint is strictly below the real boundary. -/
def Below (β : ℝ) (w : List Branch) : Prop :=
  (oddCount w : ℝ) < β * w.length

/-- A nonempty word crosses below the boundary for the first time at its end. -/
def FirstPassage (β : ℝ) (w : List Branch) : Prop :=
  w ≠ [] ∧ Below β w ∧
    ∀ k : ℕ, 0 < k → k < w.length → β * k ≤ (oddCount (w.take k) : ℝ)

/-- Surviving binary words at a prescribed length and boundary. -/
noncomputable def survivorWords (β : ℝ) (n : ℕ) : Finset (List Branch) := by
  classical
  exact (allWords n).filter (Survives β)

/-- Exact integer survivor count for the boundary `β`. -/
noncomputable def survivorCount (β : ℝ) (n : ℕ) : ℕ := (survivorWords β n).card

/-- First-passage words at a prescribed length and boundary. -/
noncomputable def passageWords (β : ℝ) (n : ℕ) : Finset (List Branch) := by
  classical
  exact (allWords n).filter (FirstPassage β)

/-- Exact integer first-passage count for the boundary `β`. -/
noncomputable def passageCount (β : ℝ) (n : ℕ) : ℕ := (passageWords β n).card

/-- The strict positive-endpoint count, without constraints on earlier prefixes. -/
noncomputable def endpointCount (β : ℝ) (n : ℕ) : ℕ :=
  ∑ k ∈ range (n+1), if (n : ℝ)*β < k then n.choose k else 0

/-- Sum of `z` to the number of odd letters over the actual surviving words.
The weight may be any real number; positivity is needed only for later estimates. -/
noncomputable def survivorWeight (β z : ℝ) (n : ℕ) : ℝ :=
  ∑ w ∈ survivorWords β n, z ^ oddCount w

/-- Sum of the odd-letter weights over the actual first-passage words. -/
noncomputable def passageWeight (β z : ℝ) (n : ℕ) : ℝ :=
  ∑ w ∈ passageWords β n, z ^ oddCount w

/-- Weighted strict endpoint binomial sum, without earlier prefix constraints. -/
noncomputable def endpointWeight (β z : ℝ) (n : ℕ) : ℝ :=
  ∑ k ∈ range (n+1), if (n : ℝ)*β < k then (n.choose k : ℝ)*z^k else 0

/-- Weight one recovers the exact integer survivor count as a real number. -/
theorem survivorWeight_one (β : ℝ) (n : ℕ) :
    survivorWeight β 1 n = (survivorCount β n : ℝ) := by
  simp [survivorWeight, survivorCount]

/-- Weight one recovers the exact integer first-passage count. -/
theorem passageWeight_one (β : ℝ) (n : ℕ) :
    passageWeight β 1 n = (passageCount β n : ℝ) := by
  simp [passageWeight, passageCount]

/-- Weight one recovers the original strict endpoint binomial count. -/
theorem endpointWeight_one (β : ℝ) (n : ℕ) :
    endpointWeight β 1 n = (endpointCount β n : ℝ) := by
  simp [endpointWeight, endpointCount, Nat.cast_sum, Nat.cast_ite]

/-- There is no strictly positive endpoint at zero depth. -/
theorem endpointWeight_zero (β z : ℝ) : endpointWeight β z 0 = 0 := by
  simp [endpointWeight]

/-- Nonnegative letter weights give nonnegative weighted endpoint counts. -/
theorem endpointWeight_nonneg (β : ℝ) {z : ℝ} (hz : 0 ≤ z) (n : ℕ) :
    0 ≤ endpointWeight β z n := by
  apply sum_nonneg
  intro k _
  split_ifs <;> positivity

/-- No positive integer multiple of an irrational boundary is an integer. -/
theorem mul_ne_nat {β : ℝ} (hβ : Irrational β) {n : ℕ} (hn : 0 < n) (k : ℕ) :
    (n : ℝ)*β ≠ k := by
  exact_mod_cast (hβ.natCast_mul (m := n) (by omega)).ne_rat (k : ℚ)

/-- At an irrational boundary the weak prefix convention is precisely strict
survival at every nonempty prefix. -/
theorem survives_iff_strict {β : ℝ} (hβ : Irrational β) (w : List Branch) :
    Survives β w ↔
      ∀ k : ℕ, 0 < k → k ≤ w.length → β*k < (oddCount (w.take k) : ℝ) := by
  constructor
  · intro hw k hk hkw
    exact (hw k hkw).lt_of_ne (by simpa [mul_comm] using mul_ne_nat hβ hk _)
  · intro hw k hkw
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp
    · exact (hw k hk hkw).le

/-- A surviving word cannot be below the boundary at its own endpoint. -/
theorem Survives.not_below {β : ℝ} {w : List Branch} (hw : Survives β w) :
    ¬ Below β w := by
  have h := hw w.length le_rfl
  simpa [Below] using not_lt_of_ge h

/-- The empty word survives every linear boundary. -/
theorem survives_nil (β : ℝ) : Survives β [] := by
  intro k hk
  have : k = 0 := by simpa using hk
  subst k
  simp

/-- A one-letter extension survives exactly when its base survives and its
new endpoint stays on or above the boundary. -/
theorem survives_concat {β : ℝ} {w : List Branch} {b : Branch} :
    Survives β (w ++ [b]) ↔ Survives β w ∧ ¬ Below β (w ++ [b]) := by
  constructor
  · intro h
    refine ⟨fun k hk => ?_, h.not_below⟩
    have hh := h k (by simp; omega)
    rwa [List.take_append_of_le_length hk] at hh
  · rintro ⟨hw, hgap⟩ k hk
    by_cases hkw : k ≤ w.length
    · rw [List.take_append_of_le_length hkw]
      exact hw k hkw
    · have he : k = (w ++ [b]).length := by
        simp only [List.length_append, List.length_singleton] at hk ⊢
        omega
      subst k
      rw [List.take_length]
      exact le_of_not_gt hgap

/-- A one-letter extension first crosses exactly when its base survives and
its new endpoint is below the boundary. -/
theorem firstPassage_concat {β : ℝ} {w : List Branch} {b : Branch} :
    FirstPassage β (w ++ [b]) ↔ Survives β w ∧ Below β (w ++ [b]) := by
  constructor
  · rintro ⟨-, hgap, hmin⟩
    refine ⟨fun k hk => ?_, hgap⟩
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · simp
    · have hh := hmin k hk0 (by simp; omega)
      rwa [List.take_append_of_le_length hk] at hh
  · rintro ⟨hw, hgap⟩
    refine ⟨by simp, hgap, fun k _ hk => ?_⟩
    have hkw : k ≤ w.length := by
      simp only [List.length_append, List.length_singleton] at hk
      omega
    rw [List.take_append_of_le_length hkw]
    exact hw k hkw

/-- Survivors and first crossings are disjoint at each next depth. -/
theorem survivors_disjoint_passages (β : ℝ) (n : ℕ) :
    Disjoint (survivorWords β (n+1)) (passageWords β (n+1)) := by
  classical
  rw [disjoint_left]
  intro w hw hc
  exact (mem_filter.mp hw).2.not_below (mem_filter.mp hc).2.2.1

/-- Every extension of a survivor is either a survivor or a first crossing,
and every word in those two disjoint classes is such an extension. -/
theorem extensions_eq_survivors_union_passages (β : ℝ) (n : ℕ) :
    (survivorWords β n).biUnion (fun w => {w ++ [Branch.even], w ++ [Branch.odd]}) =
      survivorWords β (n+1) ∪ passageWords β (n+1) := by
  classical
  ext v
  simp only [mem_biUnion, mem_union, mem_insert, mem_singleton,
    survivorWords, passageWords, mem_filter]
  constructor
  · rintro ⟨w, hw, hv⟩
    have hwlen := mem_allWords.mp hw.1
    have hvmem : v ∈ allWords (n+1) := by
      rcases hv with rfl | rfl <;> exact mem_allWords.mpr (by simp [hwlen])
    by_cases hgap : Below β v
    · refine Or.inr ⟨hvmem, ?_⟩
      rcases hv with rfl | rfl <;> exact firstPassage_concat.mpr ⟨hw.2, hgap⟩
    · refine Or.inl ⟨hvmem, ?_⟩
      rcases hv with rfl | rfl <;> exact survives_concat.mpr ⟨hw.2, hgap⟩
  · intro h
    have hvlen : v.length = n+1 := by
      rcases h with ⟨hv, -⟩ | ⟨hv, -⟩ <;> exact mem_allWords.mp hv
    obtain ⟨w, b, rfl⟩ : ∃ w b, v = w ++ [b] := by
      rcases List.eq_nil_or_concat v with rfl | ⟨w, b, rfl⟩
      · simp at hvlen
      · exact ⟨w, b, by simp⟩
    have hwlen : w.length = n := by simpa using hvlen
    have hwsurv : Survives β w := by
      rcases h with ⟨-, hs⟩ | ⟨-, hc⟩
      · exact (survives_concat.mp hs).1
      · exact (firstPassage_concat.mp hc).1
    refine ⟨w, ⟨mem_allWords.mpr hwlen, hwsurv⟩, ?_⟩
    cases b
    · exact Or.inl rfl
    · exact Or.inr rfl

/-- The exact survivor/first-passage recursion holds for every real boundary;
no irrationality or asymptotic assumption is required. -/
theorem survivorCount_add_passageCount (β : ℝ) (n : ℕ) :
    survivorCount β (n+1) + passageCount β (n+1) = 2*survivorCount β n := by
  classical
  have hpair (w : List Branch) :
      ({w ++ [Branch.even], w ++ [Branch.odd]} : Finset (List Branch)).card = 2 := by
    rw [card_insert_of_notMem (by
      simp only [mem_singleton]
      intro h
      exact Branch.noConfusion (append_singleton_inj h).2), card_singleton]
  have hbi := congrArg Finset.card (extensions_eq_survivors_union_passages β n)
  rw [card_union_of_disjoint (survivors_disjoint_passages β n),
    card_biUnion (fun x _ y _ hne => extend_fiber_disjoint hne)] at hbi
  simp only [hpair, sum_const, smul_eq_mul] at hbi
  simpa [survivorCount, passageCount, mul_comm] using hbi.symm

/-- The empty word is the only zero-depth survivor at every boundary. -/
theorem survivorWords_zero (β : ℝ) : survivorWords β 0 = {[]} := by
  classical
  ext w
  simp only [survivorWords, allWords, mem_filter, mem_singleton]
  exact ⟨And.left, fun h => ⟨h, h ▸ survives_nil β⟩⟩

/-- The zero-depth survivor count is one at every boundary. -/
theorem survivorCount_zero (β : ℝ) : survivorCount β 0 = 1 := by
  rw [survivorCount, survivorWords_zero, card_singleton]

/-- The empty surviving word has weight one for every real letter weight. -/
theorem survivorWeight_zero (β z : ℝ) : survivorWeight β z 0 = 1 := by
  simp [survivorWeight, survivorWords_zero, oddCount]

/-- The zero-depth first-passage count is zero. -/
theorem passageCount_zero (β : ℝ) : passageCount β 0 = 0 := by
  classical
  simp [passageCount, passageWords, allWords, FirstPassage]

/-- The crossing edge after `r` odd letters is one more than the natural
floor of `r / β`. Its interpretation as a first-passage time uses `0 < β ≤ 1`. -/
noncomputable def crossingDepth (β : ℝ) (r : ℕ) : ℕ := ⌊(r : ℝ) / β⌋₊ + 1

/-- At a boundary at most one, appending an odd letter to a survivor cannot
make its first crossing below the boundary. -/
theorem not_firstPassage_concat_odd {β : ℝ} (hβ : β ≤ 1) (w : List Branch) :
    ¬ FirstPassage β (w ++ [Branch.odd]) := by
  intro h
  obtain ⟨hs, hb⟩ := firstPassage_concat.mp h
  have hp := hs w.length le_rfl
  rw [List.take_length] at hp
  simp only [Below, List.length_append, List.length_singleton, Nat.cast_add,
    Nat.cast_one, oddCount_append, oddCount] at hb
  nlinarith

/-- Every first-passage word for a boundary at most one ends in an even
letter, with a surviving prefix. -/
theorem FirstPassage.exists_even_prefix {β : ℝ} (hβ : β ≤ 1)
    {w : List Branch} (hw : FirstPassage β w) :
    ∃ v, w = v ++ [Branch.even] ∧ Survives β v := by
  rcases List.eq_nil_or_concat w with rfl | ⟨v, b, rfl⟩
  · exact (hw.1 rfl).elim
  · simp only [List.concat_eq_append] at hw ⊢
    cases b with
    | even => exact ⟨v, rfl, (firstPassage_concat.mp hw).1⟩
    | odd => exact (not_firstPassage_concat_odd hβ v hw).elim

/-- First passage with `r` odd letters can occur only at edge
`floor(r / β) + 1`. The weak-survival convention makes this true for rational
boundaries as well as irrational ones when `0 < β ≤ 1`. -/
theorem FirstPassage.length_eq_crossingDepth {β : ℝ} (hβ0 : 0 < β) (hβ1 : β ≤ 1)
    {w : List Branch} (hw : FirstPassage β w) :
    w.length = crossingDepth β (oddCount w) := by
  obtain ⟨v, rfl, hs⟩ := hw.exists_even_prefix hβ1
  have hp := hs v.length le_rfl
  rw [List.take_length] at hp
  have hb := hw.2.1
  simp only [Below, List.length_append, List.length_singleton, Nat.cast_add,
    Nat.cast_one, oddCount_append, oddCount, add_zero] at hb
  have hf : ⌊(oddCount v : ℝ) / β⌋₊ = v.length := by
    apply (Nat.floor_eq_iff (div_nonneg (Nat.cast_nonneg _) hβ0.le)).2
    constructor
    · exact (le_div_iff₀ hβ0).2 (by nlinarith)
    · exact (div_lt_iff₀ hβ0).2 (by nlinarith)
  simp only [crossingDepth, List.length_append, List.length_singleton,
    oddCount_append, oddCount, add_zero, hf]

/-- Distinct odd-letter counts give strictly ordered crossing edges whenever
the boundary lies in `(0, 1]`. -/
theorem crossingDepth_strictMono {β : ℝ} (hβ0 : 0 < β) (hβ1 : β ≤ 1) :
    StrictMono (crossingDepth β) := by
  intro r s hrs
  have hf := Nat.floor_le (div_nonneg (Nat.cast_nonneg r) hβ0.le)
  have hr : (r : ℝ) + 1 ≤ s := by exact_mod_cast hrs
  have hle : ⌊(r : ℝ)/β⌋₊ + 1 ≤ ⌊(s : ℝ)/β⌋₊ := by
    apply Nat.le_floor
    push_cast
    apply (le_div_iff₀ hβ0).2
    have hfr := (le_div_iff₀ hβ0).1 hf
    nlinarith
  dsimp [crossingDepth]
  omega

/-- Every first-passage word at the `r`-th crossing edge has exactly `r` odd
letters. Thus a letter tilt is constant on each crossing class. -/
theorem FirstPassage.oddCount_eq_of_length_eq_crossingDepth {β : ℝ}
    (hβ0 : 0 < β) (hβ1 : β ≤ 1) {w : List Branch} (hw : FirstPassage β w)
    {r : ℕ} (hlen : w.length = crossingDepth β r) : oddCount w = r := by
  apply (crossingDepth_strictMono hβ0 hβ1).injective
  exact (hw.length_eq_crossingDepth hβ0 hβ1).symm.trans hlen

/-- At a crossing edge, the weighted count is the actual integer count times
one explicit power. No irrationality or nonzero-weight assumption is needed. -/
theorem passageWeight_crossingDepth {β : ℝ} (hβ0 : 0 < β) (hβ1 : β ≤ 1)
    (z : ℝ) (r : ℕ) :
    passageWeight β z (crossingDepth β r) =
      (passageCount β (crossingDepth β r) : ℝ)*z^r := by
  classical
  unfold passageWeight
  calc
    _ = ∑ _w ∈ passageWords β (crossingDepth β r), z^r := by
      apply sum_congr rfl
      intro w hw
      obtain ⟨hwlen, hpass⟩ := mem_filter.mp hw
      rw [hpass.oddCount_eq_of_length_eq_crossingDepth hβ0 hβ1
        (mem_allWords.mp hwlen)]
    _ = _ := by simp [passageCount]

/-- A nonzero tilt can be removed exactly to recover the integer crossing
count; this is an identity at every edge, not an asymptotic equivalence. -/
theorem passageCount_eq_weight_div {β z : ℝ} (hβ0 : 0 < β) (hβ1 : β ≤ 1)
    (hz : z ≠ 0) (r : ℕ) :
    (passageCount β (crossingDepth β r) : ℝ) =
      passageWeight β z (crossingDepth β r)/z^r := by
  rw [passageWeight_crossingDepth hβ0 hβ1]
  exact (mul_div_cancel_right₀ _ (pow_ne_zero _ hz)).symm

end Problems.Juggler.BeattySlope
