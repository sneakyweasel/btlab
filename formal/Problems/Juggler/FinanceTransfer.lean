/-
# Theorem 4.7's six-term bound: the transfer, and the two arithmetic refinements

Appendix A records the displayed bound

`Σ 1/(xᵢ log xᵢ) ≤ 1/(n log n) + (o−e−1)/((n+2)log(n+2)) + (2e−o)/(v log v)
                  + 1/(t log t) + (o−e−1)/(t₊ log t₊) + e/(2n² log n)`

as "Human, and not attempted … it needs Theorem 3.2 and the orbit.  Arithmetic will not reach
it."  That verdict conflates two things.  *Locating* the iterates is dynamics.  Getting from a
location to the sum is arithmetic, and it is a lemma nobody here has written — the paper spends
one sentence on it ("any deeper odd run or any higher valley only decreases the sum").

This file is that arithmetic.

## The transfer

* `inv_mul_log_antitoneOn` — `x ↦ 1/(x log x)` is antitone on `[2, ∞)`.
* `sum_inv_mul_log_le` — so pointwise lower bounds move through the sum.  This is the whole
  content of "only decreases the sum", and it is where the six-term bound's *shape* comes from:
  any classification of the orbit into classes with lower bounds gives a bound of that shape.
* `sum_inv_mul_log_le_comp` — with the bound constant on each class, the majorant collapses to
  the count-weighted sum, by `Finset.sum_comp`.  The six terms are six fibres.

## The two refinements the six-term bound makes over the three-term one

The coarse form charges every odd-run start at `n` and every internal odd at `t`.  The six-term
form splits each in two, and both splits are arithmetic given the orbit:

* `cycleMin_odd_ne_ge` — a cycle state that is odd and is not the minimum is at least `n + 2`.
  Minimality gives `≥ n`; the state and `n` are both odd, so `n + 1` is excluded by parity.
  This is the `(o−e−1)/((n+2)log(n+2))` term.
* `odd_pow_ge_of_image_ge` — an odd state whose image is at least `n²` satisfies `n⁴ ≤ v³`,
  which is the defining property of the expensive valley `v`.  One `Nat.le_sqrt`.  This is the
  `(2e−o)/(v log v)` term.

## What is still dynamics, and is a hypothesis rather than a theorem

Which state falls in which class.  That is Theorem 3.2 and the packing, and no rearrangement of
this file will produce it.  `sum_inv_mul_log_le_comp` takes it as the hypothesis `hbound`, which
is exactly the honest interface: supply the classification, get the display.
-/

import Problems.Juggler.CycleCore

namespace Problems.Juggler

open Finset

/-! ### The transfer -/

/-- `x ↦ 1/(x log x)` is antitone on `[2, ∞)`. -/
theorem inv_mul_log_antitoneOn :
    AntitoneOn (fun x : ℝ => 1 / (x * Real.log x)) (Set.Ici 2) := by
  intro x hx y hy hxy
  have hx2 : (2:ℝ) ≤ x := hx
  have hy2 : (2:ℝ) ≤ y := hy
  have hlx : 0 < Real.log x := Real.log_pos (by linarith)
  have hmul : x * Real.log x ≤ y * Real.log y := by
    gcongr <;> linarith
  exact one_div_le_one_div_of_le (by positivity) hmul

/-- **Transfer.**  Pointwise lower bounds move through the inverse-log sum.  This is the
paper's "any deeper odd run or any higher valley only decreases the sum". -/
theorem sum_inv_mul_log_le {ι : Type*} {s : Finset ι} {x b : ι → ℝ}
    (hb : ∀ i ∈ s, 2 ≤ b i) (hx : ∀ i ∈ s, b i ≤ x i) :
    ∑ i ∈ s, 1 / (x i * Real.log (x i)) ≤ ∑ i ∈ s, 1 / (b i * Real.log (b i)) :=
  Finset.sum_le_sum fun i hi =>
    inv_mul_log_antitoneOn (Set.mem_Ici.mpr (hb i hi))
      (Set.mem_Ici.mpr (le_trans (hb i hi) (hx i hi))) (hx i hi)

/-- **The classified form.**  With the lower bound constant on each class, the majorant is the
count-weighted sum over classes: the six terms of Theorem 4.7 are six fibres. -/
theorem sum_inv_mul_log_le_comp {ι κ : Type*} [DecidableEq κ] {s : Finset ι} {x : ι → ℝ}
    (cls : ι → κ) (β : κ → ℝ)
    (hβ : ∀ i ∈ s, 2 ≤ β (cls i))
    (hbound : ∀ i ∈ s, β (cls i) ≤ x i) :
    ∑ i ∈ s, 1 / (x i * Real.log (x i))
      ≤ ∑ c ∈ s.image cls,
          ((s.filter fun i => cls i = c).card : ℝ) * (1 / (β c * Real.log (β c))) := by
  refine (sum_inv_mul_log_le hβ hbound).trans ?_
  rw [Finset.sum_comp (fun c : κ => 1 / (β c * Real.log (β c))) cls]
  simp [nsmul_eq_mul]

/-! ### Theorem 4.7's display -/

/-- The six lower bounds of Theorem 4.7, in the paper's order: the cycle minimum `n`, the next
odd integer `n + 2`, the expensive valley `v`, the first internal odd `t`, the later internals
`t₊`, and every even at `n²`. -/
noncomputable def sixBounds (n v t tp : ℝ) : Fin 6 → ℝ := ![n, n + 2, v, t, tp, n ^ 2]

/-- The fibre decomposition of a majorant that is constant on classes. -/
theorem sum_comp_fin_six {L : ℕ} (cls : ℕ → Fin 6) (F : Fin 6 → ℝ) :
    ∑ i ∈ Finset.range L, F (cls i)
      = ∑ c : Fin 6, (((Finset.range L).filter fun i => cls i = c).card : ℝ) * F c := by
  rw [← Finset.sum_fiberwise_of_maps_to (g := cls) (fun i _ => Finset.mem_univ (cls i))
    (fun i => F (cls i))]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Finset.sum_congr rfl fun i hi => by rw [(Finset.mem_filter.mp hi).2],
    Finset.sum_const, nsmul_eq_mul]

/-- **Theorem 4.7's six-term bound.**  Given the classification of the orbit — which is where
Theorem 3.2 and the packing enter, and is a hypothesis here — the inverse-log sum is at most
the count-weighted sum of the six class bounds.  On a cycle the counts are the paper's
`1, o−e−1, 2e−o, 1, o−e−1, e`. -/
theorem sixTerm_bound {L : ℕ} {x : ℕ → ℝ} {n v t tp : ℝ} {c₀ c₁ c₂ c₃ c₄ c₅ : ℕ}
    (cls : ℕ → Fin 6)
    (hn : 2 ≤ n) (hv : 2 ≤ v) (ht : 2 ≤ t) (htp : 2 ≤ tp)
    (hbound : ∀ i ∈ Finset.range L, sixBounds n v t tp (cls i) ≤ x i)
    (h0 : ((Finset.range L).filter fun i => cls i = 0).card = c₀)
    (h1 : ((Finset.range L).filter fun i => cls i = 1).card = c₁)
    (h2 : ((Finset.range L).filter fun i => cls i = 2).card = c₂)
    (h3 : ((Finset.range L).filter fun i => cls i = 3).card = c₃)
    (h4 : ((Finset.range L).filter fun i => cls i = 4).card = c₄)
    (h5 : ((Finset.range L).filter fun i => cls i = 5).card = c₅) :
    ∑ i ∈ Finset.range L, 1 / (x i * Real.log (x i))
      ≤ (c₀ : ℝ) / (n * Real.log n)
        + (c₁ : ℝ) / ((n + 2) * Real.log (n + 2))
        + (c₂ : ℝ) / (v * Real.log v)
        + (c₃ : ℝ) / (t * Real.log t)
        + (c₄ : ℝ) / (tp * Real.log tp)
        + (c₅ : ℝ) / (2 * n ^ 2 * Real.log n) := by
  have hall : ∀ c : Fin 6, 2 ≤ sixBounds n v t tp c := by
    intro c
    fin_cases c <;> simp [sixBounds] <;> nlinarith
  have hβ : ∀ i ∈ Finset.range L, 2 ≤ sixBounds n v t tp (cls i) := fun i _ => hall (cls i)
  refine (sum_inv_mul_log_le hβ hbound).trans ?_
  rw [sum_comp_fin_six cls (fun c => 1 / (sixBounds n v t tp c * Real.log (sixBounds n v t tp c)))]
  rw [Fin.sum_univ_six]
  have hlogsq : Real.log (n ^ 2) = 2 * Real.log n := by
    rw [Real.log_pow]; push_cast; ring
  have b0 : sixBounds n v t tp 0 = n := by simp [sixBounds]
  have b1 : sixBounds n v t tp 1 = n + 2 := by simp [sixBounds]
  have b2 : sixBounds n v t tp 2 = v := by simp [sixBounds]
  have b3 : sixBounds n v t tp 3 = t := by simp [sixBounds]
  have b4 : sixBounds n v t tp 4 = tp := by simp [sixBounds]
  have b5 : sixBounds n v t tp 5 = n ^ 2 := by simp [sixBounds]
  rw [b0, b1, b2, b3, b4, b5, h0, h1, h2, h3, h4, h5, hlogsq]
  ring_nf
  rfl

/-! ### The two arithmetic refinements -/

/-- A cycle state that is odd and is not the minimum is at least `n + 2`: minimality gives
`≥ n`, and parity excludes `n + 1`. -/
theorem cycleMin_odd_ne_ge {n : ℕ} {w : List Branch} {i : ℕ}
    (hn : 2 ≤ n) (h : CycleMin n w) (hi : i < w.length)
    (ho : floorPower^[i] n % 2 = 1) (hne : floorPower^[i] n ≠ n) :
    n + 2 ≤ floorPower^[i] n := by
  have hge : n ≤ floorPower^[i] n := h.2 i hi
  have hnodd : n % 2 = 1 := cycleMin_start_odd hn h
  omega

/-- The expensive valley: an odd state whose image is at least `n²` satisfies `n⁴ ≤ v³`. -/
theorem odd_pow_ge_of_image_ge {v n : ℕ} (hv : v % 2 = 1) (h : n ^ 2 ≤ floorPower v) :
    n ^ 4 ≤ v ^ 3 := by
  rw [floorPower_odd_eq hv] at h
  have := (Nat.le_sqrt).mp h
  calc n ^ 4 = n ^ 2 * n ^ 2 := by ring
    _ ≤ v ^ 3 := this

/-- Paper A's `v`: the least odd integer whose cube is at least `n⁴`. -/
noncomputable def expensiveValley (n : ℕ) : ℕ := sInf {v | v % 2 = 1 ∧ n ^ 4 ≤ v ^ 3}

theorem expensiveValley_le {n x : ℕ} (hx : x % 2 = 1) (h : n ^ 4 ≤ x ^ 3) :
    expensiveValley n ≤ x :=
  Nat.sInf_le ⟨hx, h⟩

/-- **The expensive valley, with no hypothesis left.**  An odd cycle state whose successor is
even satisfies `n⁴ ≤ v³`.  Theorem 3.2 is not needed for this step: the successor *is* an even
cycle state, and `cycleMin_even_ge_sq` already bounds every even state below by `n²`. -/
theorem cycleMin_oe_start_pow_ge {n : ℕ} {w : List Branch} {i : ℕ}
    (hn : 2 ≤ n) (h : CycleMin n w) (hi1 : i + 1 < w.length)
    (ho : floorPower^[i] n % 2 = 1) (he : floorPower^[i + 1] n % 2 = 0) :
    n ^ 4 ≤ (floorPower^[i] n) ^ 3 := by
  have hsucc : floorPower^[i + 1] n = floorPower (floorPower^[i] n) :=
    Function.iterate_succ_apply' floorPower i n
  have hge : n ^ 2 ≤ floorPower (floorPower^[i] n) := by
    rw [← hsucc]
    exact cycleMin_even_ge_sq hn h hi1 he
  exact odd_pow_ge_of_image_ge ho hge

/-- So an `OE`-start is at least `v`, which is the third of the six class bounds — and it is
now a theorem rather than a hypothesis. -/
theorem cycleMin_oe_start_ge {n : ℕ} {w : List Branch} {i : ℕ}
    (hn : 2 ≤ n) (h : CycleMin n w) (hi1 : i + 1 < w.length)
    (ho : floorPower^[i] n % 2 = 1) (he : floorPower^[i + 1] n % 2 = 0) :
    expensiveValley n ≤ floorPower^[i] n :=
  expensiveValley_le ho (cycleMin_oe_start_pow_ge hn h hi1 ho he)

/-- **The first internal odd.**  The successor of any odd cycle state is at least
`t = J(n)`, since the state is odd and at least `n`. -/
theorem cycleMin_internal_ge_t {n : ℕ} {w : List Branch} {i : ℕ}
    (hn : 2 ≤ n) (h : CycleMin n w) (hi : i < w.length)
    (ho : floorPower^[i] n % 2 = 1) :
    floorPower n ≤ floorPower^[i + 1] n := by
  have hge : n ≤ floorPower^[i] n := h.2 i hi
  have hnodd : n % 2 = 1 := cycleMin_start_odd hn h
  rw [Function.iterate_succ_apply' floorPower i n]
  exact floorPower_odd_mono hnodd ho hge

/-- **The later internal odds.**  If the odd predecessor is not the minimum it is at least
`n + 2`, so the successor is at least `t₊ = J(n+2)`. -/
theorem cycleMin_internal_ge_tplus {n : ℕ} {w : List Branch} {i : ℕ}
    (hn : 2 ≤ n) (h : CycleMin n w) (hi : i < w.length)
    (ho : floorPower^[i] n % 2 = 1) (hne : floorPower^[i] n ≠ n) :
    floorPower (n + 2) ≤ floorPower^[i + 1] n := by
  have hpred : n + 2 ≤ floorPower^[i] n := cycleMin_odd_ne_ge hn h hi ho hne
  have hnodd : n % 2 = 1 := cycleMin_start_odd hn h
  have hn2odd : (n + 2) % 2 = 1 := by omega
  rw [Function.iterate_succ_apply' floorPower i n]
  exact floorPower_odd_mono hn2odd ho hpred

/-! ### Why the packing is extremal

Write the itinerary as blocks `O^{aᵢ}E`: there are `e` blocks, one even letter each, and
`Σ aᵢ = o`.  Every block contributes one *valley* (its first odd) and `aᵢ - 1` *internals*, so
the valley count is `e` and the internal count is `o - e` **whatever the run lengths are** —
those two counts are not extremal claims at all.

What the run lengths do decide is how the `e` valleys split.  A block with `aᵢ ≥ 2` has an odd
successor, so its valley is only constrained by minimality and parity: it is *cheap*, bounded
by `n + 2`.  A block with `aᵢ = 1` is an `OE` circuit, whose successor is even, so
`cycleMin_oe_start_ge` forces its valley up to `v`: it is *expensive*.  Cheap valleys
contribute more to the sum, so the extremal configuration is the one with the most of them.

And the number of cheap valleys is bounded by a counting identity, not an optimization:

`#{i : aᵢ ≥ 2} ≤ Σ_{aᵢ ≥ 2} (aᵢ - 1) = Σᵢ (aᵢ - 1) = o - e`

with equality exactly when every run has length one or two.  That is the packing.  A run of
length three trades two cheap valleys for one expensive one, which is the paper's "any deeper
odd run … only decreases the sum" in its second incarnation.
-/

/-- **The packing bound.**  At most `o − e` blocks have a run of two or more, where `o` is the
total odd count `runs.sum` and `e` the number of blocks `runs.length`.  Stated without natural
subtraction. -/
theorem blocks_ge_two_add_length_le_sum :
    ∀ runs : List ℕ, (∀ a ∈ runs, 1 ≤ a) →
      (runs.filter fun a => 2 ≤ a).length + runs.length ≤ runs.sum := by
  intro runs
  induction runs with
  | nil => intro _; simp
  | cons a t ih =>
    intro hpos
    have hta : ∀ b ∈ t, 1 ≤ b := fun b hb => hpos b (List.mem_cons_of_mem a hb)
    have ha : 1 ≤ a := hpos a (List.mem_cons_self ..)
    have h := ih hta
    by_cases h2 : 2 ≤ a
    · simp [List.filter_cons, h2, List.sum_cons]
      omega
    · simp [List.filter_cons, h2, List.sum_cons]
      omega

/-- **Equality is exactly the packing.**  The bound above is tight iff every run has length
one or two — so `(o−e)` blocks of `OOE` with `(2e−o)` of `OE` is not one admissible
configuration among many, it is the unique maximiser of the cheap-valley count. -/
theorem blocks_ge_two_eq_sum_iff :
    ∀ runs : List ℕ, (∀ a ∈ runs, 1 ≤ a) →
      ((runs.filter fun a => 2 ≤ a).length + runs.length = runs.sum ↔ ∀ a ∈ runs, a ≤ 2) := by
  intro runs
  induction runs with
  | nil => intro _; simp
  | cons a t ih =>
    intro hpos
    have hta : ∀ b ∈ t, 1 ≤ b := fun b hb => hpos b (List.mem_cons_of_mem a hb)
    have ha : 1 ≤ a := hpos a (List.mem_cons_self ..)
    have hle := blocks_ge_two_add_length_le_sum t hta
    have hiff := ih hta
    simp only [List.mem_cons, forall_eq_or_imp]
    by_cases h2 : 2 ≤ a
    · rw [List.filter_cons_of_pos (by simpa using h2)]
      simp only [List.length_cons, List.sum_cons]
      constructor
      · intro heq
        exact ⟨by omega, hiff.mp (by omega)⟩
      · rintro ⟨hA, hT⟩
        have := hiff.mpr hT
        omega
    · rw [List.filter_cons_of_neg (by simpa using h2)]
      simp only [List.length_cons, List.sum_cons]
      constructor
      · intro heq
        exact ⟨by omega, hiff.mp (by omega)⟩
      · rintro ⟨_, hT⟩
        have := hiff.mpr hT
        omega

/-- The two block types exhaust the blocks: a run has length one or at least two. -/
theorem blocks_filter_split :
    ∀ runs : List ℕ, (∀ a ∈ runs, 1 ≤ a) →
      (runs.filter fun a => a = 1).length + (runs.filter fun a => 2 ≤ a).length
        = runs.length := by
  intro runs
  induction runs with
  | nil => intro _; simp
  | cons a t ih =>
    intro hpos
    have hta : ∀ b ∈ t, 1 ≤ b := fun b hb => hpos b (List.mem_cons_of_mem a hb)
    have ha : 1 ≤ a := hpos a (List.mem_cons_self ..)
    have h := ih hta
    by_cases h1 : a = 1
    · have h2 : ¬ (2 ≤ a) := by omega
      rw [List.filter_cons_of_pos (by simpa using h1),
        List.filter_cons_of_neg (by simpa using h2)]
      simp only [List.length_cons]
      omega
    · have h2 : 2 ≤ a := by omega
      rw [List.filter_cons_of_neg (by simpa using h1),
        List.filter_cons_of_pos (by simpa using h2)]
      simp only [List.length_cons]
      omega

/-- Hence at least `2e − o` blocks are single-odd `OE` circuits, which is the count of
expensive valleys in Theorem 4.7's display. -/
theorem blocks_eq_one_ge (runs : List ℕ) (hpos : ∀ a ∈ runs, 1 ≤ a) :
    2 * runs.length ≤ (runs.filter fun a => a = 1).length + runs.sum := by
  have hsplit := blocks_filter_split runs hpos
  have hbound := blocks_ge_two_add_length_le_sum runs hpos
  omega


/-! ### From the packing inequality to the paper's counts

`sixTerm_bound` takes the six cardinalities exactly.  The packing gives them as
*inequalities* — at most `o−e−1` cheap valleys besides the minimum, at least `2e−o` expensive
ones — so the two must be bridged, and the bridge is that trading a cheap valley for an
expensive one lowers the majorant.  That needs `v ≥ n+2`, which is immediate from `v`'s
definition rather than from any estimate of `n^{4/3}`.
-/

/-- The expensive valley clears `n + 2`.  Any odd `w ≤ n` has `w³ ≤ n³ < n⁴`, so the least odd
`v` with `n⁴ ≤ v³` exceeds `n`; both are odd, so it clears `n + 2`. -/
theorem le_expensiveValley {n : ℕ} (hn : 2 ≤ n) (hodd : n % 2 = 1) :
    n + 2 ≤ expensiveValley n := by
  have hne : {v | v % 2 = 1 ∧ n ^ 4 ≤ v ^ 3}.Nonempty := by
    refine ⟨2 * n ^ 2 + 1, by omega, ?_⟩
    calc n ^ 4 ≤ n ^ 6 := Nat.pow_le_pow_right (by omega) (by norm_num)
      _ = (n ^ 2) ^ 3 := by ring
      _ ≤ (2 * n ^ 2 + 1) ^ 3 := Nat.pow_le_pow_left (by omega) 3
  have hmem : expensiveValley n % 2 = 1 ∧ n ^ 4 ≤ expensiveValley n ^ 3 :=
    Nat.sInf_mem hne
  obtain ⟨hvodd, hvge⟩ := hmem
  have hlt : n ^ 3 < n ^ 4 := by nlinarith [pow_pos (show 0 < n by omega) 3]
  have hgt : n < expensiveValley n := by
    by_contra hcon
    have hle : expensiveValley n ≤ n := not_lt.mp hcon
    have h1 : expensiveValley n ^ 3 ≤ n ^ 3 := Nat.pow_le_pow_left hle 3
    omega
  omega

/-- **The swap.**  With the valley total fixed, fewer cheap valleys means a smaller majorant. -/
theorem valley_swap_le {B C : ℝ} (hBC : C ≤ B) {c₁ c₂ k₁ k₂ : ℕ}
    (hc : c₁ ≤ k₁) (hsum : c₁ + c₂ = k₁ + k₂) :
    (c₁ : ℝ) * B + (c₂ : ℝ) * C ≤ (k₁ : ℝ) * B + (k₂ : ℝ) * C := by
  have h1 : (c₁ : ℝ) ≤ (k₁ : ℝ) := by exact_mod_cast hc
  have hs : (c₁ : ℝ) + (c₂ : ℝ) = (k₁ : ℝ) + (k₂ : ℝ) := by exact_mod_cast hsum
  have h2 : (c₂ : ℝ) = (k₁ : ℝ) + (k₂ : ℝ) - (c₁ : ℝ) := by linarith
  rw [h2]
  nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ (k₁ : ℝ) - c₁) (by linarith : (0:ℝ) ≤ B - C)]

/-- The cheap-valley majorant dominates the expensive one, which is what makes the swap
downhill: `1/(v log v) ≤ 1/((n+2) log (n+2))` once `n + 2 ≤ v`. -/
theorem expensive_le_cheap {n v : ℝ} (hn : 2 ≤ n + 2) (hv : n + 2 ≤ v) :
    1 / (v * Real.log v) ≤ 1 / ((n + 2) * Real.log (n + 2)) :=
  inv_mul_log_antitoneOn (Set.mem_Ici.mpr hn) (Set.mem_Ici.mpr (le_trans hn hv)) hv

/-- **Theorem 4.7's display from the packing inequality.**  `sixTerm_bound` needs the six
cardinalities exactly; the packing supplies the valley split as inequalities — at most `k₁`
cheap valleys with the valley total fixed.  Since `n + 2 ≤ v` the swap is downhill, so the
paper's counts dominate whatever the actual split is. -/
theorem sixTerm_bound_packed {L : ℕ} {x : ℕ → ℝ} {n v t tp : ℝ} {c₁ c₂ k₁ k₂ c₄ c₅ : ℕ}
    (cls : ℕ → Fin 6)
    (hn : 2 ≤ n) (hv : 2 ≤ v) (ht : 2 ≤ t) (htp : 2 ≤ tp) (hvge : n + 2 ≤ v)
    (hbound : ∀ i ∈ Finset.range L, sixBounds n v t tp (cls i) ≤ x i)
    (h0 : ((Finset.range L).filter fun i => cls i = 0).card = 1)
    (h1 : ((Finset.range L).filter fun i => cls i = 1).card = c₁)
    (h2 : ((Finset.range L).filter fun i => cls i = 2).card = c₂)
    (h3 : ((Finset.range L).filter fun i => cls i = 3).card = 1)
    (h4 : ((Finset.range L).filter fun i => cls i = 4).card = c₄)
    (h5 : ((Finset.range L).filter fun i => cls i = 5).card = c₅)
    (hc : c₁ ≤ k₁) (hsum : c₁ + c₂ = k₁ + k₂) :
    ∑ i ∈ Finset.range L, 1 / (x i * Real.log (x i))
      ≤ (1 : ℝ) / (n * Real.log n)
        + (k₁ : ℝ) / ((n + 2) * Real.log (n + 2))
        + (k₂ : ℝ) / (v * Real.log v)
        + (1 : ℝ) / (t * Real.log t)
        + (c₄ : ℝ) / (tp * Real.log tp)
        + (c₅ : ℝ) / (2 * n ^ 2 * Real.log n) := by
  have hswap := valley_swap_le (B := 1 / ((n + 2) * Real.log (n + 2)))
    (C := 1 / (v * Real.log v)) (expensive_le_cheap (by linarith) hvge) hc hsum
  have hswap' : (c₁ : ℝ) / ((n + 2) * Real.log (n + 2)) + (c₂ : ℝ) / (v * Real.log v)
      ≤ (k₁ : ℝ) / ((n + 2) * Real.log (n + 2)) + (k₂ : ℝ) / (v * Real.log v) := by
    simpa [div_eq_mul_inv, one_div] using hswap
  refine (sixTerm_bound cls hn hv ht htp hbound h0 h1 h2 h3 h4 h5).trans ?_
  linarith

/-! ### The decomposition, counted on indices rather than on blocks

The remaining bridge was "the itinerary decomposes into a run list".  Taken literally that is
false in general: a cycle word may contain `EE` (`cycle_trailing_evens`), and then it does not
split into blocks `O^{a}E` with one even letter each.  The paper's packing is the *extremal*
configuration, not the shape of every word.

So the decomposition is done on indices instead, where nothing has to be assumed.  Each odd
letter is a **valley** if its cyclic predecessor is even and an **internal** if that
predecessor is odd; that is a partition of the odd letters, and the valleys inject into the
even letters by taking the predecessor.  Hence

* `#valleys + #internals = o` — every odd letter is one or the other;
* `#valleys ≤ e` — with equality exactly when no `EE` occurs;
* `#internals ≥ o − e`.

That is the direction the majorant needs.  Fewer valleys and more internals is a *smaller*
sum, because a valley sits at `n`-scale and an internal at `t`-scale, so the paper's counts
`e` and `o − e` dominate whatever the word actually does — `EE` only helps.
-/

/-- The cyclic predecessor of an index in `range L`. -/
def cycPred (L i : ℕ) : ℕ := (i + (L - 1)) % L

theorem cycPred_lt {L : ℕ} (hL : 0 < L) (i : ℕ) : cycPred L i < L :=
  Nat.mod_lt _ hL

theorem cycPred_injOn {L : ℕ} (hL : 0 < L) :
    ∀ i ∈ Finset.range L, ∀ j ∈ Finset.range L, cycPred L i = cycPred L j → i = j := by
  intro i hi j hj hij
  have hi' : i < L := Finset.mem_range.mp hi
  have hj' : j < L := Finset.mem_range.mp hj
  have h : (i + (L - 1)) % L = (j + (L - 1)) % L := hij
  have hmod : i % L = j % L := by
    have := Nat.ModEq.add_right_cancel' (L - 1) (h : Nat.ModEq L _ _)
    simpa [Nat.ModEq] using this
  rwa [Nat.mod_eq_of_lt hi', Nat.mod_eq_of_lt hj'] at hmod

/-- **Every odd letter is a valley or an internal.** -/
theorem valley_add_internal (L : ℕ) (par : ℕ → Bool) :
    ((Finset.range L).filter fun i => par i && !par (cycPred L i)).card
      + ((Finset.range L).filter fun i => par i && par (cycPred L i)).card
      = ((Finset.range L).filter fun i => par i).card := by
  classical
  have key := Finset.card_filter_add_card_filter_not
    (s := (Finset.range L).filter fun i => par i = true)
    (p := fun i => par (cycPred L i) = true)
  simp only [Finset.filter_filter] at key
  have e1 : ((Finset.range L).filter fun i => par i && par (cycPred L i))
      = (Finset.range L).filter fun i => par i = true ∧ par (cycPred L i) = true := by
    ext i; simp
  have e2 : ((Finset.range L).filter fun i => par i && !par (cycPred L i))
      = (Finset.range L).filter fun i => par i = true ∧ ¬ (par (cycPred L i) = true) := by
    ext i; simp
  rw [e1, e2, ← key, add_comm]

/-- **Valleys inject into even letters** by taking the cyclic predecessor. -/
theorem valley_le_even {L : ℕ} (hL : 0 < L) (par : ℕ → Bool) :
    ((Finset.range L).filter fun i => par i && !par (cycPred L i)).card
      ≤ ((Finset.range L).filter fun i => !par i).card := by
  refine Finset.card_le_card_of_injOn (cycPred L) (fun i hi => ?_) (fun i hi j hj h => ?_)
  · obtain ⟨hmem, hcond⟩ := Finset.mem_filter.mp hi
    refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (cycPred_lt hL i), ?_⟩
    simpa using (Bool.and_eq_true_iff.mp hcond).2
  · exact cycPred_injOn hL i (Finset.mem_filter.mp hi).1 j (Finset.mem_filter.mp hj).1 h

/-- **Hence at least `o − e` internals**, which is the direction the majorant needs. -/
theorem odd_le_internal_add_even {L : ℕ} (hL : 0 < L) (par : ℕ → Bool) :
    ((Finset.range L).filter fun i => par i).card
      ≤ ((Finset.range L).filter fun i => par i && par (cycPred L i)).card
        + ((Finset.range L).filter fun i => !par i).card := by
  have hsplit := valley_add_internal L par
  have hinj := valley_le_even hL par
  omega

/-! ### The exchange in general: three classes, majorized

The valley/internal exchange is the third of the same kind, and rather than write it a third
time the general form is stated once.  With the class contributions *decreasing* and the actual
cardinalities dominated in partial sums by the target ones at equal totals, the actual majorant
is at most the target.  Abel summation collapses to

`Σ(kᵢ − cᵢ)wᵢ = (k₁−c₁)(w₁−w₂) + (k₁+k₂−c₁−c₂)(w₂−w₃)`,

both terms nonnegative.  `valley_swap_le` is the two-class case.
-/

/-- **Majorization on three classes.**  Decreasing contributions, partial sums dominated,
equal totals. -/
theorem majorize_three {w₁ w₂ w₃ : ℝ} (h12 : w₂ ≤ w₁) (h23 : w₃ ≤ w₂)
    {c₁ c₂ c₃ k₁ k₂ k₃ : ℕ}
    (h1 : c₁ ≤ k₁) (h2 : c₁ + c₂ ≤ k₁ + k₂) (htot : c₁ + c₂ + c₃ = k₁ + k₂ + k₃) :
    (c₁ : ℝ) * w₁ + (c₂ : ℝ) * w₂ + (c₃ : ℝ) * w₃
      ≤ (k₁ : ℝ) * w₁ + (k₂ : ℝ) * w₂ + (k₃ : ℝ) * w₃ := by
  have a1 : (c₁ : ℝ) ≤ (k₁ : ℝ) := by exact_mod_cast h1
  have a2 : (c₁ : ℝ) + (c₂ : ℝ) ≤ (k₁ : ℝ) + (k₂ : ℝ) := by exact_mod_cast h2
  have a3 : (c₁ : ℝ) + (c₂ : ℝ) + (c₃ : ℝ) = (k₁ : ℝ) + (k₂ : ℝ) + (k₃ : ℝ) := by
    exact_mod_cast htot
  have hc3 : (c₃ : ℝ) = (k₁ : ℝ) + (k₂ : ℝ) + (k₃ : ℝ) - (c₁ : ℝ) - (c₂ : ℝ) := by linarith
  rw [hc3]
  nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ (k₁ : ℝ) - c₁)
      (by linarith : (0:ℝ) ≤ w₁ - w₂),
    mul_nonneg (by linarith : (0:ℝ) ≤ ((k₁ : ℝ) + k₂) - ((c₁ : ℝ) + c₂))
      (by linarith : (0:ℝ) ≤ w₂ - w₃)]

/-- An odd state never exceeds its own image: `x ≤ J(x)`, since `x² ≤ x³`. -/
theorem le_floorPower_odd {x : ℕ} (hx : x % 2 = 1) (h1 : 1 ≤ x) : x ≤ floorPower x := by
  rw [floorPower_odd_eq hx]
  refine (Nat.le_sqrt).mpr ?_
  calc x * x = x ^ 2 := by ring
    _ ≤ x ^ 3 := Nat.pow_le_pow_right h1 (by norm_num)

/-- The internal majorant is below the cheap-valley majorant: `1/(t₊ log t₊) ≤
1/((n+2) log (n+2))`, because `n + 2 ≤ J(n+2)`. -/
theorem internal_le_cheap {n tp : ℝ} (hn : 2 ≤ n + 2) (htp : n + 2 ≤ tp) :
    1 / (tp * Real.log tp) ≤ 1 / ((n + 2) * Real.log (n + 2)) :=
  inv_mul_log_antitoneOn (Set.mem_Ici.mpr hn) (Set.mem_Ici.mpr (le_trans hn htp)) htp

/-- **The expensive valley sits below the first internal**: `v ≤ t = J(n)` for odd `n ≥ 9`.

The route through `n³ ≤ t²` forces a `3/2` exponent and lands on a degree-nine comparison.
Naming the witness avoids it entirely.  With `s = ⌊√n⌋` and `s'` the largest odd number at
most `s`, the witness is `n·s'`:

* `(n s')² = n² s'² ≤ n² · n = n³`, so `n s' ≤ ⌊√(n³)⌋ = t`;
* `(n s')³ = n³ s'³ ≥ n³ · n = n⁴`, since `n < (s+1)² ≤ s'³` once `s ≥ 3`;
* and `n s'` is odd, being a product of two odds.

Everything is degree three. -/
theorem expensiveValley_le_floorPower {n : ℕ} (hn : 9 ≤ n) (hodd : n % 2 = 1) :
    expensiveValley n ≤ floorPower n := by
  set s := Nat.sqrt n with hsdef
  have hsq : s * s ≤ n := Nat.sqrt_le n
  have hlt : n < (s + 1) * (s + 1) := Nat.lt_succ_sqrt n
  have hs3 : 3 ≤ s := by
    by_contra hcon
    have hs2 : s ≤ 2 := by omega
    nlinarith
  set s' := if s % 2 = 1 then s else s - 1 with hs'def
  have hs'odd : s' % 2 = 1 := by rw [hs'def]; split <;> omega
  have hs'le : s' ≤ s := by rw [hs'def]; split <;> omega
  have hs'ge : 3 ≤ s' := by rw [hs'def]; split <;> omega
  have hn_le : n ≤ s' * s' * s' := by
    have hcase : s + 1 ≤ s' + 2 := by rw [hs'def]; split <;> omega
    have h1 : (s + 1) * (s + 1) ≤ (s' + 2) * (s' + 2) := Nat.mul_le_mul hcase hcase
    have h2 : (s' + 2) * (s' + 2) ≤ s' * s' * s' := by
      obtain ⟨k, hk⟩ : ∃ k, s' = 3 + k := ⟨s' - 3, by omega⟩
      rw [hk]
      nlinarith
    omega
  have hodd' : (n * s') % 2 = 1 := by
    rw [Nat.mul_mod, hodd, hs'odd]
  have hcube : n ^ 4 ≤ (n * s') ^ 3 := by
    have : (n * s') ^ 3 = n ^ 3 * (s' * s' * s') := by ring
    rw [this]
    calc n ^ 4 = n ^ 3 * n := by ring
      _ ≤ n ^ 3 * (s' * s' * s') := Nat.mul_le_mul_left _ hn_le
  have hmem : expensiveValley n ≤ n * s' := expensiveValley_le hodd' hcube
  have hle : n * s' ≤ floorPower n := by
    rw [floorPower_odd_eq hodd]
    refine (Nat.le_sqrt).mpr ?_
    calc n * s' * (n * s') = n * n * (s' * s') := by ring
      _ ≤ n * n * n := Nat.mul_le_mul_left _ (le_trans (Nat.mul_le_mul hs'le hs'le) hsq)
      _ = n ^ 3 := by ring
  omega

/-- And below the later internals: `v ≤ t₊ = J(n+2)`, by monotonicity of `J` on odds. -/
theorem expensiveValley_le_floorPower_succ {n : ℕ} (hn : 9 ≤ n) (hodd : n % 2 = 1) :
    expensiveValley n ≤ floorPower (n + 2) :=
  le_trans (expensiveValley_le_floorPower hn hodd)
    (floorPower_odd_mono hodd (by omega) (by omega))

/-- **The last ordering.**  The internal majorant sits below the expensive-valley majorant,
so the three class contributions are linearly ordered — cheap, expensive, internal — and
`majorize_three` applies to Theorem 4.7's display. -/
theorem internal_le_expensive {v tp : ℝ} (hv : 2 ≤ v) (hvtp : v ≤ tp) :
    1 / (tp * Real.log tp) ≤ 1 / (v * Real.log v) :=
  inv_mul_log_antitoneOn (Set.mem_Ici.mpr hv) (Set.mem_Ici.mpr (le_trans hv hvtp)) hvtp

/-- **The minimum's successor is odd**, so the minimum is always a *cheap* valley.

Theorem 4.7's display puts one valley at `n` and `o−e−1` further cheap ones at `n+2`, for
`o−e` cheap valleys in all.  That is only an upper bound if the minimum is one of them: if the
minimum started an `OE` circuit there could be `o−e` cheap valleys *besides* it, and the
majorant would exceed the display, since `1/((n+2)log(n+2)) > 1/(v log v)`.

It cannot.  If `J(n)` were even it would be an even cycle state, hence at least `n²` by
`cycleMin_even_ge_sq`; but `J(n) = ⌊√(n³)⌋ < n²` because `n³ < n⁴`.  So the minimum is
followed by another odd letter and sits in a block with a run of at least two. -/
theorem cycleMin_succ_odd {n : ℕ} {w : List Branch} (hn : 2 ≤ n) (h : CycleMin n w)
    (h1 : 1 < w.length) : floorPower n % 2 = 1 := by
  by_contra hcon
  have heven : floorPower^[1] n % 2 = 0 := by
    rw [Function.iterate_one]
    omega
  have hge : n ^ 2 ≤ floorPower^[1] n := cycleMin_even_ge_sq hn h h1 heven
  rw [Function.iterate_one] at hge
  have hodd : n % 2 = 1 := cycleMin_start_odd hn h
  rw [floorPower_odd_eq hodd] at hge
  have hlt : Nat.sqrt (n ^ 3) < n ^ 2 := by
    by_contra hc
    have hge2 : n ^ 2 ≤ Nat.sqrt (n ^ 3) := by omega
    have hsq := (Nat.le_sqrt).mp hge2
    have hpos : 0 < n ^ 3 := by positivity
    have he : n ^ 2 * n ^ 2 = n ^ 3 * n := by ring
    have hmul : n ^ 3 * 2 ≤ n ^ 3 * n := Nat.mul_le_mul (le_refl _) (by omega)
    omega
  omega

end Problems.Juggler
