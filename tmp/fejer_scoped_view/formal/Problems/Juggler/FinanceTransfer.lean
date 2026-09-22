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
import Problems.Juggler.DefectFinance

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
    gcongr
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
    · simp [h2, List.sum_cons]
      omega
    · simp [h2, List.sum_cons]
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

theorem cycPred_injOn {L : ℕ} (_hL : 0 < L) :
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

/-! ### The bridge from the word to the orbit

Theorem 4.7 counts letters of `w`; the sum it bounds runs over states of the orbit.  Nothing
above connects the two.  `follows_get_even` and `follows_get_odd` (`Itinerary.lean`) each give
one direction; together they give the equivalence, and that is the bridge.

The second fact here is what the *prefix* form of the valley count needs.  Counting valleys as
"odd letters whose predecessor is even" injects them into the even letters by taking the
predecessor — but index `0` has no predecessor, so the injection gives only `#valleys ≤ e + 1`
unless some even letter is missed on the other side.  One is: the last.
-/

/-- On a realized itinerary the letter at `i` is odd exactly when the state is. -/
theorem follows_get_odd_iff {n : ℕ} {w : List Branch} (hw : follows n w) {i : ℕ}
    (hi : i < w.length) : w[i] = Branch.odd ↔ (floorPower^[i] n) % 2 = 1 := by
  constructor
  · exact follows_get_odd w hw i hi
  · intro hpar
    cases hb : w[i] with
    | even =>
        have := follows_get_even w hw i hi hb
        omega
    | odd => rfl

/-- `J(n) > n` for odd `n ≥ 3`, since `(n+1)² ≤ n³`. -/
theorem lt_floorPower_odd {n : ℕ} (hn : 3 ≤ n) (hodd : n % 2 = 1) : n < floorPower n := by
  rw [floorPower_odd_eq hodd]
  refine Nat.lt_of_succ_le ((Nat.le_sqrt).mpr ?_)
  nlinarith

/-- **The cycle's last state is even.**  Were it odd, the return `J(x) = n` with `x ≥ n` odd
would force `x = n` and hence `J(n) = n`, which `lt_floorPower_odd` forbids.  So the word ends
in `E`, the even letters outnumber the valleys, and the prefix count gives `#valleys ≤ e`. -/
theorem cycleMin_last_even {n : ℕ} {w : List Branch} (hn : 3 ≤ n) (h : CycleMin n w) :
    (floorPower^[w.length - 1] n) % 2 = 0 := by
  have hlen : 1 ≤ w.length := h.1.2.2
  set m := w.length - 1 with hm
  have hm1 : m + 1 = w.length := by omega
  have hstep : floorPower (floorPower^[m] n) = n := by
    have := cycle_iterate_period h.1
    rw [← hm1] at this
    rwa [Function.iterate_succ_apply' floorPower m n] at this
  have hge : n ≤ floorPower^[m] n := h.2 m (by omega)
  by_contra hcon
  have hoddx : floorPower^[m] n % 2 = 1 := by omega
  have hx1 : 1 ≤ floorPower^[m] n := by omega
  have hle : floorPower^[m] n ≤ floorPower (floorPower^[m] n) :=
    le_floorPower_odd hoddx hx1
  have hxn : floorPower^[m] n = n := by omega
  have hlt : n < floorPower n := lt_floorPower_odd hn (cycleMin_start_odd (by omega) h)
  rw [hxn] at hstep
  omega

/-! ### The coarse three-term bound

`juggler_cycle_finance.md` carries

`Σ 1/(xᵢ ln xᵢ) ≤ e/(n ln n) + (o−e)/(t ln t) + e/(2n² ln n)`

as EXACT — HUMAN PROOF.  Everything it needs is here.  Three classes rather than six: a state
is charged at `n` if odd, at `t` if odd with an odd predecessor, and at `n²` if even.

The reason this form is *robust where the six-term one is not*: it never splits the valleys
into cheap and expensive, and that split is the only place `EE` did damage.  So no hypothesis
about `EE` is needed here, and none appears below.
-/

/-- The three class bounds: the minimum, the first internal, and the even floor. -/
noncomputable def threeBounds (n t : ℝ) : Fin 3 → ℝ := ![n, t, n ^ 2]

theorem sum_comp_fin_three {L : ℕ} (cls : ℕ → Fin 3) (F : Fin 3 → ℝ) :
    ∑ i ∈ Finset.range L, F (cls i)
      = ∑ c : Fin 3, (((Finset.range L).filter fun i => cls i = c).card : ℝ) * F c := by
  rw [← Finset.sum_fiberwise_of_maps_to (g := cls) (fun i _ => Finset.mem_univ (cls i))
    (fun i => F (cls i))]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Finset.sum_congr rfl fun i hi => by rw [(Finset.mem_filter.mp hi).2],
    Finset.sum_const, nsmul_eq_mul]

/-- **The three-term bound.**  Valleys charged at `n`, internals at `t`, evens at `n²`; the
valley count may be replaced by any larger `kA` with the total held fixed, since `n ≤ t` makes
the exchange downhill.  No `EE` hypothesis. -/
theorem threeTerm_bound {L : ℕ} {x : ℕ → ℝ} {n t : ℝ} {cA cB cC kA kB : ℕ}
    (cls : ℕ → Fin 3) (hn : 2 ≤ n) (hnt : n ≤ t)
    (hbound : ∀ i ∈ Finset.range L, threeBounds n t (cls i) ≤ x i)
    (h0 : ((Finset.range L).filter fun i => cls i = 0).card = cA)
    (h1 : ((Finset.range L).filter fun i => cls i = 1).card = cB)
    (h2 : ((Finset.range L).filter fun i => cls i = 2).card = cC)
    (hle : cA ≤ kA) (hsum : cA + cB = kA + kB) :
    ∑ i ∈ Finset.range L, 1 / (x i * Real.log (x i))
      ≤ (kA : ℝ) / (n * Real.log n) + (kB : ℝ) / (t * Real.log t)
        + (cC : ℝ) / (2 * n ^ 2 * Real.log n) := by
  have hall : ∀ c : Fin 3, 2 ≤ threeBounds n t c := by
    intro c
    fin_cases c <;> simp [threeBounds] <;> nlinarith
  have hβ : ∀ i ∈ Finset.range L, 2 ≤ threeBounds n t (cls i) := fun i _ => hall (cls i)
  refine (sum_inv_mul_log_le hβ hbound).trans ?_
  rw [sum_comp_fin_three cls (fun c => 1 / (threeBounds n t c * Real.log (threeBounds n t c)))]
  rw [Fin.sum_univ_three]
  have b0 : threeBounds n t 0 = n := by simp [threeBounds]
  have b1 : threeBounds n t 1 = t := by simp [threeBounds]
  have b2 : threeBounds n t 2 = n ^ 2 := by simp [threeBounds]
  have hlogsq : Real.log (n ^ 2) = 2 * Real.log n := by
    rw [Real.log_pow]; push_cast; ring
  rw [b0, b1, b2, h0, h1, h2, hlogsq]
  have hswap := valley_swap_le (B := 1 / (n * Real.log n)) (C := 1 / (t * Real.log t))
    (inv_mul_log_antitoneOn (Set.mem_Ici.mpr hn) (Set.mem_Ici.mpr (le_trans hn hnt)) hnt)
    hle hsum
  have hswap' : (cA : ℝ) / (n * Real.log n) + (cB : ℝ) / (t * Real.log t)
      ≤ (kA : ℝ) / (n * Real.log n) + (kB : ℝ) / (t * Real.log t) := by
    simpa [div_eq_mul_inv, one_div] using hswap
  have hcast : (cC : ℝ) * (1 / (n ^ 2 * (2 * Real.log n)))
      = (cC : ℝ) / (2 * n ^ 2 * Real.log n) := by ring
  rw [hcast]
  have e0 : (cA : ℝ) * (1 / (n * Real.log n)) = (cA : ℝ) / (n * Real.log n) := by ring
  have e1 : (cB : ℝ) * (1 / (t * Real.log t)) = (cB : ℝ) / (t * Real.log t) := by ring
  rw [e0, e1]
  linarith

/-! ### Harvest: the shape of a cycle word, and the unique fixed point -/

/-- `J` fixes only `1` among positive integers: even states strictly descend and odd states
at least `3` strictly ascend. -/
theorem floorPower_eq_self_iff {n : ℕ} (hn : 1 ≤ n) : floorPower n = n ↔ n = 1 := by
  constructor
  · intro h
    by_contra hne
    have h2 : 2 ≤ n := by omega
    rcases Nat.mod_two_eq_zero_or_one n with he | ho
    · have := floorPower_even_lt h2 he; omega
    · have h3 : 3 ≤ n := by omega
      have := lt_floorPower_odd h3 ho; omega
  · rintro rfl
    decide

/-- A cycle has period at least two: period one would make its minimum a fixed point. -/
theorem cycleMin_length_ge_two {n : ℕ} {w : List Branch} (hn : 3 ≤ n) (h : CycleMin n w) :
    2 ≤ w.length := by
  have hlen : 1 ≤ w.length := h.1.2.2
  by_contra hcon
  have h1 : w.length = 1 := by omega
  have hper : floorPower^[w.length] n = n := cycle_iterate_period h.1
  rw [h1] at hper
  have hodd : n % 2 = 1 := cycleMin_start_odd (by omega) h
  have := lt_floorPower_odd hn hodd
  simp only [Function.iterate_one] at hper
  omega

/-- **Every cycle itinerary reads `OO…E`.**  It starts odd because the minimum is odd; its
second letter is odd because the minimum cannot start an `OE` circuit; and it ends even
because the return would otherwise fix the minimum.  This is strictly stronger than
`1 ≤ cycleCircuitCount w`, which only says some odd run starts somewhere. -/
theorem cycleMin_word_shape {n : ℕ} {w : List Branch} (hn : 3 ≤ n) (h : CycleMin n w) :
    ∃ (h0 : 0 < w.length) (h1 : 1 < w.length) (hL : w.length - 1 < w.length),
      w[0] = Branch.odd ∧ w[1] = Branch.odd ∧ w[w.length - 1] = Branch.even := by
  have hn2 : 2 ≤ n := by omega
  have hlen : 2 ≤ w.length := cycleMin_length_ge_two hn h
  refine ⟨by omega, by omega, by omega, ?_, ?_, ?_⟩
  · exact (follows_get_odd_iff h.1.1 (by omega)).mpr
      (by simpa using cycleMin_start_odd hn2 h)
  · refine (follows_get_odd_iff h.1.1 (by omega)).mpr ?_
    simpa [Function.iterate_one] using cycleMin_succ_odd hn2 h (by omega)
  · have hev := cycleMin_last_even hn h
    cases hb : w[w.length - 1] with
    | even => rfl
    | odd =>
        have := (follows_get_odd_iff h.1.1 (by omega : w.length - 1 < w.length)).mp hb
        omega

/-! ### The letter count is the index count

`oddCount_eq_card` proves the list half of this in `CycleHeightFinance`, which is outside this
barrel.  What the instantiation needs is the orbit form, and it is cheaper to prove that
directly than to import the list form and bridge it.
-/

/-- Mathlib has no `Finset.range_succ` under that name; `CycleHeightFinance` proves its own
for the same reason, and that file is outside this barrel. -/
theorem range_succ_insert (m : ℕ) : Finset.range (m + 1) = insert m (Finset.range m) := by
  ext x
  simp [Finset.mem_range, Finset.mem_insert]
  omega

theorem oddCount_append_singleton (u : List Branch) (b : Branch) :
    oddCount (u ++ [b]) = oddCount u + oddCount [b] := by
  induction u with
  | nil => simp
  | cons c t ih => cases c <;> simp [ih] <;> omega

/-- **The odd letters are the odd states.**  On a realized word the letter count equals the
number of indices carrying an odd state. -/
theorem oddCount_eq_orbit_card {n : ℕ} : ∀ w : List Branch, follows n w →
    oddCount w = ((Finset.range w.length).filter
      fun i => floorPower^[i] n % 2 = 1).card := by
  intro w
  induction w using List.reverseRecOn with
  | nil => intro _; simp
  | append_singleton u b ih =>
      intro hf
      have hu : follows n u := follows_of_append_left hf
      have hlt : u.length < (u ++ [b]).length := by simp
      have hget : (u ++ [b])[u.length] = b := by simp
      have hiff : (floorPower^[u.length] n % 2 = 1) ↔ b = Branch.odd := by
        rw [← hget]
        exact (follows_get_odd_iff hf hlt).symm
      have hlen : (u ++ [b]).length = u.length + 1 := by simp
      have hsub : ∀ i ∈ Finset.range u.length,
          (floorPower^[i] n % 2 = 1) = (floorPower^[i] n % 2 = 1) := fun _ _ => rfl
      rw [oddCount_append_singleton, ih hu, hlen, range_succ_insert, Finset.filter_insert]
      by_cases hb : b = Branch.odd
      · rw [if_pos (hiff.mpr hb), Finset.card_insert_of_notMem (by simp), hb]
        simp [oddCount]
      · have : ¬ (floorPower^[u.length] n % 2 = 1) := fun hc => hb (hiff.mp hc)
        rw [if_neg this]
        cases b with
        | odd => exact absurd rfl hb
        | even => simp [oddCount]

/-- **A cycle is at least half odd.**  Formal expansion gives `2^L < 3^o`, and `3^o ≤ 4^o`
turns that into `L ≤ 2o`, so the even letters never outnumber the odd ones.  This is what lets
the three-term bound's count exchange run: it needs `e ≤ o`. -/
theorem cycle_length_le_two_mul_oddCount {n : ℕ} {w : List Branch}
    (hn : 2 ≤ n) (h : CycleItinerary n w) : w.length ≤ 2 * oddCount w := by
  have hexp : 2 ^ w.length < 3 ^ oddCount w := cycle_itinerary_formally_expanding hn h
  have h34 : (3:ℕ) ^ oddCount w ≤ 4 ^ oddCount w :=
    Nat.pow_le_pow_left (by norm_num) _
  have h4 : (4:ℕ) ^ oddCount w = 2 ^ (2 * oddCount w) := by
    rw [show (4:ℕ) = 2 ^ 2 by norm_num, ← pow_mul]
  have hlt : (2:ℕ) ^ w.length < 2 ^ (2 * oddCount w) + 1 := by omega
  by_contra hcon
  have hge : 2 * oddCount w < w.length := by omega
  have : (2:ℕ) ^ (2 * oddCount w + 1) ≤ 2 ^ w.length :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  have hdouble : (2:ℕ) ^ (2 * oddCount w + 1) = 2 * 2 ^ (2 * oddCount w) := by ring
  have hpos : 0 < (2:ℕ) ^ (2 * oddCount w) := by positivity
  omega

/-! ### The three-term bound from `CycleMin` alone

`threeTerm_bound` is a majorant: it takes the classification and its cardinalities as
hypotheses.  What follows discharges them from `CycleMin n w`, so the displayed inequality
of `juggler_cycle_finance.md` becomes a theorem about a cycle rather than about a supplied
classification.

The classification is *defined* from the state parity rather than bridged to it, which is
what makes the filter identities case splits instead of a translation layer.  Index `0` is
the only place the cyclic predecessor is not `i - 1`, and `cycleMin_last_even` makes it a
valley, never an internal.
-/

/-- **The cyclic three-class classification.**  Even states at `2`, odd states with an odd
cyclic predecessor at `1` (internal), odd states with an even predecessor at `0` (valley). -/
def cycCls (L : ℕ) (par : ℕ → Bool) (i : ℕ) : Fin 3 :=
  if par i then (if par (cycPred L i) then 1 else 0) else 2

theorem cycCls_eq_zero {L : ℕ} {par : ℕ → Bool} {i : ℕ} :
    cycCls L par i = 0 ↔ (par i && !par (cycPred L i)) = true := by
  unfold cycCls
  cases hp : par i <;> cases hq : par (cycPred L i) <;> simp

theorem cycCls_eq_one {L : ℕ} {par : ℕ → Bool} {i : ℕ} :
    cycCls L par i = 1 ↔ (par i && par (cycPred L i)) = true := by
  unfold cycCls
  cases hp : par i <;> cases hq : par (cycPred L i) <;> simp

theorem cycCls_eq_two {L : ℕ} {par : ℕ → Bool} {i : ℕ} :
    cycCls L par i = 2 ↔ (!par i) = true := by
  unfold cycCls
  cases hp : par i <;> cases hq : par (cycPred L i) <;> simp

theorem cycCls_filter_zero (L : ℕ) (par : ℕ → Bool) :
    ((Finset.range L).filter fun i => cycCls L par i = 0)
      = (Finset.range L).filter fun i => par i && !par (cycPred L i) := by
  ext i; simp [cycCls_eq_zero]

theorem cycCls_filter_one (L : ℕ) (par : ℕ → Bool) :
    ((Finset.range L).filter fun i => cycCls L par i = 1)
      = (Finset.range L).filter fun i => par i && par (cycPred L i) := by
  ext i; simp [cycCls_eq_one]

theorem cycCls_filter_two (L : ℕ) (par : ℕ → Bool) :
    ((Finset.range L).filter fun i => cycCls L par i = 2)
      = (Finset.range L).filter fun i => !par i := by
  ext i; simp [cycCls_eq_two]

/-- For a positive index inside the window the cyclic predecessor is the ordinary one. -/
theorem cycPred_of_pos {L i : ℕ} (h1 : 1 ≤ i) (h2 : i < L) : cycPred L i = i - 1 := by
  unfold cycPred
  have : i + (L - 1) = (i - 1) + L := by omega
  rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]

/-- At index zero the cyclic predecessor is the last index. -/
theorem cycPred_zero {L : ℕ} (_hL : 0 < L) : cycPred L 0 = L - 1 := by
  unfold cycPred
  simp

/-- The number of even states equals the number of even letters. -/
theorem evenCount_eq_orbit_card {n : ℕ} {w : List Branch} (h : follows n w) :
    ((Finset.range w.length).filter
        fun i => !(decide (floorPower^[i] n % 2 = 1))).card
      = w.length - oddCount w := by
  classical
  have hodd := oddCount_eq_orbit_card w h
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := Finset.range w.length) (p := fun i => floorPower^[i] n % 2 = 1)
  have e1 : ((Finset.range w.length).filter
      fun i => !(decide (floorPower^[i] n % 2 = 1)))
      = (Finset.range w.length).filter fun i => ¬ (floorPower^[i] n % 2 = 1) := by
    ext i; simp
  rw [e1]
  simp only [Finset.card_range] at hsplit
  omega

/-- **The three-term bound for a cycle minimum.**  Valleys at `n`, internals at
`t = J(n)`, evens at `n²`, with the counts read off the itinerary: `e` valleys,
`2o − L` internals, `e` evens.  No `EE` hypothesis, and no classification supplied. -/
theorem cycleMin_threeTerm {n : ℕ} {w : List Branch} (hn : 3 ≤ n) (h : CycleMin n w) :
    ∑ i ∈ Finset.range w.length,
        1 / ((floorPower^[i] n : ℝ) * Real.log (floorPower^[i] n))
      ≤ ((w.length - oddCount w : ℕ) : ℝ) / ((n : ℝ) * Real.log n)
        + ((2 * oddCount w - w.length : ℕ) : ℝ)
            / ((floorPower n : ℝ) * Real.log (floorPower n))
        + ((w.length - oddCount w : ℕ) : ℝ) / (2 * (n : ℝ) ^ 2 * Real.log n) := by
  classical
  set L := w.length with hL
  set par : ℕ → Bool := fun i => decide (floorPower^[i] n % 2 = 1) with hpar
  have hn2 : 2 ≤ n := by omega
  have hLpos : 0 < L := h.1.2.2
  have hnodd : n % 2 = 1 := cycleMin_start_odd hn2 h
  -- the two count identities
  have hoddcard : ((Finset.range L).filter fun i => par i).card = oddCount w := by
    rw [oddCount_eq_orbit_card w h.1.1]
    congr 1
    ext i; simp [hpar, hL]
  have hevencard : ((Finset.range L).filter fun i => !par i).card = L - oddCount w := by
    simpa [hpar] using evenCount_eq_orbit_card (n := n) (w := w) h.1.1
  have hhalf : L ≤ 2 * oddCount w := cycle_length_le_two_mul_oddCount hn2 h.1
  -- index zero is a valley, never an internal
  have hlast : par (cycPred L 0) = false := by
    rw [cycPred_zero hLpos, hpar]
    simp only [decide_eq_false_iff_not]
    have := cycleMin_last_even hn h
    rw [← hL] at this
    omega
  refine threeTerm_bound (L := L) (x := fun i => (floorPower^[i] n : ℝ))
    (n := (n : ℝ)) (t := (floorPower n : ℝ))
    (cA := ((Finset.range L).filter fun i => cycCls L par i = 0).card)
    (cB := ((Finset.range L).filter fun i => cycCls L par i = 1).card)
    (cC := L - oddCount w)
    (kA := L - oddCount w) (kB := 2 * oddCount w - L)
    (cycCls L par) (by exact_mod_cast hn2) ?_ ?_ rfl rfl ?_ ?_ ?_
  · -- n ≤ t
    have := le_floorPower_odd (x := n) hnodd (by omega)
    exact_mod_cast this
  · -- the class bounds
    intro i hi
    have hiL : i < L := Finset.mem_range.mp hi
    by_cases hpi : par i
    · by_cases hpp : par (cycPred L i)
      · -- internal: the predecessor is odd, so the state is at least t
        have hcls : cycCls L par i = 1 := by simp [cycCls, hpi, hpp]
        have hipos : 1 ≤ i := by
          rcases Nat.eq_zero_or_pos i with rfl | hp
          · rw [hlast] at hpp; exact absurd hpp (by simp)
          · exact hp
        have hprev : floorPower^[i - 1] n % 2 = 1 := by
          rw [cycPred_of_pos hipos hiL] at hpp
          simpa [hpar] using hpp
        have hstep := cycleMin_internal_ge_t hn2 h (i := i - 1) (by omega) hprev
        have hidx : i - 1 + 1 = i := by omega
        rw [hidx] at hstep
        rw [hcls]
        have : threeBounds ((n : ℝ)) ((floorPower n : ℝ)) 1 = (floorPower n : ℝ) := by
          simp [threeBounds]
        rw [this]
        exact_mod_cast hstep
      · -- valley: at least the minimum
        have hcls : cycCls L par i = 0 := by simp [cycCls, hpi, hpp]
        rw [hcls]
        have : threeBounds ((n : ℝ)) ((floorPower n : ℝ)) 0 = (n : ℝ) := by
          simp [threeBounds]
        rw [this]
        exact_mod_cast cycleMin_iterate_ge h i (by omega)
    · -- even: at least n²
      have hcls : cycCls L par i = 2 := by simp [cycCls, hpi]
      have hev : floorPower^[i] n % 2 = 0 := by
        have : ¬ (floorPower^[i] n % 2 = 1) := by simpa [hpar] using hpi
        omega
      rw [hcls]
      have : threeBounds ((n : ℝ)) ((floorPower n : ℝ)) 2 = (n : ℝ) ^ 2 := by
        simp [threeBounds]
      rw [this]
      exact_mod_cast cycleMin_even_ge_sq hn2 h hiL hev
  · -- the even count
    rw [cycCls_filter_two]
    exact hevencard
  · -- valleys inject into evens
    rw [cycCls_filter_zero]
    calc ((Finset.range L).filter fun i => par i && !par (cycPred L i)).card
        ≤ ((Finset.range L).filter fun i => !par i).card := valley_le_even hLpos par
      _ = L - oddCount w := hevencard
  · -- valleys plus internals is the odd count
    rw [cycCls_filter_zero, cycCls_filter_one, valley_add_internal L par, hoddcard]
    have hoL : oddCount w ≤ L := by rw [hL]; exact oddCount_le_length w
    omega

/-- **The certified comparison, in one statement.**  `cycleMin_defect_finance` bounds the
relative defect by the `6/5` unroll of the inverse-log sum, and `cycleMin_threeTerm` bounds
that sum by the three-term charge.  Their composition is what Corollary 4.5 applies to
produce `n_max(L)`, so the per-length table now rests on a single theorem rather than on two
halves joined by hand.  The floor `400` is the one `cycleMin_defect_finance` carries; the
published table runs at `n > 10^6`. -/
theorem cycleMin_defect_threeTerm {n : ℕ} {w : List Branch}
    (hn : 400 ≤ n) (h : CycleMin n w) :
    1 - (2 : ℝ) ^ w.length / 3 ^ oddCount w ≤
      1.2 * (((w.length - oddCount w : ℕ) : ℝ) / ((n : ℝ) * Real.log n)
        + ((2 * oddCount w - w.length : ℕ) : ℝ)
            / ((floorPower n : ℝ) * Real.log (floorPower n))
        + ((w.length - oddCount w : ℕ) : ℝ) / (2 * (n : ℝ) ^ 2 * Real.log n)) := by
  refine (cycleMin_defect_finance hn h).trans ?_
  exact mul_le_mul_of_nonneg_left (cycleMin_threeTerm (by omega) h) (by norm_num)

theorem cycle_length_lt_two_mul_oddCount {n : ℕ} {w : List Branch}
    (hn : 2 ≤ n) (h : CycleItinerary n w) : w.length < 2 * oddCount w := by
  have hexp : 2 ^ w.length < 3 ^ oddCount w := cycle_itinerary_formally_expanding hn h
  have h34 : (3 : ℕ) ^ oddCount w ≤ 4 ^ oddCount w := Nat.pow_le_pow_left (by norm_num) _
  have h4 : (4 : ℕ) ^ oddCount w = 2 ^ (2 * oddCount w) := by
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul]
  have hlt : (2 : ℕ) ^ w.length < 2 ^ (2 * oddCount w) := by omega
  exact (Nat.pow_lt_pow_iff_right (by norm_num)).mp hlt

/-! ### The cheap-valley cap, with no hypothesis about `EE`

`sixTerm_bound_packed` takes the cheap count as `c₁ ≤ k₁`, so a bound on the cheap
valleys that does not mention `EE` turns the packed comparison into a hypothesis-free one.
There is such a bound, and it is half the odd count.

A *cheap* valley is an odd letter whose cyclic predecessor is even and whose cyclic
successor is odd — the start of an odd run of length at least two.  Its successor is an
odd letter with an odd predecessor, which is an internal, and the successor map is
injective.  So the cheap valleys inject into the internals; they are also a subset of the
valleys; and `valley_add_internal` makes those two classes sum to the odd count.  Hence
`2·#cheap ≤ o`, whatever the word does with `EE`.
-/

/-- The cyclic successor. -/
def cycSucc (L i : ℕ) : ℕ := (i + 1) % L

theorem cycSucc_lt {L : ℕ} (hL : 0 < L) (i : ℕ) : cycSucc L i < L :=
  Nat.mod_lt _ hL

/-- On the window the successor undoes the predecessor. -/
theorem cycPred_cycSucc {L i : ℕ} (hi : i < L) : cycPred L (cycSucc L i) = i := by
  unfold cycPred cycSucc
  rcases Nat.lt_or_ge (i + 1) L with h | h
  · rw [Nat.mod_eq_of_lt h]
    have : i + 1 + (L - 1) = i + L := by omega
    rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt hi]
  · have hL1 : i + 1 = L := by omega
    rw [hL1, Nat.mod_self, Nat.zero_add,
      Nat.mod_eq_of_lt (by omega : L - 1 < L)]
    omega

theorem cycSucc_injOn {L : ℕ} (_hL : 0 < L) :
    ∀ i ∈ Finset.range L, ∀ j ∈ Finset.range L, cycSucc L i = cycSucc L j → i = j := by
  intro i hi j hj hij
  have hi' : i < L := Finset.mem_range.mp hi
  have hj' : j < L := Finset.mem_range.mp hj
  have := congrArg (cycPred L) hij
  rwa [cycPred_cycSucc hi', cycPred_cycSucc hj'] at this

/-- **Cheap valleys inject into internals**, by taking the cyclic successor. -/
theorem cheap_le_internal {L : ℕ} (hL : 0 < L) (par : ℕ → Bool) :
    ((Finset.range L).filter
        fun i => par i && !par (cycPred L i) && par (cycSucc L i)).card
      ≤ ((Finset.range L).filter fun i => par i && par (cycPred L i)).card := by
  refine Finset.card_le_card_of_injOn (cycSucc L) (fun i hi => ?_) (fun i hi j hj h => ?_)
  · obtain ⟨hmem, hcond⟩ := Finset.mem_filter.mp hi
    have hi' : i < L := Finset.mem_range.mp hmem
    obtain ⟨hleft, hsucc⟩ := Bool.and_eq_true_iff.mp hcond
    have hodd : par i = true := (Bool.and_eq_true_iff.mp hleft).1
    refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (cycSucc_lt hL i), ?_⟩
    rw [cycPred_cycSucc hi']
    simp [hsucc, hodd]
  · exact cycSucc_injOn hL i (Finset.mem_filter.mp hi).1 j (Finset.mem_filter.mp hj).1 h

/-- Cheap valleys are valleys. -/
theorem cheap_le_valley {L : ℕ} (par : ℕ → Bool) :
    ((Finset.range L).filter
        fun i => par i && !par (cycPred L i) && par (cycSucc L i)).card
      ≤ ((Finset.range L).filter fun i => par i && !par (cycPred L i)).card := by
  refine Finset.card_le_card ?_
  intro i hi
  obtain ⟨hmem, hcond⟩ := Finset.mem_filter.mp hi
  exact Finset.mem_filter.mpr ⟨hmem, (Bool.and_eq_true_iff.mp hcond).1⟩

/-- **At most half the odd letters are cheap valleys.**  No hypothesis about `EE`: the
cheap valleys sit inside the valleys and inject into the internals, and those two classes
partition the odd letters. -/
theorem two_mul_cheap_le_odd {L : ℕ} (hL : 0 < L) (par : ℕ → Bool) :
    2 * ((Finset.range L).filter
        fun i => par i && !par (cycPred L i) && par (cycSucc L i)).card
      ≤ ((Finset.range L).filter fun i => par i).card := by
  have hsplit := valley_add_internal L par
  have h1 := cheap_le_valley (L := L) par
  have h2 := cheap_le_internal hL par
  omega

/-! ### Primitivity, and the distinctness it buys

`CycleItinerary n w` is `follows n w ∧ image n w = n ∧ 1 ≤ w.length`; it does **not** ask
that `L` be the period. So `w ++ w` is again a cycle itinerary, and again a `CycleMin`.
Any statement that charges the minimum once needs primitivity as a hypothesis -- the
display of Theorem 4.7 is one, which is why it carries it.

What primitivity buys is that the orbit states are pairwise distinct. That is the formal
prerequisite for every pigeonhole argument on a cycle, and it was missing: the pigeonhole
itself is already available as `bounded_prefix_not_nodup` in `Residuals.lean`, with
nothing in the cycle layer to feed it.
-/

/-- **Primitive cycle word**: the minimum is not revisited inside it. Equivalently `w` has
the period for its length, since `floorPower^[j] n = n` exactly at multiples of it. -/
def CyclePrimitive (n : ℕ) (w : List Branch) : Prop :=
  ∀ j, 0 < j → j < w.length → floorPower^[j] n ≠ n

/-- A doubled cycle word is a cycle word, and is not primitive. This is the counterexample
that forces the hypothesis rather than a derivation. -/
theorem not_cyclePrimitive_append_self {n : ℕ} {w : List Branch}
    (h : CycleItinerary n w) : ¬ CyclePrimitive n (w ++ w) := by
  intro hp
  have hlen : 0 < w.length := h.2.2
  refine hp w.length hlen ?_ (cycle_iterate_period h)
  simp only [List.length_append]
  omega

/-- **On a primitive cycle the orbit states are pairwise distinct.**

If two indices carried the same state, closing the cycle from the later one would return
to the minimum strictly inside the word. -/
theorem cyclePrimitive_orbit_injOn {n : ℕ} {w : List Branch}
    (h : CycleItinerary n w) (hp : CyclePrimitive n w) :
    ∀ i, i < w.length → ∀ j, j < w.length →
      floorPower^[i] n = floorPower^[j] n → i = j := by
  have key : ∀ i j, i < j → j < w.length →
      floorPower^[i] n = floorPower^[j] n → False := by
    intro i j hij hj hEq
    have hL : floorPower^[w.length] n = n := cycle_iterate_period h
    have h1 : floorPower^[(w.length - j) + i] n
        = floorPower^[(w.length - j) + j] n := by
      rw [Function.iterate_add_apply, Function.iterate_add_apply, hEq]
    have h2 : (w.length - j) + j = w.length := by omega
    rw [h2, hL] at h1
    exact hp _ (by omega) (by omega) h1
  intro i hi j hj hEq
  rcases lt_trichotomy i j with hlt | heq | hgt
  · exact ((key i j hlt hj hEq)).elim
  · exact heq
  · exact ((key j i hgt hi hEq.symm)).elim

/-- The orbit of a primitive cycle carries `L` distinct states, as a `Finset` count. -/
theorem cyclePrimitive_card_orbit {n : ℕ} {w : List Branch}
    (h : CycleItinerary n w) (hp : CyclePrimitive n w) :
    ((Finset.range w.length).image fun i => floorPower^[i] n).card = w.length := by
  rw [Finset.card_image_of_injOn, Finset.card_range]
  intro i hi j hj hEq
  exact cyclePrimitive_orbit_injOn h hp i (Finset.mem_range.mp hi) j
    (Finset.mem_range.mp hj) hEq

/-! ### The no-`EE` hypothesis, and the counts it fixes

Theorem 4.7's display needs the six class counts \(1, o-e-1, 2e-o, 1, o-e-1, e\).
Those follow from the two hypotheses its statement carries, and this section says how.

`NoEE` makes the valleys exactly the even letters: `valley_le_even` injects one way by
`cycPred`, and `NoEE` injects back by `cycSucc`, since the letter after an even one is
then odd and has an even predecessor.  With `valley_add_internal` that fixes the internal
count at `o - e`, and `cheap_le_internal` — proved earlier for the hypothesis-free cap —
immediately bounds the cheap valleys by `o - e`, which is the packing count.  No block
decomposition is needed anywhere.
-/

/-- **No two cyclically adjacent even letters.** -/
def NoEE (L : ℕ) (par : ℕ → Bool) : Prop :=
  ∀ i, i < L → par i = true ∨ par (cycPred L i) = true

/-- Under `NoEE` the even letters inject into the valleys by the cyclic successor. -/
theorem noEE_even_le_valley {L : ℕ} (hL : 0 < L) (par : ℕ → Bool) (h : NoEE L par) :
    ((Finset.range L).filter fun i => !par i).card
      ≤ ((Finset.range L).filter fun i => par i && !par (cycPred L i)).card := by
  refine Finset.card_le_card_of_injOn (cycSucc L) (fun i hi => ?_) (fun i hi j hj hij => ?_)
  · obtain ⟨hmem, hcond⟩ := Finset.mem_filter.mp hi
    have hi' : i < L := Finset.mem_range.mp hmem
    have hieven : par i = false := by simpa using hcond
    have hs : cycSucc L i < L := cycSucc_lt hL i
    have hpred : cycPred L (cycSucc L i) = i := cycPred_cycSucc hi'
    have hodd : par (cycSucc L i) = true := by
      rcases h (cycSucc L i) hs with hx | hx
      · exact hx
      · rw [hpred, hieven] at hx; exact absurd hx (by simp)
    refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hs, ?_⟩
    rw [hpred, hieven, hodd]
    simp
  · exact cycSucc_injOn hL i (Finset.mem_filter.mp hi).1 j (Finset.mem_filter.mp hj).1 hij

/-- **Under `NoEE` the valleys are exactly the even letters.** -/
theorem noEE_valley_card {L : ℕ} (hL : 0 < L) (par : ℕ → Bool) (h : NoEE L par) :
    ((Finset.range L).filter fun i => par i && !par (cycPred L i)).card
      = ((Finset.range L).filter fun i => !par i).card :=
  le_antisymm (valley_le_even hL par) (noEE_even_le_valley hL par h)

/-- **Hence the internals number `o - e`.** -/
theorem noEE_internal_card {L : ℕ} (hL : 0 < L) (par : ℕ → Bool) (h : NoEE L par) :
    ((Finset.range L).filter fun i => par i && par (cycPred L i)).card
        + ((Finset.range L).filter fun i => !par i).card
      = ((Finset.range L).filter fun i => par i).card := by
  have hsplit := valley_add_internal L par
  have hval := noEE_valley_card hL par h
  omega

/-- **And the cheap valleys number at most `o - e`**, which is the packing count.

This is the bound the run-type packing derives from a block decomposition. It needs no
blocks: a cheap valley's successor is an internal and the successor map is injective
(`cheap_le_internal`), and `NoEE` fixes the internal count. -/
theorem noEE_cheap_le {L : ℕ} (hL : 0 < L) (par : ℕ → Bool) (h : NoEE L par) :
    ((Finset.range L).filter
        fun i => par i && !par (cycPred L i) && par (cycSucc L i)).card
        + ((Finset.range L).filter fun i => !par i).card
      ≤ ((Finset.range L).filter fun i => par i).card := by
  have hcheap := cheap_le_internal hL par
  have hcount := noEE_internal_card hL par h
  omega

/-! ### The six-term bound from `CycleMin`, primitivity and `NoEE`

`sixTerm_bound_packed` is the majorant.  What follows discharges its hypotheses from a
cycle, so Theorem 4.7's display becomes a theorem about a cycle carrying exactly the two
hypotheses its statement now names --- and confirms they are *sufficient*, not merely
necessary.

The classification is again defined from the parity, so the class filters are case splits.
Primitivity is what makes class `3` a singleton: `cycleMin_internal_ge_tplus` needs the
predecessor to differ from the minimum, and on a primitive cycle the minimum occurs only
at index `0`, so index `1` is the one internal charged at `t`.
-/

/-- The six-class cyclic classification: the minimum, other cheap valleys, expensive
valleys, the first internal, the other internals, and the evens. -/
def sixCls (L : ℕ) (par : ℕ → Bool) (i : ℕ) : Fin 6 :=
  if par i then
    (if par (cycPred L i) then (if i = 1 then 3 else 4)
      else (if i = 0 then 0 else if par (cycSucc L i) then 1 else 2))
  else 5

theorem sixCls_eq_five {L : ℕ} {par : ℕ → Bool} {i : ℕ} :
    sixCls L par i = 5 ↔ (!par i) = true := by
  unfold sixCls
  cases hp : par i <;> cases hq : par (cycPred L i) <;>
    cases hs : par (cycSucc L i) <;>
    by_cases h0 : i = 0 <;> by_cases h1 : i = 1 <;>
    simp [h0, h1]

theorem sixCls_zero {L : ℕ} {par : ℕ → Bool}
    (h0 : par 0 = true) (hlast : par (cycPred L 0) = false) :
    sixCls L par 0 = 0 := by
  simp [sixCls, h0, hlast]

theorem sixCls_one {L : ℕ} {par : ℕ → Bool}
    (h1 : par 1 = true) (hpred : par (cycPred L 1) = true) :
    sixCls L par 1 = 3 := by
  simp [sixCls, h1, hpred]

theorem sixCls_eq_zero_imp {L : ℕ} {par : ℕ → Bool} {i : ℕ}
    (h : sixCls L par i = 0) : i = 0 := by
  unfold sixCls at h
  by_cases hp : par i
  · by_cases hq : par (cycPred L i)
    · rw [if_pos hp, if_pos hq] at h; split at h <;> exact absurd h (by decide)
    · rw [if_pos hp, if_neg hq] at h
      by_cases hi : i = 0
      · exact hi
      · rw [if_neg hi] at h; split at h <;> exact absurd h (by decide)
  · rw [if_neg hp] at h; exact absurd h (by decide)

theorem sixCls_eq_three_imp {L : ℕ} {par : ℕ → Bool} {i : ℕ}
    (h : sixCls L par i = 3) : i = 1 := by
  unfold sixCls at h
  by_cases hp : par i
  · by_cases hq : par (cycPred L i)
    · rw [if_pos hp, if_pos hq] at h
      by_cases hi : i = 1
      · exact hi
      · rw [if_neg hi] at h; exact absurd h (by decide)
    · rw [if_pos hp, if_neg hq] at h
      split at h
      · exact absurd h (by decide)
      · split at h <;> exact absurd h (by decide)
  · rw [if_neg hp] at h; exact absurd h (by decide)

/-- Class `0` is the singleton `{0}`. -/
theorem sixCls_filter_zero {L : ℕ} {par : ℕ → Bool} (hL : 0 < L)
    (h0 : par 0 = true) (hlast : par (cycPred L 0) = false) :
    ((Finset.range L).filter fun i => sixCls L par i = 0) = {0} := by
  ext i
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
  constructor
  · rintro ⟨-, h⟩; exact sixCls_eq_zero_imp h
  · rintro rfl; exact ⟨hL, sixCls_zero h0 hlast⟩

/-- Class `3` is the singleton `{1}`. -/
theorem sixCls_filter_three {L : ℕ} {par : ℕ → Bool} (hL : 1 < L)
    (h1 : par 1 = true) (hpred : par (cycPred L 1) = true) :
    ((Finset.range L).filter fun i => sixCls L par i = 3) = {1} := by
  ext i
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
  constructor
  · rintro ⟨-, h⟩; exact sixCls_eq_three_imp h
  · rintro rfl; exact ⟨hL, sixCls_one h1 hpred⟩

theorem sixCls_filter_five (L : ℕ) (par : ℕ → Bool) :
    ((Finset.range L).filter fun i => sixCls L par i = 5)
      = (Finset.range L).filter fun i => !par i := by
  ext i; simp [sixCls_eq_five]

/-- Class `4` is the internals with index one removed. -/
theorem sixCls_filter_four (L : ℕ) (par : ℕ → Bool) :
    ((Finset.range L).filter fun i => sixCls L par i = 4)
      = ((Finset.range L).filter fun i => par i && par (cycPred L i)).erase 1 := by
  ext i
  simp only [Finset.mem_erase, Finset.mem_filter, Finset.mem_range]
  constructor
  · intro ⟨hm, hc⟩
    unfold sixCls at hc
    by_cases hp : par i
    · by_cases hq : par (cycPred L i)
      · by_cases hi : i = 1
        · rw [if_pos hp, if_pos hq, if_pos hi] at hc; exact absurd hc (by decide)
        · exact ⟨hi, hm, by simp [hp, hq]⟩
      · rw [if_pos hp, if_neg hq] at hc
        split at hc
        · exact absurd hc (by decide)
        · split at hc <;> exact absurd hc (by decide)
    · rw [if_neg hp] at hc; exact absurd hc (by decide)
  · intro ⟨hi, hm, hc⟩
    obtain ⟨hp, hq⟩ := Bool.and_eq_true_iff.mp hc
    exact ⟨hm, by simp [sixCls, hp, hq, hi]⟩

/-- Classes `1` and `2` split the valleys other than the minimum. -/
theorem sixCls_filter_one_union_two (L : ℕ) (par : ℕ → Bool) :
    ((Finset.range L).filter fun i => sixCls L par i = 1)
        ∪ ((Finset.range L).filter fun i => sixCls L par i = 2)
      = ((Finset.range L).filter fun i => par i && !par (cycPred L i)).erase 0 := by
  ext i
  simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro (⟨hm, hc⟩ | ⟨hm, hc⟩) <;> unfold sixCls at hc <;>
      [skip; skip] <;>
      · by_cases hp : par i
        · by_cases hq : par (cycPred L i)
          · rw [if_pos hp, if_pos hq] at hc; split at hc <;> exact absurd hc (by decide)
          · rw [if_pos hp, if_neg hq] at hc
            by_cases hi : i = 0
            · rw [if_pos hi] at hc; exact absurd hc (by decide)
            · exact ⟨hi, hm, by simp [hp, hq]⟩
        · rw [if_neg hp] at hc; exact absurd hc (by decide)
  · intro ⟨hi, hm, hc⟩
    obtain ⟨hp, hq⟩ := Bool.and_eq_true_iff.mp hc
    have hq' : par (cycPred L i) = false := by simpa using hq
    by_cases hs : par (cycSucc L i)
    · exact Or.inl ⟨hm, by simp [sixCls, hp, hq', hi, hs]⟩
    · exact Or.inr ⟨hm, by simp [sixCls, hp, hq', hi, hs]⟩

theorem sixCls_one_two_disjoint (L : ℕ) (par : ℕ → Bool) :
    Disjoint ((Finset.range L).filter fun i => sixCls L par i = 1)
      ((Finset.range L).filter fun i => sixCls L par i = 2) := by
  refine Finset.disjoint_left.mpr fun i hi hj => ?_
  have h1 := (Finset.mem_filter.mp hi).2
  have h2 := (Finset.mem_filter.mp hj).2
  rw [h1] at h2
  exact absurd h2 (by decide)

/-- Classes `1` and `2` together carry one fewer than the valleys. -/
theorem sixCls_one_two_card {L : ℕ} {par : ℕ → Bool}
    (h0 : (0 : ℕ) ∈ (Finset.range L).filter fun i => par i && !par (cycPred L i)) :
    ((Finset.range L).filter fun i => sixCls L par i = 1).card
        + ((Finset.range L).filter fun i => sixCls L par i = 2).card
      = ((Finset.range L).filter fun i => par i && !par (cycPred L i)).card - 1 := by
  rw [← Finset.card_union_of_disjoint (sixCls_one_two_disjoint L par),
    sixCls_filter_one_union_two, Finset.card_erase_of_mem h0]

/-- Class `1` is the cheap valleys with the minimum removed. -/
theorem sixCls_filter_one (L : ℕ) (par : ℕ → Bool) :
    ((Finset.range L).filter fun i => sixCls L par i = 1)
      = ((Finset.range L).filter
          fun i => par i && !par (cycPred L i) && par (cycSucc L i)).erase 0 := by
  ext i
  simp only [Finset.mem_erase, Finset.mem_filter, Finset.mem_range]
  constructor
  · intro ⟨hm, hc⟩
    unfold sixCls at hc
    by_cases hp : par i
    · by_cases hq : par (cycPred L i)
      · rw [if_pos hp, if_pos hq] at hc; split at hc <;> exact absurd hc (by decide)
      · rw [if_pos hp, if_neg hq] at hc
        by_cases hi : i = 0
        · rw [if_pos hi] at hc; exact absurd hc (by decide)
        · rw [if_neg hi] at hc
          by_cases hs : par (cycSucc L i)
          · exact ⟨hi, hm, by simp [hp, hq, hs]⟩
          · rw [if_neg hs] at hc; exact absurd hc (by decide)
    · rw [if_neg hp] at hc; exact absurd hc (by decide)
  · intro ⟨hi, hm, hc⟩
    obtain ⟨hleft, hs⟩ := Bool.and_eq_true_iff.mp hc
    obtain ⟨hp, hq⟩ := Bool.and_eq_true_iff.mp hleft
    have hq' : par (cycPred L i) = false := by simpa using hq
    exact ⟨hm, by simp [sixCls, hp, hq', hi, hs]⟩

/-- **Theorem 4.7's display, from a cycle.**  The six-term bound holds for a primitive
`CycleMin` whose itinerary contains no `EE`, with the counts the display prints.  The two
hypotheses are therefore sufficient as well as necessary: `not_cyclePrimitive_append_self`
shows the first cannot be dropped, and the `EE` audit shows the second cannot. -/
theorem cycleMin_sixTerm {n : ℕ} {w : List Branch} (hn : 3 ≤ n) (h : CycleMin n w)
    (hprim : CyclePrimitive n w)
    (hee : NoEE w.length (fun i => decide (floorPower^[i] n % 2 = 1)))
    (hlen : 1 < w.length) (h3o : 3 * oddCount w < 2 * w.length) :
    ∑ i ∈ Finset.range w.length,
        1 / ((floorPower^[i] n : ℝ) * Real.log (floorPower^[i] n))
      ≤ (1 : ℝ) / ((n : ℝ) * Real.log n)
        + ((2 * oddCount w - w.length - 1 : ℕ) : ℝ)
            / (((n : ℝ) + 2) * Real.log ((n : ℝ) + 2))
        + ((2 * w.length - 3 * oddCount w : ℕ) : ℝ)
            / ((expensiveValley n : ℝ) * Real.log (expensiveValley n))
        + (1 : ℝ) / ((floorPower n : ℝ) * Real.log (floorPower n))
        + ((2 * oddCount w - w.length - 1 : ℕ) : ℝ)
            / ((floorPower (n + 2) : ℝ) * Real.log (floorPower (n + 2)))
        + ((w.length - oddCount w : ℕ) : ℝ) / (2 * (n : ℝ) ^ 2 * Real.log n) := by
  classical
  set L := w.length with hL
  set par : ℕ → Bool := fun i => decide (floorPower^[i] n % 2 = 1) with hpar
  have hn2 : 2 ≤ n := by omega
  have hLpos : 0 < L := h.1.2.2
  have hnodd : n % 2 = 1 := cycleMin_start_odd hn2 h
  have hlast : floorPower^[L - 1] n % 2 = 0 := by
    have := cycleMin_last_even hn h; rwa [← hL] at this
  -- index 0 is an odd valley, index 1 an odd internal
  have hpar0 : par 0 = true := by simp [hpar, hnodd]
  have hpredzero : par (cycPred L 0) = false := by
    rw [cycPred_zero hLpos, hpar]; simp only [decide_eq_false_iff_not]; omega
  have hsucc : floorPower n % 2 = 1 := cycleMin_succ_odd hn2 h (by omega)
  have hpar1 : par 1 = true := by simp [hpar, hsucc]
  have hpred1 : par (cycPred L 1) = true := by
    rw [cycPred_of_pos le_rfl (by omega)]; simpa using hpar0
  -- the two count identities
  have hoddcard : ((Finset.range L).filter fun i => par i).card = oddCount w := by
    rw [oddCount_eq_orbit_card w h.1.1]; congr 1; ext i; simp [hpar, hL]
  have hevencard : ((Finset.range L).filter fun i => !par i).card = L - oddCount w := by
    simpa [hpar] using evenCount_eq_orbit_card (n := n) (w := w) h.1.1
  have hvalley := noEE_valley_card hLpos par hee
  have hinternal := noEE_internal_card hLpos par hee
  have hcheap := noEE_cheap_le hLpos par hee
  have hhalf : L < 2 * oddCount w := cycle_length_lt_two_mul_oddCount hn2 h.1
  have hoL : oddCount w ≤ L := by rw [hL]; exact oddCount_le_length w
  -- membership facts the cardinality lemmas need
  have hzeromem : (0 : ℕ) ∈ (Finset.range L).filter
      fun i => par i && !par (cycPred L i) := by
    refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hLpos, ?_⟩
    simp [hpar0, hpredzero]
  have honemem : (1 : ℕ) ∈ (Finset.range L).filter
      fun i => par i && par (cycPred L i) := by
    refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), ?_⟩
    simp [hpar1, hpred1]
  refine sixTerm_bound_packed (L := L) (x := fun i => (floorPower^[i] n : ℝ))
    (n := (n : ℝ)) (v := (expensiveValley n : ℝ)) (t := (floorPower n : ℝ))
    (tp := (floorPower (n + 2) : ℝ))
    (c₁ := ((Finset.range L).filter fun i => sixCls L par i = 1).card)
    (c₂ := ((Finset.range L).filter fun i => sixCls L par i = 2).card)
    (k₁ := 2 * oddCount w - L - 1) (k₂ := 2 * L - 3 * oddCount w)
    (c₄ := 2 * oddCount w - L - 1) (c₅ := L - oddCount w)
    (sixCls L par) (by exact_mod_cast hn2) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · -- 2 <= v
    have := le_expensiveValley hn2 hnodd
    have : (2 : ℕ) ≤ expensiveValley n := by omega
    exact_mod_cast this
  · -- 2 <= t
    have := le_floorPower_odd (x := n) hnodd (by omega)
    have : (2 : ℕ) ≤ floorPower n := by omega
    exact_mod_cast this
  · -- 2 <= tp
    have hodd2 : (n + 2) % 2 = 1 := by omega
    have := le_floorPower_odd (x := n + 2) hodd2 (by omega)
    have : (2 : ℕ) ≤ floorPower (n + 2) := by omega
    exact_mod_cast this
  · -- n + 2 <= v
    have := le_expensiveValley hn2 hnodd
    exact_mod_cast this
  · -- the six class bounds
    intro i hi
    have hiL : i < L := Finset.mem_range.mp hi
    by_cases hp : par i
    · have hio : floorPower^[i] n % 2 = 1 := by simpa [hpar] using hp
      by_cases hq : par (cycPred L i)
      · -- internal
        have hipos : 1 ≤ i := by
          rcases Nat.eq_zero_or_pos i with rfl | hx
          · rw [hpredzero] at hq; exact absurd hq (by simp)
          · exact hx
        have hprev : floorPower^[i - 1] n % 2 = 1 := by
          rw [cycPred_of_pos hipos hiL] at hq; simpa [hpar] using hq
        by_cases hi1 : i = 1
        · subst hi1
          have hcls : sixCls L par 1 = 3 := sixCls_one hpar1 hpred1
          rw [hcls]
          have hb : sixBounds ((n : ℝ)) ((expensiveValley n : ℝ))
              ((floorPower n : ℝ)) ((floorPower (n + 2) : ℝ)) 3
              = (floorPower n : ℝ) := by simp [sixBounds]
          rw [hb]
          have := cycleMin_internal_ge_t hn2 h (i := 0) (by omega) (by simpa using hnodd)
          exact_mod_cast this
        · have hcls : sixCls L par i = 4 := by simp [sixCls, hp, hq, hi1]
          rw [hcls]
          have hb : sixBounds ((n : ℝ)) ((expensiveValley n : ℝ))
              ((floorPower n : ℝ)) ((floorPower (n + 2) : ℝ)) 4
              = (floorPower (n + 2) : ℝ) := by simp [sixBounds]
          rw [hb]
          have hne : floorPower^[i - 1] n ≠ n := by
            intro hcon
            exact hprim (i - 1) (by omega) (by omega) hcon
          have := cycleMin_internal_ge_tplus hn2 h (i := i - 1) (by omega) hprev hne
          have hidx : i - 1 + 1 = i := by omega
          rw [hidx] at this
          exact_mod_cast this
      · -- valley
        by_cases hi0 : i = 0
        · subst hi0
          have hcls : sixCls L par 0 = 0 := sixCls_zero hpar0 hpredzero
          rw [hcls]
          have hb : sixBounds ((n : ℝ)) ((expensiveValley n : ℝ))
              ((floorPower n : ℝ)) ((floorPower (n + 2) : ℝ)) 0
              = (n : ℝ) := by simp [sixBounds]
          rw [hb]; simp
        · have hne : floorPower^[i] n ≠ n := fun hcon =>
            hprim i (by omega) hiL hcon
          by_cases hs : par (cycSucc L i)
          · have hcls : sixCls L par i = 1 := by simp [sixCls, hp, hq, hi0, hs]
            rw [hcls]
            have hb : sixBounds ((n : ℝ)) ((expensiveValley n : ℝ))
                ((floorPower n : ℝ)) ((floorPower (n + 2) : ℝ)) 1
                = (n : ℝ) + 2 := by simp [sixBounds]
            rw [hb]
            have := cycleMin_odd_ne_ge hn2 h hiL hio hne
            exact_mod_cast this
          · have hcls : sixCls L par i = 2 := by simp [sixCls, hp, hq, hi0, hs]
            rw [hcls]
            have hb : sixBounds ((n : ℝ)) ((expensiveValley n : ℝ))
                ((floorPower n : ℝ)) ((floorPower (n + 2) : ℝ)) 2
                = (expensiveValley n : ℝ) := by simp [sixBounds]
            rw [hb]
            -- the successor is inside the window: index L-1 is even, so i <= L-2
            have hilt : i + 1 < L := by
              rcases Nat.lt_or_ge (i + 1) L with hx | hx
              · exact hx
              · exfalso
                have : i = L - 1 := by omega
                rw [this, hpar] at hp
                simp only [decide_eq_true_eq] at hp
                omega
            have hsucc' : floorPower^[i + 1] n % 2 = 0 := by
              have hz : ¬ (par (i + 1) = true) := by
                simp only [cycSucc, Nat.mod_eq_of_lt hilt] at hs
                exact hs
              simp only [hpar, decide_eq_true_eq] at hz
              omega
            have := cycleMin_oe_start_ge hn2 h hilt hio hsucc'
            exact_mod_cast this
    · -- even
      have hev : floorPower^[i] n % 2 = 0 := by
        have : ¬ (floorPower^[i] n % 2 = 1) := by simpa [hpar] using hp
        omega
      have hcls : sixCls L par i = 5 := by simp [sixCls, hp]
      rw [hcls]
      have hb : sixBounds ((n : ℝ)) ((expensiveValley n : ℝ))
          ((floorPower n : ℝ)) ((floorPower (n + 2) : ℝ)) 5
          = (n : ℝ) ^ 2 := by simp [sixBounds]
      rw [hb]
      exact_mod_cast cycleMin_even_ge_sq hn2 h hiL hev
  · -- class 0 is a singleton
    rw [sixCls_filter_zero hLpos hpar0 hpredzero]; simp
  · rfl
  · rfl
  · -- class 3 is a singleton
    rw [sixCls_filter_three (by omega) hpar1 hpred1]; simp
  · -- class 4
    rw [sixCls_filter_four, Finset.card_erase_of_mem honemem]
    omega
  · -- class 5
    rw [sixCls_filter_five]; exact hevencard
  · -- the cheap count
    have hcard := sixCls_one_two_card (L := L) (par := par) hzeromem
    have hcheapmem : (0 : ℕ) ∈ (Finset.range L).filter
        fun i => par i && !par (cycPred L i) && par (cycSucc L i) := by
      refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hLpos, ?_⟩
      have hs0 : par (cycSucc L 0) = true := by
        have : cycSucc L 0 = 1 := by
          simp only [cycSucc, Nat.zero_add]
          exact Nat.mod_eq_of_lt (by omega)
        rw [this]; exact hpar1
      simp [hpar0, hpredzero, hs0]
    rw [sixCls_filter_one, Finset.card_erase_of_mem hcheapmem]
    omega
  · -- the exchange total
    have hcard := sixCls_one_two_card (L := L) (par := par) hzeromem
    omega

end Problems.Juggler
