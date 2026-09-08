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


end Problems.Juggler
