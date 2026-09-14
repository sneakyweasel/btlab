import Problems.Juggler.FateChernoff

namespace Problems.Juggler

open Finset
open scoped Classical

/-!
# The collapsed component: fiber profiles and the next-letter bias

The exact enumeration of `research.juggler_sequence.cylinder_energy_measure` found that at
every computable scale the per-cylinder statistics of Paper C's Section 9 hypotheses are
dominated by *collapse*: a start whose walk has dipped near the envelope has contracted onto
a bounded value, and its next letter is the parity of that value. This file is the exact
layer of the observation that the collapsed mass, taken as a whole, is nearly fair.

For a finite set `S` of starts and a depth `t`, `Collapse.fiber S t v` is the number of starts
whose `t`-th iterate is `v`, `Collapse.window S t a b` the starts whose iterate lies in
`[a, b]`, and `Collapse.windowBias` the next-letter bias of the window, the starts with odd
iterate minus those with even iterate. Three exact facts:

* the bias is an alternating sum of fiber sizes, `-Σ_{v ∈ [a,b]} (-1)^v fiber(v)`
  (`Collapse.windowBias_eq_sum`), hence bounded by the total variation of the fiber
  profile over the window plus one fiber (`Collapse.abs_windowBias_le`, on the
  summation-by-parts bound `Collapse.abs_alt_sum_le`);
* one step of the map sums fibers over preimages: `fiber(t+1, v)` is the sum of the depth-`t`
  fibers over the even numbers of `[v², (v+1)²)`, the even branch, plus the sum over the odd
  preimages, at most one (`Collapse.fiber_succ`, `Collapse.fiber_succ_eq`, on the even-block
  description `Collapse.pre_filter_even`);
* the even branch smooths: if the depth-`t` profile lies between `m` and `M` on the double
  block `[v², (v+2)²)`, consecutive block sums differ by at most `(v+1)(M - m) + 2M`
  (`Collapse.blockSum_sub_le`, on the counts `v ≤ evenCount v ≤ v + 1`).

Together (`Collapse.collapse_bias_le`): the next-letter bias of the starts whose `(t+1)`-st
iterate lies in `[a, b]` is at most `Σ_{v ∈ [a,b)} ((v+1)(M_v - m_v) + 2 M_v)`, plus twice the
mass arriving through odd preimages, plus one fiber. When the depth-`t` profile is smooth,
`M_v - m_v` of order `f̄/v` on a double block of a value `v` of size `f̄ v`, the first term is
`O(f̄)` per value against a window mass of `f̄ v` per value: the collapsed mass entering
through the even branch is fair up to a relative `O(1/v)`. What is not here: any bound on the
variation of a fiber profile (the analytic content, a smoothness statement about the
contracting composite map), and the parity of the odd-preimage mass, which is the share law
at bounded scale. Not a halt theorem.
-/

namespace Collapse

/-- The fiber of the value `v` at depth `t`: the starts of `S` whose `t`-th iterate is `v`. -/
noncomputable def fiber (S : Finset ℕ) (t v : ℕ) : ℕ :=
  (S.filter fun n => floorPower^[t] n = v).card

/-- The starts of `S` whose `t`-th iterate lies in the window `[a, b]`. -/
noncomputable def window (S : Finset ℕ) (t a b : ℕ) : Finset ℕ :=
  S.filter fun n => floorPower^[t] n ∈ Icc a b

/-- The next-letter bias of the window: the starts of the window whose `t`-th iterate is odd
(next letter `O`) minus those whose `t`-th iterate is even. -/
noncomputable def windowBias (S : Finset ℕ) (t a b : ℕ) : ℝ :=
  (((window S t a b).filter fun n => floorPower^[t] n % 2 = 1).card : ℝ)
    - ((window S t a b).filter fun n => floorPower^[t] n % 2 = 0).card

/-! ### The window is the sum of its fibers -/

/-- The starts of the window whose iterate satisfies `p` are counted by the fibers over the
values of `[a, b]` satisfying `p`. -/
theorem card_filter_window (S : Finset ℕ) (t a b : ℕ) (p : ℕ → Prop) [DecidablePred p] :
    ((window S t a b).filter fun n => p (floorPower^[t] n)).card
      = ∑ v ∈ (Icc a b).filter p, fiber S t v := by
  rw [card_eq_sum_card_fiberwise (f := fun n => floorPower^[t] n) (t := (Icc a b).filter p)]
  · refine sum_congr rfl fun v hv => ?_
    rw [mem_filter] at hv
    unfold fiber window
    congr 1
    ext n
    simp only [mem_filter]
    constructor
    · rintro ⟨⟨⟨hS, -⟩, -⟩, hv'⟩
      exact ⟨hS, hv'⟩
    · rintro ⟨hS, hv'⟩
      exact ⟨⟨⟨hS, by rw [hv']; exact hv.1⟩, by rw [hv']; exact hv.2⟩, hv'⟩
  · intro n hn
    rw [Finset.mem_coe, mem_filter, window, mem_filter] at hn
    rw [Finset.mem_coe, mem_filter]
    exact ⟨hn.1.2, hn.2⟩

theorem card_window (S : Finset ℕ) (t a b : ℕ) :
    (window S t a b).card = ∑ v ∈ Icc a b, fiber S t v := by
  have h := card_filter_window S t a b (fun _ => True)
  rw [filter_true_of_mem (fun _ _ => trivial), filter_true_of_mem (fun _ _ => trivial)] at h
  exact h

/-- The bias is the alternating sum of the fibers. -/
theorem windowBias_eq_sum (S : Finset ℕ) (t a b : ℕ) :
    windowBias S t a b = -∑ v ∈ Icc a b, (-1 : ℝ) ^ v * fiber S t v := by
  unfold windowBias
  rw [card_filter_window S t a b (fun v => v % 2 = 1),
    card_filter_window S t a b (fun v => v % 2 = 0)]
  push_cast
  rw [← sum_filter_add_sum_filter_not (Icc a b) (fun v => v % 2 = 1)
    (fun v => (-1 : ℝ) ^ v * fiber S t v)]
  have hodd : ∀ v ∈ (Icc a b).filter (fun v => v % 2 = 1),
      (-1 : ℝ) ^ v * fiber S t v = -(fiber S t v : ℝ) := by
    intro v hv
    rw [mem_filter] at hv
    rw [Odd.neg_one_pow (Nat.odd_iff.mpr hv.2)]
    ring
  have heven : ∀ v ∈ (Icc a b).filter (fun v => ¬ v % 2 = 1),
      (-1 : ℝ) ^ v * fiber S t v = (fiber S t v : ℝ) := by
    intro v hv
    rw [mem_filter] at hv
    rw [Even.neg_one_pow (Nat.even_iff.mpr (Nat.mod_two_ne_one.mp hv.2))]
    ring
  rw [sum_congr rfl hodd, sum_congr rfl heven, sum_neg_distrib]
  have hfilt : (Icc a b).filter (fun v => ¬ v % 2 = 1)
      = (Icc a b).filter (fun v => v % 2 = 0) := by
    apply filter_congr
    intro v _
    exact Nat.mod_two_ne_one
  rw [hfilt]
  ring

/-! ### An alternating sum is bounded by the total variation -/

/-- Summation by parts: `|Σ_{i<n} (-1)^i h_i| ≤ Σ_{i<n-1} |h_{i+1} - h_i| + h_{n-1}` for
nonnegative `h`. -/
theorem abs_alt_sum_le (h : ℕ → ℝ) (n : ℕ) (hn : 1 ≤ n) (hh : ∀ i < n, 0 ≤ h i) :
    |∑ i ∈ range n, (-1 : ℝ) ^ i * h i|
      ≤ ∑ i ∈ range (n - 1), |h (i + 1) - h i| + h (n - 1) := by
  have hparts := Finset.sum_range_by_parts h (fun i => (-1 : ℝ) ^ i) n
  simp only [smul_eq_mul] at hparts
  have hG : ∀ k, |∑ i ∈ range k, (-1 : ℝ) ^ i| ≤ 1 := by
    intro k
    rw [neg_one_geom_sum]
    split_ifs <;> simp
  have hsum : ∑ i ∈ range n, (-1 : ℝ) ^ i * h i
      = ∑ i ∈ range n, h i * (-1 : ℝ) ^ i := by
    refine sum_congr rfl fun i _ => ?_
    ring
  rw [hsum, hparts]
  have hlast : 0 ≤ h (n - 1) := hh (n - 1) (by omega)
  have h1 : |h (n - 1) * ∑ i ∈ range n, (-1 : ℝ) ^ i| ≤ h (n - 1) := by
    rw [abs_mul, abs_of_nonneg hlast]
    exact mul_le_of_le_one_right hlast (hG n)
  have h2 : |∑ i ∈ range (n - 1), (h (i + 1) - h i) * ∑ j ∈ range (i + 1), (-1 : ℝ) ^ j|
      ≤ ∑ i ∈ range (n - 1), |h (i + 1) - h i| := by
    refine le_trans (abs_sum_le_sum_abs _ _) (sum_le_sum fun i _ => ?_)
    rw [abs_mul]
    exact mul_le_of_le_one_right (abs_nonneg _) (hG _)
  calc |h (n - 1) * ∑ i ∈ range n, (-1 : ℝ) ^ i
        - ∑ i ∈ range (n - 1), (h (i + 1) - h i) * ∑ j ∈ range (i + 1), (-1 : ℝ) ^ j|
      ≤ |h (n - 1) * ∑ i ∈ range n, (-1 : ℝ) ^ i|
        + |∑ i ∈ range (n - 1), (h (i + 1) - h i) * ∑ j ∈ range (i + 1), (-1 : ℝ) ^ j| :=
        abs_sub _ _
    _ ≤ h (n - 1) + ∑ i ∈ range (n - 1), |h (i + 1) - h i| := add_le_add h1 h2
    _ = ∑ i ∈ range (n - 1), |h (i + 1) - h i| + h (n - 1) := add_comm _ _

theorem Icc_eq_Ico (a b : ℕ) : Icc a b = Ico a (b + 1) := by
  ext x
  simp

/-- **The bias is bounded by the variation of the fiber profile.** -/
theorem abs_windowBias_le (S : Finset ℕ) (t a b : ℕ) (hab : a ≤ b) :
    |windowBias S t a b|
      ≤ ∑ v ∈ Ico a b, |(fiber S t (v + 1) : ℝ) - fiber S t v| + fiber S t b := by
  rw [windowBias_eq_sum, abs_neg, Icc_eq_Ico, sum_Ico_eq_sum_range]
  have hsigns : ∑ k ∈ range (b + 1 - a), (-1 : ℝ) ^ (a + k) * fiber S t (a + k)
      = (-1 : ℝ) ^ a * ∑ k ∈ range (b + 1 - a), (-1 : ℝ) ^ k * fiber S t (a + k) := by
    rw [mul_sum]
    refine sum_congr rfl fun k _ => ?_
    rw [pow_add]
    ring
  rw [hsigns, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
  have hn : 1 ≤ b + 1 - a := by omega
  have h := abs_alt_sum_le (fun k => (fiber S t (a + k) : ℝ)) (b + 1 - a) hn
    (fun _ _ => Nat.cast_nonneg _)
  have hb : a + (b + 1 - a - 1) = b := by omega
  have hrange : b + 1 - a - 1 = b - a := by omega
  rw [hb, hrange] at h
  refine le_trans h ?_
  rw [sum_Ico_eq_sum_range (fun v => |(fiber S t (v + 1) : ℝ) - fiber S t v|) a b]
  refine add_le_add (le_of_eq ?_) le_rfl
  refine sum_congr rfl fun k _ => ?_
  rw [add_assoc]

/-! ### One step of the map sums fibers over preimages -/

/-- A preimage of `v` under the map lies below `(v+1)²`. -/
theorem lt_sq_succ_of_floorPower_eq {u v : ℕ} (h : floorPower u = v) :
    u < (v + 1) * (v + 1) := by
  rcases Nat.even_or_odd u with he | ho
  · rw [floorPower_even_eq (Nat.even_iff.mp he)] at h
    exact (Nat.eq_sqrt.mp h.symm).2
  · rw [floorPower_odd_eq (Nat.odd_iff.mp ho)] at h
    have h3 := (Nat.eq_sqrt.mp h.symm).2
    exact lt_of_le_of_lt (Nat.le_self_pow (by norm_num) u) h3

/-- The preimages of `v` under the map. -/
noncomputable def pre (v : ℕ) : Finset ℕ :=
  (range ((v + 1) * (v + 1))).filter fun u => floorPower u = v

theorem iterate_succ_eq (t n : ℕ) : floorPower^[t + 1] n = floorPower (floorPower^[t] n) :=
  Function.iterate_succ_apply' _ _ _

/-- The fiber at depth `t+1` is the sum of the depth-`t` fibers over the preimages. -/
theorem fiber_succ (S : Finset ℕ) (t v : ℕ) :
    fiber S (t + 1) v = ∑ u ∈ pre v, fiber S t u := by
  unfold fiber
  rw [card_eq_sum_card_fiberwise (f := fun n => floorPower^[t] n) (t := pre v)]
  · refine sum_congr rfl fun u hu => ?_
    rw [pre, mem_filter] at hu
    congr 1
    ext n
    simp only [mem_filter, iterate_succ_eq]
    constructor
    · rintro ⟨⟨hS', -⟩, hu'⟩
      exact ⟨hS', hu'⟩
    · rintro ⟨hS', hu'⟩
      exact ⟨⟨hS', by rw [hu']; exact hu.2⟩, hu'⟩
  · intro n hn
    rw [Finset.mem_coe, mem_filter, iterate_succ_eq] at hn
    rw [Finset.mem_coe, pre, mem_filter, mem_range]
    exact ⟨lt_sq_succ_of_floorPower_eq hn.2, hn.2⟩

/-- The even preimages of `v` are the even numbers of `[v², (v+1)²)` (Lemma 3.1's even
block, in fiber form). -/
theorem pre_filter_even (v : ℕ) :
    (pre v).filter (fun u => u % 2 = 0)
      = (Ico (v * v) ((v + 1) * (v + 1))).filter (fun u => u % 2 = 0) := by
  ext u
  simp only [pre, mem_filter, mem_range, mem_Ico]
  constructor
  · rintro ⟨⟨hlt, hfp⟩, he⟩
    rw [floorPower_even_eq he] at hfp
    exact ⟨⟨(Nat.eq_sqrt.mp hfp.symm).1, hlt⟩, he⟩
  · rintro ⟨⟨hge, hlt⟩, he⟩
    refine ⟨⟨hlt, ?_⟩, he⟩
    rw [floorPower_even_eq he]
    exact (Nat.eq_sqrt.mpr ⟨hge, hlt⟩).symm

/-- The even branch: the depth-`t` mass of the even numbers of `[v², (v+1)²)`. -/
noncomputable def blockSum (S : Finset ℕ) (t v : ℕ) : ℝ :=
  ∑ u ∈ (Ico (v * v) ((v + 1) * (v + 1))).filter (fun u => u % 2 = 0), (fiber S t u : ℝ)

/-- The odd branch: the depth-`t` mass of the odd preimages of `v`. -/
noncomputable def oddPart (S : Finset ℕ) (t v : ℕ) : ℝ :=
  ∑ u ∈ (pre v).filter (fun u => u % 2 = 1), (fiber S t u : ℝ)

theorem oddPart_nonneg (S : Finset ℕ) (t v : ℕ) : 0 ≤ oddPart S t v :=
  sum_nonneg fun _ _ => Nat.cast_nonneg _

/-- `fiber(t+1, v) = blockSum + oddPart`. -/
theorem fiber_succ_eq (S : Finset ℕ) (t v : ℕ) :
    (fiber S (t + 1) v : ℝ) = blockSum S t v + oddPart S t v := by
  rw [fiber_succ S t v]
  push_cast
  rw [← sum_filter_add_sum_filter_not (pre v) (fun u => u % 2 = 0) (fun u => (fiber S t u : ℝ))]
  unfold blockSum oddPart
  rw [pre_filter_even]
  congr 1
  apply sum_congr _ (fun _ _ => rfl)
  apply filter_congr
  intro u _
  exact Nat.mod_two_ne_zero

/-! ### The even branch smooths -/

/-- The number of even numbers of `[v², (v+1)²)`. -/
noncomputable def evenCount (v : ℕ) : ℕ :=
  ((Ico (v * v) ((v + 1) * (v + 1))).filter (fun u => u % 2 = 0)).card

theorem evenCount_le (v : ℕ) : evenCount v ≤ v + 1 := by
  unfold evenCount
  have hsq : (v + 1) * (v + 1) = v * v + 2 * v + 1 := by ring
  calc ((Ico (v * v) ((v + 1) * (v + 1))).filter (fun u => u % 2 = 0)).card
      ≤ (Icc (v * v / 2) ((v * v + 2 * v) / 2)).card := by
        apply card_le_card_of_injOn (fun u => u / 2)
        · intro u hu
          rw [Finset.mem_coe, mem_filter, mem_Ico, hsq] at hu
          rw [Finset.mem_coe, mem_Icc]
          dsimp only
          omega
        · intro u hu u' hu' heq
          rw [Finset.mem_coe, mem_filter] at hu hu'
          simp only at heq
          omega
    _ = (v * v + 2 * v) / 2 + 1 - v * v / 2 := Nat.card_Icc _ _
    _ ≤ v + 1 := by omega

theorem le_evenCount (v : ℕ) : v ≤ evenCount v := by
  unfold evenCount
  have hsq : (v + 1) * (v + 1) = v * v + 2 * v + 1 := by ring
  calc v ≤ (Icc ((v * v + 1) / 2) ((v * v + 2 * v) / 2)).card := by
        rw [Nat.card_Icc]
        omega
    _ ≤ ((Ico (v * v) ((v + 1) * (v + 1))).filter (fun u => u % 2 = 0)).card := by
        apply card_le_card_of_injOn (fun k => 2 * k)
        · intro k hk
          rw [Finset.mem_coe, mem_Icc] at hk
          rw [Finset.mem_coe, mem_filter, mem_Ico, hsq]
          dsimp only
          omega
        · intro k _ k' _ heq
          simp only at heq
          omega

/-- **The even branch smooths.** If the depth-`t` profile lies between `m` and `M` on the
double block `[v², (v+2)²)`, consecutive block sums differ by at most `(v+1)(M-m) + 2M`. -/
theorem blockSum_sub_le (S : Finset ℕ) (t v : ℕ) {m M : ℕ}
    (hlo : ∀ u ∈ Ico (v * v) ((v + 1 + 1) * (v + 1 + 1)), m ≤ fiber S t u)
    (hhi : ∀ u ∈ Ico (v * v) ((v + 1 + 1) * (v + 1 + 1)), fiber S t u ≤ M) :
    |blockSum S t (v + 1) - blockSum S t v| ≤ (v + 1) * ((M : ℝ) - m) + 2 * M := by
  have hvv : v * v ∈ Ico (v * v) ((v + 1 + 1) * (v + 1 + 1)) := by
    rw [mem_Ico]
    constructor <;> nlinarith
  have hmM : (m : ℝ) ≤ M := by exact_mod_cast le_trans (hlo _ hvv) (hhi _ hvv)
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg _
  have hsub1 : (Ico (v * v) ((v + 1) * (v + 1))).filter (fun u => u % 2 = 0)
      ⊆ Ico (v * v) ((v + 1 + 1) * (v + 1 + 1)) := by
    intro u hu
    rw [mem_filter, mem_Ico] at hu
    rw [mem_Ico]
    constructor <;> nlinarith [hu.1.1, hu.1.2]
  have hsub2 : (Ico ((v + 1) * (v + 1)) ((v + 1 + 1) * (v + 1 + 1))).filter (fun u => u % 2 = 0)
      ⊆ Ico (v * v) ((v + 1 + 1) * (v + 1 + 1)) := by
    intro u hu
    rw [mem_filter, mem_Ico] at hu
    rw [mem_Ico]
    constructor <;> nlinarith [hu.1.1, hu.1.2]
  have hlo1 : (evenCount v : ℝ) * m ≤ blockSum S t v := by
    unfold blockSum evenCount
    have := card_nsmul_le_sum ((Ico (v * v) ((v + 1) * (v + 1))).filter (fun u => u % 2 = 0))
      (fun u => (fiber S t u : ℝ)) (m : ℝ) (fun u hu => by exact_mod_cast hlo u (hsub1 hu))
    simpa [nsmul_eq_mul] using this
  have hhi1 : blockSum S t v ≤ (evenCount v : ℝ) * M := by
    unfold blockSum evenCount
    have := sum_le_card_nsmul ((Ico (v * v) ((v + 1) * (v + 1))).filter (fun u => u % 2 = 0))
      (fun u => (fiber S t u : ℝ)) (M : ℝ) (fun u hu => by exact_mod_cast hhi u (hsub1 hu))
    simpa [nsmul_eq_mul] using this
  have hlo2 : (evenCount (v + 1) : ℝ) * m ≤ blockSum S t (v + 1) := by
    unfold blockSum evenCount
    have := card_nsmul_le_sum
      ((Ico ((v + 1) * (v + 1)) ((v + 1 + 1) * (v + 1 + 1))).filter (fun u => u % 2 = 0))
      (fun u => (fiber S t u : ℝ)) (m : ℝ) (fun u hu => by exact_mod_cast hlo u (hsub2 hu))
    simpa [nsmul_eq_mul] using this
  have hhi2 : blockSum S t (v + 1) ≤ (evenCount (v + 1) : ℝ) * M := by
    unfold blockSum evenCount
    have := sum_le_card_nsmul
      ((Ico ((v + 1) * (v + 1)) ((v + 1 + 1) * (v + 1 + 1))).filter (fun u => u % 2 = 0))
      (fun u => (fiber S t u : ℝ)) (M : ℝ) (fun u hu => by exact_mod_cast hhi u (hsub2 hu))
    simpa [nsmul_eq_mul] using this
  have hc1 : (evenCount v : ℝ) ≤ v + 1 := by exact_mod_cast evenCount_le v
  have hc1' : (v : ℝ) ≤ evenCount v := by exact_mod_cast le_evenCount v
  have hc2 : (evenCount (v + 1) : ℝ) ≤ v + 1 + 1 := by exact_mod_cast evenCount_le (v + 1)
  have hc2' : (v : ℝ) + 1 ≤ evenCount (v + 1) := by exact_mod_cast le_evenCount (v + 1)
  rw [abs_sub_le_iff]
  constructor
  · nlinarith [mul_le_mul_of_nonneg_right hc2 hM0, mul_le_mul_of_nonneg_right hc1' hm0]
  · nlinarith [mul_le_mul_of_nonneg_right hc1 hM0, mul_le_mul_of_nonneg_right hc2' hm0]

/-- The variation of the odd branch over a window is at most twice its mass. -/
theorem sum_abs_oddPart_sub_le (S : Finset ℕ) (t a b : ℕ) :
    ∑ v ∈ Ico a b, |oddPart S t (v + 1) - oddPart S t v|
      ≤ 2 * ∑ v ∈ Icc a b, oddPart S t v := by
  have h1 : ∀ v ∈ Ico a b, |oddPart S t (v + 1) - oddPart S t v|
      ≤ oddPart S t (v + 1) + oddPart S t v := by
    intro v _
    rw [abs_sub_le_iff]
    constructor <;> linarith [oddPart_nonneg S t v, oddPart_nonneg S t (v + 1)]
  refine le_trans (sum_le_sum h1) ?_
  rw [sum_add_distrib, two_mul]
  apply add_le_add
  · rw [← sum_image (g := fun v => v + 1) (fun x _ y _ h => Nat.add_right_cancel h)]
    apply sum_le_sum_of_subset_of_nonneg
    · intro w hw
      rw [mem_image] at hw
      obtain ⟨v, hv, rfl⟩ := hw
      rw [mem_Ico] at hv
      rw [mem_Icc]
      omega
    · intro _ _ _
      exact oddPart_nonneg _ _ _
  · apply sum_le_sum_of_subset_of_nonneg
    · intro v hv
      rw [mem_Ico] at hv
      rw [mem_Icc]
      omega
    · intro _ _ _
      exact oddPart_nonneg _ _ _

/-- **The collapsed component is nearly fair.** If the depth-`t` fiber
profile lies between `m v` and `M v` on the double block `[v², (v+2)²)` for every `v` in
`[a, b)`, the next-letter bias of the starts whose `(t+1)`-st iterate lies in `[a, b]` is at
most `Σ_{v ∈ [a,b)} ((v+1)(M v - m v) + 2 M v)`, plus twice the mass arriving through odd
preimages, plus one fiber. -/
theorem collapse_bias_le (S : Finset ℕ) (t a b : ℕ) (hab : a ≤ b)
    (m M : ℕ → ℕ)
    (hlo : ∀ v ∈ Ico a b, ∀ u ∈ Ico (v * v) ((v + 1 + 1) * (v + 1 + 1)),
      m v ≤ fiber S t u)
    (hhi : ∀ v ∈ Ico a b, ∀ u ∈ Ico (v * v) ((v + 1 + 1) * (v + 1 + 1)),
      fiber S t u ≤ M v) :
    |windowBias S (t + 1) a b|
      ≤ ∑ v ∈ Ico a b, ((v + 1) * ((M v : ℝ) - m v) + 2 * M v)
        + 2 * ∑ v ∈ Icc a b, oddPart S t v + fiber S (t + 1) b := by
  refine le_trans (abs_windowBias_le S (t + 1) a b hab) ?_
  have hpt : ∀ v ∈ Ico a b, |(fiber S (t + 1) (v + 1) : ℝ) - fiber S (t + 1) v|
      ≤ ((v + 1) * ((M v : ℝ) - m v) + 2 * M v)
        + |oddPart S t (v + 1) - oddPart S t v| := by
    intro v hv
    rw [fiber_succ_eq S t (v + 1), fiber_succ_eq S t v]
    calc |blockSum S t (v + 1) + oddPart S t (v + 1) - (blockSum S t v + oddPart S t v)|
        = |(blockSum S t (v + 1) - blockSum S t v)
            + (oddPart S t (v + 1) - oddPart S t v)| := by
          congr 1
          ring
      _ ≤ |blockSum S t (v + 1) - blockSum S t v|
            + |oddPart S t (v + 1) - oddPart S t v| := abs_add_le _ _
      _ ≤ _ := add_le_add (blockSum_sub_le S t v (hlo v hv) (hhi v hv)) le_rfl
  calc ∑ v ∈ Ico a b, |(fiber S (t + 1) (v + 1) : ℝ) - fiber S (t + 1) v| + fiber S (t + 1) b
      ≤ ∑ v ∈ Ico a b, (((v + 1) * ((M v : ℝ) - m v) + 2 * M v)
          + |oddPart S t (v + 1) - oddPart S t v|) + fiber S (t + 1) b :=
        add_le_add (sum_le_sum hpt) le_rfl
    _ = ∑ v ∈ Ico a b, ((v + 1) * ((M v : ℝ) - m v) + 2 * M v)
          + ∑ v ∈ Ico a b, |oddPart S t (v + 1) - oddPart S t v| + fiber S (t + 1) b := by
        rw [sum_add_distrib]
    _ ≤ _ := by
        have := sum_abs_oddPart_sub_le S t a b
        linarith

/-! ### Even steps are self-smoothing -/

/-- **A sandwich propagates through an even step.** If the depth-`t` profile lies between `m`
and `M` on the block `[v², (v+1)²)` and the odd branch at `v` carries at most `P`, then
`v m ≤ fiber(t+1, v) ≤ (v+1) M + P`. -/
theorem fiber_succ_sandwich (S : Finset ℕ) (t v : ℕ) {m M P : ℕ}
    (hlo : ∀ u ∈ Ico (v * v) ((v + 1) * (v + 1)), m ≤ fiber S t u)
    (hhi : ∀ u ∈ Ico (v * v) ((v + 1) * (v + 1)), fiber S t u ≤ M)
    (hP : oddPart S t v ≤ P) :
    v * m ≤ fiber S (t + 1) v ∧ fiber S (t + 1) v ≤ (v + 1) * M + P := by
  have hsplit : fiber S (t + 1) v
      = ∑ u ∈ (Ico (v * v) ((v + 1) * (v + 1))).filter (fun u => u % 2 = 0), fiber S t u
        + ∑ u ∈ (pre v).filter (fun u => u % 2 = 1), fiber S t u := by
    rw [fiber_succ S t v,
      ← sum_filter_add_sum_filter_not (pre v) (fun u => u % 2 = 0) (fun u => fiber S t u),
      pre_filter_even]
    congr 1
    apply sum_congr _ (fun _ _ => rfl)
    apply filter_congr
    intro u _
    exact Nat.mod_two_ne_zero
  have hodd : ∑ u ∈ (pre v).filter (fun u => u % 2 = 1), fiber S t u ≤ P := by
    have h : ((∑ u ∈ (pre v).filter (fun u => u % 2 = 1), fiber S t u : ℕ) : ℝ) ≤ P := by
      push_cast
      exact hP
    exact_mod_cast h
  have hblo : evenCount v * m
      ≤ ∑ u ∈ (Ico (v * v) ((v + 1) * (v + 1))).filter (fun u => u % 2 = 0), fiber S t u := by
    have := card_nsmul_le_sum ((Ico (v * v) ((v + 1) * (v + 1))).filter (fun u => u % 2 = 0))
      (fun u => fiber S t u) m (fun u hu => hlo u (mem_filter.mp hu).1)
    simpa [evenCount, smul_eq_mul] using this
  have hbhi : ∑ u ∈ (Ico (v * v) ((v + 1) * (v + 1))).filter (fun u => u % 2 = 0), fiber S t u
      ≤ evenCount v * M := by
    have := sum_le_card_nsmul ((Ico (v * v) ((v + 1) * (v + 1))).filter (fun u => u % 2 = 0))
      (fun u => fiber S t u) M (fun u hu => hhi u (mem_filter.mp hu).1)
    simpa [evenCount, smul_eq_mul] using this
  have hc := evenCount_le v
  have hc' := le_evenCount v
  constructor
  · calc v * m ≤ evenCount v * m := Nat.mul_le_mul_right m hc'
      _ ≤ _ := hblo
      _ ≤ fiber S (t + 1) v := by rw [hsplit]; exact Nat.le_add_right _ _
  · calc fiber S (t + 1) v
        ≤ evenCount v * M + P := by rw [hsplit]; exact Nat.add_le_add hbhi hodd
      _ ≤ (v + 1) * M + P := Nat.add_le_add_right (Nat.mul_le_mul_right M hc) P

/-- **Two even steps.** If the depth-`t` profile lies between `m w` and `M w` on the block
`[w⁴, (w+2)⁴)` and the odd branch at depth `t` is at most `P w` on `[w², (w+2)²)`, for every
`w` in `[a, b)`, the next-letter bias of the starts whose `(t+2)`-nd iterate lies in `[a, b]`
is bounded by the propagated sandwich `w² m w ≤ fiber(t+1, ·) ≤ (w+2)² M w + P w`: the
relative oscillation of the profile is not amplified by an even step, and the loss is a
relative `O(1/w)`. -/
theorem collapse_bias_two_step (S : Finset ℕ) (t a b : ℕ) (hab : a ≤ b) (m M P : ℕ → ℕ)
    (hlo : ∀ w ∈ Ico a b, ∀ u ∈ Ico (w * w * (w * w)) ((w + 1 + 1) * (w + 1 + 1)
      * ((w + 1 + 1) * (w + 1 + 1))), m w ≤ fiber S t u)
    (hhi : ∀ w ∈ Ico a b, ∀ u ∈ Ico (w * w * (w * w)) ((w + 1 + 1) * (w + 1 + 1)
      * ((w + 1 + 1) * (w + 1 + 1))), fiber S t u ≤ M w)
    (hP : ∀ w ∈ Ico a b, ∀ v ∈ Ico (w * w) ((w + 1 + 1) * (w + 1 + 1)),
      oddPart S t v ≤ P w) :
    |windowBias S (t + 1 + 1) a b|
      ≤ ∑ w ∈ Ico a b, ((w + 1) * ((((w + 1 + 1) * (w + 1 + 1) * M w + P w : ℕ) : ℝ)
            - ((w * w * m w : ℕ) : ℝ))
          + 2 * (((w + 1 + 1) * (w + 1 + 1) * M w + P w : ℕ) : ℝ))
        + 2 * ∑ w ∈ Icc a b, oddPart S (t + 1) w + fiber S (t + 1 + 1) b := by
  refine collapse_bias_le S (t + 1) a b hab (fun w => w * w * m w)
    (fun w => (w + 1 + 1) * (w + 1 + 1) * M w + P w) ?_ ?_
  · intro w hw v hv
    rw [mem_Ico] at hv
    have hsub : ∀ u ∈ Ico (v * v) ((v + 1) * (v + 1)),
        u ∈ Ico (w * w * (w * w)) ((w + 1 + 1) * (w + 1 + 1) * ((w + 1 + 1) * (w + 1 + 1))) := by
      intro u hu
      rw [mem_Ico] at hu ⊢
      constructor <;> nlinarith [hu.1, hu.2, hv.1, hv.2]
    have h := (fiber_succ_sandwich S t v (fun u hu => hlo w hw u (hsub u hu))
      (fun u hu => hhi w hw u (hsub u hu)) (hP w hw v (mem_Ico.mpr hv))).1
    calc w * w * m w ≤ v * m w := Nat.mul_le_mul_right _ hv.1
      _ ≤ fiber S (t + 1) v := h
  · intro w hw v hv
    rw [mem_Ico] at hv
    have hsub : ∀ u ∈ Ico (v * v) ((v + 1) * (v + 1)),
        u ∈ Ico (w * w * (w * w)) ((w + 1 + 1) * (w + 1 + 1) * ((w + 1 + 1) * (w + 1 + 1))) := by
      intro u hu
      rw [mem_Ico] at hu ⊢
      constructor <;> nlinarith [hu.1, hu.2, hv.1, hv.2]
    have h := (fiber_succ_sandwich S t v (fun u hu => hlo w hw u (hsub u hu))
      (fun u hu => hhi w hw u (hsub u hu)) (hP w hw v (mem_Ico.mpr hv))).2
    calc fiber S (t + 1) v ≤ (v + 1) * M w + P w := h
      _ ≤ (w + 1 + 1) * (w + 1 + 1) * M w + P w :=
          Nat.add_le_add_right (Nat.mul_le_mul_right _ (by omega)) _

end Collapse

end Problems.Juggler
