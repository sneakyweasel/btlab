import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Complex.ExponentialBounds
import Problems.Juggler.FateChernoff

namespace Problems.Juggler

open Finset
open scoped Classical

/-!
# The Tao-type reduction: a rate on the odd failures implies the conjecture

Paper C (`docs/theory/juggler_fate_almost_all_note.md`), Theorem 7.2, and Theorem A of the
Tao-reduction note (`docs/theory/juggler_tao_reduction_note.md`), with the contagion bound
of Theorem 5.3 as a hypothesis.

The proof has three exact parts and one asymptotic step.

* **The `E`-tree bound.** Every member `n ≥ 1` of a forward-closed class `A` descends to an
  odd member `n₀` through even steps only (Theorem 6.1, `exists_odd_ancestor`), so `n` sits at
  some level `j` of the `E`-tree of `n₀`. Level `j` lies above `n₀^{2^j}`
  (`evenDescent_pow_le`), so at most `1 + log₂ log₂ x` levels meet `[1, x]`, and each level
  has log-mass at most `1/(n₀ - 1) ≤ (3/2)/n₀`: the level-`(j+1)` set is covered by the even
  blocks of the level-`j` set, an even block of `m` has log-mass at most `(m+1)/m²` (Lemma 3.1),
  and the factors `1 + n₀^{-2^j}` telescope, `(1 - u) ∏ (1 + u^{2^j}) = 1 - u^{2^{J}}`.
  Hence `logMass A x ≤ (3/2) (1 + log₂ log₂ x) · oddLogMass A x`
  (`logMass_le_oddLogMass`). The paper's constant is `2`.
* **The dyadic sum.** If `#{n odd in (y, 2y] : n ∈ A} ≤ y (log y)^{-e}` for `y ≥ y₀ ≥ 2`,
  then the odd log-mass up to `x` is at most a constant plus
  `(log 2)^{-e} (log₂ x + 1)^{1-e}/(1 - e)` (`oddLogMass_le_of_dyadic`), by the telescoping
  Bernoulli bound `Σ_{k ≤ K} k^{-e} ≤ K^{1-e}/(1-e)` (`sum_rpow_neg_le`).
* **The contradiction.** With `λ > 1 - e` the lower bound `K (log x)^λ` of the contagion
  theorem beats `(log x)^{1-e+δ}` for `x` large; the class is empty.

The contagion bound (Theorem 5.3) is the analytic core of Paper C and stays a human proof; it
enters here as the hypothesis `hlow`, stated only for a nonempty class. So
`tao_rate_implies_empty` is exactly the paper's proof of Theorem 7.2 given Theorem 5.3, and
`tao_rate_implies_conjecture` is its instance on the failure set `¬ReachesOne`. Backward
closure of the class is not used: the `E`-tree covering needs only forward closure. Not a
halt theorem: nothing here proves the rate hypothesis.
-/

/-! ### Log-masses and the odd members of a dyadic block -/

/-- The log-mass `Σ_{1 ≤ n ≤ x, n ∈ A} 1/n`. -/
noncomputable def logMass (A : ℕ → Prop) (x : ℕ) : ℝ :=
  ∑ n ∈ {n ∈ Icc 1 x | A n}, (1 : ℝ) / n

/-- The odd log-mass `Σ_{1 ≤ n ≤ x odd, n ∈ A} 1/n`. -/
noncomputable def oddLogMass (A : ℕ → Prop) (x : ℕ) : ℝ :=
  ∑ n ∈ {n ∈ Icc 1 x | n % 2 = 1 ∧ A n}, (1 : ℝ) / n

/-- The odd members of `A` in `(y, 2y]`. -/
noncomputable def oddMembers (A : ℕ → Prop) (y : ℕ) : Finset ℕ :=
  {n ∈ Ioc y (2 * y) | n % 2 = 1 ∧ A n}

theorem oddMembers_not_reachesOne (y : ℕ) :
    oddMembers (fun n => ¬ReachesOne n) y = oddFailures y := by
  ext n
  simp [oddMembers, oddFailures]

/-! ### The `E`-tree of an odd member -/

/-- `n` descends to `n₀` in exactly `j` steps, all of them even: `n` lies at level `j` of
the `E`-tree of `n₀`. -/
def EvenDescent (n j n₀ : ℕ) : Prop :=
  floorPower^[j] n = n₀ ∧ ∀ i < j, floorPower^[i] n % 2 = 0

theorem evenDescent_zero {n n₀ : ℕ} : EvenDescent n 0 n₀ ↔ n = n₀ := by
  constructor
  · rintro ⟨h, -⟩
    simpa using h
  · rintro rfl
    exact ⟨rfl, fun i hi => absurd hi (Nat.not_lt_zero i)⟩

theorem evenDescent_succ {n j n₀ : ℕ} (h : EvenDescent n (j + 1) n₀) :
    n % 2 = 0 ∧ EvenDescent (floorPower n) j n₀ := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨by simpa using h2 0 (Nat.succ_pos j), ?_, ?_⟩
  · rw [Function.iterate_succ_apply] at h1
    exact h1
  · intro i hi
    have := h2 (i + 1) (by omega)
    rw [Function.iterate_succ_apply] at this
    exact this

/-- Level `j` of the `E`-tree of `n₀` sits above `n₀^{2^j}`. -/
theorem evenDescent_pow_le {n j n₀ : ℕ} (h : EvenDescent n j n₀) : n₀ ^ (2 ^ j) ≤ n := by
  induction j generalizing n with
  | zero =>
      rw [evenDescent_zero] at h
      subst h
      simp
  | succ j ih =>
      obtain ⟨he, h'⟩ := evenDescent_succ h
      have hm := ih h'
      rw [floorPower_even_eq he] at hm
      calc n₀ ^ (2 ^ (j + 1)) = (n₀ ^ (2 ^ j)) ^ 2 := by rw [pow_succ, pow_mul]
        _ ≤ n.sqrt ^ 2 := Nat.pow_le_pow_left hm 2
        _ ≤ n := by rw [pow_two]; exact Nat.sqrt_le n

/-- Level `j` of the `E`-tree of `n₀`, cut at `x`. -/
noncomputable def treeLevel (n₀ j x : ℕ) : Finset ℕ :=
  {n ∈ Icc 1 x | EvenDescent n j n₀}

/-- The even block of `m`: the even `n` with `m² ≤ n < (m+1)²`. -/
noncomputable def evenBlock (m : ℕ) : Finset ℕ :=
  {n ∈ Ico (m * m) ((m + 1) * (m + 1)) | n % 2 = 0}

/-- Level `j + 1` is covered by the even blocks of level `j`. -/
theorem treeLevel_succ_subset (n₀ j x : ℕ) :
    treeLevel n₀ (j + 1) x ⊆ (treeLevel n₀ j x).biUnion evenBlock := by
  intro n hn
  simp only [treeLevel, mem_filter, mem_Icc] at hn
  obtain ⟨⟨h1, hx⟩, hd⟩ := hn
  obtain ⟨he, hd'⟩ := evenDescent_succ hd
  rw [mem_biUnion]
  refine ⟨floorPower n, ?_, ?_⟩
  · simp only [treeLevel, mem_filter, mem_Icc]
    refine ⟨⟨floorPower_pos h1, ?_⟩, hd'⟩
    rw [floorPower_even_eq he]
    exact le_trans (Nat.sqrt_le_self n) hx
  · simp only [evenBlock, mem_filter, mem_Ico]
    rw [floorPower_even_eq he]
    exact ⟨⟨Nat.sqrt_le n, Nat.lt_succ_sqrt n⟩, he⟩

/-- Lemma 3.1, the upper count: an even block has at most `m + 1` elements. -/
theorem evenBlock_card_le (m : ℕ) : (evenBlock m).card ≤ m + 1 := by
  have hexp : (m + 1) * (m + 1) = m * m + 2 * m + 1 := by ring
  have hmaps : ∀ n ∈ evenBlock m, (fun n => (n - m * m) / 2) n ∈ range (m + 1) := by
    intro n hn
    simp only [evenBlock, mem_filter, mem_Ico] at hn
    rw [mem_range]
    show (n - m * m) / 2 < m + 1
    omega
  have hinj : Set.InjOn (fun n => (n - m * m) / 2) ↑(evenBlock m) := by
    intro a ha b hb hab
    simp only [coe_filter, evenBlock, Set.mem_ofPred_eq, mem_Ico] at ha hb
    simp only at hab
    omega
  simpa using Finset.card_le_card_of_injOn _ hmaps hinj

/-- Lemma 3.1, the upper log-mass: `Σ_{n ∈ E(m)} 1/n ≤ (m+1)/m²`. -/
theorem evenBlock_logMass_le {m : ℕ} (hm : 1 ≤ m) :
    ∑ n ∈ evenBlock m, (1 : ℝ) / n ≤ (m + 1) / (m * m) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hterm : ∀ n ∈ evenBlock m, (1 : ℝ) / n ≤ 1 / (m * m) := by
    intro n hn
    simp only [evenBlock, mem_filter, mem_Ico] at hn
    have : (m : ℝ) * m ≤ n := by exact_mod_cast hn.1.1
    exact one_div_le_one_div_of_le (by positivity) this
  calc ∑ n ∈ evenBlock m, (1 : ℝ) / n
      ≤ (evenBlock m).card • (1 / ((m : ℝ) * m)) := sum_le_card_nsmul _ _ _ hterm
    _ = (evenBlock m).card * (1 / ((m : ℝ) * m)) := by rw [nsmul_eq_mul]
    _ ≤ (m + 1) * (1 / ((m : ℝ) * m)) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact_mod_cast evenBlock_card_le m
    _ = (m + 1) / (m * m) := by ring

/-- A sum over a union of finsets is at most the sum of the sums, for nonnegative terms. -/
theorem sum_biUnion_le_sum {ι α : Type*} [DecidableEq α] (s : Finset ι) (t : ι → Finset α)
    (f : α → ℝ) (hf : ∀ a, 0 ≤ f a) :
    ∑ a ∈ s.biUnion t, f a ≤ ∑ i ∈ s, ∑ a ∈ t i, f a := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
      rw [biUnion_insert, sum_insert hi]
      have h := sum_union_inter (s₁ := t i) (s₂ := s.biUnion t) (f := f)
      have h0 : 0 ≤ ∑ a ∈ t i ∩ s.biUnion t, f a := sum_nonneg fun a _ => hf a
      linarith

/-- One level up multiplies the log-mass by at most `1 + n₀^{-2^j}`. -/
theorem treeLevel_logMass_succ_le {n₀ : ℕ} (hn₀ : 1 ≤ n₀) (j x : ℕ) :
    ∑ n ∈ treeLevel n₀ (j + 1) x, (1 : ℝ) / n ≤
      (1 + (1 / (n₀ : ℝ)) ^ (2 ^ j)) * ∑ m ∈ treeLevel n₀ j x, (1 : ℝ) / m := by
  have hnn : ∀ n : ℕ, (0 : ℝ) ≤ 1 / n := fun n => by positivity
  have hn₀R : (0 : ℝ) < n₀ := by exact_mod_cast hn₀
  calc ∑ n ∈ treeLevel n₀ (j + 1) x, (1 : ℝ) / n
      ≤ ∑ n ∈ (treeLevel n₀ j x).biUnion evenBlock, (1 : ℝ) / n :=
        sum_le_sum_of_subset_of_nonneg (treeLevel_succ_subset n₀ j x) (fun n _ _ => hnn n)
    _ ≤ ∑ m ∈ treeLevel n₀ j x, ∑ n ∈ evenBlock m, (1 : ℝ) / n := sum_biUnion_le_sum _ _ _ hnn
    _ ≤ ∑ m ∈ treeLevel n₀ j x, (1 + (1 / (n₀ : ℝ)) ^ (2 ^ j)) * (1 / m) := by
        apply sum_le_sum
        intro m hm
        simp only [treeLevel, mem_filter, mem_Icc] at hm
        have hm1 : 1 ≤ m := hm.1.1
        have hpow : n₀ ^ (2 ^ j) ≤ m := evenDescent_pow_le hm.2
        have hmR : (0 : ℝ) < m := by exact_mod_cast hm1
        have hinv : (1 : ℝ) / m ≤ (1 / (n₀ : ℝ)) ^ (2 ^ j) := by
          rw [one_div_pow]
          apply one_div_le_one_div_of_le (pow_pos hn₀R _)
          exact_mod_cast hpow
        calc ∑ n ∈ evenBlock m, (1 : ℝ) / n ≤ (m + 1) / (m * m) := evenBlock_logMass_le hm1
          _ = (1 + 1 / m) * (1 / m) := by field_simp
          _ ≤ (1 + (1 / (n₀ : ℝ)) ^ (2 ^ j)) * (1 / m) := by
              apply mul_le_mul_of_nonneg_right _ (hnn m)
              linarith
    _ = (1 + (1 / (n₀ : ℝ)) ^ (2 ^ j)) * ∑ m ∈ treeLevel n₀ j x, (1 : ℝ) / m := by rw [mul_sum]

theorem treeLevel_zero_le {n₀ : ℕ} (x : ℕ) :
    ∑ n ∈ treeLevel n₀ 0 x, (1 : ℝ) / n ≤ 1 / n₀ := by
  have hsub : treeLevel n₀ 0 x ⊆ {n₀} := by
    intro n hn
    simp only [treeLevel, mem_filter] at hn
    rw [mem_singleton]
    exact evenDescent_zero.mp hn.2
  calc ∑ n ∈ treeLevel n₀ 0 x, (1 : ℝ) / n ≤ ∑ n ∈ {n₀}, (1 : ℝ) / n :=
        sum_le_sum_of_subset_of_nonneg hsub (fun n _ _ => by positivity)
    _ = 1 / n₀ := sum_singleton _ _

/-- The telescoped level bound: `Σ_{level j} 1/n ≤ (1/n₀)(1 - u^{2^j})/(1 - u)`, `u = 1/n₀`. -/
theorem treeLevel_logMass_le {n₀ : ℕ} (hn₀ : 2 ≤ n₀) (j x : ℕ) :
    ∑ n ∈ treeLevel n₀ j x, (1 : ℝ) / n ≤
      (1 / n₀) * (1 - (1 / (n₀ : ℝ)) ^ (2 ^ j)) / (1 - 1 / n₀) := by
  have hn₀R : (2 : ℝ) ≤ n₀ := by exact_mod_cast hn₀
  have hu : (1 : ℝ) / n₀ ≤ 1 / 2 := by
    rw [div_le_div_iff₀ (by linarith) (by norm_num)]
    linarith
  have hu0 : (0 : ℝ) ≤ 1 / n₀ := by positivity
  have h1u : (0 : ℝ) < 1 - 1 / n₀ := by linarith
  induction j with
  | zero =>
      calc _ ≤ (1 : ℝ) / n₀ := treeLevel_zero_le x
        _ = _ := by
          rw [pow_zero, pow_one, mul_div_assoc, div_self h1u.ne', mul_one]
  | succ j ih =>
      calc ∑ n ∈ treeLevel n₀ (j + 1) x, (1 : ℝ) / n
          ≤ (1 + (1 / (n₀ : ℝ)) ^ (2 ^ j)) * ∑ m ∈ treeLevel n₀ j x, (1 : ℝ) / m :=
            treeLevel_logMass_succ_le (by omega) j x
        _ ≤ (1 + (1 / (n₀ : ℝ)) ^ (2 ^ j)) *
              ((1 / n₀) * (1 - (1 / (n₀ : ℝ)) ^ (2 ^ j)) / (1 - 1 / n₀)) :=
            mul_le_mul_of_nonneg_left ih (by positivity)
        _ = (1 / n₀) * (1 - (1 / (n₀ : ℝ)) ^ (2 ^ (j + 1))) / (1 - 1 / n₀) := by
            rw [pow_succ, pow_mul]
            field_simp
            ring

/-- Every level of the `E`-tree of `n₀ ≥ 3` has log-mass at most `(3/2)/n₀`. -/
theorem treeLevel_logMass_le' {n₀ : ℕ} (hn₀ : 3 ≤ n₀) (j x : ℕ) :
    ∑ n ∈ treeLevel n₀ j x, (1 : ℝ) / n ≤ 3 / 2 * (1 / n₀) := by
  have h := treeLevel_logMass_le (n₀ := n₀) (by omega) j x
  have hn₀R : (3 : ℝ) ≤ n₀ := by exact_mod_cast hn₀
  have hpow : (0 : ℝ) ≤ (1 / (n₀ : ℝ)) ^ (2 ^ j) := by positivity
  have hu3 : (1 : ℝ) / n₀ ≤ 1 / 3 := by
    rw [div_le_div_iff₀ (by linarith) (by norm_num)]
    linarith
  have h1u : (0 : ℝ) < 1 - 1 / n₀ := by linarith
  have h0 : (0 : ℝ) < 1 / n₀ := by positivity
  calc _ ≤ (1 / n₀) * (1 - (1 / (n₀ : ℝ)) ^ (2 ^ j)) / (1 - 1 / n₀) := h
    _ ≤ (1 / n₀) * 1 / (1 - 1 / n₀) := by
        apply div_le_div_of_nonneg_right _ h1u.le
        apply mul_le_mul_of_nonneg_left _ h0.le
        linarith
    _ ≤ 3 / 2 * (1 / n₀) := by
        rw [div_le_iff₀ h1u]
        nlinarith

/-! ### The covering of a forward-closed class by the `E`-trees of its odd members -/

/-- Every member of a forward-closed class excluding `1` lies at a level `j ≤ log₂ log₂ x`
of the `E`-tree of an odd member `n₀ ≤ x`. -/
theorem logMass_le_treeLevels {A : ℕ → Prop} (hF : ForwardClosed A) (h1 : ¬A 1) (x : ℕ) :
    logMass A x ≤ ∑ n₀ ∈ {n₀ ∈ Icc 1 x | n₀ % 2 = 1 ∧ A n₀},
      ∑ j ∈ range (Nat.log 2 (Nat.log 2 x) + 1), ∑ n ∈ treeLevel n₀ j x, (1 : ℝ) / n := by
  have hnn : ∀ n : ℕ, (0 : ℝ) ≤ 1 / n := fun n => by positivity
  have hsub : {n ∈ Icc 1 x | A n} ⊆ ({n₀ ∈ Icc 1 x | n₀ % 2 = 1 ∧ A n₀}).biUnion
      (fun n₀ => (range (Nat.log 2 (Nat.log 2 x) + 1)).biUnion (fun j => treeLevel n₀ j x)) := by
    intro n hn
    simp only [mem_filter, mem_Icc] at hn
    obtain ⟨⟨hn1, hnx⟩, hA⟩ := hn
    obtain ⟨k, hodd, hAk, heven⟩ := exists_odd_ancestor hF n hn1 hA
    have hdesc : EvenDescent n k (floorPower^[k] n) := ⟨rfl, heven⟩
    have hpos : 1 ≤ floorPower^[k] n := floorPower_iterate_pos hn1 k
    have hne : floorPower^[k] n ≠ 1 := fun h => h1 (h ▸ hAk)
    have hge : 2 ≤ floorPower^[k] n := by omega
    have hpow := evenDescent_pow_le hdesc
    have hle : floorPower^[k] n ≤ n := le_trans (Nat.le_self_pow (Nat.two_pow_pos k).ne' _) hpow
    rw [mem_biUnion]
    refine ⟨floorPower^[k] n, ?_, ?_⟩
    · simp only [mem_filter, mem_Icc]
      exact ⟨⟨hpos, le_trans hle hnx⟩, hodd, hAk⟩
    · rw [mem_biUnion]
      refine ⟨k, ?_, ?_⟩
      · rw [mem_range]
        have h2 : 2 ^ (2 ^ k) ≤ n := le_trans (Nat.pow_le_pow_left hge _) hpow
        have h3 : 2 ^ k ≤ Nat.log 2 x := Nat.le_log_of_pow_le (by norm_num) (le_trans h2 hnx)
        have h4 : k ≤ Nat.log 2 (Nat.log 2 x) := Nat.le_log_of_pow_le (by norm_num) h3
        omega
      · simp only [treeLevel, mem_filter, mem_Icc]
        exact ⟨⟨hn1, hnx⟩, hdesc⟩
  calc logMass A x
      ≤ ∑ n ∈ ({n₀ ∈ Icc 1 x | n₀ % 2 = 1 ∧ A n₀}).biUnion
          (fun n₀ => (range (Nat.log 2 (Nat.log 2 x) + 1)).biUnion (fun j => treeLevel n₀ j x)),
          (1 : ℝ) / n :=
        sum_le_sum_of_subset_of_nonneg hsub (fun n _ _ => hnn n)
    _ ≤ ∑ n₀ ∈ {n₀ ∈ Icc 1 x | n₀ % 2 = 1 ∧ A n₀},
          ∑ n ∈ (range (Nat.log 2 (Nat.log 2 x) + 1)).biUnion (fun j => treeLevel n₀ j x),
            (1 : ℝ) / n :=
        sum_biUnion_le_sum _ _ _ hnn
    _ ≤ _ := by
        apply sum_le_sum
        intro n₀ _
        exact sum_biUnion_le_sum _ _ _ hnn

/-- **The `E`-tree bound.** The log-mass of a forward-closed class excluding `1` is at most
`(3/2)(1 + log₂ log₂ x)` times its odd log-mass. -/
theorem logMass_le_oddLogMass {A : ℕ → Prop} (hF : ForwardClosed A) (h1 : ¬A 1) (x : ℕ) :
    logMass A x ≤ 3 / 2 * ((Nat.log 2 (Nat.log 2 x) : ℝ) + 1) * oddLogMass A x := by
  calc logMass A x
      ≤ ∑ n₀ ∈ {n₀ ∈ Icc 1 x | n₀ % 2 = 1 ∧ A n₀},
          ∑ j ∈ range (Nat.log 2 (Nat.log 2 x) + 1), ∑ n ∈ treeLevel n₀ j x, (1 : ℝ) / n :=
        logMass_le_treeLevels hF h1 x
    _ ≤ ∑ n₀ ∈ {n₀ ∈ Icc 1 x | n₀ % 2 = 1 ∧ A n₀},
          ∑ j ∈ range (Nat.log 2 (Nat.log 2 x) + 1), 3 / 2 * (1 / (n₀ : ℝ)) := by
        apply sum_le_sum
        intro n₀ hn₀
        simp only [mem_filter, mem_Icc] at hn₀
        have hne : n₀ ≠ 1 := fun h => h1 (h ▸ hn₀.2.2)
        have h3 : 3 ≤ n₀ := by omega
        apply sum_le_sum
        intro j _
        exact treeLevel_logMass_le' h3 j x
    _ = 3 / 2 * ((Nat.log 2 (Nat.log 2 x) : ℝ) + 1) * oddLogMass A x := by
        simp only [sum_const, card_range, nsmul_eq_mul, oddLogMass, mul_sum]
        apply sum_congr rfl
        intro n₀ _
        push_cast
        ring

/-! ### From the dyadic rate to the odd log-mass -/

theorem oddLogMass_double (A : ℕ → Prop) (y : ℕ) :
    oddLogMass A (2 * y) = oddLogMass A y + ∑ n ∈ oddMembers A y, (1 : ℝ) / n := by
  unfold oddLogMass
  rw [← sum_filter_add_sum_filter_not {n ∈ Icc 1 (2 * y) | n % 2 = 1 ∧ A n} (fun n => n ≤ y)]
  congr 1
  · apply sum_congr _ (fun _ _ => rfl)
    ext n
    simp only [mem_filter, mem_Icc]
    constructor
    · rintro ⟨⟨⟨h1, _⟩, h⟩, hy⟩
      exact ⟨⟨h1, hy⟩, h⟩
    · rintro ⟨⟨h1, hy⟩, h⟩
      exact ⟨⟨⟨h1, by omega⟩, h⟩, hy⟩
  · apply sum_congr _ (fun _ _ => rfl)
    ext n
    simp only [oddMembers, mem_filter, mem_Icc, mem_Ioc, not_le]
    constructor
    · rintro ⟨⟨⟨_, h2⟩, h⟩, hy⟩
      exact ⟨⟨hy, h2⟩, h⟩
    · rintro ⟨⟨hy, h2⟩, h⟩
      exact ⟨⟨⟨by omega, h2⟩, h⟩, hy⟩

theorem oddLogMass_mono (A : ℕ → Prop) {x x' : ℕ} (h : x ≤ x') :
    oddLogMass A x ≤ oddLogMass A x' :=
  sum_le_sum_of_subset_of_nonneg (filter_subset_filter _ (Icc_subset_Icc_right h))
    (fun n _ _ => by positivity)

theorem oddLogMass_nonneg (A : ℕ → Prop) (x : ℕ) : 0 ≤ oddLogMass A x :=
  sum_nonneg fun n _ => by positivity

theorem oddMembers_sum_le (A : ℕ → Prop) {y : ℕ} (hy : 1 ≤ y) :
    ∑ n ∈ oddMembers A y, (1 : ℝ) / n ≤ (oddMembers A y).card / y := by
  have hterm : ∀ n ∈ oddMembers A y, (1 : ℝ) / n ≤ 1 / y := by
    intro n hn
    simp only [oddMembers, mem_filter, mem_Ioc] at hn
    exact one_div_le_one_div_of_le (by exact_mod_cast hy) (by exact_mod_cast hn.1.1.le)
  calc _ ≤ (oddMembers A y).card • ((1 : ℝ) / y) := sum_le_card_nsmul _ _ _ hterm
    _ = _ := by rw [nsmul_eq_mul]; ring

/-- Doubling `K` times from `y₀`: the odd log-mass grows by at most the dyadic rates. -/
theorem oddLogMass_pow_le {A : ℕ → Prop} {y₀ : ℕ} (hy₀ : 1 ≤ y₀) (e : ℝ)
    (hdy : ∀ y : ℕ, y₀ ≤ y → ((oddMembers A y).card : ℝ) ≤ y * Real.log y ^ (-e)) (K : ℕ) :
    oddLogMass A (2 ^ K * y₀) ≤
      oddLogMass A y₀ + ∑ k ∈ range K, Real.log ((2 ^ k * y₀ : ℕ) : ℝ) ^ (-e) := by
  induction K with
  | zero => simp
  | succ K ih =>
      have hy : y₀ ≤ 2 ^ K * y₀ := Nat.le_mul_of_pos_left y₀ (Nat.two_pow_pos K)
      have hy1 : 1 ≤ 2 ^ K * y₀ := le_trans hy₀ hy
      have hyR : (0 : ℝ) < ((2 ^ K * y₀ : ℕ) : ℝ) := by exact_mod_cast hy1
      rw [pow_succ, mul_comm (2 ^ K) 2, mul_assoc, oddLogMass_double, sum_range_succ]
      have hb := oddMembers_sum_le A hy1
      have hc := hdy _ hy
      have : ∑ n ∈ oddMembers A (2 ^ K * y₀), (1 : ℝ) / n ≤
          Real.log ((2 ^ K * y₀ : ℕ) : ℝ) ^ (-e) := by
        calc _ ≤ ((oddMembers A (2 ^ K * y₀)).card : ℝ) / ((2 ^ K * y₀ : ℕ) : ℝ) := hb
          _ ≤ (((2 ^ K * y₀ : ℕ) : ℝ) * Real.log ((2 ^ K * y₀ : ℕ) : ℝ) ^ (-e)) /
                ((2 ^ K * y₀ : ℕ) : ℝ) :=
              div_le_div_of_nonneg_right hc hyR.le
          _ = _ := by field_simp
      linarith

/-- The telescoping Bernoulli bound `Σ_{k=1}^{K} k^{-e} ≤ K^{1-e}/(1-e)` for `0 < e < 1`. -/
theorem sum_rpow_neg_le {e : ℝ} (he0 : 0 < e) (he1 : e < 1) (K : ℕ) :
    ∑ k ∈ range K, ((k : ℝ) + 1) ^ (-e) ≤ (K : ℝ) ^ (1 - e) / (1 - e) := by
  induction K with
  | zero => simp [Real.zero_rpow (by linarith : (1 : ℝ) - e ≠ 0)]
  | succ K ih =>
      rw [sum_range_succ]
      have hK : (0 : ℝ) < (K : ℝ) + 1 := by positivity
      have hbern : (K : ℝ) ^ (1 - e) ≤
          ((K : ℝ) + 1) ^ (1 - e) * (1 + (1 - e) * -(1 / ((K : ℝ) + 1))) := by
        have hs : (-1 : ℝ) ≤ -(1 / ((K : ℝ) + 1)) := by
          have : (1 : ℝ) / ((K : ℝ) + 1) ≤ 1 := by
            rw [div_le_one hK]
            linarith
          linarith
        have hb := rpow_one_add_le_one_add_mul_self hs (by linarith : (0 : ℝ) ≤ 1 - e)
          (by linarith : 1 - e ≤ 1)
        have hK' : (K : ℝ) = ((K : ℝ) + 1) * (1 + -(1 / ((K : ℝ) + 1))) := by
          field_simp
          ring
        have hnn : (0 : ℝ) ≤ 1 + -(1 / ((K : ℝ) + 1)) := by linarith
        calc (K : ℝ) ^ (1 - e) = (((K : ℝ) + 1) * (1 + -(1 / ((K : ℝ) + 1)))) ^ (1 - e) := by
              rw [← hK']
          _ = ((K : ℝ) + 1) ^ (1 - e) * (1 + -(1 / ((K : ℝ) + 1))) ^ (1 - e) := by
              rw [Real.mul_rpow hK.le hnn]
          _ ≤ ((K : ℝ) + 1) ^ (1 - e) * (1 + (1 - e) * -(1 / ((K : ℝ) + 1))) :=
              mul_le_mul_of_nonneg_left hb (Real.rpow_nonneg hK.le _)
      have hsub : ((K : ℝ) + 1) ^ (1 - e) / ((K : ℝ) + 1) = ((K : ℝ) + 1) ^ (-e) := by
        rw [← Real.rpow_sub_one hK.ne']
        congr 1
        ring
      have hkey : (1 - e) * ((K : ℝ) + 1) ^ (-e) ≤ ((K : ℝ) + 1) ^ (1 - e) - (K : ℝ) ^ (1 - e) := by
        have : ((K : ℝ) + 1) ^ (1 - e) * (1 + (1 - e) * -(1 / ((K : ℝ) + 1))) =
            ((K : ℝ) + 1) ^ (1 - e) - (1 - e) * (((K : ℝ) + 1) ^ (1 - e) / ((K : ℝ) + 1)) := by
          ring
        rw [this, hsub] at hbern
        linarith
      have h1e : (0 : ℝ) < 1 - e := by linarith
      have hstep : ((K : ℝ) + 1) ^ (-e) ≤
          (((K : ℝ) + 1) ^ (1 - e) - (K : ℝ) ^ (1 - e)) / (1 - e) := by
        rw [le_div_iff₀ h1e]
        linarith
      push_cast
      calc _ ≤ (K : ℝ) ^ (1 - e) / (1 - e) +
              (((K : ℝ) + 1) ^ (1 - e) - (K : ℝ) ^ (1 - e)) / (1 - e) := add_le_add ih hstep
        _ = _ := by ring

/-- **The dyadic sum.** A rate `y (log y)^{-e}` on the odd members of every block `(y, 2y]`,
`y ≥ y₀ ≥ 2`, bounds the odd log-mass up to `x` by
`oddLogMass y₀ + (log 2)^{-e} (log₂ x + 1)^{1-e}/(1-e)`. -/
theorem oddLogMass_le_of_dyadic {A : ℕ → Prop} {y₀ : ℕ} (hy₀ : 2 ≤ y₀) {e : ℝ} (he0 : 0 < e)
    (he1 : e < 1)
    (hdy : ∀ y : ℕ, y₀ ≤ y → ((oddMembers A y).card : ℝ) ≤ y * Real.log y ^ (-e)) (x : ℕ) :
    oddLogMass A x ≤ oddLogMass A y₀ +
      Real.log 2 ^ (-e) * ((Nat.log 2 x : ℝ) + 1) ^ (1 - e) / (1 - e) := by
  have hxle : x ≤ 2 ^ (Nat.log 2 x + 1) * y₀ := by
    have h1 := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) x
    calc x ≤ 2 ^ (Nat.log 2 x + 1) := h1.le
      _ ≤ 2 ^ (Nat.log 2 x + 1) * y₀ := Nat.le_mul_of_pos_right _ (by omega)
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hterm : ∀ k ∈ range (Nat.log 2 x + 1),
      Real.log ((2 ^ k * y₀ : ℕ) : ℝ) ^ (-e) ≤ Real.log 2 ^ (-e) * ((k : ℝ) + 1) ^ (-e) := by
    intro k _
    have hy₀R : (2 : ℝ) ≤ y₀ := by exact_mod_cast hy₀
    have hlogy : Real.log 2 ≤ Real.log y₀ := Real.log_le_log (by norm_num) hy₀R
    have hcast : ((2 ^ k * y₀ : ℕ) : ℝ) = 2 ^ k * (y₀ : ℝ) := by push_cast; ring
    have hlog : ((k : ℝ) + 1) * Real.log 2 ≤ Real.log ((2 ^ k * y₀ : ℕ) : ℝ) := by
      rw [hcast, Real.log_mul (by positivity) (by positivity), Real.log_pow]
      linarith
    calc Real.log ((2 ^ k * y₀ : ℕ) : ℝ) ^ (-e) ≤ (((k : ℝ) + 1) * Real.log 2) ^ (-e) :=
          Real.rpow_le_rpow_of_nonpos (by positivity) hlog (by linarith)
      _ = Real.log 2 ^ (-e) * ((k : ℝ) + 1) ^ (-e) := by
          rw [Real.mul_rpow (by positivity) hlog2.le]
          ring
  calc oddLogMass A x ≤ oddLogMass A (2 ^ (Nat.log 2 x + 1) * y₀) := oddLogMass_mono A hxle
    _ ≤ oddLogMass A y₀ +
          ∑ k ∈ range (Nat.log 2 x + 1), Real.log ((2 ^ k * y₀ : ℕ) : ℝ) ^ (-e) :=
        oddLogMass_pow_le (by omega) e hdy _
    _ ≤ oddLogMass A y₀ +
          ∑ k ∈ range (Nat.log 2 x + 1), Real.log 2 ^ (-e) * ((k : ℝ) + 1) ^ (-e) :=
        add_le_add le_rfl (sum_le_sum hterm)
    _ = oddLogMass A y₀ +
          Real.log 2 ^ (-e) * ∑ k ∈ range (Nat.log 2 x + 1), ((k : ℝ) + 1) ^ (-e) := by
        rw [mul_sum]
    _ ≤ oddLogMass A y₀ +
          Real.log 2 ^ (-e) * (((Nat.log 2 x + 1 : ℕ) : ℝ) ^ (1 - e) / (1 - e)) :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left (sum_rpow_neg_le he0 he1 _)
          (Real.rpow_nonneg hlog2.le _))
    _ = _ := by push_cast; ring

/-! ### The asymptotic step -/

theorem natLog_le_logb {m : ℕ} (hm : 1 ≤ m) : (Nat.log 2 m : ℝ) ≤ Real.logb 2 m := by
  rw [Real.le_logb_iff_rpow_le (by norm_num) (by exact_mod_cast hm), Real.rpow_natCast]
  exact_mod_cast Nat.pow_log_le_self 2 (by omega)

theorem log_le_rpow_div {v δ : ℝ} (hv : 0 < v) (hδ : 0 < δ) : Real.log v ≤ v ^ δ / δ := by
  have h := Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hv δ)
  rw [Real.log_rpow hv] at h
  rw [le_div_iff₀ hδ]
  linarith

theorem exists_rpow_gt {δ : ℝ} (hδ : 0 < δ) (c : ℝ) :
    ∃ u₁ : ℝ, 1 ≤ u₁ ∧ ∀ u, u₁ ≤ u → c < u ^ δ := by
  refine ⟨max 1 ((max c 0 + 1) ^ (1 / δ)), le_max_left _ _, ?_⟩
  intro u hu
  have hc0' : 0 ≤ max c 0 := le_max_right c 0
  have hc0 : 0 ≤ max c 0 + 1 := by linarith
  have h1 : (max c 0 + 1) ^ (1 / δ) ≤ u := le_trans (le_max_right _ _) hu
  have h2 : ((max c 0 + 1) ^ (1 / δ)) ^ δ ≤ u ^ δ :=
    Real.rpow_le_rpow (Real.rpow_nonneg hc0 _) h1 hδ.le
  rw [← Real.rpow_mul hc0, one_div_mul_cancel hδ.ne', Real.rpow_one] at h2
  have : c ≤ max c 0 := le_max_left _ _
  linarith

/-- The upper bound at every `x ≥ 3`: `logMass A x ≤ D (log x)^{δ + 1 - e}` for an explicit
`D`, once the dyadic rate holds with `0 < e < 1` from `y₀ ≥ 2` and `0 < δ ≤ 1`. -/
theorem logMass_le_rpow {A : ℕ → Prop} (hF : ForwardClosed A) (h1 : ¬A 1) {y₀ : ℕ}
    (hy₀ : 2 ≤ y₀) {e : ℝ} (he0 : 0 < e) (he1 : e < 1)
    (hdy : ∀ y : ℕ, y₀ ≤ y → ((oddMembers A y).card : ℝ) ≤ y * Real.log y ^ (-e))
    {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ x : ℕ, 3 ≤ x → logMass A x ≤ D * Real.log x ^ (δ + (1 - e)) := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hB0 := oddLogMass_nonneg A y₀
  have hc0 : 0 ≤ Real.log 2 ^ (-e) / (1 - e) :=
    div_nonneg (Real.rpow_nonneg hlog2.le _) (by linarith)
  have hc₂0 : 0 ≤ Real.log 2 ^ (-e) / (1 - e) * (2 / Real.log 2) ^ (1 - e) :=
    mul_nonneg hc0 (Real.rpow_nonneg (by positivity) _)
  refine ⟨3 / 2 * (4 / δ + 1) *
    (oddLogMass A y₀ + Real.log 2 ^ (-e) / (1 - e) * (2 / Real.log 2) ^ (1 - e)),
    by positivity, ?_⟩
  intro x hx
  have hxR : (3 : ℝ) ≤ x := by exact_mod_cast hx
  have hxpos : (0 : ℝ) < x := by linarith
  have hu1 : 1 ≤ Real.log x := by
    rw [Real.le_log_iff_exp_le hxpos]
    exact le_trans (le_of_lt (lt_trans Real.exp_one_lt_d9 (by norm_num))) hxR
  have hu0 : 0 < Real.log x := by linarith
  have hL1 : 1 ≤ Nat.log 2 x := Nat.le_log_of_pow_le (by norm_num) (by omega : 2 ^ 1 ≤ x)
  have hLpos : (0 : ℝ) < Nat.log 2 x := by exact_mod_cast hL1
  have hL : (Nat.log 2 x : ℝ) ≤ Real.log x / Real.log 2 := by
    have := natLog_le_logb (by omega : 1 ≤ x)
    rwa [Real.logb] at this
  have hlog2half : (1 : ℝ) / 2 < Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hL2 : (Nat.log 2 x : ℝ) ≤ 2 * Real.log x := by
    have h2 : Real.log x / Real.log 2 ≤ 2 * Real.log x := by
      rw [div_le_iff₀ hlog2]
      nlinarith
    linarith
  have hK1 : (Nat.log 2 x : ℝ) + 1 ≤ 2 / Real.log 2 * Real.log x := by
    have h1' : (1 : ℝ) ≤ Real.log x / Real.log 2 := by
      rw [le_div_iff₀ hlog2]
      have : Real.log 2 ≤ Real.log x := Real.log_le_log (by norm_num) (by linarith)
      linarith
    have : 2 / Real.log 2 * Real.log x = Real.log x / Real.log 2 + Real.log x / Real.log 2 := by
      ring
    linarith
  have hJ : (Nat.log 2 (Nat.log 2 x) : ℝ) + 1 ≤ (4 / δ + 1) * Real.log x ^ δ := by
    have h1' := natLog_le_logb hL1
    rw [Real.logb] at h1'
    have h2' : Real.log (Nat.log 2 x : ℝ) ≤ (Nat.log 2 x : ℝ) ^ δ / δ := log_le_rpow_div hLpos hδ0
    have h3' : (Nat.log 2 x : ℝ) ^ δ ≤ (2 * Real.log x) ^ δ :=
      Real.rpow_le_rpow hLpos.le hL2 hδ0.le
    have h4' : (2 * Real.log x) ^ δ ≤ 2 * Real.log x ^ δ := by
      rw [Real.mul_rpow (by norm_num) hu0.le]
      have : (2 : ℝ) ^ δ ≤ 2 := Real.rpow_le_self_of_one_le (by norm_num) hδ1
      exact mul_le_mul_of_nonneg_right this (Real.rpow_nonneg hu0.le _)
    have hu1δ : 1 ≤ Real.log x ^ δ := Real.one_le_rpow hu1 hδ0.le
    have hlogL : 0 ≤ Real.log (Nat.log 2 x : ℝ) := Real.log_natCast_nonneg _
    have h5' : Real.log (Nat.log 2 x : ℝ) / Real.log 2 ≤ 2 * Real.log (Nat.log 2 x : ℝ) := by
      rw [div_le_iff₀ hlog2]
      nlinarith
    have h6' : Real.log (Nat.log 2 x : ℝ) ≤ 2 * Real.log x ^ δ / δ := by
      calc Real.log (Nat.log 2 x : ℝ) ≤ (Nat.log 2 x : ℝ) ^ δ / δ := h2'
        _ ≤ 2 * Real.log x ^ δ / δ := by
            apply div_le_div_of_nonneg_right _ hδ0.le
            linarith
    have h7' : 2 * (2 * Real.log x ^ δ / δ) = 4 / δ * Real.log x ^ δ := by
      field_simp
      ring
    calc (Nat.log 2 (Nat.log 2 x) : ℝ) + 1 ≤ Real.log (Nat.log 2 x : ℝ) / Real.log 2 + 1 := by
          linarith
      _ ≤ 2 * (2 * Real.log x ^ δ / δ) + 1 := by linarith
      _ ≤ 4 / δ * Real.log x ^ δ + Real.log x ^ δ := by linarith
      _ = (4 / δ + 1) * Real.log x ^ δ := by ring
  have hodd := oddLogMass_le_of_dyadic hy₀ he0 he1 hdy x
  have hmain := logMass_le_oddLogMass hF h1 x
  have hpow1 : ((Nat.log 2 x : ℝ) + 1) ^ (1 - e) ≤
      (2 / Real.log 2) ^ (1 - e) * Real.log x ^ (1 - e) := by
    rw [← Real.mul_rpow (by positivity) hu0.le]
    exact Real.rpow_le_rpow (by positivity) hK1 (by linarith)
  have hu1e : 1 ≤ Real.log x ^ (1 - e) := Real.one_le_rpow hu1 (by linarith)
  have hodd' : oddLogMass A x ≤
      (oddLogMass A y₀ + Real.log 2 ^ (-e) / (1 - e) * (2 / Real.log 2) ^ (1 - e)) *
        Real.log x ^ (1 - e) := by
    calc oddLogMass A x
        ≤ oddLogMass A y₀ + Real.log 2 ^ (-e) / (1 - e) * ((Nat.log 2 x : ℝ) + 1) ^ (1 - e) := by
          calc _ ≤ _ := hodd
            _ = _ := by ring
      _ ≤ oddLogMass A y₀ + Real.log 2 ^ (-e) / (1 - e) *
            ((2 / Real.log 2) ^ (1 - e) * Real.log x ^ (1 - e)) :=
          add_le_add le_rfl (mul_le_mul_of_nonneg_left hpow1 hc0)
      _ ≤ oddLogMass A y₀ * Real.log x ^ (1 - e) + Real.log 2 ^ (-e) / (1 - e) *
            ((2 / Real.log 2) ^ (1 - e) * Real.log x ^ (1 - e)) := by
          have : oddLogMass A y₀ ≤ oddLogMass A y₀ * Real.log x ^ (1 - e) := by
            nlinarith
          linarith
      _ = _ := by ring
  have hJ0 : (0 : ℝ) ≤ (Nat.log 2 (Nat.log 2 x) : ℝ) + 1 := by positivity
  have hoddx := oddLogMass_nonneg A x
  calc logMass A x ≤ 3 / 2 * ((Nat.log 2 (Nat.log 2 x) : ℝ) + 1) * oddLogMass A x := hmain
    _ ≤ 3 / 2 * ((4 / δ + 1) * Real.log x ^ δ) *
          ((oddLogMass A y₀ + Real.log 2 ^ (-e) / (1 - e) * (2 / Real.log 2) ^ (1 - e)) *
            Real.log x ^ (1 - e)) := by
        apply mul_le_mul _ hodd' hoddx (by positivity)
        exact mul_le_mul_of_nonneg_left hJ (by norm_num)
    _ = 3 / 2 * (4 / δ + 1) *
          (oddLogMass A y₀ + Real.log 2 ^ (-e) / (1 - e) * (2 / Real.log 2) ^ (1 - e)) *
          (Real.log x ^ δ * Real.log x ^ (1 - e)) := by ring
    _ = _ := by rw [← Real.rpow_add hu0]

/-- **Paper C Theorem 7.2 (Theorem A of the Tao-reduction note), given the contagion
bound.** Let `A` be forward-closed and exclude `1`. Suppose the contagion bound holds for
`A` whenever it is nonempty — `Σ_{n ≤ x, n ∈ A} 1/n ≥ K (log x)^λ` for all large `x`, some
`K > 0` — and that its odd members satisfy the Tao-type rate
`#{n odd in (y, 2y] : n ∈ A} ≤ y (log y)^{-e}` for all large `y`, with `e > 1 - λ`. Then `A`
has no positive member. -/
theorem tao_rate_implies_empty {A : ℕ → Prop} (hF : ForwardClosed A) (h1 : ¬A 1)
    {lam e : ℝ} (hlam0 : 0 < lam) (hlam1 : lam < 1) (he : 1 - lam < e)
    (hlow : (∃ n, 1 ≤ n ∧ A n) → ∃ K : ℝ, 0 < K ∧ ∃ x₀ : ℕ, ∀ x : ℕ, x₀ ≤ x →
      K * Real.log x ^ lam ≤ logMass A x)
    (htao : ∃ y₀ : ℕ, ∀ y : ℕ, y₀ ≤ y →
      ((oddMembers A y).card : ℝ) ≤ y * Real.log y ^ (-e)) :
    ∀ n, 1 ≤ n → ¬A n := by
  intro n hn hA
  obtain ⟨K, hK, x₀, hlow'⟩ := hlow ⟨n, hn, hA⟩
  obtain ⟨y₀, hy⟩ := htao
  -- the reduced exponent `e' ∈ (1 - λ, 1)`, `e' ≤ e`
  obtain ⟨e', he'e, he'1, he'lo, he'0⟩ :
      ∃ e' : ℝ, e' ≤ e ∧ e' < 1 ∧ 1 - lam < e' ∧ 0 < e' :=
    ⟨min e (1 - lam / 2), min_le_left _ _,
      lt_of_le_of_lt (min_le_right _ _) (by linarith), lt_min he (by linarith), by
        have : 1 - lam < min e (1 - lam / 2) := lt_min he (by linarith)
        linarith⟩
  -- the reduced dyadic hypothesis from `y₁ = max y₀ 3`
  obtain ⟨y₁, hy₁2, hy₁0, hy₁3⟩ : ∃ y₁ : ℕ, 2 ≤ y₁ ∧ y₀ ≤ y₁ ∧ 3 ≤ y₁ :=
    ⟨max y₀ 3, le_trans (by norm_num) (le_max_right y₀ 3), le_max_left _ _, le_max_right _ _⟩
  have hdy : ∀ y : ℕ, y₁ ≤ y → ((oddMembers A y).card : ℝ) ≤ y * Real.log y ^ (-e') := by
    intro y hy'
    have hy3 : (3 : ℝ) ≤ y := by exact_mod_cast le_trans hy₁3 hy'
    have hlog1 : 1 ≤ Real.log y := by
      rw [Real.le_log_iff_exp_le (by linarith)]
      exact le_trans (le_of_lt (lt_trans Real.exp_one_lt_d9 (by norm_num))) hy3
    calc ((oddMembers A y).card : ℝ) ≤ y * Real.log y ^ (-e) := hy y (le_trans hy₁0 hy')
      _ ≤ y * Real.log y ^ (-e') := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact Real.rpow_le_rpow_of_exponent_le hlog1 (by linarith)
  -- the gap `δ`, with `λ = (δ + 1 - e') + δ`
  obtain ⟨δ, hδ0, hδ1, hδeq⟩ : ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ lam = δ + (1 - e') + δ :=
    ⟨(lam - (1 - e')) / 2, by linarith, by linarith, by ring⟩
  obtain ⟨D, hD0, hD⟩ := logMass_le_rpow hF h1 hy₁2 he'0 he'1 hdy hδ0 hδ1
  -- a scale where the lower bound wins
  obtain ⟨u₁, hu₁1, hu₁⟩ := exists_rpow_gt hδ0 (D / K)
  obtain ⟨x, hxx₀, hx3, hxu⟩ : ∃ x : ℕ, x₀ ≤ x ∧ 3 ≤ x ∧ Real.exp u₁ ≤ x :=
    ⟨max (max x₀ 3) ⌈Real.exp u₁⌉₊, le_trans (le_max_left _ _) (le_max_left _ _),
      le_trans (le_max_right _ _) (le_max_left _ _), by
        have h := Nat.le_ceil (Real.exp u₁)
        have h' : (⌈Real.exp u₁⌉₊ : ℝ) ≤ ((max (max x₀ 3) ⌈Real.exp u₁⌉₊ : ℕ) : ℝ) := by
          exact_mod_cast le_max_right _ _
        linarith⟩
  have hxpos : (0 : ℝ) < x := by
    have : (3 : ℝ) ≤ x := by exact_mod_cast hx3
    linarith
  have hu : u₁ ≤ Real.log x := (Real.le_log_iff_exp_le hxpos).mpr hxu
  have hu0 : 0 < Real.log x := lt_of_lt_of_le (by linarith) hu
  have hgt : D / K < Real.log x ^ δ := hu₁ _ hu
  have hgt' : D < K * Real.log x ^ δ := by
    rw [div_lt_iff₀ hK] at hgt
    linarith
  have hlower := hlow' x hxx₀
  have hupper := hD x hx3
  have hsplit : Real.log x ^ lam = Real.log x ^ (δ + (1 - e')) * Real.log x ^ δ := by
    rw [hδeq, Real.rpow_add hu0]
  have hpos : 0 < Real.log x ^ (δ + (1 - e')) := Real.rpow_pos_of_pos hu0 _
  rw [hsplit] at hlower
  -- `K u^δ · u^{δ+1-e'} ≤ D · u^{δ+1-e'}` against `D < K u^δ`
  have : K * Real.log x ^ δ * Real.log x ^ (δ + (1 - e')) ≤ D * Real.log x ^ (δ + (1 - e')) := by
    calc K * Real.log x ^ δ * Real.log x ^ (δ + (1 - e')) =
          K * (Real.log x ^ (δ + (1 - e')) * Real.log x ^ δ) := by ring
      _ ≤ logMass A x := hlower
      _ ≤ D * Real.log x ^ (δ + (1 - e')) := hupper
  have := le_of_mul_le_mul_right this hpos
  linarith

/-- **Paper C Theorem 7.2 on the failure set.** If the contagion bound holds for the failure
set whenever it is nonempty, and the odd failures satisfy the Tao-type rate with
`e > 1 - λ`, then every positive integer reaches `1`. -/
theorem tao_rate_implies_conjecture {lam e : ℝ} (hlam0 : 0 < lam) (hlam1 : lam < 1)
    (he : 1 - lam < e)
    (hlow : (∃ n, 1 ≤ n ∧ ¬ReachesOne n) → ∃ K : ℝ, 0 < K ∧ ∃ x₀ : ℕ, ∀ x : ℕ, x₀ ≤ x →
      K * Real.log x ^ lam ≤ logMass (fun n => ¬ReachesOne n) x)
    (htao : ∃ y₀ : ℕ, ∀ y : ℕ, y₀ ≤ y → ((oddFailures y).card : ℝ) ≤ y * Real.log y ^ (-e)) :
    ∀ n, 1 ≤ n → ReachesOne n := by
  intro n hn
  by_contra h
  refine tao_rate_implies_empty not_reachesOne_forwardClosed (fun h1 => h1 reachesOne_one)
    hlam0 hlam1 he hlow ?_ n hn h
  simpa only [oddMembers_not_reachesOne] using htao

end Problems.Juggler
