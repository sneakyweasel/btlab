import Problems.Juggler.FateTaoReduction

namespace Problems.Juggler

open Finset
open scoped Classical

/-!
# The seed of the contagion recursion

Paper C (`docs/theory/juggler_fate_almost_all_note.md`), Lemma 5.2.

A nonempty backward-closed class `A` contains an integer `m ≥ 3`
(`exists_ge_three_of_backwardClosed`), and for any such `m` the log-mass of `A` on the
half-interval `(√y, y]` is at least

  `c_A = (1 - 2/m⁴) (0.375/(m+1) - 1/((m+1)² - 1))`

for every `y ≥ (m+1)⁴` (`seed_lemma`). This is the seed `g_A ≥ c_A` on `[4 log(m+1), ∞)`
that the recursion lemma (`recursion_lemma`, Lemma 5.1) needs; the paper's `g_A(t)` at real
`t = log x` counts the integers in `(√x, x]`, which are exactly the integers in
`(⌊√⌊x⌋⌋, ⌊x⌋]`, so the integer form `y = ⌊x⌋` loses nothing.

The proof is the paper's. The even-block tree `S_0 = {m}`, `S_{k+1} = ⋃_{m'' ∈ S_k} E(m'')`
lies in `A` (Lemma 3.1) and in `[m^{2^k}, (m+1)^{2^k})`; its log-mass obeys
`ℓ(S_{k+1}) ≥ (1 - 2 m^{-2^k}) ℓ(S_k)` (the lower bound of Lemma 3.1, `m/(m+1)² ≥ (1-2/m)/m`),
so `ℓ(S_k) ≥ (1 - 2 Σ_{j ≥ 1} m^{-2^j}) ℓ(S_1) ≥ (3/4) ℓ(S_1) ≥ 0.375/(m+1)` for `m ≥ 3`, by
`m^{-2^j} ≤ m^{-2j}` and the geometric series `Σ_{j ≥ 1} m^{-2j} = 1/(m² - 1) ≤ 1/8`. For
`y ≥ (m+1)⁴` pick `k ≥ 2` with `(m+1)^{2^k} ≤ y < (m+1)^{2^{k+1}}`; then `S_k ⊆ (y^{1/4}, y]`,
its members above `√y` lie in `(√y, y]`, those at most `√y - 1` have their even blocks in
`(√y, y]` with log-mass at least `(1 - 2m^{-4})` times their own, and at most one member equals
`⌊√y⌋`, with `1/n ≤ 1/((m+1)² - 1)`.

Not a density theorem: the seed is one hypothesis of Theorem 5.3, whose other inputs
(Proposition 4.4 and the production inequalities) stay human proofs. Not a halt theorem.
-/

/-- Every nonempty backward-closed class (with a positive member) contains some `m ≥ 3`:
`1 ↦ 2 ↦ 4` through even blocks. -/
theorem exists_ge_three_of_backwardClosed {A : ℕ → Prop} (hA : BackwardClosed A) {a : ℕ}
    (ha : 1 ≤ a) (hAa : A a) : ∃ m, 3 ≤ m ∧ A m := by
  have h2 : A 1 → A 2 := fun h => even_block_mem hA h (by norm_num) (by norm_num) (by norm_num)
  have h4 : A 2 → A 4 := fun h => even_block_mem hA h (by norm_num) (by norm_num) (by norm_num)
  rcases Nat.lt_or_ge a 3 with h | h
  · interval_cases a
    · exact ⟨4, by norm_num, h4 (h2 hAa)⟩
    · exact ⟨4, by norm_num, h4 hAa⟩
  · exact ⟨a, h, hAa⟩

/-! ### The even-block tree -/

/-- `S_k`: the `k`-fold even-block tree of `m`, `S_0 = {m}`, `S_{k+1} = ⋃_{m'' ∈ S_k} E(m'')`. -/
noncomputable def blockTree (m : ℕ) : ℕ → Finset ℕ
  | 0 => {m}
  | k + 1 => (blockTree m k).biUnion evenBlock

theorem blockTree_zero (m : ℕ) : blockTree m 0 = {m} := rfl

theorem blockTree_succ (m k : ℕ) : blockTree m (k + 1) = (blockTree m k).biUnion evenBlock := rfl

/-- The tree of a member lies in the class (Lemma 3.1). -/
theorem blockTree_mem {A : ℕ → Prop} (hA : BackwardClosed A) {m : ℕ} (hm : A m) :
    ∀ k, ∀ n ∈ blockTree m k, A n := by
  intro k
  induction k with
  | zero =>
      intro n hn
      rw [blockTree_zero, mem_singleton] at hn
      exact hn ▸ hm
  | succ k ih =>
      intro n hn
      rw [blockTree_succ, mem_biUnion] at hn
      obtain ⟨m'', hm'', hn⟩ := hn
      simp only [evenBlock, mem_filter, mem_Ico] at hn
      exact even_block_mem hA (ih m'' hm'') hn.2 hn.1.1 hn.1.2

/-- Level `k` of the tree lies in `[m^{2^k}, (m+1)^{2^k})`. -/
theorem blockTree_bounds (m : ℕ) : ∀ k, ∀ n ∈ blockTree m k,
    m ^ (2 ^ k) ≤ n ∧ n < (m + 1) ^ (2 ^ k) := by
  intro k
  induction k with
  | zero =>
      intro n hn
      rw [blockTree_zero, mem_singleton] at hn
      subst hn
      simp
  | succ k ih =>
      intro n hn
      rw [blockTree_succ, mem_biUnion] at hn
      obtain ⟨m'', hm'', hn⟩ := hn
      simp only [evenBlock, mem_filter, mem_Ico] at hn
      obtain ⟨hlo, hhi⟩ := ih m'' hm''
      constructor
      · calc m ^ (2 ^ (k + 1)) = (m ^ (2 ^ k)) ^ 2 := by rw [pow_succ, pow_mul]
          _ ≤ m'' ^ 2 := Nat.pow_le_pow_left hlo 2
          _ = m'' * m'' := by ring
          _ ≤ n := hn.1.1
      · calc n < (m'' + 1) * (m'' + 1) := hn.1.2
          _ = (m'' + 1) ^ 2 := by ring
          _ ≤ ((m + 1) ^ (2 ^ k)) ^ 2 := Nat.pow_le_pow_left hhi 2
          _ = (m + 1) ^ (2 ^ (k + 1)) := by rw [← pow_mul, ← pow_succ]

/-- Distinct even blocks are disjoint: the block of `m` is the fibre `⌊√n⌋ = m`. -/
theorem evenBlock_disjoint {m₁ m₂ : ℕ} (h : m₁ ≠ m₂) : Disjoint (evenBlock m₁) (evenBlock m₂) := by
  rw [Finset.disjoint_left]
  intro n h1 h2
  simp only [evenBlock, mem_filter, mem_Ico] at h1 h2
  have e1 : m₁ = n.sqrt := Nat.eq_sqrt.mpr ⟨h1.1.1, h1.1.2⟩
  have e2 : m₂ = n.sqrt := Nat.eq_sqrt.mpr ⟨h2.1.1, h2.1.2⟩
  exact h (e1.trans e2.symm)

theorem evenBlock_pairwiseDisjoint (s : Finset ℕ) :
    (s : Set ℕ).PairwiseDisjoint evenBlock := by
  intro a _ b _ hab
  exact evenBlock_disjoint hab

/-- Lemma 3.1, the lower log-mass: `Σ_{n ∈ E(m)} 1/n ≥ m/(m+1)²`. -/
theorem evenBlock_logMass_ge {m : ℕ} (hm : 1 ≤ m) :
    (m : ℝ) / ((m + 1) * (m + 1)) ≤ ∑ n ∈ evenBlock m, (1 : ℝ) / n := by
  have hterm : ∀ n ∈ evenBlock m, (1 : ℝ) / ((m + 1) * (m + 1)) ≤ 1 / n := by
    intro n hn
    simp only [evenBlock, mem_filter, mem_Ico] at hn
    have hn0 : 0 < n := lt_of_lt_of_le (Nat.mul_pos hm hm) hn.1.1
    have : (n : ℝ) ≤ (m + 1) * (m + 1) := by exact_mod_cast hn.1.2.le
    exact one_div_le_one_div_of_le (by exact_mod_cast hn0) this
  have hcard : m ≤ (evenBlock m).card := even_block_card m
  calc (m : ℝ) / ((m + 1) * (m + 1)) = m * (1 / ((m + 1) * (m + 1))) := by ring
    _ ≤ (evenBlock m).card * (1 / ((m + 1) * (m + 1))) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact_mod_cast hcard
    _ = (evenBlock m).card • (1 / (((m : ℝ) + 1) * (m + 1))) := by rw [nsmul_eq_mul]
    _ ≤ ∑ n ∈ evenBlock m, (1 : ℝ) / n := card_nsmul_le_sum _ _ _ hterm

/-- `m/(m+1)² ≥ (1 - 2/m)/m` for `m ≥ 1`: Lemma 3.1's lower bound in the paper's form. -/
theorem evenBlock_logMass_ge' {m : ℕ} (hm : 1 ≤ m) :
    (1 - 2 / (m : ℝ)) * (1 / m) ≤ ∑ n ∈ evenBlock m, (1 : ℝ) / n := by
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  refine le_trans ?_ (evenBlock_logMass_ge hm)
  rw [show (1 - 2 / (m : ℝ)) * (1 / m) = ((m : ℝ) - 2) / (m * m) by field_simp]
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith

/-- One level up multiplies the log-mass by at least `1 - 2 m^{-2^k}`. -/
theorem blockTree_logMass_succ_ge {m : ℕ} (hm : 1 ≤ m) (k : ℕ) :
    (1 - 2 * (1 / (m : ℝ)) ^ (2 ^ k)) * ∑ n ∈ blockTree m k, (1 : ℝ) / n ≤
      ∑ n ∈ blockTree m (k + 1), (1 : ℝ) / n := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  rw [blockTree_succ, sum_biUnion (evenBlock_pairwiseDisjoint _), mul_sum]
  apply sum_le_sum
  intro m'' hm''
  obtain ⟨hlo, -⟩ := blockTree_bounds m k m'' hm''
  have hm''1 : 1 ≤ m'' := le_trans (Nat.one_le_pow _ _ hm) hlo
  have hm''R : (0 : ℝ) < m'' := by exact_mod_cast hm''1
  have hinv : (1 : ℝ) / m'' ≤ (1 / (m : ℝ)) ^ (2 ^ k) := by
    rw [one_div_pow]
    apply one_div_le_one_div_of_le (pow_pos hmR _)
    exact_mod_cast hlo
  calc (1 - 2 * (1 / (m : ℝ)) ^ (2 ^ k)) * (1 / m'')
      ≤ (1 - 2 / (m'' : ℝ)) * (1 / m'') := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        have : (2 : ℝ) / m'' = 2 * (1 / m'') := by ring
        linarith
    _ ≤ ∑ n ∈ evenBlock m'', (1 : ℝ) / n := evenBlock_logMass_ge' hm''1

theorem two_mul_succ_le_two_pow : ∀ j : ℕ, 2 * (j + 1) ≤ 2 ^ (j + 1) := by
  intro j
  induction j with
  | zero => norm_num
  | succ j ih =>
      have : 2 ≤ 2 ^ (j + 1) := by
        calc 2 = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ (j + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      calc 2 * (j + 1 + 1) = 2 * (j + 1) + 2 := by ring
        _ ≤ 2 ^ (j + 1) + 2 ^ (j + 1) := by omega
        _ = 2 ^ (j + 1 + 1) := by ring

/-- `Σ_{j=1}^{k} m^{-2^j} ≤ 1/(m² - 1)` for `m ≥ 2`. -/
theorem sum_inv_pow_two_pow_le {m : ℕ} (hm : 2 ≤ m) (k : ℕ) :
    ∑ j ∈ range k, (1 / (m : ℝ)) ^ (2 ^ (j + 1)) ≤ 1 / ((m : ℝ) ^ 2 - 1) := by
  have hmR : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hq0 : (0 : ℝ) ≤ 1 / m := by positivity
  have hq1 : (1 : ℝ) / m ≤ 1 := by
    rw [div_le_one (by linarith)]
    linarith
  set q : ℝ := (1 / (m : ℝ)) ^ 2 with hq
  have hq0' : 0 ≤ q := by positivity
  have hq1' : q < 1 := by
    rw [hq, div_pow, one_pow, div_lt_one (by positivity)]
    nlinarith
  have hterm : ∀ j ∈ range k, (1 / (m : ℝ)) ^ (2 ^ (j + 1)) ≤ q ^ (j + 1) := by
    intro j _
    rw [hq, ← pow_mul]
    exact pow_le_pow_of_le_one hq0 hq1 (two_mul_succ_le_two_pow j)
  have hgeom : ∑ j ∈ range k, q ^ (j + 1) ≤ q / (1 - q) := by
    have h1q : 0 < 1 - q := by linarith
    have : ∑ j ∈ range k, q ^ (j + 1) = q * ∑ j ∈ range k, q ^ j := by
      rw [mul_sum]
      apply sum_congr rfl
      intro j _
      ring
    rw [this, geom_sum_eq hq1'.ne k]
    have hk0 : 0 ≤ q ^ k := pow_nonneg hq0' k
    have hflip : (q ^ k - 1) / (q - 1) = (1 - q ^ k) / (1 - q) := by
      rw [div_eq_div_iff (by linarith) (by linarith)]
      ring
    rw [hflip, ← mul_div_assoc]
    apply div_le_div_of_nonneg_right _ h1q.le
    nlinarith
  calc ∑ j ∈ range k, (1 / (m : ℝ)) ^ (2 ^ (j + 1)) ≤ ∑ j ∈ range k, q ^ (j + 1) :=
        sum_le_sum hterm
    _ ≤ q / (1 - q) := hgeom
    _ = 1 / ((m : ℝ) ^ 2 - 1) := by
        rw [hq]
        field_simp

/-- `ℓ(S_{k+1}) ≥ (1 - 2 Σ_{j=1}^{k} m^{-2^j}) ℓ(S_1)`. -/
theorem blockTree_logMass_ge_aux {m : ℕ} (hm : 3 ≤ m) : ∀ k : ℕ,
    (1 - 2 * ∑ j ∈ range k, (1 / (m : ℝ)) ^ (2 ^ (j + 1))) * ∑ n ∈ blockTree m 1, (1 : ℝ) / n ≤
      ∑ n ∈ blockTree m (k + 1), (1 : ℝ) / n := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
      have hmR : (3 : ℝ) ≤ m := by exact_mod_cast hm
      have hS1 : 0 ≤ ∑ n ∈ blockTree m 1, (1 : ℝ) / n := sum_nonneg fun n _ => by positivity
      have hstep := blockTree_logMass_succ_ge (m := m) (by omega) (k + 1)
      have ha0 : 0 ≤ (1 / (m : ℝ)) ^ (2 ^ (k + 1)) := by positivity
      have ha1 : (1 / (m : ℝ)) ^ (2 ^ (k + 1)) ≤ 1 / 3 := by
        have h1 : (1 / (m : ℝ)) ^ (2 ^ (k + 1)) ≤ (1 / (m : ℝ)) ^ 1 :=
          pow_le_pow_of_le_one (by positivity)
            (by rw [div_le_one (by linarith)]; linarith) Nat.one_le_two_pow
        rw [pow_one] at h1
        have h2 : (1 : ℝ) / m ≤ 1 / 3 := by
          rw [div_le_div_iff₀ (by linarith) (by norm_num)]
          linarith
        linarith
      have hb0 : 0 ≤ ∑ j ∈ range k, (1 / (m : ℝ)) ^ (2 ^ (j + 1)) :=
        sum_nonneg fun j _ => by positivity
      rw [sum_range_succ]
      calc (1 - 2 * (∑ j ∈ range k, (1 / (m : ℝ)) ^ (2 ^ (j + 1)) + (1 / (m : ℝ)) ^ (2 ^ (k + 1)))) *
            ∑ n ∈ blockTree m 1, (1 : ℝ) / n
          ≤ (1 - 2 * (1 / (m : ℝ)) ^ (2 ^ (k + 1))) *
              ((1 - 2 * ∑ j ∈ range k, (1 / (m : ℝ)) ^ (2 ^ (j + 1))) *
                ∑ n ∈ blockTree m 1, (1 : ℝ) / n) := by
            have : (1 - 2 * (∑ j ∈ range k, (1 / (m : ℝ)) ^ (2 ^ (j + 1)) +
                (1 / (m : ℝ)) ^ (2 ^ (k + 1)))) ≤
                (1 - 2 * (1 / (m : ℝ)) ^ (2 ^ (k + 1))) *
                  (1 - 2 * ∑ j ∈ range k, (1 / (m : ℝ)) ^ (2 ^ (j + 1))) := by
              nlinarith
            rw [← mul_assoc]
            exact mul_le_mul_of_nonneg_right this hS1
        _ ≤ (1 - 2 * (1 / (m : ℝ)) ^ (2 ^ (k + 1))) * ∑ n ∈ blockTree m (k + 1), (1 : ℝ) / n :=
            mul_le_mul_of_nonneg_left ih (by linarith)
        _ ≤ ∑ n ∈ blockTree m (k + 1 + 1), (1 : ℝ) / n := hstep

/-- `ℓ(S_{k+1}) ≥ (3/4) ℓ(S_1) ≥ 0.375/(m+1)` for `m ≥ 3`. -/
theorem blockTree_logMass_ge {m : ℕ} (hm : 3 ≤ m) (k : ℕ) :
    3 / 8 / ((m : ℝ) + 1) ≤ ∑ n ∈ blockTree m (k + 1), (1 : ℝ) / n := by
  have hmR : (3 : ℝ) ≤ m := by exact_mod_cast hm
  have hsum := sum_inv_pow_two_pow_le (by omega : 2 ≤ m) k
  have h8 : 1 / ((m : ℝ) ^ 2 - 1) ≤ 1 / 8 := by
    rw [div_le_div_iff₀ (by nlinarith) (by norm_num)]
    nlinarith
  have hS1 : 1 / (2 * ((m : ℝ) + 1)) ≤ ∑ n ∈ blockTree m 1, (1 : ℝ) / n := by
    rw [blockTree_succ, blockTree_zero, singleton_biUnion]
    refine le_trans ?_ (evenBlock_logMass_ge (by omega))
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have hS1' : 0 ≤ ∑ n ∈ blockTree m 1, (1 : ℝ) / n := sum_nonneg fun n _ => by positivity
  calc 3 / 8 / ((m : ℝ) + 1) = 3 / 4 * (1 / (2 * ((m : ℝ) + 1))) := by
        field_simp
        ring
    _ ≤ (1 - 2 * ∑ j ∈ range k, (1 / (m : ℝ)) ^ (2 ^ (j + 1))) *
          ∑ n ∈ blockTree m 1, (1 : ℝ) / n := by
        apply mul_le_mul _ hS1 (by positivity) (by linarith)
        linarith
    _ ≤ _ := blockTree_logMass_ge_aux hm k

/-! ### The seed -/

/-- The log-mass of `A` on the half-interval `(√y, y]`, the paper's `g_A(log y)`. -/
noncomputable def halfLogMass (A : ℕ → Prop) (y : ℕ) : ℝ :=
  ∑ n ∈ {n ∈ Ioc y.sqrt y | A n}, (1 : ℝ) / n

/-- **Paper C Lemma 5.2 (seed).** If `A` is backward-closed and contains `m ≥ 3`, then for
every `y ≥ (m+1)⁴`,
`Σ_{√y < n ≤ y, n ∈ A} 1/n ≥ (1 - 2/m⁴) (3/8 · 1/(m+1) - 1/((m+1)² - 1))`. -/
theorem seed_lemma {A : ℕ → Prop} (hA : BackwardClosed A) {m : ℕ} (hm : 3 ≤ m) (hmA : A m)
    {y : ℕ} (hy : (m + 1) ^ 4 ≤ y) :
    (1 - 2 / (m : ℝ) ^ 4) * (3 / 8 / ((m : ℝ) + 1) - 1 / (((m : ℝ) + 1) ^ 2 - 1)) ≤
      halfLogMass A y := by
  have hmR : (3 : ℝ) ≤ m := by exact_mod_cast hm
  have hm1 : 1 < m + 1 := by omega
  have hy0 : y ≠ 0 := by
    have : 0 < (m + 1) ^ 4 := by positivity
    omega
  -- the scale `k ≥ 2` with `(m+1)^{2^k} ≤ y < (m+1)^{2^{k+1}}`
  set L := Nat.log (m + 1) y with hL
  have hL4 : 4 ≤ L := Nat.le_log_of_pow_le hm1 hy
  set k := Nat.log 2 L with hk
  have hk2 : 2 ≤ k := Nat.le_log_of_pow_le (by norm_num) (le_trans (by norm_num : 2 ^ 2 ≤ 4) hL4)
  have hpk : 2 ^ k ≤ L := Nat.pow_log_le_self 2 (by omega)
  have hLk : L < 2 ^ (k + 1) := Nat.lt_pow_succ_log_self (by norm_num) L
  have hylo : (m + 1) ^ (2 ^ k) ≤ y :=
    le_trans (Nat.pow_le_pow_right (by omega) hpk) (Nat.pow_log_le_self (m + 1) hy0)
  have hyhi : y < (m + 1) ^ (2 ^ (k + 1)) :=
    lt_of_lt_of_le (Nat.lt_pow_succ_log_self hm1 y) (Nat.pow_le_pow_right (by omega) hLk)
  -- facts about the level-`k` tree
  have hm2 : m + 1 ≤ m ^ 2 := by nlinarith
  have hsq : (m + 1) ^ (2 ^ k) ≤ m ^ (2 ^ (k + 1)) := by
    calc (m + 1) ^ (2 ^ k) ≤ (m ^ 2) ^ (2 ^ k) := Nat.pow_le_pow_left hm2 _
      _ = m ^ (2 ^ (k + 1)) := by rw [← pow_mul, pow_succ, mul_comm]
  have h4 : 4 ≤ 2 ^ k := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk2
  have hmem : ∀ n ∈ blockTree m k, A n := blockTree_mem hA hmA k
  have hbnd : ∀ n ∈ blockTree m k, m ^ (2 ^ k) ≤ n ∧ n < (m + 1) ^ (2 ^ k) := blockTree_bounds m k
  have hle_y : ∀ n ∈ blockTree m k, n ≤ y := fun n hn => le_trans (hbnd n hn).2.le hylo
  have hge_m4 : ∀ n ∈ blockTree m k, m ^ 4 ≤ n := fun n hn =>
    le_trans (Nat.pow_le_pow_right (by omega) h4) (hbnd n hn).1
  -- `n⁴ > y` on the tree: `n⁴ ≥ m^{2^{k+2}} = (m²)^{2^{k+1}} ≥ (m+1)^{2^{k+1}} > y`
  have hfourth : ∀ n ∈ blockTree m k, y < (n * n) ^ 2 := by
    intro n hn
    calc y < (m + 1) ^ (2 ^ (k + 1)) := hyhi
      _ ≤ (m ^ 2) ^ (2 ^ (k + 1)) := Nat.pow_le_pow_left hm2 _
      _ = (m ^ (2 ^ k)) ^ 4 := by
          rw [← pow_mul, ← pow_mul, pow_succ]
          ring_nf
      _ ≤ n ^ 4 := Nat.pow_le_pow_left (hbnd n hn).1 4
      _ = (n * n) ^ 2 := by ring
  -- the three pieces of the tree relative to `⌊√y⌋`
  set S := blockTree m k with hS
  set P₁ := {n ∈ S | y.sqrt < n} with hP₁
  set P₂ := {n ∈ S | n + 1 ≤ y.sqrt} with hP₂
  set P₃ := {n ∈ S | n = y.sqrt} with hP₃
  have hnn : ∀ n : ℕ, (0 : ℝ) ≤ 1 / n := fun n => by positivity
  -- `ℓ(S) = ℓ(P₁) + ℓ(P₂) + ℓ(P₃)`
  have hsplit : ∑ n ∈ S, (1 : ℝ) / n =
      ∑ n ∈ P₁, (1 : ℝ) / n + ∑ n ∈ P₂, (1 : ℝ) / n + ∑ n ∈ P₃, (1 : ℝ) / n := by
    rw [← sum_filter_add_sum_filter_not S (fun n => y.sqrt < n),
      ← sum_filter_add_sum_filter_not (S.filter (fun n => ¬y.sqrt < n)) (fun n => n + 1 ≤ y.sqrt),
      filter_filter, filter_filter, add_assoc]
    congr 2
    · apply sum_congr _ (fun _ _ => rfl)
      ext n
      simp only [hP₂, mem_filter]
      constructor
      · rintro ⟨h, -, h'⟩; exact ⟨h, h'⟩
      · rintro ⟨h, h'⟩; exact ⟨h, by omega, h'⟩
    · apply sum_congr _ (fun _ _ => rfl)
      ext n
      simp only [hP₃, mem_filter]
      constructor
      · rintro ⟨h, h1, h2⟩; exact ⟨h, by omega⟩
      · rintro ⟨h, h'⟩; exact ⟨h, by omega, by omega⟩
  -- `ℓ(P₃) ≤ 1/((m+1)² - 1)`
  have hP₃le : ∑ n ∈ P₃, (1 : ℝ) / n ≤ 1 / (((m : ℝ) + 1) ^ 2 - 1) := by
    have hsub : P₃ ⊆ {y.sqrt} := by
      intro n hn
      simp only [hP₃, mem_filter] at hn
      rw [mem_singleton]
      exact hn.2
    have hcard : P₃.card ≤ 1 := le_trans (card_le_card hsub) (by simp)
    have hterm : ∀ n ∈ P₃, (1 : ℝ) / n ≤ 1 / (((m : ℝ) + 1) ^ 2 - 1) := by
      intro n hn
      simp only [hP₃, mem_filter] at hn
      have h1 : m ^ 4 ≤ n := hge_m4 n hn.1
      have h2 : (m + 1) ^ 2 - 1 ≤ m ^ 4 := by
        have : (m + 1) ^ 2 ≤ m ^ 4 + 1 := by nlinarith
        omega
      have h3 : ((m : ℝ) + 1) ^ 2 - 1 ≤ n := by
        have : (((m + 1) ^ 2 - 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast le_trans h2 h1
        have h' : (((m + 1) ^ 2 - 1 : ℕ) : ℝ) = ((m : ℝ) + 1) ^ 2 - 1 := by
          rw [Nat.cast_sub (by nlinarith)]
          push_cast
          ring
        linarith
      exact one_div_le_one_div_of_le (by nlinarith) h3
    calc ∑ n ∈ P₃, (1 : ℝ) / n ≤ P₃.card • (1 / (((m : ℝ) + 1) ^ 2 - 1)) :=
          sum_le_card_nsmul _ _ _ hterm
      _ = P₃.card * (1 / (((m : ℝ) + 1) ^ 2 - 1)) := by rw [nsmul_eq_mul]
      _ ≤ 1 * (1 / (((m : ℝ) + 1) ^ 2 - 1)) := by
          have hpos : (0 : ℝ) < ((m : ℝ) + 1) ^ 2 - 1 := by nlinarith
          apply mul_le_mul_of_nonneg_right _ (div_nonneg zero_le_one hpos.le)
          exact_mod_cast hcard
      _ = _ := one_mul _
  -- `P₁ ⊆ (√y, y] ∩ A`
  have hP₁sub : P₁ ⊆ {n ∈ Ioc y.sqrt y | A n} := by
    intro n hn
    simp only [hP₁, mem_filter] at hn
    simp only [mem_filter, mem_Ioc]
    exact ⟨⟨hn.2, hle_y n hn.1⟩, hmem n hn.1⟩
  -- `E(P₂) ⊆ (√y, y] ∩ A`
  have hEP₂sub : P₂.biUnion evenBlock ⊆ {n ∈ Ioc y.sqrt y | A n} := by
    intro n hn
    rw [mem_biUnion] at hn
    obtain ⟨m'', hm'', hn⟩ := hn
    simp only [hP₂, mem_filter] at hm''
    simp only [evenBlock, mem_filter, mem_Ico] at hn
    simp only [mem_filter, mem_Ioc]
    refine ⟨⟨?_, ?_⟩, even_block_mem hA (hmem m'' hm''.1) hn.2 hn.1.1 hn.1.2⟩
    · -- `⌊√y⌋ < m''² ≤ n` from `y < (m''²)²`
      have : y.sqrt < m'' * m'' := Nat.sqrt_lt'.mpr (hfourth m'' hm''.1)
      omega
    · -- `n < (m''+1)² ≤ ⌊√y⌋² ≤ y`
      calc n ≤ (m'' + 1) * (m'' + 1) := hn.1.2.le
        _ ≤ y.sqrt * y.sqrt := Nat.mul_le_mul hm''.2 hm''.2
        _ ≤ y := Nat.sqrt_le y
  -- `P₁` and `E(P₂)` are disjoint: `P₁ < (m+1)^{2^k} ≤ m^{2^{k+1}} ≤ E(P₂)`
  have hdisj : Disjoint P₁ (P₂.biUnion evenBlock) := by
    rw [Finset.disjoint_left]
    intro n h1 h2
    simp only [hP₁, mem_filter] at h1
    rw [mem_biUnion] at h2
    obtain ⟨m'', hm'', h2⟩ := h2
    simp only [hP₂, mem_filter] at hm''
    simp only [evenBlock, mem_filter, mem_Ico] at h2
    have hlt : n < (m + 1) ^ (2 ^ k) := (hbnd n h1.1).2
    have hge : m ^ (2 ^ (k + 1)) ≤ n := by
      calc m ^ (2 ^ (k + 1)) = (m ^ (2 ^ k)) ^ 2 := by rw [pow_succ, pow_mul]
        _ ≤ m'' ^ 2 := Nat.pow_le_pow_left (hbnd m'' hm''.1).1 2
        _ = m'' * m'' := by ring
        _ ≤ n := h2.1.1
    omega
  -- `ℓ(E(P₂)) ≥ (1 - 2/m⁴) ℓ(P₂)`
  have h81 : (81 : ℝ) ≤ (m : ℝ) ^ 4 := by
    have := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 3) hmR 4
    norm_num at this
    linarith
  have hm4 : (0 : ℝ) < 1 - 2 / (m : ℝ) ^ 4 := by
    have : (2 : ℝ) / (m : ℝ) ^ 4 ≤ 2 / 81 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      linarith
    linarith
  have hEP₂ : (1 - 2 / (m : ℝ) ^ 4) * ∑ n ∈ P₂, (1 : ℝ) / n ≤
      ∑ n ∈ P₂.biUnion evenBlock, (1 : ℝ) / n := by
    rw [sum_biUnion (evenBlock_pairwiseDisjoint _), mul_sum]
    apply sum_le_sum
    intro m'' hm''
    simp only [hP₂, mem_filter] at hm''
    have h1 : m ^ 4 ≤ m'' := hge_m4 m'' hm''.1
    have hm''1 : 1 ≤ m'' := le_trans (by nlinarith) h1
    have hm''R : (0 : ℝ) < m'' := by exact_mod_cast hm''1
    have hinv : (1 : ℝ) / m'' ≤ 1 / (m : ℝ) ^ 4 := by
      apply one_div_le_one_div_of_le (by positivity)
      exact_mod_cast h1
    calc (1 - 2 / (m : ℝ) ^ 4) * (1 / m'') ≤ (1 - 2 / (m'' : ℝ)) * (1 / m'') := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          have : (2 : ℝ) / m'' = 2 * (1 / m'') := by ring
          have : (2 : ℝ) / (m : ℝ) ^ 4 = 2 * (1 / (m : ℝ) ^ 4) := by ring
          linarith
      _ ≤ ∑ n ∈ evenBlock m'', (1 : ℝ) / n := evenBlock_logMass_ge' hm''1
  -- assemble
  have hP₁0 : 0 ≤ ∑ n ∈ P₁, (1 : ℝ) / n := sum_nonneg fun n _ => hnn n
  have hS0 : 3 / 8 / ((m : ℝ) + 1) ≤ ∑ n ∈ S, (1 : ℝ) / n := by
    obtain ⟨k', hk'⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    rw [hS, hk']
    exact blockTree_logMass_ge hm k'
  have hunion : ∑ n ∈ P₁, (1 : ℝ) / n + ∑ n ∈ P₂.biUnion evenBlock, (1 : ℝ) / n ≤
      halfLogMass A y := by
    rw [← sum_union hdisj]
    exact sum_le_sum_of_subset_of_nonneg (union_subset hP₁sub hEP₂sub) (fun n _ _ => hnn n)
  have hm4' : 1 - 2 / (m : ℝ) ^ 4 ≤ 1 := by
    have : (0 : ℝ) ≤ 2 / (m : ℝ) ^ 4 := by positivity
    linarith
  calc (1 - 2 / (m : ℝ) ^ 4) * (3 / 8 / ((m : ℝ) + 1) - 1 / (((m : ℝ) + 1) ^ 2 - 1))
      ≤ (1 - 2 / (m : ℝ) ^ 4) * (∑ n ∈ S, (1 : ℝ) / n - ∑ n ∈ P₃, (1 : ℝ) / n) := by
        apply mul_le_mul_of_nonneg_left _ hm4.le
        linarith
    _ = (1 - 2 / (m : ℝ) ^ 4) * (∑ n ∈ P₁, (1 : ℝ) / n + ∑ n ∈ P₂, (1 : ℝ) / n) := by
        rw [hsplit]
        ring
    _ ≤ ∑ n ∈ P₁, (1 : ℝ) / n + (1 - 2 / (m : ℝ) ^ 4) * ∑ n ∈ P₂, (1 : ℝ) / n := by
        nlinarith
    _ ≤ ∑ n ∈ P₁, (1 : ℝ) / n + ∑ n ∈ P₂.biUnion evenBlock, (1 : ℝ) / n := by linarith
    _ ≤ halfLogMass A y := hunion

/-- The seed constant is positive for `m ≥ 3`, so the seed is a usable `c₀ > 0` for
`recursion_lemma`. -/
theorem seed_constant_pos {m : ℕ} (hm : 3 ≤ m) :
    0 < (1 - 2 / (m : ℝ) ^ 4) * (3 / 8 / ((m : ℝ) + 1) - 1 / (((m : ℝ) + 1) ^ 2 - 1)) := by
  have hmR : (3 : ℝ) ≤ m := by exact_mod_cast hm
  have h81 : (81 : ℝ) ≤ (m : ℝ) ^ 4 := by
    have := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 3) hmR 4
    norm_num at this
    linarith
  have h1 : (0 : ℝ) < 1 - 2 / (m : ℝ) ^ 4 := by
    have : (2 : ℝ) / (m : ℝ) ^ 4 ≤ 2 / 81 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      linarith
    linarith
  have h2 : (0 : ℝ) < 3 / 8 / ((m : ℝ) + 1) - 1 / (((m : ℝ) + 1) ^ 2 - 1) := by
    have hpos : (0 : ℝ) < ((m : ℝ) + 1) ^ 2 - 1 := by nlinarith
    rw [sub_pos, div_lt_div_iff₀ hpos (by positivity)]
    nlinarith
  exact mul_pos h1 h2

end Problems.Juggler
