import Mathlib.Analysis.Complex.ExponentialBounds
import Problems.Juggler.FatePoorProduction

namespace Problems.Juggler

open Finset
open scoped Classical

namespace Density

/-!
# Corollary 5.4 and the density clauses of Corollary 5.5

Paper C, Corollary 5.4 (natural density, infinitely often): if the shell log-mass
`g_A(t) = Σ_{√x < n ≤ x, n ∈ A} 1/n`, `x = e^t`, is at least `K t^λ` for all large `t`, then for
every large `X` some dyadic block `(y/2, y]` with `√X < y ≤ X` carries at least
`(K/12) y (log y)^{λ-1}` members of `A`. The proof is the manuscript's pigeonhole: the shell
`(√X, X]` is covered by the blocks `(X/2^{j+1}, X/2^j]` with `j ≤ log₂ X`, at most `3 log X`
of them; a block's log-mass is at most `2 #(A ∩ block)/y`; the best block is at least the
average; and `log X < 2 log y` on the shell turns `(log X)^{λ-1}` into `(log y)^{λ-1}`.

The block `(y/2, y]` is `Ioc (y / 2) y` in the natural numbers, which is the paper's block
when `y` is even and `(⌊y/2⌋, y]` otherwise; its count is `blockCount A y`.

Composed with `Production.contagion_averaged` this is Corollary 5.4 for every
`0 < λ ≤ 100/203` with no hypothesis (`natDensity_averaged`), and instantiated at the fate
classes it is Corollary 5.5, each clause in its log-mass form and its dyadic-block form: the
reach-one class (`reachesOne_backwardClosed`, which contains `1`), the failures
(`not_reachesOne_backwardClosed`, nonempty if some start fails), the basin of a state `m`
(`ancestor_backwardClosed`, which contains `m`; the paper's clause is the case of a cycle
state) and the divergent starts (`escapes_backwardClosed`, nonempty if some orbit diverges).

Not a halt theorem: nothing here decides a fate, and the constants are those of
`contagion_averaged`.
-/

/-- `#(A ∩ (y/2, y])`, the count on the dyadic block of Corollary 5.4. -/
noncomputable def blockCount (A : ℕ → Prop) (y : ℕ) : ℕ :=
  ({n ∈ Ioc (y / 2) y | A n}).card

/-! ### One block: log-mass against count -/

/-- A block's log-mass is at most `2 #(A ∩ (y/2, y]) / y`, because every member exceeds
`y/2`. -/
theorem block_logMass_le (A : ℕ → Prop) {y : ℕ} (hy : 1 ≤ y) :
    ∑ n ∈ {n ∈ Ioc (y / 2) y | A n}, (1 : ℝ) / n ≤ 2 * (blockCount A y : ℝ) / y := by
  have hy0 : (0 : ℝ) < y := by exact_mod_cast hy
  have hbound : ∀ n ∈ {n ∈ Ioc (y / 2) y | A n}, (1 : ℝ) / n ≤ 2 / y := by
    intro n hn
    rw [mem_filter, mem_Ioc] at hn
    obtain ⟨⟨h1, _⟩, _⟩ := hn
    have h2 : y < 2 * n := by omega
    have hyn : (y : ℝ) / 2 ≤ n := by
      have : (y : ℝ) ≤ 2 * n := by exact_mod_cast h2.le
      linarith
    calc (1 : ℝ) / n ≤ 1 / ((y : ℝ) / 2) := one_div_le_one_div_of_le (by positivity) hyn
      _ = 2 / y := one_div_div _ _
  calc ∑ n ∈ {n ∈ Ioc (y / 2) y | A n}, (1 : ℝ) / n
      ≤ ({n ∈ Ioc (y / 2) y | A n}).card • (2 / (y : ℝ)) := sum_le_card_nsmul _ _ _ hbound
    _ = 2 * (blockCount A y : ℝ) / y := by
        simp only [nsmul_eq_mul, blockCount]; ring

/-! ### The dyadic cover of the shell -/

/-- Every `1 ≤ n ≤ X` lies in the block `(X/2^{j+1}, X/2^j]` with `j = ⌊log₂(X/n)⌋`. -/
theorem block_index {n X : ℕ} (hn : 1 ≤ n) (hnX : n ≤ X) :
    X / 2 ^ (Nat.log 2 (X / n) + 1) < n ∧ n ≤ X / 2 ^ Nat.log 2 (X / n) := by
  have hq : 0 < X / n := Nat.div_pos hnX hn
  have h1 : 2 ^ Nat.log 2 (X / n) ≤ X / n := Nat.pow_log_le_self 2 hq.ne'
  have h2 : X / n < 2 ^ (Nat.log 2 (X / n) + 1) := Nat.lt_pow_succ_log_self (by norm_num) _
  constructor
  · rw [Nat.div_lt_iff_lt_mul (by positivity)]
    calc X < X / n * n + n := Nat.lt_div_mul_add hn
      _ = (X / n + 1) * n := by ring
      _ ≤ 2 ^ (Nat.log 2 (X / n) + 1) * n := Nat.mul_le_mul_right _ h2
      _ = n * 2 ^ (Nat.log 2 (X / n) + 1) := Nat.mul_comm _ _
  · rw [Nat.le_div_iff_mul_le (by positivity)]
    calc n * 2 ^ Nat.log 2 (X / n) ≤ n * (X / n) := Nat.mul_le_mul_left _ h1
      _ ≤ X := Nat.mul_div_le X n

/-- The shell `(√X, X]` is covered by the blocks `(X/2^{j+1}, X/2^j]`, `j < J`, that reach
above `√X`, whenever `X < 2^J`; so its log-mass is at most the sum of their log-masses. -/
theorem halfLogMass_le_blocks (A : ℕ → Prop) {X J : ℕ} (hJ : X < 2 ^ J) :
    halfLogMass A X ≤ ∑ j ∈ {j ∈ range J | X.sqrt < X / 2 ^ j},
      ∑ n ∈ {n ∈ Ioc (X / 2 ^ j / 2) (X / 2 ^ j) | A n}, (1 : ℝ) / n := by
  unfold halfLogMass
  have hmaps : ∀ n ∈ {n ∈ Ioc X.sqrt X | A n},
      Nat.log 2 (X / n) ∈ {j ∈ range J | X.sqrt < X / 2 ^ j} := by
    intro n hn
    rw [mem_filter, mem_Ioc] at hn
    obtain ⟨⟨hsn, hnX⟩, _⟩ := hn
    have hn1 : 1 ≤ n := by omega
    obtain ⟨_, hle⟩ := block_index hn1 hnX
    rw [mem_filter, mem_range]
    refine ⟨?_, lt_of_lt_of_le hsn hle⟩
    have hq : 0 < X / n := Nat.div_pos hnX hn1
    have h1 : 2 ^ Nat.log 2 (X / n) ≤ X / n := Nat.pow_log_le_self 2 hq.ne'
    have h2 : 2 ^ Nat.log 2 (X / n) < 2 ^ J :=
      lt_of_le_of_lt h1 (lt_of_le_of_lt (Nat.div_le_self X n) hJ)
    exact Nat.lt_of_not_le fun hnot =>
      absurd h2 (not_lt.mpr (Nat.pow_le_pow_right (by norm_num) hnot))
  rw [← sum_fiberwise_of_maps_to hmaps]
  apply sum_le_sum
  intro j _
  apply sum_le_sum_of_subset_of_nonneg
  · intro n hn
    rw [mem_filter] at hn
    obtain ⟨hnS, hjn⟩ := hn
    rw [mem_filter, mem_Ioc] at hnS
    obtain ⟨⟨hsn, hnX⟩, hAn⟩ := hnS
    have hn1 : 1 ≤ n := by omega
    obtain ⟨hlt, hle⟩ := block_index hn1 hnX
    rw [mem_filter, mem_Ioc]
    refine ⟨⟨?_, ?_⟩, hAn⟩
    · rw [Nat.div_div_eq_div_mul, ← pow_succ, ← hjn]
      exact hlt
    · rw [← hjn]
      exact hle
  · intro n _ _
    positivity

/-! ### The pigeonhole -/

/-- **Paper C Corollary 5.4, the pigeonhole.** If the shell log-mass of `A` at `X ≥ 3` is at
least `K (log X)^λ` with `0 < λ ≤ 1`, then some block `(y/2, y]` with `√X < y ≤ X` holds at
least `(K/12) y (log y)^{λ-1}` members of `A`. -/
theorem exists_block_of_shell (A : ℕ → Prop) {K lam : ℝ} (hK : 0 < K) (hlam0 : 0 < lam)
    (hlam1 : lam ≤ 1) {X : ℕ} (hX : 3 ≤ X)
    (h : K * Real.log X ^ lam ≤ halfLogMass A X) :
    ∃ y : ℕ, X.sqrt < y ∧ y ≤ X ∧
      K / 12 * y * Real.log y ^ (lam - 1) ≤ (blockCount A y : ℝ) := by
  have hX0 : (0 : ℝ) < X := by exact_mod_cast (show 0 < X by omega)
  have hX3 : (3 : ℝ) ≤ X := by exact_mod_cast hX
  set t := Real.log X with ht
  have ht1 : 1 < t := by
    have h3 : (1 : ℝ) < Real.log 3 := by
      rw [Real.lt_log_iff_exp_lt (by norm_num)]
      exact Real.exp_one_lt_three
    have := Real.log_le_log (by norm_num : (0 : ℝ) < 3) hX3
    linarith
  have ht0 : 0 < t := by linarith
  -- the number of blocks
  set J := Nat.log 2 X + 1 with hJ
  have hXJ : X < 2 ^ J := Nat.lt_pow_succ_log_self (by norm_num) X
  have hJpos : (0 : ℝ) < J := by rw [hJ]; positivity
  have hJt : (J : ℝ) ≤ 3 * t := by
    have hpow : 2 ^ Nat.log 2 X ≤ X := Nat.pow_log_le_self 2 (by omega)
    have h1 : Real.log ((2 : ℝ) ^ Nat.log 2 X) ≤ Real.log X :=
      Real.log_le_log (by positivity) (by exact_mod_cast hpow)
    rw [Real.log_pow, ← ht] at h1
    have hlog2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
    have hL0 : (0 : ℝ) ≤ Nat.log 2 X := by positivity
    have hhalf : (Nat.log 2 X : ℝ) * (1 / 2) ≤ (Nat.log 2 X : ℝ) * Real.log 2 :=
      mul_le_mul_of_nonneg_left (by linarith) hL0
    rw [hJ]
    push_cast
    linarith
  -- the blocks, the cover, and the count on each block
  set F := {j ∈ range J | X.sqrt < X / 2 ^ j} with hF
  have hcover := halfLogMass_le_blocks A hXJ
  have hblocks : ∑ j ∈ F, ∑ n ∈ {n ∈ Ioc (X / 2 ^ j / 2) (X / 2 ^ j) | A n}, (1 : ℝ) / n
      ≤ ∑ j ∈ F, 2 * (blockCount A (X / 2 ^ j) : ℝ) / (X / 2 ^ j : ℕ) := by
    apply sum_le_sum
    intro j hj
    rw [hF, mem_filter] at hj
    exact block_logMass_le A (by omega)
  have hFne : F.Nonempty := by
    refine ⟨0, ?_⟩
    rw [hF, mem_filter, mem_range]
    refine ⟨by omega, ?_⟩
    simpa using Nat.sqrt_lt_self (by omega : 1 < X)
  have hcard : (F.card : ℝ) ≤ J := by
    have : F.card ≤ J := by
      rw [hF]
      exact (card_filter_le _ _).trans (card_range J).le
    exact_mod_cast this
  have hJne : (J : ℝ) ≠ 0 := hJpos.ne'
  have hsum : ∑ _j ∈ F, K * t ^ lam / J
      ≤ ∑ j ∈ F, 2 * (blockCount A (X / 2 ^ j) : ℝ) / (X / 2 ^ j : ℕ) := by
    rw [sum_const, nsmul_eq_mul]
    calc (F.card : ℝ) * (K * t ^ lam / J) ≤ J * (K * t ^ lam / J) :=
          mul_le_mul_of_nonneg_right hcard (by positivity)
      _ = K * t ^ lam := by field_simp
      _ ≤ halfLogMass A X := h
      _ ≤ _ := hcover.trans hblocks
  obtain ⟨j, hjF, hj⟩ := exists_le_of_sum_le hFne hsum
  rw [hF, mem_filter, mem_range] at hjF
  obtain ⟨_, hsy⟩ := hjF
  -- the block found
  refine ⟨X / 2 ^ j, hsy, Nat.div_le_self X _, ?_⟩
  set y := X / 2 ^ j with hy
  have hy1 : 1 ≤ y := by omega
  have hY0 : (0 : ℝ) < y := by exact_mod_cast hy1
  have hB0 : (0 : ℝ) ≤ (blockCount A y : ℝ) := by positivity
  -- `y² > X`, so `log y > t/2`
  have hXy : X < y ^ 2 :=
    lt_of_lt_of_le (Nat.lt_succ_sqrt' X) (Nat.pow_le_pow_left hsy 2)
  have hlogy : t / 2 < Real.log y := by
    have h1 : (X : ℝ) < (y : ℝ) ^ 2 := by exact_mod_cast hXy
    have h2 := Real.log_lt_log hX0 h1
    rw [Real.log_pow, ← ht] at h2
    push_cast at h2
    linarith
  have hly0 : 0 < Real.log y := by linarith
  -- `(log y)^{λ-1} ≤ 2 t^{λ-1}`
  have hQ : t ^ (lam - 1) = t ^ lam / t := Real.rpow_sub_one ht0.ne' lam
  have hQ0 : 0 ≤ t ^ (lam - 1) := by positivity
  have hL : Real.log y ^ (lam - 1) ≤ 2 * t ^ (lam - 1) := by
    have h1 : Real.log y ^ (lam - 1) ≤ (t / 2) ^ (lam - 1) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) hlogy.le (by linarith)
    have h2 : (t / 2) ^ (lam - 1) = t ^ (lam - 1) / (2 : ℝ) ^ (lam - 1) :=
      Real.div_rpow ht0.le (by norm_num) _
    have h3 : (2 : ℝ) ^ (-1 : ℝ) ≤ (2 : ℝ) ^ (lam - 1) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    rw [Real.rpow_neg_one] at h3
    have h4 : t ^ (lam - 1) / (2 : ℝ) ^ (lam - 1) ≤ t ^ (lam - 1) / (2 : ℝ)⁻¹ :=
      div_le_div_of_nonneg_left hQ0 (by norm_num) h3
    have h5 : t ^ (lam - 1) / (2 : ℝ)⁻¹ = 2 * t ^ (lam - 1) := by ring
    linarith [h1, h2 ▸ h4, h5]
  -- unwind the pigeonhole inequality
  have hP0 : 0 < t ^ lam := by positivity
  rw [div_le_iff₀ hJpos] at hj
  have h1 : K * t ^ lam * y ≤ 2 * (blockCount A y : ℝ) * J := by
    have := mul_le_mul_of_nonneg_right hj hY0.le
    calc K * t ^ lam * y ≤ 2 * (blockCount A y : ℝ) / y * J * y := this
      _ = 2 * (blockCount A y : ℝ) * J := by field_simp
  have h2 : K * t ^ lam * y ≤ 6 * (blockCount A y : ℝ) * t := by
    have := mul_le_mul_of_nonneg_left hJt (by positivity : (0 : ℝ) ≤ 2 * (blockCount A y : ℝ))
    linarith
  have h3 : K * t ^ (lam - 1) * y ≤ 6 * (blockCount A y : ℝ) := by
    have hPQ : t ^ lam = t ^ (lam - 1) * t := by rw [hQ]; field_simp
    rw [hPQ] at h2
    have h6 : (K * t ^ (lam - 1) * y) * t ≤ (6 * (blockCount A y : ℝ)) * t := by linarith
    exact le_of_mul_le_mul_right h6 ht0
  calc K / 12 * y * Real.log y ^ (lam - 1) ≤ K / 12 * y * (2 * t ^ (lam - 1)) := by gcongr
    _ = K * t ^ (lam - 1) * y / 6 := by ring
    _ ≤ (blockCount A y : ℝ) := by linarith

/-! ### Corollary 5.4 -/

/-- **Paper C Corollary 5.4 (natural density, infinitely often), from a shell bound.** If
`g_A(t) ≥ K t^λ` for all `t ≥ t₁`, with `0 < λ ≤ 1`, then there is `c > 0` such that for every
large `X` some `y` with `√X < y ≤ X` has `#(A ∩ (y/2, y]) ≥ c y (log y)^{λ-1}`; the blocks
found are distinct for `X` running through powers of `4`, so there are infinitely many. -/
theorem natDensity_of_shell_bound (A : ℕ → Prop) {K lam t₁ : ℝ} (hK : 0 < K)
    (hlam0 : 0 < lam) (hlam1 : lam ≤ 1) (h : ∀ t, t₁ ≤ t → K * t ^ lam ≤ gA A t) :
    ∃ c : ℝ, 0 < c ∧ ∃ X₀ : ℕ, ∀ X, X₀ ≤ X → ∃ y : ℕ, X.sqrt < y ∧ y ≤ X ∧
      c * y * Real.log y ^ (lam - 1) ≤ (blockCount A y : ℝ) := by
  refine ⟨K / 12, by positivity, ⌈Real.exp t₁⌉₊ + 3, fun X hX => ?_⟩
  have hX3 : 3 ≤ X := by omega
  have hXpos : (0 : ℝ) < X := by exact_mod_cast (show 0 < X by omega)
  have hlog : t₁ ≤ Real.log X := by
    rw [Real.le_log_iff_exp_le hXpos]
    have h1 := Nat.le_ceil (Real.exp t₁)
    have h2 : ((⌈Real.exp t₁⌉₊ + 3 : ℕ) : ℝ) ≤ X := by exact_mod_cast hX
    push_cast at h2
    linarith
  have hg := h _ hlog
  have hhalf : K * Real.log X ^ lam ≤ halfLogMass A X := by
    have : gA A (Real.log X) = halfLogMass A X := by
      unfold gA
      rw [Real.exp_log hXpos, Nat.floor_natCast]
    rwa [this] at hg
  exact exists_block_of_shell A hK hlam0 hlam1 hX3 hhalf

/-- **Paper C Corollary 5.4 for every `0 < λ ≤ 100/203`, with no hypothesis.** For every
nonempty backward-closed `A`, on a dyadic block inside every shell `(√X, X]` with `X` large,
`A` has natural density at least `c (log y)^{λ-1}`. Theorem 5.18 (`contagion_averaged`)
supplies the shell bound. -/
theorem natDensity_averaged {A : ℕ → Prop} (hA : BackwardClosed A) {a : ℕ} (ha : 1 ≤ a)
    (hAa : A a) {lam : ℝ} (hlam0 : 0 < lam) (hlam : lam ≤ 100 / 203) :
    ∃ c : ℝ, 0 < c ∧ ∃ X₀ : ℕ, ∀ X, X₀ ≤ X → ∃ y : ℕ, X.sqrt < y ∧ y ≤ X ∧
      c * y * Real.log y ^ (lam - 1) ≤ (blockCount A y : ℝ) := by
  obtain ⟨K, hK, t₁, -, h⟩ := Production.contagion_averaged hA ha hAa (η₀ := 1 / 100000)
    (by norm_num) (by norm_num) hlam0
    (lt_of_lt_of_le Production.zeta2avg_pos (Production.zeta2avg_antitone (by norm_num) hlam))
  exact natDensity_of_shell_bound A hK hlam0 (by linarith) h

/-! ### Corollary 5.5: the fate classes -/

/-- **Corollary 5.5(1), log-mass form.** The reach-one class `R` is backward-closed and
contains `1`, so `Σ_{n ∈ R, n ≤ x} 1/n ≥ K (log x)^λ` for every `0 < λ ≤ 100/203`. -/
theorem reachesOne_logMass_averaged {lam : ℝ} (hlam0 : 0 < lam) (hlam : lam ≤ 100 / 203) :
    ∃ K : ℝ, 0 < K ∧ ∃ x₀ : ℕ, ∀ x : ℕ, x₀ ≤ x →
      K * Real.log x ^ lam ≤ logMass ReachesOne x :=
  Production.logMass_contagion_averaged reachesOne_backwardClosed le_rfl reachesOne_one
    hlam0 hlam

/-- **Corollary 5.5(1), dyadic-block form.** -/
theorem reachesOne_natDensity_averaged {lam : ℝ} (hlam0 : 0 < lam)
    (hlam : lam ≤ 100 / 203) :
    ∃ c : ℝ, 0 < c ∧ ∃ X₀ : ℕ, ∀ X, X₀ ≤ X → ∃ y : ℕ, X.sqrt < y ∧ y ≤ X ∧
      c * y * Real.log y ^ (lam - 1) ≤ (blockCount ReachesOne y : ℝ) :=
  natDensity_averaged reachesOne_backwardClosed le_rfl reachesOne_one hlam0 hlam

/-- **Corollary 5.5(2), dyadic-block form.** If some start `a` does not reach `1`, the failures
have natural density at least `c (log y)^{λ-1}` on a dyadic block inside every large shell;
the log-mass form is `Production.failures_logMass_averaged`. -/
theorem failures_natDensity_averaged {a : ℕ} (ha : 1 ≤ a) (hfail : ¬ReachesOne a) {lam : ℝ}
    (hlam0 : 0 < lam) (hlam : lam ≤ 100 / 203) :
    ∃ c : ℝ, 0 < c ∧ ∃ X₀ : ℕ, ∀ X, X₀ ≤ X → ∃ y : ℕ, X.sqrt < y ∧ y ≤ X ∧
      c * y * Real.log y ^ (lam - 1) ≤ (blockCount (fun n => ¬ReachesOne n) y : ℝ) :=
  natDensity_averaged not_reachesOne_backwardClosed ha hfail hlam0 hlam

/-- **Corollary 5.5(3) for a cycle, log-mass form.** The basin of a state `m ≥ 1`, the starts
whose orbit passes through `m`, is backward-closed and contains `m`; for a periodic `m` it is
the basin of that cycle. -/
theorem basin_logMass_averaged {m : ℕ} (hm : 1 ≤ m) {lam : ℝ} (hlam0 : 0 < lam)
    (hlam : lam ≤ 100 / 203) :
    ∃ K : ℝ, 0 < K ∧ ∃ x₀ : ℕ, ∀ x : ℕ, x₀ ≤ x →
      K * Real.log x ^ lam ≤ logMass (fun n => Ancestor n m) x :=
  Production.logMass_contagion_averaged (ancestor_backwardClosed m) hm (ancestor_refl m)
    hlam0 hlam

/-- **Corollary 5.5(3) for a cycle, dyadic-block form.** -/
theorem basin_natDensity_averaged {m : ℕ} (hm : 1 ≤ m) {lam : ℝ} (hlam0 : 0 < lam)
    (hlam : lam ≤ 100 / 203) :
    ∃ c : ℝ, 0 < c ∧ ∃ X₀ : ℕ, ∀ X, X₀ ≤ X → ∃ y : ℕ, X.sqrt < y ∧ y ≤ X ∧
      c * y * Real.log y ^ (lam - 1) ≤ (blockCount (fun n => Ancestor n m) y : ℝ) :=
  natDensity_averaged (ancestor_backwardClosed m) hm (ancestor_refl m) hlam0 hlam

/-- **Corollary 5.5(3) for divergence, log-mass form.** If some orbit diverges, the divergent
starts carry log-mass at least `K (log x)^λ`. -/
theorem escapes_logMass_averaged {a : ℕ} (ha : 1 ≤ a) (hesc : EscapesToInfinity a) {lam : ℝ}
    (hlam0 : 0 < lam) (hlam : lam ≤ 100 / 203) :
    ∃ K : ℝ, 0 < K ∧ ∃ x₀ : ℕ, ∀ x : ℕ, x₀ ≤ x →
      K * Real.log x ^ lam ≤ logMass EscapesToInfinity x :=
  Production.logMass_contagion_averaged escapes_backwardClosed ha hesc hlam0 hlam

/-- **Corollary 5.5(3) for divergence, dyadic-block form.** -/
theorem escapes_natDensity_averaged {a : ℕ} (ha : 1 ≤ a) (hesc : EscapesToInfinity a)
    {lam : ℝ} (hlam0 : 0 < lam) (hlam : lam ≤ 100 / 203) :
    ∃ c : ℝ, 0 < c ∧ ∃ X₀ : ℕ, ∀ X, X₀ ≤ X → ∃ y : ℕ, X.sqrt < y ∧ y ≤ X ∧
      c * y * Real.log y ^ (lam - 1) ≤ (blockCount EscapesToInfinity y : ℝ) :=
  natDensity_averaged escapes_backwardClosed ha hesc hlam0 hlam

end Density

end Problems.Juggler
