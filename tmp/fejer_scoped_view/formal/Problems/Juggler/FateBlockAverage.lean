import Mathlib.Analysis.Complex.ExponentialBounds
import Problems.Juggler.FateFiberParity
import Problems.Juggler.FateLandingWindow

namespace Problems.Juggler

open Finset

/-!
# The block average: Proposition 4.4 given its exponential-sum bounds

Paper C (`docs/theory/juggler_fate_almost_all_note.md`), Proposition 4.4. Over an even block
the even-image fraction of the fibers averages to `1/2`, so that the set

`U(m') = {n odd in I(m') : ⌊n^{3/4}⌋ even and ⌊n^{3/2}⌋ even}`

has `|U(m')|` within `C_B m'^{11/9} log(m'+1)` of a quarter of the odd integers of the block
(equation (4.1)). The paper's proof is analytic: Vaaler's interval approximation to the parity
wave, the second-derivative test and Kusmin--Landau on the resulting exponential sums.

**None of that analysis is formalized, and this file does not prove Proposition 4.4.** What is
here is the exact layer, and the deduction of (4.1) from the analytic bounds taken as
hypotheses, in the manner of Theorem 5.3 given the production inequality:

* the paper's `I(m')` is exact — the odd `n` with `m'² ≤ ⌊n^{3/4}⌋ < (m'+1)²` are exactly
  the odd `n` of `[⌈m'^{8/3}⌉, ⌈(m'+1)^{8/3}⌉)`, by the landing window of Appendix D.1
  (`mem_oddBlock`, on `LandingWindow.exact_endpoints`);
* `U(m')` is the disjoint union of the even-image parts of the fibers `Φ(m)` over the even
  `m` of the block, as the proposition states (`U_card_eq`, with `oddBlock_card_eq` the same
  statement for the whole block), so the block average is literally an average of the fiber
  counts of Lemma 4.2;
* expanding the two parity indicators gives the four sums the proof starts from, exactly:
  `4|U(m')| = M + S₁ + S₂ + S₁₂` (`four_card_U`), where `M` is the number of odd `n` in the
  block and the `S` are the parity sums;
* hence (4.1) holds as soon as the three parity sums obey the analytic bound
  (`block_average_of_bounds`, `block_average_bound`);
* **the slow sum needs no analysis.** `S₁` is an alternating sum of fiber sizes
  (`slowSum_eq_fibers`), consecutive fibers differ by at most two members
  (`oeFiber_card_succ_diff`, from the two-sided fiber bounds of Lemma 4.2's file), and the
  block pairs off into `m'` such differences plus one fiber, so
  `|S₁| ≤ 2m' + (2/3)(m'+1)^{2/3} + 1` (`slowSum_abs_le`) — the paper's "the slow sum is
  `O(m')`", proved. Equation (4.1) therefore holds with only the fast sum and the product sum
  as hypotheses (`block_average_two_bounds`, and `block_average_bound_two` in the paper's
  shape with `C_B = C/2 + 2`);
* the number `M` of odd integers of the block is pinned two-sidedly by the fiber bounds
  (`oddBlock_card_le`, `oddBlock_card_ge`), so `M/4` is within `m' + 1` of `m'^{5/3}/3`
  (`oddBlock_quarter_close`) and the proposition's asymptotic form holds with an explicit
  error, `|U(m')| = m'^{5/3}/3 ± (B/2 + 2(m'+1))`, given the two bounds
  (`block_average_asymptotic`).

The two hypotheses that remain — the fast sum `Σ ψ(n^{3/2})` and the product sum — are
exactly the exponential sums the paper estimates by Vaaler's approximation, the
second-derivative test and Kusmin--Landau. Mathlib does not carry these; until they are
formalized Proposition 4.4 is a human proof and the verification table says so. Nothing in
this file bounds a density, and nothing here is a halt theorem.
-/

namespace BlockAverage

open LandingWindow

/-! ### The block, its fibers, and the set `U(m')` -/

/-- The paper's `E(m')`: the even `m` with `m'² ≤ m < (m'+1)²`. -/
def blockE (m' : ℕ) : Finset ℕ := {m ∈ Finset.Ico (m' ^ 2) ((m' + 1) ^ 2) | m % 2 = 0}

/-- The odd integers of the paper's `I(m') = [m'^{8/3}, (m'+1)^{8/3})`, written exactly with
the landing window of Appendix D.1. -/
def oddBlock (m' : ℕ) : Finset ℕ :=
  {n ∈ Finset.Ico (windowStart (m' ^ 2)) (windowStart ((m' + 1) ^ 2)) | n % 2 = 1}

/-- Membership in the block is the exact condition `m'² ≤ ⌊n^{3/4}⌋ < (m'+1)²`. -/
theorem mem_oddBlock {m' n : ℕ} :
    n ∈ oddBlock m' ↔ n % 2 = 1 ∧ m' ^ 2 ≤ cell34 n ∧ cell34 n < (m' + 1) ^ 2 := by
  rw [oddBlock, Finset.mem_filter, Finset.mem_Ico]
  constructor
  · rintro ⟨h, hodd⟩
    exact ⟨hodd, exact_endpoints.mpr h⟩
  · rintro ⟨hodd, h⟩
    exact ⟨exact_endpoints.mp h, hodd⟩

/-- The fiber of `⌊n^{3/4}⌋` over `m`, among the odd integers, is the paper's `Φ(m)`. -/
theorem mem_oeFiber_iff_cell34 {m n : ℕ} :
    n ∈ FiberParity.oeFiber m ↔ n % 2 = 1 ∧ cell34 n = m := by
  rw [FiberParity.mem_oeFiber, cell34, sqrt_sqrt_eq_iff]

/-- `U(m')`: the odd `n` of the block whose two floors are both even. -/
def U (m' : ℕ) : Finset ℕ :=
  {n ∈ oddBlock m' | cell34 n % 2 = 0 ∧ (n ^ 3).sqrt % 2 = 0}

/-! ### The block is the disjoint union of its fibers -/

theorem oddBlock_card_eq (m' : ℕ) :
    (oddBlock m').card
      = ∑ m ∈ Finset.Ico (m' ^ 2) ((m' + 1) ^ 2), (FiberParity.oeFiber m).card := by
  classical
  have hmaps : ∀ n ∈ oddBlock m', cell34 n ∈ Finset.Ico (m' ^ 2) ((m' + 1) ^ 2) := by
    intro n hn
    rw [mem_oddBlock] at hn
    exact Finset.mem_Ico.mpr ⟨hn.2.1, hn.2.2⟩
  rw [Finset.card_eq_sum_card_fiberwise hmaps]
  refine Finset.sum_congr rfl fun m hm => ?_
  congr 1
  ext n
  rw [Finset.mem_filter, mem_oddBlock, mem_oeFiber_iff_cell34]
  rw [Finset.mem_Ico] at hm
  constructor
  · rintro ⟨⟨hodd, -, -⟩, hcell⟩
    exact ⟨hodd, hcell⟩
  · rintro ⟨hodd, hcell⟩
    exact ⟨⟨hodd, by omega, by omega⟩, hcell⟩

/-- **The proposition's first sentence, exactly.** `U(m')` is the disjoint union of the
even-image parts of the fibers `Φ(m)` over the even `m` of the block, so its size is the sum
of the even-image counts of Lemma 4.2. -/
theorem U_card_eq (m' : ℕ) :
    (U m').card = ∑ m ∈ blockE m', FiberParity.evenImageCount m := by
  classical
  have hmaps : ∀ n ∈ U m', cell34 n ∈ blockE m' := by
    intro n hn
    rw [U, Finset.mem_filter, mem_oddBlock] at hn
    exact Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨hn.1.2.1, hn.1.2.2⟩, hn.2.1⟩
  rw [Finset.card_eq_sum_card_fiberwise hmaps]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [FiberParity.evenImageCount]
  congr 1
  ext n
  rw [Finset.mem_filter, Finset.mem_filter, U, Finset.mem_filter, mem_oddBlock,
    mem_oeFiber_iff_cell34]
  rw [blockE, Finset.mem_filter, Finset.mem_Ico] at hm
  constructor
  · rintro ⟨⟨⟨hodd, -, -⟩, -, himg⟩, hcell⟩
    exact ⟨⟨hodd, hcell⟩, himg⟩
  · rintro ⟨⟨hodd, hcell⟩, himg⟩
    refine ⟨⟨⟨hodd, by omega, by omega⟩, ?_, himg⟩, hcell⟩
    rw [hcell]
    exact hm.2

/-! ### The four sums -/

/-- The parity wave `ψ(z) = (-1)^{⌊z⌋}`, at an integer floor value. -/
def psi (k : ℕ) : ℤ := if k % 2 = 0 then 1 else -1

/-- `Σ ψ(n^{3/4})`, the slow sum. -/
def slowSum (m' : ℕ) : ℤ := ∑ n ∈ oddBlock m', psi (cell34 n)

/-- `Σ ψ(n^{3/2})`, the fast sum. -/
def fastSum (m' : ℕ) : ℤ := ∑ n ∈ oddBlock m', psi ((n ^ 3).sqrt)

/-- `Σ ψ(n^{3/4}) ψ(n^{3/2})`, the product sum. -/
def productSum (m' : ℕ) : ℤ := ∑ n ∈ oddBlock m', psi (cell34 n) * psi ((n ^ 3).sqrt)

/-- **Expanding the two indicators**, exactly: `4|U(m')| = M + S₁ + S₂ + S₁₂`, where `M` is
the number of odd integers of the block. This is the identity the paper's proof starts from;
the three sums are what its exponential-sum estimates bound. -/
theorem four_card_U (m' : ℕ) :
    4 * ((U m').card : ℤ) = ((oddBlock m').card : ℤ) + slowSum m' + fastSum m' + productSum m' := by
  classical
  have key : ∀ n : ℕ, (1 + psi (cell34 n)) * (1 + psi ((n ^ 3).sqrt))
      = if cell34 n % 2 = 0 ∧ (n ^ 3).sqrt % 2 = 0 then 4 else 0 := by
    intro n
    unfold psi
    by_cases h1 : cell34 n % 2 = 0 <;> by_cases h2 : (n ^ 3).sqrt % 2 = 0 <;>
      simp [h1, h2]
  have hsum : ∑ n ∈ oddBlock m', (1 + psi (cell34 n)) * (1 + psi ((n ^ 3).sqrt))
      = 4 * ((U m').card : ℤ) := by
    rw [Finset.sum_congr rfl fun n _ => key n, ← Finset.sum_filter, ← U, Finset.sum_const,
      nsmul_eq_mul]
    ring
  rw [← hsum]
  have hexpand : ∀ n : ℕ, (1 + psi (cell34 n)) * (1 + psi ((n ^ 3).sqrt))
      = 1 + psi (cell34 n) + psi ((n ^ 3).sqrt) + psi (cell34 n) * psi ((n ^ 3).sqrt) := by
    intro n; ring
  rw [Finset.sum_congr rfl fun n _ => hexpand n]
  simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, mul_one]
  rfl

/-! ### Proposition 4.4 from the analytic bounds -/

/-- **Proposition 4.4, equation (4.1), given the exponential-sum bounds.** If each of the
three parity sums is at most `B` in absolute value, then `|U(m')|` is within `3B/4` of a
quarter of the odd integers of the block. Exact; the content of the proposition is that `B`
may be taken to be `C m'^{11/9} log(m'+1)`, which is the hypothesis, not the conclusion. -/
theorem block_average_of_bounds {m' : ℕ} {B : ℝ}
    (h₁ : |(slowSum m' : ℝ)| ≤ B) (h₂ : |(fastSum m' : ℝ)| ≤ B)
    (h₁₂ : |(productSum m' : ℝ)| ≤ B) :
    |((U m').card : ℝ) - ((oddBlock m').card : ℝ) / 4| ≤ 3 * B / 4 := by
  have hkey : (4 : ℝ) * ((U m').card : ℝ)
      = ((oddBlock m').card : ℝ) + (slowSum m' : ℝ) + (fastSum m' : ℝ) + (productSum m' : ℝ) := by
    exact_mod_cast congrArg (fun z : ℤ => (z : ℝ)) (four_card_U m')
  have hdiff : ((U m').card : ℝ) - ((oddBlock m').card : ℝ) / 4
      = ((slowSum m' : ℝ) + (fastSum m' : ℝ) + (productSum m' : ℝ)) / 4 := by linarith
  rw [hdiff, abs_div, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 4)]
  have htri : |(slowSum m' : ℝ) + (fastSum m' : ℝ) + (productSum m' : ℝ)| ≤ 3 * B := by
    calc |(slowSum m' : ℝ) + (fastSum m' : ℝ) + (productSum m' : ℝ)|
        ≤ |(slowSum m' : ℝ) + (fastSum m' : ℝ)| + |(productSum m' : ℝ)| := abs_add_le _ _
      _ ≤ |(slowSum m' : ℝ)| + |(fastSum m' : ℝ)| + |(productSum m' : ℝ)| := by
          have := abs_add_le (slowSum m' : ℝ) (fastSum m' : ℝ); linarith
      _ ≤ 3 * B := by linarith
  linarith

/-- Proposition 4.4 in the paper's shape: with each parity sum bounded by
`C m'^{11/9} log(m'+1)` — the analytic input, assumed here — equation (4.1) holds with
`C_B = 3C/4`. -/
theorem block_average_bound {m' : ℕ} {C : ℝ}
    (h₁ : |(slowSum m' : ℝ)| ≤ C * (m' : ℝ) ^ ((11 : ℝ) / 9) * Real.log (m' + 1))
    (h₂ : |(fastSum m' : ℝ)| ≤ C * (m' : ℝ) ^ ((11 : ℝ) / 9) * Real.log (m' + 1))
    (h₁₂ : |(productSum m' : ℝ)| ≤ C * (m' : ℝ) ^ ((11 : ℝ) / 9) * Real.log (m' + 1)) :
    |((U m').card : ℝ) - ((oddBlock m').card : ℝ) / 4|
      ≤ 3 / 4 * C * (m' : ℝ) ^ ((11 : ℝ) / 9) * Real.log (m' + 1) := by
  have := block_average_of_bounds h₁ h₂ h₁₂
  linarith

/-! ### The slow sum is an alternating sum of fiber sizes, hence `O(m')` -/

theorem psi_succ (m : ℕ) : psi (m + 1) = -psi m := by
  unfold psi
  rcases Nat.mod_two_eq_zero_or_one m with h | h
  · have h' : (m + 1) % 2 = 1 := by omega
    simp [h, h']
  · have h' : (m + 1) % 2 = 0 := by omega
    simp [h, h']

theorem abs_psi (m : ℕ) : |psi m| = 1 := by
  unfold psi
  split_ifs <;> simp

/-- Inside the block, the fiber of `⌊n^{3/4}⌋` over `m` is `Φ(m)`. -/
theorem oddBlock_filter_eq {m' m : ℕ} (hm : m ∈ Finset.Ico (m' ^ 2) ((m' + 1) ^ 2)) :
    {n ∈ oddBlock m' | cell34 n = m} = FiberParity.oeFiber m := by
  ext n
  rw [Finset.mem_filter, mem_oddBlock, mem_oeFiber_iff_cell34]
  rw [Finset.mem_Ico] at hm
  constructor
  · rintro ⟨⟨hodd, -, -⟩, hcell⟩
    exact ⟨hodd, hcell⟩
  · rintro ⟨hodd, hcell⟩
    exact ⟨⟨hodd, by omega, by omega⟩, hcell⟩

/-- **The slow sum, fiber by fiber.** `S₁ = Σ_{m'² ≤ m < (m'+1)²} ψ(m) |Φ(m)|`: the parity
of `⌊n^{3/4}⌋` is constant on a fiber, so the slow sum is an alternating sum of fiber sizes. -/
theorem slowSum_eq_fibers (m' : ℕ) :
    slowSum m' = ∑ m ∈ Finset.Ico (m' ^ 2) ((m' + 1) ^ 2),
      psi m * ((FiberParity.oeFiber m).card : ℤ) := by
  classical
  have hmaps : ∀ n ∈ oddBlock m', cell34 n ∈ Finset.Ico (m' ^ 2) ((m' + 1) ^ 2) := by
    intro n hn
    rw [mem_oddBlock] at hn
    exact Finset.mem_Ico.mpr ⟨hn.2.1, hn.2.2⟩
  rw [slowSum, ← Finset.sum_fiberwise_of_maps_to hmaps]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [Finset.sum_congr rfl (fun n hn => by rw [(Finset.mem_filter.mp hn).2]),
    Finset.sum_const, nsmul_eq_mul, oddBlock_filter_eq hm]
  ring

/-- Consecutive fibers differ by at most two members (`m ≥ 1`): the fiber bounds
`(2/3)m^{1/3} - 1 ≤ |Φ(m)| ≤ (2/3)(m+1)^{1/3} + 1` overlap, and
`(m+2)^{1/3} - m^{1/3} ≤ (2/3) m^{-2/3} ≤ 2/3` by Bernoulli. -/
theorem oeFiber_card_succ_diff {m : ℕ} (hm : 1 ≤ m) :
    |((FiberParity.oeFiber m).card : ℤ) - ((FiberParity.oeFiber (m + 1)).card : ℤ)| ≤ 2 := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hle := FiberParity.oeFiber_card_le m
  have hge := FiberParity.oeFiber_card_ge (m := m + 1) (by omega)
  have hle' := FiberParity.oeFiber_card_le (m + 1)
  have hge' := FiberParity.oeFiber_card_ge hm
  push_cast at hge hle'
  rw [show (m : ℝ) + 1 + 1 = m + 2 by ring] at hle'
  have hb := Numerics.bernoulli_le (a := (m : ℝ)) (h := 2) (p := (1 : ℝ) / 3)
    (q := -((2 : ℝ) / 3)) hm0 (by linarith) (by norm_num) (by norm_num) (by norm_num)
  have hv : (m : ℝ) ^ (-((2 : ℝ) / 3)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hm1 (by norm_num)
  have h1 : ((FiberParity.oeFiber m).card : ℝ) - (FiberParity.oeFiber (m + 1)).card ≤ 2 := by
    linarith
  have h2 : ((FiberParity.oeFiber (m + 1)).card : ℝ) - (FiberParity.oeFiber m).card < 3 := by
    linarith
  rw [abs_le]
  constructor
  · have : ((FiberParity.oeFiber (m + 1)).card : ℤ) - (FiberParity.oeFiber m).card < 3 := by
      exact_mod_cast h2
    omega
  · exact_mod_cast h1

/-- An alternating sum over `2k` consecutive terms whose neighbours differ by at most `d` is
at most `k d` in absolute value: each pair telescopes to one difference. -/
theorem abs_alt_sum_le (f : ℕ → ℤ) (a : ℕ) (d : ℤ)
    (hd : ∀ m, a ≤ m → |f m - f (m + 1)| ≤ d) :
    ∀ k : ℕ, |∑ m ∈ Finset.Ico a (a + 2 * k), psi m * f m| ≤ k * d := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
      have hpair : psi (a + 2 * k) * f (a + 2 * k) + psi (a + 2 * k + 1) * f (a + 2 * k + 1)
          = psi (a + 2 * k) * (f (a + 2 * k) - f (a + 2 * k + 1)) := by
        rw [psi_succ]; ring
      rw [show a + 2 * (k + 1) = a + 2 * k + 1 + 1 by ring,
        Finset.sum_Ico_succ_top (by omega), Finset.sum_Ico_succ_top (by omega), add_assoc,
        hpair]
      calc |(∑ m ∈ Finset.Ico a (a + 2 * k), psi m * f m)
              + psi (a + 2 * k) * (f (a + 2 * k) - f (a + 2 * k + 1))|
          ≤ |∑ m ∈ Finset.Ico a (a + 2 * k), psi m * f m|
              + |psi (a + 2 * k) * (f (a + 2 * k) - f (a + 2 * k + 1))| := abs_add_le _ _
        _ ≤ k * d + d := by
            rw [abs_mul, abs_psi, one_mul]
            exact add_le_add ih (hd _ (by omega))
        _ = ((k + 1 : ℕ) : ℤ) * d := by push_cast; ring

/-- **The slow sum is `O(m')`.** `|S₁| ≤ 2m' + (2/3)(m'+1)^{2/3} + 1`: the block is `m'`
pairs of consecutive fibers, each contributing at most `2`, plus one fiber left over. This
is the paper's "pair consecutive fibers, whose odd-point counts differ by at most 3, and bound
the remaining end fiber", with `2` in place of `3`. -/
theorem slowSum_abs_le {m' : ℕ} (hm : 1 ≤ m') :
    |(slowSum m' : ℝ)| ≤ 2 * m' + (2 / 3 * ((m' : ℝ) + 1) ^ ((2 : ℝ) / 3) + 1) := by
  have hsplit : Finset.Ico (m' ^ 2) ((m' + 1) ^ 2)
      = Finset.Ico (m' ^ 2) (m' ^ 2 + 2 * m' + 1) := by
    congr 1; ring
  set A := ∑ m ∈ Finset.Ico (m' ^ 2) (m' ^ 2 + 2 * m'),
    psi m * ((FiberParity.oeFiber m).card : ℤ) with hA
  have hZ : slowSum m' = A + psi (m' ^ 2 + 2 * m')
      * ((FiberParity.oeFiber (m' ^ 2 + 2 * m')).card : ℤ) := by
    rw [slowSum_eq_fibers, hsplit, Finset.sum_Ico_succ_top (by omega)]
  have hpairs : |A| ≤ (m' : ℤ) * 2 :=
    abs_alt_sum_le (fun m => ((FiberParity.oeFiber m).card : ℤ)) (m' ^ 2) 2
      (fun m hm' => oeFiber_card_succ_diff (by nlinarith)) m'
  have hAbs : |(A : ℝ)| ≤ 2 * m' := by
    have h' : ((|A| : ℤ) : ℝ) ≤ (((m' : ℤ) * 2 : ℤ) : ℝ) := by exact_mod_cast hpairs
    push_cast at h'
    linarith
  have hlast : ((FiberParity.oeFiber (m' ^ 2 + 2 * m')).card : ℝ)
      ≤ 2 / 3 * ((m' : ℝ) + 1) ^ ((2 : ℝ) / 3) + 1 := by
    have h := FiberParity.oeFiber_card_le (m' ^ 2 + 2 * m')
    have e : ((m' ^ 2 + 2 * m' : ℕ) : ℝ) + 1 = ((m' : ℝ) + 1) ^ (2 : ℕ) := by push_cast; ring
    rw [e, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)] at h
    norm_num at h ⊢
    linarith
  have hpsi : |(psi (m' ^ 2 + 2 * m') : ℝ)| = 1 := by exact_mod_cast abs_psi _
  rw [hZ]
  push_cast
  calc |(A : ℝ) + (psi (m' ^ 2 + 2 * m') : ℝ) * ((FiberParity.oeFiber (m' ^ 2 + 2 * m')).card : ℝ)|
      ≤ |(A : ℝ)| + |(psi (m' ^ 2 + 2 * m') : ℝ)
          * ((FiberParity.oeFiber (m' ^ 2 + 2 * m')).card : ℝ)| := abs_add_le _ _
    _ ≤ 2 * m' + (2 / 3 * ((m' : ℝ) + 1) ^ ((2 : ℝ) / 3) + 1) := by
        rw [abs_mul, hpsi, one_mul, Nat.abs_cast]
        exact add_le_add hAbs hlast

/-! ### The number of odd integers of the block, two-sidedly -/

theorem card_Ico_block (m' : ℕ) : (Finset.Ico (m' ^ 2) ((m' + 1) ^ 2)).card = 2 * m' + 1 := by
  rw [Nat.card_Ico]
  have : (m' + 1) ^ 2 = m' ^ 2 + (2 * m' + 1) := by ring
  omega

/-- `M ≤ (2m'+1)((2/3)(m'+1)^{2/3} + 1)`: every fiber of the block has at most
`(2/3)((m'+1)²)^{1/3} + 1` members. -/
theorem oddBlock_card_le (m' : ℕ) :
    ((oddBlock m').card : ℝ) ≤ (2 * m' + 1) * (2 / 3 * ((m' : ℝ) + 1) ^ ((2 : ℝ) / 3) + 1) := by
  rw [oddBlock_card_eq]
  push_cast
  have h := Finset.sum_le_card_nsmul (Finset.Ico (m' ^ 2) ((m' + 1) ^ 2))
    (fun m => ((FiberParity.oeFiber m).card : ℝ))
    (2 / 3 * ((m' : ℝ) + 1) ^ ((2 : ℝ) / 3) + 1) ?_
  · rw [card_Ico_block, nsmul_eq_mul] at h
    push_cast at h
    exact h
  · intro m hm
    rw [Finset.mem_Ico] at hm
    have h := FiberParity.oeFiber_card_le m
    have h1 : (m : ℝ) + 1 ≤ ((m' : ℝ) + 1) ^ (2 : ℕ) := by
      have : m + 1 ≤ (m' + 1) ^ 2 := hm.2
      exact_mod_cast this
    have hle : ((m : ℝ) + 1) ^ ((1 : ℝ) / 3) ≤ ((m' : ℝ) + 1) ^ ((2 : ℝ) / 3) := by
      calc ((m : ℝ) + 1) ^ ((1 : ℝ) / 3) ≤ (((m' : ℝ) + 1) ^ (2 : ℕ)) ^ ((1 : ℝ) / 3) :=
            Real.rpow_le_rpow (by positivity) h1 (by norm_num)
        _ = ((m' : ℝ) + 1) ^ ((2 : ℝ) / 3) := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]; norm_num
    linarith

/-- `(2m'+1)((2/3)m'^{2/3} - 1) ≤ M`: every fiber of the block has at least
`(2/3)(m'²)^{1/3} - 1` members. -/
theorem oddBlock_card_ge {m' : ℕ} (hm : 1 ≤ m') :
    (2 * m' + 1) * (2 / 3 * (m' : ℝ) ^ ((2 : ℝ) / 3) - 1) ≤ ((oddBlock m').card : ℝ) := by
  rw [oddBlock_card_eq]
  push_cast
  have h := Finset.card_nsmul_le_sum (Finset.Ico (m' ^ 2) ((m' + 1) ^ 2))
    (fun m => ((FiberParity.oeFiber m).card : ℝ))
    (2 / 3 * (m' : ℝ) ^ ((2 : ℝ) / 3) - 1) ?_
  · rw [card_Ico_block, nsmul_eq_mul] at h
    push_cast at h
    exact h
  · intro m hm'
    rw [Finset.mem_Ico] at hm'
    have hm1 : 1 ≤ m := by nlinarith
    have h := FiberParity.oeFiber_card_ge hm1
    have h1 : ((m' : ℝ)) ^ (2 : ℕ) ≤ (m : ℝ) := by exact_mod_cast hm'.1
    have hge : (m' : ℝ) ^ ((2 : ℝ) / 3) ≤ (m : ℝ) ^ ((1 : ℝ) / 3) := by
      calc (m' : ℝ) ^ ((2 : ℝ) / 3) = ((m' : ℝ) ^ (2 : ℕ)) ^ ((1 : ℝ) / 3) := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]; norm_num
        _ ≤ (m : ℝ) ^ ((1 : ℝ) / 3) := Real.rpow_le_rpow (by positivity) h1 (by norm_num)
    linarith

/-- A quarter of the block is `m'^{5/3}/3` up to `m' + 1`: the "in particular" of the
proposition, before the parity sums enter. -/
theorem oddBlock_quarter_close {m' : ℕ} (hm : 1 ≤ m') :
    |((oddBlock m').card : ℝ) / 4 - (m' : ℝ) ^ ((5 : ℝ) / 3) / 3| ≤ m' + 1 := by
  have hx1 : (1 : ℝ) ≤ m' := by exact_mod_cast hm
  have hx0 : (0 : ℝ) < m' := by linarith
  set x : ℝ := (m' : ℝ) with hx
  set u := x ^ ((2 : ℝ) / 3) with hu
  set v := x ^ (-((1 : ℝ) / 3)) with hv
  set w := x ^ ((5 : ℝ) / 3) with hw
  have hxu : x * u = w := by
    rw [hu, hw, show (5 : ℝ) / 3 = 1 + 2 / 3 by norm_num, Real.rpow_add hx0, Real.rpow_one]
  have hxv : x * v = u := by
    rw [hv, hu, show (2 : ℝ) / 3 = 1 + -(1 / 3) by norm_num, Real.rpow_add hx0, Real.rpow_one]
  have hu_le : u ≤ x := by
    calc u = x ^ ((2 : ℝ) / 3) := rfl
      _ ≤ x ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num)
      _ = x := Real.rpow_one x
  have hv_le : v ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hx1 (by norm_num)
  have hu0 : 0 ≤ u := Real.rpow_nonneg hx0.le _
  have hv0 : 0 ≤ v := Real.rpow_nonneg hx0.le _
  have hM_le := oddBlock_card_le m'
  have hM_ge := oddBlock_card_ge hm
  have hb : (x + 1) ^ ((2 : ℝ) / 3) ≤ u + 2 / 3 * v := FiberParity.rpow_two_thirds_succ_le hm
  have hb' : (2 * x + 1) * (x + 1) ^ ((2 : ℝ) / 3) ≤ (2 * x + 1) * (u + 2 / 3 * v) :=
    mul_le_mul_of_nonneg_left hb (by linarith)
  rw [abs_le]
  constructor
  · nlinarith
  · nlinarith

/-! ### Proposition 4.4 with the slow sum discharged -/

/-- **Proposition 4.4, equation (4.1), given the two exponential-sum bounds.** The slow sum is
proved (`slowSum_abs_le`); the fast sum and the product sum remain hypotheses. -/
theorem block_average_two_bounds {m' : ℕ} (hm : 1 ≤ m') {B : ℝ}
    (h₂ : |(fastSum m' : ℝ)| ≤ B) (h₁₂ : |(productSum m' : ℝ)| ≤ B) :
    |((U m').card : ℝ) - ((oddBlock m').card : ℝ) / 4| ≤ B / 2 + (m' + 1) := by
  have hkey : (4 : ℝ) * ((U m').card : ℝ) = ((oddBlock m').card : ℝ)
      + (slowSum m' : ℝ) + (fastSum m' : ℝ) + (productSum m' : ℝ) := by
    exact_mod_cast congrArg (fun z : ℤ => (z : ℝ)) (four_card_U m')
  have h₁ := slowSum_abs_le hm
  have hm0 : (0 : ℝ) ≤ m' := Nat.cast_nonneg _
  have hpow : ((m' : ℝ) + 1) ^ ((2 : ℝ) / 3) ≤ (m' : ℝ) + 1 := by
    calc ((m' : ℝ) + 1) ^ ((2 : ℝ) / 3) ≤ ((m' : ℝ) + 1) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
      _ = (m' : ℝ) + 1 := Real.rpow_one _
  have hdiff : ((U m').card : ℝ) - ((oddBlock m').card : ℝ) / 4
      = ((slowSum m' : ℝ) + (fastSum m' : ℝ) + (productSum m' : ℝ)) / 4 := by linarith
  rw [hdiff, abs_div, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 4),
    div_le_iff₀ (by norm_num : (0 : ℝ) < 4)]
  have htri : |(slowSum m' : ℝ) + (fastSum m' : ℝ) + (productSum m' : ℝ)|
      ≤ |(slowSum m' : ℝ)| + |(fastSum m' : ℝ)| + |(productSum m' : ℝ)| := by
    calc |(slowSum m' : ℝ) + (fastSum m' : ℝ) + (productSum m' : ℝ)|
        ≤ |(slowSum m' : ℝ) + (fastSum m' : ℝ)| + |(productSum m' : ℝ)| := abs_add_le _ _
      _ ≤ |(slowSum m' : ℝ)| + |(fastSum m' : ℝ)| + |(productSum m' : ℝ)| := by
          have := abs_add_le (slowSum m' : ℝ) (fastSum m' : ℝ); linarith
  linarith

/-- **The asymptotic form of Proposition 4.4 with an explicit error**, given the two bounds:
`|U(m')|` is within `B/2 + 2(m'+1)` of `m'^{5/3}/3`. With `B = C m'^{11/9} log(m'+1)` this
is the paper's `|U(m')| = m'^{5/3}/3 (1 + O(m'^{-4/9} log(m'+1)))`. -/
theorem block_average_asymptotic {m' : ℕ} (hm : 1 ≤ m') {B : ℝ}
    (h₂ : |(fastSum m' : ℝ)| ≤ B) (h₁₂ : |(productSum m' : ℝ)| ≤ B) :
    |((U m').card : ℝ) - (m' : ℝ) ^ ((5 : ℝ) / 3) / 3| ≤ B / 2 + 2 * (m' + 1) := by
  have h1 := block_average_two_bounds hm h₂ h₁₂
  have h2 := oddBlock_quarter_close hm
  calc |((U m').card : ℝ) - (m' : ℝ) ^ ((5 : ℝ) / 3) / 3|
      = |(((U m').card : ℝ) - ((oddBlock m').card : ℝ) / 4)
          + (((oddBlock m').card : ℝ) / 4 - (m' : ℝ) ^ ((5 : ℝ) / 3) / 3)| := by ring_nf
    _ ≤ |((U m').card : ℝ) - ((oddBlock m').card : ℝ) / 4|
          + |((oddBlock m').card : ℝ) / 4 - (m' : ℝ) ^ ((5 : ℝ) / 3) / 3| := abs_add_le _ _
    _ ≤ B / 2 + (m' + 1) + (m' + 1) := add_le_add h1 h2
    _ = B / 2 + 2 * (m' + 1) := by ring

/-- Proposition 4.4 in the paper's shape with only the two exponential-sum hypotheses: for
`m' ≥ 2` and both remaining sums at most `C m'^{11/9} log(m'+1)`, equation (4.1) holds with
`C_B = C/2 + 2`. -/
theorem block_average_bound_two {m' : ℕ} (hm : 2 ≤ m') {C : ℝ}
    (h₂ : |(fastSum m' : ℝ)| ≤ C * (m' : ℝ) ^ ((11 : ℝ) / 9) * Real.log (m' + 1))
    (h₁₂ : |(productSum m' : ℝ)| ≤ C * (m' : ℝ) ^ ((11 : ℝ) / 9) * Real.log (m' + 1)) :
    |((U m').card : ℝ) - ((oddBlock m').card : ℝ) / 4|
      ≤ (C / 2 + 2) * (m' : ℝ) ^ ((11 : ℝ) / 9) * Real.log (m' + 1) := by
  have h := block_average_two_bounds (by omega) h₂ h₁₂
  have hx : (2 : ℝ) ≤ m' := by exact_mod_cast hm
  have hpow : (m' : ℝ) ≤ (m' : ℝ) ^ ((11 : ℝ) / 9) := by
    calc (m' : ℝ) = (m' : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ (m' : ℝ) ^ ((11 : ℝ) / 9) :=
          Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
  have hlog : 1 ≤ Real.log ((m' : ℝ) + 1) := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    have := Real.exp_one_lt_d9
    linarith
  have hprod : (m' : ℝ) + 1 ≤ 2 * ((m' : ℝ) ^ ((11 : ℝ) / 9) * Real.log (m' + 1)) := by
    have h0 : 0 ≤ (m' : ℝ) ^ ((11 : ℝ) / 9) := by positivity
    nlinarith
  linarith

end BlockAverage

end Problems.Juggler
