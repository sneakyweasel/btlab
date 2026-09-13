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
  (`block_average_of_bounds`, `block_average_bound`).

The hypotheses of the last item are exactly what the paper proves by exponential sums and what
this file assumes. Discharging them needs Vaaler's approximation and the van der Corput
estimates, which Mathlib does not carry; until then Proposition 4.4 is a human proof and the
verification table says so. The "in particular" form `|U(m')| = m'^{5/3}/3 (1 + O(·))` needs in
addition a two-sided estimate for the number of odd integers of the block, which is not here
either. Nothing in this file bounds a density, and nothing here is a halt theorem.
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

end BlockAverage

end Problems.Juggler
