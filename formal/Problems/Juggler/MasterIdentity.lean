/-
# Paper B, Lemma 5.1: the master identity

`docs/theory/juggler_parity_discrepancy_note.md`, Lemma 5.1, is the exact
bookkeeping that lets the kernel argument double-difference the phase `c·θ₂`
without leaving an unbounded smooth part behind.  The probe
(`src/research/juggler_sequence/paper_b_audit.py`) checks its identities
numerically, at 60 digits on random odd `n`.  They are exact, so they can be
proved instead, and that is what this file does.

Four parts.

1. **(i), the level-2 defect.**  The manuscript proves it by Taylor at `v` with a
   Lagrange remainder.  As with Lemma 4.3(i), the mean value is avoidable: with
   `a = √v` and `b = √Y`, the remainder is exactly `R = ¼(b-a)²(2b+a)`, and both
   printed bounds follow by `nlinarith`.
2. **(ii), the carry as a sawtooth difference.**  `[{A}+{B} ≥ 1] = {A}+{B}-{A+B}`,
   the identity the manuscript displays, and the double-gap identity built from
   two applications of it.
3. **The exact product rule for double differences** over the four base points
   `n`, `n+d₁`, `n+d₂`, `n+d₁+d₂`.  The manuscript says this is "verified by
   expanding both sides"; here it is `ring`.
4. **(iv), the master identity itself**, assembled from 2 and 3.  Every bracket
   on the right is bounded by `2`, which is the point of the lemma.

What is *not* here: Lemma 5.1(iii)'s branch-freeze inventory, whose content is
analytic (mean value theorems and the numerical ranges of `β_i`), and everything
downstream of it.
-/

import Problems.Juggler.PaperBAssembly
import Mathlib.Tactic

namespace Problems.Juggler

/-! ## 1. Lemma 5.1(i): the level-2 defect in closed form -/

section Level2Defect

/-- **The closed form.**  With `a = √v` and `b = √Y` (so `θ₂ = b² - a²` is the
level-2 defect `Y - v`), the Taylor defect
`Y^(3/2) - v^(3/2) - (3/2)v^(1/2)θ₂` is exactly `½(b-a)²(2b+a)`.  Since
`Y^(3/2) = m^(9/4)`, the manuscript's remainder is `R = ¼(b-a)²(2b+a)`. -/
theorem lemma51_i_closed_form (a b : ℝ) :
    b ^ 3 - a ^ 3 - (3 / 2) * a * (b ^ 2 - a ^ 2)
      = (1 / 2) * (b - a) ^ 2 * (2 * b + a) := by ring

/-- **`0 ≤ R`.**  The level-2 defect remainder is one-signed, as the manuscript
needs. -/
theorem lemma51_i_nonneg (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) :
    0 ≤ (1 / 4) * (b - a) ^ 2 * (2 * b + a) := by
  have h : 0 ≤ 2 * b + a := by linarith
  positivity

/-- **`R·a ≤ (3/16)θ₂²`**, i.e. `R ≤ (3/16)θ₂²v^(-1/2)`; at `θ₂ < 1` this is the
printed `R ≤ (3/16)v^(-1/2)`.  Reduces to `(a + 3b)(a - b) ≤ 0`. -/
theorem lemma51_i_upper (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) :
    ((1 / 4) * (b - a) ^ 2 * (2 * b + a)) * a ≤ (3 / 16) * (b ^ 2 - a ^ 2) ^ 2 := by
  nlinarith [sq_nonneg (b - a), sq_nonneg (a + b),
    mul_nonneg (sq_nonneg (b - a)) (by linarith : (0:ℝ) ≤ a + 3 * b),
    mul_nonneg ha (sq_nonneg (b - a))]

/-- The manuscript's form: `(3/4)v^(1/2)θ₂ = ½(m^(9/4) - v^(3/2)) - R`, stated
with `v = a²`, `Y = b²`, `m^(9/4) = Y^(3/2) = b³`. -/
theorem lemma51_i_identity (a b : ℝ) :
    (3 / 4) * a * (b ^ 2 - a ^ 2)
      = (1 / 2) * (b ^ 3 - a ^ 3) - (1 / 4) * (b - a) ^ 2 * (2 * b + a) := by ring

end Level2Defect

/-! ## 2. Lemma 5.1(ii): carries are differences of unit sawtooths -/

section Carries

/-- The unit carry `[{A} + {B} ≥ 1]`, as a real number. -/
noncomputable def carry (A B : ℝ) : ℝ :=
  if 1 ≤ Int.fract A + Int.fract B then 1 else 0

theorem carry_nonneg (A B : ℝ) : 0 ≤ carry A B := by
  unfold carry; split <;> norm_num

theorem carry_le_one (A B : ℝ) : carry A B ≤ 1 := by
  unfold carry; split <;> norm_num

/-- **The sawtooth form of the carry**, the elementary identity the manuscript
displays: `[{A}+{B} ≥ 1] = {A} + {B} - {A+B}`.  Both sides equal
`{A}+{B}-{A+B}` because `{A}+{B} ∈ [0,2)`. -/
theorem carry_as_sawtooth (A B : ℝ) :
    carry A B = Int.fract A + Int.fract B - Int.fract (A + B) := by
  have h := carry_identity A B
  have hcast : ((⌊A + B⌋ : ℤ) : ℝ) - (⌊A⌋ : ℤ) - (⌊B⌋ : ℤ) = carry A B := by
    unfold carry
    by_cases hc : 1 ≤ Int.fract A + Int.fract B
    · rw [if_pos hc] at h ⊢
      have : (⌊A + B⌋ : ℤ) = ⌊A⌋ + ⌊B⌋ + 1 := by omega
      rw [this]; push_cast; ring
    · rw [if_neg hc] at h ⊢
      have : (⌊A + B⌋ : ℤ) = ⌊A⌋ + ⌊B⌋ := by omega
      rw [this]; push_cast; ring
  simp only [Int.fract] at *
  linarith

/-- **The substitution engine.**  One step of the level-2 bookkeeping: the
increment of the defect `θ₂ = {Y}` across a shift equals the sawtooth of the
gap minus the carry.  Every substitution in Lemma 5.1(iv) is this lemma. -/
theorem fract_diff_level2 (y w : ℝ) :
    Int.fract (y + w) - Int.fract y = Int.fract w - carry y w := by
  rw [carry_as_sawtooth]
  simp only [Int.fract]
  push_cast
  ring

/-- **Lemma 5.1(ii), the double gap.**  With `v = ⌊Y⌋`, `g₂ = Δ₁v`,
`W = Δ₁Y` and `ΔΔY = Δ₂W`, the second difference of the integer part is
`Δ₂g₂ = ⌊ΔΔY⌋ + κ'' + Δ₂κ₂` — two applications of the carry identity, first to
`Y` at shift `d₁`, then to `W` at shift `d₂`. -/
theorem lemma51_double_gap (y₀ y₁ y₂ y₁₂ : ℝ) :
    ((⌊y₁₂⌋ - ⌊y₂⌋ : ℤ) : ℝ) - ((⌊y₁⌋ - ⌊y₀⌋ : ℤ) : ℝ)
      = ((⌊(y₁₂ - y₂) - (y₁ - y₀)⌋ : ℤ) : ℝ)
        + carry (y₁ - y₀) ((y₁₂ - y₂) - (y₁ - y₀))
        + (carry y₂ (y₁₂ - y₂) - carry y₀ (y₁ - y₀)) := by
  have h₁ : ((⌊y₁⌋ - ⌊y₀⌋ : ℤ) : ℝ)
      = ((⌊y₁ - y₀⌋ : ℤ) : ℝ) + carry y₀ (y₁ - y₀) := by
    have := fract_diff_level2 y₀ (y₁ - y₀)
    simp only [Int.fract] at this
    have e : y₀ + (y₁ - y₀) = y₁ := by ring
    rw [e] at this
    push_cast
    linarith
  have h₂ : ((⌊y₁₂⌋ - ⌊y₂⌋ : ℤ) : ℝ)
      = ((⌊y₁₂ - y₂⌋ : ℤ) : ℝ) + carry y₂ (y₁₂ - y₂) := by
    have := fract_diff_level2 y₂ (y₁₂ - y₂)
    simp only [Int.fract] at this
    have e : y₂ + (y₁₂ - y₂) = y₁₂ := by ring
    rw [e] at this
    push_cast
    linarith
  have h₃ : ((⌊y₁₂ - y₂⌋ : ℤ) : ℝ) - ((⌊y₁ - y₀⌋ : ℤ) : ℝ)
      = ((⌊(y₁₂ - y₂) - (y₁ - y₀)⌋ : ℤ) : ℝ)
        + carry (y₁ - y₀) ((y₁₂ - y₂) - (y₁ - y₀)) := by
    have := fract_diff_level2 (y₁ - y₀) ((y₁₂ - y₂) - (y₁ - y₀))
    simp only [Int.fract] at this
    have e : (y₁ - y₀) + ((y₁₂ - y₂) - (y₁ - y₀)) = y₁₂ - y₂ := by ring
    rw [e] at this
    push_cast
    linarith
  rw [h₁, h₂]
  linarith [h₃]

end Carries

/-! ## 3. The exact product rule for double differences -/

section ProductRule

/-- **The product rule over four base points.**  With
`ΔΔg = g₁₂ - g₁ - g₂ + g₀`, `(Δ₂c)(n+d₁) = c₁₂ - c₁` and
`(Δ₁c)(n+d₂) = c₁₂ - c₂`,
`ΔΔ(cf) = c₁₁·ΔΔf + (Δ₂c)(n+d₁)·Δ₁f + (Δ₁c)(n+d₂)·Δ₂f + (ΔΔc)·f`.
The manuscript says "verified by expanding both sides over the four base
points"; that expansion is `ring`. -/
theorem double_difference_product (c₀ c₁ c₂ c₁₂ f₀ f₁ f₂ f₁₂ : ℝ) :
    c₁₂ * f₁₂ - c₁ * f₁ - c₂ * f₂ + c₀ * f₀
      = c₁₂ * (f₁₂ - f₁ - f₂ + f₀)
        + (c₁₂ - c₁) * (f₁ - f₀)
        + (c₁₂ - c₂) * (f₂ - f₀)
        + (c₁₂ - c₁ - c₂ + c₀) * f₀ := by ring

end ProductRule

/-! ## 4. Lemma 5.1(iv): the master identity -/

section Master

/-- **Lemma 5.1(iv), the master identity.**  The doubly differenced kernel phase
`ΔΔ(c·θ₂)`, with `θ₂ = {Y}` the level-2 defect, decomposes exactly into four
terms, in each of which the non-smooth factor is a *bounded* bracket:

* `(ΔΔc)·θ₂`, with `θ₂ ∈ [0,1)`;
* `(Δ₂c)(n+d₁)·({W} - κ₂)`, with `W = Δ₁Y` and `κ₂` the level-2 carry;
* `(Δ₁c)(n+d₂)·({W'} - κ₂')`, with `W' = Δ₂Y`;
* `c₁₁·({ΔΔY} - κ'' - Δ₂κ₂)`.

No unbounded smooth part survives the differencing — which is the whole purpose
of the lemma.  The proof is the product rule of Section 3 together with three
applications of `fract_diff_level2`. -/
theorem lemma51_master (c₀ c₁ c₂ c₁₂ y₀ y₁ y₂ y₁₂ : ℝ) :
    c₁₂ * Int.fract y₁₂ - c₁ * Int.fract y₁ - c₂ * Int.fract y₂ + c₀ * Int.fract y₀
      = (c₁₂ - c₁ - c₂ + c₀) * Int.fract y₀
        + (c₁₂ - c₁) * (Int.fract (y₁ - y₀) - carry y₀ (y₁ - y₀))
        + (c₁₂ - c₂) * (Int.fract (y₂ - y₀) - carry y₀ (y₂ - y₀))
        + c₁₂ * (Int.fract ((y₁₂ - y₂) - (y₁ - y₀))
            - carry (y₁ - y₀) ((y₁₂ - y₂) - (y₁ - y₀))
            - (carry y₂ (y₁₂ - y₂) - carry y₀ (y₁ - y₀))) := by
  -- Δ₁θ₂ = {W} - κ₂
  have e₁ : Int.fract y₁ - Int.fract y₀
      = Int.fract (y₁ - y₀) - carry y₀ (y₁ - y₀) := by
    have := fract_diff_level2 y₀ (y₁ - y₀)
    have e : y₀ + (y₁ - y₀) = y₁ := by ring
    rwa [e] at this
  -- Δ₂θ₂ = {W'} - κ₂'
  have e₂ : Int.fract y₂ - Int.fract y₀
      = Int.fract (y₂ - y₀) - carry y₀ (y₂ - y₀) := by
    have := fract_diff_level2 y₀ (y₂ - y₀)
    have e : y₀ + (y₂ - y₀) = y₂ := by ring
    rwa [e] at this
  -- the upper edge, Δ₁θ₂ at n + d₂
  have e₃ : Int.fract y₁₂ - Int.fract y₂
      = Int.fract (y₁₂ - y₂) - carry y₂ (y₁₂ - y₂) := by
    have := fract_diff_level2 y₂ (y₁₂ - y₂)
    have e : y₂ + (y₁₂ - y₂) = y₁₂ := by ring
    rwa [e] at this
  -- ΔΔθ₂ = {ΔΔY} - κ'' - Δ₂κ₂
  have e₄ : Int.fract (y₁₂ - y₂) - Int.fract (y₁ - y₀)
      = Int.fract ((y₁₂ - y₂) - (y₁ - y₀))
        - carry (y₁ - y₀) ((y₁₂ - y₂) - (y₁ - y₀)) := by
    have := fract_diff_level2 (y₁ - y₀) ((y₁₂ - y₂) - (y₁ - y₀))
    have e : (y₁ - y₀) + ((y₁₂ - y₂) - (y₁ - y₀)) = y₁₂ - y₂ := by ring
    rwa [e] at this
  -- ΔΔθ₂, obtained from the upper edge minus the lower edge
  have eC : Int.fract y₁₂ - Int.fract y₁ - Int.fract y₂ + Int.fract y₀
      = Int.fract ((y₁₂ - y₂) - (y₁ - y₀))
        - carry (y₁ - y₀) ((y₁₂ - y₂) - (y₁ - y₀))
        - (carry y₂ (y₁₂ - y₂) - carry y₀ (y₁ - y₀)) := by
    linarith [e₁, e₃, e₄]
  -- with the three increments back in θ₂ form, the statement is the product rule
  rw [← eC, ← e₁, ← e₂]
  ring

/-- **Every bracket is bounded by `2`.**  This is what the decomposition buys:
the three carry brackets and the defect itself are all `O(1)`, so the doubly
differenced phase carries no growing amplitude. -/
theorem lemma51_brackets_le_two (y₀ y₁ y₂ y₁₂ : ℝ) :
    |Int.fract y₀| ≤ 2
    ∧ |Int.fract (y₁ - y₀) - carry y₀ (y₁ - y₀)| ≤ 2
    ∧ |Int.fract (y₂ - y₀) - carry y₀ (y₂ - y₀)| ≤ 2
    ∧ |Int.fract ((y₁₂ - y₂) - (y₁ - y₀))
        - carry (y₁ - y₀) ((y₁₂ - y₂) - (y₁ - y₀))
        - (carry y₂ (y₁₂ - y₂) - carry y₀ (y₁ - y₀))| ≤ 2 := by
  have f₀ := Int.fract_nonneg y₀
  have f₀' := Int.fract_lt_one y₀
  refine ⟨by rw [abs_le]; constructor <;> linarith, ?_, ?_, ?_⟩
  · have a := Int.fract_nonneg (y₁ - y₀)
    have b := Int.fract_lt_one (y₁ - y₀)
    have c := carry_nonneg y₀ (y₁ - y₀)
    have d := carry_le_one y₀ (y₁ - y₀)
    rw [abs_le]; constructor <;> linarith
  · have a := Int.fract_nonneg (y₂ - y₀)
    have b := Int.fract_lt_one (y₂ - y₀)
    have c := carry_nonneg y₀ (y₂ - y₀)
    have d := carry_le_one y₀ (y₂ - y₀)
    rw [abs_le]; constructor <;> linarith
  · have a := Int.fract_nonneg ((y₁₂ - y₂) - (y₁ - y₀))
    have b := Int.fract_lt_one ((y₁₂ - y₂) - (y₁ - y₀))
    have c₁ := carry_nonneg (y₁ - y₀) ((y₁₂ - y₂) - (y₁ - y₀))
    have d₁ := carry_le_one (y₁ - y₀) ((y₁₂ - y₂) - (y₁ - y₀))
    have c₂ := carry_nonneg y₂ (y₁₂ - y₂)
    have d₂ := carry_le_one y₂ (y₁₂ - y₂)
    have c₃ := carry_nonneg y₀ (y₁ - y₀)
    have d₃ := carry_le_one y₀ (y₁ - y₀)
    rw [abs_le]; constructor <;> linarith

end Master

end Problems.Juggler
