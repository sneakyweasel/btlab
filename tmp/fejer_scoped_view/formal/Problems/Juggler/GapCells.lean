import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic

namespace Problems.Juggler

/-!
# Gap cells: exact floor reductions for the parity-discrepancy program

The analytic discrepancy estimates of the finite-dynamics note
(Section 5) and of the two-step parity companion are human proofs.
They rest on three exact floor reductions, packaged here:

* `floor_add_eq_add_carry` — the floor of a sum splits into the two
  floors plus a 0/1 carry decided by the fractional parts;
* `floor_gap_eq_carry` / `seq_floor_gap` — the gap-cell identity
  (Lemmas B and N of the companion): the increment of `⌊Y⌋` along a
  step is the floor of the smooth increment plus a sawtooth carry;
* `floor_odd_iff_half_le_fract_half` — the parity of `⌊x⌋` is the
  event `{x/2} ≥ 1/2`, the exact fractional-part form that converts
  parity sums into interval discrepancies.

No analytic estimate is claimed here. These identities are exact and
unconditional; the van der Corput and Erdős–Turán stages of the
companion remain human proofs outside Lean.
-/

/-- The floor of a sum is the sum of floors plus a 0/1 carry, decided
by whether the fractional parts overflow. -/
theorem floor_add_eq_add_carry (x y : ℝ) :
    ⌊x + y⌋ = ⌊x⌋ + ⌊y⌋ +
      if 1 ≤ Int.fract x + Int.fract y then 1 else 0 := by
  have hxy : x + y = ((⌊x⌋ + ⌊y⌋ : ℤ) : ℝ) + (Int.fract x + Int.fract y) := by
    have hx := Int.floor_add_fract x
    have hy := Int.floor_add_fract y
    push_cast
    linarith
  rw [hxy, Int.floor_intCast_add]
  congr 1
  by_cases h : 1 ≤ Int.fract x + Int.fract y
  · rw [if_pos h]
    refine Int.floor_eq_iff.mpr ⟨by exact_mod_cast h, ?_⟩
    have hx1 := Int.fract_lt_one x
    have hy1 := Int.fract_lt_one y
    push_cast
    linarith
  · rw [if_neg h]
    have hlt : Int.fract x + Int.fract y < 1 := not_le.mp h
    refine Int.floor_eq_iff.mpr ⟨?_, by push_cast; linarith⟩
    have hx0 := Int.fract_nonneg x
    have hy0 := Int.fract_nonneg y
    push_cast
    linarith

/-- Gap-cell identity (Lemma B pattern): the increment of `⌊·⌋` across
a shift `δ` is `⌊δ⌋` plus the carry `𝟙[{x} ≥ 1 − {δ}]`. -/
theorem floor_gap_eq_carry (x δ : ℝ) :
    ⌊x + δ⌋ - ⌊x⌋ = ⌊δ⌋ +
      if 1 - Int.fract δ ≤ Int.fract x then 1 else 0 := by
  rw [floor_add_eq_add_carry x δ]
  by_cases h : 1 - Int.fract δ ≤ Int.fract x
  · rw [if_pos h, if_pos (by linarith)]
    ring
  · rw [if_neg h, if_neg (fun hc => h (by linarith))]
    ring

/-- Level-2 gap identity (Lemma N pattern): along any real-valued
sequence `Y`, the integer gap `⌊Y (n+h)⌋ − ⌊Y n⌋` is the floor of the
smooth increment plus a 0/1 carry read off the fractional parts. With
`Y = (m ∘ ·)^{3/2}` this is the companion's `g₂ = ⌊ΔY⌋ + κ₂`. -/
theorem seq_floor_gap (Y : ℕ → ℝ) (n h : ℕ) :
    ⌊Y (n + h)⌋ - ⌊Y n⌋ =
      ⌊Y (n + h) - Y n⌋ +
        if 1 - Int.fract (Y (n + h) - Y n) ≤ Int.fract (Y n) then 1
        else 0 := by
  have hgap := floor_gap_eq_carry (Y n) (Y (n + h) - Y n)
  rw [add_sub_cancel] at hgap
  exact hgap

/-- The carry of the gap identity is 0 or 1. -/
theorem gap_carry_mem (x δ : ℝ) :
    (if 1 - Int.fract δ ≤ Int.fract x then (1 : ℤ) else 0) = 0 ∨
      (if 1 - Int.fract δ ≤ Int.fract x then (1 : ℤ) else 0) = 1 := by
  by_cases h : 1 - Int.fract δ ≤ Int.fract x
  · exact Or.inr (if_pos h)
  · exact Or.inl (if_neg h)

/-- Double-gap identity (Lemma R2 of the two-step parity companion):
the second difference of the level-2 gap `g₂ n = ⌊Y (n+h₁)⌋ − ⌊Y n⌋`
along a shift `h₂` is the floor of the double increment `Δ₂Δ₁Y` plus
a 0/1 carry on the first increment plus the difference of the two
Lemma-N carries. Two composed instances of `seq_floor_gap`. -/
theorem seq_floor_gap_second (Y : ℕ → ℝ) (n h₁ h₂ : ℕ) :
    (⌊Y (n + h₁ + h₂)⌋ - ⌊Y (n + h₂)⌋) - (⌊Y (n + h₁)⌋ - ⌊Y n⌋) =
      ⌊(Y (n + h₁ + h₂) - Y (n + h₂)) - (Y (n + h₁) - Y n)⌋ +
        (if 1 - Int.fract ((Y (n + h₁ + h₂) - Y (n + h₂)) -
              (Y (n + h₁) - Y n)) ≤
            Int.fract (Y (n + h₁) - Y n) then 1 else 0) +
        ((if 1 - Int.fract (Y (n + h₁ + h₂) - Y (n + h₂)) ≤
              Int.fract (Y (n + h₂)) then 1 else 0) -
          (if 1 - Int.fract (Y (n + h₁) - Y n) ≤
              Int.fract (Y n) then 1 else 0)) := by
  have hW0 := seq_floor_gap Y n h₁
  have hW1 := seq_floor_gap Y (n + h₂) h₁
  rw [show n + h₂ + h₁ = n + h₁ + h₂ from by omega] at hW1
  have hDW := floor_gap_eq_carry (Y (n + h₁) - Y n)
    ((Y (n + h₁ + h₂) - Y (n + h₂)) - (Y (n + h₁) - Y n))
  rw [show Y (n + h₁) - Y n +
        ((Y (n + h₁ + h₂) - Y (n + h₂)) - (Y (n + h₁) - Y n)) =
      Y (n + h₁ + h₂) - Y (n + h₂) from by ring] at hDW
  omega

/-- Carry as a difference of sawtooths (Lemma 5.1(ii) of the
parity-discrepancy note): the 0/1 carry `𝟙[{a} + {b} ≥ 1]` equals
`{a} + {b} − {a + b}` exactly, for all reals. This is the identity that
lets the kernel argument expand each carry additively by finite
Fourier series. -/
theorem carry_eq_fract_add_sub_fract (a b : ℝ) :
    (if 1 ≤ Int.fract a + Int.fract b then (1 : ℝ) else 0) =
      Int.fract a + Int.fract b - Int.fract (a + b) := by
  have hfl := floor_add_eq_add_carry a b
  have ha := Int.floor_add_fract a
  have hb := Int.floor_add_fract b
  have hab := Int.floor_add_fract (a + b)
  have hcast : ((⌊a + b⌋ : ℤ) : ℝ) =
      (⌊a⌋ : ℝ) + (⌊b⌋ : ℝ) +
        (if 1 ≤ Int.fract a + Int.fract b then (1 : ℝ) else 0) := by
    rw [hfl]; push_cast
    split_ifs <;> simp
  linarith

/-- The exact product rule for second differences over four base
points (the algebraic skeleton of the master identity, Lemma 5.1(iv)
of the parity-discrepancy note): with the values of `c` and `f` at
`n`, `n+d₁`, `n+d₂`, `n+d₁+d₂` written `ca, cb, cc, cd` and
`fa, fb, fc, fd`, the doubly differenced product decomposes into the
doubly differenced `f` weighted by the shifted `c`, two mixed terms,
and the doubly differenced `c` weighted by `f`. -/
theorem second_difference_product_rule
    (ca cb cc cd fa fb fc fd : ℝ) :
    cd * fd - cb * fb - cc * fc + ca * fa =
      cd * (fd - fb - fc + fa) + (cd - cb) * (fb - fa) +
        (cd - cc) * (fc - fa) + (cd - cb - cc + ca) * fa := by
  ring

/-- Parity bridge: `⌊x⌋` is odd exactly when `{x/2} ≥ 1/2`. This is
the exact fractional-part reduction that converts the parity sums of
the discrepancy program into interval discrepancies. -/
theorem floor_odd_iff_half_le_fract_half (x : ℝ) :
    ⌊x⌋ % 2 = 1 ↔ (1 / 2 : ℝ) ≤ Int.fract (x / 2) := by
  obtain ⟨t, ht0, ht1, hx⟩ : ∃ t : ℝ, 0 ≤ t ∧ t < 1 ∧ x = ⌊x⌋ + t :=
    ⟨Int.fract x, Int.fract_nonneg x, Int.fract_lt_one x,
      (Int.floor_add_fract x).symm⟩
  rcases Int.even_or_odd ⌊x⌋ with ⟨q, hq⟩ | ⟨q, hq⟩
  · have hfr : Int.fract (x / 2) = t / 2 := by
      have hx2 : x / 2 = (q : ℝ) + t / 2 := by
        rw [hx, hq]; push_cast; ring
      rw [hx2, Int.fract_intCast_add,
        Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩]
    rw [hfr]
    constructor
    · intro h; exfalso; omega
    · intro h; exfalso; linarith
  · have hfr : Int.fract (x / 2) = (1 + t) / 2 := by
      have hx2 : x / 2 = (q : ℝ) + (1 + t) / 2 := by
        rw [hx, hq]; push_cast; ring
      rw [hx2, Int.fract_intCast_add,
        Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩]
    rw [hfr]
    constructor
    · intro _; linarith
    · intro _; omega

end Problems.Juggler
