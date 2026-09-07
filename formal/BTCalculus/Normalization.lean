import BTCalculus.Derivative

namespace BTCalculus

/-!
Coefficient-vector normalization. Unique balanced expansion is standard;
this file packages the local carry rewrite, value preservation, the LSD
normal form, and a lexicographic termination rank. Global confluence of
the stripped rewrite is proved in `BTCalculus.Confluence`.
-/

def isTrit (c : ℤ) : Prop := c = -1 ∨ c = 0 ∨ c = 1

/-- The least significant digit of any integer is a trit. -/
theorem isTrit_lsdZ (n : ℤ) : isTrit (lsdZ n) :=
  lsdZ_is_trit n

/-- `|lsd n| <= 1`. -/
theorem lsdZ_natAbs_le_one (n : ℤ) : (lsdZ n).natAbs ≤ 1 := by
  rcases lsdZ_is_trit n with h | h | h <;> simp [h]

/-- A coefficient that is not a trit has absolute value at least `2`. -/
theorem not_isTrit_natAbs {c : ℤ} (h : ¬ isTrit c) : 2 ≤ c.natAbs := by
  unfold isTrit at h
  have : c ≠ -1 ∧ c ≠ 0 ∧ c ≠ 1 := by
    refine ⟨?_, ?_, ?_⟩
    · intro eq; exact h (Or.inl eq)
    · intro eq; exact h (Or.inr (Or.inl eq))
    · intro eq; exact h (Or.inr (Or.inr eq))
  have hz : c.natAbs ≠ 0 := by
    intro hz
    exact this.2.1 (Int.natAbs_eq_zero.mp hz)
  have hone : c.natAbs ≠ 1 := by
    intro h1
    have hex : c = 1 ∨ c = -1 := (Int.natAbs_eq_iff (n := 1)).mp h1
    rcases hex with h' | h'
    · exact this.2.2 h'
    · exact this.1 h'
  omega

/-- Normalising a non-trit head strictly shrinks it in absolute value. -/
theorem step_head_abs_lt {c : ℤ} (h : ¬ isTrit c) :
    (lsdZ c).natAbs < c.natAbs := by
  have hc := not_isTrit_natAbs h
  have hr := lsdZ_natAbs_le_one c
  omega

def coeffValue : List ℤ → ℤ
  | [] => 0
  | c :: cs => c + 3 * coeffValue cs

def getCoeff (cs : List ℤ) (i : ℕ) : ℤ :=
  cs.getD i 0

/-- Every coefficient of the empty word is `0`. -/
theorem getCoeff_nil (i : ℕ) : getCoeff [] i = 0 := by
  simp [getCoeff]

/-- The head coefficient of the empty word is a trit. -/
theorem getCoeff_zero_isTrit : isTrit (getCoeff [] 0) := by
  simp [getCoeff, isTrit]

def addHead (q : ℤ) : List ℤ → List ℤ
  | [] => [q]
  | c :: cs => (c + q) :: cs

/-- `addHead` adds its argument to the value. -/
theorem addHead_value (q : ℤ) (cs : List ℤ) :
    coeffValue (addHead q cs) = coeffValue cs + q := by
  cases cs with
  | nil =>
    simp [addHead, coeffValue]
  | cons c rest =>
    simp [addHead, coeffValue, add_comm, add_left_comm, add_assoc]

/-- One rewrite at the LSD. Legal whenever the head is not a trit. -/
def stepZero : List ℤ → List ℤ
  | [] => []
  | c :: cs => lsdZ c :: addHead (DZ c) cs

/-- The head-normalising step preserves the value. -/
theorem stepZero_value (cs : List ℤ) :
    coeffValue (stepZero cs) = coeffValue cs := by
  cases cs with
  | nil => rfl
  | cons c rest =>
    simp [stepZero, coeffValue, addHead_value]
    have h := decomp c
    linarith

/-- Abstract one-step relation: rewrite at a chosen index. -/
def step : List ℤ → ℕ → List ℤ
  | cs, 0 => stepZero cs
  | [], _n + 1 => []
  | c :: cs, n + 1 => c :: step cs n

/-- The normalising step at any index preserves the value. -/
theorem step_value (cs : List ℤ) (i : ℕ) :
    coeffValue (step cs i) = coeffValue cs := by
  induction cs generalizing i with
  | nil =>
    cases i with
    | zero => rfl
    | succ _ => rfl
  | cons c rest ih =>
    cases i with
    | zero =>
      simpa [step] using stepZero_value (c :: rest)
    | succ n =>
      simp [step, coeffValue, ih]

def absList (cs : List ℤ) : List ℕ :=
  cs.map Int.natAbs

/-- The head step strictly decreases the absolute-value lexicographic rank. -/
theorem stepZero_lex {c : ℤ} (cs : List ℤ) (h : ¬ isTrit c) :
    List.Lex (· < ·) (absList (stepZero (c :: cs))) (absList (c :: cs)) := by
  have hlt := step_head_abs_lt h
  simp [absList, stepZero]
  exact List.Lex.rel hlt

/-- The step at index `0` strictly decreases the abs-lex rank. -/
theorem step_lex_zero {c : ℤ} (cs : List ℤ) (h : ¬ isTrit c) :
    List.Lex (· < ·) (absList (step (c :: cs) 0)) (absList (c :: cs)) := by
  simpa [step] using stepZero_lex cs h

/-- A decrease at index `n` lifts to a decrease at index `n + 1`. -/
theorem step_lex_succ {c : ℤ} {cs : List ℤ} {n : ℕ}
    (h : List.Lex (· < ·) (absList (step cs n)) (absList cs)) :
    List.Lex (· < ·) (absList (step (c :: cs) (n + 1))) (absList (c :: cs)) := by
  simp only [absList, step, List.map_cons]
  exact List.Lex.cons h

/-- `|3 D n| = 3 |D n|`. -/
theorem DZ_natAbs_mul_three (n : ℤ) :
    (3 * DZ n).natAbs = 3 * (DZ n).natAbs := by
  simp [Int.natAbs_mul]

/-- `n - lsd n = 3 D n`: the digit-and-carry split of an integer. -/
theorem sub_lsd_eq_three_DZ (n : ℤ) : n - lsdZ n = 3 * DZ n := by
  have h := decomp n
  linarith

/-- Algebraic single-coefficient carry bound: `3 |q| ≤ |c| + 1`. -/
theorem DZ_carry_bound (n : ℤ) :
    3 * (DZ n).natAbs ≤ n.natAbs + 1 := by
  have hsub := sub_lsd_eq_three_DZ n
  have htri : (n - lsdZ n).natAbs ≤ n.natAbs + (lsdZ n).natAbs :=
    Int.natAbs_sub_le n (lsdZ n)
  have hr := lsdZ_natAbs_le_one n
  have h3 : (3 * DZ n).natAbs = 3 * (DZ n).natAbs := DZ_natAbs_mul_three n
  have : 3 * (DZ n).natAbs ≤ n.natAbs + (lsdZ n).natAbs := by
    rw [← h3, ← hsub]
    exact htri
  omega

/-- Dual lower estimate: `|n| ≤ 3 |DZ n| + 1`. -/
theorem DZ_carry_lower (n : ℤ) :
    n.natAbs ≤ 3 * (DZ n).natAbs + 1 := by
  have hn : n = lsdZ n + 3 * DZ n := decomp n
  have hr := lsdZ_natAbs_le_one n
  have hadd := Int.natAbs_add_le (lsdZ n) (3 * DZ n)
  have h3 : (3 * DZ n).natAbs = 3 * (DZ n).natAbs := DZ_natAbs_mul_three n
  have hnabs : n.natAbs = (lsdZ n + 3 * DZ n).natAbs := congrArg Int.natAbs hn
  omega

/-- Bound for a coefficient in `[-B, B]` with no incoming carry. -/
theorem DZ_le_of_abs_le {n : ℤ} {B : ℕ} (h : n.natAbs ≤ B) :
    (DZ n).natAbs ≤ (B + 1) / 3 := by
  have hb := DZ_carry_bound n
  have hmul : 3 * (DZ n).natAbs ≤ B + 1 := by omega
  have : (DZ n).natAbs * 3 ≤ B + 1 := by
    rw [Nat.mul_comm]
    exact hmul
  exact (Nat.le_div_iff_mul_le (by decide : (0 : ℕ) < 3)).2 this

/-- `D` strictly shrinks a nonzero integer in absolute value. -/
theorem DZ_natAbs_lt {n : ℤ} (hn : n ≠ 0) : (DZ n).natAbs < n.natAbs := by
  have hb := DZ_carry_bound n
  by_cases hq : DZ n = 0
  · rw [hq, Int.natAbs_zero]
    exact Int.natAbs_pos.mpr hn
  · have hk : 0 < (DZ n).natAbs := Int.natAbs_pos.mpr hq
    omega

set_option linter.unusedVariables false in
def encodeZ (n : ℤ) : List ℤ :=
  if h0 : n = 0 then
    [0]
  else
    let q := DZ n
    if q = 0 then [lsdZ n] else lsdZ n :: encodeZ q
termination_by n.natAbs
decreasing_by
  exact DZ_natAbs_lt h0

/-- `encodeZ 0 = [0]`. -/
theorem encodeZ_zero : encodeZ 0 = [0] := by
  rw [encodeZ]
  simp

/-- Recursive form of `encodeZ` on a nonzero integer. -/
theorem encodeZ_of_ne_zero {n : ℤ} (hn : n ≠ 0) :
    encodeZ n =
      if DZ n = 0 then [lsdZ n] else lsdZ n :: encodeZ (DZ n) := by
  rw [encodeZ, dif_neg hn]

/-- `encodeZ` is value-preserving: `value (encodeZ n) = n`. -/
theorem encodeZ_value (n : ℤ) : coeffValue (encodeZ n) = n := by
  induction hn : n.natAbs using Nat.strong_induction_on generalizing n with
  | h k ih =>
    by_cases hz : n = 0
    · subst hz
      simp [encodeZ_zero, coeffValue]
    · have hform := encodeZ_of_ne_zero hz
      by_cases hq : DZ n = 0
      · simp [hform, hq, coeffValue]
        have hde := decomp n
        simp [hq] at hde
        linarith
      · have hih := ih (DZ n).natAbs (by
          have := DZ_natAbs_lt hz
          omega) (DZ n) rfl
        simp [hform, hq, coeffValue, hih]
        have hde := decomp n
        linarith

/-- Strategy A / D normal form: digits of `encode(value)`. -/
def normalizeLSD (cs : List ℤ) : List ℤ :=
  encodeZ (coeffValue cs)

/-- Normalisation preserves the value of a coefficient word. -/
theorem normalizeLSD_value (cs : List ℤ) :
    coeffValue (normalizeLSD cs) = coeffValue cs := by
  simpa [normalizeLSD] using encodeZ_value (coeffValue cs)

/-- A normalising step does not change the normal form. -/
theorem step_preserves_normalize (cs : List ℤ) (i : ℕ) :
    normalizeLSD (step cs i) = normalizeLSD cs := by
  simp [normalizeLSD, step_value]

def allTrits : List ℤ → Prop
  | [] => True
  | c :: cs => isTrit c ∧ allTrits cs

/-- The empty word is all trits. -/
theorem allTrits_nil : allTrits [] := trivial

/-- `encodeZ n` consists of trits. -/
theorem encodeZ_trits (n : ℤ) : allTrits (encodeZ n) := by
  induction hn : n.natAbs using Nat.strong_induction_on generalizing n with
  | h k ih =>
    by_cases hz : n = 0
    · subst hz
      simp [encodeZ_zero, allTrits, isTrit]
    · have hform := encodeZ_of_ne_zero hz
      have hr : isTrit (lsdZ n) := isTrit_lsdZ n
      by_cases hq : DZ n = 0
      · simp [hform, hq, allTrits, hr]
      · have hih := ih (DZ n).natAbs (by
          have := DZ_natAbs_lt hz
          omega) (DZ n) rfl
        simp [hform, hq, allTrits, hr, hih]

/-- The normal form consists of trits. -/
theorem normalizeLSD_trits (cs : List ℤ) : allTrits (normalizeLSD cs) :=
  encodeZ_trits (coeffValue cs)

def irreducible (cs : List ℤ) : Prop :=
  ∀ i : ℕ, isTrit (getCoeff cs i)

/-- An all-trits word is irreducible. -/
theorem allTrits_irreducible : ∀ cs, allTrits cs → irreducible cs
  | [], _ => by
    intro i
    simp [irreducible, getCoeff, isTrit]
  | c :: cs, h => by
    intro i
    cases i with
    | zero =>
      simpa [getCoeff, List.getD] using h.1
    | succ n =>
      have := allTrits_irreducible cs h.2 n
      simpa [getCoeff, List.getD] using this

/-- Indexing past the head drops it. -/
theorem getCoeff_cons_succ (c : ℤ) (cs : List ℤ) (n : ℕ) :
    getCoeff (c :: cs) (n + 1) = getCoeff cs n := by
  simp [getCoeff, List.getD]

/-- Irreducibility of a cons splits into a trit head and an irreducible tail. -/
theorem irreducible_cons {c : ℤ} {cs : List ℤ} (h : irreducible (c :: cs)) :
    isTrit c ∧ irreducible cs := by
  refine ⟨?_, ?_⟩
  · simpa [irreducible, getCoeff, List.getD] using h 0
  · intro i
    simpa [getCoeff_cons_succ] using h (i + 1)

/-- An irreducible word is all trits. -/
theorem irreducible_allTrits : ∀ cs, irreducible cs → allTrits cs
  | [], _ => trivial
  | c :: cs, h => by
    have hc := irreducible_cons h
    exact ⟨hc.1, irreducible_allTrits cs hc.2⟩

/-- Irreducible and all-trits are the same condition. -/
theorem irreducible_iff_allTrits (cs : List ℤ) :
    irreducible cs ↔ allTrits cs :=
  ⟨irreducible_allTrits cs, allTrits_irreducible cs⟩

/-- Canonical in the Lean sense: every stored coefficient is a trit.
High zeros are allowed; Python `CoeffWord` strips them separately. -/
def isCanonical (cs : List ℤ) : Prop :=
  irreducible cs

/-- The normal form is irreducible. -/
theorem normalizeLSD_irreducible (cs : List ℤ) :
    irreducible (normalizeLSD cs) :=
  allTrits_irreducible _ (normalizeLSD_trits cs)

/-- On a singleton, normalisation is `encodeZ`: `normalizeLSD [n] = encodeZ n`. -/
theorem encodeZ_normalize (n : ℤ) :
    normalizeLSD [n] = encodeZ n := by
  simp [normalizeLSD, coeffValue]

/-- Head rewrite of a singleton is value-preserving. -/
theorem stepZero_singleton (n : ℤ) :
    coeffValue (stepZero [n]) = n := by
  simpa [stepZero, addHead, coeffValue] using (decomp n).symm

end BTCalculus
