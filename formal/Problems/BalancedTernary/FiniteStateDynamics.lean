import BTCalculus.Normalization

namespace Problems.BalancedTernary

open BTCalculus

/-!
Doubled-trit residual dynamics. The successor is the existing balanced
quotient `DZ (c + 2 d)` on a trit `d`. Gain `3 * DZ` is a synthetic
perturbation, not value-preserving normalization.
-/

def doubledNext (c d : ℤ) : ℤ :=
  DZ (c + 2 * d)

def doubledOut (c d : ℤ) : ℤ :=
  lsdZ (c + 2 * d)

def carryGain (gain c d : ℤ) : ℤ :=
  gain * DZ (c + 2 * d)

def inBox (c : ℤ) : Prop :=
  c.natAbs ≤ 1

/-- Digit/carry decomposition of the doubled stream: `c + 2d = doubledOut c d + 3 * doubledNext c d`. -/
theorem doubled_decomp (c d : ℤ) :
    c + 2 * d = doubledOut c d + 3 * doubledNext c d := by
  simpa [doubledOut, doubledNext] using decomp (c + 2 * d)

/-- `|n| <= 1` exactly when `n` is `-1`, `0` or `1`. -/
theorem natAbs_le_one_iff {c : ℤ} :
    c.natAbs ≤ 1 ↔ c = -1 ∨ c = 0 ∨ c = 1 := by
  constructor
  · intro h
    have : c.natAbs = 0 ∨ c.natAbs = 1 := by omega
    rcases this with h0 | h1
    · exact Or.inr (Or.inl (Int.natAbs_eq_zero.mp h0))
    · have hex := (Int.natAbs_eq_iff (n := 1)).mp h1
      rcases hex with hpos | hneg
      · exact Or.inr (Or.inr hpos)
      · exact Or.inl hneg
  · intro h
    rcases h with h | h | h <;> simp [h]

/-- A trit has absolute value at most `1`. -/
theorem isTrit_natAbs {d : ℤ} (hd : isTrit d) : d.natAbs ≤ 1 := by
  rcases hd with h | h | h <;> simp [h]

/-- `lsd` is odd: `lsd (-n) = -lsd n`. -/
theorem lsdZ_neg (n : ℤ) : lsdZ (-n) = -lsdZ n := by
  have ht := lsdZ_is_trit n
  have hmod := (lsdZ_mod n).neg
  have htrit : -lsdZ n = -1 ∨ -lsdZ n = 0 ∨ -lsdZ n = 1 := by
    rcases ht with h | h | h <;> simp [h]
  exact lsdZ_unique htrit hmod

/-- `D` is odd: `D (-n) = -D n`. -/
theorem DZ_neg (n : ℤ) : DZ (-n) = -DZ n := by
  have hpos := decomp n
  have hneg := decomp (-n)
  have hr := lsdZ_neg n
  linarith

/-- Carry and output are both odd in their arguments: negating `c` and `d` negates `doubledNext` and negates the emitted trit. -/
theorem doubledTrit_sign (c d : ℤ) :
    doubledNext (-c) (-d) = -doubledNext c d ∧
      doubledOut (-c) (-d) = -doubledOut c d := by
  have harg : -c + 2 * (-d) = -(c + 2 * d) := by ring
  constructor
  · simp only [doubledNext]
    rw [harg, DZ_neg]
  · simp only [doubledOut]
    rw [harg, lsdZ_neg]

/-- `1` is reachable from carry `0`: `doubledNext 0 1 = 1`. -/
theorem doubledTrit_reach_one : doubledNext 0 1 = 1 := by
  native_decide

/-- `-1` is reachable from carry `0`: `doubledNext 0 (-1) = -1`. -/
theorem doubledTrit_reach_neg : doubledNext 0 (-1) = -1 := by
  native_decide

/-- The carry stays in the box `{-1, 0, 1}` when it starts there and `d` is a trit. -/
theorem doubledNext_abs_le_one {c d : ℤ}
    (hc : inBox c) (hd : isTrit d) :
    inBox (doubledNext c d) := by
  have hc' := natAbs_le_one_iff.mp hc
  rcases hc' with rfl | rfl | rfl <;> rcases hd with rfl | rfl | rfl <;>
    (simp [inBox, doubledNext]; native_decide)

/-- Closure: the doubled-trit carry never leaves `{-1, 0, 1}`. -/
theorem doubledTrit_closure {c d : ℤ}
    (hc : inBox c) (hd : isTrit d) :
    inBox (doubledNext c d) :=
  doubledNext_abs_le_one hc hd

/-- `V(c) = |c|` strictly decreases under `c |-> doubledNext c d` whenever `|c| >= 2` and `d` is a trit -- the Lyapunov function that forces the carry back into the box. -/
theorem doubledTrit_lyapunov {c d : ℤ}
    (hc : 2 ≤ c.natAbs) (hd : isTrit d) :
    (doubledNext c d).natAbs < c.natAbs := by
  have hd' := isTrit_natAbs hd
  have hsum : (c + 2 * d).natAbs ≤ c.natAbs + 2 := by
    have hle := Int.natAbs_add_le c (2 * d)
    have h2 : (2 * d).natAbs = 2 * d.natAbs := by
      simp [Int.natAbs_mul]
    omega
  have hdz := DZ_le_of_abs_le (B := c.natAbs + 2) hsum
  have hle : (doubledNext c d).natAbs ≤ (c.natAbs + 2 + 1) / 3 := by
    simpa [doubledNext] using hdz
  have hdiv : (c.natAbs + 2 + 1) / 3 < c.natAbs := by
    have hsum3 : c.natAbs + 2 + 1 = c.natAbs + 3 := by omega
    rw [hsum3, Nat.div_lt_iff_lt_mul (by decide : (0 : ℕ) < 3)]
    omega
  omega

/-- Flushing with digit `0` from any in-box carry returns carry `0`. -/
theorem doubledTrit_flush {c : ℤ} (hc : inBox c) :
    doubledNext c 0 = 0 := by
  have hcases := natAbs_le_one_iff.mp hc
  rcases hcases with rfl | rfl | rfl <;> (simp [doubledNext]; native_decide)

/-- `lsd (3n + 2) = -1`. -/
theorem lsdZ_three_mul_add_two (n : ℤ) : lsdZ (3 * n + 2) = -1 := by
  have hmod : (3 * n + 2) % 3 = 2 := by
    have : (3 * n) % 3 = 0 := by simp
    rw [Int.add_emod, this]
    norm_num
  simp [lsdZ, hmod]

/-- `D (3n + 2) = n + 1`. -/
theorem DZ_three_mul_add_two (n : ℤ) : DZ (3 * n + 2) = n + 1 := by
  unfold DZ
  rw [lsdZ_three_mul_add_two]
  have hrewrite : (3 * n + 2 - -1) = 3 * (n + 1) := by ring
  rw [hrewrite]
  exact Int.mul_ediv_cancel_left (n + 1) (by decide : (3 : ℤ) ≠ 0)

def carryGain3 : ℕ → ℤ
  | 0 => 0
  | n + 1 => 3 * DZ (carryGain3 n + 2)

/-- `carryGain3 n = 3n` along the all-`+1` word. -/
theorem carryGain3_eq (n : ℕ) : carryGain3 n = 3 * (n : ℤ) := by
  induction n with
  | zero => simp [carryGain3]
  | succ n ih =>
    simp [carryGain3, ih, DZ_three_mul_add_two]

/-- `carryGain3` is unbounded: no `B` bounds every `|carryGain3 n|`. -/
theorem carryGain3_unbounded (B : ℕ) :
    ∃ n : ℕ, B < (carryGain3 n).natAbs := by
  refine ⟨B + 1, ?_⟩
  simp [carryGain3_eq]
  omega

def outSig (c : ℤ) : ℤ × ℤ × ℤ :=
  (doubledOut c (-1), doubledOut c 0, doubledOut c 1)

/-- The three carries `-1`, `0` and `1` have pairwise distinct Mealy output signatures, so the three-state machine is minimal. -/
theorem doubledTrit_outputSignatures_distinct :
    outSig 0 ≠ outSig 1 ∧ outSig 0 ≠ outSig (-1) ∧ outSig 1 ≠ outSig (-1) := by
  native_decide

end Problems.BalancedTernary
