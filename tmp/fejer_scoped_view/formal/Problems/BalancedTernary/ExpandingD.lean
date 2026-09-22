import BTCalculus.Integral
import BTCalculus.Normalization

namespace Problems.BalancedTernary

open BTCalculus
open Representation.Words

/-!
Expanding map ``T(n) = 3n - lsd(n)``. This is not laboratory ``DZ``.
Canonical ``T`` is the section ``n ↦ -lsd(n) + 3n``. The LSD
observable of the ``T``-orbit is exactly the current LSD.
-/

/-- The expanding map `T n = 3 * n - lsdZ n`. This is not laboratory `DZ`. -/
def expandingD (n : ℤ) : ℤ :=
  3 * n - lsdZ n

/-- The gain-`lambda` family `T_lambda n = 3 * n - lambda * lsdZ n`; gain `1` is
`expandingD`. -/
def expandingDGain (gain n : ℤ) : ℤ :=
  3 * n - gain * lsdZ n

/-- The expanding map in section shape: `T n = -lsdZ n + 3 * n`, i.e. the section
`I_a` taken at the varying digit `a = -lsdZ n` rather than at a constant one. -/
theorem expandingD_eq_IZ_shape (n : ℤ) :
    expandingD n = -lsdZ n + 3 * n := by
  unfold expandingD
  ring

/-- `T n` is congruent to `-lsdZ n` mod `3`. -/
theorem expandingD_mod (n : ℤ) : expandingD n ≡ -lsdZ n [ZMOD 3] := by
  unfold expandingD
  refine Int.modEq_iff_dvd.mpr ⟨-n, by ring⟩

/-- The negated least significant digit is again a trit. -/
theorem neg_lsdZ_is_trit (n : ℤ) :
    -lsdZ n = -1 ∨ -lsdZ n = 0 ∨ -lsdZ n = 1 := by
  rcases lsdZ_is_trit n with h | h | h <;> simp [h]

/-- One step flips the least significant digit: `lsdZ (T n) = -lsdZ n`. -/
theorem lsdZ_expandingD (n : ℤ) : lsdZ (expandingD n) = -lsdZ n :=
  lsdZ_unique (neg_lsdZ_is_trit n) (expandingD_mod n)

/-- `T n` in terms of the carry and digit of `n`: `T n = 9 * DZ n + 2 * lsdZ n`. -/
theorem expandingD_decomp (n : ℤ) :
    expandingD n = 9 * DZ n + 2 * lsdZ n := by
  unfold expandingD
  have h := decomp n
  linarith

/-- Laboratory `DZ` is a left inverse of `T`: `DZ (T n) = n`. -/
theorem DZ_expandingD (n : ℤ) : DZ (expandingD n) = n := by
  have hdecomp := decomp (expandingD n)
  have hlsd := lsdZ_expandingD n
  have hexpr : expandingD n = 3 * n - lsdZ n := rfl
  linarith

/-- `T` on a section: `T (IZ a x) = 9 * x + 2 * a.toInt`. -/
theorem expandingD_IZ (a : Representation.Words.Trit) (x : ℤ) :
    expandingD (IZ a x) = 9 * x + 2 * a.toInt := by
  unfold expandingD
  rw [lsdZ_IZ]
  unfold IZ
  ring

/-- The digit emitted after a section step is `-a`, independent of the higher-digit
residual `x`: `lsdZ (T (IZ a x)) = -a.toInt`. -/
theorem lsdZ_expandingD_IZ (a : Representation.Words.Trit) (x : ℤ) :
    lsdZ (expandingD (IZ a x)) = -a.toInt := by
  rw [lsdZ_expandingD, lsdZ_IZ]

/-- The digit alternates along the whole orbit: `lsdZ (T^[k] n) = (-1)^k * lsdZ n`. Every
future least-significant-digit observation is a function of `lsdZ n` alone. -/
theorem lsdZ_iterate_expandingD (k : ℕ) (n : ℤ) :
    lsdZ (expandingD^[k] n) = (-1 : ℤ) ^ k * lsdZ n := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', lsdZ_expandingD, ih]
    ring

/-- `T` moves a positive integer strictly up. -/
theorem expandingD_gt_of_pos {n : ℤ} (hn : 0 < n) : n < expandingD n := by
  have hr := lsdZ_is_trit n
  unfold expandingD
  rcases hr with h | h | h <;> nlinarith

/-- `T` moves a negative integer strictly down. -/
theorem expandingD_lt_of_neg {n : ℤ} (hn : n < 0) : expandingD n < n := by
  have hr := lsdZ_is_trit n
  unfold expandingD
  rcases hr with h | h | h <;> nlinarith

/-- `T` strictly increases absolute value away from `0`. -/
theorem expandingD_abs_lt {n : ℤ} (hn : n ≠ 0) :
    |n| < |expandingD n| := by
  rcases lt_trichotomy n 0 with hneg | h0 | hpos
  · have ht := expandingD_lt_of_neg hneg
    have hT : expandingD n < 0 := lt_trans ht hneg
    rw [abs_of_neg hneg, abs_of_neg hT]
    omega
  · exact (hn h0).elim
  · have ht := expandingD_gt_of_pos hpos
    have hT : 0 < expandingD n := lt_trans hpos ht
    rw [abs_of_pos hpos, abs_of_pos hT]
    exact ht

/-- The `natAbs` form of the expansion: `|n| < |T n|` for `n != 0`. -/
theorem expandingD_expands {n : ℤ} (hn : n ≠ 0) :
    n.natAbs < (expandingD n).natAbs := by
  have h := expandingD_abs_lt hn
  have : (n.natAbs : ℤ) < ((expandingD n).natAbs : ℤ) := by
    simpa [Int.natCast_natAbs] using h
  exact Int.ofNat_lt.mp this

/-- `T 1 = 2`. -/
theorem expandingD_one : expandingD 1 = 2 := by native_decide

/-- `T` is not a contraction in magnitude: `|T n| <= |n|` fails, witnessed at `n = 1`
where `T 1 = 2`. -/
theorem magnitude_contraction_false :
    ¬ ∀ n : ℤ, (expandingD n).natAbs ≤ n.natAbs := by
  intro h
  have := h 1
  rw [expandingD_one] at this
  exact (by native_decide : ¬ (2 : ℕ) ≤ 1) this

/-- Gain `1` recovers `expandingD`. -/
theorem expandingDGain_one (n : ℤ) : expandingDGain 1 n = expandingD n := by
  unfold expandingDGain expandingD
  ring

/-- `T_2 n` is congruent to `lsdZ n` mod `3`. -/
theorem expandingDGain_two_mod (n : ℤ) :
    expandingDGain 2 n ≡ lsdZ n [ZMOD 3] := by
  unfold expandingDGain
  refine Int.modEq_iff_dvd.mpr ⟨lsdZ n - n, by ring⟩

/-- Gain `2` fixes the digit rather than flipping it: `lsdZ (T_2 n) = lsdZ n`. -/
theorem lsdZ_expandingDGain_two (n : ℤ) :
    lsdZ (expandingDGain 2 n) = lsdZ n :=
  lsdZ_unique (lsdZ_is_trit n) (expandingDGain_two_mod n)

/-- Gain `3` is nine times the carry: `T_3 n = 9 * DZ n`. -/
theorem expandingDGain_three_eq (n : ℤ) : expandingDGain 3 n = 9 * DZ n := by
  unfold expandingDGain
  have h := decomp n
  linarith

/-- Gain `3` annihilates the digit: `lsdZ (T_3 n) = 0`. -/
theorem lsdZ_expandingDGain_three (n : ℤ) :
    lsdZ (expandingDGain 3 n) = 0 := by
  rw [expandingDGain_three_eq]
  apply lsdZ_unique (Or.inr (Or.inl rfl))
  refine Int.modEq_iff_dvd.mpr ⟨-3 * DZ n, by ring⟩

/-- The three digit signatures of one `T` step: `lsdZ (T 0) = 0`, `lsdZ (T 1) = -1`,
`lsdZ (T (-1)) = 1`. -/
theorem expandingD_three_signatures :
    lsdZ (expandingD 0) = 0 ∧
      lsdZ (expandingD 1) = -1 ∧
      lsdZ (expandingD (-1)) = 1 := by
  rw [lsdZ_expandingD, lsdZ_expandingD, lsdZ_expandingD]
  native_decide

/-- A trit is its own least significant digit. -/
theorem lsdZ_of_isTrit {a : ℤ} (ha : isTrit a) : lsdZ a = a :=
  lsdZ_unique ha (Int.ModEq.refl a)

/-- Trits are closed under negation. -/
theorem neg_isTrit {r : ℤ} (hr : isTrit r) : isTrit (-r) := by
  rcases hr with h | h | h <;> simp [isTrit, h]

/-- The one-digit observable is closed under `T` on trits: `lsdZ (T r)` is a trit
whenever `r` is. -/
theorem expandingD_residue_T {r : ℤ} (hr : isTrit r) :
    isTrit (lsdZ (expandingD r)) := by
  rw [lsdZ_expandingD, lsdZ_of_isTrit hr]
  exact neg_isTrit hr

/-- Every `Trit` value is a trit as an integer. -/
theorem expandingD_residue_I (a : Representation.Words.Trit) :
    isTrit a.toInt :=
  trit_toInt_is_trit a

/-- Both halves of trit closure together: `T` keeps the digit observable inside the trits,
and section labels are trits. -/
theorem expandingD_residue_closure :
    (∀ r : ℤ, isTrit r → isTrit (lsdZ (expandingD r))) ∧
      (∀ a : Representation.Words.Trit, isTrit a.toInt) :=
  ⟨fun _ hr => expandingD_residue_T hr, expandingD_residue_I⟩

/-- Length-2 integer jet, LSD-first: `(lsdZ n, lsdZ (DZ n))`. -/
def jet2 (n : ℤ) : ℤ × ℤ :=
  (lsdZ n, lsdZ (DZ n))

/-- The order-2 jet of one step: `jet2 (T n) = (-lsdZ n, lsdZ n)` -- it depends on the
first input digit only. -/
theorem jet2_expandingD (n : ℤ) :
    jet2 (expandingD n) = (-lsdZ n, lsdZ n) := by
  unfold jet2
  rw [lsdZ_expandingD, DZ_expandingD]

/-- The order-2 jet of a section: `jet2 (IZ a x) = (a.toInt, lsdZ x)`. -/
theorem jet2_IZ (a : Representation.Words.Trit) (x : ℤ) :
    jet2 (IZ a x) = (a.toInt, lsdZ x) := by
  unfold jet2
  rw [lsdZ_IZ, D_after_I]

/-- The jet reads back a trit window: `jet2 (a + 3 * b) = (a, b)` for trits `a`, `b`. -/
theorem jet2_of_window {a b : ℤ} (ha : isTrit a) (hb : isTrit b) :
    jet2 (a + 3 * b) = (a, b) := by
  unfold jet2
  have hlsd : lsdZ (a + 3 * b) = a :=
    lsdZ_unique ha (Int.modEq_iff_dvd.mpr ⟨-b, by ring⟩)
  have hdz : DZ (a + 3 * b) = b := by
    have hde := decomp (a + 3 * b)
    rw [hlsd] at hde
    linarith
  rw [hlsd, hdz, lsdZ_of_isTrit hb]

/-- Every trit window `(a, b)` is sent to `(-a, a)`: `jet2 (T (a + 3 * b)) = (-a, a)`, so
the second input digit is discarded. -/
theorem jet2_residue_closure {a b : ℤ} (ha : isTrit a) (hb : isTrit b) :
    jet2 (expandingD (a + 3 * b)) = (-a, a) := by
  have hn := jet2_of_window ha hb
  have hlsd : lsdZ (a + 3 * b) = a := by
    have := congrArg Prod.fst hn
    simpa [jet2] using this
  rw [jet2_expandingD, hlsd]

/-- A multiple of `3` has least significant digit `0`. -/
theorem lsdZ_mul3 (m : ℤ) : lsdZ (3 * m) = 0 :=
  lsdZ_unique (Or.inr (Or.inl rfl)) (Int.modEq_iff_dvd.mpr ⟨-m, by ring⟩)

/-- The carry after a gain-`2` step: `DZ (T_2 n) = 3 * DZ n`. -/
theorem DZ_expandingDGain_two (n : ℤ) :
    DZ (expandingDGain 2 n) = 3 * DZ n := by
  have hde := decomp (expandingDGain 2 n)
  rw [lsdZ_expandingDGain_two] at hde
  have hn := decomp n
  unfold expandingDGain at *
  linarith

/-- The order-2 jet at gain `2`: `jet2 (T_2 n) = (lsdZ n, 0)`. -/
theorem jet2_expandingDGain_two (n : ℤ) :
    jet2 (expandingDGain 2 n) = (lsdZ n, 0) := by
  unfold jet2
  rw [lsdZ_expandingDGain_two, DZ_expandingDGain_two, lsdZ_mul3]

/-- The carry after a gain-`3` step: `DZ (T_3 n) = 3 * DZ n`. -/
theorem DZ_expandingDGain_three (n : ℤ) :
    DZ (expandingDGain 3 n) = 3 * DZ n := by
  rw [expandingDGain_three_eq]
  have hde := decomp (9 * DZ n)
  have hlsd : lsdZ (9 * DZ n) = 0 := by
    simpa [expandingDGain_three_eq] using lsdZ_expandingDGain_three n
  rw [hlsd] at hde
  linarith

/-- The order-2 jet at gain `3` is constant: `jet2 (T_3 n) = (0, 0)`. -/
theorem jet2_expandingDGain_three (n : ℤ) :
    jet2 (expandingDGain 3 n) = (0, 0) := by
  unfold jet2
  rw [lsdZ_expandingDGain_three, DZ_expandingDGain_three, lsdZ_mul3]

/-- Length-3 integer jet, LSD-first: `(lsd, lsd∘DZ, lsd∘DZ²)`. -/
def jet3 (n : ℤ) : ℤ × ℤ × ℤ :=
  (lsdZ n, lsdZ (DZ n), lsdZ (DZ (DZ n)))

/-- `jet2` is the length-2 prefix of `jet3`. -/
theorem jet2_eq_prefix_jet3 (n : ℤ) :
    jet2 n = ((jet3 n).1, (jet3 n).2.1) :=
  rfl

/-- The order-3 jet of one step: `jet3 (T n) = (-lsdZ n, lsdZ n, lsdZ (DZ n))`. -/
theorem jet3_expandingD (n : ℤ) :
    jet3 (expandingD n) = (-lsdZ n, lsdZ n, lsdZ (DZ n)) := by
  unfold jet3
  rw [lsdZ_expandingD, DZ_expandingD]

/-- The order-3 jet of a step factors through the order-2 jet of the input:
`jet3 (T n) = (-(jet2 n).1, (jet2 n).1, (jet2 n).2)`. The third input digit is
discarded. -/
theorem jet3_factors_through_jet2 (n : ℤ) :
    jet3 (expandingD n) = (-(jet2 n).1, (jet2 n).1, (jet2 n).2) := by
  unfold jet3 jet2
  rw [lsdZ_expandingD, DZ_expandingD]

/-- Truncating the order-3 jet of a step gives its order-2 jet. -/
theorem jet3_expandingD_commutes_with_jet2 (n : ℤ) :
    jet2 (expandingD n) = ((jet3 (expandingD n)).1, (jet3 (expandingD n)).2.1) :=
  jet2_eq_prefix_jet3 (expandingD n)

/-- The order-3 jet of a section: `jet3 (IZ a x) = (a.toInt, lsdZ x, lsdZ (DZ x))`. -/
theorem jet3_IZ (a : Representation.Words.Trit) (x : ℤ) :
    jet3 (IZ a x) = (a.toInt, lsdZ x, lsdZ (DZ x)) := by
  unfold jet3
  rw [lsdZ_IZ, D_after_I]

/-- The jet reads back a three-trit window: `jet3 (a + 3 * b + 9 * c) = (a, b, c)`. -/
theorem jet3_of_window {a b c : ℤ} (ha : isTrit a) (hb : isTrit b) (hc : isTrit c) :
    jet3 (a + 3 * b + 9 * c) = (a, b, c) := by
  unfold jet3
  have hlsd : lsdZ (a + 3 * b + 9 * c) = a :=
    lsdZ_unique ha (Int.modEq_iff_dvd.mpr ⟨-(b + 3 * c), by ring⟩)
  have hdz : DZ (a + 3 * b + 9 * c) = b + 3 * c := by
    have hde := decomp (a + 3 * b + 9 * c)
    rw [hlsd] at hde
    linarith
  have hwin := jet2_of_window hb hc
  unfold jet2 at hwin
  rw [hlsd, hdz]
  exact congrArg (fun p : ℤ × ℤ => (a, p)) hwin

/-- A three-trit window `(a, b, c)` is sent to `(-a, a, b)`, so `c` is discarded. -/
theorem jet3_residue_closure {a b c : ℤ} (ha : isTrit a) (hb : isTrit b)
    (hc : isTrit c) :
    jet3 (expandingD (a + 3 * b + 9 * c)) = (-a, a, b) := by
  have hwin := jet3_of_window ha hb hc
  have hlsd : lsdZ (a + 3 * b + 9 * c) = a := by
    simpa [jet3] using congrArg Prod.fst hwin
  have hmid : lsdZ (DZ (a + 3 * b + 9 * c)) = b := by
    simpa [jet3] using congrArg (fun p : ℤ × ℤ × ℤ => p.2.1) hwin
  rw [jet3_expandingD, hlsd, hmid]

/-- The carry of `3 * m` is `m`. -/
theorem DZ_mul3 (m : ℤ) : DZ (3 * m) = m := by
  have hde := decomp (3 * m)
  rw [lsdZ_mul3] at hde
  linarith

/-- The order-3 jet at gain `2`: `jet3 (T_2 n) = (lsdZ n, 0, lsdZ (DZ n))`. -/
theorem jet3_expandingDGain_two (n : ℤ) :
    jet3 (expandingDGain 2 n) = (lsdZ n, 0, lsdZ (DZ n)) := by
  unfold jet3
  rw [lsdZ_expandingDGain_two, DZ_expandingDGain_two, lsdZ_mul3, DZ_mul3]

/-- The order-3 jet at gain `3`: `jet3 (T_3 n) = (0, 0, lsdZ (DZ n))`. Gain `3` collapses
the first two coordinates but not the third -- the second input digit survives. -/
theorem jet3_expandingDGain_three (n : ℤ) :
    jet3 (expandingDGain 3 n) = (0, 0, lsdZ (DZ n)) := by
  unfold jet3
  rw [lsdZ_expandingDGain_three, DZ_expandingDGain_three, lsdZ_mul3, DZ_mul3]

end Problems.BalancedTernary
