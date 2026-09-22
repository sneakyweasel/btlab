import Problems.Juggler.CollatzBridge
import Mathlib.Data.Rat.Lemmas

/-!
# Rational parity coding of terminating Juggler trajectories

The endpoint is the fixed point `1` of the rational `3n-1` map. Pulling it
back through an actual itinerary gives a code independent of the chosen
hitting time. The reduced denominator is odd, so numerator parity selects
the correct rational branch. Negation gives the `3n+1` orbit.

This file treats the terminating basin only. It does not construct the
infinite 2-adic code or assert that every positive start terminates.
-/

namespace Problems.Juggler.CollatzRational

open CollatzBridge

/-- Inverse branches of the rational `3n-1` map. -/
def pullback : Branch → ℚ → ℚ
  | .even, q => 2 * q
  | .odd, q => (2 * q + 1) / 3

/-- Pull an endpoint back through a prescribed finite word. -/
def pullbackWord : List Branch → ℚ → ℚ
  | [], q => q
  | b :: w, q => pullback b (pullbackWord w q)

/-- Code using the first `d` actual Juggler letters and endpoint `1`. -/
def codeAt (n d : ℕ) : ℚ := pullbackWord (itinerary n d) 1

theorem pullbackWord_affine (w : List Branch) (q : ℚ) :
    3 ^ oddCount w * pullbackWord w q =
      2 ^ w.length * q + (wordConst w : ℚ) := by
  induction w with
  | nil => simp [pullbackWord]
  | cons b w ih =>
    cases b <;>
      simp only [pullbackWord, pullback, oddCount_even_cons, oddCount_odd_cons,
        wordConst_even, wordConst_odd, List.length_cons, Nat.cast_add,
        Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, pow_succ] <;>
      linear_combination 2 * ih

theorem codeAt_formula (n d : ℕ) :
    codeAt n d = ((2 : ℚ) ^ d + wordConst (itinerary n d)) /
      3 ^ oddCount (itinerary n d) := by
  apply (eq_div_iff (by positivity)).2
  simpa [codeAt, itinerary_length, mul_comm] using
    pullbackWord_affine (itinerary n d) (1 : ℚ)

theorem codeAt_zero (n : ℕ) : codeAt n 0 = 1 := rfl

theorem codeAt_succ (n d : ℕ) :
    codeAt n (d + 1) = pullback (bit n) (codeAt (floorPower n) d) := rfl

theorem codeAt_one (d : ℕ) : codeAt 1 d = 1 := by
  induction d with
  | zero => rfl
  | succ d ih => rw [codeAt_succ, floorPower_one, ih]; norm_num [bit, pullback]

/-- Appending the fixed terminal tail does not change a code. -/
theorem codeAt_stable {n d : ℕ} (hd : floorPower^[d] n = 1) (k : ℕ) :
    codeAt n (d + k) = codeAt n d := by
  induction d generalizing n with
  | zero =>
    have hn : n = 1 := hd
    subst n
    simp [codeAt_one]
  | succ d ih =>
    rw [iterate_cons] at hd
    rw [show d + 1 + k = (d + k) + 1 by omega, codeAt_succ, codeAt_succ,
      ih hd]

/-- Any two genuine hitting-time witnesses give the same rational code. -/
theorem codeAt_independent {n d e : ℕ}
    (hd : floorPower^[d] n = 1) (he : floorPower^[e] n = 1) :
    codeAt n d = codeAt n e := by
  rcases le_total d e with h | h
  · simpa [Nat.add_sub_of_le h] using (codeAt_stable hd (e - d)).symm
  · simpa [Nat.add_sub_of_le h] using codeAt_stable he (d - e)

/-- Rational code on the terminating basin; no value is assigned off that basin. -/
noncomputable def terminatingCode (n : ℕ) (h : ReachesOne n) : ℚ :=
  codeAt n (Nat.find h)

theorem terminatingCode_eq_codeAt {n d : ℕ} (h : ReachesOne n)
    (hd : floorPower^[d] n = 1) : terminatingCode n h = codeAt n d :=
  codeAt_independent (Nat.find_spec h) hd

theorem reachesOne_step {n : ℕ} (h : ReachesOne n) : ReachesOne (floorPower n) := by
  obtain ⟨d, hd⟩ := h
  cases d with
  | zero =>
    have hn : n = 1 := hd
    simpa [hn, floorPower_one] using reachesOne_one
  | succ d => exact ⟨d, by simpa [iterate_cons] using hd⟩

theorem terminatingCode_pullback {n : ℕ} (h : ReachesOne n) :
    terminatingCode n h =
      pullback (bit n) (terminatingCode (floorPower n) (reachesOne_step h)) := by
  let d := Nat.find (reachesOne_step h)
  have hd : floorPower^[d] (floorPower n) = 1 := Nat.find_spec (reachesOne_step h)
  rw [terminatingCode_eq_codeAt h (d := d + 1) (by simpa [iterate_cons] using hd),
    codeAt_succ]
  rfl

/-- Parity of a fraction is unchanged by reducing an odd denominator. -/
theorem parity_of_odd_denominator (a b : ℤ) (hb : b % 2 = 1) :
    (((a : ℚ) / b).num % 2 = a % 2) ∧
      ((((a : ℚ) / b).den : ℤ) % 2 = 1) := by
  have hb0 : b ≠ 0 := by omega
  obtain ⟨c, ha, hc⟩ := Rat.num_den_mk hb0
    (Rat.intCast_div_eq_divInt a b)
  have hm := congrArg (fun z : ℤ => z % 2) hc
  rw [hb, Int.mul_emod] at hm
  rcases Int.emod_two_eq_zero_or_one c with hc0 | hc1
  · simp [hc0] at hm
  · have hden : ((((a : ℚ) / b).den : ℤ) % 2) = 1 := by simpa [hc1] using hm.symm
    refine ⟨?_, hden⟩
    have hn := congrArg (fun z : ℤ => z % 2) ha
    simpa [Int.mul_emod, hc1] using hn.symm

theorem pullback_parity (b : Branch) (q : ℚ) (hq : (q.den : ℤ) % 2 = 1) :
    ((pullback b q).den : ℤ) % 2 = 1 ∧
      ((pullback b q).num % 2 = 0 ↔ b = .even) := by
  have hden : (q.den : ℚ) ≠ 0 := by exact_mod_cast Rat.den_nz q
  cases b with
  | even =>
    have heq : pullback .even q = ((2 * q.num : ℤ) : ℚ) / (q.den : ℤ) := by
      conv_lhs => rw [pullback, ← Rat.num_div_den q]
      push_cast
      ring
    rw [heq]
    obtain ⟨hn, hd⟩ := parity_of_odd_denominator (2 * q.num) q.den hq
    refine ⟨hd, ?_⟩
    constructor
    · intro _; rfl
    · intro _; rw [hn]; omega
  | odd =>
    have heq : pullback .odd q = ((2 * q.num + q.den : ℤ) : ℚ) /
        ((3 * (q.den : ℤ) : ℤ) : ℚ) := by
      conv_lhs => rw [pullback, ← Rat.num_div_den q]
      push_cast
      field_simp
    rw [heq]
    have h3 : (3 * (q.den : ℤ)) % 2 = 1 := by omega
    obtain ⟨hn, hd⟩ := parity_of_odd_denominator (2 * q.num + q.den) (3 * q.den) h3
    refine ⟨hd, ?_⟩
    constructor
    · intro he; rw [hn] at he; omega
    · intro he; cases he

theorem pullbackWord_den_odd (w : List Branch) (q : ℚ)
    (hq : (q.den : ℤ) % 2 = 1) : ((pullbackWord w q).den : ℤ) % 2 = 1 := by
  induction w with
  | nil => exact hq
  | cons b w ih => exact (pullback_parity b _ ih).1

/-- The reduced denominator divides the power of three counting the odd letters. -/
theorem codeAt_den_dvd (n d : ℕ) :
    ((codeAt n d).den : ℤ) ∣ (3 : ℤ) ^ oddCount (itinerary n d) := by
  rw [codeAt_formula]
  simpa only [Rat.divInt_eq_div, Int.cast_add, Int.cast_pow, Int.cast_ofNat,
    Int.cast_natCast] using
    Rat.den_dvd ((2 : ℤ) ^ d + (wordConst (itinerary n d) : ℤ))
      ((3 : ℤ) ^ oddCount (itinerary n d))

theorem terminatingCode_parity {n : ℕ} (h : ReachesOne n) :
    ((terminatingCode n h).den : ℤ) % 2 = 1 ∧
      ((terminatingCode n h).num % 2 = 0 ↔ n % 2 = 0) := by
  rw [terminatingCode_pullback h]
  have hq : ((terminatingCode (floorPower n) (reachesOne_step h)).den : ℤ) % 2 = 1 :=
    pullbackWord_den_odd _ 1 (by norm_num)
  obtain ⟨hd, hn⟩ := pullback_parity (bit n) _ hq
  refine ⟨hd, hn.trans ?_⟩
  simp [bit]

/-- Rational `3n-1`; on odd-denominator fractions the numerator gives parity. -/
def minusStep (q : ℚ) : ℚ :=
  if q.num % 2 = 0 then q / 2 else (3 * q - 1) / 2

/-- Rational `3n+1` with the same parity convention. -/
def plusStep (q : ℚ) : ℚ :=
  if q.num % 2 = 0 then q / 2 else (3 * q + 1) / 2

theorem plusStep_neg (q : ℚ) : plusStep (-q) = -minusStep q := by
  have hp : (-q).num % 2 = 0 ↔ q.num % 2 = 0 := by rw [Rat.neg_num]; omega
  simp only [plusStep, minusStep, hp]
  split_ifs <;> ring

/-- The rational extension agrees with the existing integer shortcut map. -/
theorem plusStep_intCast (z : ℤ) : plusStep (z : ℚ) = (shortcutZ z : ℚ) := by
  have hz := two_mul_shortcutZ z
  by_cases hp : z % 2 = 0
  · rw [if_pos hp] at hz
    have hq : (2 : ℚ) * (shortcutZ z : ℚ) = z := by exact_mod_cast hz
    simp only [plusStep, Rat.num_intCast, hp, ite_true]
    linarith
  · rw [if_neg hp] at hz
    have hq : (2 : ℚ) * (shortcutZ z : ℚ) = 3 * z + 1 := by exact_mod_cast hz
    simp only [plusStep, Rat.num_intCast, hp, ite_false]
    linarith

/-- On integers, `3n-1` is the existing signed `3n+1` map under negation. -/
theorem minusStep_intCast (z : ℤ) : minusStep (z : ℚ) = ((-shortcutZ (-z) : ℤ) : ℚ) := by
  have h := plusStep_intCast (-z)
  rw [Int.cast_neg, plusStep_neg] at h
  simpa using congrArg Neg.neg h

/-- One actual Juggler step becomes one rational `3n-1` step. -/
theorem terminatingCode_semiconjugacy {n : ℕ} (h : ReachesOne n) :
    terminatingCode (floorPower n) (reachesOne_step h) = minusStep (terminatingCode n h) := by
  have hp := (terminatingCode_parity h).2
  simp only [minusStep, hp]
  rw [terminatingCode_pullback h]
  by_cases hn : n % 2 = 0
  · simp [hn, bit, pullback]
  · simp [hn, bit, pullback]; ring

/-- Negating the code gives the corresponding rational `3n+1` step. -/
theorem terminatingCode_plus_semiconjugacy {n : ℕ} (h : ReachesOne n) :
    -terminatingCode (floorPower n) (reachesOne_step h) =
      plusStep (-terminatingCode n h) := by
  rw [plusStep_neg, terminatingCode_semiconjugacy h]

theorem pullbackWord_pos (w : List Branch) {q : ℚ} (hq : 0 < q) :
    0 < pullbackWord w q := by
  induction w with
  | nil => exact hq
  | cons b w ih => cases b <;> simp only [pullbackWord, pullback] <;> positivity

theorem terminatingCode_pos {n : ℕ} (h : ReachesOne n) :
    0 < terminatingCode n h := pullbackWord_pos _ (by norm_num)

/-- The complete rational bridge, with an explicit termination hypothesis. -/
theorem terminating_bridge {n : ℕ} (h : ReachesOne n) :
    (∀ d, floorPower^[d] n = 1 →
      terminatingCode n h = codeAt n d ∧
      ((terminatingCode n h).den : ℤ) ∣ (3 : ℤ) ^ oddCount (itinerary n d)) ∧
    0 < terminatingCode n h ∧
    ((terminatingCode n h).den : ℤ) % 2 = 1 ∧
    ((terminatingCode n h).num % 2 = 0 ↔ n % 2 = 0) ∧
    terminatingCode (floorPower n) (reachesOne_step h) = minusStep (terminatingCode n h) ∧
    -terminatingCode (floorPower n) (reachesOne_step h) =
      plusStep (-terminatingCode n h) := by
  refine ⟨?_, terminatingCode_pos h, (terminatingCode_parity h).1,
    (terminatingCode_parity h).2, terminatingCode_semiconjugacy h,
    terminatingCode_plus_semiconjugacy h⟩
  intro d hd
  refine ⟨terminatingCode_eq_codeAt h hd, ?_⟩
  rw [terminatingCode_eq_codeAt h hd]
  exact codeAt_den_dvd n d

theorem terminatingCode_three : terminatingCode 3 three_reachesOne = 83 / 27 := by
  rw [terminatingCode_eq_codeAt three_reachesOne (d := 6) (by decide +kernel)]
  norm_num [codeAt, itinerary, bit, floorPower, pullbackWord, pullback]

theorem terminatingCode_four : terminatingCode 4 four_reachesOne = 4 := by
  rw [terminatingCode_eq_codeAt four_reachesOne (d := 2) (by decide +kernel)]
  norm_num [codeAt, itinerary, bit, floorPower, pullbackWord, pullback]

theorem terminatingCode_six : terminatingCode 6 six_reachesOne = 4 := by
  rw [terminatingCode_eq_codeAt six_reachesOne (d := 2) (by decide +kernel)]
  norm_num [codeAt, itinerary, bit, floorPower, pullbackWord, pullback]

/-- A terminating ordinary integer can have a nonintegral rational code. -/
theorem terminatingCode_three_not_integer :
    ¬ ∃ z : ℤ, terminatingCode 3 three_reachesOne = (z : ℚ) := by
  rw [terminatingCode_three]
  rintro ⟨z, hz⟩
  have he : (83 : ℚ) = 27 * z := by linarith
  have hi : (83 : ℤ) = 27 * z := by exact_mod_cast he
  omega

/-- Distinct terminating starts can have the same rational code. -/
theorem terminatingCode_not_injective :
    (4 : ℕ) ≠ 6 ∧ terminatingCode 4 four_reachesOne = terminatingCode 6 six_reachesOne := by
  simp [terminatingCode_four, terminatingCode_six]

end Problems.Juggler.CollatzRational
