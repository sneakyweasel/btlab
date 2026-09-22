import Problems.Juggler.CollatzRational
import Mathlib.NumberTheory.Padics.RingHoms

/-!
# The signed Collatz code of every Juggler itinerary

The finite residue/word bijection gives compatible residues for every
actual Juggler itinerary. Mathlib's inverse limit constructs their
2-adic limit, without a termination hypothesis.
-/

noncomputable section

namespace Problems.Juggler.CollatzPadic

open CollatzBridge

local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

/-- The ordinary Collatz residue realizing the first `d` Juggler parities. -/
def residue (n d : ℕ) : ℕ :=
  Nat.find (exists_residue_of_word (itinerary_length n d))

theorem residue_lt (n d : ℕ) : residue n d < 2 ^ d :=
  (Nat.find_spec (exists_residue_of_word (itinerary_length n d))).1

theorem residue_word (n d : ℕ) : parityWord (residue n d) d = itinerary n d :=
  (Nat.find_spec (exists_residue_of_word (itinerary_length n d))).2

/-- Longer actual itineraries select the same residue at every earlier precision. -/
theorem residue_compatible (n i j : ℕ) (hij : i ≤ j) :
    residue n j % 2 ^ i = residue n i % 2 ^ i := by
  apply (parityWord_eq_iff _ _ _).mp
  rw [← parityWord_take hij, residue_word, itinerary_take n j i hij, residue_word]

theorem residue_increment (n i : ℕ) :
    (2 : ℤ) ^ i ∣ (residue n (i + 1) : ℤ) - residue n i := by
  have hz : (residue n i : ZMod (2 ^ i)) = residue n (i + 1) :=
    (ZMod.natCast_eq_natCast_iff' _ _ _).2 (residue_compatible n i (i + 1) (by omega)).symm
  have hi := (ZMod.intCast_eq_intCast_iff_dvd_sub
    (residue n i : ℤ) (residue n (i + 1) : ℤ) (2 ^ i)).mp (by simpa using hz)
  simpa using hi

/-- The `3n+1` code, defined for every start by compatible finite residues. -/
def plusCode (n : ℕ) : ℤ_[2] :=
  PadicInt.ofIntSeq (fun d => (residue n d : ℤ))
    (PadicInt.isCauSeq_padicNorm_of_pow_dvd_sub _ 2 (residue_increment n))

/-- The `3n-1` code is the negative of the `3n+1` code. -/
def code (n : ℕ) : ℤ_[2] := -plusCode n

theorem plusCode_residue (n d : ℕ) :
    PadicInt.toZModPow d (plusCode n) = (residue n d : ZMod (2 ^ d)) := by
  simpa [plusCode] using PadicInt.toZModPow_ofIntSeq_of_pow_dvd_sub
    (fun d => (residue n d : ℤ)) 2 (residue_increment n) d

theorem residue_first_parity (n d : ℕ) : residue n (d + 1) % 2 = n % 2 := by
  have hb := congrArg List.head? (residue_word n (d + 1))
  simp only [parityWord_succ, itinerary_succ, List.head?_cons, Option.some.injEq] at hb
  rcases Nat.mod_two_eq_zero_or_one (residue n (d + 1)) with hr | hr <;>
    rcases Nat.mod_two_eq_zero_or_one n with hn | hn <;>
    simp [bit, hr, hn] at hb ⊢

/-- The finite coded Collatz successor has exactly the remaining Juggler word. -/
theorem residue_successor (n d : ℕ) :
    shortcutC (residue n (d + 1)) % 2 ^ d = residue (floorPower n) d % 2 ^ d := by
  apply (parityWord_eq_iff _ _ _).mp
  have hw := congrArg List.tail (residue_word n (d + 1))
  simpa only [parityWord_succ, itinerary_succ, List.tail_cons, residue_word] using hw

theorem plusCode_parity (n : ℕ) :
    PadicInt.toZModPow 1 (plusCode n) = 0 ↔ n % 2 = 0 := by
  rw [plusCode_residue]
  change (residue n 1 : ZMod 2) = (0 : ℕ) ↔ _
  rw [ZMod.natCast_eq_natCast_iff']
  simpa using residue_first_parity n 0 ▸ Iff.rfl

/-- Exact one-step identity, cleared of the nonunit divisor two. -/
theorem plusCode_step (n : ℕ) :
    2 * plusCode (floorPower n) =
      if n % 2 = 0 then plusCode n else 3 * plusCode n + 1 := by
  apply PadicInt.ext_of_toZModPow.mp
  intro d
  have hsame : (residue n (d + 1) : ZMod (2 ^ d)) = residue n d :=
    (ZMod.natCast_eq_natCast_iff' _ _ _).2 (residue_compatible n d (d + 1) (by omega))
  have hnext : (shortcutC (residue n (d + 1)) : ZMod (2 ^ d)) = residue (floorPower n) d :=
    (ZMod.natCast_eq_natCast_iff' _ _ _).2 (residue_successor n d)
  have hs := congrArg (fun a : ℕ => (a : ZMod (2 ^ d)))
    (two_mul_shortcutC (residue n (d + 1)))
  rw [residue_first_parity] at hs
  simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat, Nat.cast_one, apply_ite] at hs
  rw [hnext, hsame] at hs
  simpa only [map_mul, map_add, map_ofNat, map_one, apply_ite, plusCode_residue] using hs

theorem code_parity (n : ℕ) :
    PadicInt.toZModPow 1 (code n) = 0 ↔ n % 2 = 0 := by
  simpa [code] using plusCode_parity n

theorem code_step (n : ℕ) :
    2 * code (floorPower n) =
      if n % 2 = 0 then code n else 3 * code n - 1 := by
  have h := plusCode_step n
  unfold code
  split_ifs at h ⊢ with hn <;> linear_combination -h

/-- Equality of coded residues is exactly equality of the actual finite itineraries. -/
theorem code_residue_eq_iff (n m d : ℕ) :
    PadicInt.toZModPow d (code n) = PadicInt.toZModPow d (code m) ↔
      itinerary n d = itinerary m d := by
  simp only [code, map_neg, neg_inj, plusCode_residue]
  rw [ZMod.natCast_eq_natCast_iff', ← parityWord_eq_iff, residue_word, residue_word]

/-- Every coded residue class is exactly its corresponding actual parity cylinder. -/
theorem code_residue_word_iff (n r d : ℕ) :
    PadicInt.toZModPow d (code n) = -(r : ZMod (2 ^ d)) ↔
      itinerary n d = parityWord r d := by
  simp only [code, map_neg, neg_inj, plusCode_residue]
  rw [ZMod.natCast_eq_natCast_iff', ← parityWord_eq_iff, residue_word]

/-- The equivalence preserves finite source sets exactly; it is not a distribution estimate. -/
theorem code_cylinder_eq (S : Finset ℕ) (r d : ℕ) :
    S.filter (fun n => PadicInt.toZModPow d (code n) = -(r : ZMod (2 ^ d))) =
      S.filter (fun n => itinerary n d = parityWord r d) := by
  ext n
  simp only [Finset.mem_filter, code_residue_word_iff]

theorem code_one : code 1 = 1 := by
  have h := code_step 1
  norm_num [floorPower_one] at h
  linear_combination -h

/-- Numerator of the `3n+1` step, selected by the actual residue modulo two. -/
def plusNumerator (x : ℤ_[2]) : ℤ_[2] :=
  if PadicInt.toZModPow 1 x = 0 then x else 3 * x + 1

theorem two_dvd_plusNumerator (x : ℤ_[2]) : (2 : ℤ_[2]) ∣ plusNumerator x := by
  have hz : PadicInt.toZModPow 1 (plusNumerator x) = 0 := by
    unfold plusNumerator
    split_ifs with hx
    · exact hx
    · have hv := ZMod.val_lt (PadicInt.toZModPow 1 x)
      have hval : (PadicInt.toZModPow 1 x).val = 1 := by
        have hn : (PadicInt.toZModPow 1 x).val ≠ 0 := by
          intro h
          apply hx
          simpa [h] using (ZMod.natCast_zmod_val (PadicInt.toZModPow 1 x)).symm
        norm_num at hv
        omega
      have hone : PadicInt.toZModPow 1 x = 1 := by
        simpa [hval] using (ZMod.natCast_zmod_val (PadicInt.toZModPow 1 x)).symm
      norm_num [hone, map_ofNat]
      decide
  apply Ideal.mem_span_singleton.mp
  have hmem : plusNumerator x ∈ RingHom.ker (PadicInt.toZModPow 1) := hz
  rw [PadicInt.ker_toZModPow] at hmem
  simpa using hmem

/-- The `3n+1` map on 2-adic integers, using its exactly divisible numerator. -/
def plusStep (x : ℤ_[2]) : ℤ_[2] := Classical.choose (two_dvd_plusNumerator x)

theorem two_mul_plusStep (x : ℤ_[2]) : 2 * plusStep x = plusNumerator x :=
  (Classical.choose_spec (two_dvd_plusNumerator x)).symm

/-- The `3n-1` map on 2-adic integers, obtained by negation. -/
def minusStep (x : ℤ_[2]) : ℤ_[2] := -plusStep (-x)

theorem two_mul_minusStep (x : ℤ_[2]) :
    2 * minusStep x = if PadicInt.toZModPow 1 x = 0 then x else 3 * x - 1 := by
  have h := two_mul_plusStep (-x)
  unfold plusNumerator at h
  simp only [map_neg, neg_eq_zero] at h
  unfold minusStep
  split_ifs at h ⊢ with hx <;> linear_combination -h

theorem plusCode_semiconjugacy (n : ℕ) :
    plusCode (floorPower n) = plusStep (plusCode n) := by
  apply mul_left_cancel₀ (by norm_num : (2 : ℤ_[2]) ≠ 0)
  rw [two_mul_plusStep]
  simpa only [plusNumerator, plusCode_parity] using plusCode_step n

/-- Every actual Juggler orbit maps into an actual 2-adic `3n-1` orbit. -/
theorem code_semiconjugacy (n : ℕ) : code (floorPower n) = minusStep (code n) := by
  simpa [code, minusStep] using congrArg Neg.neg (plusCode_semiconjugacy n)

theorem code_plus_semiconjugacy (n : ℕ) : -code (floorPower n) = plusStep (-code n) := by
  simpa [code] using plusCode_semiconjugacy n

theorem code_iterate (n d : ℕ) :
    code (floorPower^[d] n) = minusStep^[d] (code n) := by
  induction d with
  | zero => rfl
  | succ d ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
      code_semiconjugacy, ih]

/-- A code remembers the whole parity itinerary, rather than the original integer. -/
theorem code_eq_iff (n m : ℕ) :
    code n = code m ↔ ∀ d, itinerary n d = itinerary m d := by
  rw [← PadicInt.ext_of_toZModPow]
  exact forall_congr' (fun d => code_residue_eq_iff n m d)

/-- The finite affine formula for the global code along actual Juggler iterates. -/
theorem code_affine (n d : ℕ) :
    3 ^ oddCount (itinerary n d) * code n =
      2 ^ d * code (floorPower^[d] n) + (wordConst (itinerary n d) : ℤ_[2]) := by
  induction d generalizing n with
  | zero => simp [itinerary]
  | succ d ih =>
    have hi := ih (floorPower n)
    have hs := code_step n
    rw [iterate_cons]
    rcases Nat.mod_two_eq_zero_or_one n with hn | hn
    · rw [if_pos hn] at hs
      simp only [itinerary_succ, bit_even hn, oddCount_even_cons, wordConst_even,
        Nat.cast_mul, Nat.cast_ofNat, pow_succ]
      linear_combination 2 * hi - (3 : ℤ_[2]) ^ oddCount (itinerary (floorPower n) d) * hs
    · rw [if_neg (by omega)] at hs
      simp only [itinerary_succ, bit_odd hn, oddCount_odd_cons, wordConst_odd,
        Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, pow_succ]
      linear_combination 2 * hi - (3 : ℤ_[2]) ^ oddCount (itinerary (floorPower n) d) * hs

/-- On terminating starts the global code agrees with the previously verified rational code. -/
theorem code_eq_terminatingCode {n : ℕ} (h : ReachesOne n) :
    (code n : ℚ_[2]) = (CollatzRational.terminatingCode n h : ℚ_[2]) := by
  obtain ⟨d, hd⟩ := h
  have hc := code_affine n d
  rw [hd, code_one, mul_one] at hc
  have hr : (3 : ℚ) ^ oddCount (itinerary n d) * CollatzRational.terminatingCode n ⟨d, hd⟩ =
      2 ^ d + wordConst (itinerary n d) := by
    rw [CollatzRational.terminatingCode_eq_codeAt ⟨d, hd⟩ hd]
    simpa [CollatzRational.codeAt, itinerary_length] using
      CollatzRational.pullbackWord_affine (itinerary n d) (1 : ℚ)
  have hc' : (3 : ℚ_[2]) ^ oddCount (itinerary n d) * (code n : ℚ_[2]) =
      2 ^ d + wordConst (itinerary n d) := by
    exact_mod_cast congrArg (fun x : ℤ_[2] => (x : ℚ_[2])) hc
  have hr' : (3 : ℚ_[2]) ^ oddCount (itinerary n d) *
      (CollatzRational.terminatingCode n ⟨d, hd⟩ : ℚ_[2]) =
      2 ^ d + wordConst (itinerary n d) := by exact_mod_cast hr
  exact mul_left_cancel₀ (by norm_num) (hc'.trans hr'.symm)

theorem code_three_cleared : (27 : ℤ_[2]) * code 3 = 83 := by
  have h := code_affine 3 6
  have he : floorPower^[6] 3 = 1 := by decide +kernel
  rw [he, code_one] at h
  norm_num [itinerary, floorPower, bit, wordConst, oddCount] at h
  exact h

theorem code_three_not_integer : ¬ ∃ z : ℤ, code 3 = (z : ℤ_[2]) := by
  rintro ⟨z, hz⟩
  have h := code_three_cleared
  rw [hz] at h
  have hi : (27 : ℤ) * z = 83 := by exact_mod_cast h
  omega

theorem code_four : code 4 = 4 := by
  have h := code_affine 4 2
  have he : floorPower^[2] 4 = 1 := by decide +kernel
  rw [he, code_one] at h
  norm_num [itinerary, floorPower, bit, wordConst, oddCount] at h
  exact h

theorem code_six : code 6 = 4 := by
  have h := code_affine 6 2
  have he : floorPower^[2] 6 = 1 := by decide +kernel
  rw [he, code_one] at h
  norm_num [itinerary, floorPower, bit, wordConst, oddCount] at h
  exact h

theorem code_not_injective : ¬ Function.Injective code := by
  intro h
  have he : (4 : ℕ) = 6 := h (code_four.trans code_six.symm)
  omega

/-- The global signed orbit bridge and its exact finite information content. -/
theorem orbit_bridge (n : ℕ) :
    (PadicInt.toZModPow 1 (code n) = 0 ↔ n % 2 = 0) ∧
    code (floorPower n) = minusStep (code n) ∧
    -code (floorPower n) = plusStep (-code n) ∧
    (∀ d, code (floorPower^[d] n) = minusStep^[d] (code n)) ∧
    (∀ r d, PadicInt.toZModPow d (code n) = -(r : ZMod (2 ^ d)) ↔
      itinerary n d = parityWord r d) ∧
    (∀ h : ReachesOne n, (code n : ℚ_[2]) =
      (CollatzRational.terminatingCode n h : ℚ_[2])) :=
  ⟨code_parity n, code_semiconjugacy n, code_plus_semiconjugacy n,
    code_iterate n, code_residue_word_iff n, fun h => code_eq_terminatingCode h⟩

end Problems.Juggler.CollatzPadic
