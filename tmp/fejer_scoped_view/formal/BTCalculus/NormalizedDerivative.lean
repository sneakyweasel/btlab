import BTCalculus.Normalization

namespace BTCalculus

/-!
Normalized coefficient derivative. Naive drop of ``c_0`` is not semantic ``D``.
-/

def dCoeff : List ℤ → List ℤ
  | [] => [0]
  | [_] => [0]
  | _c :: cs => cs

def hatDRaw : List ℤ → List ℤ
  | [] => [0]
  | c :: cs => addHead (DZ c) cs

theorem lsdZ_add_mul3 (c m : ℤ) : lsdZ (c + 3 * m) = lsdZ c := by
  apply lsdZ_unique (lsdZ_is_trit c)
  have hcm : (c + 3 * m) % 3 = c % 3 := by
    have h3 : (3 * m) % 3 = 0 := Int.mul_emod_right 3 m
    rw [Int.add_emod, h3, add_zero, Int.emod_emod]
  have hc := lsdZ_mod c
  change (c + 3 * m) % 3 = lsdZ c % 3
  have : c % 3 = lsdZ c % 3 := hc
  exact hcm.trans this

theorem DZ_add_mul3 (c m : ℤ) : DZ (c + 3 * m) = DZ c + m := by
  have hlsd := lsdZ_add_mul3 c m
  unfold DZ
  rw [hlsd]
  have : c + 3 * m - lsdZ c = (c - lsdZ c) + 3 * m := by ring
  rw [this, Int.add_ediv_of_dvd_right]
  · have : (c - lsdZ c) / 3 + 3 * m / 3 = (c - lsdZ c) / 3 + m := by
      have h3 : (3 * m) / 3 = m := Int.mul_ediv_cancel_left m (by decide : (3 : ℤ) ≠ 0)
      rw [h3]
    exact this
  · exact dvd_mul_right 3 m

theorem hatDRaw_value : ∀ cs : List ℤ, coeffValue (hatDRaw cs) = DZ (coeffValue cs)
  | [] => by
    simp [hatDRaw, coeffValue, DZ, lsdZ]
  | c :: cs => by
    simp [hatDRaw, coeffValue, addHead_value]
    rw [add_comm]
    exact (DZ_add_mul3 c (coeffValue cs)).symm

def hatDCanon (cs : List ℤ) : List ℤ :=
  encodeZ (DZ (coeffValue cs))

theorem hatDCanon_value (cs : List ℤ) :
    coeffValue (hatDCanon cs) = DZ (coeffValue cs) := by
  simpa [hatDCanon] using encodeZ_value (DZ (coeffValue cs))

theorem hatDCanon_eq_normalize_raw (cs : List ℤ) :
    hatDCanon cs = normalizeLSD (hatDRaw cs) := by
  simp [hatDCanon, normalizeLSD, hatDRaw_value]

/-- Milestone 14 witness: naive drop of ``[2]`` is not semantic ``D``. -/
theorem m14_witness_dCoeff :
    coeffValue (dCoeff [2]) = 0 := by
  simp [dCoeff, coeffValue]

theorem lsdZ_two : lsdZ 2 = -1 := by
  simp [lsdZ]

theorem DZ_two : DZ 2 = 1 := by
  simp [DZ, lsdZ_two]

theorem encodeZ_two : encodeZ 2 = [-1, 1] := by
  have hne : (2 : ℤ) ≠ 0 := by decide
  rw [encodeZ_of_ne_zero hne, DZ_two, lsdZ_two]
  have hone : (1 : ℤ) ≠ 0 := by decide
  rw [encodeZ_of_ne_zero hone]
  simp [DZ, lsdZ]

theorem m14_witness_normalized_D :
    DZ (coeffValue (normalizeLSD [2])) = 1 := by
  simp [normalizeLSD, coeffValue, encodeZ_two, DZ, lsdZ]

theorem m14_witness_naive_ne :
    coeffValue (dCoeff [2]) ≠ DZ (coeffValue (normalizeLSD [2])) := by
  simp [m14_witness_dCoeff, m14_witness_normalized_D]

theorem hatDRaw_two : hatDRaw [2] = [1] := by
  simp [hatDRaw, addHead, DZ_two]

theorem hatDRaw_two_correct :
    coeffValue (hatDRaw [2]) = DZ (coeffValue [2]) :=
  hatDRaw_value [2]

theorem trit_DZ {c : ℤ} (h : isTrit c) : DZ c = 0 := by
  unfold DZ
  have : lsdZ c = c := lsdZ_unique h (Int.ModEq.refl c)
  rw [this, sub_self, Int.zero_ediv]

/-- If the LSD is already a trit, naive drop is semantic ``D``. -/
theorem canonical_drop (c : ℤ) (cs : List ℤ) (h : isTrit c) :
    coeffValue (dCoeff (c :: cs)) = DZ (coeffValue (c :: cs)) := by
  have hdz := trit_DZ h
  simp only [coeffValue]
  rw [DZ_add_mul3, hdz, zero_add]
  cases cs with
  | nil => simp [dCoeff, coeffValue]
  | cons d rest => simp [dCoeff, coeffValue]

def ICoeff (a : ℤ) (cs : List ℤ) : List ℤ := a :: cs

theorem hatDRaw_I_value (a : ℤ) (cs : List ℤ) (ha : isTrit a) :
    coeffValue (hatDRaw (ICoeff a cs)) = coeffValue cs := by
  simp [ICoeff, hatDRaw_value, coeffValue]
  rw [DZ_add_mul3, trit_DZ ha, zero_add]

end BTCalculus
