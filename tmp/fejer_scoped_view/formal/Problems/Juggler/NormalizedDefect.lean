import Problems.Juggler.Residuals

namespace Problems.Juggler

/-!
# Normalized relative slack

The surplus ratio `R = Δ / (n^{3^o} - n^{2^k})` is defined only when
the formal surplus is positive, and then `R ≤ 1` if and only if
`T_w(n) ≥ n`. It is a change of coordinates for the endpoint
comparison, not an independent potential.

The relative slack `1 + q = n^{3^o} / T_w(n)^{2^k}` is the same
identity in multiplicative form. Concatenation multiplies these
ratios and factors out the huge exponents. This file does not claim
that every start reaches `1`.
-/

/-- Numerator of `1+q`. -/
def slackNum (n : ℕ) (w : List Branch) : ℕ :=
  n ^ (3 ^ oddCount w)

/-- Denominator of `1+q`. -/
def slackDen (n : ℕ) (w : List Branch) : ℕ :=
  image n w ^ (2 ^ w.length)

/-- Pair `(Δ, T^{2^k})`. The ratio is the relative slack `q`. -/
def relativeSlack (n : ℕ) (w : List Branch) : ℕ × ℕ :=
  (globalDefect n w, slackDen n w)

/-- Pair `(n^{3^o}, T^{2^k})`. The ratio is `1+q`. -/
def onePlusSlack (n : ℕ) (w : List Branch) : ℕ × ℕ :=
  (slackNum n w, slackDen n w)

/-- Formal envelope surplus. Zero in `ℕ` when the itinerary is
exponent-contracting. -/
def formalSurplus (n : ℕ) (w : List Branch) : ℕ :=
  n ^ (3 ^ oddCount w) - n ^ (2 ^ w.length)

/-- Pair `(Δ, S)`. The ratio is `R` when `S > 0`. -/
def defectRatio (n : ℕ) (w : List Branch) : ℕ × ℕ :=
  (globalDefect n w, formalSurplus n w)

/-- Residual-block surplus ratio. Same pair as `defectRatio`. -/
def residualDefectRatio (x a b : ℕ) : ℕ × ℕ :=
  defectRatio x (oddEvenBlock a b)

/-- Local remainder over `T(x)^2`. -/
def normalizedLocalDefect (x : ℕ) : ℕ × ℕ :=
  (if x % 2 = 0 then localDefectEven x else localDefectOdd x,
    floorPower x ^ 2)

theorem slack_identity {n : ℕ} {w : List Branch} (hw : follows n w) :
    slackNum n w = slackDen n w + globalDefect n w :=
  global_defect_identity hw

theorem slackNum_ge_slackDen {n : ℕ} {w : List Branch} (hw : follows n w) :
    slackDen n w ≤ slackNum n w :=
  Nat.le.intro (slack_identity hw).symm

theorem slackNum_append (n : ℕ) (u v : List Branch) :
    slackNum n (u ++ v) = slackNum n u ^ (3 ^ oddCount v) := by
  simp [slackNum, oddCount_append, pow_three_add]

theorem slackDen_append (n : ℕ) (u v : List Branch) :
    slackDen n (u ++ v) = slackDen (image n u) v ^ (2 ^ u.length) := by
  simp only [slackDen, image_append, List.length_append]
  rw [pow_add, mul_comm (2 ^ u.length), ← Nat.pow_mul]

theorem slackDen_num_bridge (n : ℕ) (u v : List Branch) :
    slackDen n u ^ (3 ^ oddCount v) =
      slackNum (image n u) v ^ (2 ^ u.length) := by
  simp only [slackDen, slackNum]
  rw [← Nat.pow_mul, ← Nat.pow_mul, mul_comm]

/-- Exact concatenation law for `1+q`. Not additive in `R`. -/
theorem onePlusSlack_concat (n : ℕ) (u v : List Branch) :
    slackNum n (u ++ v) *
        slackDen n u ^ (3 ^ oddCount v) *
        slackDen (image n u) v ^ (2 ^ u.length) =
      slackNum n u ^ (3 ^ oddCount v) *
        slackNum (image n u) v ^ (2 ^ u.length) *
        slackDen n (u ++ v) := by
  rw [slackNum_append, slackDen_append, slackDen_num_bridge]

theorem slackNum_even_cons (n : ℕ) (w : List Branch) :
    slackNum n (w ++ [Branch.even]) = slackNum n w := by
  rw [slackNum_append]
  simp [oddCount_even_cons, oddCount_nil]

theorem slackNum_odd_cons (n : ℕ) (w : List Branch) :
    slackNum n (w ++ [Branch.odd]) = slackNum n w ^ 3 := by
  rw [slackNum_append]
  simp [oddCount_odd_cons, oddCount_nil]

theorem image_singleton_even (x : ℕ) :
    image x [Branch.even] = floorPower x :=
  rfl

theorem image_singleton_odd (x : ℕ) :
    image x [Branch.odd] = floorPower x :=
  rfl

theorem slackDen_singleton (x : ℕ) (b : Branch) :
    slackDen x [b] = floorPower x ^ 2 := by
  cases b <;> simp [slackDen, image]

theorem slackNum_singleton_even (x : ℕ) :
    slackNum x [Branch.even] = x := by
  simp [slackNum, oddCount]

theorem slackNum_singleton_odd (x : ℕ) :
    slackNum x [Branch.odd] = x ^ 3 := by
  simp [slackNum, oddCount]

theorem onePlusSlack_singleton_even {x : ℕ} (h : x % 2 = 0) :
    slackNum x [Branch.even] =
      slackDen x [Branch.even] + localDefectEven x := by
  simpa [slackNum_singleton_even, slackDen_singleton] using
    (localDefectEven_add h).symm

theorem onePlusSlack_singleton_odd {x : ℕ} (h : x % 2 = 1) :
    slackNum x [Branch.odd] =
      slackDen x [Branch.odd] + localDefectOdd x := by
  simpa [slackNum_singleton_odd, slackDen_singleton] using
    (localDefectOdd_add h).symm

theorem normalizedLocalDefect_even {x : ℕ} (h : x % 2 = 0) :
    normalizedLocalDefect x =
      (localDefectEven x, slackDen x [Branch.even]) := by
  simp [normalizedLocalDefect, slackDen_singleton, h]

theorem normalizedLocalDefect_odd {x : ℕ} (h : x % 2 = 1) :
    normalizedLocalDefect x =
      (localDefectOdd x, slackDen x [Branch.odd]) := by
  simp [normalizedLocalDefect, slackDen_singleton, h]

/-- Even letter: `1+q' = (1+q)(1+η)^{2^k}` in `ℕ`. -/
theorem relative_slack_even (n : ℕ) (w : List Branch) :
    slackNum n (w ++ [Branch.even]) *
        slackDen n w *
        slackDen (image n w) [Branch.even] ^ (2 ^ w.length) =
      slackNum n w *
        slackNum (image n w) [Branch.even] ^ (2 ^ w.length) *
        slackDen n (w ++ [Branch.even]) := by
  simpa [oddCount] using onePlusSlack_concat n w [Branch.even]

/-- Odd letter: `1+q' = (1+q)^3 (1+η)^{2^k}` in `ℕ`. -/
theorem relative_slack_odd (n : ℕ) (w : List Branch) :
    slackNum n (w ++ [Branch.odd]) *
        slackDen n w ^ 3 *
        slackDen (image n w) [Branch.odd] ^ (2 ^ w.length) =
      slackNum n w ^ 3 *
        slackNum (image n w) [Branch.odd] ^ (2 ^ w.length) *
        slackDen n (w ++ [Branch.odd]) := by
  simpa [oddCount] using onePlusSlack_concat n w [Branch.odd]

/-- Running `1+q` does not decrease under a realized extension.
This is not the endpoint comparison `T_w(n) ≥ n`. -/
theorem onePlusSlack_ge_of_prefix {n : ℕ} {u v : List Branch}
    (hu : follows n u) (hv : follows (image n u) v) :
    slackNum n u * slackDen n (u ++ v) ≤
      slackNum n (u ++ v) * slackDen n u := by
  have hN := slackNum_append n u v
  have hD := slackDen_append n u v
  have hB := slackDen_num_bridge n u v
  have hgeV : slackDen (image n u) v ≤ slackNum (image n u) v :=
    slackNum_ge_slackDen hv
  have hgeU : slackDen n u ≤ slackNum n u := slackNum_ge_slackDen hu
  have hpos : 1 ≤ 3 ^ oddCount v := Nat.one_le_pow (oddCount v) 3 (by decide)
  have hden_le : slackDen n (u ++ v) ≤ slackDen n u ^ (3 ^ oddCount v) := by
    rw [hD, hB]
    exact Nat.pow_le_pow_left hgeV _
  have hstep : slackDen n u ^ (3 ^ oddCount v) ≤
      slackNum n u ^ (3 ^ oddCount v - 1) * slackDen n u := by
    have he : 3 ^ oddCount v = 3 ^ oddCount v - 1 + 1 :=
      (Nat.sub_add_cancel hpos).symm
    rw [he, pow_add, pow_one]
    exact Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hgeU _)
  have hmid : slackDen n (u ++ v) ≤
      slackNum n u ^ (3 ^ oddCount v - 1) * slackDen n u :=
    le_trans hden_le hstep
  have hmul := Nat.mul_le_mul_left (slackNum n u) hmid
  have hpow : slackNum n u * slackNum n u ^ (3 ^ oddCount v - 1) =
      slackNum n u ^ (3 ^ oddCount v) := by
    have he : 1 + (3 ^ oddCount v - 1) = 3 ^ oddCount v := by omega
    calc
      slackNum n u * slackNum n u ^ (3 ^ oddCount v - 1)
          = slackNum n u ^ 1 * slackNum n u ^ (3 ^ oddCount v - 1) := by
            rw [pow_one]
      _ = slackNum n u ^ (1 + (3 ^ oddCount v - 1)) :=
            (pow_add _ _ _).symm
      _ = slackNum n u ^ (3 ^ oddCount v) := by
            rw [he]
  rw [hN]
  calc
    slackNum n u * slackDen n (u ++ v)
        ≤ slackNum n u * (slackNum n u ^ (3 ^ oddCount v - 1) * slackDen n u) :=
          hmul
    _ = (slackNum n u * slackNum n u ^ (3 ^ oddCount v - 1)) * slackDen n u := by
          ac_rfl
    _ = slackNum n u ^ (3 ^ oddCount v) * slackDen n u := by
          rw [hpow]

/-- `R` concatenation is the global-defect lift over the formal surplus.
It is not a function of `(R_u, R_v)` alone. -/
theorem defectRatio_concat {n : ℕ} {u v : List Branch}
    (hu : follows n u) (hv : follows (image n u) v) :
    (defectRatio n (u ++ v)).1 =
      powGap (image n u ^ (2 ^ u.length)) (globalDefect n u)
        (3 ^ oddCount v) +
      powGap (image (image n u) v ^ (2 ^ v.length))
        (globalDefect (image n u) v) (2 ^ u.length) ∧
    (defectRatio n (u ++ v)).2 =
      n ^ (3 ^ (oddCount u + oddCount v)) -
        n ^ (2 ^ (u.length + v.length)) := by
  constructor
  · simpa [defectRatio] using global_defect_append hu hv
  · simp [defectRatio, formalSurplus, oddCount_append, List.length_append]

/-- When the formal surplus is a genuine difference, `R ≤ 1` iff
`T_w(n) ≥ n`. This is not a new obstruction. -/
theorem defectRatio_le_one_iff_image_ge {n : ℕ} {w : List Branch}
    (hw : follows n w)
    (hS : n ^ (2 ^ w.length) ≤ n ^ (3 ^ oddCount w)) :
    globalDefect n w ≤ formalSurplus n w ↔ n ≤ image n w := by
  have hid := slack_identity hw
  have hne : 2 ^ w.length ≠ 0 :=
    Nat.ne_of_gt (Nat.two_pow_pos w.length)
  constructor
  · intro h
    have hadd : globalDefect n w + n ^ (2 ^ w.length) ≤ slackNum n w :=
      (Nat.le_sub_iff_add_le hS).mp (by simpa [formalSurplus, slackNum] using h)
    have hden : n ^ (2 ^ w.length) ≤ slackDen n w := by
      have h' : globalDefect n w + n ^ (2 ^ w.length) ≤
          slackDen n w + globalDefect n w := by
        simpa [hid] using hadd
      rw [add_comm (globalDefect n w)] at h'
      exact Nat.le_of_add_le_add_right h'
    exact (Nat.pow_le_pow_iff_left hne).mp (by simpa [slackDen] using hden)
  · intro h
    have hpow : n ^ (2 ^ w.length) ≤ slackDen n w := by
      simpa [slackDen] using (Nat.pow_le_pow_iff_left hne).mpr h
    have hadd : globalDefect n w + n ^ (2 ^ w.length) ≤ slackNum n w := by
      have : globalDefect n w + n ^ (2 ^ w.length) ≤
          globalDefect n w + slackDen n w :=
        Nat.add_le_add_left hpow _
      simpa [hid, add_comm] using this
    exact (Nat.le_sub_iff_add_le hS).mpr
      (by simpa [formalSurplus, slackNum] using hadd)

/-- A realized return uses the whole formal surplus. On a cycle,
`R = 1` whenever the surplus is the `ℕ` difference. -/
theorem image_eq_start_defectRatio {n : ℕ} {w : List Branch}
    (hw : follows n w) (himg : image n w = n) :
    globalDefect n w = formalSurplus n w := by
  have hid := global_defect_identity hw
  rw [himg] at hid
  have hle : n ^ (2 ^ w.length) ≤ n ^ (3 ^ oddCount w) :=
    Nat.le.intro hid.symm
  simp [formalSurplus]
  exact ((Nat.sub_eq_iff_eq_add hle).mpr (hid.trans (add_comm _ _))).symm

theorem oddEvenBlock_not_monochrome {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) :
    ¬ isMonochrome (oddEvenBlock a b) := by
  intro h
  rcases h with heven | hodd
  · have ho : oddCount (oddEvenBlock a b) = 0 := by
      rw [heven, oddCount_replicate_even]
    have : a = 0 := by simpa [oddCount_oddEvenBlock] using ho
    omega
  · have ho : oddCount (oddEvenBlock a b) = a := oddCount_oddEvenBlock a b
    have hlen : (oddEvenBlock a b).length = a + b := length_oddEvenBlock a b
    rw [hodd, oddCount_replicate_odd, hlen] at ho
    omega

theorem residualStep_of_odd {x y : ℕ}
    (h : ResidualStep x y) (hodd : x % 2 = 1) :
    ∃ a b, 1 ≤ a ∧ 1 ≤ b ∧ follows x (oddEvenBlock a b) ∧
      image x (oddEvenBlock a b) = y := by
  obtain ⟨a, b, hb, hw, himg⟩ := h
  refine ⟨a, b, ?_, hb, hw, himg⟩
  by_contra h0
  have ha0 : a = 0 := by omega
  have hw' : follows x (List.replicate b Branch.even) := by
    simpa [oddEvenBlock, ha0] using hw
  have heven : x % 2 = 0 := by
    cases b with
    | zero => cases hb
    | succ b =>
        simpa [List.replicate_succ] using hw'.1
  omega

theorem residualStep_relative_slack {x y : ℕ} (h : ResidualStep x y) :
    ∃ a b, 1 ≤ b ∧ follows x (oddEvenBlock a b) ∧
      image x (oddEvenBlock a b) = y ∧
        slackNum x (oddEvenBlock a b) =
          slackDen x (oddEvenBlock a b) +
            globalDefect x (oddEvenBlock a b) ∧
        relativeSlack x (oddEvenBlock a b) =
          (globalDefect x (oddEvenBlock a b), y ^ (2 ^ (a + b))) := by
  obtain ⟨a, b, hb, hw, himg⟩ := h
  refine ⟨a, b, hb, hw, himg, slack_identity hw, ?_⟩
  simp [relativeSlack, slackDen, himg, length_oddEvenBlock]

theorem residualStep_onePlusSlack_concat {x y : ℕ} (h : ResidualStep x y) :
    ∃ a b, 1 ≤ b ∧ follows x (oddEvenBlock a b) ∧
      image x (oddEvenBlock a b) = y ∧
        slackNum x (oddEvenBlock a b) *
            slackDen x (List.replicate a Branch.odd) ^
              (3 ^ oddCount (List.replicate b Branch.even)) *
            slackDen (image x (List.replicate a Branch.odd))
              (List.replicate b Branch.even) ^ (2 ^ a) =
          slackNum x (List.replicate a Branch.odd) ^
              (3 ^ oddCount (List.replicate b Branch.even)) *
            slackNum (image x (List.replicate a Branch.odd))
              (List.replicate b Branch.even) ^ (2 ^ a) *
            slackDen x (oddEvenBlock a b) := by
  obtain ⟨a, b, hb, hw, himg⟩ := h
  refine ⟨a, b, hb, hw, himg, ?_⟩
  simpa [oddEvenBlock, List.length_replicate] using
    onePlusSlack_concat x (List.replicate a Branch.odd)
      (List.replicate b Branch.even)

theorem residualStep_defect_pos_of_odd {x y : ℕ}
    (h : ResidualStep x y) (hodd : x % 2 = 1) :
    ∃ a b, 1 ≤ a ∧ 1 ≤ b ∧ follows x (oddEvenBlock a b) ∧
      image x (oddEvenBlock a b) = y ∧
        0 < globalDefect x (oddEvenBlock a b) := by
  obtain ⟨a, b, ha, hb, hw, himg⟩ := residualStep_of_odd h hodd
  refine ⟨a, b, ha, hb, hw, himg,
    global_defect_pos_of_mixed hw (oddEvenBlock_not_monochrome ha hb)⟩

theorem persistent_odd_residual_defect_pos {x y : ℕ}
    (h : PersistentOddResidual x y) (hodd : x % 2 = 1) :
    ∃ a b, 1 ≤ a ∧ 1 ≤ b ∧ follows x (oddEvenBlock a b) ∧
      image x (oddEvenBlock a b) = y ∧
        0 < globalDefect x (oddEvenBlock a b) :=
  residualStep_defect_pos_of_odd h.1 hodd

theorem residualStep_defectRatio {x y : ℕ} (h : ResidualStep x y) :
    ∃ a b, 1 ≤ b ∧ follows x (oddEvenBlock a b) ∧
      image x (oddEvenBlock a b) = y ∧
        residualDefectRatio x a b =
          (globalDefect x (oddEvenBlock a b),
            formalSurplus x (oddEvenBlock a b)) := by
  obtain ⟨a, b, hb, hw, himg⟩ := h
  exact ⟨a, b, hb, hw, himg, rfl⟩

end Problems.Juggler
