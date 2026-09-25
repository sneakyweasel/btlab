import Problems.Juggler.BeattyIsoLevels

/-!
# The grid tree of an isolated slope

Tree level `l+1` is good level `l`: grid `q = Q_(g l)`, margin `2/Q_(g l + 1)`,
window length `q^(-γ)`, on the side of the sign of `θ = qα - P`. The root has
length `1`. With the size floor `B`, every good denominator satisfies
`q^(γ-1) ≥ 8` and `q^(ν-γ) ≥ 5`, which gives the grid axioms.
-/

namespace Problems.Juggler.BeattySlope

open Filter Topology Set

/-- Numerical parameters: `1 < γ < ν` and a size floor `B`. -/
structure IsoParams (ν γ B : ℝ) : Prop where
  γ1 : 1 < γ
  γν : γ < ν
  B10 : 10 ≤ B
  Bγ : 8 ≤ B ^ (γ - 1)
  Bν : 5 ≤ B ^ (ν - γ)

namespace IsoLevels

variable {ν γ B : ℝ} {G : ℕ → Prop} [DecidablePred G] (Lv : IsoLevels ν G B)

/-- Good denominator at good level `l`. -/
noncomputable def den (l : ℕ) : ℝ := isoDen ν G (Lv.g l)

/-- The next denominator. -/
noncomputable def den' (l : ℕ) : ℝ := isoDen ν G (Lv.g l + 1)

/-- The error `θ = Q α - P` at good level `l`. -/
noncomputable def θ (l : ℕ) : ℝ := Lv.den l * isoSlope ν G - cfNum (isoQuot ν G) (Lv.g l)

/-- Good denominators are at least the size floor. -/
theorem den_ge (l : ℕ) : B ≤ Lv.den l :=
  Lv.big.trans (by unfold den; exact_mod_cast isoDen_mono (Lv.mono.monotone (Nat.zero_le l)))

/-- Good denominators increase with the level. -/
theorem den_mono : Monotone Lv.den := fun _ _ h => by
  unfold den; exact_mod_cast isoDen_mono (Lv.mono.monotone h)

/-- The next denominator lies between `Q^ν` and `4Q^ν`. -/
theorem den'_bounds (hν : 1 ≤ ν) (l : ℕ) : Lv.den l ^ ν ≤ Lv.den' l ∧ Lv.den' l ≤ 4 * Lv.den l ^ ν :=
  isoDen_good_growth hν (Lv.one_le_g l) (Lv.good l)

/-- The error at a good level lies between `1/(2Q')` and `1/Q'`. -/
theorem θ_bounds (l : ℕ) : 1 / (2 * Lv.den' l) ≤ |Lv.θ l| ∧ |Lv.θ l| ≤ 1 / Lv.den' l :=
  iso_err_bounds (Lv.g l)

/-- The good denominator is at most the next denominator. -/
theorem den_le_den' (l : ℕ) : Lv.den l ≤ Lv.den' l := by
  unfold den den'; exact_mod_cast isoDen_mono (Nat.le_succ _)

/-- The next denominator is at most the following good denominator. -/
theorem den'_le_den (l : ℕ) : Lv.den' l ≤ Lv.den (l + 1) := by
  unfold den den'; exact_mod_cast isoDen_mono (Lv.mono (Nat.lt_succ_self l))

variable {Lv} (P : IsoParams ν γ B)
include P

/-- Good denominators are positive. -/
theorem den_pos (l : ℕ) : 0 < Lv.den l := by linarith [Lv.den_ge l, P.B10]

/-- Good denominators are at least one. -/
theorem den_one (l : ℕ) : 1 ≤ Lv.den l := by linarith [Lv.den_ge l, P.B10]

/-- Good denominators satisfy `Q^(γ-1) ≥ 8`. -/
theorem den_rpow_γ (l : ℕ) : 8 ≤ Lv.den l ^ (γ - 1) :=
  P.Bγ.trans (Real.rpow_le_rpow (by linarith [P.B10]) (Lv.den_ge l) (by linarith [P.γ1]))

/-- Good denominators satisfy `Q^(ν-γ) ≥ 5`. -/
theorem den_rpow_ν (l : ℕ) : 5 ≤ Lv.den l ^ (ν - γ) :=
  P.Bν.trans (Real.rpow_le_rpow (by linarith [P.B10]) (Lv.den_ge l) (by linarith [P.γν]))

/-- The next denominators are positive. -/
theorem den'_pos (l : ℕ) : 0 < Lv.den' l := (den_pos (Lv := Lv) P l).trans_le (Lv.den_le_den' l)

/-- `d q' ≥ 5` at every level. -/
theorem dq' (l : ℕ) : 5 ≤ Lv.den l ^ (-γ) * Lv.den' l := by
  have hq := den_pos (Lv := Lv) P l
  have h1 := (Lv.den'_bounds (by linarith [P.γ1, P.γν]) l).1
  calc (5 : ℝ) ≤ Lv.den l ^ (ν - γ) := den_rpow_ν (Lv := Lv) P l
    _ = Lv.den l ^ (-γ) * Lv.den l ^ ν := by rw [← Real.rpow_add hq]; ring_nf
    _ ≤ _ := mul_le_mul_of_nonneg_left h1 (by positivity)

/-- The margins: `2/q' + q^(-γ) ≤ (3/4)/q` and `1/q' + 3 q^(-γ) ≤ (1/2)/q`. -/
theorem margins (l : ℕ) :
    2 / Lv.den' l + Lv.den l ^ (-γ) ≤ 3 / 4 / Lv.den l ∧
      1 / Lv.den' l + 3 * Lv.den l ^ (-γ) ≤ 1 / 2 / Lv.den l := by
  have hq := den_pos (Lv := Lv) P l
  have hq1 := den_one (Lv := Lv) P l
  have hν1 : 1 ≤ ν := by linarith [P.γ1, P.γν]
  have h1 := (Lv.den'_bounds hν1 l).1
  have hγ := den_rpow_γ (Lv := Lv) P l
  -- `q^(-γ) = q^(-1) q^(1-γ) ≤ q^(-1)/8`
  have e1 : Lv.den l ^ (-γ) = (1 / Lv.den l) * (1 / Lv.den l ^ (γ - 1)) := by
    rw [one_div, one_div, ← Real.rpow_neg_one, ← Real.rpow_neg hq.le, ← Real.rpow_add hq]; ring_nf
  have e2 : 1 / Lv.den l ^ (γ - 1) ≤ 1 / 8 := one_div_le_one_div_of_le (by norm_num) hγ
  have hd : Lv.den l ^ (-γ) ≤ 1 / 8 / Lv.den l := by
    rw [e1]; calc 1 / Lv.den l * (1 / Lv.den l ^ (γ - 1)) ≤ 1 / Lv.den l * (1 / 8) :=
      mul_le_mul_of_nonneg_left e2 (by positivity)
    _ = 1 / 8 / Lv.den l := by ring
  -- `1/q' ≤ q^(-ν) ≤ q^(-1)/8`
  have hν8 : 8 ≤ Lv.den l ^ (ν - 1) :=
    hγ.trans (Real.rpow_le_rpow_of_exponent_le hq1 (by linarith [P.γν]))
  have hq' : 1 / Lv.den' l ≤ 1 / 8 / Lv.den l := by
    have hqν : Lv.den l ^ ν = Lv.den l * Lv.den l ^ (ν - 1) := by
      rw [← Real.rpow_one_add' hq.le (by linarith [P.γ1, P.γν])]; ring_nf
    calc 1 / Lv.den' l ≤ 1 / Lv.den l ^ ν := one_div_le_one_div_of_le (by positivity) h1
      _ = 1 / Lv.den l * (1 / Lv.den l ^ (ν - 1)) := by rw [hqν]; field_simp
      _ ≤ 1 / Lv.den l * (1 / 8) :=
          mul_le_mul_of_nonneg_left (one_div_le_one_div_of_le (by norm_num) hν8) (by positivity)
      _ = 1 / 8 / Lv.den l := by ring
  have r : 0 < 1 / Lv.den l := by positivity
  have c0 : 0 < 1 / 8 / Lv.den l := by positivity
  constructor
  · have : 2 / Lv.den' l = 2 * (1 / Lv.den' l) := by ring
    rw [this]
    have e3 : 3 / 4 / Lv.den l = 6 * (1 / 8 / Lv.den l) := by ring
    rw [e3]; linarith
  · have e3 : 1 / 2 / Lv.den l = 4 * (1 / 8 / Lv.den l) := by ring
    rw [e3]; linarith

omit P in
/-- The sign of the error at a tree level. -/
noncomputable def side (l : ℕ) : Bool := decide (0 < Lv.θ l)

/-- The grid data of the isolated slope. -/
noncomputable def grid : GridData where
  q := fun l => match l with | 0 => 1 | l + 1 => isoDen ν G (Lv.g l)
  q' := fun l => match l with | 0 => 1 | l + 1 => Lv.den' l
  pos := fun l => match l with | 0 => true | l + 1 => Lv.side l
  d := fun l => match l with | 0 => 1 | l + 1 => Lv.den l ^ (-γ)
  d_zero := rfl
  d_pos := fun l => by
    cases l with
    | zero => exact one_pos
    | succ l => exact Real.rpow_pos_of_pos (den_pos (Lv := Lv) P l) _
  q_ge := fun l => by
    have := Lv.den_ge l; have := P.B10
    have : (2 : ℝ) ≤ isoDen ν G (Lv.g l) := by unfold den at *; linarith
    exact_mod_cast this
  q'_pos := fun l => den'_pos (Lv := Lv) P l
  dq_ge := fun l => by
    cases l with
    | zero =>
      show (10 : ℝ) ≤ 1 * (isoDen ν G (Lv.g 0) : ℕ)
      have := Lv.den_ge 0; have := P.B10; unfold den at *; linarith
    | succ l =>
      show (10 : ℝ) ≤ Lv.den l ^ (-γ) * (isoDen ν G (Lv.g (l + 1)) : ℕ)
      have hq := den_pos (Lv := Lv) P l
      have h1 := (Lv.den'_bounds (by linarith [P.γ1, P.γν]) l).1
      -- `Q(l+1) ≥ 2Q' ≥ 2 Q^ν ≥ 10 Q^γ`
      have h3 : 2 * Lv.den' l ≤ (isoDen ν G (Lv.g (l + 1)) : ℝ) := Lv.step2 l
      have hQn : 2 * Lv.den l ^ ν ≤ (isoDen ν G (Lv.g (l + 1)) : ℝ) := by linarith [h1, h3]
      calc (10 : ℝ) ≤ 2 * Lv.den l ^ (ν - γ) := by linarith [den_rpow_ν (Lv := Lv) P l]
        _ = Lv.den l ^ (-γ) * (2 * Lv.den l ^ ν) := by
            rw [show ν - γ = -γ + ν by ring, Real.rpow_add hq]; ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hQn (Real.rpow_pos_of_pos hq _).le
  margin := fun l => by
    have := (margins (Lv := Lv) P l).1
    have hq := den_pos (Lv := Lv) P l
    show 2 / Lv.den' l + Lv.den l ^ (-γ) < 1 / ((isoDen ν G (Lv.g l) : ℕ) : ℝ)
    have e : ((isoDen ν G (Lv.g l) : ℕ) : ℝ) = Lv.den l := rfl
    rw [e]
    have : 3 / 4 / Lv.den l < 1 / Lv.den l := div_lt_div_of_pos_right (by norm_num) hq
    linarith

end IsoLevels

end Problems.Juggler.BeattySlope
