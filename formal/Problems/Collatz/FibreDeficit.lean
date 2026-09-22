import Problems.Collatz.FibreMassError

/-! # Actual deficient progressions cannot be discarded at finite reciprocal cost -/

noncomputable section

namespace Problems.Collatz.FibreDeficit

open Finset FibreMass FibreActual FibreMassError
open scoped Classical

/-- Weights positive on units and zero on nonunits are nonnegative everywhere. -/
theorem weight_nonneg {r : ℕ} {h : Level r → ℝ}
    (hz : ∀ b, b.val % 3 = 0 → h b = 0)
    (hp : ∀ b, b.val % 3 ≠ 0 → 0 < h b) : ∀ b, 0 ≤ h b := by
  intro b
  by_cases hb : b.val % 3 = 0
  · rw [hz b hb]
  · exact (hp b hb).le

/-- A homogeneous deficient residue remains uniformly deficient at every sufficiently large integer in it. -/
theorem deficient_progression (plus : Bool) {r : ℕ} (hr : 1 ≤ r)
    (h : Level r → ℝ) (hz : ∀ b, b.val % 3 = 0 → h b = 0)
    (hp : ∀ b, b.val % 3 ≠ 0 → 0 < h b) :
    ∃ a : Level (r+1), a.val % 3 ≠ 0 ∧ ∃ δ : ℝ, 0 < δ ∧ ∃ B : ℕ, 1 ≤ B ∧
      ∀ m : ℕ, B ≤ m → residue (r+1) m = a →
        (m:ℝ)*actualMass plus r h m ≤ h (residue r m)-δ := by
  obtain ⟨a,ha,hdef⟩ := finite_weight_obstruction plus hr h hz hp (d := 1) (by omega)
  have hh := weight_nonneg hz hp
  let H : ℝ := 1+∑ b, h b
  have hH (b : Level r) : h b ≤ H := by
    have ht := single_le_sum (s := univ) (fun b _ => hh b) (mem_univ b)
    dsimp [H]
    linarith
  let δ : ℝ := (h (project r 1 a)-transfer plus r h a)/2
  have hδ : 0 < δ := by change transfer plus r h a < h (project r 1 a) at hdef; dsimp [δ]; linarith
  let B : ℕ := max 1 ⌈1/2+H/δ⌉₊
  refine ⟨a,ha,δ,hδ,B,le_max_left _ _,?_⟩
  intro m hm hma
  have hm1 : 1 ≤ m := (le_max_left _ _).trans hm
  have hmR : (1:ℝ) ≤ m := by exact_mod_cast hm1
  have hceil : (⌈1/2+H/δ⌉₊:ℝ) ≤ m := by exact_mod_cast ((le_max_right _ _).trans hm)
  have hlarge : H/δ ≤ (m:ℝ)-1/2 := by linarith [Nat.le_ceil (1/2+H/δ)]
  have herr : H/((m:ℝ)-1/2) ≤ δ := by
    apply (div_le_iff₀ (by linarith : (0:ℝ) < m-1/2)).mpr
    have ht := (div_le_iff₀ hδ).mp hlarge
    nlinarith
  have he := (abs_le.mp (actual_mass_error plus r hh hH hm1)).2
  rw [hma] at he
  have hb : residue r m = project r 1 a := by rw [← project_residue r 1 m, hma]
  rw [hb]
  dsimp [δ] at *
  linarith

/-- An explicit progression of positive odd representatives of a prescribed ternary residue above a cutoff. -/
def progression (r : ℕ) (a : Level (r+1)) (B t : ℕ) : ℕ :=
  a.val+3^(r+1)*(a.val+1+2*(B+t))

/-- Every member of the chosen progression is positive. -/
theorem progression_pos (r : ℕ) (a : Level (r+1)) (B t : ℕ) :
    1 ≤ progression r a B t := by
  have hp : 0 < 3^(r+1) := by positivity
  have hi : 0 < a.val+1+2*(B+t) := by omega
  have := Nat.mul_pos hp hi
  unfold progression
  omega

/-- Every member of the chosen progression lies above the prescribed cutoff. -/
theorem progression_large (r : ℕ) (a : Level (r+1)) (B t : ℕ) :
    B ≤ progression r a B t := by
  have hp : 0 < 3^(r+1) := by positivity
  have ht : a.val+1+2*(B+t) ≤ 3^(r+1)*(a.val+1+2*(B+t)) :=
    Nat.le_mul_of_pos_left _ hp
  unfold progression
  omega

/-- Every member of the chosen progression is odd. -/
theorem progression_odd (r : ℕ) (a : Level (r+1)) (B t : ℕ) :
    Odd (progression r a B t) := by
  have hp : Odd ((3:ℕ)^(r+1)) := (show Odd (3:ℕ) by decide).pow
  obtain ⟨q,hq⟩ := hp
  refine ⟨a.val+q*(a.val+1+2*(B+t))+(B+t), ?_⟩
  unfold progression
  calc _ = a.val+(2*q+1)*(a.val+1+2*(B+t)) :=
      congrArg (fun z : ℕ => a.val+z*(a.val+1+2*(B+t))) hq
    _ = _ := by ring

/-- The progression stays in the prescribed ternary residue class. -/
theorem progression_residue (r : ℕ) (a : Level (r+1)) (B t : ℕ) :
    residue (r+1) (progression r a B t) = a := by
  apply Fin.ext
  simp [residue, progression, Nat.add_mod, Nat.mod_eq_of_lt a.isLt]

/-- The progression enumerates distinct integers. -/
theorem progression_injective (r : ℕ) (a : Level (r+1)) (B : ℕ) :
    Function.Injective (progression r a B) := by
  intro i j he
  have ht : 3^(r+1)*(a.val+1+2*(B+i)) = 3^(r+1)*(a.val+1+2*(B+j)) :=
    Nat.add_left_cancel he
  have hq := Nat.eq_of_mul_eq_mul_left (by positivity : 0 < 3^(r+1)) ht
  omega

/-- The progression has positive common difference twice the ternary modulus. -/
theorem progression_affine (r : ℕ) (a : Level (r+1)) (B t : ℕ) :
    progression r a B t = progression r a B 0+(2*3^(r+1))*t := by
  unfold progression
  ring

/-- Reciprocals along any positive arithmetic progression have divergent sum. -/
theorem arithmetic_mass_not_summable {A : ℕ} (hA : 1 ≤ A) (D : ℕ) :
    ¬Summable (fun t : ℕ => (1:ℝ)/(A+D*t)) := by
  intro hs
  have hAR : (1:ℝ) ≤ A := by exact_mod_cast hA
  have hpos (t : ℕ) : (0:ℝ) < A+D*t := by positivity
  have hcmp (t : ℕ) : (1:ℝ)/(t+1) ≤ (A+D)*((1:ℝ)/(A+D*t)) := by
    rw [mul_one_div]
    apply (div_le_div_iff₀ (by positivity) (hpos t)).mpr
    have htn : (0:ℝ) ≤ t := Nat.cast_nonneg _
    have hdn : (0:ℝ) ≤ D := Nat.cast_nonneg _
    nlinarith
  have ht : Summable (fun t : ℕ => (1:ℝ)/(t+1)) :=
    Summable.of_nonneg_of_le (fun t => by positivity) hcmp (hs.mul_left ((A:ℝ)+D))
  have hf : Summable (fun t : ℕ => (1:ℝ)/(t:ℝ)) :=
    (summable_nat_add_iff 1).mp (by simpa using ht)
  exact Real.not_summable_one_div_natCast hf

/-- The chosen odd residue progression has divergent reciprocal mass. -/
theorem progression_mass_not_summable (r : ℕ) (a : Level (r+1)) (B : ℕ) :
    ¬Summable (fun t : ℕ => (1:ℝ)/progression r a B t) := by
  have he : (fun t : ℕ => (1:ℝ)/progression r a B t) =
      (fun t : ℕ => (1:ℝ)/((progression r a B 0:ℝ)+(2*3^(r+1):ℕ)*t)) := by
    funext t
    congr 1
    exact_mod_cast progression_affine r a B t
  rw [he]
  exact arithmetic_mass_not_summable (progression_pos r a B 0) (2*3^(r+1))

/-- An integer in a unit ternary residue class is itself coprime to three. -/
theorem residue_unit {r m : ℕ} {a : Level (r+1)} (ha : a.val % 3 ≠ 0)
    (hm : residue (r+1) m = a) : m % 3 ≠ 0 := by
  have hd : 3 ∣ 3^(r+1) := by exact ⟨3^r, by rw [pow_succ]; ring⟩
  have he : m % 3^(r+1) = a.val := congrArg Fin.val hm
  have ht : a.val % 3 = m % 3 := by rw [← he]; exact Nat.mod_mod_of_dvd m hd
  rwa [ht] at ha

/-- A positive odd unit whose actual predecessor mass fails to reproduce its periodic target weight. -/
def Deficient (plus : Bool) (r : ℕ) (h : Level r → ℝ) (m : ℕ) : Prop :=
  1 ≤ m ∧ Odd m ∧ m % 3 ≠ 0 ∧ (m:ℝ)*actualMass plus r h m < h (residue r m)

/-- For either sign and any positive unit table, actual deficient targets have divergent reciprocal mass. -/
theorem deficient_mass_not_summable (plus : Bool) {r : ℕ} (hr : 1 ≤ r)
    (h : Level r → ℝ) (hz : ∀ b, b.val % 3 = 0 → h b = 0)
    (hp : ∀ b, b.val % 3 ≠ 0 → 0 < h b) :
    ¬Summable (fun m : ℕ => if Deficient plus r h m then (1:ℝ)/m else 0) := by
  obtain ⟨a,ha,δ,hδ,B,hB,hbad⟩ := deficient_progression plus hr h hz hp
  have hdef (t : ℕ) : Deficient plus r h (progression r a B t) := by
    refine ⟨progression_pos r a B t, progression_odd r a B t,
      residue_unit ha (progression_residue r a B t), ?_⟩
    have ht := hbad _ (progression_large r a B t) (progression_residue r a B t)
    linarith
  intro hs
  have ht := hs.comp_injective (progression_injective r a B)
  change Summable (fun t : ℕ => if Deficient plus r h (progression r a B t)
    then (1:ℝ)/progression r a B t else 0) at ht
  have hf : Summable (fun t : ℕ => (1:ℝ)/progression r a B t) := by
    simpa only [Function.comp_apply, if_pos (hdef _)] using ht
  exact progression_mass_not_summable r a B hf

/-- A globally finite reciprocal-mass exceptional set leaves an actual deficient
positive odd unit target outside it, for either signed odd-return map. -/
theorem outside_finite_mass (plus : Bool) {r : ℕ} (hr : 1 ≤ r)
    (h : Level r → ℝ) (hz : ∀ b, b.val % 3 = 0 → h b = 0)
    (hp : ∀ b, b.val % 3 ≠ 0 → 0 < h b) (E : ℕ → Prop)
    (hE : Summable (fun m : ℕ => if E m then (1:ℝ)/m else 0)) :
    ∃ m : ℕ, Deficient plus r h m ∧ ¬E m := by
  by_contra! hno
  apply deficient_mass_not_summable plus hr h hz hp
  apply Summable.of_nonneg_of_le (fun m => by split_ifs <;> positivity) _ hE
  intro m
  by_cases hm : Deficient plus r h m
  · simp [hm, hno m hm]
  · simp [hm]
    split_ifs <;> positivity

/-- Every finite reciprocal-mass deletion leaves a positive odd unit whose full
actual predecessor mass is strictly below its periodic target weight. -/
theorem exists_predecessor_mass_lt (plus : Bool) {r : ℕ} (hr : 1 ≤ r)
    (h : Level r → ℝ) (hz : ∀ b, b.val % 3 = 0 → h b = 0)
    (hp : ∀ b, b.val % 3 ≠ 0 → 0 < h b) (E : ℕ → Prop)
    (hE : Summable (fun m : ℕ => if E m then (1:ℝ)/m else 0)) :
    ∃ m : ℕ, 1 ≤ m ∧ Odd m ∧ m % 3 ≠ 0 ∧ ¬E m ∧
      (m:ℝ)*(∑' n : {n : ℕ // 1 ≤ n ∧ Odd n ∧ oddReturn plus n = m},
        h (residue r n.val)/n.val) < h (residue r m) := by
  obtain ⟨m, ⟨hm, ho, hu, hd⟩, hE⟩ := outside_finite_mass plus hr h hz hp E hE
  refine ⟨m, hm, ho, hu, hE, ?_⟩
  rwa [← actualMass_predecessors plus r h hm ho]

end Problems.Collatz.FibreDeficit
