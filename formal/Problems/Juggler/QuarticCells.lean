import Problems.Juggler.CubicReturn

namespace Problems.Juggler.QuarticCells

/-!
Exact cells for the prescribed quartic return words. Every actual-cycle
statement below retains all source guards and derives the required
injectivity from periodicity.
-/

abbrev O := CubicReturn.O
abbrev B := ReturnCells.oe
abbrev F := ReturnCells.ooe

def G (x : ℕ) : ℕ := O (B x)

def FGuard (x : ℕ) : Prop :=
  x % 2 = 1 ∧ O x % 2 = 1 ∧ O (O x) % 2 = 0

def GGuard (x : ℕ) : Prop :=
  x % 2 = 1 ∧ O x % 2 = 0 ∧ B x % 2 = 1

theorem O_mono : Monotone O := by
  intro x y h
  exact Nat.sqrt_le_sqrt (Nat.pow_le_pow_left h 3)

theorem B_mono : Monotone B := by
  intro x y h
  exact Nat.sqrt_le_sqrt (O_mono h)

theorem F_mono : Monotone F := by
  intro x y h
  exact B_mono (O_mono h)

theorem G_mono : Monotone G := by
  intro x y h
  exact O_mono (B_mono h)

theorem G_gt_of_B_ge_five {x : ℕ} (hx : 5 ≤ B x) : x < G x := by
  let v := B x
  have hg : v < (O (O v)).sqrt := CubicReturn.ooe_gt hx
  have hs : (v + 1) ^ 2 ≤ O (O v) := by
    simpa only [pow_two] using Nat.le_sqrt.mp
      (show v + 1 ≤ (O (O v)).sqrt by omega)
  have hp := Nat.pow_le_pow_left hs 2
  have hO := CubicReturn.O_sq_le (O v)
  change O (O v) ^ 2 ≤ O v ^ 3 at hO
  have hbound : (v + 1) ^ 4 ≤ O v ^ 3 := by
    calc
      (v + 1) ^ 4 = ((v + 1) ^ 2) ^ 2 := by ring
      _ ≤ O (O v) ^ 2 := hp
      _ ≤ O v ^ 3 := hO
  have hcell := (ReturnCells.oe_cell x).2
  change x ^ 3 < (v + 1) ^ 4 at hcell
  have hpow : x ^ 3 < G x ^ 3 := hcell.trans_le hbound
  by_contra hn
  have hh := Nat.pow_le_pow_left (show G x ≤ x by omega) 3
  omega

theorem G_gt {x : ℕ} (hx : 16 ≤ x) : x < G x := by
  apply G_gt_of_B_ge_five
  have hm := B_mono hx
  have h₁₆ : B 16 = 8 := by decide +kernel
  rw [h₁₆] at hm
  omega

theorem B_square (v : ℕ) : B (v ^ 2) = O v := by
  change (((v ^ 2) ^ 3).sqrt).sqrt = (v ^ 3).sqrt
  have h : (v ^ 2) ^ 3 = (v ^ 3) ^ 2 := by ring
  rw [h, Nat.sqrt_eq']

theorem B_eq_iff {x v : ℕ} :
    B x = v ↔ v ^ 4 ≤ x ^ 3 ∧ x ^ 3 < (v + 1) ^ 4 :=
  ReturnCells.oe_eq_iff

theorem B_source_cell (x : ℕ) :
    B x ^ 2 ≤ O x ∧ O x < (B x + 1) ^ 2 := by
  exact ⟨Nat.sqrt_le' (O x), Nat.lt_succ_sqrt' (O x)⟩

theorem F_cell_envelope (x : ℕ) :
    G x ≤ F x ∧ F x ≤ O (B x + 1) := by
  obtain ⟨hlo, hhi⟩ := B_source_cell x
  constructor
  · change O (B x) ≤ B (O x)
    simpa only [B_square] using B_mono hlo
  · change B (O x) ≤ O (B x + 1)
    simpa only [B_square] using B_mono (Nat.le_of_lt hhi)

theorem F_le_G_of_B_lt {x y : ℕ} (h : B x < B y) : F x ≤ G y := by
  exact (F_cell_envelope x).2.trans (O_mono h)

theorem G_le_F_of_B_eq {x y : ℕ} (h : B x = B y) : G y ≤ F x := by
  simpa [G, h] using (F_cell_envelope x).1

theorem inversion_iff_cell {x y : ℕ} (hxy : x ≤ y) (hne : F x ≠ G y) :
    G y < F x ↔ B x = B y := by
  constructor
  · intro hinv
    have hmono := B_mono hxy
    by_contra hn
    have hlt : B x < B y := lt_of_le_of_ne hmono hn
    exact (not_lt_of_ge (F_le_G_of_B_lt hlt)) hinv
  · intro heq
    exact lt_of_le_of_ne (G_le_F_of_B_eq heq) (Ne.symm hne)

theorem F_actual {x : ℕ} (h : FGuard x) :
    floorPower (floorPower (floorPower x)) = F x :=
  ReturnCells.ooe_actual h.1 h.2.1 h.2.2

theorem G_actual {x : ℕ} (h : GGuard x) :
    floorPower (floorPower (floorPower x)) = G x := by
  rw [ReturnCells.oe_actual h.1 h.2.1, floorPower_odd_eq h.2.2]
  rfl

theorem third_inj {C : Set ℕ} {m M x y : ℕ}
    (D : CubicReturn.PeriodicExtrema C m M) (hx : x ∈ C) (hy : y ∈ C)
    (h : floorPower (floorPower (floorPower x)) =
      floorPower (floorPower (floorPower y))) : x = y := by
  apply D.inj hx hy
  apply D.inj (D.closed _ hx) (D.closed _ hy)
  exact D.inj (D.closed _ (D.closed _ hx)) (D.closed _ (D.closed _ hy)) h

theorem F_ne_G_of_periodic {C : Set ℕ} {m M x y : ℕ}
    (D : CubicReturn.PeriodicExtrema C m M) (hx : x ∈ C) (hy : y ∈ C)
    (hF : FGuard x) (hG : GGuard y) : F x ≠ G y := by
  intro heq
  have hxy : x = y := third_inj D hx hy (by
    rw [F_actual hF, G_actual hG, heq])
  subst y
  have := hF.2.1
  have := hG.2.1
  omega

theorem periodic_inversion_iff_cell {C : Set ℕ} {m M x y : ℕ}
    (D : CubicReturn.PeriodicExtrema C m M) (hx : x ∈ C) (hy : y ∈ C)
    (hF : FGuard x) (hG : GGuard y) (hxy : x ≤ y) :
    G y < F x ↔ B x = B y :=
  inversion_iff_cell hxy (F_ne_G_of_periodic D hx hy hF hG)

theorem periodic_same_cell_strict {C : Set ℕ} {m M x y : ℕ}
    (D : CubicReturn.PeriodicExtrema C m M) (hx : x ∈ C) (hy : y ∈ C)
    (hF : FGuard x) (hG : GGuard y) (hcell : B x = B y) :
    G y < F x := by
  exact lt_of_le_of_ne (G_le_F_of_B_eq hcell)
    (Ne.symm (F_ne_G_of_periodic D hx hy hF hG))

theorem periodic_G_cell_unique {C : Set ℕ} {m M x y : ℕ}
    (D : CubicReturn.PeriodicExtrema C m M) (hx : x ∈ C) (hy : y ∈ C)
    (hGx : GGuard x) (hGy : GGuard y) (hcell : B x = B y) : x = y := by
  apply third_inj D hx hy
  rw [G_actual hGx, G_actual hGy]
  exact congrArg O hcell

theorem periodic_F_inverts_at_most_one_G {C : Set ℕ} {m M x y z : ℕ}
    (D : CubicReturn.PeriodicExtrema C m M)
    (hx : x ∈ C) (hy : y ∈ C) (hz : z ∈ C)
    (hF : FGuard x) (hGy : GGuard y) (hGz : GGuard z)
    (hxy : x ≤ y) (hxz : x ≤ z)
    (hyi : G y < F x) (hzi : G z < F x) : y = z := by
  have hycell := (periodic_inversion_iff_cell D hx hy hF hGy hxy).mp hyi
  have hzcell := (periodic_inversion_iff_cell D hx hz hF hGz hxz).mp hzi
  exact periodic_G_cell_unique D hy hz hGy hGz (hycell.symm.trans hzcell)

theorem G_guard_square_faces {x : ℕ} (h : GGuard x) :
    B x ^ 2 + 1 ≤ O x ∧ O x + 2 ≤ (B x + 1) ^ 2 ∧
      x ^ 3 + 2 ≤ (O x + 1) ^ 2 := by
  obtain ⟨hlo, hhi⟩ := B_source_cell x
  have hloMod : B x ^ 2 % 2 = 1 := by simp [Nat.pow_mod, h.2.2]
  have hhiMod : (B x + 1) ^ 2 % 2 = 0 := by
    simp [Nat.pow_mod, Nat.add_mod, h.2.2]
  have hxMod : x ^ 3 % 2 = 1 := by simp [Nat.pow_mod, h.1]
  have hpMod : (O x + 1) ^ 2 % 2 = 1 := by
    simp [Nat.pow_mod, Nat.add_mod, h.2.1]
  have hcell := CubicReturn.lt_O_succ_sq x
  change x ^ 3 < (O x + 1) ^ 2 at hcell
  have hp := h.2.1
  omega

noncomputable def logEta (v : ℝ) : ℝ :=
  Real.log (Real.log (v + 1) / Real.log v)

theorem logEta_pos {v : ℝ} (hv : 1 < v) : 0 < logEta v := by
  apply Real.log_pos
  apply (one_lt_div (Real.log_pos hv)).mpr
  exact Real.log_lt_log (by linarith) (by linarith)

theorem logEta_antitone {u v : ℝ} (hu : 1 < u) (huv : u ≤ v) :
    logEta v ≤ logEta u := by
  have hv : 1 < v := hu.trans_le huv
  have hup : 0 < u := by linarith
  have hvp : 0 < v := by linarith
  have hlu := Real.log_pos hu
  have hlv := Real.log_pos hv
  have hinc : Real.log (v + 1) - Real.log v ≤
      Real.log (u + 1) - Real.log u := by
    rw [← Real.log_div (by linarith : v + 1 ≠ 0) (ne_of_gt hvp),
      ← Real.log_div (by linarith : u + 1 ≠ 0) (ne_of_gt hup)]
    apply Real.log_le_log (div_pos (by linarith) hvp)
    apply (div_le_div_iff₀ hvp hup).mpr
    nlinarith
  have hmul := mul_le_mul hinc (Real.log_le_log hup huv) (le_of_lt hlu)
    (sub_nonneg.mpr (Real.log_le_log hup (by linarith : u ≤ u + 1)))
  apply Real.log_le_log (div_pos (Real.log_pos (by linarith : 1 < v + 1)) hlv)
  apply (div_le_div_iff₀ hlv hlu).mpr
  nlinarith

theorem logEta_lt_inv {v : ℝ} (hv : 1 < v) :
    logEta v < 1 / (v * Real.log v) := by
  have hvp : 0 < v := by linarith
  have hlv := Real.log_pos hv
  have hq : 1 < Real.log (v + 1) / Real.log v := by
    apply (one_lt_div hlv).mpr
    exact Real.log_lt_log hvp (by linarith)
  have hr : 1 < (v + 1) / v := by
    apply (one_lt_div hvp).mpr
    linarith
  have h₁ := Real.log_lt_sub_one_of_pos (lt_trans zero_lt_one hq) (ne_of_gt hq)
  have h₂ := Real.log_lt_sub_one_of_pos (lt_trans zero_lt_one hr) (ne_of_gt hr)
  rw [Real.log_div (by linarith : v + 1 ≠ 0) (ne_of_gt hvp)] at h₂
  calc
    logEta v < Real.log (v + 1) / Real.log v - 1 := h₁
    _ = (Real.log (v + 1) - Real.log v) / Real.log v := by
      field_simp
    _ < ((v + 1) / v - 1) / Real.log v := div_lt_div_of_pos_right h₂ hlv
    _ = 1 / (v * Real.log v) := by
      field_simp
      ring

theorem power_cells_loglog_lt {x y v : ℝ}
    (hx : 1 < x) (hy : 1 < y) (hv : 1 < v)
    (hlo : v ^ 4 ≤ y ^ 3) (hhi : x ^ 3 < (v + 1) ^ 4) :
    Real.log (Real.log x) - Real.log (Real.log y) < logEta v := by
  have hlx := Real.log_pos hx
  have hly := Real.log_pos hy
  have hlv := Real.log_pos hv
  have hlv1 := Real.log_pos (show 1 < v + 1 by linarith)
  have hloglo := Real.log_le_log (pow_pos (show 0 < v by linarith) 4) hlo
  have hloghi := Real.log_lt_log (pow_pos (show 0 < x by linarith) 3) hhi
  rw [Real.log_pow, Real.log_pow] at hloglo hloghi
  norm_num at hloglo hloghi
  have hp₁ := mul_lt_mul_of_pos_right hloghi hlv
  have hp₂ := mul_le_mul_of_nonneg_left hloglo (le_of_lt hlv1)
  have hdiv : Real.log x / Real.log y < Real.log (v + 1) / Real.log v := by
    apply (div_lt_div_iff₀ hly hlv).mpr
    nlinarith
  have hlog := Real.log_lt_log (div_pos hlx hly) hdiv
  rw [Real.log_div (ne_of_gt hlx) (ne_of_gt hly)] at hlog
  exact hlog

theorem same_cell_loglog_lt {x y v : ℕ}
    (hx : 1 < x) (hy : 1 < y) (hv : 1 < v)
    (hxc : B x = v) (hyc : B y = v) :
    Real.log (Real.log (x : ℝ)) - Real.log (Real.log (y : ℝ)) < logEta v := by
  apply power_cells_loglog_lt (by exact_mod_cast hx) (by exact_mod_cast hy)
    (by exact_mod_cast hv)
  · exact_mod_cast (B_eq_iff.mp hyc).1
  · exact_mod_cast (B_eq_iff.mp hxc).2

theorem same_cell_loglog_lt_min {m x y v : ℕ}
    (hm : 1 < m) (hmx : m ≤ x) (hmy : m ≤ y) (hmv : m ≤ v)
    (hxc : B x = v) (hyc : B y = v) :
    Real.log (Real.log (x : ℝ)) - Real.log (Real.log (y : ℝ)) < logEta m := by
  exact (same_cell_loglog_lt (hm.trans_le hmx) (hm.trans_le hmy)
    (hm.trans_le hmv) hxc hyc).trans_le
    (logEta_antitone (by exact_mod_cast hm) (by exact_mod_cast hmv))

/-- The shared cube and square forbid simultaneous unit remainders. -/
theorem cube_ne_square_successor_square_successor (x v : ℕ) :
    x ^ 3 ≠ (v ^ 2 + 1) ^ 2 + 1 := by
  intro h
  have hm := congrArg (fun n : ℕ => n % 7) h
  have hx := Nat.mod_lt x (by decide : 0 < 7)
  have hv := Nat.mod_lt v (by decide : 0 < 7)
  interval_cases hrx : x % 7 <;> interval_cases hrv : v % 7 <;>
    norm_num [Nat.add_mod, Nat.pow_mod, hrx, hrv] at hm

/-- Two actual parity switches leave at least one remainder at least three. -/
theorem guarded_OE_remainder_dichotomy {x h v : ℕ}
    (hx : x % 2 = 1) (hh : h % 2 = 0) (hv : v % 2 = 1)
    (hO : h ^ 2 ≤ x ^ 3) (hE : v ^ 2 ≤ h) :
    h ^ 2 + 3 ≤ x ^ 3 ∨ v ^ 2 + 3 ≤ h := by
  have hxp : x ^ 3 % 2 = 1 := by simp [Nat.pow_mod, hx]
  have hhp : h ^ 2 % 2 = 0 := by simp [Nat.pow_mod, hh]
  have hvp : v ^ 2 % 2 = 1 := by simp [Nat.pow_mod, hv]
  by_contra hn
  have h1 : x ^ 3 = h ^ 2 + 1 := by omega
  have h2 : h = v ^ 2 + 1 := by omega
  exact cube_ne_square_successor_square_successor x v (by rw [h1, h2])

/-- A parity-guarded OE pair has a strictly improved lower cube face. -/
theorem guarded_OE_lower_cube {x h v : ℕ}
    (hx : x % 2 = 1) (hh : h % 2 = 0) (hv : v % 2 = 1)
    (hO : h ^ 2 ≤ x ^ 3) (hE : v ^ 2 ≤ h) :
    (v ^ 2 + 1) ^ 2 + 3 ≤ x ^ 3 := by
  have hxp : x ^ 3 % 2 = 1 := by simp [Nat.pow_mod, hx]
  have hhp : h ^ 2 % 2 = 0 := by simp [Nat.pow_mod, hh]
  have hvp : v ^ 2 % 2 = 1 := by simp [Nat.pow_mod, hv]
  have h1 : h ^ 2 + 1 ≤ x ^ 3 := by omega
  have h2 : v ^ 2 + 1 ≤ h := by omega
  rcases guarded_OE_remainder_dichotomy hx hh hv hO hE with hR | hQ
  · have hp := Nat.pow_le_pow_left h2 2
    omega
  · have hp := Nat.pow_le_pow_left hQ 2
    nlinarith

theorem actual_OE_lower_cube {x : ℕ}
    (hx : x % 2 = 1) (hO : O x % 2 = 0) (hB : B x % 2 = 1) :
    (B x ^ 2 + 1) ^ 2 + 3 ≤ x ^ 3 := by
  exact guarded_OE_lower_cube hx hO hB (CubicReturn.O_sq_le x)
    (B_source_cell x).1

end Problems.Juggler.QuarticCells
