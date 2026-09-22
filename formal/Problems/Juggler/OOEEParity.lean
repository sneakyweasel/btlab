import BTCalculus.FejerBox3
import Problems.Juggler.OOEESlowModes
import Problems.Juggler.FateOOEEAssembly

/-! # The joint OOEE parity count from actual Fourier modes -/

noncomputable section
attribute [local instance] Classical.propDecidable

namespace Problems.Juggler.OOEEParity

open Finset BTCalculus.WeylDifferencing BTCalculus.FejerArc BTCalculus.FejerWeighted
open BTCalculus.FourierBoxCounting
open OOEEPhaseComparison OOEERootPhase OOEESlowModes FateOOEEAssembly

def point (x : ℝ) : BTCalculus.FejerBox3.Point :=
  ⟨⟨((x^(3/2:ℝ)/2:ℝ):UnitAddCircle), ((nestedPower x/2:ℝ):UnitAddCircle)⟩,
    ((actualRoot x/2:ℝ):UnitAddCircle)⟩

theorem arc_fract {a b x : ℝ} (ha : 0 ≤ a) (hb : b ≤ 1) :
    (x:UnitAddCircle) ∈ arc a b ↔ a ≤ Int.fract x ∧ Int.fract x < b := by
  constructor
  · rintro ⟨u, hu, he⟩
    have hu01 : u ∈ Set.Ico (0:ℝ) (0+1) := ⟨ha.trans hu.1, by linarith [hu.2]⟩
    have hx01 : Int.fract x ∈ Set.Ico (0:ℝ) (0+1) :=
      ⟨Int.fract_nonneg _, by simpa using Int.fract_lt_one x⟩
    have he' : (u:UnitAddCircle) = ((Int.fract x:ℝ):UnitAddCircle) := by
      simpa only [AddCircle.coe_fract] using he
    have hu' := (AddCircle.coe_eq_coe_iff_of_mem_Ico hu01 hx01).1 he'
    simpa only [hu', Set.mem_Ico] using hu
  · intro hx
    exact ⟨Int.fract x, hx, AddCircle.coe_fract x⟩

theorem lower_half_floor (x : ℝ) :
    ((x/2:ℝ):UnitAddCircle) ∈ arc 0 (1/2) ↔ ⌊x⌋ % 2 = 0 := by
  rw [arc_fract (by norm_num) (by norm_num)]
  have h := Sweep.cell_modEq_zero_iff (x/2)
  simp only [Sweep.cell, Int.ModEq, mul_div_cancel₀ _ (by norm_num : (2:ℝ) ≠ 0)] at h
  simpa [Int.fract_nonneg] using h.symm

theorem upper_half_floor (x : ℝ) :
    ((x/2:ℝ):UnitAddCircle) ∈ arc (1/2) 1 ↔ ⌊x⌋ % 2 = 1 := by
  rw [arc_fract (by norm_num) (by norm_num)]
  have h := Sweep.cell_modEq_one_iff (x/2)
  simp only [Sweep.cell, Int.ModEq, mul_div_cancel₀ _ (by norm_num : (2:ℝ) ≠ 0)] at h
  simpa [Int.fract_lt_one] using h.symm

theorem firstFloor_nat (n : ℕ) : firstFloor (n:ℝ) = (Nat.sqrt (n^3):ℝ) := by
  have hp : (n:ℝ)^(3/2:ℝ) = Real.sqrt ((n^3:ℕ):ℝ) := by
    rw [three_halves_eq_mul_sqrt (by positivity), ← FiberParity.two_xval]
    unfold FiberParity.xval
    ring
  rw [firstFloor, hp, Real.floor_real_sqrt_eq_nat_sqrt]
  norm_cast

theorem secondFloor_nat (n : ℕ) :
    secondFloor (n:ℝ) = (Nat.sqrt ((Nat.sqrt (n^3))^3):ℝ) := by
  rw [secondFloor, nestedPower, firstFloor_nat]
  exact firstFloor_nat (Nat.sqrt (n^3))

theorem actualRoot_floor_nat (n : ℕ) :
    ⌊actualRoot (n:ℝ)⌋ = (Nat.sqrt (Nat.sqrt ((Nat.sqrt (n^3))^3)):ℤ) := by
  rw [actualRoot, secondFloor_nat, Real.floor_real_sqrt_eq_nat_sqrt]

/-- Every floor boundary is included with its correct parity. -/
theorem point_guards {n : ℕ} (hn : n % 2 = 1) :
    ((point n).1.1 ∈ arc (1/2) 1 ∧ (point n).1.2 ∈ arc 0 (1/2) ∧
      (point n).2 ∈ arc 0 (1/2)) ↔ ooeeGuard n := by
  simp only [point, upper_half_floor, lower_half_floor]
  have hfirst : ⌊(n:ℝ)^(3/2:ℝ)⌋ = (Nat.sqrt (n^3):ℤ) := by
    have h := firstFloor_nat n
    unfold firstFloor at h
    exact_mod_cast h
  have hsecond : ⌊nestedPower (n:ℝ)⌋ = (Nat.sqrt ((Nat.sqrt (n^3))^3):ℤ) := by
    have h := secondFloor_nat n
    unfold secondFloor at h
    exact_mod_cast h
  rw [hfirst, hsecond, actualRoot_floor_nat]
  constructor
  · rintro ⟨h1,h2,h3⟩
    have ho : Nat.sqrt (n^3) % 2 = 1 := by exact_mod_cast h1
    have he : Nat.sqrt ((Nat.sqrt (n^3))^3) % 2 = 0 := by exact_mod_cast h2
    refine ⟨hn, ?_, ?_, ?_⟩
    · simpa only [floorPower_odd_eq hn] using ho
    · simpa only [floorPower_odd_eq hn, floorPower_odd_eq ho] using he
    · simpa only [floorPower_odd_eq hn, floorPower_odd_eq ho, floorPower_even_eq he] using
        (show Nat.sqrt (Nat.sqrt ((Nat.sqrt (n^3))^3)) % 2 = 0 by exact_mod_cast h3)
  · rintro ⟨_,h1,h2,h3⟩
    rw [floorPower_odd_eq hn] at h1 h2 h3
    rw [floorPower_odd_eq h1] at h2 h3
    rw [floorPower_even_eq h2] at h3
    exact ⟨by exact_mod_cast h1, by exact_mod_cast h2, by exact_mod_cast h3⟩

theorem mode_phase (i j k : ℤ) (x : ℝ) :
    BTCalculus.FejerBox3.mode i j k (point x) = phase (actualPhase ((j:ℝ)/2) i k x) := by
  simp only [BTCalculus.FejerBox3.mode, BTCalculus.FejerBox.mode, point,
    OOEECarryFourier.fourier_phase, OOEECarryFourier.phase_add]
  congr 1
  unfold actualPhase
  ring

theorem actual_guard_discrepancy {a H N : ℕ} {E : ℝ} (ha : a % 2 = 1)
    (hH : 3 ≤ H) (hN : 0 < N) (hE : 0 ≤ E)
    (hmodes : ∀ i j k : ℤ, |i| ≤ H → |j| ≤ H → |k| ≤ H →
      (i ≠ 0 ∨ j ≠ 0 ∨ k ≠ 0) →
      ‖∑ n ∈ range N, phase (actualPhase ((j:ℝ)/2) i k ((a:ℝ)+2*n))‖ ≤ E) :
    |(count (fun n => ooeeGuard (a+2*n)) N:ℝ)/N-1/8| ≤
      15/Real.sqrt ((H:ℝ)+1)+((mass H)^3+6*mass H)*(E/N) := by
  have hn : (0:ℝ) < N := by exact_mod_cast hN
  have h := BTCalculus.FejerBox3.finite_box_discrepancy
    (fun n => point ((a:ℝ)+2*n)) (a := 1/2) (b := 1) (c := 0) (d := 1/2) (e := 0) (f := 1/2)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hH hN (div_nonneg hE hn.le) (by
      intro i j k hi hj hk hne
      simp only [average, mode_phase, norm_div, Complex.norm_natCast]
      exact div_le_div_of_nonneg_right (hmodes i j k hi hj hk hne) hn.le)
  have hpred : (fun n : ℕ => (point ((a:ℝ)+2*n)).1.1 ∈ arc (1/2) 1 ∧
      (point ((a:ℝ)+2*n)).1.2 ∈ arc 0 (1/2) ∧ (point ((a:ℝ)+2*n)).2 ∈ arc 0 (1/2)) =
      (fun n => ooeeGuard (a+2*n)) := by
    funext n
    apply propext
    have hp : (a+2*n)%2 = 1 := by omega
    simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] using point_guards hp
  rw [hpred] at h
  norm_num only at h
  exact h

/-- The actual count uses proved cancellation; only the explicit resonance windows are excluded. -/
theorem nonresonant_guard_discrepancy (H : ℕ) (hH : 3 ≤ H) {D : ℝ} (hD : 0 ≤ D) :
    ∃ B : ℝ, 0 < B ∧ ∃ P0 : ℝ, ∀ P : ℝ, P0 ≤ P → ∀ a N : ℕ, ∀ C : ℝ,
      a % 2 = 1 → 0 < N → 0 < C →
      (∀ n < N, P ≤ (a:ℝ)+2*n ∧ (a:ℝ)+2*n ≤ 2*P ∧ (a:ℝ)+2*n ≤ P+D*P^(7/16:ℝ)) →
      (N:ℝ) ≤ D*P^(7/16:ℝ) → (9/32)*D*H ≤ C →
      (∀ k : ℤ, |k| ≤ H → k ≠ 0 → Nonresonant P C k) →
      |(count (fun n => ooeeGuard (a+2*n)) N:ℝ)/N-1/8| ≤
        15/Real.sqrt ((H:ℝ)+1)+((mass H)^3+6*mass H)*
          ((B*P^(13/32:ℝ)+(2/C)*P^(7/16:ℝ)+3*Real.pi*H*D*P^(1/16:ℝ)+1)/N) := by
  let s : Finset (ℤ × ℤ × ℤ) :=
    Icc (-(H:ℤ)) H ×ˢ (Icc (-(H:ℤ)) H ×ˢ Icc (-(H:ℤ)) H)
  obtain ⟨B,hB,P0,hfast⟩ := finite_actual_mixed_modes s hD
  refine ⟨B,hB,max 1 P0,?_⟩
  intro P hP a N C ha hN hC hpoints hND hdom hnr
  have hP1 : 1 ≤ P := (le_max_left _ _).trans hP
  have hP0 : 0 < P := by linarith
  have hPP : P0 ≤ P := (le_max_right _ _).trans hP
  apply actual_guard_discrepancy ha hH hN (by positivity)
  intro i j k hi hj hk hne
  have hkR : |(k:ℝ)| ≤ H := by exact_mod_cast hk
  by_cases hmix : i ≠ 0 ∨ j ≠ 0
  · have hmem : (i,j,k) ∈ s := by
      simpa only [s, mem_product, mem_Icc] using And.intro (abs_le.mp hi) (And.intro (abs_le.mp hj) (abs_le.mp hk))
    have hm := hfast P hPP a N (fun n hn => ⟨(hpoints n hn).1,(hpoints n hn).2.1⟩)
      hND (i,j,k) hmem hmix
    exact hm.trans (by
      have hpos : 0 ≤ (2/C)*P^(7/16:ℝ)+3*Real.pi*H*D*P^(1/16:ℝ)+1 := by positivity
      linarith)
  · have hi0 : i = 0 := by tauto
    have hj0 : j = 0 := by tauto
    subst i
    subst j
    have hk0 : k ≠ 0 := by tauto
    have hd : (9/32)*D*|(k:ℝ)| ≤ C :=
      (mul_le_mul_of_nonneg_left hkR (by positivity)).trans hdom
    have hs := actual_slow_samples (k := (k:ℝ)) N hP1 hD hC
      (fun n hn => ⟨(hpoints n hn).1,(hpoints n hn).2.2⟩) hd (hnr k hk hk0)
    simp only [actualPhase, Int.cast_zero, zero_div, zero_mul, zero_add]
    apply hs.trans
    have hkterm : 3*Real.pi*|(k:ℝ)| *D*P^(1/16:ℝ) ≤ 3*Real.pi*H*D*P^(1/16:ℝ) := by gcongr
    nlinarith [Real.rpow_pos_of_pos hP0 (13/32)]

end Problems.Juggler.OOEEParity
