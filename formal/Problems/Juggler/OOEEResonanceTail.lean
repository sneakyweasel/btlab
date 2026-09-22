import Problems.Juggler.OOEEFibreResonance
import Problems.Juggler.FateThinFibers
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-! # Counting OOEE slow resonances and their reciprocal tails -/

noncomputable section
attribute [local instance] Classical.propDecidable

namespace Problems.Juggler.OOEEResonanceTail

open Finset OOEEFibreResonance

def countConstant (H : ℕ) (C : ℝ) : ℝ := (H:ℝ)*(80*C+10*H)

theorem alpha_nonneg (m : ℕ) : 0 ≤ alpha m := by unfold alpha; positivity

theorem decay_antitone {u m : ℕ} (hu : 1 ≤ u) (hum : u ≤ m) : decay m ≤ decay u := by
  exact Real.rpow_le_rpow_of_nonpos (by exact_mod_cast hu)
    (by exact_mod_cast hum) (by norm_num)

theorem alpha_step {m : ℕ} (hm : 1 ≤ m) : decay (m+1)/4 ≤ alpha (m+1)-alpha m := by
  have hm0 : (0:ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hb := Numerics.bernoulli_le (a := (m:ℝ)+1) (h := -1)
    (p := 2/9) (q := -7/9) (by positivity) (by linarith)
    (by norm_num) (by norm_num) (by norm_num)
  rw [show (m:ℝ)+1+ -1 = m by ring] at hb
  dsimp [alpha,decay]
  push_cast
  linarith

theorem two_power_le {p : ℝ} (hp : p ≤ 1) : (2:ℝ)^p ≤ 2 := by
  simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le
    (by norm_num : (1:ℝ) ≤ 2) hp

theorem alpha_double_le (u : ℕ) : alpha (2*u) ≤ (9/4)*(u:ℝ)^(2/9:ℝ) := by
  have ht := two_power_le (p := (2/9:ℝ)) (by norm_num)
  have hu : 0 ≤ (u:ℝ)^(2/9:ℝ) := by positivity
  dsimp [alpha]
  push_cast
  rw [Real.mul_rpow (by norm_num) (by positivity)]
  nlinarith [mul_le_mul_of_nonneg_right ht hu]

theorem decay_double_le (u : ℕ) : decay u ≤ 2*decay (2*u) := by
  have ht := two_power_le (p := (7/9:ℝ)) (by norm_num)
  have he : decay u = (2:ℝ)^(7/9:ℝ)*decay (2*u) := by
    dsimp [decay]
    push_cast
    rw [Real.mul_rpow (by norm_num) (by positivity),
      show (-7/9:ℝ) = -(7/9) by norm_num,Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2)]
    field_simp
  have hd : 0 ≤ decay (2*u) := by unfold decay; positivity
  nlinarith [mul_le_mul_of_nonneg_right ht hd]

/-- A closed integer-neighbourhood fits in a shifted arc, even for large widths. -/
theorem resonant_fract {x δ : ℝ} {z : ℤ} (hz : |x-(z:ℝ)| ≤ δ) :
    Int.fract (x+δ) ≤ 2*δ := by
  have hb := abs_le.mp hz
  have hf : z ≤ ⌊x+δ⌋ := Int.le_floor.mpr (by linarith)
  have hfR : (z:ℝ) ≤ (⌊x+δ⌋:ℝ) := by exact_mod_cast hf
  change x+δ-(⌊x+δ⌋:ℝ) ≤ 2*δ
  linarith

/-- A fixed positive frequency has O(u^(2/9)) resonant targets in (u,2u]. -/
theorem resonance_count_one {u q : ℕ} (hu : 1 ≤ u) (hq : 1 ≤ q)
    {C : ℝ} (hC : 0 ≤ C) :
    ((Ioc u (2*u)).filter (fun m => ∃ z : ℤ,
      |(q:ℝ)*alpha m-(z:ℝ)| ≤ C*decay m)).card ≤
        (80*C+10*(q:ℝ))*(u:ℝ)^(2/9:ℝ) := by
  have hu0 : (0:ℝ) < u := by exact_mod_cast (show 0 < u by omega)
  have hq0 : (0:ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hqR : (1:ℝ) ≤ q := by exact_mod_cast hq
  let δ : ℝ := C*decay u
  let d : ℝ := (q:ℝ)/4*decay (2*u)
  have hd : 0 < d := by dsimp [d,decay]; positivity
  have hδ : 0 ≤ δ := by dsimp [δ,decay]; positivity
  have hstep (m : ℕ) (hm : u < m) (hm2 : m < 2*u) :
      d ≤ ((q:ℝ)*alpha (m+1)+δ)-((q:ℝ)*alpha m+δ) := by
    have hs := alpha_step (show 1 ≤ m by omega)
    have he := decay_antitone (show 1 ≤ m+1 by omega) (show m+1 ≤ 2*u by omega)
    have hmul := mul_le_mul_of_nonneg_left hs hq0.le
    have hmul2 := mul_le_mul_of_nonneg_left he hq0.le
    dsimp [d]
    linarith
  have hcover : (Ioc u (2*u)).filter (fun m => ∃ z : ℤ,
        |(q:ℝ)*alpha m-(z:ℝ)| ≤ C*decay m) ⊆
      (Ioc u (2*u)).filter (fun m => 0 ≤ Int.fract ((q:ℝ)*alpha m+δ) ∧
        Int.fract ((q:ℝ)*alpha m+δ) < 0+(2*δ+d)) := by
    intro m hm
    obtain ⟨hmI,z,hz⟩ := mem_filter.mp hm
    have hw : C*decay m ≤ δ := mul_le_mul_of_nonneg_left
      (decay_antitone hu (mem_Ioc.mp hmI).1.le) hC
    have hf := resonant_fract (hz.trans hw)
    exact mem_filter.mpr ⟨hmI,Int.fract_nonneg _,by linarith⟩
  have harc := FiberParity.arc_count_le (fun m => (q:ℝ)*alpha m+δ)
    u (2*u) (by omega) d 0 (2*δ+d) hd (by positivity) hstep
  have hwindow : ((⌊(q:ℝ)*alpha (2*u)+δ⌋-⌊(q:ℝ)*alpha (u+1)+δ⌋+1:ℤ):ℝ) ≤
      5*(q:ℝ)*(u:ℝ)^(2/9:ℝ) := by
    have hf1 := Int.floor_le ((q:ℝ)*alpha (2*u)+δ)
    have hf2 := Int.lt_floor_add_one ((q:ℝ)*alpha (u+1)+δ)
    have hlo : 0 ≤ (q:ℝ)*alpha (u+1) := mul_nonneg hq0.le (alpha_nonneg _)
    have hp1 : 1 ≤ (u:ℝ)^(2/9:ℝ) := Real.one_le_rpow (by exact_mod_cast hu) (by norm_num)
    have hmain := mul_le_mul_of_nonneg_left (alpha_double_le u) hq0.le
    push_cast
    nlinarith
  have hwidth : (2*δ+d)/d+1 ≤ 16*C/q+2 := by
    have hδ2 : δ ≤ 2*C*decay (2*u) := by
      have h := mul_le_mul_of_nonneg_left (decay_double_le u) hC
      dsimp [δ]
      nlinarith
    have he : (8*C/q)*d = 2*C*decay (2*u) := by dsimp [d]; field_simp; ring
    have hratio : δ/d ≤ 8*C/q := (div_le_iff₀ hd).mpr (by rw [he]; exact hδ2)
    have hid : (2*δ+d)/d+1 = 2*(δ/d)+2 := by field_simp; ring
    rw [hid,show 16*C/(q:ℝ) = 2*(8*C/q) by ring]
    linarith
  have hcard : (((Ioc u (2*u)).filter (fun m => ∃ z : ℤ,
      |(q:ℝ)*alpha m-(z:ℝ)| ≤ C*decay m)).card:ℝ) ≤
      (((Ioc u (2*u)).filter (fun m => 0 ≤ Int.fract ((q:ℝ)*alpha m+δ) ∧
        Int.fract ((q:ℝ)*alpha m+δ) < 0+(2*δ+d))).card:ℝ) := by
    exact_mod_cast card_le_card hcover
  calc _ ≤ _ := hcard.trans harc
    _ ≤ (5*(q:ℝ)*(u:ℝ)^(2/9:ℝ))*((2*δ+d)/d+1) :=
      mul_le_mul_of_nonneg_right hwindow (by positivity)
    _ ≤ (5*(q:ℝ)*(u:ℝ)^(2/9:ℝ))*(16*C/q+2) :=
      mul_le_mul_of_nonneg_left hwidth (by positivity)
    _ = _ := by field_simp; ring

theorem resonance_count {u H : ℕ} (hu : 1 ≤ u) {C : ℝ} (hC : 0 ≤ C) :
    (((Ioc u (2*u)).filter (Resonant H C)).card:ℝ) ≤
      countConstant H C*(u:ℝ)^(2/9:ℝ) := by
  let S (j : ℕ) := (Ioc u (2*u)).filter (fun m => ∃ z : ℤ,
    ((|(j+1:ℕ)*alpha m-(z:ℝ)|):ℝ) ≤ C*decay m)
  have hcover : (Ioc u (2*u)).filter (Resonant H C) ⊆ (range H).biUnion S := by
    intro m hm
    obtain ⟨hmI,q,hq1,hqH,z,hz⟩ := mem_filter.mp hm
    refine mem_biUnion.mpr ⟨q-1,mem_range.mpr (by omega),?_⟩
    apply mem_filter.mpr
    refine ⟨hmI,z,?_⟩
    simpa only [Nat.sub_add_cancel hq1] using hz
  have hper (j : ℕ) (hj : j ∈ range H) : ((S j).card:ℝ) ≤
      (80*C+10*(H:ℝ))*(u:ℝ)^(2/9:ℝ) := by
    have h := resonance_count_one hu (show 1 ≤ j+1 by omega) hC
    have hjH : (j+1:ℕ) ≤ H := by simpa using mem_range.mp hj
    have hjR : ((j+1:ℕ):ℝ) ≤ H := by exact_mod_cast hjH
    exact h.trans (by gcongr)
  have hc : (((Ioc u (2*u)).filter (Resonant H C)).card:ℝ) ≤
      ∑ j ∈ range H, ((S j).card:ℝ) := by
    exact_mod_cast (card_le_card hcover).trans card_biUnion_le
  apply hc.trans
  have hs := sum_le_sum hper
  simpa only [sum_const,card_range,nsmul_eq_mul,countConstant,mul_assoc] using hs

theorem resonance_block_mass {u H : ℕ} (hu : 1 ≤ u) {C : ℝ} (hC : 0 ≤ C) :
    (∑ m ∈ (Ioc u (2*u)).filter (Resonant H C), (1:ℝ)/m) ≤
      countConstant H C*decay u := by
  have hu0 : (0:ℝ) < u := by exact_mod_cast (show 0 < u by omega)
  have hterm : ∀ m ∈ (Ioc u (2*u)).filter (Resonant H C), (1:ℝ)/m ≤ 1/u := by
    intro m hm
    exact one_div_le_one_div_of_le hu0 (by exact_mod_cast (mem_Ioc.mp (mem_filter.mp hm).1).1.le)
  have hs := sum_le_card_nsmul _ _ _ hterm
  rw [nsmul_eq_mul] at hs
  have he : (u:ℝ)^(2/9:ℝ)*(1/u) = decay u := by
    rw [show (1:ℝ)/u = (u:ℝ)^(-1:ℝ) by rw [Real.rpow_neg_one,one_div],
      ← Real.rpow_add hu0]
    norm_num [decay]
  calc _ ≤ _ := hs
    _ ≤ (countConstant H C*(u:ℝ)^(2/9:ℝ))*(1/u) :=
      mul_le_mul_of_nonneg_right (resonance_count hu hC) (by positivity)
    _ = _ := by rw [mul_assoc,he]

theorem decay_pow_two_mul {U : ℕ} (hU : 1 ≤ U) (i : ℕ) :
    decay (2^i*U) = ((2:ℝ)^(-7/9:ℝ))^i*decay U := by
  dsimp [decay]
  push_cast
  rw [Real.mul_rpow (by positivity) (by positivity)]
  congr 1
  rw [← Real.rpow_natCast (2:ℝ) i,← Real.rpow_mul (by norm_num),
    ← Real.rpow_natCast ((2:ℝ)^(-7/9:ℝ)) i,← Real.rpow_mul (by norm_num)]
  ring_nf

theorem resonance_dyadic_mass {U H : ℕ} (hU : 1 ≤ U) {C : ℝ} (hC : 0 ≤ C) (K : ℕ) :
    (∑ m ∈ (Ioc U (2^K*U)).filter (Resonant H C), (1:ℝ)/m) ≤
      ∑ i ∈ range K, countConstant H C*decay (2^i*U) := by
  induction K with
  | zero => simp
  | succ K ih =>
    have hle1 : U ≤ 2^K*U := Nat.le_mul_of_pos_left U (by positivity)
    have hle2 : 2^K*U ≤ 2^(K+1)*U := by gcongr <;> omega
    rw [← Ioc_union_Ioc_eq_Ioc hle1 hle2,filter_union,
      sum_union (disjoint_filter_filter (FiberParity.Ioc_disjoint_next _ _ _)),sum_range_succ]
    have hb := resonance_block_mass (H := H) (hU.trans hle1) hC
    rw [show 2*(2^K*U) = 2^(K+1)*U by ring] at hb
    linarith

theorem dyadic_ratio_le : (2:ℝ)^(-7/9:ℝ) ≤ 2/3 := by
  rw [Numerics.rpow_le_iff_pow (n := 9) (by norm_num) (by norm_num) (by norm_num)]
  norm_num

/-- Uniform in the finite upper cutoff; hence a summable reciprocal tail. -/
theorem resonance_tail {U N H : ℕ} (hU : 1 ≤ U) {C : ℝ} (hC : 0 ≤ C) :
    (∑ m ∈ (Ioc U N).filter (Resonant H C), (1:ℝ)/m) ≤
      3*countConstant H C*decay U := by
  have hcov : (Ioc U N).filter (Resonant H C) ⊆
      (Ioc U (2^N*U)).filter (Resonant H C) := by
    apply filter_subset_filter
    apply Ioc_subset_Ioc_right
    exact Nat.lt_two_pow_self.le.trans (Nat.le_mul_of_pos_right _ (by omega))
  have hs := sum_le_sum_of_subset_of_nonneg hcov
    (fun m _ _ => by positivity : ∀ m ∈ (Ioc U (2^N*U)).filter (Resonant H C),
      m ∉ (Ioc U N).filter (Resonant H C) → (0:ℝ) ≤ 1/m)
  let r : ℝ := (2:ℝ)^(-7/9:ℝ)
  have hr0 : 0 ≤ r := by dsimp [r]; positivity
  have hr1 : r < 1 := by have h := dyadic_ratio_le; dsimp [r]; linarith
  have hgeom : ∑ i ∈ range N, r^i ≤ 3 := by
    have hg : ∑ i ∈ range N, r^i ≤ r^0/(1-r) := by
      rw [range_eq_Ico]
      exact geom_sum_Ico_le_of_lt_one hr0 hr1
    have hratio : 1/(1-r) ≤ 3 := by
      rw [div_le_iff₀ (by linarith)]
      have h := dyadic_ratio_le
      dsimp [r]
      linarith
    exact hg.trans (by simpa using hratio)
  have hcoef : 0 ≤ countConstant H C*decay U := by dsimp [countConstant,decay]; positivity
  have he : (∑ i ∈ range N, countConstant H C*decay (2^i*U)) =
      (countConstant H C*decay U)*(∑ i ∈ range N, r^i) := by
    rw [mul_sum]
    apply sum_congr rfl
    intro i _
    rw [decay_pow_two_mul hU i]
    dsimp [r]
    ring
  calc _ ≤ _ := hs
    _ ≤ _ := resonance_dyadic_mass hU hC N
    _ = _ := he
    _ ≤ (countConstant H C*decay U)*3 := mul_le_mul_of_nonneg_left hgeom hcoef
    _ = _ := by ring

/-- Every fixed deviation of the actual fibre count has an eventual reciprocal tail. -/
theorem count_poor_tail {η : ℝ} (hη : 0 < η) :
    ∃ D : ℝ, 0 < D ∧ ∃ M : ℕ, 64 ≤ M ∧ ∀ U N : ℕ, M ≤ U →
      (∑ m ∈ (Ioc U N).filter (CountPoor η), (1:ℝ)/m) ≤ D*(U:ℝ)^(-7/9:ℝ) := by
  obtain ⟨H,hH,C,hC,M,hM,hinc⟩ := count_poor_resonant hη
  have hHp : (0:ℝ) < H := by exact_mod_cast (show 0 < H by omega)
  refine ⟨3*countConstant H C,by dsimp [countConstant]; positivity,M,hM,?_⟩
  intro U N hU
  have hcov : (Ioc U N).filter (CountPoor η) ⊆ (Ioc U N).filter (Resonant H C) := by
    intro m hm
    obtain ⟨hmI,hpoor⟩ := mem_filter.mp hm
    exact mem_filter.mpr ⟨hmI,hinc m (by have := (mem_Ioc.mp hmI).1; omega) hpoor⟩
  have hs := sum_le_sum_of_subset_of_nonneg hcov
    (fun m _ _ => by positivity : ∀ m ∈ (Ioc U N).filter (Resonant H C),
      m ∉ (Ioc U N).filter (CountPoor η) → (0:ℝ) ≤ 1/m)
  exact hs.trans (resonance_tail (by omega) hC.le)

/-- The same tail bound for the infinite series of deficient-target reciprocals. -/
theorem count_poor_tsum_tail {η : ℝ} (hη : 0 < η) :
    ∃ D : ℝ, 0 < D ∧ ∃ M : ℕ, 64 ≤ M ∧ ∀ U : ℕ, M ≤ U →
      Summable (fun m : ℕ => if U < m ∧ CountPoor η m then (1:ℝ)/m else 0) ∧
      (∑' m : ℕ, if U < m ∧ CountPoor η m then (1:ℝ)/m else 0) ≤ D*(U:ℝ)^(-7/9:ℝ) := by
  obtain ⟨D,hD,M,hM,htail⟩ := count_poor_tail hη
  refine ⟨D,hD,M,hM,?_⟩
  intro U hU
  have hn : ∀ m : ℕ, 0 ≤ (if U < m ∧ CountPoor η m then (1:ℝ)/m else 0) := by
    intro m
    split_ifs <;> positivity
  have hf (s : Finset ℕ) :
      (∑ m ∈ s, if U < m ∧ CountPoor η m then (1:ℝ)/m else 0) ≤ D*(U:ℝ)^(-7/9:ℝ) := by
    rw [← sum_filter]
    have hcov : s.filter (fun m => U < m ∧ CountPoor η m) ⊆
        (Ioc U (s.sup id)).filter (CountPoor η) := by
      intro m hm
      obtain ⟨hms,hmU,hpoor⟩ := mem_filter.mp hm
      exact mem_filter.mpr ⟨mem_Ioc.mpr ⟨hmU,le_sup (f := id) hms⟩,hpoor⟩
    have hs := sum_le_sum_of_subset_of_nonneg hcov
      (fun m _ _ => by positivity : ∀ m ∈ (Ioc U (s.sup id)).filter (CountPoor η),
        m ∉ s.filter (fun m => U < m ∧ CountPoor η m) → (0:ℝ) ≤ 1/m)
    exact hs.trans (htail U (s.sup id) hU)
  exact ⟨summable_of_sum_le hn hf,Real.tsum_le_of_sum_le hn hf⟩

end Problems.Juggler.OOEEResonanceTail
