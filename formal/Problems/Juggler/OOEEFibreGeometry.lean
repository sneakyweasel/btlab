import Problems.Juggler.OOEEParity
import Problems.Juggler.OddPredecessorTransport

/-! # Exact OOEE target fibres and their source scale

The inverse thresholds retain both ceilings. Odd candidates are enumerated
without an endpoint approximation, then compared with the real power scale.
-/

noncomputable section
attribute [local instance] Classical.propDecidable

namespace Problems.Juggler.OOEEFibreGeometry

open Finset OddPredecessorTransport FateOOEEAssembly

def inverse (a : ℕ) : ℕ := ⌈(a:ℝ)^(2/3:ℝ)⌉₊
def endpoint (m : ℕ) : ℕ := inverse (inverse (m^4))
def base (m : ℕ) : ℝ := (m:ℝ)^(16/9:ℝ)
def scale (m : ℕ) : ℝ := (m:ℝ)^(7/9:ℝ)
def firstOdd (m : ℕ) : ℕ := 2*(endpoint m/2)+1
def candidateCount (m : ℕ) : ℕ := endpoint (m+1)/2-endpoint m/2
def sample (m j : ℕ) : ℕ := firstOdd m+2*j
def candidates (m : ℕ) : Finset ℕ := (range (candidateCount m)).image (sample m)
def fibre (m : ℕ) : Finset ℕ := (candidates m).filter ooeeGuard

theorem inverse_le (a n : ℕ) : inverse a ≤ n ↔ a ≤ oddMap n := by
  rw [inverse, Nat.ceil_le, Numerics.rpow_le_iff_pow (n := 3) (by positivity) (by positivity) (by norm_num)]
  norm_num
  rw [oddMap, Nat.le_sqrt]
  norm_cast
  simp only [pow_two]

theorem inverse_monotone : Monotone inverse := by
  intro a b hab
  exact Nat.ceil_le_ceil (Real.rpow_le_rpow (by positivity) (by exact_mod_cast hab) (by norm_num))

theorem endpoint_monotone : Monotone endpoint := by
  intro a b hab
  exact inverse_monotone (inverse_monotone (Nat.pow_le_pow_left hab 4))

theorem endpoint_le (m n : ℕ) : endpoint m ≤ n ↔ m^4 ≤ oddMap (oddMap n) := by
  rw [endpoint, inverse_le, inverse_le]

theorem formal_cell (m n : ℕ) :
    Nat.sqrt (Nat.sqrt (oddMap (oddMap n))) = m ↔ endpoint m ≤ n ∧ n < endpoint (m+1) := by
  have h (a v : ℕ) : a ≤ Nat.sqrt (Nat.sqrt v) ↔ a^4 ≤ v := by
    rw [Nat.le_sqrt, Nat.le_sqrt]
    ring_nf
  have h1 := h m (oddMap (oddMap n))
  have h2 := h (m+1) (oddMap (oddMap n))
  have he1 := endpoint_le m n
  have he2 := endpoint_le (m+1) n
  omega

theorem actual_four_steps {n : ℕ} (hn : ooeeGuard n) :
    floorPower^[4] n = Nat.sqrt (Nat.sqrt (oddMap (oddMap n))) := by
  obtain ⟨h0,h1,h2,h3⟩ := hn
  have ho : oddMap n % 2 = 1 := by simpa only [oddMap_eq_step h0] using h1
  have he : oddMap (oddMap n) % 2 = 0 := by
    simpa only [oddMap_eq_step h0, oddMap_eq_step h1] using h2
  have hq : Nat.sqrt (oddMap (oddMap n)) % 2 = 0 := by
    simpa only [oddMap_eq_step h0, oddMap_eq_step h1, floorPower_even_eq h2] using h3
  change floorPower (floorPower (floorPower (floorPower n))) = _
  rw [← oddMap_eq_step h0, ← oddMap_eq_step ho, floorPower_even_eq he, floorPower_even_eq hq]

theorem sample_injective (m : ℕ) : Function.Injective (sample m) := by
  intro a b hab
  dsimp [sample] at hab
  omega

theorem mem_candidates {m n : ℕ} : n ∈ candidates m ↔
    n % 2 = 1 ∧ endpoint m ≤ n ∧ n < endpoint (m+1) := by
  have hL := endpoint_monotone (Nat.le_succ m)
  have hdiv : endpoint m/2 ≤ endpoint (m+1)/2 := Nat.div_le_div_right hL
  simp only [candidates, mem_image, mem_range]
  constructor
  · rintro ⟨j,hj,rfl⟩
    dsimp [sample, firstOdd, candidateCount] at *
    omega
  · rintro ⟨hn,hl,hu⟩
    refine ⟨n/2-endpoint m/2, ?_, ?_⟩ <;> dsimp [sample, firstOdd, candidateCount] <;> omega

theorem sample_mem {m j : ℕ} (hj : j < candidateCount m) : sample m j ∈ candidates m :=
  mem_image.mpr ⟨j,mem_range.mpr hj,rfl⟩

theorem candidate_card (m : ℕ) : (candidates m).card = candidateCount m := by
  rw [candidates, Finset.card_image_of_injective _ (sample_injective m), card_range]

/-- The finite set is exactly the actual guarded predecessor fibre. -/
theorem mem_fibre {m n : ℕ} : n ∈ fibre m ↔ ooeeGuard n ∧ floorPower^[4] n = m := by
  rw [fibre, mem_filter, mem_candidates]
  constructor
  · rintro ⟨⟨_,hl,hu⟩,hg⟩
    exact ⟨hg,(actual_four_steps hg).trans ((formal_cell m n).mpr ⟨hl,hu⟩)⟩
  · rintro ⟨hg,ht⟩
    exact ⟨⟨hg.1,(formal_cell m n).mp ((actual_four_steps hg).symm.trans ht)⟩,hg⟩

theorem fibre_card_count (m : ℕ) : (fibre m).card =
    BTCalculus.FourierBoxCounting.count (fun j => ooeeGuard (firstOdd m+2*j)) (candidateCount m) := by
  unfold fibre candidates BTCalculus.FourierBoxCounting.count
  rw [Finset.filter_image, Finset.card_image_of_injective _ (sample_injective m)]
  rfl

theorem endpoint_bounds {m : ℕ} (hm : 1 ≤ m) :
    base m ≤ endpoint m ∧ (endpoint m:ℝ) ≤ base m+2 := by
  have hm0 : (0:ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  let t : ℝ := ((m^4:ℕ):ℝ)^(2/3:ℝ)
  have ht1 : 1 ≤ t := Real.one_le_rpow
    (by exact_mod_cast (show 1 ≤ m^4 from Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ (by omega)))) (by norm_num)
  have ht0 : 0 < t := by linarith
  have hB0 : 0 ≤ (inverse (m^4):ℝ) := by positivity
  have hlo : t ≤ (inverse (m^4):ℝ) := Nat.le_ceil _
  have hhi : (inverse (m^4):ℝ) ≤ t+1 := (Nat.ceil_lt_add_one (by positivity : 0 ≤ t)).le
  have hAlo : ((inverse (m^4):ℝ)^(2/3:ℝ)) ≤ (endpoint m:ℝ) := Nat.le_ceil _
  have hAhi : (endpoint m:ℝ) ≤ (inverse (m^4):ℝ)^(2/3:ℝ)+1 :=
    (Nat.ceil_lt_add_one (Real.rpow_nonneg hB0 _)).le
  have ht : t^(2/3:ℝ) = base m := by
    dsimp [t,base]
    rw [Nat.cast_pow, ← Real.rpow_natCast, ← Real.rpow_mul hm0.le, ← Real.rpow_mul hm0.le]
    norm_num
  have hpowlo := Real.rpow_le_rpow ht0.le hlo (by norm_num : (0:ℝ) ≤ 2/3)
  have hpowhi := Real.rpow_le_rpow hB0 hhi (by norm_num : (0:ℝ) ≤ 2/3)
  have hb := Numerics.bernoulli_le (a := t) (h := 1) (p := 2/3) (q := -1/3)
    ht0 (by linarith) (by norm_num) (by norm_num) (by norm_num)
  have hi : t^(-1/3:ℝ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos ht1 (by norm_num)
  rw [ht] at hpowlo hb
  exact ⟨hpowlo.trans hAlo,by linarith⟩

theorem power_increment {m : ℕ} (hm : 1 ≤ m) :
    (16/9)*scale m ≤ base (m+1)-base m ∧
      base (m+1)-base m ≤ (16/9)*scale m+2 := by
  have hm0 : (0:ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hm1 : (1:ℝ) ≤ m := by exact_mod_cast hm
  have hl := Numerics.bernoulli_ge (a := (m:ℝ)) (h := 1) (p := 16/9) (q := 7/9)
    hm0 (by linarith) (by norm_num) (by norm_num)
  have hu := Numerics.bernoulli_ge (a := (m:ℝ)+1) (h := -1) (p := 16/9) (q := 7/9)
    (by positivity) (by linarith) (by norm_num) (by norm_num)
  have hb := Numerics.bernoulli_le (a := (m:ℝ)) (h := 1) (p := 7/9) (q := -2/9)
    hm0 (by linarith) (by norm_num) (by norm_num) (by norm_num)
  have hi : (m:ℝ)^(-2/9:ℝ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hm1 (by norm_num)
  rw [show (m:ℝ)+1+ -1 = m by ring] at hu
  dsimp [base,scale]
  push_cast
  constructor <;> linarith

theorem endpoint_gap_bounds {m : ℕ} (hm : 1 ≤ m) :
    (16/9)*scale m-2 ≤ (endpoint (m+1):ℝ)-endpoint m ∧
      (endpoint (m+1):ℝ)-endpoint m ≤ (16/9)*scale m+4 := by
  have hl := endpoint_bounds hm
  have hu := endpoint_bounds (show 1 ≤ m+1 by omega)
  have hi := power_increment hm
  constructor <;> linarith [hl.1,hl.2,hu.1,hu.2,hi.1,hi.2]

theorem candidate_rounding (m : ℕ) :
    |(candidateCount m:ℝ)-((endpoint (m+1):ℝ)-endpoint m)/2| ≤ 1 := by
  have hL : endpoint m ≤ endpoint (m+1) := endpoint_monotone (Nat.le_succ m)
  have hlo : endpoint (m+1) ≤ endpoint m+2*candidateCount m+1 := by
    dsimp [candidateCount]
    omega
  have hhi : endpoint m+2*candidateCount m ≤ endpoint (m+1)+1 := by
    dsimp [candidateCount]
    omega
  have hloR : (endpoint (m+1):ℝ) ≤ endpoint m+2*candidateCount m+1 := by exact_mod_cast hlo
  have hhiR : (endpoint m:ℝ)+2*candidateCount m ≤ endpoint (m+1)+1 := by exact_mod_cast hhi
  exact abs_le.mpr ⟨by linarith,by linarith⟩

theorem candidate_count_error {m : ℕ} (hm : 1 ≤ m) :
    |(candidateCount m:ℝ)-(8/9)*scale m| ≤ 3 := by
  have he := endpoint_gap_bounds hm
  have hc := abs_le.mp (candidate_rounding m)
  exact abs_le.mpr ⟨by linarith [he.1,hc.1],by linarith [he.2,hc.2]⟩

theorem scale_ge_eight {m : ℕ} (hm : 64 ≤ m) : 8 ≤ scale m := by
  have hbase : (8:ℝ) ≤ (64:ℝ)^(7/9:ℝ) := by
    rw [Numerics.le_rpow_iff_pow (n := 9) (by norm_num) (by norm_num) (by norm_num)]
    norm_num
  exact hbase.trans (Real.rpow_le_rpow (by norm_num) (by exact_mod_cast hm) (by norm_num))

theorem base_eq_mul_scale (m : ℕ) : base m = (m:ℝ)*scale m := by
  by_cases hm : m = 0
  · simp [hm,base,scale]
  · have hm0 : (0:ℝ) < m := by exact_mod_cast (Nat.pos_of_ne_zero hm)
    dsimp [base,scale]
    rw [show (16/9:ℝ) = 1+7/9 by norm_num, Real.rpow_add hm0, Real.rpow_one]

theorem source_window {m n : ℕ} (hm : 64 ≤ m) (hn : n ∈ candidates m) :
    base m ≤ n ∧ (n:ℝ) ≤ 2*base m ∧ (n:ℝ) ≤ base m+3*scale m := by
  have hm1 : 1 ≤ m := by omega
  have hmem := mem_candidates.mp hn
  have hL := (endpoint_bounds hm1).1
  have hU := (endpoint_bounds (show 1 ≤ m+1 by omega)).2
  have hI := (power_increment hm1).2
  have hS := scale_ge_eight hm
  have hnL : (endpoint m:ℝ) ≤ n := by exact_mod_cast hmem.2.1
  have hnU : (n:ℝ) ≤ endpoint (m+1) := by exact_mod_cast hmem.2.2.le
  have hw : (n:ℝ) ≤ base m+3*scale m := by linarith
  have hmR : (64:ℝ) ≤ m := by exact_mod_cast hm
  have hratio : 3*scale m ≤ base m := by rw [base_eq_mul_scale]; nlinarith
  exact ⟨hL.trans hnL,by linarith,hw⟩

theorem candidate_count_scale {m : ℕ} (hm : 64 ≤ m) :
    scale m/2 ≤ (candidateCount m:ℝ) ∧ (candidateCount m:ℝ) ≤ 3*scale m := by
  have hS := scale_ge_eight hm
  have he := abs_le.mp (candidate_count_error (show 1 ≤ m by omega))
  constructor <;> linarith [he.1,he.2]

theorem candidate_count_pos {m : ℕ} (hm : 64 ≤ m) : 0 < candidateCount m := by
  have h := (candidate_count_scale hm).1
  have hs := scale_ge_eight hm
  have hp : (0:ℝ) < candidateCount m := by linarith
  exact_mod_cast hp

end Problems.Juggler.OOEEFibreGeometry
