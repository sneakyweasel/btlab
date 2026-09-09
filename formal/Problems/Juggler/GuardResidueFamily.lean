import Problems.Juggler.FateContagion
import Problems.Juggler.LandingValuation
import Mathlib.Tactic

namespace Problems.Juggler

/-!
An explicit subfamily of the written fixed-residue construction.
The auxiliary base is c^3. For a requested modulus q, choose c=512q-1.
The exact polynomial certificates below use c>=511.
-/

def guardResidueTPlus (c : ℤ) : ℤ := c ^ 12 + 4
def guardResidueTMinus (c : ℤ) : ℤ := c ^ 12 - 4 * c
def guardResidueVPlus (c : ℤ) : ℤ :=
  c ^ 54 + 18*c^42 + 126*c^30 + 420*c^18 + 630*c^6
def guardResidueVMinus (c : ℤ) : ℤ :=
  c ^ 54 - 18*c^43 + 126*c^32 - 420*c^21 + 630*c^10 - 1
def guardResidueTwiceZPlus (c : ℤ) : ℤ :=
  2*c^27 + 18*c^15 + 45*c^3 - 1
def guardResidueTwiceZMinus (c : ℤ) : ℤ :=
  2*c^27 - 18*c^16 + 45*c^5 - 1
def guardResidueZPlus (c : ℤ) : ℤ := guardResidueTwiceZPlus c / 2
def guardResidueZMinus (c : ℤ) : ℤ := guardResidueTwiceZMinus c / 2

private theorem guard_power_dominate {c : ℤ} (hc : 511 ≤ c)
    (K i j : ℕ) (hK : K ≤ 133432831) (hij : i + 3 ≤ j) :
    (K : ℤ) * c ^ i ≤ c ^ j := by
  have hc0 : 0 ≤ c := by omega
  have hc1 : 1 ≤ c := by omega
  have hk : (K : ℤ) ≤ c ^ 3 := by
    calc
      (K : ℤ) ≤ 133432831 := by exact_mod_cast hK
      _ = (511 : ℤ) ^ 3 := by norm_num
      _ ≤ c ^ 3 := by gcongr
  calc
    (K : ℤ) * c ^ i ≤ c ^ 3 * c ^ i :=
      mul_le_mul_of_nonneg_right hk (pow_nonneg hc0 _)
    _ = c ^ (i+3) := by ring
    _ ≤ c ^ j := pow_le_pow_right₀ hc1 hij

theorem guardResidue_t_pos {c : ℤ} (hc : 511 ≤ c) :
    0 < guardResidueTPlus c ∧ 0 < guardResidueTMinus c := by
  have hc0 : 0 < c := by omega
  have hd := guard_power_dominate hc 5 1 12 (by decide) (by decide)
  norm_num at hd
  dsimp [guardResidueTPlus, guardResidueTMinus]
  constructor
  · positivity
  · nlinarith

theorem guardResidue_vplus_cells {c : ℤ} (hc : 511 ≤ c) :
    0 < guardResidueVPlus c ∧
    guardResidueVPlus c ^ 2 ≤ guardResidueTPlus c ^ 9 ∧
    guardResidueTPlus c ^ 9 < (guardResidueVPlus c + 1) ^ 2 := by
  have hc0 : 0 < c := by omega
  have hd0 := guard_power_dominate hc 8904 36 48 (by decide) (by decide)
  have hd1 := guard_power_dominate hc 60624 24 48 (by decide) (by decide)
  have hd2 := guard_power_dominate hc 192924 12 48 (by decide) (by decide)
  have hd3 := guard_power_dominate hc 262144 0 48 (by decide) (by decide)
  have hd4 := guard_power_dominate hc 511 48 54 (by decide) (by decide)
  norm_num at hd0 hd1 hd2 hd3 hd4
  have hP : 0 < c ^ 48 := pow_pos hc0 _
  have hdef : guardResidueTPlus c ^ 9 - guardResidueVPlus c ^ 2 =
      504*c^48+8904*c^36+60624*c^24+192924*c^12+262144 := by
    unfold guardResidueTPlus guardResidueVPlus
    ring
  have hlo : 0 < guardResidueTPlus c ^ 9 - guardResidueVPlus c ^ 2 := by
    rw [hdef]
    positivity
  have hhi : guardResidueTPlus c ^ 9 - guardResidueVPlus c ^ 2 ≤ 508*c^48 := by
    rw [hdef]
    linarith
  have hv : 0 < guardResidueVPlus c := by
    unfold guardResidueVPlus
    positivity
  have hV : c ^ 54 ≤ guardResidueVPlus c := by
    unfold guardResidueVPlus
    nlinarith [pow_nonneg (le_of_lt hc0) 42, pow_nonneg (le_of_lt hc0) 30,
      pow_nonneg (le_of_lt hc0) 18, pow_nonneg (le_of_lt hc0) 6]
  refine ⟨hv, by linarith, ?_⟩
  nlinarith

theorem guardResidue_vminus_cells {c : ℤ} (hc : 511 ≤ c) :
    0 < guardResidueVMinus c ∧
    guardResidueVMinus c ^ 2 ≤ guardResidueTMinus c ^ 9 ∧
    guardResidueTMinus c ^ 9 < (guardResidueVMinus c + 1) ^ 2 := by
  have hc0 : 0 < c := by omega
  have hd0 := guard_power_dominate hc 8904 42 53 (by decide) (by decide)
  have hd1 := guard_power_dominate hc 192924 20 53 (by decide) (by decide)
  have hd2 := guard_power_dominate hc 60624 31 53 (by decide) (by decide)
  have hd3 := guard_power_dominate hc 262144 9 53 (by decide) (by decide)
  have hd4 := guard_power_dominate hc 18 43 53 (by decide) (by decide)
  have hd5 := guard_power_dominate hc 420 21 53 (by decide) (by decide)
  norm_num at hd0 hd1 hd2 hd3 hd4 hd5
  have h54 : 511*c^53 ≤ c^54 := by nlinarith [mul_le_mul_of_nonneg_right hc (le_of_lt (pow_pos hc0 53))]
  have hP : 1 ≤ c ^ 53 := by have := pow_pos hc0 53; omega
  have hdef : (guardResidueVMinus c + 1) ^ 2 - guardResidueTMinus c ^ 9 =
      504*c^53-8904*c^42+60624*c^31-192924*c^20+262144*c^9 := by
    unfold guardResidueTMinus guardResidueVMinus
    ring
  have hlo : 0 < (guardResidueVMinus c + 1) ^ 2 - guardResidueTMinus c ^ 9 := by
    rw [hdef]
    nlinarith [pow_nonneg (le_of_lt hc0) 31, pow_nonneg (le_of_lt hc0) 9]
  have hhi : (guardResidueVMinus c + 1) ^ 2 - guardResidueTMinus c ^ 9 ≤ 506*c^53 := by
    rw [hdef]
    nlinarith [pow_nonneg (le_of_lt hc0) 42, pow_nonneg (le_of_lt hc0) 20]
  have hV : 509*c^53-1 ≤ guardResidueVMinus c := by
    unfold guardResidueVMinus
    nlinarith [pow_nonneg (le_of_lt hc0) 32, pow_nonneg (le_of_lt hc0) 10]
  refine ⟨by linarith, ?_, by linarith⟩
  nlinarith

theorem guardResidue_zplus_lower_scaled {c : ℤ} (hc : 511 ≤ c) :
    0 < 16*guardResidueTPlus c ^ 9 - guardResidueTwiceZPlus c ^ 4 := by
  have hc0 : 0 < c := by omega
  have hd0 := guard_power_dominate hc 24 54 81 (by decide) (by decide)
  norm_num at hd0
  have hd1 := guard_power_dominate hc 432 42 81 (by decide) (by decide)
  norm_num at hd1
  have hd2 := guard_power_dominate hc 3024 30 81 (by decide) (by decide)
  norm_num at hd2
  have hd3 := guard_power_dominate hc 9720 18 81 (by decide) (by decide)
  norm_num at hd3
  have hd4 := guard_power_dominate hc 12150 6 81 (by decide) (by decide)
  norm_num at hd4
  have hp72 : 0 ≤ c ^ 72 := pow_nonneg (le_of_lt hc0) _
  have hp69 : 0 ≤ c ^ 69 := pow_nonneg (le_of_lt hc0) _
  have hp60 : 0 ≤ c ^ 60 := pow_nonneg (le_of_lt hc0) _
  have hp57 : 0 ≤ c ^ 57 := pow_nonneg (le_of_lt hc0) _
  have hp48 : 0 ≤ c ^ 48 := pow_nonneg (le_of_lt hc0) _
  have hp45 : 0 ≤ c ^ 45 := pow_nonneg (le_of_lt hc0) _
  have hp36 : 0 ≤ c ^ 36 := pow_nonneg (le_of_lt hc0) _
  have hp33 : 0 ≤ c ^ 33 := pow_nonneg (le_of_lt hc0) _
  have hp27 : 0 ≤ c ^ 27 := pow_nonneg (le_of_lt hc0) _
  have hp24 : 0 ≤ c ^ 24 := pow_nonneg (le_of_lt hc0) _
  have hp21 : 0 ≤ c ^ 21 := pow_nonneg (le_of_lt hc0) _
  have hp15 : 0 ≤ c ^ 15 := pow_nonneg (le_of_lt hc0) _
  have hp12 : 0 ≤ c ^ 12 := pow_nonneg (le_of_lt hc0) _
  have hp9 : 0 ≤ c ^ 9 := pow_nonneg (le_of_lt hc0) _
  have hp3 : 0 ≤ c ^ 3 := pow_nonneg (le_of_lt hc0) _
  have hp0 : 0 ≤ c ^ 0 := pow_nonneg (le_of_lt hc0) _
  have hp81 : 0 < c ^ 81 := pow_pos hc0 _
  have he : 16*guardResidueTPlus c ^ 9 - guardResidueTwiceZPlus c ^ 4 = 32*c^81 + 480*c^72 + 864*c^69 + 12600*c^60 + 9936*c^57 - 24*c^54 + 139824*c^48 + 62208*c^45 - 432*c^42 + 839424*c^36 + 223560*c^33 - 3024*c^30 + 8*c^27 + 2876184*c^24 + 437400*c^21 - 9720*c^18 + 72*c^15 + 5336559*c^12 + 364500*c^9 - 12150*c^6 + 180*c^3 + 4194303 := by
    unfold guardResidueTPlus guardResidueTwiceZPlus
    ring
  rw [he]
  nlinarith

theorem guardResidue_zplus_upper_scaled {c : ℤ} (hc : 511 ≤ c) :
    0 < (guardResidueTwiceZPlus c + 2) ^ 4 - 16*guardResidueTPlus c ^ 9 := by
  have hc0 : 0 < c := by omega
  have hd0 := guard_power_dominate hc 480 72 81 (by decide) (by decide)
  norm_num at hd0
  have hd1 := guard_power_dominate hc 12600 60 81 (by decide) (by decide)
  norm_num at hd1
  have hd2 := guard_power_dominate hc 139824 48 81 (by decide) (by decide)
  norm_num at hd2
  have hd3 := guard_power_dominate hc 839424 36 81 (by decide) (by decide)
  norm_num at hd3
  have hd4 := guard_power_dominate hc 2876184 24 81 (by decide) (by decide)
  norm_num at hd4
  have hd5 := guard_power_dominate hc 5336559 12 81 (by decide) (by decide)
  norm_num at hd5
  have hd6 := guard_power_dominate hc 4194303 0 81 (by decide) (by decide)
  norm_num at hd6
  have hp69 : 0 ≤ c ^ 69 := pow_nonneg (le_of_lt hc0) _
  have hp57 : 0 ≤ c ^ 57 := pow_nonneg (le_of_lt hc0) _
  have hp54 : 0 ≤ c ^ 54 := pow_nonneg (le_of_lt hc0) _
  have hp45 : 0 ≤ c ^ 45 := pow_nonneg (le_of_lt hc0) _
  have hp42 : 0 ≤ c ^ 42 := pow_nonneg (le_of_lt hc0) _
  have hp33 : 0 ≤ c ^ 33 := pow_nonneg (le_of_lt hc0) _
  have hp30 : 0 ≤ c ^ 30 := pow_nonneg (le_of_lt hc0) _
  have hp27 : 0 ≤ c ^ 27 := pow_nonneg (le_of_lt hc0) _
  have hp21 : 0 ≤ c ^ 21 := pow_nonneg (le_of_lt hc0) _
  have hp18 : 0 ≤ c ^ 18 := pow_nonneg (le_of_lt hc0) _
  have hp15 : 0 ≤ c ^ 15 := pow_nonneg (le_of_lt hc0) _
  have hp9 : 0 ≤ c ^ 9 := pow_nonneg (le_of_lt hc0) _
  have hp6 : 0 ≤ c ^ 6 := pow_nonneg (le_of_lt hc0) _
  have hp3 : 0 ≤ c ^ 3 := pow_nonneg (le_of_lt hc0) _
  have hp81 : 0 < c ^ 81 := pow_pos hc0 _
  have he : (guardResidueTwiceZPlus c + 2) ^ 4 - 16*guardResidueTPlus c ^ 9 = 32*c^81 - 480*c^72 + 864*c^69 - 12600*c^60 + 9936*c^57 + 24*c^54 - 139824*c^48 + 62208*c^45 + 432*c^42 - 839424*c^36 + 223560*c^33 + 3024*c^30 + 8*c^27 - 2876184*c^24 + 437400*c^21 + 9720*c^18 + 72*c^15 - 5336559*c^12 + 364500*c^9 + 12150*c^6 + 180*c^3 - 4194303 := by
    unfold guardResidueTPlus guardResidueTwiceZPlus
    ring
  rw [he]
  nlinarith

theorem guardResidue_zminus_lower_scaled {c : ℤ} (hc : 511 ≤ c) :
    0 < 16*guardResidueTMinus c ^ 9 - guardResidueTwiceZMinus c ^ 4 := by
  have hc0 : 0 < c := by omega
  have hd0 := guard_power_dominate hc 480 75 81 (by decide) (by decide)
  norm_num at hd0
  have hd1 := guard_power_dominate hc 864 70 81 (by decide) (by decide)
  norm_num at hd1
  have hd2 := guard_power_dominate hc 24 54 81 (by decide) (by decide)
  norm_num at hd2
  have hd3 := guard_power_dominate hc 139824 53 81 (by decide) (by decide)
  norm_num at hd3
  have hd4 := guard_power_dominate hc 62208 48 81 (by decide) (by decide)
  norm_num at hd4
  have hd5 := guard_power_dominate hc 3024 32 81 (by decide) (by decide)
  norm_num at hd5
  have hd6 := guard_power_dominate hc 2876184 31 81 (by decide) (by decide)
  norm_num at hd6
  have hd7 := guard_power_dominate hc 437400 26 81 (by decide) (by decide)
  norm_num at hd7
  have hd8 := guard_power_dominate hc 72 16 81 (by decide) (by decide)
  norm_num at hd8
  have hd9 := guard_power_dominate hc 12150 10 81 (by decide) (by decide)
  norm_num at hd9
  have hd10 := guard_power_dominate hc 4194304 9 81 (by decide) (by decide)
  norm_num at hd10
  have hd11 := guard_power_dominate hc 1 0 81 (by decide) (by decide)
  norm_num at hd11
  have hp64 : 0 ≤ c ^ 64 := pow_nonneg (le_of_lt hc0) _
  have hp59 : 0 ≤ c ^ 59 := pow_nonneg (le_of_lt hc0) _
  have hp43 : 0 ≤ c ^ 43 := pow_nonneg (le_of_lt hc0) _
  have hp42 : 0 ≤ c ^ 42 := pow_nonneg (le_of_lt hc0) _
  have hp37 : 0 ≤ c ^ 37 := pow_nonneg (le_of_lt hc0) _
  have hp27 : 0 ≤ c ^ 27 := pow_nonneg (le_of_lt hc0) _
  have hp21 : 0 ≤ c ^ 21 := pow_nonneg (le_of_lt hc0) _
  have hp20 : 0 ≤ c ^ 20 := pow_nonneg (le_of_lt hc0) _
  have hp15 : 0 ≤ c ^ 15 := pow_nonneg (le_of_lt hc0) _
  have hp5 : 0 ≤ c ^ 5 := pow_nonneg (le_of_lt hc0) _
  have hp81 : 0 < c ^ 81 := pow_pos hc0 _
  have he : 16*guardResidueTMinus c ^ 9 - guardResidueTwiceZMinus c ^ 4 = 32*c^81 - 480*c^75 - 864*c^70 + 12600*c^64 + 9936*c^59 - 24*c^54 - 139824*c^53 - 62208*c^48 + 432*c^43 + 839424*c^42 + 223560*c^37 - 3024*c^32 - 2876184*c^31 + 8*c^27 - 437400*c^26 + 9720*c^21 + 5336559*c^20 - 72*c^16 + 364500*c^15 - 12150*c^10 - 4194304*c^9 + 180*c^5 - 1 := by
    unfold guardResidueTMinus guardResidueTwiceZMinus
    ring
  rw [he]
  nlinarith

theorem guardResidue_zminus_upper_scaled {c : ℤ} (hc : 511 ≤ c) :
    0 < (guardResidueTwiceZMinus c + 2) ^ 4 - 16*guardResidueTMinus c ^ 9 := by
  have hc0 : 0 < c := by omega
  have hd0 := guard_power_dominate hc 864 70 81 (by decide) (by decide)
  norm_num at hd0
  have hd1 := guard_power_dominate hc 12600 64 81 (by decide) (by decide)
  norm_num at hd1
  have hd2 := guard_power_dominate hc 62208 48 81 (by decide) (by decide)
  norm_num at hd2
  have hd3 := guard_power_dominate hc 432 43 81 (by decide) (by decide)
  norm_num at hd3
  have hd4 := guard_power_dominate hc 839424 42 81 (by decide) (by decide)
  norm_num at hd4
  have hd5 := guard_power_dominate hc 437400 26 81 (by decide) (by decide)
  norm_num at hd5
  have hd6 := guard_power_dominate hc 9720 21 81 (by decide) (by decide)
  norm_num at hd6
  have hd7 := guard_power_dominate hc 5336559 20 81 (by decide) (by decide)
  norm_num at hd7
  have hd8 := guard_power_dominate hc 72 16 81 (by decide) (by decide)
  norm_num at hd8
  have hp75 : 0 ≤ c ^ 75 := pow_nonneg (le_of_lt hc0) _
  have hp59 : 0 ≤ c ^ 59 := pow_nonneg (le_of_lt hc0) _
  have hp54 : 0 ≤ c ^ 54 := pow_nonneg (le_of_lt hc0) _
  have hp53 : 0 ≤ c ^ 53 := pow_nonneg (le_of_lt hc0) _
  have hp37 : 0 ≤ c ^ 37 := pow_nonneg (le_of_lt hc0) _
  have hp32 : 0 ≤ c ^ 32 := pow_nonneg (le_of_lt hc0) _
  have hp31 : 0 ≤ c ^ 31 := pow_nonneg (le_of_lt hc0) _
  have hp27 : 0 ≤ c ^ 27 := pow_nonneg (le_of_lt hc0) _
  have hp15 : 0 ≤ c ^ 15 := pow_nonneg (le_of_lt hc0) _
  have hp10 : 0 ≤ c ^ 10 := pow_nonneg (le_of_lt hc0) _
  have hp9 : 0 ≤ c ^ 9 := pow_nonneg (le_of_lt hc0) _
  have hp5 : 0 ≤ c ^ 5 := pow_nonneg (le_of_lt hc0) _
  have hp0 : 0 ≤ c ^ 0 := pow_nonneg (le_of_lt hc0) _
  have hp81 : 0 < c ^ 81 := pow_pos hc0 _
  have he : (guardResidueTwiceZMinus c + 2) ^ 4 - 16*guardResidueTMinus c ^ 9 = 32*c^81 + 480*c^75 - 864*c^70 - 12600*c^64 + 9936*c^59 + 24*c^54 + 139824*c^53 - 62208*c^48 - 432*c^43 - 839424*c^42 + 223560*c^37 + 3024*c^32 + 2876184*c^31 + 8*c^27 - 437400*c^26 - 9720*c^21 - 5336559*c^20 - 72*c^16 + 364500*c^15 + 12150*c^10 + 4194304*c^9 + 180*c^5 + 1 := by
    unfold guardResidueTMinus guardResidueTwiceZMinus
    ring
  rw [he]
  nlinarith


theorem guardResidue_mod_two {c : ℤ} (hc : c % 4 = 3) :
    guardResidueTPlus c % 2 = 1 ∧ guardResidueTMinus c % 2 = 1 ∧
    guardResidueVPlus c % 2 = 1 ∧ guardResidueVMinus c % 2 = 0 ∧
    guardResidueTwiceZPlus c % 4 = 2 ∧ guardResidueTwiceZMinus c % 4 = 2 := by
  have hc2 : c % 2 = 1 := by omega
  have hp (k : ℕ) : c ^ k % 2 = 1 := by
    have hh : Int.ModEq 2 c 1 := by change c % 2 = 1 % 2; norm_num; exact hc2
    have := hh.pow k
    simpa [Int.ModEq] using this
  have h12 := hp 12
  have h54 := hp 54
  have h4 : Int.ModEq 4 c 3 := by
    change c % 4 = 3 % 4
    norm_num
    exact hc
  have h27 : c ^ 27 % 4 = 3 := by
    have := h4.pow 27
    norm_num [Int.ModEq] at this
    exact this
  have h15 : c ^ 15 % 4 = 3 := by
    have := h4.pow 15
    norm_num [Int.ModEq] at this
    exact this
  have h3 : c ^ 3 % 4 = 3 := by
    have := h4.pow 3
    norm_num [Int.ModEq] at this
    exact this
  have h16 : c ^ 16 % 4 = 1 := by
    have := h4.pow 16
    norm_num [Int.ModEq] at this
    exact this
  have h5 : c ^ 5 % 4 = 3 := by
    have := h4.pow 5
    norm_num [Int.ModEq] at this
    exact this
  dsimp [guardResidueTPlus, guardResidueTMinus, guardResidueVPlus,
    guardResidueVMinus, guardResidueTwiceZPlus, guardResidueTwiceZMinus]
  omega

theorem guardResidue_z_twice {c : ℤ} (hc : c % 4 = 3) :
    2 * guardResidueZPlus c = guardResidueTwiceZPlus c ∧
    2 * guardResidueZMinus c = guardResidueTwiceZMinus c ∧
    guardResidueZPlus c % 2 = 1 ∧ guardResidueZMinus c % 2 = 1 := by
  obtain ⟨_,_,_,_,hp,hm⟩ := guardResidue_mod_two hc
  unfold guardResidueZPlus guardResidueZMinus
  omega

theorem guardResidue_t_congr {c q : ℤ} (hq : q ∣ c + 1) :
    Int.ModEq q (guardResidueTPlus c) (guardResidueTMinus c) := by
  apply Int.modEq_iff_dvd.mpr
  obtain ⟨k,hk⟩ := hq
  refine ⟨-4*k, ?_⟩
  unfold guardResidueTPlus guardResidueTMinus
  nlinarith

theorem guardResidue_z_congr {c q : ℤ} (hc : c % 4 = 3) (hq : q ∣ c+1) :
    Int.ModEq q (guardResidueZPlus c) (guardResidueZMinus c) := by
  obtain ⟨hp,hm,_,_⟩ := guardResidue_z_twice hc
  have hdiv : 2*((c-1)/2)=c-1 := by omega
  have he : guardResidueZPlus c - guardResidueZMinus c =
      (c+1)*(9*c^15-45*c^3*((c-1)/2)) := by
    dsimp only [guardResidueTwiceZPlus, guardResidueTwiceZMinus] at hp hm
    have hprod := congrArg (fun x : ℤ => 45*(c+1)*c^3*x) hdiv
    nlinarith [hprod]
  apply Int.modEq_iff_dvd.mpr
  have hd : q ∣ guardResidueZPlus c - guardResidueZMinus c := by
    rw [he]
    exact dvd_mul_of_dvd_left hq _
  simpa only [neg_sub] using dvd_neg.mpr hd

theorem guardResidue_raw_record {c q : ℤ} (hc : c % 4 = 3) (hq : q ∣ c+1) :
    Int.ModEq q (guardResidueTPlus c ^ 2) (guardResidueTMinus c ^ 2) ∧
    Int.ModEq q (guardResidueTPlus c ^ 3) (guardResidueTMinus c ^ 3) ∧
    Int.ModEq q (guardResidueZPlus c) (guardResidueZMinus c) ∧
    Int.ModEq q ((guardResidueTPlus c ^ 2)^9-guardResidueZPlus c^8)
      ((guardResidueTMinus c ^ 2)^9-guardResidueZMinus c^8) := by
  have ht := guardResidue_t_congr hq
  have hz := guardResidue_z_congr hc hq
  exact ⟨ht.pow 2, ht.pow 3, hz, (ht.pow 2).pow 9 |>.sub (hz.pow 8)⟩

private theorem guard_int_sqrt_cell {a v : ℤ}
    (ha : 0 ≤ a) (hv : 0 ≤ v)
    (hlo : v^2 ≤ a^9) (hhi : a^9 < (v+1)^2) :
    Nat.sqrt ((a.toNat^3)^3) = v.toNat := by
  have haN : (a.toNat : ℤ) = a := Int.toNat_of_nonneg ha
  have hvN : (v.toNat : ℤ) = v := Int.toNat_of_nonneg hv
  have hloZ : (v.toNat : ℤ)^2 ≤ ((a.toNat : ℤ)^3)^3 := by
    rw [haN,hvN]
    convert hlo using 1 <;> ring
  have hhiZ : ((a.toNat : ℤ)^3)^3 < ((v.toNat : ℤ)+1)^2 := by
    rw [haN,hvN]
    convert hhi using 1 <;> ring
  have hloN : v.toNat^2 ≤ (a.toNat^3)^3 := by exact_mod_cast hloZ
  have hhiN : (a.toNat^3)^3 < (v.toNat+1)^2 := by exact_mod_cast hhiZ
  exact (Nat.eq_sqrt.mpr ⟨by simpa only [pow_two] using hloN,
    by simpa only [pow_two] using hhiN⟩).symm

private theorem guard_int_fourth_cell {a z : ℤ}
    (ha : 0 ≤ a) (hz : 0 ≤ z)
    (hlo : z^4 ≤ a^9) (hhi : a^9 < (z+1)^4) :
    (Nat.sqrt ((a.toNat^3)^3)).sqrt = z.toNat := by
  apply sqrt_sqrt_eq_iff.mpr
  have haN : (a.toNat : ℤ) = a := Int.toNat_of_nonneg ha
  have hzN : (z.toNat : ℤ) = z := Int.toNat_of_nonneg hz
  have hloZ : (z.toNat : ℤ)^4 ≤ ((a.toNat : ℤ)^3)^3 := by
    rw [haN,hzN]
    convert hlo using 1 <;> ring
  have hhiZ : ((a.toNat : ℤ)^3)^3 < ((z.toNat : ℤ)+1)^4 := by
    rw [haN,hzN]
    convert hhi using 1 <;> ring
  exact ⟨by exact_mod_cast hloZ, by exact_mod_cast hhiZ⟩

private theorem guard_toNat_parity {a : ℤ} (ha : 0 ≤ a) (p : ℕ) (hp : a%2=p) :
    a.toNat%2=p := by
  have he : (a.toNat : ℤ)%2=(p:ℤ) := by
    simpa only [Int.toNat_of_nonneg ha] using hp
  exact_mod_cast he


theorem guardResidue_z_cells {c : ℤ} (hc : 511 ≤ c) (hm : c % 4 = 3) :
    0 < guardResidueZPlus c ∧ 0 < guardResidueZMinus c ∧
    guardResidueZPlus c ^ 4 ≤ guardResidueTPlus c ^ 9 ∧
    guardResidueTPlus c ^ 9 < (guardResidueZPlus c+1)^4 ∧
    guardResidueZMinus c ^ 4 ≤ guardResidueTMinus c ^ 9 ∧
    guardResidueTMinus c ^ 9 < (guardResidueZMinus c+1)^4 := by
  obtain ⟨hp,hn,_,_⟩ := guardResidue_z_twice hm
  have hc0 : 0 < c := by omega
  have hd := guard_power_dominate hc 18 16 27 (by decide) (by decide)
  norm_num at hd
  have hzp : 0 < guardResidueZPlus c := by
    dsimp [guardResidueTwiceZPlus] at hp
    nlinarith [pow_pos hc0 27, pow_nonneg (le_of_lt hc0) 15,
      pow_pos hc0 3]
  have hzm : 0 < guardResidueZMinus c := by
    dsimp [guardResidueTwiceZMinus] at hn
    nlinarith [pow_pos hc0 27, pow_pos hc0 5]
  have hpl := guardResidue_zplus_lower_scaled hc
  have hpu := guardResidue_zplus_upper_scaled hc
  have hml := guardResidue_zminus_lower_scaled hc
  have hmu := guardResidue_zminus_upper_scaled hc
  rw [← hp] at hpl hpu
  rw [← hn] at hml hmu
  ring_nf at hpl hpu hml hmu
  exact ⟨hzp,hzm,by linarith,by linarith,by linarith,by linarith⟩

theorem guardResidue_ooe_traces {c : ℤ} (hc : 511 ≤ c) (hm : c % 4 = 3) :
    Nat.sqrt (((guardResidueTPlus c).toNat ^ 2)^3) =
      (guardResidueTPlus c).toNat ^ 3 ∧
    Nat.sqrt (((guardResidueTPlus c).toNat ^ 3)^3) =
      (guardResidueVPlus c).toNat ∧
    Nat.sqrt (guardResidueVPlus c).toNat = (guardResidueZPlus c).toNat ∧
    Nat.sqrt (((guardResidueTMinus c).toNat ^ 2)^3) =
      (guardResidueTMinus c).toNat ^ 3 ∧
    Nat.sqrt (((guardResidueTMinus c).toNat ^ 3)^3) =
      (guardResidueVMinus c).toNat ∧
    Nat.sqrt (guardResidueVMinus c).toNat = (guardResidueZMinus c).toNat := by
  obtain ⟨hTp,hTm⟩ := guardResidue_t_pos hc
  obtain ⟨hVp,hVl,hVu⟩ := guardResidue_vplus_cells hc
  obtain ⟨hVm,hWl,hWu⟩ := guardResidue_vminus_cells hc
  obtain ⟨hZp,hZm,hZpl,hZpu,hZml,hZmu⟩ := guardResidue_z_cells hc hm
  have hsp := guard_int_sqrt_cell (le_of_lt hTp) (le_of_lt hVp) hVl hVu
  have hsm := guard_int_sqrt_cell (le_of_lt hTm) (le_of_lt hVm) hWl hWu
  have hep := guard_int_fourth_cell (le_of_lt hTp) (le_of_lt hZp) hZpl hZpu
  have hem := guard_int_fourth_cell (le_of_lt hTm) (le_of_lt hZm) hZml hZmu
  rw [hsp] at hep
  rw [hsm] at hem
  refine ⟨?_,hsp,hep,?_,hsm,hem⟩
  · rw [show ((guardResidueTPlus c).toNat^2)^3 =
      ((guardResidueTPlus c).toNat^3)^2 by ring, Nat.sqrt_eq']
  · rw [show ((guardResidueTMinus c).toNat^2)^3 =
      ((guardResidueTMinus c).toNat^3)^2 by ring, Nat.sqrt_eq']

theorem guardResidue_nat_parities {c : ℤ} (hc : 511 ≤ c) (hm : c % 4 = 3) :
    (guardResidueTPlus c).toNat % 2 = 1 ∧
    (guardResidueTMinus c).toNat % 2 = 1 ∧
    (guardResidueVPlus c).toNat % 2 = 1 ∧
    (guardResidueVMinus c).toNat % 2 = 0 ∧
    (guardResidueZPlus c).toNat % 2 = 1 ∧
    (guardResidueZMinus c).toNat % 2 = 1 := by
  obtain ⟨hTp,hTm⟩ := guardResidue_t_pos hc
  obtain ⟨hVp,_,_⟩ := guardResidue_vplus_cells hc
  obtain ⟨hVm,_,_⟩ := guardResidue_vminus_cells hc
  obtain ⟨hZp,hZm,_,_,_,_⟩ := guardResidue_z_cells hc hm
  obtain ⟨pTp,pTm,pVp,pVm,_,_⟩ := guardResidue_mod_two hm
  obtain ⟨_,_,pZp,pZm⟩ := guardResidue_z_twice hm
  exact ⟨guard_toNat_parity (le_of_lt hTp) 1 pTp,
    guard_toNat_parity (le_of_lt hTm) 1 pTm,
    guard_toNat_parity (le_of_lt hVp) 1 pVp,
    guard_toNat_parity (le_of_lt hVm) 0 pVm,
    guard_toNat_parity (le_of_lt hZp) 1 pZp,
    guard_toNat_parity (le_of_lt hZm) 1 pZm⟩

theorem guardResidue_good_juggler_block {c : ℤ}
    (hc : 511 ≤ c) (hm : c % 4 = 3) :
    floorPower ((guardResidueTMinus c).toNat^2) =
      (guardResidueTMinus c).toNat^3 ∧
    floorPower ((guardResidueTMinus c).toNat^3) =
      (guardResidueVMinus c).toNat ∧
    floorPower (guardResidueVMinus c).toNat =
      (guardResidueZMinus c).toNat := by
  obtain ⟨_,pT,_,pV,_,_⟩ := guardResidue_nat_parities hc hm
  obtain ⟨_,_,_,_,hO,hE⟩ := guardResidue_ooe_traces hc hm
  have hp2 : ((guardResidueTMinus c).toNat^2)%2=1 := by simp [Nat.pow_mod,pT]
  have hp3 : ((guardResidueTMinus c).toNat^3)%2=1 := by simp [Nat.pow_mod,pT]
  refine ⟨?_,?_,?_⟩
  · rw [floorPower_odd_eq hp2]
    rw [show ((guardResidueTMinus c).toNat^2)^3 =
      ((guardResidueTMinus c).toNat^3)^2 by ring, Nat.sqrt_eq']
  · rw [floorPower_odd_eq hp3,hO]
  · rw [floorPower_even_eq pV,hE]

theorem guardResidue_first_remainders_zero (c : ℤ) :
    ((guardResidueTPlus c).toNat^2)^3 -
      ((guardResidueTPlus c).toNat^3)^2 = 0 ∧
    ((guardResidueTMinus c).toNat^2)^3 -
      ((guardResidueTMinus c).toNat^3)^2 = 0 := by
  constructor <;> rw [show ∀ a : ℕ, (a^2)^3=(a^3)^2 by intro a; ring] <;> omega

private theorem guard_nat_mod_of_cast {q x y : ℕ} {a b : ℤ}
    (hx : (x : ℤ)=a) (hy : (y : ℤ)=b) (hm : Int.ModEq (q : ℤ) a b) :
    x%q=y%q := by
  change a%(q:ℤ)=b%(q:ℤ) at hm
  have he : (x:ℤ)%(q:ℤ)=(y:ℤ)%(q:ℤ) := by simpa only [hx,hy] using hm
  exact_mod_cast he

theorem guardResidue_nat_record {q : ℕ} {c : ℤ}
    (hc : 511 ≤ c) (hm : c % 4 = 3) (hq : (q:ℤ) ∣ c+1) :
    ((guardResidueTPlus c).toNat^2)%q=((guardResidueTMinus c).toNat^2)%q ∧
    ((guardResidueTPlus c).toNat^3)%q=((guardResidueTMinus c).toNat^3)%q ∧
    (guardResidueZPlus c).toNat%q=(guardResidueZMinus c).toNat%q ∧
    Int.ModEq (q:ℤ) ((guardResidueTPlus c^2)^9-guardResidueZPlus c^8)
      ((guardResidueTMinus c^2)^9-guardResidueZMinus c^8) := by
  obtain ⟨hTp,hTm⟩ := guardResidue_t_pos hc
  obtain ⟨hZp,hZm,_,_,_,_⟩ := guardResidue_z_cells hc hm
  obtain ⟨hx,hu,hz,hE⟩ := guardResidue_raw_record hm hq
  have hTpN := Int.toNat_of_nonneg (le_of_lt hTp)
  have hTmN := Int.toNat_of_nonneg (le_of_lt hTm)
  refine ⟨?_,?_,?_,hE⟩
  · apply guard_nat_mod_of_cast (a:=guardResidueTPlus c^2)
      (b:=guardResidueTMinus c^2) _ _ hx
    · push_cast
      rw [hTpN]
    · push_cast
      rw [hTmN]
  · apply guard_nat_mod_of_cast (a:=guardResidueTPlus c^3)
      (b:=guardResidueTMinus c^3) _ _ hu
    · push_cast
      rw [hTpN]
    · push_cast
      rw [hTmN]
  · exact guard_nat_mod_of_cast (Int.toNat_of_nonneg (le_of_lt hZp))
      (Int.toNat_of_nonneg (le_of_lt hZm)) hz

def guardResidueParameter (q : ℕ) : ℤ := 512*(q:ℤ)-1

theorem guardResidueParameter_valid {q : ℕ} (hq : 0 < q) :
    511 ≤ guardResidueParameter q ∧ guardResidueParameter q % 4 = 3 ∧
    (q:ℤ) ∣ guardResidueParameter q + 1 := by
  unfold guardResidueParameter
  refine ⟨by omega,by omega,?_⟩
  refine ⟨512,by ring⟩

theorem guardResidueFamily_every_modulus (q : ℕ) (hq : 0 < q) :
    ∃ c : ℤ, 511 ≤ c ∧ c%4=3 ∧
      ((guardResidueTPlus c).toNat^2)%q=((guardResidueTMinus c).toNat^2)%q ∧
      ((guardResidueTPlus c).toNat^3)%q=((guardResidueTMinus c).toNat^3)%q ∧
      (guardResidueZPlus c).toNat%q=(guardResidueZMinus c).toNat%q ∧
      Int.ModEq (q:ℤ) ((guardResidueTPlus c^2)^9-guardResidueZPlus c^8)
        ((guardResidueTMinus c^2)^9-guardResidueZMinus c^8) ∧
      (guardResidueVPlus c).toNat%2=1 ∧
      (guardResidueVMinus c).toNat%2=0 ∧
      floorPower ((guardResidueTMinus c).toNat^2)=(guardResidueTMinus c).toNat^3 ∧
      floorPower ((guardResidueTMinus c).toNat^3)=(guardResidueVMinus c).toNat ∧
      floorPower (guardResidueVMinus c).toNat=(guardResidueZMinus c).toNat ∧
      Nat.sqrt (((guardResidueTPlus c).toNat^3)^3)=(guardResidueVPlus c).toNat ∧
      Nat.sqrt (guardResidueVPlus c).toNat=(guardResidueZPlus c).toNat := by
  let c := guardResidueParameter q
  obtain ⟨hc,hm,hd⟩ := guardResidueParameter_valid hq
  change 511 ≤ c at hc
  change c%4=3 at hm
  change (q:ℤ)∣c+1 at hd
  obtain ⟨hx,hu,hz,hE⟩ := guardResidue_nat_record hc hm hd
  obtain ⟨_,_,hVp,hVm,_,_⟩ := guardResidue_nat_parities hc hm
  obtain ⟨hg1,hg2,hg3⟩ := guardResidue_good_juggler_block hc hm
  obtain ⟨_,hb1,hb2,_,_,_⟩ := guardResidue_ooe_traces hc hm
  exact ⟨c,hc,hm,hx,hu,hz,hE,hVp,hVm,hg1,hg2,hg3,hb1,hb2⟩

end Problems.Juggler
