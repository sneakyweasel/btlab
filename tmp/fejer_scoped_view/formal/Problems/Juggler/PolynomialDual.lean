import Problems.Juggler.OddCubicPhase
import Problems.Juggler.CollatzRational

/-!
# The unit-gap obstruction to polynomial stationary duals

The smooth multiplier of a word is 3^o / 2^L. Its stationary dual
exponent has denominator 3^o - 2^L, the signed Collatz cycle gap.
This file classifies its integral values; it asserts no estimate for
an actual floor composition or a parity-selected sum.
-/

namespace Problems.Juggler.PolynomialDual

def multiplier (o L : ℕ) : ℚ := 3 ^ o / 2 ^ L

def dualDegree (o L : ℕ) : ℚ := 3 ^ o / (3 ^ o - 2 ^ L)

theorem dualDegree_eq (o L : ℕ) (hexp : 2 ^ L < 3 ^ o) :
    dualDegree o L = multiplier o L / (multiplier o L - 1) := by
  have hg : (3 : ℚ) ^ o - 2 ^ L ≠ 0 := by
    have : (2 : ℚ) ^ L < 3 ^ o := by exact_mod_cast hexp
    linarith
  unfold dualDegree multiplier
  field_simp

theorem rational_degree_iff {o L d : ℕ} (hexp : 2 ^ L < 3 ^ o) :
    dualDegree o L = d ↔ 3 ^ o = d * (3 ^ o - 2 ^ L) := by
  have hg : (3 : ℚ) ^ o - 2 ^ L ≠ 0 := by
    have : (2 : ℚ) ^ L < 3 ^ o := by exact_mod_cast hexp
    linarith
  unfold dualDegree
  rw [div_eq_iff hg]
  have hc : ((3 ^ o - 2 ^ L : ℕ) : ℚ) = 3 ^ o - 2 ^ L := by
    rw [Nat.cast_sub hexp.le]; norm_cast
  rw [← hc]
  norm_cast

theorem pullback_fixed_gap {w : List Branch} {q : ℚ}
    (hq : CollatzRational.pullbackWord w q = q) :
    ((3 : ℚ) ^ oddCount w - 2 ^ w.length) * q = CollatzBridge.wordConst w := by
  have hf := CollatzRational.pullbackWord_affine w q
  rw [hq] at hf
  linear_combination hf

theorem gap_coprime (o L : ℕ) (hexp : 2 ^ L ≤ 3 ^ o) :
    Nat.Coprime (3 ^ o - 2 ^ L) (3 ^ o) := by
  rw [Nat.coprime_self_sub_left hexp]
  exact (by decide : Nat.Coprime 2 3).pow _ _

theorem integral_degree_iff_gap_one (o L : ℕ) (hexp : 2 ^ L < 3 ^ o) :
    (∃ d : ℕ, 3 ^ o = d * (3 ^ o - 2 ^ L)) ↔ 3 ^ o = 2 ^ L + 1 := by
  constructor
  · rintro ⟨d, hd⟩
    have hdiv : 3 ^ o - 2 ^ L ∣ 3 ^ o := ⟨d, by simpa [mul_comm] using hd⟩
    have he := (gap_coprime o L hexp.le).eq_one_of_dvd hdiv
    omega
  · intro h
    refine ⟨3 ^ o, ?_⟩
    have : 3 ^ o - 2 ^ L = 1 := by omega
    rw [this, mul_one]

private theorem power_gap_two {a b : ℕ} (ha : 0 < a)
    (he : 2 ^ b = 2 ^ a + 2) : a = 1 ∧ b = 2 := by
  have hb : 2 ≤ b := by
    by_contra h
    interval_cases b <;> simp_all
  have ha1 : a = 1 := by
    by_contra h
    have ha2 : 2 ≤ a := by omega
    have da : 4 ∣ 2 ^ a := by simpa using Nat.pow_dvd_pow 2 ha2
    have db : 4 ∣ 2 ^ b := by simpa using Nat.pow_dvd_pow 2 hb
    omega
  refine ⟨ha1, ?_⟩
  rw [ha1] at he
  have : 2 ^ b = 2 ^ 2 := by norm_num at he ⊢; exact he
  exact (Nat.pow_right_injective (by decide : 2 ≤ 2)) this

theorem unit_gap_classification {o L : ℕ} (ho : 0 < o) (hL : 0 < L)
    (he : 3 ^ o = 2 ^ L + 1) :
    (o = 1 ∧ L = 1) ∨ (o = 2 ∧ L = 3) := by
  by_cases hsmall : L < 3
  · interval_cases L
    · left
      refine ⟨?_, rfl⟩
      apply Nat.pow_right_injective (by decide : 2 ≤ 3)
      simpa using he
    · have hdiv : 3 ∣ 3 ^ o := dvd_pow_self 3 (by omega : o ≠ 0)
      norm_num at he
      omega
  · have hL3 : 3 ≤ L := by omega
    have h8 : 8 ∣ 2 ^ L := by simpa using Nat.pow_dvd_pow 2 hL3
    have hoEven : Even o := by
      rcases Nat.even_or_odd o with h | ⟨k, hk⟩
      · exact h
      · have hm : 3 ^ o % 8 = 3 := by
          rw [hk]
          rw [pow_add, pow_mul]
          norm_num [Nat.mul_mod, Nat.pow_mod]
        omega
    obtain ⟨k, hk⟩ := hoEven
    have hkpos : 0 < k := by omega
    have hq : 1 < 3 ^ k := Nat.one_lt_pow (by omega) (by decide)
    have hprod : (3 ^ k - 1) * (3 ^ k + 1) = 2 ^ L := by
      have hs : 3 ^ o = (3 ^ k) ^ 2 := by rw [hk, pow_add]; ring
      rw [hs] at he
      have hsub : 3 ^ k - 1 + 1 = 3 ^ k := by omega
      nlinarith
    have dl : 3 ^ k - 1 ∣ 2 ^ L := ⟨3 ^ k + 1, hprod.symm⟩
    have dr : 3 ^ k + 1 ∣ 2 ^ L := ⟨3 ^ k - 1, by nlinarith [hprod]⟩
    obtain ⟨a, _, ha⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp dl
    obtain ⟨b, _, hb⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp dr
    have hapos : 0 < a := by
      by_contra h
      have ha0 : a = 0 := by omega
      simp [ha0] at ha
      have hk3 : 3 ≤ 3 ^ k := Nat.le_self_pow (by omega) 3
      omega
    have hg : 2 ^ b = 2 ^ a + 2 := by omega
    have ha1 := (power_gap_two hapos hg).1
    have hk1 : k = 1 := by
      apply Nat.pow_right_injective (by decide : 2 ≤ 3)
      norm_num [ha1] at ha
      simpa using (show 3 ^ k = 3 by omega)
    right
    have ho2 : o = 2 := by omega
    refine ⟨ho2, ?_⟩
    apply Nat.pow_right_injective (by decide : 2 ≤ 2)
    norm_num [ho2] at he
    norm_num
    omega

theorem integral_degree_classification {o L d : ℕ} (ho : 0 < o) (hL : 0 < L)
    (hexp : 2 ^ L < 3 ^ o) (hd : 3 ^ o = d * (3 ^ o - 2 ^ L)) :
    (o = 1 ∧ L = 1 ∧ d = 3) ∨ (o = 2 ∧ L = 3 ∧ d = 9) := by
  have hg := (integral_degree_iff_gap_one o L hexp).mp ⟨d, hd⟩
  rcases unit_gap_classification ho hL hg with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · left; norm_num at hd ⊢; omega
  · right; norm_num at hd ⊢; omega

theorem no_integral_degree_after_three {o L : ℕ} (ho : 0 < o) (hL : 3 < L)
    (hexp : 2 ^ L < 3 ^ o) :
    ¬ ∃ d : ℕ, 3 ^ o = d * (3 ^ o - 2 ^ L) := by
  rintro ⟨d, hd⟩
  rcases integral_degree_classification ho (by omega) hexp hd with h | h <;> omega

theorem rational_degree_classification {o L d : ℕ} (ho : 0 < o) (hL : 0 < L)
    (hexp : 2 ^ L < 3 ^ o) (hd : dualDegree o L = d) :
    (o = 1 ∧ L = 1 ∧ d = 3) ∨ (o = 2 ∧ L = 3 ∧ d = 9) :=
  integral_degree_classification ho hL hexp ((rational_degree_iff hexp).mp hd)

theorem all_odd_second_degree : dualDegree 2 2 = 9 / 5 := by
  norm_num [dualDegree]

noncomputable def ninthPhase (h r : ℝ) : ℝ :=
  r / 2 - 8388608 * r ^ 9 / (387420489 * h ^ 8)

theorem ninth_stationary_algebra {h : ℝ} (hh : h ≠ 0) (r : ℝ) :
    h / 2 * (8 * r / (9 * h)) ^ 9 -
        r * (((8 * r / (9 * h)) ^ 8 - 1) / 2) = ninthPhase h r := by
  unfold ninthPhase
  field_simp
  ring

theorem ninth_stationary_index {h : ℝ} (hh : h ≠ 0) (r : ℝ) :
    9 * h / 8 * (8 * r / (9 * h)) = r := by
  field_simp

open OddCubicPhase

theorem half_monomial_antiperiodic {q : ℕ} (hq : Odd q) (c : ℤ) (d r : ℕ) :
    wave (((r : ℝ) + q) / 2 - c * ((r : ℝ) + q) ^ d / q) =
      -wave ((r : ℝ) / 2 - c * (r : ℝ) ^ d / q) := by
  have hd : (q : ℤ) ∣ ((r : ℤ) + q) ^ d - (r : ℤ) ^ d := by
    simpa using sub_dvd_pow_sub_pow ((r : ℤ) + q) (r : ℤ) d
  obtain ⟨z, hz⟩ := hd
  have hzR : ((r : ℝ) + q) ^ d - (r : ℝ) ^ d = (q : ℝ) * z := by
    exact_mod_cast hz
  obtain ⟨k, hk⟩ := hq
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast (show q ≠ 0 by omega)
  have hqR : (q : ℝ) = 2 * (k : ℝ) + 1 := by exact_mod_cast hk
  have hs : ((r : ℝ) + q) / 2 - c * ((r : ℝ) + q) ^ d / q =
      ((r : ℝ) / 2 - c * (r : ℝ) ^ d / q) +
        (1 / 2 + ((k : ℤ) - c * z : ℤ)) := by
    push_cast
    field_simp
    linear_combination -2 * (c : ℝ) * hzR + (q : ℝ) * hqR
  rw [hs, wave_half_int]

theorem ninth_odd_antiperiodic {h : ℕ} (hh : Odd h) (r : ℕ) :
    wave (ninthPhase h (r + 387420489 * h ^ 8)) = -wave (ninthPhase h r) := by
  have hq : Odd (387420489 * h ^ 8) :=
    (by decide : Odd (387420489 : ℕ)).mul hh.pow
  simpa [ninthPhase] using half_monomial_antiperiodic hq 8388608 9 r

theorem ninth_odd_complete_mean_zero {h : ℕ} (hh : Odd h) :
    ∑ r ∈ Finset.range (2 * (387420489 * h ^ 8)), wave (ninthPhase h r) = 0 := by
  apply antiperiodic_sum_zero
  intro r
  simpa using ninth_odd_antiperiodic hh r

end Problems.Juggler.PolynomialDual
