import Problems.Juggler.CriticalCostKernel
import Problems.Juggler.CubicOrbitCharge
import Problems.Juggler.CubicCriticalLocation
import Mathlib.Logic.Equiv.Fin.Rotate

/-!
# Actual-cycle assembly of the lifted-gap recurrence

An `OrbitUpperChargeCertificate` supplies the sorted states, rank rotation
and charge. This module extracts the positive lifted gaps, square remainders
and the exact RC68 correction, then feeds the existing valuation kernels.
No period or floor improvement is claimed.
-/

namespace Problems.Juggler.CubicRemainderAssembly

open CubicGrid CubicRemainderVariation CubicConstraintFusion CubicCriticalLocation
open scoped BigOperators

variable {m M k : ℕ}

def evenCount (Q : OrbitUpperChargeCertificate m M k) : ℕ :=
  Q.length - Q.oddCount

def lastIdx (Q : OrbitUpperChargeCertificate m M k) : Fin Q.length :=
  ⟨Q.length - 1, Nat.sub_lt Q.length_pos (by decide)⟩

theorem state_min (Q : OrbitUpperChargeCertificate m M k) :
    Q.state ⟨0, Q.length_pos⟩ = m := Q.min_eq

theorem state_max (Q : OrbitUpperChargeCertificate m M k) :
    Q.state (lastIdx Q) = M := Q.max_eq

theorem le_max (Q : OrbitUpperChargeCertificate m M k) (i : Fin Q.length) :
    Q.state i ≤ M :=
  (Q.ordered.monotone (show i ≤ lastIdx Q from Nat.le_sub_one_of_lt i.isLt)).trans_eq
    (state_max Q)

theorem min_le (Q : OrbitUpperChargeCertificate m M k) (i : Fin Q.length) :
    m ≤ Q.state i :=
  (state_min Q).symm.trans_le
    (Q.ordered.monotone (show (⟨0, Q.length_pos⟩ : Fin Q.length) ≤ i from
      Nat.zero_le i.val))

/-- Surplus `o log 3 > L log 2` and `log 3 < 2 log 2` force `e < o`. -/
theorem evenCount_lt_oddCount (Q : OrbitUpperChargeCertificate m M k)
    (_hm : 1 < m) : evenCount Q < Q.oddCount := by
  let : NeZero Q.length := ⟨Q.length_pos.ne'⟩
  have hsurp : 0 < logGridSurplus Q.length Q.oddCount := Q.charge.surplus_pos
  have h3 : Real.log 3 < 2 * Real.log 2 := by
    have : Real.log 3 < Real.log 4 :=
      Real.log_lt_log (by norm_num) (by norm_num)
    have h4 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]
      push_cast
      ring
    linarith
  unfold logGridSurplus at hsurp
  have hlt : (Q.length : ℝ) * Real.log 2 < (Q.oddCount : ℝ) * Real.log 3 := by
    linarith
  have hoPos : 0 < (Q.oddCount : ℝ) := by
    by_contra hne
    have hz : Q.oddCount = 0 := by
      have : (Q.oddCount : ℝ) ≤ 0 := by linarith
      have : (Q.oddCount : ℝ) = 0 :=
        le_antisymm this (Nat.cast_nonneg _)
      exact_mod_cast this
    simp [hz] at hsurp
    nlinarith [Real.log_pos (by norm_num : (1 : ℝ) < 2)]
  have hlt' : (Q.length : ℝ) * Real.log 2 <
      (Q.oddCount : ℝ) * (2 * Real.log 2) := by
    nlinarith
  have h2pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hmul : (Q.length : ℝ) * Real.log 2 <
      (2 * Q.oddCount : ℝ) * Real.log 2 := by
    convert hlt' using 1
    ring
  have hcast : (Q.length : ℝ) < 2 * (Q.oddCount : ℝ) :=
    lt_of_mul_lt_mul_right hmul h2pos.le
  have hL : Q.length < 2 * Q.oddCount := by exact_mod_cast hcast
  exact Nat.sub_lt_left_of_lt_add Q.oddCount_le (by omega)

theorem max_even (Q : OrbitUpperChargeCertificate m M k)
    (hm : 1 < m) (_hM : M < m ^ 3) : M % 2 = 0 := by
  rcases Nat.mod_two_eq_zero_or_one M with he | ho
  · exact he
  · have hMge : 3 ≤ M := by
      have hge : m ≤ M := by
        simpa [state_max Q] using min_le Q (lastIdx Q)
      rcases eq_or_lt_of_le hge with hEq | hlt
      · have : m % 2 = 1 := by simpa [hEq] using ho
        omega
      · omega
    have hgt : M < floorPower M := floorPower_odd_gt hMge ho
    have hstep : Q.state (Q.next (lastIdx Q)) = floorPower M := by
      simpa [state_max Q] using Q.step (lastIdx Q)
    have hle : Q.state (Q.next (lastIdx Q)) ≤ M := le_max Q _
    omega

theorem evenCount_pos (Q : OrbitUpperChargeCertificate m M k)
    (hm : 1 < m) (hM : M < m ^ 3) : 0 < evenCount Q := by
  have hpar : M % 2 = 0 := max_even Q hm hM
  have hnot : ¬ (lastIdx Q).val < Q.oddCount := by
    intro hlt
    have hodd := (Q.odd_cut (lastIdx Q)).mpr hlt
    simp [state_max Q] at hodd
    exact absurd hodd (by simp [hpar])
  have hval : (lastIdx Q).val = Q.length - 1 := rfl
  have : ¬ Q.length - 1 < Q.oddCount := by simpa [hval] using hnot
  simp only [evenCount]
  omega

theorem oddCount_pos (Q : OrbitUpperChargeCertificate m M k) (hm : 1 < m) :
    0 < Q.oddCount :=
  Nat.zero_lt_of_lt (evenCount_lt_oddCount Q hm)

theorem length_ge_three (Q : OrbitUpperChargeCertificate m M k)
    (hm : 1 < m) (hM : M < m ^ 3) : 3 ≤ Q.length := by
  have hlt := evenCount_lt_oddCount Q hm
  have hpos := evenCount_pos Q hm hM
  have ho := Q.oddCount_le
  simp only [evenCount] at hlt hpos
  omega

def excess (Q : OrbitUpperChargeCertificate m M k) : ℕ :=
  Q.oddCount - evenCount Q

theorem excess_pos (Q : OrbitUpperChargeCertificate m M k) (hm : 1 < m) :
    0 < excess Q :=
  Nat.sub_pos_of_lt (evenCount_lt_oddCount Q hm)

def lastOdd (Q : OrbitUpperChargeCertificate m M k)
    (hm : 1 < m) (hM : M < m ^ 3) : Fin Q.length :=
  ⟨Q.oddCount - 1, by
    have := oddCount_pos Q hm
    have hpos := evenCount_pos Q hm hM
    have := Q.oddCount_le
    simp only [evenCount] at hpos
    omega⟩

def firstEven (Q : OrbitUpperChargeCertificate m M k)
    (hm : 1 < m) (hM : M < m ^ 3) : Fin Q.length :=
  ⟨Q.oddCount, by
    have hpos := evenCount_pos Q hm hM
    have := Q.oddCount_le
    simp only [evenCount] at hpos
    omega⟩

def ooCut (Q : OrbitUpperChargeCertificate m M k)
    (hm : 1 < m) (_hM : M < m ^ 3) : Fin Q.length :=
  ⟨excess Q - 1, by
    have h1 : excess Q ≤ Q.oddCount := Nat.sub_le _ _
    have h2 : Q.oddCount ≤ Q.length := Q.oddCount_le
    have h3 : 0 < excess Q := excess_pos Q hm
    omega⟩

def succIdx (Q : OrbitUpperChargeCertificate m M k)
    (i : Fin Q.length) : Fin Q.length :=
  finRotate Q.length i

def predIdx (Q : OrbitUpperChargeCertificate m M k)
    (i : Fin Q.length) : Fin Q.length :=
  (finRotate Q.length).symm i

def gap (Q : OrbitUpperChargeCertificate m M k) (i : Fin Q.length) : ℕ :=
  if h : i.val + 1 < Q.length then
    Q.state ⟨i.val + 1, h⟩ - Q.state i
  else
    m ^ 3 - M

def rem (Q : OrbitUpperChargeCertificate m M k) (i : Fin Q.length) : ℕ :=
  if i.val < Q.oddCount then
    Q.state i ^ 3 - Q.state (Q.next i) ^ 2
  else
    Q.state i - Q.state (Q.next i) ^ 2

def numer (Q : OrbitUpperChargeCertificate m M k) (i : Fin Q.length) : ℕ :=
  if h : i.val + 1 < Q.length then
    if i.val < Q.oddCount then
      Q.state i ^ 2 + Q.state i * Q.state ⟨i.val + 1, h⟩ +
        Q.state ⟨i.val + 1, h⟩ ^ 2
    else
      1
  else
    1

def denom (Q : OrbitUpperChargeCertificate m M k)
    (i : Fin Q.length) : ℕ :=
  if i.val + 1 = Q.oddCount then
    m ^ 3 + M
  else
    Q.state (Q.next i) + Q.state (Q.next (succIdx Q i))

def corr (Q : OrbitUpperChargeCertificate m M k) (i : Fin Q.length) : ℤ :=
  (numer Q i : ℤ) * gap Q i - (denom Q i : ℤ) * gap Q (Q.next i)

theorem gap_pos (Q : OrbitUpperChargeCertificate m M k)
    (hM : M < m ^ 3) (i : Fin Q.length) : 0 < gap Q i := by
  unfold gap
  split_ifs with h
  · exact Nat.sub_pos_of_lt (Q.ordered (by
      change (⟨i.val, i.isLt⟩ : Fin Q.length) < ⟨i.val + 1, h⟩
      exact Nat.lt_succ_self i.val))
  · exact Nat.sub_pos_of_lt hM

theorem gap_lt_cube (Q : OrbitUpperChargeCertificate m M k)
    (hM : M < m ^ 3) (i : Fin Q.length) : gap Q i < m ^ 3 := by
  unfold gap
  split_ifs with h
  · have hle := le_max Q ⟨i.val + 1, h⟩
    have hge := min_le Q i
    have hmM : m ≤ M := by simpa [state_max Q] using min_le Q (lastIdx Q)
    have hgap : Q.state ⟨i.val + 1, h⟩ - Q.state i ≤ M - m :=
      (Nat.sub_le_sub_right hle (Q.state i)).trans (Nat.sub_le_sub_left hge M)
    have hadd : M < m + m ^ 3 := by
      have := Nat.lt_add_right m hM
      rwa [Nat.add_comm]
    have hMm : M - m < m ^ 3 := Nat.sub_lt_left_of_lt_add hmM hadd
    exact lt_of_le_of_lt hgap hMm
  · have hmM : m ≤ M := by simpa [state_max Q] using min_le Q (lastIdx Q)
    have hcube : 0 < m ^ 3 := Nat.zero_lt_of_lt hM
    have hmpos : 0 < m := Nat.pos_of_ne_zero fun hz => by simp [hz] at hcube
    have hMpos : 0 < M := lt_of_lt_of_le hmpos hmM
    exact Nat.sub_lt hcube hMpos

set_option exponentiation.threshold 128 in
theorem leftover_cube_lt_two_pow :
    (520000000 : ℕ) ^ 3 < 2 ^ 87 := by
  decide

theorem leftover_pred_cube_lt :
    (519999999 : ℕ) ^ 3 < 520000000 ^ 3 :=
  Nat.pow_lt_pow_left (by decide : (519999999 : ℕ) < 520000000)
    (by decide : (3 : ℕ) ≠ 0)

theorem leftover_gap_lt_pow (Q : OrbitUpperChargeCertificate m M k)
    (hM : M < m ^ 3) (hmin : m < 520000000) (i : Fin Q.length) :
    gap Q i < 2 ^ 87 := by
  have h1 := gap_lt_cube Q hM i
  have hm' : m ≤ 519999999 := Nat.lt_succ_iff.mp hmin
  have h2 : m ^ 3 ≤ 519999999 ^ 3 :=
    Nat.pow_le_pow_left hm' 3
  exact lt_of_lt_of_le h1
    (h2.trans (leftover_pred_cube_lt.le.trans leftover_cube_lt_two_pow.le))

theorem leftover_gap_val_le (Q : OrbitUpperChargeCertificate m M k)
    (hM : M < m ^ 3) (hmin : m < 520000000) (i : Fin Q.length) :
    padicValNat 2 (gap Q i) ≤ 86 :=
  valuation_le_of_lt_pow_succ (gap_pos Q hM i) (leftover_gap_lt_pow Q hM hmin i)

theorem rem_add (Q : OrbitUpperChargeCertificate m M k) (i : Fin Q.length) :
    (if i.val < Q.oddCount then Q.state i ^ 3 else Q.state i) =
      Q.state (Q.next i) ^ 2 + rem Q i := by
  unfold rem
  by_cases ho : i.val < Q.oddCount
  · have hodd : Q.state i % 2 = 1 := (Q.odd_cut i).mpr ho
    have hle : Q.state (Q.next i) ^ 2 ≤ Q.state i ^ 3 := by
      simpa [Q.step i] using floorPower_odd_sq_le_cube hodd
    simp [ho, Nat.add_sub_of_le hle]
  · have heven : Q.state i % 2 = 0 := by
      have := Q.odd_cut i
      omega
    have hle : Q.state (Q.next i) ^ 2 ≤ Q.state i := by
      simpa [Q.step i] using floorPower_even_sq_le heven
    simp [ho, Nat.add_sub_of_le hle]

theorem numer_pos (Q : OrbitUpperChargeCertificate m M k)
    (hm : 1 < m) (i : Fin Q.length) : 0 < numer Q i := by
  unfold numer
  split_ifs with _ ho
  · have hx : 1 < Q.state i := lt_of_lt_of_le hm (min_le Q i)
    nlinarith
  · decide
  · decide

theorem denom_pos (Q : OrbitUpperChargeCertificate m M k)
    (hm : 1 < m) (hM : M < m ^ 3) (i : Fin Q.length) : 0 < denom Q i := by
  unfold denom
  split_ifs
  · have : 0 < m ^ 3 := Nat.zero_lt_of_lt hM
    omega
  · have hx : m ≤ Q.state (Q.next i) := min_le Q _
    omega

theorem numer_odd (Q : OrbitUpperChargeCertificate m M k)
    (i : Fin Q.length) : numer Q i % 2 = 1 := by
  unfold numer
  split_ifs with h ho
  · have hodd : Q.state i % 2 = 1 := (Q.odd_cut i).mpr ho
    rcases Nat.mod_two_eq_zero_or_one (Q.state ⟨i.val + 1, h⟩) with he | ho2
    · simp [Nat.add_mod, Nat.mul_mod, Nat.pow_mod, hodd, he]
    · simp [Nat.add_mod, Nat.mul_mod, Nat.pow_mod, hodd, ho2]
  · decide
  · decide

theorem corr_eq_zero_mul (Q : OrbitUpperChargeCertificate m M k)
    {i : Fin Q.length} (h : corr Q i = 0) :
    numer Q i * gap Q i = denom Q i * gap Q (Q.next i) := by
  have hz : (numer Q i : ℤ) * gap Q i - (denom Q i : ℤ) * gap Q (Q.next i) = 0 := by
    simpa [corr] using h
  exact_mod_cast (sub_eq_zero.mp hz)

theorem succIdx_val_of_lt (Q : OrbitUpperChargeCertificate m M k)
    {i : Fin Q.length} (h : i.val + 1 < Q.length) :
    (succIdx Q i).val = i.val + 1 := by
  let : NeZero Q.length := ⟨Q.length_pos.ne'⟩
  rw [succIdx, finRotate_val, Nat.mod_eq_of_lt h]

theorem succIdx_eq_add (Q : OrbitUpperChargeCertificate m M k)
    {i : Fin Q.length} (h : i.val + 1 < Q.length) :
    succIdx Q i = ⟨i.val + 1, h⟩ :=
  Fin.ext (succIdx_val_of_lt Q h)

theorem pred_succ (Q : OrbitUpperChargeCertificate m M k) (i : Fin Q.length) :
    predIdx Q (succIdx Q i) = i :=
  Equiv.symm_apply_apply (finRotate Q.length) i

theorem next_succ (Q : OrbitUpperChargeCertificate m M k) (i : Fin Q.length) :
    Q.next (succIdx Q i) = succIdx Q (Q.next i) := by
  let : NeZero Q.length := ⟨Q.length_pos.ne'⟩
  have hcomm :=
    rank_commute_finRotate Q.next (evenCount Q) (fun j => by
      simpa [evenCount] using Q.rotation j)
  exact hcomm.eq i

theorem gap_of_lt (Q : OrbitUpperChargeCertificate m M k)
    {i : Fin Q.length} (h : i.val + 1 < Q.length) :
    gap Q i = Q.state (succIdx Q i) - Q.state i := by
  unfold gap
  simp [h, succIdx_eq_add Q h]

theorem lastIdx_ne_of_succ_lt (Q : OrbitUpperChargeCertificate m M k)
    {i : Fin Q.length} (h : i.val + 1 < Q.length) :
    i ≠ lastIdx Q := by
  intro hi
  have : i.val = Q.length - 1 := by rw [hi]; rfl
  omega

theorem next_val_ne_last_of_not_cut (Q : OrbitUpperChargeCertificate m M k)
    (hm : 1 < m) (_hM : M < m ^ 3) {i : Fin Q.length}
    (hcut : i.val + 1 ≠ Q.oddCount) :
    (Q.next i).val ≠ Q.length - 1 := by
  intro hlast
  have hrot : (Q.next i).val = (i.val + evenCount Q) % Q.length := Q.rotation i
  have heq : (i.val + evenCount Q) % Q.length = Q.length - 1 := by
    simpa [hrot] using hlast
  rcases lt_or_ge (i.val + evenCount Q) Q.length with hlt | hge
  · rw [Nat.mod_eq_of_lt hlt] at heq
    have hassoc := (Nat.add_sub_assoc Q.oddCount_le i.val).symm
    have heq' : i.val + Q.length - Q.oddCount = Q.length - 1 := by
      simpa [evenCount, hassoc] using heq
    have hL : Q.oddCount ≤ i.val + Q.length :=
      Q.oddCount_le.trans (Nat.le_add_left Q.length i.val)
    have hadd := congrArg (fun n => n + Q.oddCount) heq'
    rw [Nat.sub_add_cancel hL] at hadd
    have hone : 1 ≤ Q.length := Nat.succ_le_of_lt Q.length_pos
    have : i.val + 1 = Q.oddCount := by omega
    exact hcut this
  · have h2 : i.val + evenCount Q < Q.length + Q.length := by
      have hle : i.val + 1 + evenCount Q ≤ Q.length + Q.length :=
        Nat.add_le_add (Nat.succ_le_of_lt i.isLt) (Nat.sub_le _ _)
      rw [Nat.add_right_comm] at hle
      exact Nat.lt_of_succ_le hle
    have hsub : i.val + evenCount Q - Q.length < Q.length :=
      Nat.sub_lt_left_of_lt_add hge h2
    have hsum := (Nat.add_sub_of_le hge).symm
    rw [hsum, Nat.add_mod, Nat.mod_self, Nat.zero_add, Nat.mod_mod,
      Nat.mod_eq_of_lt hsub] at heq
    have htot : i.val + evenCount Q = Q.length + (Q.length - 1) := by
      rw [hsum, heq]
    have hassoc := Nat.add_sub_assoc Q.oddCount_le i.val
    have htot' : i.val + Q.length - Q.oddCount = Q.length + (Q.length - 1) := by
      simpa [evenCount, hassoc] using htot
    have hL : Q.oddCount ≤ i.val + Q.length :=
      Q.oddCount_le.trans (Nat.le_add_left Q.length i.val)
    have hadd := congrArg (fun n => n + Q.oddCount) htot'
    rw [Nat.sub_add_cancel hL] at hadd
    have ho := oddCount_pos Q hm
    have hone : 1 ≤ Q.length := Nat.succ_le_of_lt Q.length_pos
    have hival : i.val = Q.length - 1 + Q.oddCount := by
      apply Nat.add_left_cancel (n := Q.length)
      calc
        Q.length + i.val = i.val + Q.length := Nat.add_comm _ _
        _ = Q.length + (Q.length - 1) + Q.oddCount := hadd
        _ = Q.length + (Q.length - 1 + Q.oddCount) := by
          rw [Nat.add_assoc]
    exact (not_le_of_gt i.isLt) (by omega)

theorem gap_next_of_not_cut (Q : OrbitUpperChargeCertificate m M k)
    (hm : 1 < m) (hM : M < m ^ 3) {i : Fin Q.length}
    (hcut : i.val + 1 ≠ Q.oddCount) :
    gap Q (Q.next i) =
      Q.state (Q.next (succIdx Q i)) - Q.state (Q.next i) := by
  have hlt : (Q.next i).val + 1 < Q.length := by
    have hne := next_val_ne_last_of_not_cut Q hm hM hcut
    have hbound : (Q.next i).val < Q.length := (Q.next i).isLt
    omega
  rw [gap_of_lt Q hlt, next_succ Q i]

theorem rem_add_int_odd (Q : OrbitUpperChargeCertificate m M k)
    {i : Fin Q.length} (ho : i.val < Q.oddCount) :
    (Q.state i : ℤ) ^ 3 = (Q.state (Q.next i) : ℤ) ^ 2 + rem Q i := by
  have h := rem_add Q i
  simp [ho] at h
  exact_mod_cast h

theorem rem_add_int_even (Q : OrbitUpperChargeCertificate m M k)
    {i : Fin Q.length} (he : ¬ i.val < Q.oddCount) :
    (Q.state i : ℤ) = (Q.state (Q.next i) : ℤ) ^ 2 + rem Q i := by
  have h := rem_add Q i
  simp [he] at h
  exact_mod_cast h

theorem cube_sub_cube_of_le {a b : ℕ} (hle : a ≤ b) :
    (b : ℤ) ^ 3 - (a : ℤ) ^ 3 =
      ((b - a : ℕ) : ℤ) *
        ((a : ℤ) ^ 2 + (a : ℤ) * b + (b : ℤ) ^ 2) := by
  have hcast : ((b - a : ℕ) : ℤ) = (b : ℤ) - a := Nat.cast_sub hle
  rw [hcast]
  ring

theorem sq_sub_sq_of_le {a b : ℕ} (hle : a ≤ b) :
    (b : ℤ) ^ 2 - (a : ℤ) ^ 2 =
      ((b - a : ℕ) : ℤ) * ((a : ℤ) + b) := by
  have hcast : ((b - a : ℕ) : ℤ) = (b : ℤ) - a := Nat.cast_sub hle
  rw [hcast]
  ring

theorem rem_diff_ordinary (Q : OrbitUpperChargeCertificate m M k)
    (hm : 1 < m) (hM : M < m ^ 3) {i : Fin Q.length}
    (hnext : i.val + 1 < Q.length) (hcut : i.val + 1 ≠ Q.oddCount) :
    corr Q i = (rem Q (succIdx Q i) : ℤ) - rem Q i := by
  have hgap : gap Q i = Q.state (succIdx Q i) - Q.state i :=
    gap_of_lt Q hnext
  have hgapσ : gap Q (Q.next i) =
      Q.state (Q.next (succIdx Q i)) - Q.state (Q.next i) :=
    gap_next_of_not_cut Q hm hM hcut
  have hle : Q.state i ≤ Q.state (succIdx Q i) := by
    apply Q.ordered.monotone
    rw [succIdx_eq_add Q hnext]
    exact Nat.le_succ i.val
  have hltσ : (Q.next i).val + 1 < Q.length := by
    have hne := next_val_ne_last_of_not_cut Q hm hM hcut
    have : (Q.next i).val < Q.length := (Q.next i).isLt
    omega
  have hleσ : Q.state (Q.next i) ≤ Q.state (Q.next (succIdx Q i)) := by
    apply Q.ordered.monotone
    rw [next_succ Q i, succIdx_eq_add Q hltσ]
    exact Nat.le_succ (Q.next i).val
  have hB : denom Q i =
      Q.state (Q.next i) + Q.state (Q.next (succIdx Q i)) := by
    unfold denom
    simp [hcut]
  by_cases ho : i.val < Q.oddCount
  · have ho' : (succIdx Q i).val < Q.oddCount := by
      rw [succIdx_val_of_lt Q hnext]; omega
    have hN : numer Q i =
        Q.state i ^ 2 + Q.state i * Q.state (succIdx Q i) +
          Q.state (succIdx Q i) ^ 2 := by
      unfold numer
      simp [hnext, ho, succIdx_eq_add Q hnext]
    have hsrc := cube_sub_cube_of_le hle
    have himg := sq_sub_sq_of_le hleσ
    have hodd := rem_add_int_odd Q ho
    have hodd' := rem_add_int_odd Q ho'
    have hc : ((Q.state (succIdx Q i) - Q.state i : ℕ) : ℤ) =
        (Q.state (succIdx Q i) : ℤ) - Q.state i := Nat.cast_sub hle
    have ht : ((Q.state (Q.next (succIdx Q i)) - Q.state (Q.next i) : ℕ) : ℤ) =
        (Q.state (Q.next (succIdx Q i)) : ℤ) - Q.state (Q.next i) :=
      Nat.cast_sub hleσ
    have hBc : ((Q.state (Q.next i) + Q.state (Q.next (succIdx Q i)) : ℕ) : ℤ) =
        (Q.state (Q.next i) : ℤ) + Q.state (Q.next (succIdx Q i)) :=
      Nat.cast_add _ _
    have hNc :
        ((Q.state i ^ 2 + Q.state i * Q.state (succIdx Q i) +
            Q.state (succIdx Q i) ^ 2 : ℕ) : ℤ) =
          (Q.state i : ℤ) ^ 2 + (Q.state i : ℤ) * Q.state (succIdx Q i) +
            (Q.state (succIdx Q i) : ℤ) ^ 2 := by
      push_cast
      rfl
    unfold corr
    rw [hgap, hgapσ, hN, hB, hc, ht, hBc, hNc]
    linarith [hsrc, himg, hodd, hodd']
  · have ho' : ¬ (succIdx Q i).val < Q.oddCount := by
      rw [succIdx_val_of_lt Q hnext]; omega
    have hN : numer Q i = 1 := by
      unfold numer
      simp [hnext, ho]
    have himg := sq_sub_sq_of_le hleσ
    have heven := rem_add_int_even Q ho
    have heven' := rem_add_int_even Q ho'
    have hc : ((Q.state (succIdx Q i) - Q.state i : ℕ) : ℤ) =
        (Q.state (succIdx Q i) : ℤ) - Q.state i := Nat.cast_sub hle
    have ht : ((Q.state (Q.next (succIdx Q i)) - Q.state (Q.next i) : ℕ) : ℤ) =
        (Q.state (Q.next (succIdx Q i)) : ℤ) - Q.state (Q.next i) :=
      Nat.cast_sub hleσ
    have hBc : ((Q.state (Q.next i) + Q.state (Q.next (succIdx Q i)) : ℕ) : ℤ) =
        (Q.state (Q.next i) : ℤ) + Q.state (Q.next (succIdx Q i)) :=
      Nat.cast_add _ _
    unfold corr
    rw [hgap, hgapσ, hN, hB, hc, ht, hBc, Nat.cast_one]
    linarith [himg, heven, heven']

def blockBeta (Q : OrbitUpperChargeCertificate m M k)
    (βOO βOE βEO : ℕ) (i : Fin Q.length) : ℕ :=
  if i.val < excess Q then βOO
  else if i.val < Q.oddCount then βOE
  else βEO

def deviations (Q : OrbitUpperChargeCertificate m M k)
    (βOO βOE βEO : ℕ) : Finset (Fin Q.length) :=
  Finset.univ.filter fun i => rem Q i ≠ blockBeta Q βOO βOE βEO i

def resets (Q : OrbitUpperChargeCertificate m M k) : Finset (Fin Q.length) :=
  Finset.univ.filter fun i => corr Q i ≠ 0

def boundary (Q : OrbitUpperChargeCertificate m M k)
    (hm : 1 < m) (hM : M < m ^ 3) : Finset (Fin Q.length) :=
  {ooCut Q hm hM, lastOdd Q hm hM, lastIdx Q}

theorem boundary_card_le (Q : OrbitUpperChargeCertificate m M k)
    (hm : 1 < m) (hM : M < m ^ 3) :
    (boundary Q hm hM).card ≤ 3 := by
  simpa [boundary] using
    (Finset.card_insert_le (ooCut Q hm hM) {lastOdd Q hm hM, lastIdx Q}).trans
      (Nat.succ_le_succ
        ((Finset.card_insert_le (lastOdd Q hm hM) {lastIdx Q}).trans
          (Nat.succ_le_succ (by simp))))

/-- Leftover RC70 from an assembled even-denominator and deviation cover. -/
theorem leftover_rc70_of_cover (Q : OrbitUpperChargeCertificate m M k)
    (hm : 1 < m) (hM : M < m ^ 3) (hmin : m < 520000000)
    (βOO βOE βEO : ℕ)
    (heven : ∀ i, i ∉ resets Q → denom Q i % 2 = 0)
    (hcover : resets Q ⊆
      boundary Q hm hM ∪ deviations Q βOO βOE βEO ∪
        (deviations Q βOO βOE βEO).image (predIdx Q)) :
    Q.length ≤ (86 + 1) * (3 + 2 * (deviations Q βOO βOE βEO).card) := by
  have hcard : Fintype.card (Fin Q.length) = Q.length := Fintype.card_fin _
  simpa [hcard] using
    arithmetic_three_block_deviations (next := Q.next) (l := gap Q)
      (N := numer Q) (B := denom Q) 86
      (resets Q) (boundary Q hm hM) (deviations Q βOO βOE βEO)
      (predIdx Q)
      (fun i => gap_pos Q hM i)
      (fun i => numer_pos Q hm i)
      (fun i => denom_pos Q hm hM i)
      (fun i => leftover_gap_val_le Q hM hmin i)
      (fun i _ => numer_odd Q i)
      heven
      (fun i hi => corr_eq_zero_mul Q (by
        have : i ∈ resets Q ↔ corr Q i ≠ 0 := by
          simp [resets, Finset.mem_filter]
        simpa [this] using hi))
      (boundary_card_le Q hm hM)
      hcover

theorem leftover_deviation_lower_of_cover
    (Q : OrbitUpperChargeCertificate m M k)
    (hm : 1 < m) (hM : M < m ^ 3) (hmin : m < 520000000)
    (hL : Q.length = 780239)
    (βOO βOE βEO : ℕ)
    (heven : ∀ i, i ∉ resets Q → denom Q i % 2 = 0)
    (hcover : resets Q ⊆
      boundary Q hm hM ∪ deviations Q βOO βOE βEO ∪
        (deviations Q βOO βOE βEO).image (predIdx Q)) :
    4483 ≤ (deviations Q βOO βOE βEO).card := by
  have hrc := leftover_rc70_of_cover Q hm hM hmin βOO βOE βEO heven hcover
  have hcount : 780239 ≤ (86 + 1) * (3 + 2 * (deviations Q βOO βOE βEO).card) := by
    omega
  exact fixed_count_deviation_lower (Nat.le_refl 86) hcount

/-- Result 20 conditional consumer: supplied even-gap block lengths and
`runCost` inequalities at the leftover tuple yield RC79. -/
theorem leftover_run_critical_of_blocks
    {ι : Type*} [Fintype ι]
    (length cost : ι → ℕ)
    (hlength : ∀ i, 0 < length i)
    (hsum : ∑ i, length i = 780237)
    (hcost : ∀ i, runCost (length i) ≤ cost i)
    (hbudget : 4 + ∑ i, cost i ≤ m ^ 3 - m)
    (hgap : m ^ 3 - m ≤ 519999999 ^ 3 - 519999999) :
    14569 ≤ Fintype.card ι :=
  fixed_run_budget_critical_count_lower length cost (m ^ 3 - m)
    hlength hsum hcost hbudget hgap

theorem leftover_reset_lower_of_count {H T : ℕ} (hH : H ≤ 86)
    (hcount : 780239 ≤ (H + 1) * T) : 8969 ≤ T :=
  fixed_count_reset_lower hH hcount

theorem leftover_run_nonzero_of_blocks {C T : ℕ}
    (hC : 14569 ≤ C) (hfilter : C + 2 ≤ T) : 14571 ≤ T :=
  CubicConstraintFusion.fixed_nonzero_lower hC hfilter

theorem leftover_run_deviation_of_blocks {C S : ℕ}
    (hC : 14569 ≤ C) (hcover : C ≤ 1 + 2 * S) : 7284 ≤ S :=
  CubicConstraintFusion.fixed_deviation_lower hC hcover

end Problems.Juggler.CubicRemainderAssembly
