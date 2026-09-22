import Problems.Juggler.Defect

namespace Problems.Juggler

/-!
# Global accumulated defect

Local floor remainders compose by a weighted lift, not by addition.
`powGap a ρ e = (a+ρ)^e - a^e` is the exact increment. An even letter
adds a lift of the local remainder through `2^k`. An odd letter cubes
the running slack and then lifts the new remainder.

This file does not claim that every start reaches `1`.
-/

/-- Exact increment of an `e`-th power under a nonnegative addend. -/
def powGap (a ρ e : ℕ) : ℕ :=
  (a + ρ) ^ e - a ^ e

theorem powGap_add (a ρ e : ℕ) :
    a ^ e + powGap a ρ e = (a + ρ) ^ e :=
  Nat.add_sub_of_le (Nat.pow_le_pow_left (Nat.le_add_right a ρ) e)

@[simp] theorem powGap_zero_addend (a e : ℕ) : powGap a 0 e = 0 := by
  simp [powGap]

@[simp] theorem powGap_zero_exp (a ρ : ℕ) : powGap a ρ 0 = 0 := by
  simp [powGap]

theorem powGap_ge_pow {a ρ e : ℕ} (he : 1 ≤ e) :
    ρ ^ e ≤ powGap a ρ e := by
  have hsum : a ^ e + ρ ^ e ≤ (a + ρ) ^ e :=
    pow_add_pow_le_add_pow he
  exact Nat.le_sub_of_add_le (add_comm (a ^ e) _ ▸ hsum)

theorem powGap_ge {a ρ e : ℕ} (he : 1 ≤ e) :
    ρ ≤ powGap a ρ e :=
  le_trans (Nat.le_self_pow (Nat.pos_iff_ne_zero.mp he) ρ) (powGap_ge_pow he)

theorem powGap_eq_zero_iff {a ρ e : ℕ} (he : 1 ≤ e) :
    powGap a ρ e = 0 ↔ ρ = 0 := by
  constructor
  · intro h
    by_contra hρ
    have hlt : a ^ e < (a + ρ) ^ e :=
      Nat.pow_lt_pow_left (Nat.lt_add_of_pos_right (Nat.pos_of_ne_zero hρ))
        (Nat.pos_iff_ne_zero.mp he)
    exact (not_le_of_gt hlt) (Nat.sub_eq_zero_iff_le.mp h)
  · intro h
    simp [powGap, h]

/-- Even step at prefix length `k`. -/
def accumulateEven (D ρ y k : ℕ) : ℕ :=
  D + powGap (y ^ 2) ρ (2 ^ k)

/-- Odd step at prefix length `k`. -/
def accumulateOdd (D ρ x y k : ℕ) : ℕ :=
  powGap (y ^ 2) ρ (2 ^ k) + powGap (x ^ (2 ^ k)) D 3

theorem accumulateEven_ge (D ρ y k : ℕ) :
    D ≤ accumulateEven D ρ y k :=
  Nat.le_add_right _ _

theorem accumulateOdd_ge (D ρ x y k : ℕ) :
    D ≤ accumulateOdd D ρ x y k :=
  le_trans (powGap_ge (by decide : (1 : ℕ) ≤ 3)) (Nat.le_add_left _ _)

/-- Running accumulation along a remaining suffix. `k` is letters already consumed. -/
def accumulatedDefect (current D k : ℕ) : List Branch → ℕ
  | [] => D
  | .even :: w =>
      accumulatedDefect (floorPower current)
        (accumulateEven D (localDefectEven current) (floorPower current) k)
        (k + 1) w
  | .odd :: w =>
      accumulatedDefect (floorPower current)
        (accumulateOdd D (localDefectOdd current) current (floorPower current) k)
        (k + 1) w

def globalDefect (n : ℕ) (w : List Branch) : ℕ :=
  accumulatedDefect n 0 0 w

theorem global_defect_nonneg (n : ℕ) (w : List Branch) :
    0 ≤ globalDefect n w :=
  Nat.zero_le _

theorem accumulatedDefect_ge (current D k : ℕ) :
    ∀ w, D ≤ accumulatedDefect current D k w
  | [] => le_rfl
  | .even :: w =>
      le_trans (accumulateEven_ge D _ _ k) (accumulatedDefect_ge _ _ _ w)
  | .odd :: w =>
      le_trans (accumulateOdd_ge D _ _ _ k) (accumulatedDefect_ge _ _ _ w)

theorem pow_sq_pow (y k : ℕ) :
    (y ^ 2) ^ (2 ^ k) = y ^ (2 ^ (k + 1)) := by
  rw [← Nat.pow_mul, two_pow_succ, mul_comm]

theorem pow_cube_pow (x k : ℕ) :
    (x ^ (2 ^ k)) ^ 3 = (x ^ 3) ^ (2 ^ k) := by
  rw [← Nat.pow_mul, mul_comm, Nat.pow_mul]

theorem pow_three_succ (n o : ℕ) :
    (n ^ (3 ^ o)) ^ 3 = n ^ (3 ^ (o + 1)) := by
  rw [← Nat.pow_mul, mul_comm, ← three_pow_succ]

theorem pow_three_add (n a b : ℕ) :
    n ^ (3 ^ (a + b)) = (n ^ (3 ^ a)) ^ (3 ^ b) := by
  rw [pow_add, Nat.pow_mul]

theorem accumulateEven_rewrite (D ρ y k : ℕ) :
    (y ^ 2 + ρ) ^ (2 ^ k) + D =
      y ^ (2 ^ (k + 1)) + accumulateEven D ρ y k := by
  have h := powGap_add (y ^ 2) ρ (2 ^ k)
  rw [← h, pow_sq_pow]
  simp [accumulateEven]
  ac_rfl

theorem accumulateOdd_rewrite (D ρ x y k : ℕ)
    (hy : y ^ 2 + ρ = x ^ 3) :
    (x ^ (2 ^ k) + D) ^ 3 =
      y ^ (2 ^ (k + 1)) + accumulateOdd D ρ x y k := by
  have hcube := powGap_add (x ^ (2 ^ k)) D 3
  have hlift := powGap_add (y ^ 2) ρ (2 ^ k)
  rw [← hcube, pow_cube_pow, ← hy, ← hlift, pow_sq_pow]
  simp [accumulateOdd]
  ac_rfl

/-- Generalized identity: a prefix slack `D` extends through any realized suffix. -/
theorem accumulatedDefect_identity {start current D k o : ℕ} :
    ∀ w, follows current w →
      start ^ (3 ^ o) = current ^ (2 ^ k) + D →
      start ^ (3 ^ (o + oddCount w)) =
        image current w ^ (2 ^ (k + w.length)) +
          accumulatedDefect current D k w
  | [], _, hstart => by
      simpa [image, oddCount, accumulatedDefect] using hstart
  | .even :: rest, hw, hstart => by
      have hy : floorPower current ^ 2 + localDefectEven current = current :=
        localDefectEven_add hw.1
      have hstart0 :
          start ^ (3 ^ o) =
            (floorPower current ^ 2 + localDefectEven current) ^ (2 ^ k) + D := by
        simpa [hy] using hstart
      have hstart' :
          start ^ (3 ^ o) =
            floorPower current ^ (2 ^ (k + 1)) +
              accumulateEven D (localDefectEven current) (floorPower current) k :=
        (accumulateEven_rewrite D (localDefectEven current)
          (floorPower current) k) ▸ hstart0
      have hih :=
        accumulatedDefect_identity (start := start)
          (current := floorPower current)
          (D := accumulateEven D (localDefectEven current) (floorPower current) k)
          (k := k + 1) (o := o) rest hw.2 hstart'
      have hk : k + (rest.length + 1) = k + 1 + rest.length := by omega
      simpa [image, oddCount_even_cons, List.length_cons, accumulatedDefect, hk]
        using hih
  | .odd :: rest, hw, hstart => by
      have hy : floorPower current ^ 2 + localDefectOdd current = current ^ 3 :=
        localDefectOdd_add hw.1
      have hstart' :
          start ^ (3 ^ (o + 1)) =
            floorPower current ^ (2 ^ (k + 1)) +
              accumulateOdd D (localDefectOdd current) current
                (floorPower current) k := by
        rw [← pow_three_succ, hstart]
        exact accumulateOdd_rewrite _ _ _ _ _ hy
      have hih :=
        accumulatedDefect_identity (start := start)
          (current := floorPower current)
          (D := accumulateOdd D (localDefectOdd current) current
            (floorPower current) k)
          (k := k + 1) (o := o + 1) rest hw.2 hstart'
      have hk : k + (rest.length + 1) = k + 1 + rest.length := by omega
      have ho : o + (oddCount rest + 1) = o + 1 + oddCount rest := by omega
      simpa [image, oddCount_odd_cons, List.length_cons, accumulatedDefect, hk, ho]
        using hih

/-- Core identity: `n^{3^o} = T_w(n)^{2^k} + Δ_w(n)`. -/
theorem global_defect_identity {n : ℕ} {w : List Branch} (hw : follows n w) :
    n ^ (3 ^ oddCount w) =
      image n w ^ (2 ^ w.length) + globalDefect n w := by
  have h0 : n ^ (3 ^ 0) = n ^ (2 ^ 0) + 0 := by simp
  simpa [globalDefect] using
    accumulatedDefect_identity (start := n) (current := n) (D := 0)
      (k := 0) (o := 0) w hw h0

/-- The envelope is the nonnegativity of the accumulated defect. -/
theorem power_bound_of_global_defect {n : ℕ} {w : List Branch}
    (hw : follows n w) :
    PowerBound (image n w) n w.length (oddCount w) :=
  Nat.le.intro (global_defect_identity hw).symm

theorem power_bound_follows_of_global_defect {n : ℕ} {w : List Branch}
    (hw : follows n w) :
    PowerBound (floorPower^[w.length] n) n w.length (oddCount w) := by
  simpa [image_eq_iterate] using power_bound_of_global_defect hw

theorem globalDefect_eq_powerDeficit {n : ℕ} {w : List Branch}
    (hw : follows n w) :
    globalDefect n w =
      powerDeficit (image n w) n w.length (oddCount w) := by
  have h := global_defect_identity hw
  have hle : image n w ^ (2 ^ w.length) ≤ n ^ (3 ^ oddCount w) :=
    Nat.le.intro h.symm
  unfold powerDeficit
  exact ((Nat.sub_eq_iff_eq_add hle).mpr (h.trans (add_comm _ _))).symm

theorem global_defect_eq_zero_iff {n : ℕ} {w : List Branch}
    (hw : follows n w) :
    globalDefect n w = 0 ↔
      PowerBoundEq (image n w) n w.length (oddCount w) := by
  have hid := global_defect_identity hw
  constructor
  · intro hz
    rw [hz, Nat.add_zero] at hid
    exact hid.symm
  · intro heq
    have hid' : image n w ^ (2 ^ w.length) =
        image n w ^ (2 ^ w.length) + globalDefect n w := by
      rwa [← heq] at hid
    exact Nat.add_eq_left.mp hid'.symm

theorem globalDefect_singleton {n : ℕ} {b : Branch}
    (hw : follows n [b]) :
    globalDefect n [b] = branchDefect b n := by
  cases b with
  | even =>
      simp [globalDefect, accumulatedDefect, accumulateEven, powGap, branchDefect,
        localDefectEven]
  | odd =>
      simp [globalDefect, accumulatedDefect, accumulateOdd, powGap, branchDefect,
        localDefectOdd]

theorem localsTight_iff_zero_defects {n : ℕ} :
    ∀ {w}, follows n w →
      (localsTight n w ↔
        ∀ i, (hi : i < w.length) →
          branchDefect w[i] (floorPower^[i] n) = 0)
  | [], _ => by
      constructor
      · intro _ i hi
        cases hi
      · intro
        trivial
  | b :: rest, hw => by
      have hf : follows n [b] := by
        cases b <;> exact ⟨hw.1, trivial⟩
      have hrest : follows (floorPower n) rest := by
        cases b <;> exact hw.2
      have ih := localsTight_iff_zero_defects (n := floorPower n) hrest
      constructor
      · intro ht i hi
        cases i with
        | zero =>
            exact (branchDefect_eq_zero_iff_localTight hf).mpr ht.1
        | succ j =>
            have hj : j < rest.length := by
              simpa [List.length_cons] using Nat.succ_lt_succ_iff.mp hi
            simpa [List.getElem_cons_succ, iterate_cons] using ih.mp ht.2 j hj
      · intro hz
        refine ⟨(branchDefect_eq_zero_iff_localTight hf).mp ?_, ih.mpr ?_⟩
        · simpa [List.getElem_cons_zero] using hz 0 (Nat.succ_pos _)
        · intro j hj
          have hj' : j + 1 < (b :: rest).length := by
            simpa [List.length_cons] using Nat.succ_lt_succ hj
          simpa [List.getElem_cons_succ, iterate_cons] using hz (j + 1) hj'

theorem accumulatedDefect_eq_zero_iff {current D k : ℕ} :
    ∀ w, follows current w →
      (accumulatedDefect current D k w = 0 ↔
        D = 0 ∧
          ∀ i, (hi : i < w.length) →
            branchDefect w[i] (floorPower^[i] current) = 0)
  | [], _ => by
      simp [accumulatedDefect]
  | .even :: rest, hw => by
      have he : 1 ≤ 2 ^ k := Nat.one_le_two_pow
      have ih :=
        accumulatedDefect_eq_zero_iff (current := floorPower current)
          (D := accumulateEven D (localDefectEven current) (floorPower current) k)
          (k := k + 1) rest hw.2
      constructor
      · intro hz
        have ⟨hD', hrest0⟩ := ih.mp (by simpa [accumulatedDefect] using hz)
        have hsum :=
          Nat.add_eq_zero_iff.mp (by simpa [accumulateEven] using hD')
        refine ⟨hsum.1, ?_⟩
        intro i hi
        cases i with
        | zero =>
            have hρ : localDefectEven current = 0 :=
              (powGap_eq_zero_iff he).mp hsum.2
            simpa [branchDefect, List.getElem_cons_zero] using hρ
        | succ j =>
            have hj : j < rest.length := by
              simpa [List.length_cons] using Nat.succ_lt_succ_iff.mp hi
            simpa [List.getElem_cons_succ, iterate_cons] using hrest0 j hj
      · intro ⟨hD0, hz⟩
        have hρ : localDefectEven current = 0 := by
          simpa [branchDefect, List.getElem_cons_zero] using hz 0 (Nat.succ_pos _)
        have hD' :
            accumulateEven D (localDefectEven current) (floorPower current) k = 0 := by
          simp [accumulateEven, hD0, hρ]
        refine ih.mpr ⟨hD', ?_⟩
        intro j hj
        have hj' : j + 1 < (Branch.even :: rest).length := by
          simpa [List.length_cons] using Nat.succ_lt_succ hj
        simpa [List.getElem_cons_succ, iterate_cons] using hz (j + 1) hj'
  | .odd :: rest, hw => by
      have he : 1 ≤ 2 ^ k := Nat.one_le_two_pow
      have ih :=
        accumulatedDefect_eq_zero_iff (current := floorPower current)
          (D := accumulateOdd D (localDefectOdd current) current (floorPower current) k)
          (k := k + 1) rest hw.2
      constructor
      · intro hz
        have ⟨hD', hrest0⟩ := ih.mp (by simpa [accumulatedDefect] using hz)
        have hparts :=
          Nat.add_eq_zero_iff.mp (by simpa [accumulateOdd] using hD')
        refine ⟨(powGap_eq_zero_iff (by decide : (1 : ℕ) ≤ 3)).mp hparts.2, ?_⟩
        intro i hi
        cases i with
        | zero =>
            have hρ : localDefectOdd current = 0 :=
              (powGap_eq_zero_iff he).mp hparts.1
            simpa [branchDefect, List.getElem_cons_zero] using hρ
        | succ j =>
            have hj : j < rest.length := by
              simpa [List.length_cons] using Nat.succ_lt_succ_iff.mp hi
            simpa [List.getElem_cons_succ, iterate_cons] using hrest0 j hj
      · intro ⟨hD0, hz⟩
        have hρ : localDefectOdd current = 0 := by
          simpa [branchDefect, List.getElem_cons_zero] using hz 0 (Nat.succ_pos _)
        have hD' :
            accumulateOdd D (localDefectOdd current) current (floorPower current) k = 0 := by
          simp [accumulateOdd, hD0, hρ]
        refine ih.mpr ⟨hD', ?_⟩
        intro j hj
        have hj' : j + 1 < (Branch.odd :: rest).length := by
          simpa [List.length_cons] using Nat.succ_lt_succ hj
        simpa [List.getElem_cons_succ, iterate_cons] using hz (j + 1) hj'

theorem global_defect_eq_zero_iff_locals {n : ℕ} {w : List Branch}
    (hw : follows n w) :
    globalDefect n w = 0 ↔
      ∀ i, (hi : i < w.length) →
        branchDefect w[i] (floorPower^[i] n) = 0 := by
  have h := accumulatedDefect_eq_zero_iff (current := n) (D := 0) (k := 0) w hw
  constructor
  · intro hz
    exact (h.mp (by simpa [globalDefect] using hz)).2
  · intro hz
    simpa [globalDefect] using h.mpr ⟨rfl, hz⟩

theorem global_defect_eq_zero_iff_localsTight {n : ℕ} {w : List Branch}
    (hw : follows n w) :
    globalDefect n w = 0 ↔ localsTight n w := by
  rw [global_defect_eq_zero_iff_locals hw, localsTight_iff_zero_defects hw]

theorem global_defect_pos_of_mixed {n : ℕ} {w : List Branch}
    (hw : follows n w) (hmix : ¬ isMonochrome w) :
    0 < globalDefect n w := by
  have htight := not_localsTight_of_nonmonochrome hw hmix
  exact Nat.pos_of_ne_zero fun hz =>
    htight ((global_defect_eq_zero_iff_localsTight hw).mp hz)

theorem global_defect_eq_zero_implies_monochrome {n : ℕ} {w : List Branch}
    (hw : follows n w) (hz : globalDefect n w = 0) :
    isMonochrome w := by
  have heq : PowerBoundEq (image n w) n w.length (oddCount w) :=
    (global_defect_eq_zero_iff hw).mp hz
  have heq' : PowerBoundEq (floorPower^[w.length] n) n w.length (oddCount w) := by
    simpa [image_eq_iterate] using heq
  exact power_bound_eq_implies_monochrome hw heq'

/-- Exact composition law. Not an additive cocycle. -/
theorem global_defect_append {n : ℕ} {u v : List Branch}
    (hu : follows n u) (hv : follows (image n u) v) :
    globalDefect n (u ++ v) =
      powGap (image n u ^ (2 ^ u.length)) (globalDefect n u)
        (3 ^ oddCount v) +
      powGap (image (image n u) v ^ (2 ^ v.length))
        (globalDefect (image n u) v) (2 ^ u.length) := by
  have hid := global_defect_identity (follows_append hu hv)
  have hu' := global_defect_identity hu
  have hv' := global_defect_identity hv
  have himg : image n (u ++ v) = image (image n u) v := image_append n u v
  have ho : oddCount (u ++ v) = oddCount u + oddCount v := oddCount_append u v
  have hk : (u ++ v).length = u.length + v.length := List.length_append
  have hleft :
      n ^ (3 ^ (oddCount u + oddCount v)) =
        image (image n u) v ^ (2 ^ (u.length + v.length)) +
          globalDefect n (u ++ v) := by
    simpa [himg, ho, hk] using hid
  have hmid3 :
      n ^ (3 ^ (oddCount u + oddCount v)) =
        (image n u ^ (2 ^ u.length) + globalDefect n u) ^
          (3 ^ oddCount v) := by
    rw [pow_three_add, hu']
  have hliftU :=
    powGap_add (image n u ^ (2 ^ u.length)) (globalDefect n u)
      (3 ^ oddCount v)
  have hmidPow :
      (image n u ^ (2 ^ u.length)) ^ (3 ^ oddCount v) =
        (image n u ^ (3 ^ oddCount v)) ^ (2 ^ u.length) := by
    rw [← Nat.pow_mul, mul_comm, Nat.pow_mul]
  have hexp :
      (image (image n u) v ^ (2 ^ v.length)) ^ (2 ^ u.length) =
        image (image n u) v ^ (2 ^ (u.length + v.length)) := by
    rw [← Nat.pow_mul, ← pow_add, add_comm]
  have hliftV :=
    powGap_add (image (image n u) v ^ (2 ^ v.length))
      (globalDefect (image n u) v) (2 ^ u.length)
  have hright :
      n ^ (3 ^ (oddCount u + oddCount v)) =
        image (image n u) v ^ (2 ^ (u.length + v.length)) +
          (powGap (image n u ^ (2 ^ u.length)) (globalDefect n u)
            (3 ^ oddCount v) +
            powGap (image (image n u) v ^ (2 ^ v.length))
              (globalDefect (image n u) v) (2 ^ u.length)) := by
    rw [hmid3, ← hliftU, hmidPow, hv', ← hliftV, hexp]
    ac_rfl
  exact Nat.add_left_cancel (hleft.symm.trans hright)

theorem global_defect_ge_suffix {n : ℕ} {u v : List Branch}
    (hu : follows n u) (hv : follows (image n u) v) :
    (globalDefect (image n u) v) ^ (2 ^ u.length) ≤ globalDefect n (u ++ v) := by
  rw [global_defect_append hu hv]
  exact le_trans (powGap_ge_pow Nat.one_le_two_pow) (Nat.le_add_left _ _)

theorem globalDefect_cons_ge_head {n : ℕ} {b : Branch} {w : List Branch}
    (hw : follows n (b :: w)) :
    branchDefect b n ≤ globalDefect n (b :: w) := by
  cases b with
  | even =>
      have hD : accumulateEven 0 (localDefectEven n) (floorPower n) 0 =
          branchDefect .even n := by
        simpa [globalDefect, accumulatedDefect, branchDefect] using
          globalDefect_singleton (n := n) (b := .even) ⟨hw.1, trivial⟩
      simp [globalDefect, accumulatedDefect]
      rw [hD]
      exact accumulatedDefect_ge _ _ _ _
  | odd =>
      have hD : accumulateOdd 0 (localDefectOdd n) n (floorPower n) 0 =
          branchDefect .odd n := by
        simpa [globalDefect, accumulatedDefect, branchDefect] using
          globalDefect_singleton (n := n) (b := .odd) ⟨hw.1, trivial⟩
      simp [globalDefect, accumulatedDefect]
      rw [hD]
      exact accumulatedDefect_ge _ _ _ _

theorem global_defect_ge_local {n : ℕ} {w : List Branch} {i : ℕ}
    (hw : follows n w) (hi : i < w.length) :
    (branchDefect w[i] (floorPower^[i] n)) ^ (2 ^ i) ≤ globalDefect n w := by
  have hlen : (w.take i).length = i := List.length_take_of_le (Nat.le_of_lt hi)
  have hsplit : w.take i ++ w.drop i = w := List.take_append_drop i w
  have hu : follows n (w.take i) := follows_take w i hw
  have hw' : follows n (w.take i ++ w.drop i) := by
    rw [hsplit]
    exact hw
  have hv : follows (image n (w.take i)) (w.drop i) :=
    follows_of_append_right hw'
  have himg : image n (w.take i) = floorPower^[i] n :=
    image_take_of_le (Nat.le_of_lt hi)
  have hdrop : w.drop i = w[i] :: w.drop (i + 1) :=
    List.drop_eq_getElem_cons hi
  have hcons : follows (floorPower^[i] n) (w[i] :: w.drop (i + 1)) := by
    rw [← hdrop, ← himg]
    exact hv
  have hhead := globalDefect_cons_ge_head hcons
  have hcomp := global_defect_ge_suffix (u := w.take i) (v := w.drop i) hu hv
  have hge :
      (branchDefect w[i] (floorPower^[i] n)) ^ (2 ^ i) ≤
        (globalDefect (floorPower^[i] n) (w.drop i)) ^ (2 ^ i) :=
    Nat.pow_le_pow_left (hdrop ▸ hhead) _
  rw [himg, hlen, hsplit] at hcomp
  exact le_trans hge hcomp

end Problems.Juggler
