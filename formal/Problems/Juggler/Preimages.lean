import Problems.Juggler.Defect

namespace Problems.Juggler

/-!
# One-step preimages and first-even geometry

One-step preimage of a Juggler step. This is the integer interval
for `T(n) = M`, not a termination theorem and not a perfect-power
height.

The remaining Diophantine question — whether an odd first defect can
satisfy `HasPowTwoDepth (floorPower n) s` for some `s ≥ 2` when
`⌊∛(a^8)⌋` is even — is not claimed here. Finite search is not an
impossibility theorem.
-/

theorem floor_sqrt_eq_iff_sq_interval {n M : ℕ} :
    n.sqrt = M ↔ M ^ 2 ≤ n ∧ n < (M + 1) ^ 2 := by
  constructor
  · intro h
    subst h
    exact ⟨by simpa [pow_two] using Nat.sqrt_le n,
      by simpa [pow_two, Nat.succ_eq_add_one] using Nat.lt_succ_sqrt n⟩
  · intro ⟨hle, hlt⟩
    apply Nat.eq_of_le_of_lt_succ
    · exact Nat.le_sqrt.mpr (by simpa [pow_two] using hle)
    · exact Nat.sqrt_lt.mpr (by simpa [pow_two] using hlt)

theorem floorPower_even_eq_iff_sq_interval {n M : ℕ} (heven : n % 2 = 0) :
    floorPower n = M ↔ M ^ 2 ≤ n ∧ n < (M + 1) ^ 2 := by
  rw [floorPower_even_eq heven]
  exact floor_sqrt_eq_iff_sq_interval

theorem floorPower_odd_eq_iff_cube_interval {n M : ℕ} (hodd : n % 2 = 1) :
    floorPower n = M ↔ M ^ 2 ≤ n ^ 3 ∧ n ^ 3 < (M + 1) ^ 2 := by
  rw [floorPower_odd_eq hodd]
  exact floor_sqrt_eq_iff_sq_interval

theorem floorPower_odd_eq_pow_two_depth_iff {n a s : ℕ} (hodd : n % 2 = 1) :
    floorPower n = a ^ (2 ^ s) ↔
      a ^ (2 ^ (s + 1)) ≤ n ^ 3 ∧ n ^ 3 < (a ^ (2 ^ s) + 1) ^ 2 := by
  have hsq : (a ^ (2 ^ s)) ^ 2 = a ^ (2 ^ (s + 1)) := (pow_two_succ_sq a s).symm
  constructor
  · intro h
    have hI := (floorPower_odd_eq_iff_cube_interval hodd).mp h
    exact ⟨hsq ▸ hI.1, hI.2⟩
  · intro h
    exact (floorPower_odd_eq_iff_cube_interval hodd).mpr ⟨hsq ▸ h.1, h.2⟩

/-!
## Fourth-power window

Nearest-cube form of `a^8 ≤ n^3 < (a^4+1)^2`. Occupancy is at most one
cube. A non-cube `a` leaves only the candidate `⌊∛(a^8)⌋+1`. That
candidate is even exactly when the cube root is odd. This does not
kill an even cube-root, and is not a termination theorem.
-/

theorem succ_cube_sub_cube (m : ℕ) :
    (m + 1) ^ 3 = m ^ 3 + (3 * m ^ 2 + 3 * m + 1) := by
  ring

theorem fourth_window_span (a : ℕ) :
    (a ^ 4 + 1) ^ 2 = a ^ 8 + 2 * a ^ 4 + 1 := by
  ring

theorem nat_cbrt_eq_iff {m N : ℕ} :
    Nat.nthRoot 3 N = m ↔ m ^ 3 ≤ N ∧ N < (m + 1) ^ 3 := by
  constructor
  · intro h
    subst h
    exact ⟨Nat.pow_nthRoot_le (Or.inl (by decide : (3 : ℕ) ≠ 0)),
      Nat.lt_pow_nthRoot_add_one (by decide : (3 : ℕ) ≠ 0) N⟩
  · intro ⟨hle, hlt⟩
    exact Nat.nthRoot_eq_of_le_of_lt hle hlt

theorem pow_eight_eq_cube {a m : ℕ} (h : a ^ 8 = m ^ 3) :
    ∃ k, a = k ^ 3 ∧ m = k ^ 8 := by
  obtain ⟨c, ha, hm⟩ :=
    Nat.exists_eq_pow_of_pow_eq_pow (Or.inl (by decide : (8 : ℕ) ≠ 0)) h
  have hg : Nat.gcd 8 3 = 1 := by decide
  have h3 : 3 / Nat.gcd 8 3 = 3 := by simp [hg]
  have h8 : 8 / Nat.gcd 8 3 = 8 := by simp [hg]
  exact ⟨c, by simpa [h3] using ha, by simpa [h8] using hm⟩

theorem is_cube_iff_eighth_is_cube {a : ℕ} :
    (∃ k, a = k ^ 3) ↔ Nat.nthRoot 3 (a ^ 8) ^ 3 = a ^ 8 := by
  constructor
  · rintro ⟨k, rfl⟩
    have hpow : (k ^ 3) ^ 8 = (k ^ 8) ^ 3 := by ring
    rw [hpow, Nat.nthRoot_pow (by decide : (3 : ℕ) ≠ 0)]
  · intro h
    obtain ⟨k, hk, _⟩ := pow_eight_eq_cube h.symm
    exact ⟨k, hk⟩

lemma eight_mul_pow_twelve_le {a : ℕ} : 8 * a ^ 12 ≤ 27 * a ^ 16 := by
  cases a with
  | zero => simp
  | succ a =>
      have h16 : (a + 1) ^ 16 = (a + 1) ^ 4 * (a + 1) ^ 12 := pow_add _ 4 12
      rw [h16]
      have : 8 ≤ 27 * (a + 1) ^ 4 := by
        have : 1 ≤ (a + 1) ^ 4 := Nat.one_le_pow 4 (a + 1) (Nat.succ_pos _)
        nlinarith
      simpa [mul_left_comm, mul_assoc] using Nat.mul_le_mul_right ((a + 1) ^ 12) this

lemma three_mul_sq_ge_two_pow_four {n a : ℕ} (h : a ^ 8 ≤ n ^ 3) :
    2 * a ^ 4 ≤ 3 * n ^ 2 := by
  have hn6 : a ^ 16 ≤ n ^ 6 := by
    have := Nat.pow_le_pow_left h 2
    simpa [← pow_mul] using this
  have hcmp : (2 * a ^ 4) ^ 3 ≤ (3 * n ^ 2) ^ 3 := by
    have hL : (2 * a ^ 4) ^ 3 = 8 * a ^ 12 := by ring
    have hR : (3 * n ^ 2) ^ 3 = 27 * n ^ 6 := by ring
    rw [hL, hR]
    exact le_trans eight_mul_pow_twelve_le (Nat.mul_le_mul_left 27 hn6)
  exact (Nat.pow_le_pow_iff_left (by decide : (3 : ℕ) ≠ 0)).mp hcmp

lemma cube_gap_covers_fourth_window {n a : ℕ} (h : a ^ 8 ≤ n ^ 3) :
    2 * a ^ 4 + 1 ≤ 3 * n ^ 2 + 3 * n + 1 := by
  have hsq := three_mul_sq_ge_two_pow_four h
  have : 2 * a ^ 4 ≤ 3 * n * (n + 1) := by
    calc
      2 * a ^ 4 ≤ 3 * n ^ 2 := hsq
      _ ≤ 3 * n ^ 2 + 3 * n := Nat.le_add_right _ _
      _ = 3 * n * (n + 1) := by ring
  omega

theorem fourth_window_occupancy {a n k : ℕ}
    (hn : a ^ 8 ≤ n ^ 3 ∧ n ^ 3 < (a ^ 4 + 1) ^ 2)
    (hk : a ^ 8 ≤ k ^ 3 ∧ k ^ 3 < (a ^ 4 + 1) ^ 2) :
    n = k := by
  wlog hlt : n ≤ k
  · exact (this hk hn (le_of_not_ge hlt)).symm
  apply le_antisymm hlt
  by_contra hne
  have hsucc : n + 1 ≤ k := by omega
  have hgap := cube_gap_covers_fourth_window hn.1
  have hnext : (n + 1) ^ 3 ≤ k ^ 3 := Nat.pow_le_pow_left hsucc 3
  have hspan := fourth_window_span a
  have hlt' : (n + 1) ^ 3 < a ^ 8 + 2 * a ^ 4 + 1 := by
    calc
      (n + 1) ^ 3 ≤ k ^ 3 := hnext
      _ < (a ^ 4 + 1) ^ 2 := hk.2
      _ = a ^ 8 + 2 * a ^ 4 + 1 := hspan
  have hge : a ^ 8 + (3 * n ^ 2 + 3 * n + 1) ≤ (n + 1) ^ 3 := by
    rw [succ_cube_sub_cube]
    exact Nat.add_le_add_right hn.1 _
  have : a ^ 8 + (2 * a ^ 4 + 1) ≤ (n + 1) ^ 3 :=
    le_trans (Nat.add_le_add_left hgap _) hge
  omega

theorem eighth_pow_mem_fourth_window (k : ℕ) :
    (k ^ 3) ^ 8 ≤ (k ^ 8) ^ 3 ∧ (k ^ 8) ^ 3 < ((k ^ 3) ^ 4 + 1) ^ 2 := by
  constructor
  · have : (k ^ 3) ^ 8 = (k ^ 8) ^ 3 := by ring
    exact this.le
  · have hspan := fourth_window_span (k ^ 3)
    have heq : (k ^ 8) ^ 3 = (k ^ 3) ^ 8 := by ring
    rw [heq, hspan]
    exact Nat.lt_add_of_pos_right (Nat.succ_pos _)

theorem exact_cube_left_endpoint {k n : ℕ}
    (h : (k ^ 3) ^ 8 ≤ n ^ 3 ∧ n ^ 3 < ((k ^ 3) ^ 4 + 1) ^ 2) :
    n = k ^ 8 :=
  fourth_window_occupancy h (eighth_pow_mem_fourth_window k)

theorem fourth_window_cube_eq_succ_cbrt {a n : ℕ}
    (hnot : Nat.nthRoot 3 (a ^ 8) ^ 3 ≠ a ^ 8)
    (h : a ^ 8 ≤ n ^ 3 ∧ n ^ 3 < (a ^ 4 + 1) ^ 2) :
    n = Nat.nthRoot 3 (a ^ 8) + 1 := by
  set m := Nat.nthRoot 3 (a ^ 8)
  have hm : m ^ 3 ≤ a ^ 8 ∧ a ^ 8 < (m + 1) ^ 3 := (nat_cbrt_eq_iff).1 rfl
  have hlt : m ^ 3 < a ^ 8 := lt_of_le_of_ne hm.1 hnot
  have hn_gt : m < n := by
    apply lt_of_not_ge
    intro hle
    have : n ^ 3 ≤ m ^ 3 := Nat.pow_le_pow_left hle 3
    exact (not_le_of_gt hlt) (le_trans h.1 this)
  have hge : m + 1 ≤ n := Nat.succ_le_of_lt hn_gt
  have hcube : a ^ 8 ≤ (m + 1) ^ 3 ∧ (m + 1) ^ 3 < (a ^ 4 + 1) ^ 2 := by
    refine ⟨le_of_lt hm.2, lt_of_le_of_lt (Nat.pow_le_pow_left hge 3) h.2⟩
  exact fourth_window_occupancy h hcube

theorem noncube_odd_cbrt_fourth_window_cube_even {a n : ℕ}
    (hnot : Nat.nthRoot 3 (a ^ 8) ^ 3 ≠ a ^ 8)
    (hodd : Nat.nthRoot 3 (a ^ 8) % 2 = 1)
    (h : a ^ 8 ≤ n ^ 3 ∧ n ^ 3 < (a ^ 4 + 1) ^ 2) :
    n % 2 = 0 := by
  have hn := fourth_window_cube_eq_succ_cbrt hnot h
  have : (Nat.nthRoot 3 (a ^ 8) + 1) % 2 = 0 := by omega
  simpa [hn] using this

theorem odd_cube_interval_of_odd_cbrt_implies_square {n a : ℕ}
    (hodd : n % 2 = 1)
    (hcbrt : Nat.nthRoot 3 (a ^ 8) % 2 = 1)
    (h : a ^ 8 ≤ n ^ 3 ∧ n ^ 3 < (a ^ 4 + 1) ^ 2) :
    n.sqrt ^ 2 = n := by
  by_cases hcube : Nat.nthRoot 3 (a ^ 8) ^ 3 = a ^ 8
  · obtain ⟨k, ha, _⟩ := pow_eight_eq_cube hcube.symm
    subst ha
    have := exact_cube_left_endpoint h
    subst this
    have hpow : (k ^ 4) ^ 2 = k ^ 8 := by rw [← pow_mul]
    have hroot : (k ^ 8).sqrt = k ^ 4 := by
      rw [← hpow]
      exact Nat.sqrt_eq' _
    rw [hroot, hpow]
  · have heven := noncube_odd_cbrt_fourth_window_cube_even hcube hcbrt h
    omega

theorem floorPower_odd_eq_fourth_power_of_odd_cbrt_implies_square
    {n a : ℕ} (hodd : n % 2 = 1)
    (hcbrt : Nat.nthRoot 3 (a ^ 8) % 2 = 1)
    (hT : floorPower n = a ^ 4) :
    n.sqrt ^ 2 = n := by
  have hI := (floorPower_odd_eq_iff_cube_interval hodd).mp hT
  have hsq : (a ^ 4) ^ 2 = a ^ 8 := by ring
  exact odd_cube_interval_of_odd_cbrt_implies_square hodd hcbrt
    ⟨hsq ▸ hI.1, hI.2⟩

theorem odd_nonsquare_not_fourth_power_of_odd_cbrt {n a : ℕ}
    (hodd : n % 2 = 1) (hsq : n.sqrt ^ 2 ≠ n)
    (hcbrt : Nat.nthRoot 3 (a ^ 8) % 2 = 1) :
    floorPower n ≠ a ^ 4 := by
  intro hT
  exact hsq (floorPower_odd_eq_fourth_power_of_odd_cbrt_implies_square
    hodd hcbrt hT)

/-- Every `2^s`-th power with `s ≥ 2` is a fourth power. -/
theorem pow_two_depth_ge_two_is_fourth {a s : ℕ} (hs : 2 ≤ s) :
    a ^ (2 ^ s) = (a ^ (2 ^ (s - 2))) ^ 4 := by
  have hsplit : 2 ^ s = 2 ^ (s - 2) * 4 := by
    calc
      2 ^ s = 2 ^ (s - 2 + 2) := by rw [Nat.sub_add_cancel hs]
      _ = 2 ^ (s - 2) * 2 ^ 2 := pow_add _ _ _
      _ = 2 ^ (s - 2) * 4 := by rfl
  rw [hsplit, pow_mul]

theorem odd_first_defect_not_fourth_power_of_odd_cbrt
    {n a : ℕ} (hodd : n % 2 = 1)
    (hδ : floorPower n ^ 2 < n ^ 3)
    (hcbrt : Nat.nthRoot 3 (a ^ 8) % 2 = 1) :
    floorPower n ≠ a ^ 4 := by
  have hsq : n.sqrt ^ 2 ≠ n := by
    intro h
    have heq : floorPower n ^ 2 = n ^ 3 :=
      (floorPower_odd_sq_eq_cube_iff_square hodd).mpr h
    exact (lt_irrefl _) (heq ▸ hδ)
  exact odd_nonsquare_not_fourth_power_of_odd_cbrt hodd hsq hcbrt

/-- Restricted Phase-G corollary: an odd first defect cannot have a
sharp exact-even suffix of length `≥ 2` when the fourth-power base has
odd cube root of `a^8`. The even-cube-root case is open. -/
theorem odd_first_defect_not_pow_two_depth_ge_two_of_odd_cbrt
    {n a s : ℕ} (hodd : n % 2 = 1)
    (hδ : floorPower n ^ 2 < n ^ 3)
    (hs : 2 ≤ s)
    (hcbrt : Nat.nthRoot 3 ((a ^ (2 ^ (s - 2))) ^ 8) % 2 = 1) :
    floorPower n ≠ a ^ (2 ^ s) := by
  intro hT
  have hfourth : floorPower n = (a ^ (2 ^ (s - 2))) ^ 4 := by
    rw [hT, pow_two_depth_ge_two_is_fourth hs]
  exact odd_first_defect_not_fourth_power_of_odd_cbrt hodd hδ hcbrt hfourth


def itineraryEOO : List Branch := [.even, .odd, .odd]
def itineraryOOE : List Branch := [.odd, .odd, .even]
def itineraryOEO : List Branch := [.odd, .even, .odd]

theorem follows_itineraryEOO_iff {n : ℕ} :
    follows n itineraryEOO ↔
      n % 2 = 0 ∧
        floorPower n % 2 = 1 ∧
          floorPower (floorPower n) % 2 = 1 := by
  simp [follows, itineraryEOO]

theorem follows_itineraryOOE_iff {n : ℕ} :
    follows n itineraryOOE ↔
      n % 2 = 1 ∧
        floorPower n % 2 = 1 ∧
          floorPower (floorPower n) % 2 = 0 := by
  simp [follows, itineraryOOE]

theorem follows_itineraryOEO_iff {n : ℕ} :
    follows n itineraryOEO ↔
      n % 2 = 1 ∧
        floorPower n % 2 = 0 ∧
          floorPower (floorPower n) % 2 = 1 := by
  simp [follows, itineraryOEO]

theorem oddCount_itineraryEOO : oddCount itineraryEOO = 2 := by simp [itineraryEOO]
theorem oddCount_itineraryOOE : oddCount itineraryOOE = 2 := by simp [itineraryOOE]
theorem oddCount_itineraryOEO : oddCount itineraryOEO = 2 := by simp [itineraryOEO]
theorem length_itineraryEOO : itineraryEOO.length = 3 := by simp [itineraryEOO]
theorem length_itineraryOOE : itineraryOOE.length = 3 := by simp [itineraryOOE]
theorem length_itineraryOEO : itineraryOEO.length = 3 := by simp [itineraryOEO]

theorem follows_eoo_two : follows 2 itineraryEOO := by
  rw [follows_itineraryEOO_iff]; native_decide

theorem follows_eoo_twelve : follows 12 itineraryEOO := by
  rw [follows_itineraryEOO_iff]; native_decide

theorem follows_eoo_fourteen : follows 14 itineraryEOO := by
  rw [follows_itineraryEOO_iff]; native_decide

theorem floorPower_eoo_two_contracts : floorPower^[3] 2 < 2 := by
  native_decide

theorem floorPower_eoo_twelve_contracts : floorPower^[3] 12 < 12 := by
  native_decide

theorem floorPower_eoo_fourteen_contracts : floorPower^[3] 14 < 14 := by
  native_decide

theorem floorPower_eoo_two_eq : floorPower^[3] 2 = 1 := by
  native_decide

theorem floorPower_eoo_twelve_eq : floorPower^[3] 12 = 11 := by
  native_decide

theorem floorPower_eoo_fourteen_eq : floorPower^[3] 14 = 11 := by
  native_decide

theorem n_lt_formal_gap_three_two {n : ℕ} (hn : 2 ≤ n) :
    n < n ^ 9 - n ^ 8 := by
  have hfact : n ^ 9 - n ^ 8 = n ^ 8 * (n - 1) := by
    rw [pow_succ, Nat.mul_sub_left_distrib, mul_one]
  rw [hfact]
  cases eq_or_lt_of_le hn with
  | inl h2 =>
      subst h2
      native_decide
  | inr hlt =>
      have hn3 : 3 ≤ n := Nat.succ_le_of_lt hlt
      have hself : n ≤ n ^ 8 := Nat.le_self_pow (by decide : 8 ≠ 0) n
      have hmul : n * (n - 1) ≤ n ^ 8 * (n - 1) :=
        Nat.mul_le_mul_right (n - 1) hself
      have hn0 : 0 < n := lt_of_lt_of_le (by decide : 0 < 3) hn3
      have hpred : 1 < n - 1 := by omega
      have hstrict : n * 1 < n * (n - 1) :=
        Nat.mul_lt_mul_of_pos_left hpred hn0
      exact lt_of_lt_of_le (by simpa using hstrict) hmul

theorem localDefectEven_lt_formal_gap_three_two {n : ℕ} (hn : 2 ≤ n) :
    localDefectEven n < n ^ 9 - n ^ 8 :=
  lt_of_le_of_lt (Nat.sub_le _ _) (n_lt_formal_gap_three_two hn)

theorem eoo_first_defect_lt_formal_gap {n : ℕ} (hn : 2 ≤ n)
    (_hw : follows n itineraryEOO) :
    localDefectEven n < n ^ (3 ^ oddCount itineraryEOO) - n ^ (2 ^ itineraryEOO.length) := by
  simpa [oddCount_itineraryEOO, length_itineraryEOO] using
    localDefectEven_lt_formal_gap_three_two hn

theorem floorPower_eoo_two_deficit_gt_gap :
    2 ^ (3 ^ 2) - 2 ^ (2 ^ 3) <
      powerDeficit (floorPower^[3] 2) 2 3 2 := by
  native_decide

theorem floorPower_eoo_of_follows {n : ℕ} (hw : follows n itineraryEOO) :
    floorPower^[3] n = (((n.sqrt ^ 3).sqrt ^ 3).sqrt) := by
  have heven : n % 2 = 0 := (follows_itineraryEOO_iff.mp hw).1
  have hodd1 : floorPower n % 2 = 1 := (follows_itineraryEOO_iff.mp hw).2.1
  have h1 : floorPower n = n.sqrt := floorPower_even_eq heven
  have h2 : floorPower (floorPower n) = (n.sqrt ^ 3).sqrt := by
    rw [h1, floorPower_odd_eq (by simpa [h1] using hodd1)]
  have hodd2 : floorPower (floorPower n) % 2 = 1 :=
    (follows_itineraryEOO_iff.mp hw).2.2
  have h3 : floorPower (floorPower (floorPower n)) =
      ((n.sqrt ^ 3).sqrt ^ 3).sqrt := by
    rw [h2, floorPower_odd_eq (by simpa [h2] using hodd2)]
  simpa [Function.iterate_succ_apply] using h3

theorem eoo_sqrt_odd {n : ℕ} (hw : follows n itineraryEOO) :
    n.sqrt % 2 = 1 := by
  have h := (follows_itineraryEOO_iff.mp hw).2.1
  simpa [floorPower_even_eq (follows_itineraryEOO_iff.mp hw).1] using h

theorem eoo_n_ge_two {n : ℕ} (hw : follows n itineraryEOO) : 2 ≤ n := by
  have heven : n % 2 = 0 := (follows_itineraryEOO_iff.mp hw).1
  have hn0 : n ≠ 0 := by
    intro h
    subst h
    simp [follows, itineraryEOO, floorPower] at hw
  omega

theorem eoo_sqrt_cube_pow_of_small {q : ℕ} (hlo : 5 ≤ q) (hhi : q ≤ 24) :
    ((q ^ 3).sqrt) ^ 3 ≥ (q + 1) ^ 4 := by
  interval_cases q <;> first | omega | native_decide

theorem succ_pow_eight_le_five_mul {s : ℕ} (hs : 5 ≤ s) :
    (s + 1) ^ 8 ≤ 5 * s ^ 8 := by
  have h56 : 5 * (s + 1) ≤ 6 * s := by omega
  have hpow : (5 * (s + 1)) ^ 8 ≤ (6 * s) ^ 8 :=
    Nat.pow_le_pow_left h56 8
  have hmul : 5 ^ 8 * (s + 1) ^ 8 ≤ 6 ^ 8 * s ^ 8 := by
    simpa [mul_pow] using hpow
  have h69 : (6 : ℕ) ^ 8 ≤ 5 ^ 9 := by native_decide
  have hR : 6 ^ 8 * s ^ 8 ≤ 5 ^ 9 * s ^ 8 :=
    Nat.mul_le_mul_right (s ^ 8) h69
  have hchain : 5 ^ 8 * (s + 1) ^ 8 ≤ 5 ^ 9 * s ^ 8 := le_trans hmul hR
  have hrew : 5 ^ 9 * s ^ 8 = 5 ^ 8 * (5 * s ^ 8) := by
    rw [pow_succ']
    ring
  rw [hrew] at hchain
  exact Nat.le_of_mul_le_mul_left hchain (pow_pos (by decide : 0 < 5) 8)

theorem succ_pow_eight_le_pow_nine {s : ℕ} (hs : 5 ≤ s) :
    (s + 1) ^ 8 ≤ s ^ 9 := by
  have h5 := succ_pow_eight_le_five_mul hs
  have hmul : 5 * s ^ 8 ≤ s * s ^ 8 := Nat.mul_le_mul_right (s ^ 8) hs
  have hrew : s * s ^ 8 = s ^ 9 := by
    calc
      s * s ^ 8 = s ^ 8 * s := mul_comm _ _
      _ = s ^ 9 := (pow_succ s 8).symm
  exact le_trans h5 (hrew ▸ hmul)

theorem eoo_qs_le_cbrt {q : ℕ} : q * q.sqrt ≤ (q ^ 3).sqrt := by
  refine Nat.le_sqrt.mpr ?_
  have hs : q.sqrt * q.sqrt ≤ q := Nat.sqrt_le q
  have hleft : (q * q.sqrt) * (q * q.sqrt) = (q * q) * (q.sqrt * q.sqrt) := by
    ring
  have hmid : (q * q) * (q.sqrt * q.sqrt) ≤ (q * q) * q :=
    Nat.mul_le_mul_left (q * q) hs
  have : (q * q.sqrt) * (q * q.sqrt) ≤ q * q * q := by
    simpa [hleft] using hmid
  have : q * q * q = q ^ 3 := by simp [pow_three, mul_assoc]
  simpa [this] using ‹(q * q.sqrt) * (q * q.sqrt) ≤ q * q * q›

theorem eoo_qs_cube_ge_of_ge_twenty_five {q : ℕ} (hq : 25 ≤ q) :
    (q * q.sqrt) ^ 3 ≥ (q + 1) ^ 4 := by
  set s := q.sqrt
  have hs : 5 ≤ s := Nat.le_sqrt.mpr (show 5 * 5 ≤ q from hq)
  have hsq : s * s ≤ q := Nat.sqrt_le q
  have hup : q + 1 ≤ (s + 1) * (s + 1) :=
    Nat.succ_le_of_lt (Nat.lt_succ_sqrt q)
  have hqs : s * s * s ≤ q * s := Nat.mul_le_mul_right s hsq
  have hleft : (s * s * s) ^ 3 ≤ (q * s) ^ 3 := Nat.pow_le_pow_left hqs 3
  have hright : (q + 1) ^ 4 ≤ ((s + 1) * (s + 1)) ^ 4 :=
    Nat.pow_le_pow_left hup 4
  have hs3 : s * s * s = s ^ 3 := by
    simp [pow_three, mul_assoc]
  have hs9 : (s * s * s) ^ 3 = s ^ 9 := by
    rw [hs3]
    calc
      (s ^ 3) ^ 3 = s ^ (3 * 3) := (Nat.pow_mul s 3 3).symm
      _ = s ^ 9 := by norm_num
  have h8 : ((s + 1) * (s + 1)) ^ 4 = (s + 1) ^ 8 := by
    have hexp : (s + 1) * (s + 1) = (s + 1) ^ 2 := (pow_two (s + 1)).symm
    rw [hexp]
    calc
      ((s + 1) ^ 2) ^ 4 = (s + 1) ^ (2 * 4) := (Nat.pow_mul (s + 1) 2 4).symm
      _ = (s + 1) ^ 8 := by norm_num
  have hcmp : (s + 1) ^ 8 ≤ s ^ 9 := succ_pow_eight_le_pow_nine hs
  have hmid : ((s + 1) * (s + 1)) ^ 4 ≤ (s * s * s) ^ 3 := by
    simpa [h8, hs9] using hcmp
  exact le_trans hright (le_trans hmid hleft)

theorem eoo_sqrt_cube_pow_ge {q : ℕ} (hq : 5 ≤ q) :
    ((q ^ 3).sqrt) ^ 3 ≥ (q + 1) ^ 4 := by
  cases lt_or_ge q 25 with
  | inl hlt =>
      have : q ≤ 24 := Nat.lt_succ_iff.mp hlt
      exact eoo_sqrt_cube_pow_of_small hq this
  | inr hge =>
      exact le_trans (eoo_qs_cube_ge_of_ge_twenty_five hge)
        (Nat.pow_le_pow_left eoo_qs_le_cbrt 3)

theorem eoo_image_ge_succ_sq {n : ℕ} (hw : follows n itineraryEOO)
    (hq : 5 ≤ n.sqrt) :
    (n.sqrt + 1) ^ 2 ≤ floorPower^[3] n := by
  have himg := floorPower_eoo_of_follows hw
  have hpow := eoo_sqrt_cube_pow_ge hq
  have hle : (n.sqrt + 1) ^ 2 ≤ ((n.sqrt ^ 3).sqrt ^ 3).sqrt := by
    refine Nat.le_sqrt.mpr ?_
    have hexp : (n.sqrt + 1) ^ 2 * (n.sqrt + 1) ^ 2 = (n.sqrt + 1) ^ 4 := by
      ring
    simpa [hexp] using hpow
  simpa [himg] using hle

theorem eoo_expands_of_sqrt_ge_five {n : ℕ} (hw : follows n itineraryEOO)
    (hq : 5 ≤ n.sqrt) :
    n < floorPower^[3] n := by
  have hsucc : n < (n.sqrt + 1) * (n.sqrt + 1) := Nat.lt_succ_sqrt n
  have hsq : (n.sqrt + 1) * (n.sqrt + 1) = (n.sqrt + 1) ^ 2 := by
    simp [pow_two]
  have : n < (n.sqrt + 1) ^ 2 := by simpa [hsq] using hsucc
  exact lt_of_lt_of_le this (eoo_image_ge_succ_sq hw hq)

theorem eoo_sqrt_cases {n : ℕ} (hw : follows n itineraryEOO) :
    n.sqrt = 1 ∨ n.sqrt = 3 ∨ 5 ≤ n.sqrt := by
  have hodd : n.sqrt % 2 = 1 := eoo_sqrt_odd hw
  have hn : 2 ≤ n := eoo_n_ge_two hw
  have hpos : 1 ≤ n.sqrt := Nat.le_sqrt.mpr (by
    have : 1 ≤ n := le_trans (by decide : 1 ≤ 2) hn
    simpa using this)
  cases lt_or_ge n.sqrt 5 with
  | inr h5 => exact Or.inr (Or.inr h5)
  | inl hlt =>
      have : n.sqrt = 1 ∨ n.sqrt = 3 := by
        interval_cases n.sqrt <;> omega
      exact this.imp_right Or.inl

theorem eoo_eq_two_of_sqrt_one {n : ℕ} (hw : follows n itineraryEOO)
    (h1 : n.sqrt = 1) : n = 2 := by
  have heven : n % 2 = 0 := (follows_itineraryEOO_iff.mp hw).1
  have hge : 1 ≤ n := by
    have : 1 * 1 ≤ n := by simpa [h1] using Nat.sqrt_le n
    omega
  have hlt : n < 4 := by
    have : n < (n.sqrt + 1) * (n.sqrt + 1) := Nat.lt_succ_sqrt n
    simpa [h1] using this
  interval_cases n <;> omega

theorem eoo_of_sqrt_three {n : ℕ} (hw : follows n itineraryEOO)
    (h3 : n.sqrt = 3) : n = 10 ∨ n = 12 ∨ n = 14 := by
  have heven : n % 2 = 0 := (follows_itineraryEOO_iff.mp hw).1
  have hge : 9 ≤ n := by simpa [h3] using Nat.sqrt_le n
  have hlt : n < 16 := by
    have : n < (n.sqrt + 1) * (n.sqrt + 1) := Nat.lt_succ_sqrt n
    simpa [h3] using this
  interval_cases n <;> omega

theorem floorPower_eoo_image_of_sqrt_three {n : ℕ} (hw : follows n itineraryEOO)
    (h3 : n.sqrt = 3) : floorPower^[3] n = 11 := by
  have himg := floorPower_eoo_of_follows hw
  have : ((((3 : ℕ) ^ 3).sqrt) ^ 3).sqrt = 11 := by native_decide
  simpa [himg, h3] using this

/-- `EOO` contracts if and only if `n ∈ {2, 12, 14}`. Not a halt theorem. -/
theorem floorPower_eoo_contracts_iff {n : ℕ} (hw : follows n itineraryEOO) :
    floorPower^[3] n < n ↔ n = 2 ∨ n = 12 ∨ n = 14 := by
  constructor
  · intro hlt
    rcases eoo_sqrt_cases hw with h1 | h3 | h5
    · exact Or.inl (eoo_eq_two_of_sqrt_one hw h1)
    · have hmem := eoo_of_sqrt_three hw h3
      have himg : floorPower^[3] n = 11 :=
        floorPower_eoo_image_of_sqrt_three hw h3
      rcases hmem with rfl | rfl | rfl
      · simp [himg] at hlt
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr rfl)
    · exact (lt_asymm hlt (eoo_expands_of_sqrt_ge_five hw h5)).elim
  · rintro (rfl | rfl | rfl)
    · exact floorPower_eoo_two_contracts
    · exact floorPower_eoo_twelve_contracts
    · exact floorPower_eoo_fourteen_contracts

/-!
## EOO square-root cells

The first even step freezes the remaining `OO` computation on the
square-root cell `[q^2, (q+1)^2)`. Contraction is the threshold
`n > eooCellOutput q`. This explains the enumerated set `{2, 12, 14}`
and is not a halt theorem.
-/

theorem sqrt_cell_iff {n q : ℕ} :
    n.sqrt = q ↔ q ^ 2 ≤ n ∧ n < (q + 1) ^ 2 :=
  floor_sqrt_eq_iff_sq_interval

def eooCellOutput (q : ℕ) : ℕ := (((q ^ 3).sqrt) ^ 3).sqrt

theorem follows_eoo_sqrt_iff {n : ℕ} :
    follows n itineraryEOO ↔
      n % 2 = 0 ∧ n.sqrt % 2 = 1 ∧ (n.sqrt ^ 3).sqrt % 2 = 1 := by
  constructor
  · intro hw
    have h := follows_itineraryEOO_iff.mp hw
    refine ⟨h.1, eoo_sqrt_odd hw, ?_⟩
    have h1 : floorPower n = n.sqrt := floorPower_even_eq h.1
    have h2 : floorPower (floorPower n) = (n.sqrt ^ 3).sqrt := by
      rw [h1, floorPower_odd_eq (by simpa [h1] using h.2.1)]
    simpa [h2] using h.2.2
  · intro ⟨heven, hoddq, hoddb⟩
    refine follows_itineraryEOO_iff.mpr ⟨heven, ?_, ?_⟩
    · simpa [floorPower_even_eq heven] using hoddq
    · have h1 : floorPower n = n.sqrt := floorPower_even_eq heven
      have h2 : floorPower (floorPower n) = (n.sqrt ^ 3).sqrt := by
        rw [h1, floorPower_odd_eq (by simpa [h1] using hoddq)]
      simpa [h2] using hoddb

theorem eoo_output_eq_cell {n : ℕ} (hw : follows n itineraryEOO) :
    floorPower^[3] n = eooCellOutput n.sqrt :=
  floorPower_eoo_of_follows hw

theorem eoo_output_constant_on_sqrt_cell {n m : ℕ}
    (hn : follows n itineraryEOO) (hm : follows m itineraryEOO)
    (hq : n.sqrt = m.sqrt) :
    floorPower^[3] n = floorPower^[3] m := by
  rw [eoo_output_eq_cell hn, eoo_output_eq_cell hm, hq]

/-- On a realized `EOO` start, contraction is the cell threshold
`n > eooCellOutput ⌊√n⌋`. -/
theorem eoo_contracts_on_cell {n : ℕ} (hw : follows n itineraryEOO) :
    floorPower^[3] n < n ↔ eooCellOutput n.sqrt < n := by
  simp [eoo_output_eq_cell hw]

theorem eoo_cell_output_one : eooCellOutput 1 = 1 := by
  native_decide

theorem eoo_cell_output_three : eooCellOutput 3 = 11 := by
  native_decide

theorem eoo_cell_output_ge_succ_sq {q : ℕ} (hq : 5 ≤ q) :
    (q + 1) ^ 2 ≤ eooCellOutput q := by
  have hpow := eoo_sqrt_cube_pow_ge hq
  refine Nat.le_sqrt.mpr ?_
  have hexp : (q + 1) ^ 2 * (q + 1) ^ 2 = (q + 1) ^ 4 := by ring
  simpa [eooCellOutput, hexp] using hpow

theorem eoo_residue {n : ℕ} (hw : follows n itineraryEOO) :
    localDefectEven n = n - n.sqrt ^ 2 :=
  localDefectEven_eq (follows_itineraryEOO_iff.mp hw).1

/-!
## Primitive one-step preimages and the first-even freeze

Even and odd branches have exact one-step preimages. The first even
letter freezes every suffix on the square-root one-step preimage. Odd
one-step preimages contain at most one integer, so an initial odd letter
does not freeze a useful range. This is not a halt theorem and not a
preimage-tree calculus.
-/

theorem even_preimage_iff {n q : ℕ} (heven : n % 2 = 0) :
    floorPower n = q ↔ q ^ 2 ≤ n ∧ n < (q + 1) ^ 2 :=
  floorPower_even_eq_iff_sq_interval heven

theorem odd_preimage_iff {n m : ℕ} (hodd : n % 2 = 1) :
    floorPower n = m ↔ m ^ 2 ≤ n ^ 3 ∧ n ^ 3 < (m + 1) ^ 2 :=
  floorPower_odd_eq_iff_cube_interval hodd

theorem preimage_same_next_state {n q : ℕ} (heven : n % 2 = 0)
    (hcell : q ^ 2 ≤ n ∧ n < (q + 1) ^ 2) :
    floorPower n = q :=
  (even_preimage_iff heven).mpr hcell

theorem iterate_cons_even {n k : ℕ} (heven : n % 2 = 0) :
    floorPower^[k + 1] n = floorPower^[k] n.sqrt := by
  rw [iterate_cons, floorPower_even_eq heven]

theorem iterate_cons_odd {n k : ℕ} (hodd : n % 2 = 1) :
    floorPower^[k + 1] n = floorPower^[k] (n ^ 3).sqrt := by
  rw [iterate_cons, floorPower_odd_eq hodd]

/-- On a realized first-even itinerary, the suffix is evaluated at `⌊√n⌋`. -/
theorem first_even_freeze {n : ℕ} {v : List Branch}
    (hw : follows n (.even :: v)) :
    floorPower^[v.length + 1] n = floorPower^[v.length] n.sqrt :=
  iterate_cons_even hw.1

theorem first_odd_freeze {n : ℕ} {v : List Branch}
    (hw : follows n (.odd :: v)) :
    floorPower^[v.length + 1] n = floorPower^[v.length] (n ^ 3).sqrt :=
  iterate_cons_odd hw.1

theorem suffix_same_output_on_cell {n₁ n₂ : ℕ} {v : List Branch}
    (h1 : follows n₁ (.even :: v)) (h2 : follows n₂ (.even :: v))
    (hq : n₁.sqrt = n₂.sqrt) :
    floorPower^[v.length + 1] n₁ = floorPower^[v.length + 1] n₂ := by
  rw [first_even_freeze h1, first_even_freeze h2, hq]

/-- First-even contraction is the cell threshold `T_v(⌊√n⌋) < n`. -/
theorem first_even_contracts_iff {n : ℕ} {v : List Branch}
    (hw : follows n (.even :: v)) :
    floorPower^[v.length + 1] n < n ↔
      floorPower^[v.length] n.sqrt < n := by
  simp [first_even_freeze hw]

theorem eoo_from_first_even {n : ℕ} (hw : follows n itineraryEOO) :
    floorPower^[3] n < n ↔ floorPower^[2] n.sqrt < n :=
  first_even_contracts_iff (v := [.odd, .odd]) (by simpa [itineraryEOO] using hw)

theorem constant_cell_trichotomy {c lo hi : ℕ} (_h : lo < hi) :
    c < lo ∨ hi ≤ c ∨ (lo ≤ c ∧ c < hi) := by
  omega

theorem constant_cell_all_contract {c lo n : ℕ}
    (hc : c < lo) (hn : lo ≤ n) : c < n :=
  lt_of_lt_of_le hc hn

theorem constant_cell_all_expand {c hi n : ℕ}
    (hc : hi ≤ c) (hn : n < hi) : ¬c < n :=
  fun h => (lt_asymm h) (lt_of_lt_of_le hn hc)

theorem cube_succ_diff (n : ℕ) :
    (n + 1) ^ 3 - n ^ 3 = 3 * n ^ 2 + 3 * n + 1 := by
  have h : (n + 1) ^ 3 = n ^ 3 + (3 * n ^ 2 + 3 * n + 1) := by ring
  omega

theorem sq_succ_diff (m : ℕ) :
    (m + 1) ^ 2 - m ^ 2 = 2 * m + 1 := by
  have h : (m + 1) ^ 2 = m ^ 2 + 2 * m + 1 := by ring
  omega

/-- An odd one-step preimage `{n : m^2 ≤ n^3 < (m+1)^2}` has at most one point. -/
theorem odd_preimage_unique {m a b : ℕ}
    (ha : m ^ 2 ≤ a ^ 3 ∧ a ^ 3 < (m + 1) ^ 2)
    (hb : m ^ 2 ≤ b ^ 3 ∧ b ^ 3 < (m + 1) ^ 2) :
    a = b := by
  wlog hle : a ≤ b generalizing a b
  · exact (this hb ha (le_of_not_ge hle)).symm
  refine eq_of_le_of_not_lt hle fun hlt => ?_
  have hsucc : a + 1 ≤ b := Nat.succ_le_of_lt hlt
  have hcube : (a + 1) ^ 3 ≤ b ^ 3 := Nat.pow_le_pow_left hsucc 3
  have hlt2 : (a + 1) ^ 3 < (m + 1) ^ 2 := lt_of_le_of_lt hcube hb.2
  have hge : m ^ 2 ≤ a ^ 3 := ha.1
  have hgap : (a + 1) ^ 3 - a ^ 3 < (m + 1) ^ 2 - m ^ 2 := by
    have h1 : (a + 1) ^ 3 - a ^ 3 ≤ (a + 1) ^ 3 - m ^ 2 :=
      Nat.sub_le_sub_left hge _
    have h2 : (a + 1) ^ 3 - m ^ 2 < (m + 1) ^ 2 - m ^ 2 :=
      Nat.sub_lt_sub_right
        (le_trans hge (Nat.pow_le_pow_left (Nat.le_succ a) 3)) hlt2
    exact lt_of_le_of_lt h1 h2
  have hlin : 3 * a ^ 2 + 3 * a + 1 < 2 * m + 1 := by
    simpa [cube_succ_diff a, sq_succ_diff m] using hgap
  have h2m : 3 * a ^ 2 + 3 * a + 1 ≤ 2 * m := by omega
  cases Nat.eq_zero_or_pos a with
  | inl ha0 =>
      subst ha0
      have hm0 : m = 0 := Nat.eq_zero_of_le_zero (by simpa using hge)
      subst hm0
      exact (lt_irrefl (1 : ℕ)) hlin
  | inr hap =>
      have hsq : 3 * a ^ 2 ≤ 2 * m :=
        le_trans (Nat.le_add_right _ _) (le_trans (Nat.le_add_right _ _) h2m)
      have h4 : (3 * a ^ 2) ^ 2 ≤ (2 * m) ^ 2 := Nat.pow_le_pow_left hsq 2
      have h9 : 9 * a ^ 4 ≤ 4 * m ^ 2 := by
        simpa [pow_two, pow_succ, pow_zero, mul_assoc, mul_left_comm, mul_comm] using h4
      have hstrict : 4 * a ^ 3 < 9 * a ^ 4 := by
        have hmul : 4 < 9 * a := by omega
        have hpos : 0 < a ^ 3 := pow_pos hap 3
        simpa [mul_assoc, pow_succ, pow_zero] using
          Nat.mul_lt_mul_of_pos_right hmul hpos
      have : 4 * a ^ 3 < 4 * m ^ 2 := lt_of_lt_of_le hstrict h9
      have habs : a ^ 3 < m ^ 2 := (Nat.mul_lt_mul_left (by decide : 0 < 4)).mp this
      exact (lt_irrefl _) (lt_of_lt_of_le habs hge)

/-!
## First-even cell thresholds

On a square-root cell the contracting inputs are the integers
`n ∈ [q^2, (q+1)^2) ∩ (c, ∞)`. Any contraction requires
`c + 1 < (q+1)^2`; the whole cell contracts iff `c < q^2`.
The one-sided power envelope does not prove these lower bounds.
This is not a halt theorem.
-/

theorem sq_lt_succ_sq (q : ℕ) : q ^ 2 < (q + 1) ^ 2 := by
  have h : (q + 1) ^ 2 = q ^ 2 + 2 * q + 1 := by ring
  omega

theorem cell_any_contracts_iff {c lo hi : ℕ} :
    (∃ n, lo ≤ n ∧ n < hi ∧ c < n) ↔ lo < hi ∧ c + 1 < hi := by
  constructor
  · rintro ⟨n, hlo, hhi, hc⟩
    exact ⟨lt_of_le_of_lt hlo hhi, lt_of_le_of_lt (Nat.succ_le_of_lt hc) hhi⟩
  · intro ⟨hcell, hc⟩
    refine ⟨max lo (c + 1), Nat.le_max_left _ _, ?_, ?_⟩
    · exact max_lt_iff.mpr ⟨hcell, hc⟩
    · exact Nat.lt_of_succ_le (Nat.le_max_right _ _)

theorem cell_all_contracts_iff {c lo hi : ℕ} :
    (∀ n, lo ≤ n → n < hi → c < n) ↔ hi ≤ lo ∨ c < lo := by
  constructor
  · intro h
    cases Nat.lt_or_ge lo hi with
    | inl hlt => exact Or.inr (h lo le_rfl hlt)
    | inr hle => exact Or.inl hle
  · rintro (hle | hc) n hlo hhi
    · exact (not_lt_of_ge (le_trans hle hlo) hhi).elim
    · exact lt_of_lt_of_le hc hlo

theorem first_even_any_contracts_iff {c q : ℕ} :
    (∃ n, q ^ 2 ≤ n ∧ n < (q + 1) ^ 2 ∧ c < n) ↔ c + 1 < (q + 1) ^ 2 := by
  constructor
  · intro h
    exact (cell_any_contracts_iff.mp h).2
  · intro h
    exact cell_any_contracts_iff.mpr ⟨sq_lt_succ_sq q, h⟩

theorem first_even_all_contracts_iff {c q : ℕ} :
    (∀ n, q ^ 2 ≤ n → n < (q + 1) ^ 2 → c < n) ↔ c < q ^ 2 := by
  have h := cell_all_contracts_iff (c := c) (lo := q ^ 2) (hi := (q + 1) ^ 2)
  have hne : ¬(q + 1) ^ 2 ≤ q ^ 2 := not_le_of_gt (sq_lt_succ_sq q)
  simp [h, hne]

theorem floorPower_odd_ge {n : ℕ} (hodd : n % 2 = 1) :
    n ≤ floorPower n := by
  rw [floorPower_odd_eq hodd]
  refine Nat.le_sqrt.mpr ?_
  have hn : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr (fun h => by
    subst h
    simp at hodd)
  have : n * n ≤ n * n * n :=
    Nat.le_mul_of_pos_right (n * n) hn
  simpa [pow_two, pow_three, mul_assoc] using this

theorem eooCellOutput_eq_iterate {q : ℕ}
    (hw : follows q [.odd, .odd]) :
    eooCellOutput q = floorPower^[2] q := by
  have hodd : q % 2 = 1 := hw.1
  have h1 : floorPower q = (q ^ 3).sqrt := floorPower_odd_eq hodd
  have hodd2 : floorPower q % 2 = 1 := hw.2.1
  have h2 : floorPower (floorPower q) = ((q ^ 3).sqrt ^ 3).sqrt := by
    rw [h1, floorPower_odd_eq (by simpa [h1] using hodd2)]
  simpa [eooCellOutput, Function.iterate_succ_apply, h1] using h2.symm

/-- For the suffix `OO`, every `q ≥ 5` that realizes the itinerary sits at or
above the next square. So `Q_{OO}` is finite. -/
theorem oo_suffix_threshold {q : ℕ} (hq : 5 ≤ q)
    (hw : follows q [.odd, .odd]) :
    (q + 1) ^ 2 ≤ floorPower^[2] q := by
  simpa [eooCellOutput_eq_iterate hw] using eoo_cell_output_ge_succ_sq hq

theorem follows_oo_of_ooo {q : ℕ}
    (hw : follows q [.odd, .odd, .odd]) :
    follows q [.odd, .odd] :=
  ⟨hw.1, hw.2.1, trivial⟩

theorem ooo_three : floorPower^[3] 3 = 36 := by
  native_decide

/-- For the suffix `OOO`, every `q ≥ 3` that realizes the itinerary sits at or
above the next square. So `Q_{OOO}` is finite. -/
theorem ooo_suffix_threshold {q : ℕ} (hq : 3 ≤ q)
    (hw : follows q [.odd, .odd, .odd]) :
    (q + 1) ^ 2 ≤ floorPower^[3] q := by
  cases lt_or_ge q 5 with
  | inl hlt =>
      have hq3 : q = 3 := by
        have hodd : q % 2 = 1 := hw.1
        omega
      subst hq3
      rw [ooo_three]
      omega
  | inr h5 =>
      have hoo := follows_oo_of_ooo hw
      have h2 := oo_suffix_threshold h5 hoo
      have hodd2 : floorPower^[2] q % 2 = 1 := by
        simpa [Function.iterate_succ_apply] using hw.2.2.1
      have hge : floorPower^[2] q ≤ floorPower^[3] q := by
        simpa [Function.iterate_succ_apply] using floorPower_odd_ge hodd2
      exact le_trans h2 hge

/-- An odd state at or above `(n+1)^2` has odd-step image at least
`(n+1)^3`. This is the exact one-odd lift of a next-square residual,
not an asymptotic. -/
theorem odd_ge_succ_sq_floorPower_ge_cube {z n : ℕ}
    (hodd : z % 2 = 1) (hz : (n + 1) ^ 2 ≤ z) :
    (n + 1) ^ 3 ≤ floorPower z := by
  rw [floorPower_odd_eq hodd]
  refine Nat.le_sqrt.mpr ?_
  have hpow : ((n + 1) ^ 2) ^ 3 ≤ z ^ 3 := Nat.pow_le_pow_left hz 3
  have hexp : ((n + 1) ^ 3) ^ 2 = ((n + 1) ^ 2) ^ 3 := by
    simp [← Nat.pow_mul]
  have : ((n + 1) ^ 3) ^ 2 ≤ z ^ 3 := by
    rwa [hexp]
  simpa [pow_two] using this

/-- On `OOO` at `q ≥ 5` the residual is at least `(q+1)^3`, not merely
the next-square bound inherited by `ooo_suffix_threshold`. -/
theorem ooo_residual_ge_cube {q : ℕ} (hq : 5 ≤ q)
    (hw : follows q [.odd, .odd, .odd]) :
    (q + 1) ^ 3 ≤ floorPower^[3] q := by
  have hoo := follows_oo_of_ooo hw
  have h2 := oo_suffix_threshold hq hoo
  have hodd2 : floorPower^[2] q % 2 = 1 := by
    simpa [Function.iterate_succ_apply] using hw.2.2.1
  have hcube := odd_ge_succ_sq_floorPower_ge_cube hodd2 h2
  simpa [Function.iterate_succ_apply] using hcube

/-!
## Coarse lower growth

The one-sided envelope is an upper bound and cannot prove eventual
non-contraction. For `n ≥ 1` the elementary comparison
`n < 4 · n.sqrt^2` gives a multiplicative lower bound on each branch.
These compose along a fixed itinerary to
`q^{3^o} ≤ D_v · T_v(q)^{2^r}`. If `3^o > 2^{r+1}`, the exponent gap
beats `(q+1)^2` for all sufficiently large `q`. The threshold depends
on `v`. This is not a halt theorem and not a lower-envelope theory.
-/

/-- Weak lower bound `n^{3^o} ≤ D · m^{2^k}`. Separate from `PowerBound`. -/
def LowerPowerBound (m n k o D : ℕ) : Prop :=
  n ^ (3 ^ o) ≤ D * m ^ (2 ^ k)

def lowerDenomFrom (k o D : ℕ) : List Branch → ℕ
  | [] => D
  | .even :: w => lowerDenomFrom (k + 1) o (D * 4 ^ (2 ^ k)) w
  | .odd :: w => lowerDenomFrom (k + 1) (o + 1) (D ^ 3 * 4 ^ (2 ^ k)) w

def lowerDenom (w : List Branch) : ℕ := lowerDenomFrom 0 0 1 w

theorem three_pow_odd (o : ℕ) : 3 ^ o % 2 = 1 := by
  induction o with
  | zero => simp
  | succ o ih =>
      simp [pow_succ, Nat.mul_mod, ih]

theorem two_pow_even_of_pos {k : ℕ} (hk : 1 ≤ k) : 2 ^ k % 2 = 0 := by
  cases k with
  | zero => omega
  | succ k => simp [pow_succ]

/-- No finite itinerary has formal exponent exactly `2`. -/
theorem alpha_ne_two (v : List Branch) :
    3 ^ oddCount v ≠ 2 ^ (v.length + 1) := by
  intro h
  have hodd : 3 ^ oddCount v % 2 = 1 := three_pow_odd _
  have heven : 2 ^ (v.length + 1) % 2 = 0 :=
    two_pow_even_of_pos (Nat.succ_le_succ (Nat.zero_le _))
  rw [h] at hodd
  omega

theorem four_mul_sqrt_sq_gt {n : ℕ} (hn : 1 ≤ n) :
    n < 4 * n.sqrt ^ 2 := by
  have hs : 1 ≤ n.sqrt := Nat.le_sqrt.mpr (by simpa [pow_two] using hn)
  have hsucc : n < (n.sqrt + 1) ^ 2 := by
    simpa [pow_two, Nat.succ_eq_add_one] using Nat.lt_succ_sqrt n
  have h2 : n.sqrt + 1 ≤ 2 * n.sqrt := by omega
  have hsq : (n.sqrt + 1) ^ 2 ≤ (2 * n.sqrt) ^ 2 :=
    Nat.pow_le_pow_left h2 2
  have : n < (2 * n.sqrt) ^ 2 := lt_of_lt_of_le hsucc hsq
  have hexp : (2 * n.sqrt) ^ 2 = 4 * n.sqrt ^ 2 := by ring
  simpa [hexp] using this

theorem four_mul_floorPower_even_sq {n : ℕ} (heven : n % 2 = 0)
    (hn : 1 ≤ n) : n ≤ 4 * floorPower n ^ 2 := by
  rw [floorPower_even_eq heven]
  exact Nat.le_of_lt (four_mul_sqrt_sq_gt hn)

theorem four_mul_floorPower_odd_sq {n : ℕ} (hodd : n % 2 = 1)
    (hn : 1 ≤ n) : n ^ 3 ≤ 4 * floorPower n ^ 2 := by
  rw [floorPower_odd_eq hodd]
  have h3 : 1 ≤ n ^ 3 :=
    Nat.succ_le_of_lt (pow_pos (lt_of_lt_of_le (by decide : 0 < 1) hn) 3)
  exact Nat.le_of_lt (four_mul_sqrt_sq_gt h3)

theorem lower_power_empty (n : ℕ) : LowerPowerBound n n 0 0 1 := by
  simp [LowerPowerBound]

theorem lower_power_append_even {m n k o D : ℕ}
    (h : LowerPowerBound m n k o D) (heven : m % 2 = 0) (hm : 1 ≤ m) :
    LowerPowerBound (floorPower m) n (k + 1) o (D * 4 ^ (2 ^ k)) := by
  have h4 := four_mul_floorPower_even_sq heven hm
  unfold LowerPowerBound at *
  have hpow : m ^ (2 ^ k) ≤ (4 * floorPower m ^ 2) ^ (2 ^ k) :=
    Nat.pow_le_pow_left h4 _
  have hle : n ^ (3 ^ o) ≤ D * (4 * floorPower m ^ 2) ^ (2 ^ k) :=
    le_trans h (Nat.mul_le_mul_left D hpow)
  have hexp : (4 * floorPower m ^ 2) ^ (2 ^ k) =
      4 ^ (2 ^ k) * (floorPower m ^ 2) ^ (2 ^ k) := mul_pow 4 _ _
  have hT : (floorPower m ^ 2) ^ (2 ^ k) = floorPower m ^ (2 * 2 ^ k) :=
    (Nat.pow_mul (floorPower m) 2 (2 ^ k)).symm
  calc
    n ^ (3 ^ o)
        ≤ D * (4 * floorPower m ^ 2) ^ (2 ^ k) := hle
    _ = D * (4 ^ (2 ^ k) * (floorPower m ^ 2) ^ (2 ^ k)) := by rw [hexp]
    _ = D * 4 ^ (2 ^ k) * floorPower m ^ (2 * 2 ^ k) := by
        rw [hT, mul_assoc]
    _ = (D * 4 ^ (2 ^ k)) * floorPower m ^ (2 ^ (k + 1)) := by
        rw [two_pow_succ, mul_assoc]

theorem lower_power_append_odd {m n k o D : ℕ}
    (h : LowerPowerBound m n k o D) (hodd : m % 2 = 1) (hm : 1 ≤ m) :
    LowerPowerBound (floorPower m) n (k + 1) (o + 1)
      (D ^ 3 * 4 ^ (2 ^ k)) := by
  have h4 := four_mul_floorPower_odd_sq hodd hm
  unfold LowerPowerBound at *
  have hcube : n ^ (3 ^ (o + 1)) = (n ^ (3 ^ o)) ^ 3 :=
    (pow_three_succ_right n o).symm
  have hD : (n ^ (3 ^ o)) ^ 3 ≤ (D * m ^ (2 ^ k)) ^ 3 :=
    Nat.pow_le_pow_left h 3
  have hexpD : (D * m ^ (2 ^ k)) ^ 3 = D ^ 3 * (m ^ (2 ^ k)) ^ 3 :=
    mul_pow D _ 3
  have h4pow : (m ^ 3) ^ (2 ^ k) ≤ (4 * floorPower m ^ 2) ^ (2 ^ k) :=
    Nat.pow_le_pow_left h4 _
  have hm3 : (m ^ (2 ^ k)) ^ 3 = (m ^ 3) ^ (2 ^ k) := by
    rw [← Nat.pow_mul, ← Nat.pow_mul, mul_comm]
  have hexp : (4 * floorPower m ^ 2) ^ (2 ^ k) =
      4 ^ (2 ^ k) * (floorPower m ^ 2) ^ (2 ^ k) := mul_pow 4 _ _
  have hT : (floorPower m ^ 2) ^ (2 ^ k) = floorPower m ^ (2 * 2 ^ k) :=
    (Nat.pow_mul (floorPower m) 2 (2 ^ k)).symm
  calc
    n ^ (3 ^ (o + 1))
        = (n ^ (3 ^ o)) ^ 3 := hcube
    _ ≤ (D * m ^ (2 ^ k)) ^ 3 := hD
    _ = D ^ 3 * (m ^ (2 ^ k)) ^ 3 := hexpD
    _ = D ^ 3 * (m ^ 3) ^ (2 ^ k) := by rw [hm3]
    _ ≤ D ^ 3 * (4 * floorPower m ^ 2) ^ (2 ^ k) :=
        Nat.mul_le_mul_left _ h4pow
    _ = D ^ 3 * (4 ^ (2 ^ k) * (floorPower m ^ 2) ^ (2 ^ k)) := by rw [hexp]
    _ = D ^ 3 * 4 ^ (2 ^ k) * floorPower m ^ (2 * 2 ^ k) := by
        rw [hT, mul_assoc]
    _ = (D ^ 3 * 4 ^ (2 ^ k)) * floorPower m ^ (2 ^ (k + 1)) := by
        rw [two_pow_succ, mul_assoc]

theorem lower_power_from {start current k o D : ℕ}
    (h : LowerPowerBound current start k o D) (hpos : 1 ≤ current) :
    ∀ v, follows current v →
      LowerPowerBound (image current v) start (k + v.length)
        (o + oddCount v) (lowerDenomFrom k o D v) := by
  intro v
  induction v generalizing current k o D with
  | nil =>
      intro _
      simpa [image, lowerDenomFrom] using h
  | cons b w ih =>
      intro hw
      cases b with
      | even =>
          have heven : current % 2 = 0 := hw.1
          have hrest : follows (floorPower current) w := hw.2
          have hnext := lower_power_append_even h heven hpos
          have hpos' : 1 ≤ floorPower current := floorPower_pos hpos
          have hih := ih hnext hpos' hrest
          simpa [image, lowerDenomFrom, List.length_cons, Nat.add_comm,
            Nat.add_left_comm, Nat.add_assoc] using hih
      | odd =>
          have hodd : current % 2 = 1 := hw.1
          have hrest : follows (floorPower current) w := hw.2
          have hnext := lower_power_append_odd h hodd hpos
          have hpos' : 1 ≤ floorPower current := floorPower_pos hpos
          have hih := ih hnext hpos' hrest
          simpa [image, lowerDenomFrom, List.length_cons, oddCount,
            Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hih

theorem lower_growth_word {q : ℕ} {v : List Branch}
    (hq : 1 ≤ q) (hw : follows q v) :
    LowerPowerBound (image q v) q v.length (oddCount v) (lowerDenom v) := by
  simpa [lowerDenom] using lower_power_from (lower_power_empty q) hq v hw

theorem succ_sq_le_four_sq {q : ℕ} (hq : 1 ≤ q) :
    (q + 1) ^ 2 ≤ 4 * q ^ 2 := by
  cases q with
  | zero => omega
  | succ t =>
      have : (t + 2) ^ 2 ≤ 4 * (t + 1) ^ 2 := by
        have hL : (t + 2) ^ 2 = t ^ 2 + 4 * t + 4 := by ring
        have hR : 4 * (t + 1) ^ 2 = 4 * t ^ 2 + 8 * t + 4 := by ring
        have : t ^ 2 + 4 * t + 4 ≤ 4 * t ^ 2 + 8 * t + 4 := by
          exact Nat.add_le_add (Nat.add_le_add (Nat.le_mul_of_pos_left (t ^ 2) (by decide : 1 ≤ 4))
            (Nat.mul_le_mul_right t (by decide : 4 ≤ 8))) le_rfl
        simpa [hL, hR] using this
      simpa [Nat.succ_eq_add_one] using this

theorem superquadratic_gap {v : List Branch}
    (hα : 2 ^ (v.length + 1) < 3 ^ oddCount v) :
    1 ≤ 3 ^ oddCount v - 2 ^ (v.length + 1) :=
  Nat.succ_le_of_lt (Nat.sub_pos_of_lt hα)

theorem lowerDenomFrom_pos (k o D : ℕ) (hD : 1 ≤ D) :
    ∀ w, 1 ≤ lowerDenomFrom k o D w := by
  intro w
  induction w generalizing k o D with
  | nil => simpa [lowerDenomFrom] using hD
  | cons b w ih =>
      cases b with
      | even =>
          have h4 : 1 ≤ (4 : ℕ) ^ (2 ^ k) :=
            Nat.succ_le_of_lt (pow_pos (by decide : 0 < 4) _)
          have hD' : 1 ≤ D * 4 ^ (2 ^ k) := by
            simpa using Nat.mul_le_mul hD h4
          exact ih (k + 1) o _ hD'
      | odd =>
          have h3 : 1 ≤ D ^ 3 := Nat.succ_le_of_lt (pow_pos (lt_of_lt_of_le (by decide : 0 < 1) hD) 3)
          have h4 : 1 ≤ (4 : ℕ) ^ (2 ^ k) :=
            Nat.succ_le_of_lt (pow_pos (by decide : 0 < 4) _)
          have hD' : 1 ≤ D ^ 3 * 4 ^ (2 ^ k) := by
            simpa using Nat.mul_le_mul h3 h4
          exact ih (k + 1) (o + 1) _ hD'

theorem lowerDenom_pos (w : List Branch) : 1 ≤ lowerDenom w :=
  lowerDenomFrom_pos 0 0 1 (by decide) w

theorem pow_le_pow_left_cancel {a b k : ℕ} (hk : 1 ≤ k)
    (h : a ^ k ≤ b ^ k) : a ≤ b := by
  refine le_of_not_gt fun hlt => ?_
  have hlt' : b ^ k < a ^ k :=
    Nat.pow_lt_pow_left hlt (Nat.one_le_iff_ne_zero.mp hk)
  exact (not_le_of_gt hlt') h

/-- Every fixed superquadratic suffix is eventually above the next square.
The threshold `Q0` depends on `v`. -/
theorem eventually_no_first_even_contraction {v : List Branch}
    (hα : 2 ^ (v.length + 1) < 3 ^ oddCount v) :
    ∃ Q0, ∀ q, Q0 ≤ q → follows q v → (q + 1) ^ 2 ≤ image q v := by
  set D := lowerDenom v
  set r := v.length
  set Q0 := D * 4 ^ (2 ^ r)
  refine ⟨Q0, fun q hq hw => ?_⟩
  have hD : 1 ≤ D := lowerDenom_pos v
  have h4p : 1 ≤ (4 : ℕ) ^ (2 ^ r) :=
    Nat.succ_le_of_lt (pow_pos (by decide : 0 < 4) _)
  have hQpos : 1 ≤ Q0 := by
    simpa [Q0] using Nat.mul_le_mul hD h4p
  have hq1 : 1 ≤ q := le_trans hQpos hq
  have hL : LowerPowerBound (image q v) q r (oddCount v) D := by
    simpa [D, r] using lower_growth_word hq1 hw
  have hgap : 1 ≤ 3 ^ oddCount v - 2 ^ (r + 1) := superquadratic_gap (by simpa [r] using hα)
  have hqg : q ≤ q ^ (3 ^ oddCount v - 2 ^ (r + 1)) :=
    le_trans (by simp : q ≤ q ^ 1)
      (Nat.pow_le_pow_right hq1 hgap)
  have hleft : Q0 * q ^ (2 ^ (r + 1)) ≤ q ^ (3 ^ oddCount v) := by
    have hmul : Q0 * q ^ (2 ^ (r + 1)) ≤
        q ^ (3 ^ oddCount v - 2 ^ (r + 1)) * q ^ (2 ^ (r + 1)) :=
      Nat.mul_le_mul_right _ (le_trans hq hqg)
    have hadd : q ^ (3 ^ oddCount v - 2 ^ (r + 1)) * q ^ (2 ^ (r + 1)) =
        q ^ (3 ^ oddCount v) := by
      rw [← Nat.pow_add, Nat.sub_add_cancel (Nat.le_of_lt (by simpa [r] using hα))]
    simpa [hadd] using hmul
  have hsucc : (q + 1) ^ (2 ^ (r + 1)) ≤ 4 ^ (2 ^ r) * q ^ (2 ^ (r + 1)) := by
    have hsq := succ_sq_le_four_sq hq1
    have hpow : ((q + 1) ^ 2) ^ (2 ^ r) ≤ (4 * q ^ 2) ^ (2 ^ r) :=
      Nat.pow_le_pow_left hsq _
    have hLexp : ((q + 1) ^ 2) ^ (2 ^ r) = (q + 1) ^ (2 ^ (r + 1)) := by
      rw [← Nat.pow_mul, two_pow_succ, mul_comm]
    have hRexp : (4 * q ^ 2) ^ (2 ^ r) = 4 ^ (2 ^ r) * q ^ (2 ^ (r + 1)) := by
      rw [mul_pow, ← Nat.pow_mul, two_pow_succ, mul_comm]
    simpa [hLexp, hRexp] using hpow
  have hDsucc : D * (q + 1) ^ (2 ^ (r + 1)) ≤ q ^ (3 ^ oddCount v) :=
    calc
      D * (q + 1) ^ (2 ^ (r + 1))
          ≤ D * (4 ^ (2 ^ r) * q ^ (2 ^ (r + 1))) :=
            Nat.mul_le_mul_left D hsucc
      _ = Q0 * q ^ (2 ^ (r + 1)) := by
            simp [Q0, mul_assoc]
      _ ≤ q ^ (3 ^ oddCount v) := hleft
  have hT : (q + 1) ^ (2 ^ (r + 1)) ≤ image q v ^ (2 ^ r) := by
    have hbound : q ^ (3 ^ oddCount v) ≤ D * image q v ^ (2 ^ r) := hL
    have : D * (q + 1) ^ (2 ^ (r + 1)) ≤ D * image q v ^ (2 ^ r) :=
      le_trans hDsucc hbound
    exact Nat.le_of_mul_le_mul_left this (lt_of_lt_of_le (by decide : 0 < 1) hD)
  have hT' : ((q + 1) ^ 2) ^ (2 ^ r) ≤ image q v ^ (2 ^ r) := by
    have hexp : (q + 1) ^ (2 ^ (r + 1)) = ((q + 1) ^ 2) ^ (2 ^ r) := by
      rw [← Nat.pow_mul, two_pow_succ, mul_comm]
    simpa [hexp] using hT
  exact pow_le_pow_left_cancel
    (Nat.succ_le_of_lt (pow_pos (by decide : 0 < 2) r)) hT'

theorem oo_lower_growth_eventual :
    ∃ Q0, ∀ q, Q0 ≤ q → follows q [.odd, .odd] →
      (q + 1) ^ 2 ≤ image q [.odd, .odd] :=
  eventually_no_first_even_contraction
    (by native_decide : 2 ^ (([.odd, .odd] : List Branch).length + 1) <
      3 ^ oddCount [.odd, .odd])

end Problems.Juggler
