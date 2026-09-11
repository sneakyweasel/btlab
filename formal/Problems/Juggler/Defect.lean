import Problems.Juggler.ItineraryStats
import Problems.Juggler.Equality

namespace Problems.Juggler

/-!
# Envelope defect and compensated contraction

Composite envelope defect. This is not the refuted local claim
`T(n)^2 < n^3` for every odd `n`, and not a termination theorem.
`StrictPowerBound` is the strict companion of `PowerBound`.
-/

def localDefectEven (x : ℕ) : ℕ := x - floorPower x ^ 2

/-- What one odd step loses to the floor, as `x³ - J(x)²`. Summing these around
a cycle is the finance identity. -/
def localDefectOdd (x : ℕ) : ℕ := x ^ 3 - floorPower x ^ 2

def StrictPowerBound (m n k o : ℕ) : Prop := m ^ (2 ^ k) < n ^ (3 ^ o)

def isMonochrome (w : List Branch) : Prop :=
  w = List.replicate w.length Branch.even ∨
    w = List.replicate w.length Branch.odd

theorem localDefectEven_eq {x : ℕ} (heven : x % 2 = 0) :
    localDefectEven x = x - x.sqrt ^ 2 := by
  simp [localDefectEven, floorPower, heven]

theorem localDefectOdd_eq {x : ℕ} (hodd : x % 2 = 1) :
    localDefectOdd x = x ^ 3 - (x ^ 3).sqrt ^ 2 := by
  simp [localDefectOdd, floorPower_odd_eq hodd]

theorem localDefectEven_add {x : ℕ} (heven : x % 2 = 0) :
    floorPower x ^ 2 + localDefectEven x = x :=
  Nat.add_sub_of_le (floorPower_even_sq_le heven)

theorem localDefectOdd_add {x : ℕ} (hodd : x % 2 = 1) :
    floorPower x ^ 2 + localDefectOdd x = x ^ 3 :=
  Nat.add_sub_of_le (floorPower_odd_sq_le_cube hodd)

theorem localDefectEven_eq_zero_iff {x : ℕ} (heven : x % 2 = 0) :
    localDefectEven x = 0 ↔ x.sqrt ^ 2 = x := by
  rw [localDefectEven_eq heven, Nat.sub_eq_zero_iff_le]
  constructor
  · intro h
    exact le_antisymm (by simpa [pow_two] using Nat.sqrt_le x) h
  · intro h
    exact h.ge

theorem localDefectOdd_eq_zero_iff {x : ℕ} (hodd : x % 2 = 1) :
    localDefectOdd x = 0 ↔ x.sqrt ^ 2 = x := by
  constructor
  · intro h
    have hadd := localDefectOdd_add hodd
    rw [h, Nat.add_zero] at hadd
    exact (floorPower_odd_sq_eq_cube_iff_square hodd).mp hadd
  · intro hsq
    have : floorPower x ^ 2 = x ^ 3 :=
      (floorPower_odd_sq_eq_cube_iff_square hodd).mpr hsq
    simp [localDefectOdd, this]

theorem localDefectEven_lt_succ_sqrt {x : ℕ} (heven : x % 2 = 0) :
    localDefectEven x < 2 * x.sqrt + 1 := by
  rw [localDefectEven_eq heven]
  have hle : x.sqrt * x.sqrt ≤ x := Nat.sqrt_le x
  have hlt : x < (x.sqrt + 1) * (x.sqrt + 1) := by
    simpa [Nat.succ_eq_add_one] using Nat.lt_succ_sqrt x
  have hbin : (x.sqrt + 1) * (x.sqrt + 1) = x.sqrt ^ 2 + 2 * x.sqrt + 1 := by ring
  have hsq : x.sqrt ^ 2 = x.sqrt * x.sqrt := pow_two _
  omega

/-- Same bound in the successor `T(x)`, not `√x`. -/
theorem localDefectEven_lt_succ {x : ℕ} (heven : x % 2 = 0) :
    localDefectEven x < 2 * floorPower x + 1 := by
  simpa [floorPower_even_eq heven] using localDefectEven_lt_succ_sqrt heven

/-- Odd remainder sits in the same successor window `0 ≤ ρ < 2T(x)+1`. -/
theorem localDefectOdd_lt_succ {x : ℕ} (hodd : x % 2 = 1) :
    localDefectOdd x < 2 * floorPower x + 1 := by
  rw [localDefectOdd_eq hodd, floorPower_odd_eq hodd]
  have hle : (x ^ 3).sqrt * (x ^ 3).sqrt ≤ x ^ 3 := Nat.sqrt_le (x ^ 3)
  have hlt : x ^ 3 < ((x ^ 3).sqrt + 1) * ((x ^ 3).sqrt + 1) := by
    simpa [Nat.succ_eq_add_one] using Nat.lt_succ_sqrt (x ^ 3)
  have hbin : ((x ^ 3).sqrt + 1) * ((x ^ 3).sqrt + 1) =
      (x ^ 3).sqrt ^ 2 + 2 * (x ^ 3).sqrt + 1 := by ring
  have hsq : (x ^ 3).sqrt ^ 2 = (x ^ 3).sqrt * (x ^ 3).sqrt := pow_two _
  omega

/-- Local floor remainder of a realized letter. The envelope drops this. -/
def branchDefect : Branch → ℕ → ℕ
  | .even, x => localDefectEven x
  | .odd, x => localDefectOdd x

theorem branchDefect_add {x : ℕ} {b : Branch} (h : follows x [b]) :
    x ^ branchExp b = floorPower x ^ 2 + branchDefect b x := by
  cases b with
  | even =>
      simpa [branchExp, branchDefect, pow_one] using
        (localDefectEven_add h.1).symm
  | odd =>
      simpa [branchExp, branchDefect] using (localDefectOdd_add h.1).symm

theorem branchDefect_lt {x : ℕ} {b : Branch} (h : follows x [b]) :
    branchDefect b x < 2 * floorPower x + 1 := by
  cases b with
  | even =>
      simpa [branchDefect] using localDefectEven_lt_succ h.1
  | odd =>
      simpa [branchDefect] using localDefectOdd_lt_succ h.1

theorem branchDefect_eq_zero_iff_localTight {x : ℕ} {b : Branch}
    (h : follows x [b]) :
    branchDefect b x = 0 ↔ localTight x b := by
  cases b with
  | even =>
      constructor
      · intro hz
        have hadd := localDefectEven_add h.1
        have hz' : localDefectEven x = 0 := by
          simpa [branchDefect] using hz
        rw [hz', Nat.add_zero] at hadd
        simpa [localTight] using hadd
      · intro ht
        have : floorPower x ^ 2 = x := by simpa [localTight] using ht
        simp [branchDefect, localDefectEven, this]
  | odd =>
      constructor
      · intro hz
        have hadd := localDefectOdd_add h.1
        have hz' : localDefectOdd x = 0 := by
          simpa [branchDefect] using hz
        rw [hz', Nat.add_zero] at hadd
        simpa [localTight] using hadd
      · intro ht
        have : floorPower x ^ 2 = x ^ 3 := by simpa [localTight] using ht
        simp [branchDefect, localDefectOdd, this]

/-- Dropping a nonnegative remainder recovers the local envelope step. -/
theorem power_bound_of_branchDefect {x : ℕ} {b : Branch} (h : follows x [b]) :
    floorPower x ^ 2 ≤ x ^ branchExp b := by
  have hadd := branchDefect_add h
  exact Nat.le.intro (hadd.symm)

theorem pow_sq_lt {a b e : ℕ} (h : a ^ 2 < b) (he : e ≠ 0) :
    a ^ (2 * e) < b ^ e := by
  have : (a ^ 2) ^ e < b ^ e := Nat.pow_lt_pow_left h he
  rwa [← Nat.pow_mul] at this

theorem pow_add_pow_le_add_pow {b d e : ℕ} (he : 1 ≤ e) :
    b ^ e + d ^ e ≤ (b + d) ^ e := by
  cases e with
  | zero => exact (Nat.not_succ_le_zero 0 he).elim
  | succ e =>
      have hb : b ^ e ≤ (b + d) ^ e := Nat.pow_le_pow_left (Nat.le_add_right b d) _
      have hd : d ^ e ≤ (b + d) ^ e := Nat.pow_le_pow_left (Nat.le_add_left d b) _
      calc
        b ^ (e + 1) + d ^ (e + 1)
          = b * b ^ e + d * d ^ e := by
            rw [pow_succ, pow_succ, mul_comm (b ^ e), mul_comm (d ^ e)]
        _ ≤ b * (b + d) ^ e + d * (b + d) ^ e :=
            add_le_add (Nat.mul_le_mul_left b hb) (Nat.mul_le_mul_left d hd)
        _ = (b + d) * (b + d) ^ e := by ring
        _ = (b + d) ^ (e + 1) := by rw [pow_succ, mul_comm]

theorem pow_sub_pow_ge_sub {a b e : ℕ} (hba : b ≤ a) (he : 1 ≤ e) :
    a - b ≤ a ^ e - b ^ e := by
  set d := a - b
  have ha : b + d = a := Nat.add_sub_of_le hba
  have hsum : b ^ e + d ^ e ≤ a ^ e := by
    simpa [ha] using pow_add_pow_le_add_pow (b := b) (d := d) he
  have hd : d ≤ d ^ e := Nat.le_self_pow (Nat.pos_iff_ne_zero.mp he) d
  have : d ^ e ≤ a ^ e - b ^ e :=
    Nat.le_sub_of_add_le (add_comm (b ^ e) _ ▸ hsum)
  exact le_trans hd this

theorem strict_power_bound_append_even {m n k o : ℕ}
    (h : StrictPowerBound m n k o) (heven : m % 2 = 0) :
    StrictPowerBound (floorPower m) n (k + 1) o := by
  have hsq : floorPower m ^ 2 ≤ m := floorPower_even_sq_le heven
  unfold StrictPowerBound at *
  have h2 : 2 ^ (k + 1) = 2 * 2 ^ k := two_pow_succ k
  rw [h2]
  exact lt_of_le_of_lt (pow_sq_le hsq) h

theorem strict_power_bound_append_odd {m n k o : ℕ}
    (h : StrictPowerBound m n k o) (hodd : m % 2 = 1) :
    StrictPowerBound (floorPower m) n (k + 1) (o + 1) := by
  have hsq : floorPower m ^ 2 ≤ m ^ 3 := floorPower_odd_sq_le_cube hodd
  unfold StrictPowerBound at *
  have h2 : 2 ^ (k + 1) = 2 * 2 ^ k := two_pow_succ k
  have hmid : m ^ (3 * 2 ^ k) = (m ^ (2 ^ k)) ^ 3 := by
    rw [mul_comm, Nat.pow_mul]
  have hle : floorPower m ^ (2 ^ (k + 1)) ≤ (m ^ (2 ^ k)) ^ 3 := by
    rw [h2]
    exact (pow_sq_le_cube hsq).trans_eq hmid
  have hlt : (m ^ (2 ^ k)) ^ 3 < (n ^ (3 ^ o)) ^ 3 :=
    Nat.pow_lt_pow_left h (by decide : (3 : ℕ) ≠ 0)
  have hright : (n ^ (3 ^ o)) ^ 3 = n ^ (3 ^ (o + 1)) := by
    calc
      (n ^ (3 ^ o)) ^ 3 = n ^ (3 ^ o * 3) := (Nat.pow_mul n (3 ^ o) 3).symm
      _ = n ^ (3 * 3 ^ o) := by rw [mul_comm]
      _ = n ^ (3 ^ (o + 1)) := by rw [← pow_succ']
  exact lt_of_le_of_lt hle (hlt.trans_eq hright)

theorem strict_power_bound_of_even_defect {m n k o : ℕ}
    (h : PowerBoundEq m n k o) (_heven : m % 2 = 0)
    (hδ : floorPower m ^ 2 < m) :
    StrictPowerBound (floorPower m) n (k + 1) o := by
  unfold StrictPowerBound PowerBoundEq at *
  have h2 : 2 ^ (k + 1) = 2 * 2 ^ k := two_pow_succ k
  rw [h2, Nat.pow_mul, ← h]
  exact Nat.pow_lt_pow_left hδ (pow_ne_zero_two_pow k)

theorem strict_power_bound_of_odd_defect {m n k o : ℕ}
    (h : PowerBoundEq m n k o) (_hodd : m % 2 = 1)
    (hδ : floorPower m ^ 2 < m ^ 3) :
    StrictPowerBound (floorPower m) n (k + 1) (o + 1) := by
  unfold StrictPowerBound PowerBoundEq at *
  have h2 : 2 ^ (k + 1) = 2 * 2 ^ k := two_pow_succ k
  rw [h2, Nat.pow_mul]
  have : (floorPower m ^ 2) ^ (2 ^ k) < (m ^ 3) ^ (2 ^ k) :=
    Nat.pow_lt_pow_left hδ (pow_ne_zero_two_pow k)
  have hmid : (m ^ 3) ^ (2 ^ k) = (m ^ (2 ^ k)) ^ 3 := by
    rw [← Nat.pow_mul, mul_comm, Nat.pow_mul]
  have hends : (m ^ (2 ^ k)) ^ 3 = n ^ (3 ^ (o + 1)) := by
    rw [h]
    calc
      (n ^ (3 ^ o)) ^ 3 = n ^ (3 ^ o * 3) := (Nat.pow_mul n (3 ^ o) 3).symm
      _ = n ^ (3 * 3 ^ o) := by rw [mul_comm]
      _ = n ^ (3 ^ (o + 1)) := by rw [← pow_succ']
  exact this.trans_eq (hmid.trans hends)

theorem even_defect_gap_ge_local {m n k o : ℕ}
    (h : PowerBoundEq m n k o) (_heven : m % 2 = 0)
    (hδ : floorPower m ^ 2 < m) :
    localDefectEven m ≤ n ^ (3 ^ o) - floorPower m ^ (2 ^ (k + 1)) := by
  have h2 : 2 ^ (k + 1) = 2 * 2 ^ k := two_pow_succ k
  have hle : floorPower m ^ 2 ≤ m := le_of_lt hδ
  have hgap : m - floorPower m ^ 2 ≤ m ^ (2 ^ k) - (floorPower m ^ 2) ^ (2 ^ k) :=
    pow_sub_pow_ge_sub hle (Nat.one_le_pow _ _ (by decide : 0 < 2))
  unfold PowerBoundEq at h
  simpa [localDefectEven, h, h2, Nat.pow_mul] using hgap

theorem odd_defect_gap_ge_local {m n k o : ℕ}
    (h : PowerBoundEq m n k o) (_hodd : m % 2 = 1)
    (hδ : floorPower m ^ 2 < m ^ 3) :
    localDefectOdd m ≤ n ^ (3 ^ (o + 1)) - floorPower m ^ (2 ^ (k + 1)) := by
  have h2 : 2 ^ (k + 1) = 2 * 2 ^ k := two_pow_succ k
  have h3 : 3 ^ (o + 1) = 3 * 3 ^ o := three_pow_succ o
  have hle : floorPower m ^ 2 ≤ m ^ 3 := le_of_lt hδ
  have hgap :
      (m ^ 3) ^ (2 ^ k) - (floorPower m ^ 2) ^ (2 ^ k) ≥ m ^ 3 - floorPower m ^ 2 :=
    pow_sub_pow_ge_sub hle (Nat.one_le_pow _ _ (by decide : 0 < 2))
  have hmid : (m ^ 3) ^ (2 ^ k) = n ^ (3 ^ (o + 1)) := by
    have : (m ^ 3) ^ (2 ^ k) = (m ^ (2 ^ k)) ^ 3 := by
      rw [← Nat.pow_mul, mul_comm, Nat.pow_mul]
    rw [this, h]
    calc
      (n ^ (3 ^ o)) ^ 3 = n ^ (3 ^ o * 3) := (Nat.pow_mul n (3 ^ o) 3).symm
      _ = n ^ (3 * 3 ^ o) := by rw [mul_comm]
      _ = n ^ (3 ^ (o + 1)) := by rw [← pow_succ']
  simpa [localDefectOdd, h2, Nat.pow_mul, hmid] using hgap

theorem strict_power_bound_from {start current k o : ℕ}
    (hbound : StrictPowerBound current start k o) :
    ∀ w, follows current w →
      StrictPowerBound (image current w) start (k + w.length)
        (o + oddCount w) := by
  intro w
  induction w generalizing current k o with
  | nil =>
      intro _
      simpa using hbound
  | cons b rest ih =>
      intro hw
      cases b with
      | even =>
          have heven : current % 2 = 0 := hw.1
          have hrest : follows (floorPower current) rest := hw.2
          have hih :=
            ih (current := floorPower current) (k := k + 1) (o := o)
              (strict_power_bound_append_even hbound heven) hrest
          have hk : k + (rest.length + 1) = k + 1 + rest.length := by omega
          simp [List.length_cons]
          rw [hk]
          exact hih
      | odd =>
          have hodd : current % 2 = 1 := hw.1
          have hrest : follows (floorPower current) rest := hw.2
          have hih :=
            ih (current := floorPower current) (k := k + 1) (o := o + 1)
              (strict_power_bound_append_odd hbound hodd) hrest
          have hk : k + (rest.length + 1) = k + 1 + rest.length := by omega
          have ho : o + (oddCount rest + 1) = o + 1 + oddCount rest := by omega
          simp [List.length_cons]
          rw [hk, ho]
          exact hih

theorem power_bound_word_strict {n : ℕ} {w : List Branch}
    (hw : follows n w) (hmix : ¬ isMonochrome w) :
    StrictPowerBound (floorPower^[w.length] n) n w.length (oddCount w) := by
  have hle : PowerBound (floorPower^[w.length] n) n w.length (oddCount w) :=
    power_bound_follows hw
  have hne : ¬ PowerBoundEq (floorPower^[w.length] n) n w.length (oddCount w) := by
    intro heq
    exact hmix (power_bound_eq_implies_monochrome hw heq)
  exact lt_of_le_of_ne hle hne

theorem strict_power_bound_of_not_extremal {n : ℕ} {w : List Branch}
    (hw : follows n w)
    (hnot :
      ¬ ((w = List.replicate w.length Branch.even ∧
            ∃ a, a % 2 = 0 ∧ n = a ^ (2 ^ w.length)) ∨
          (w = List.replicate w.length Branch.odd ∧
            ∃ a, a % 2 = 1 ∧ n = a ^ (2 ^ w.length)))) :
    StrictPowerBound (floorPower^[w.length] n) n w.length (oddCount w) := by
  have hle := power_bound_follows hw
  have hne : ¬ PowerBoundEq (floorPower^[w.length] n) n w.length (oddCount w) := by
    intro heq
    exact hnot (power_bound_eq_iff_extremal.mp ⟨hw, heq⟩)
  exact lt_of_le_of_ne hle hne

theorem power_bound_defect_ge_one {n : ℕ} {w : List Branch}
    (hw : follows n w) (hmix : ¬ isMonochrome w) :
    1 ≤ n ^ (3 ^ oddCount w) - (floorPower^[w.length] n) ^ (2 ^ w.length) := by
  have hlt := power_bound_word_strict hw hmix
  have hle : (floorPower^[w.length] n) ^ (2 ^ w.length) + 1 ≤
      n ^ (3 ^ oddCount w) := Nat.succ_le_of_lt hlt
  exact Nat.le_sub_of_add_le (add_comm _ 1 ▸ hle)

theorem not_localsTight_of_nonmonochrome {n : ℕ} {w : List Branch}
    (hw : follows n w) (hmix : ¬ isMonochrome w) :
    ¬ localsTight n w := by
  intro htight
  have heq := localsTight_implies_power_bound_eq w hw htight
  exact hmix (power_bound_eq_implies_monochrome hw heq)

/-- Numeric companion of `PowerBound`. Nonnegative once the weak bound holds. -/
def powerDeficit (m n k o : ℕ) : ℕ := n ^ (3 ^ o) - m ^ (2 ^ k)

theorem powerBound_of_eq {m n k o : ℕ} (h : PowerBoundEq m n k o) :
    PowerBound m n k o :=
  le_of_eq h

theorem power_bound_eq_empty (n : ℕ) : PowerBoundEq n n 0 0 := by
  simp [PowerBoundEq]

theorem power_deficit_append_even {m n k o : ℕ}
    (_h : PowerBound m n k o) (heven : m % 2 = 0) :
    powerDeficit m n k o ≤ powerDeficit (floorPower m) n (k + 1) o := by
  unfold powerDeficit
  have h2 : 2 ^ (k + 1) = 2 * 2 ^ k := two_pow_succ k
  have hle : floorPower m ^ (2 ^ (k + 1)) ≤ m ^ (2 ^ k) := by
    rw [h2]
    exact pow_sq_le (floorPower_even_sq_le heven)
  exact Nat.sub_le_sub_left hle _

theorem power_deficit_append_odd {m n k o : ℕ}
    (h : PowerBound m n k o) (hodd : m % 2 = 1) :
    powerDeficit m n k o ≤ powerDeficit (floorPower m) n (k + 1) (o + 1) := by
  unfold powerDeficit PowerBound at *
  have h2 : 2 ^ (k + 1) = 2 * 2 ^ k := two_pow_succ k
  have hsq : floorPower m ^ 2 ≤ m ^ 3 := floorPower_odd_sq_le_cube hodd
  have hmid : m ^ (3 * 2 ^ k) = (m ^ (2 ^ k)) ^ 3 := by
    rw [mul_comm, Nat.pow_mul]
  have hT : floorPower m ^ (2 ^ (k + 1)) ≤ (m ^ (2 ^ k)) ^ 3 := by
    rw [h2]
    exact (pow_sq_le_cube hsq).trans_eq hmid
  have hright : (n ^ (3 ^ o)) ^ 3 = n ^ (3 ^ (o + 1)) := by
    calc
      (n ^ (3 ^ o)) ^ 3 = n ^ (3 ^ o * 3) := (Nat.pow_mul n (3 ^ o) 3).symm
      _ = n ^ (3 * 3 ^ o) := by rw [mul_comm]
      _ = n ^ (3 ^ (o + 1)) := by rw [← pow_succ']
  have hcube :
      n ^ (3 ^ o) - m ^ (2 ^ k) ≤
        (n ^ (3 ^ o)) ^ 3 - (m ^ (2 ^ k)) ^ 3 :=
    pow_sub_pow_ge_sub h (by decide : (1 : ℕ) ≤ 3)
  have hdrop :
      (n ^ (3 ^ o)) ^ 3 - (m ^ (2 ^ k)) ^ 3 ≤
        (n ^ (3 ^ o)) ^ 3 - floorPower m ^ (2 ^ (k + 1)) :=
    Nat.sub_le_sub_left hT _
  have : n ^ (3 ^ o) - m ^ (2 ^ k) ≤
      (n ^ (3 ^ o)) ^ 3 - floorPower m ^ (2 ^ (k + 1)) :=
    le_trans hcube hdrop
  rwa [hright] at this

theorem power_deficit_from {start current k o : ℕ}
    (hbound : PowerBound current start k o) :
    ∀ w, follows current w →
      powerDeficit current start k o ≤
        powerDeficit (image current w) start (k + w.length)
          (o + oddCount w) := by
  intro w
  induction w generalizing current k o with
  | nil =>
      intro _
      exact le_rfl
  | cons b rest ih =>
      intro hw
      cases b with
      | even =>
          have heven : current % 2 = 0 := hw.1
          have hrest : follows (floorPower current) rest := hw.2
          have hstep := power_deficit_append_even hbound heven
          have hih :=
            ih (current := floorPower current) (k := k + 1) (o := o)
              (power_bound_append_even hbound heven) hrest
          have hk : k + (rest.length + 1) = k + 1 + rest.length := by omega
          simp [List.length_cons]
          rw [hk]
          exact le_trans hstep hih
      | odd =>
          have hodd : current % 2 = 1 := hw.1
          have hrest : follows (floorPower current) rest := hw.2
          have hstep := power_deficit_append_odd hbound hodd
          have hih :=
            ih (current := floorPower current) (k := k + 1) (o := o + 1)
              (power_bound_append_odd hbound hodd) hrest
          have hk : k + (rest.length + 1) = k + 1 + rest.length := by omega
          have ho : o + (oddCount rest + 1) = o + 1 + oddCount rest := by omega
          simp [List.length_cons]
          rw [hk, ho]
          exact le_trans hstep hih

theorem local_defect_even_le_suffix_deficit {m n k o : ℕ} {v : List Branch}
    (h : PowerBoundEq m n k o) (heven : m % 2 = 0)
    (hδ : floorPower m ^ 2 < m) (hv : follows (floorPower m) v) :
    localDefectEven m ≤
      powerDeficit (image (floorPower m) v) n
        (k + 1 + v.length) (o + oddCount v) := by
  have hgap : localDefectEven m ≤ powerDeficit (floorPower m) n (k + 1) o :=
    even_defect_gap_ge_local h heven hδ
  have hbound : PowerBound (floorPower m) n (k + 1) o :=
    power_bound_append_even (powerBound_of_eq h) heven
  exact hgap.trans (power_deficit_from hbound v hv)

theorem local_defect_odd_le_suffix_deficit {m n k o : ℕ} {v : List Branch}
    (h : PowerBoundEq m n k o) (hodd : m % 2 = 1)
    (hδ : floorPower m ^ 2 < m ^ 3) (hv : follows (floorPower m) v) :
    localDefectOdd m ≤
      powerDeficit (image (floorPower m) v) n
        (k + 1 + v.length) (o + 1 + oddCount v) := by
  have hgap : localDefectOdd m ≤ powerDeficit (floorPower m) n (k + 1) (o + 1) :=
    odd_defect_gap_ge_local h hodd hδ
  have hbound : PowerBound (floorPower m) n (k + 1) (o + 1) :=
    power_bound_append_odd (powerBound_of_eq h) hodd
  exact hgap.trans (power_deficit_from hbound v hv)

theorem powerDeficit_even_first {n : ℕ} (_heven : n % 2 = 0) :
    powerDeficit (floorPower n) n 1 0 = localDefectEven n := by
  simp [powerDeficit, localDefectEven]

theorem powerDeficit_odd_first {n : ℕ} (_hodd : n % 2 = 1) :
    powerDeficit (floorPower n) n 1 1 = localDefectOdd n := by
  simp [powerDeficit, localDefectOdd]

theorem pow_sub_pow_gt_sub {a b e : ℕ} (hba : b < a) (he : 2 ≤ e) (ha : 2 ≤ a) :
    a - b < a ^ e - b ^ e := by
  set d := a - b
  have hba' : b ≤ a := le_of_lt hba
  have hdpos : 1 ≤ d := Nat.succ_le_of_lt (Nat.sub_pos_of_lt hba)
  have ha' : b + d = a := Nat.add_sub_of_le hba'
  have hsum : b ^ e + d ^ e ≤ a ^ e := by
    simpa [ha'] using
      pow_add_pow_le_add_pow (b := b) (d := d)
        (le_trans (by decide : (1 : ℕ) ≤ 2) he)
  have hge : d ^ e ≤ a ^ e - b ^ e :=
    Nat.le_sub_of_add_le (add_comm (b ^ e) _ ▸ hsum)
  by_cases hd1 : d ≤ 1
  · have hd : d = 1 := le_antisymm hd1 hdpos
    have hb : 1 ≤ b := by
      have : 2 ≤ b + d := by simpa [ha'] using ha
      omega
    have he1 : 1 ≤ e - 1 := by omega
    have htail : b ^ (e - 1) + 1 ≤ (b + 1) ^ (e - 1) := by
      simpa using pow_add_pow_le_add_pow (b := b) (d := 1) he1
    have ha1 : a = b + 1 := by omega
    have hpow : (b + 1) ^ e = (b + 1) ^ (e - 1) * (b + 1) := by
      rw [← pow_succ, Nat.sub_add_cancel (by omega)]
    have hmul : (b ^ (e - 1) + 1) * (b + 1) ≤ (b + 1) ^ e := by
      rw [hpow]
      exact Nat.mul_le_mul_right _ htail
    have hexp : b ^ e + b ^ (e - 1) + b + 1 ≤ (b + 1) ^ e := by
      have hexpand :
          (b ^ (e - 1) + 1) * (b + 1) = b ^ e + b ^ (e - 1) + b + 1 := by
        calc
          (b ^ (e - 1) + 1) * (b + 1)
            = b ^ (e - 1) * (b + 1) + (b + 1) := by
              rw [add_mul, one_mul]
          _ = b ^ (e - 1) * b + b ^ (e - 1) + (b + 1) := by
              rw [mul_add, mul_one]
          _ = b ^ e + b ^ (e - 1) + (b + 1) := by
              rw [← pow_succ, Nat.sub_add_cancel (by omega)]
          _ = b ^ e + b ^ (e - 1) + b + 1 :=
            (add_assoc (b ^ e + b ^ (e - 1)) b (1 : ℕ)).symm
      exact hexpand ▸ hmul
    have hgap3 : 3 ≤ a ^ e - b ^ e := by
      have hb1 : 1 ≤ b ^ (e - 1) := by
        simpa using Nat.pow_le_pow_left hb (e - 1)
      have h3 : b ^ e + 3 ≤ (b + 1) ^ e := by
        have : 3 ≤ b ^ (e - 1) + b + 1 := by omega
        omega
      simpa [ha1] using Nat.le_sub_of_add_le (add_comm (b ^ e) (3 : ℕ) ▸ h3)
    rw [hd]
    exact Nat.lt_of_lt_of_le (by decide : (1 : ℕ) < 3) hgap3
  · have hlt : 1 < d := Nat.not_le.mp hd1
    have hd2 : 2 ≤ d := Nat.succ_le_of_lt hlt
    have hsq : d < d ^ 2 := by
      have : d * 1 < d * d :=
        Nat.mul_lt_mul_of_pos_left (by omega : 1 < d) (by omega : 0 < d)
      simpa [pow_two] using this
    have hde : d ^ 2 ≤ d ^ e := Nat.pow_le_pow_right hdpos he
    exact lt_of_lt_of_le (lt_of_lt_of_le hsq hde) hge

theorem two_le_two_pow_of_pos {k : ℕ} (hk : 1 ≤ k) : 2 ≤ 2 ^ k :=
  Nat.pow_le_pow_right (by decide : (1 : ℕ) ≤ 2) hk

theorem even_defect_gap_gt_of_pos_prefix {m n k o : ℕ}
    (h : PowerBoundEq m n k o) (_heven : m % 2 = 0)
    (hδ : floorPower m ^ 2 < m) (hk : 1 ≤ k) (hm : 2 ≤ m) :
    localDefectEven m < powerDeficit (floorPower m) n (k + 1) o := by
  have h2 : 2 ^ (k + 1) = 2 * 2 ^ k := two_pow_succ k
  have he : 2 ≤ 2 ^ k := two_le_two_pow_of_pos hk
  have hgap :
      m - floorPower m ^ 2 < m ^ (2 ^ k) - (floorPower m ^ 2) ^ (2 ^ k) :=
    pow_sub_pow_gt_sub hδ he hm
  unfold PowerBoundEq at h
  simpa [localDefectEven, powerDeficit, h, h2, Nat.pow_mul] using hgap

theorem odd_defect_gap_gt_of_pos_prefix {m n k o : ℕ}
    (h : PowerBoundEq m n k o) (_hodd : m % 2 = 1)
    (hδ : floorPower m ^ 2 < m ^ 3) (hk : 1 ≤ k) (hm : 2 ≤ m) :
    localDefectOdd m < powerDeficit (floorPower m) n (k + 1) (o + 1) := by
  have h2 : 2 ^ (k + 1) = 2 * 2 ^ k := two_pow_succ k
  have he : 2 ≤ 2 ^ k := two_le_two_pow_of_pos hk
  have hm3 : 2 ≤ m ^ 3 := by
    have : 8 ≤ m ^ 3 := Nat.pow_le_pow_left hm 3
    exact le_trans (by decide : (2 : ℕ) ≤ 8) this
  have hgap :
      m ^ 3 - floorPower m ^ 2 < (m ^ 3) ^ (2 ^ k) - (floorPower m ^ 2) ^ (2 ^ k) :=
    pow_sub_pow_gt_sub hδ he hm3
  have hmid : (m ^ 3) ^ (2 ^ k) = n ^ (3 ^ (o + 1)) := by
    have : (m ^ 3) ^ (2 ^ k) = (m ^ (2 ^ k)) ^ 3 := by
      rw [← Nat.pow_mul, mul_comm, Nat.pow_mul]
    rw [this, h]
    calc
      (n ^ (3 ^ o)) ^ 3 = n ^ (3 ^ o * 3) := (Nat.pow_mul n (3 ^ o) 3).symm
      _ = n ^ (3 * 3 ^ o) := by rw [mul_comm]
      _ = n ^ (3 ^ (o + 1)) := by rw [← pow_succ']
  simpa [localDefectOdd, powerDeficit, h2, Nat.pow_mul, hmid] using hgap

theorem power_deficit_append_even_eq {m n k o : ℕ}
    (_h : PowerBound m n k o) (_heven : m % 2 = 0)
    (htight : floorPower m ^ 2 = m) :
    powerDeficit (floorPower m) n (k + 1) o = powerDeficit m n k o := by
  unfold powerDeficit
  have h2 : 2 ^ (k + 1) = 2 * 2 ^ k := two_pow_succ k
  have hT : floorPower m ^ (2 ^ (k + 1)) = m ^ (2 ^ k) := by
    rw [h2, Nat.pow_mul, htight]
  rw [hT]

theorem power_deficit_append_even_of_defect {m n k o : ℕ}
    (h : PowerBound m n k o) (_heven : m % 2 = 0)
    (hδ : floorPower m ^ 2 < m) :
    powerDeficit m n k o < powerDeficit (floorPower m) n (k + 1) o := by
  unfold powerDeficit PowerBound at *
  have h2 : 2 ^ (k + 1) = 2 * 2 ^ k := two_pow_succ k
  have hT : floorPower m ^ (2 ^ (k + 1)) = (floorPower m ^ 2) ^ (2 ^ k) := by
    rw [h2, Nat.pow_mul]
  have hlt : (floorPower m ^ 2) ^ (2 ^ k) < m ^ (2 ^ k) :=
    Nat.pow_lt_pow_left hδ (pow_ne_zero_two_pow k)
  rw [hT]
  have hleft :
      n ^ (3 ^ o) - m ^ (2 ^ k) + (floorPower m ^ 2) ^ (2 ^ k) < n ^ (3 ^ o) := by
    have :
        n ^ (3 ^ o) - m ^ (2 ^ k) + (floorPower m ^ 2) ^ (2 ^ k) <
          n ^ (3 ^ o) - m ^ (2 ^ k) + m ^ (2 ^ k) :=
      Nat.add_lt_add_left hlt _
    rwa [Nat.sub_add_cancel h] at this
  have hA :
      n ^ (3 ^ o) - (floorPower m ^ 2) ^ (2 ^ k) + (floorPower m ^ 2) ^ (2 ^ k) =
        n ^ (3 ^ o) :=
    Nat.sub_add_cancel (le_of_lt (lt_of_lt_of_le hlt h))
  have hcmp :
      n ^ (3 ^ o) - m ^ (2 ^ k) + (floorPower m ^ 2) ^ (2 ^ k) <
        n ^ (3 ^ o) - (floorPower m ^ 2) ^ (2 ^ k) + (floorPower m ^ 2) ^ (2 ^ k) := by
    rwa [hA]
  exact Nat.lt_of_add_lt_add_right hcmp

theorem power_deficit_append_odd_of_strict {m n k o : ℕ}
    (h : StrictPowerBound m n k o) (hodd : m % 2 = 1) :
    powerDeficit m n k o < powerDeficit (floorPower m) n (k + 1) (o + 1) := by
  unfold powerDeficit StrictPowerBound at *
  have h2 : 2 ^ (k + 1) = 2 * 2 ^ k := two_pow_succ k
  have hsq : floorPower m ^ 2 ≤ m ^ 3 := floorPower_odd_sq_le_cube hodd
  have hmid : m ^ (3 * 2 ^ k) = (m ^ (2 ^ k)) ^ 3 := by
    rw [mul_comm, Nat.pow_mul]
  have hT : floorPower m ^ (2 ^ (k + 1)) ≤ (m ^ (2 ^ k)) ^ 3 := by
    rw [h2]
    exact (pow_sq_le_cube hsq).trans_eq hmid
  have hright : (n ^ (3 ^ o)) ^ 3 = n ^ (3 ^ (o + 1)) := by
    calc
      (n ^ (3 ^ o)) ^ 3 = n ^ (3 ^ o * 3) := (Nat.pow_mul n (3 ^ o) 3).symm
      _ = n ^ (3 * 3 ^ o) := by rw [mul_comm]
      _ = n ^ (3 ^ (o + 1)) := by rw [← pow_succ']
  have hmpos : 1 ≤ m := by
    have : m % 2 = 1 := hodd
    omega
  have ha : 2 ≤ n ^ (3 ^ o) := by
    have hb : 1 ≤ m ^ (2 ^ k) := by
      simpa using Nat.pow_le_pow_left hmpos (2 ^ k)
    have : m ^ (2 ^ k) + 1 ≤ n ^ (3 ^ o) := Nat.succ_le_of_lt h
    omega
  have hcube :
      n ^ (3 ^ o) - m ^ (2 ^ k) <
        (n ^ (3 ^ o)) ^ 3 - (m ^ (2 ^ k)) ^ 3 :=
    pow_sub_pow_gt_sub h (by decide : (2 : ℕ) ≤ 3) ha
  have hdrop :
      (n ^ (3 ^ o)) ^ 3 - (m ^ (2 ^ k)) ^ 3 ≤
        (n ^ (3 ^ o)) ^ 3 - floorPower m ^ (2 ^ (k + 1)) :=
    Nat.sub_le_sub_left hT _
  have : n ^ (3 ^ o) - m ^ (2 ^ k) <
      (n ^ (3 ^ o)) ^ 3 - floorPower m ^ (2 ^ (k + 1)) :=
    lt_of_lt_of_le hcube hdrop
  rwa [hright] at this

theorem suffix_deficit_eq_of_exact_even {current start k o : ℕ} {v : List Branch}
    (hbound : PowerBound current start k o)
    (hv : follows current v)
    (hevenV : v = List.replicate v.length Branch.even)
    (htight : localsTight current v) :
    powerDeficit (image current v) start (k + v.length) o
      = powerDeficit current start k o := by
  induction v generalizing current k with
  | nil => simp
  | cons b rest ih =>
      have hklen : (b :: rest).length = rest.length + 1 := rfl
      have hb : b = Branch.even := by
        have hrep : b :: rest = List.replicate (rest.length + 1) Branch.even := by
          simpa [hklen] using hevenV
        rw [List.replicate_succ] at hrep
        exact List.cons.inj hrep |>.1
      cases b with
      | odd => cases hb
      | even =>
          have heven : current % 2 = 0 := hv.1
          have hloc : floorPower current ^ 2 = current := by
            simpa [localTight] using htight.1
          have hstep := power_deficit_append_even_eq hbound heven hloc
          have hrestV : rest = List.replicate rest.length Branch.even := by
            have hrep : Branch.even :: rest =
                List.replicate (rest.length + 1) Branch.even := by
              simpa [hklen] using hevenV
            rw [List.replicate_succ] at hrep
            exact List.cons.inj hrep |>.2
          have hih :=
            ih (power_bound_append_even hbound heven) hv.2 hrestV htight.2
          have hk : k + (rest.length + 1) = k + 1 + rest.length := by omega
          simp [List.length_cons]
          rw [hk, hih, hstep]

theorem suffix_eq_of_deficit_eq {current start k o : ℕ} {v : List Branch}
    (hbound : PowerBound current start k o)
    (hstrict : StrictPowerBound current start k o)
    (hv : follows current v)
    (heq : powerDeficit (image current v) start (k + v.length) (o + oddCount v)
            = powerDeficit current start k o) :
    v = List.replicate v.length Branch.even ∧ localsTight current v := by
  induction v generalizing current k o with
  | nil =>
      exact ⟨rfl, trivial⟩
  | cons b rest ih =>
      cases b with
      | even =>
          have heven : current % 2 = 0 := hv.1
          have hrest : follows (floorPower current) rest := hv.2
          have hk : k + (rest.length + 1) = k + 1 + rest.length := by omega
          by_cases htight : floorPower current ^ 2 = current
          · have hstep := power_deficit_append_even_eq hbound heven htight
            have hbound' := power_bound_append_even hbound heven
            have hstrict' := strict_power_bound_append_even hstrict heven
            have heq' :
                powerDeficit (image (floorPower current) rest) start
                  (k + 1 + rest.length) (o + oddCount rest) =
                  powerDeficit (floorPower current) start (k + 1) o := by
              simp [List.length_cons] at heq
              rw [hk] at heq
              exact heq.trans hstep.symm
            have ih' := ih hbound' hstrict' hrest heq'
            have hklen : (Branch.even :: rest).length = rest.length + 1 := rfl
            refine ⟨?_, ⟨by simpa [localTight] using htight, ih'.2⟩⟩
            rw [hklen]
            conv => lhs; rw [ih'.1]
            rw [← List.replicate_succ]
          · have hδ : floorPower current ^ 2 < current :=
              lt_of_le_of_ne (floorPower_even_sq_le heven) htight
            have hlt := power_deficit_append_even_of_defect hbound heven hδ
            have hmono :=
              power_deficit_from (power_bound_append_even hbound heven) rest hrest
            have hlt' :
                powerDeficit current start k o <
                  powerDeficit (image (floorPower current) rest) start
                    (k + 1 + rest.length) (o + oddCount rest) :=
              hlt.trans_le hmono
            simp [List.length_cons] at heq
            rw [hk] at heq
            rw [heq] at hlt'
            exact (lt_irrefl _ hlt').elim
      | odd =>
          have hodd : current % 2 = 1 := hv.1
          have hrest : follows (floorPower current) rest := hv.2
          have hlt := power_deficit_append_odd_of_strict hstrict hodd
          have hmono :=
            power_deficit_from
              (power_bound_append_odd (le_of_lt hstrict) hodd) rest hrest
          have hk : k + (rest.length + 1) = k + 1 + rest.length := by omega
          have ho : o + (oddCount rest + 1) = o + 1 + oddCount rest := by omega
          have hlt' :
              powerDeficit current start k o <
                powerDeficit (image (floorPower current) rest) start
                  (k + 1 + rest.length) (o + 1 + oddCount rest) :=
            hlt.trans_le hmono
          simp [List.length_cons] at heq
          rw [hk, ho] at heq
          rw [heq] at hlt'
          exact (lt_irrefl _ hlt').elim

theorem power_deficit_eq_local_even_iff {n : ℕ} {v : List Branch}
    (heven : n % 2 = 0) (hδ : floorPower n ^ 2 < n)
    (hv : follows (floorPower n) v) :
    powerDeficit (image (floorPower n) v) n (v.length + 1) (oddCount v)
      = localDefectEven n ↔
      v = List.replicate v.length Branch.even ∧
        localsTight (floorPower n) v := by
  have hfirst : powerDeficit (floorPower n) n 1 0 = localDefectEven n :=
    powerDeficit_even_first heven
  have hstrict : StrictPowerBound (floorPower n) n 1 0 := by
    simpa [StrictPowerBound] using hδ
  have hbound : PowerBound (floorPower n) n 1 0 := le_of_lt hstrict
  constructor
  · intro heq
    have heq' :
        powerDeficit (image (floorPower n) v) n (1 + v.length) (0 + oddCount v)
          = powerDeficit (floorPower n) n 1 0 := by
      simpa [hfirst, add_comm v.length] using heq
    exact suffix_eq_of_deficit_eq hbound hstrict hv heq'
  · intro ⟨hevenV, htight⟩
    have ho : oddCount v = 0 := by
      rw [hevenV, oddCount_replicate_even]
    have heq := suffix_deficit_eq_of_exact_even hbound hv hevenV htight
    simpa [hfirst, ho, add_comm v.length] using heq

theorem power_deficit_eq_local_odd_iff {n : ℕ} {v : List Branch}
    (hodd : n % 2 = 1) (hδ : floorPower n ^ 2 < n ^ 3)
    (hv : follows (floorPower n) v) :
    powerDeficit (image (floorPower n) v) n (v.length + 1) (oddCount v + 1)
      = localDefectOdd n ↔
      v = List.replicate v.length Branch.even ∧
        localsTight (floorPower n) v := by
  have hfirst : powerDeficit (floorPower n) n 1 1 = localDefectOdd n :=
    powerDeficit_odd_first hodd
  have hstrict : StrictPowerBound (floorPower n) n 1 1 := by
    simpa [StrictPowerBound] using hδ
  have hbound : PowerBound (floorPower n) n 1 1 := le_of_lt hstrict
  constructor
  · intro heq
    have heq' :
        powerDeficit (image (floorPower n) v) n (1 + v.length) (1 + oddCount v)
          = powerDeficit (floorPower n) n 1 1 := by
      simpa [hfirst, add_comm v.length, add_comm (oddCount v)] using heq
    exact suffix_eq_of_deficit_eq hbound hstrict hv heq'
  · intro ⟨hevenV, htight⟩
    have ho : oddCount v = 0 := by
      rw [hevenV, oddCount_replicate_even]
    have heq := suffix_deficit_eq_of_exact_even hbound hv hevenV htight
    simpa [hfirst, ho, add_comm v.length] using heq

/-!
## Defect-compensated contraction

Formal drift `3^o > 2^k` does not by itself decide the block direction.
If the envelope deficit exceeds the formal gap `n^{3^o} - n^{2^k}`, the
image still contracts. This is not a halt theorem, not a first-defect
certificate, and not a lower-envelope theory.
-/

/-- Reusable certificate: a deficit larger than the formal exponent gap
forces `m < n` for `n ≥ 2`. -/
theorem power_bound_compensated_contracts
    {m n k o D : ℕ} (_hn : 2 ≤ n)
    (_hpow : PowerBound m n k o)
    (hD : D ≤ powerDeficit m n k o)
    (hgap : n ^ (3 ^ o) - n ^ (2 ^ k) < D) :
    m < n := by
  refine Nat.lt_of_not_ge fun hge => ?_
  have hleft : n ^ (2 ^ k) ≤ m ^ (2 ^ k) := Nat.pow_le_pow_left hge _
  have hΔ : n ^ (3 ^ o) - m ^ (2 ^ k) ≤ n ^ (3 ^ o) - n ^ (2 ^ k) :=
    Nat.sub_le_sub_left hleft _
  unfold powerDeficit at hD
  exact (lt_irrefl D) (lt_of_le_of_lt (le_trans hD hΔ) hgap)

theorem power_bound_compensated_contracts_follows
    {n : ℕ} {w : List Branch} {D : ℕ}
    (hn : 2 ≤ n) (hw : follows n w)
    (hD : D ≤ powerDeficit (floorPower^[w.length] n) n w.length (oddCount w))
    (hgap : n ^ (3 ^ oddCount w) - n ^ (2 ^ w.length) < D) :
    floorPower^[w.length] n < n :=
  power_bound_compensated_contracts hn (power_bound_follows hw) hD hgap

end Problems.Juggler
