import Problems.Juggler.Minimal
import Problems.Juggler.Preimages

namespace Problems.Juggler

/-!
# Predecessor closure of `ReachesOne`

`Good` is `ReachesOne`. Finite-horizon `Bad_H` is not formalized.
Predecessor closure from `{1}` is proved equal to `ReachesOne`. That
is a reparameterization, not a halt theorem and not a new induction
on interval coverage.
-/

def Good (n : ℕ) : Prop := ReachesOne n

def Bad (n : ℕ) : Prop := ¬ReachesOne n

theorem good_one : Good 1 :=
  reachesOne_one

theorem good_of_good_successor {n : ℕ} (h : Good (floorPower n)) : Good n :=
  reachesOne_of_iterate (k := 1) rfl h

theorem good_of_predecessor_certificate {n m : ℕ}
    (hm : Good m) (hT : floorPower n = m) : Good n := by
  simpa [hT] using good_of_good_successor (n := n) (by simpa [hT] using hm)

def PredEven (n m : ℕ) : Prop :=
  n % 2 = 0 ∧ floorPower n = m

def PredOdd (n m : ℕ) : Prop :=
  n % 2 = 1 ∧ floorPower n = m

theorem predEven_preimage {n m : ℕ} (h : PredEven n m) :
    m ^ 2 ≤ n ∧ n < (m + 1) ^ 2 :=
  (floorPower_even_eq_iff_sq_interval h.1).mp h.2

theorem predOdd_preimage {n m : ℕ} (h : PredOdd n m) :
    m ^ 2 ≤ n ^ 3 ∧ n ^ 3 < (m + 1) ^ 2 :=
  (floorPower_odd_eq_iff_cube_interval h.1).mp h.2

theorem good_of_predEven {n m : ℕ} (hm : Good m) (h : PredEven n m) : Good n :=
  good_of_predecessor_certificate hm h.2

theorem good_of_predOdd {n m : ℕ} (hm : Good m) (h : PredOdd n m) : Good n :=
  good_of_predecessor_certificate hm h.2

theorem even_good_of_sqrt_le {B n : ℕ}
    (hB : ∀ m, 1 ≤ m → m ≤ B → Good m)
    (heven : n % 2 = 0) (hpos : 1 ≤ n) (hs : n.sqrt ≤ B) : Good n := by
  have himg : floorPower n = n.sqrt := floorPower_even_eq heven
  have hsqrtpos : 1 ≤ n.sqrt :=
    Nat.le_sqrt.mpr (by simpa [pow_two] using hpos)
  exact good_of_predecessor_certificate (hB n.sqrt hsqrtpos hs) himg

theorem odd_not_pred_of_le {n m : ℕ} (hn : 3 ≤ n) (hodd : n % 2 = 1)
    (hle : m ≤ n) : ¬PredOdd n m := by
  intro h
  have hgt : n < floorPower n := floorPower_odd_gt hn hodd
  have : floorPower n = m := h.2
  omega

/-- `n` is not an immediate predecessor of any target `≤ B`. -/
def UncoveredOneStep (B n : ℕ) : Prop :=
  B < n ∧ B < floorPower n

theorem uncovered_odd {B n : ℕ} (hB : 2 ≤ B) (hn : B < n)
    (hodd : n % 2 = 1) : UncoveredOneStep B n := by
  have hn3 : 3 ≤ n := by omega
  have hgt : n < floorPower n := floorPower_odd_gt hn3 hodd
  exact ⟨hn, lt_trans hn hgt⟩

theorem uncovered_even_iff {B n : ℕ} (heven : n % 2 = 0) (_hpos : 1 ≤ n) :
    UncoveredOneStep B n ↔ B < n ∧ (B + 1) ^ 2 ≤ n := by
  have himg : floorPower n = n.sqrt := floorPower_even_eq heven
  constructor
  · intro h
    have hsqrt : B < n.sqrt := by simpa [himg] using h.2
    have hle : B + 1 ≤ n.sqrt := Nat.succ_le_of_lt hsqrt
    have hsq : (B + 1) ^ 2 ≤ n :=
      le_trans (Nat.pow_le_pow_left hle 2)
        (by simpa [pow_two] using Nat.sqrt_le n)
    exact ⟨h.1, hsq⟩
  · intro ⟨hn, hsq⟩
    have hle : B + 1 ≤ n.sqrt :=
      Nat.le_sqrt.mpr (by simpa [pow_two] using hsq)
    exact ⟨hn, by simpa [himg] using Nat.lt_of_succ_le hle⟩

theorem minimal_bad_uncovered_one_step {n : ℕ} (h : MinimalNonTerm n) :
    UncoveredOneStep (n - 1) n := by
  have hn12 : 12 ≤ n := minimal_nonterm_ge_twelve h
  have hodd := minimal_nonterm_odd h
  have hn : n - 1 < n := by omega
  have hn3 : 3 ≤ n := by omega
  have hgt : n < floorPower n := floorPower_odd_gt hn3 hodd
  exact ⟨hn, lt_trans hn hgt⟩

theorem minimal_bad_even_preimage_exclusion {n m : ℕ}
    (h : MinimalNonTerm n) (_hm : m < n) : ¬PredEven n m := by
  have hodd := minimal_nonterm_odd h
  intro hp
  have heven : n % 2 = 0 := hp.1
  omega

theorem minimal_bad_odd_preimage_exclusion {n m : ℕ}
    (h : MinimalNonTerm n) (hm : m < n) : ¬PredOdd n m := by
  have hn12 := minimal_nonterm_ge_twelve h
  have hodd := minimal_nonterm_odd h
  have hn3 : 3 ≤ n := by omega
  exact odd_not_pred_of_le hn3 hodd (Nat.le_of_lt hm)

theorem minimal_bad_barrier_constraint {n : ℕ} (h : MinimalNonTerm n) :
    ∀ k, n ≤ floorPower^[k] n :=
  minimal_nonterm_iterate_ge h

theorem pow_four_eq_mul_mul (n : ℕ) : n ^ 4 = (n * n) * (n * n) := by
  simp [pow_succ, pow_zero, mul_assoc]

theorem oe_barrier_pow {x n : ℕ}
    (hodd : x % 2 = 1) (heven : (x ^ 3).sqrt % 2 = 0) :
    n ≤ floorPower (floorPower x) ↔ n ^ 4 ≤ x ^ 3 := by
  have h1 : floorPower x = (x ^ 3).sqrt := floorPower_odd_eq hodd
  have h2 : floorPower (floorPower x) = ((x ^ 3).sqrt).sqrt := by
    rw [h1]
    exact floorPower_even_eq heven
  rw [h2]
  constructor
  · intro hle
    have hs : n * n ≤ (x ^ 3).sqrt := Nat.le_sqrt.mp hle
    have h4 : (n * n) * (n * n) ≤ x ^ 3 := Nat.le_sqrt.mp hs
    simpa [pow_four_eq_mul_mul] using h4
  · intro hpow
    have h4 : (n * n) * (n * n) ≤ x ^ 3 := by
      simpa [pow_four_eq_mul_mul] using hpow
    exact Nat.le_sqrt.mpr (Nat.le_sqrt.mpr h4)

theorem ee_barrier_pow {x n : ℕ}
    (he : x % 2 = 0) (he2 : x.sqrt % 2 = 0) :
    n ≤ floorPower (floorPower x) ↔ n ^ 4 ≤ x := by
  have h1 : floorPower x = x.sqrt := floorPower_even_eq he
  have h2 : floorPower (floorPower x) = x.sqrt.sqrt := by
    rw [h1]
    exact floorPower_even_eq he2
  rw [h2]
  constructor
  · intro hle
    have hs : n * n ≤ x.sqrt := Nat.le_sqrt.mp hle
    have h4 : (n * n) * (n * n) ≤ x := Nat.le_sqrt.mp hs
    simpa [pow_four_eq_mul_mul] using h4
  · intro hpow
    have h4 : (n * n) * (n * n) ≤ x := by
      simpa [pow_four_eq_mul_mul] using hpow
    exact Nat.le_sqrt.mpr (Nat.le_sqrt.mpr h4)

theorem eo_barrier_pow {x n : ℕ}
    (he : x % 2 = 0) (ho : x.sqrt % 2 = 1) :
    n ≤ floorPower (floorPower x) ↔ n ^ 2 ≤ x.sqrt ^ 3 := by
  have h1 : floorPower x = x.sqrt := floorPower_even_eq he
  have h2 : floorPower (floorPower x) = (x.sqrt ^ 3).sqrt := by
    rw [h1]
    exact floorPower_odd_eq ho
  rw [h2]
  constructor
  · intro hle
    simpa [pow_two] using Nat.le_sqrt.mp hle
  · intro hpow
    exact Nat.le_sqrt.mpr (by simpa [pow_two] using hpow)

theorem oo_barrier_of_le {x n : ℕ}
    (hx : 3 ≤ x) (hodd : x % 2 = 1) (hodd1 : (x ^ 3).sqrt % 2 = 1)
    (hn : n ≤ x) : n ≤ floorPower (floorPower x) :=
  le_of_lt (lt_of_le_of_lt hn (floorPower_odd_odd_two_step_gt hx hodd hodd1))

/-- Exact predecessor closure of `{1}`. -/
inductive PredClosure : ℕ → Prop
  | seed : PredClosure 1
  | pred {n m : ℕ} (hm : PredClosure m) (hT : floorPower n = m) : PredClosure n

theorem good_of_predClosure {n : ℕ} (h : PredClosure n) : Good n := by
  induction h with
  | seed => exact good_one
  | pred hm hT ih => exact good_of_predecessor_certificate ih hT

theorem predClosure_of_iterate {n k : ℕ} (h : floorPower^[k] n = 1) :
    PredClosure n := by
  induction k generalizing n with
  | zero =>
      simp at h
      subst h
      exact PredClosure.seed
  | succ k ih =>
      rw [iterate_cons] at h
      exact PredClosure.pred (ih h) rfl

theorem predClosure_iff_good {n : ℕ} : PredClosure n ↔ Good n := by
  constructor
  · exact good_of_predClosure
  · rintro ⟨k, hk⟩
    exact predClosure_of_iterate hk

theorem predClosure_iff_reachesOne {n : ℕ} : PredClosure n ↔ ReachesOne n :=
  predClosure_iff_good

theorem minimal_bad_not_predClosure {n : ℕ} (h : MinimalNonTerm n) :
    ¬PredClosure n := by
  intro hp
  exact h.not_reachesOne (good_of_predClosure hp)

end Problems.Juggler
