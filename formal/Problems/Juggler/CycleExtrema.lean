import Problems.Juggler.CycleCore
import Problems.Juggler.Scale

namespace Problems.Juggler

/-!
# Cycle extrema, peak blocks, and remainders

The extrema of any nontrivial cycle are word-independent: the
minimum is odd, the maximum is even, and `M > m^2`. A realized path
from `m` to any even cycle state is therefore superquadratic. After
the even-count-3 assembler, first-even overshoot sharpens the scale
to `M ≥ (m+1)^2` (`cycleMin_max_ge_succ_sq` in `EvenCountThree`):
the first-cell family is impossible and `T(M) > m`. The maximum
begins a finite even run `E^r` onto an odd landing `p`, with
`p^{2^r} ≤ M < (p+1)^{2^r}`. The predecessor `x` of `M` is odd and
strictly between the landing and the maximum: `p < x < M`, with
`M^2 ≤ x^3 < (M+1)^2` and `x^3 ≥ p^{2^{r+1}}`. The peak block
`OE^r` is a canonical strict descent `T_{OE^r}(x)=p<x` and is
formally contracting. Financing that descent from `p` back to `x`
recovers the existing ascent scale, not a stronger envelope. The
distinguished order is `m ≤ p < x < M` with a strict top window
`p^{2^r} < M`. Composing the known scale laws does not beat the
ordinary itinerary envelope.

The local floor remainder `branchDefect` is the information the
envelope drops: `x^e = T(x)^2 + ρ` with `0 ≤ ρ < 2T(x)+1`. On a
cycle these remainders balance against the odd/even state gaps, and
at least one remainder is positive for `n ≥ 2`. Dropping every `ρ`
recovers `power_bound_word`. Not on the leftover import path.
This is not a halt theorem and not a claim that every cycle itinerary
is impossible.
-/

/-- Dual of `CycleMin`: the start is a maximum of its realized cycle. -/
def CycleMax (n : ℕ) (w : List Branch) : Prop :=
  CycleItinerary n w ∧ ∀ j, j < w.length → floorPower^[j] n ≤ n

theorem cycleMax_cycleItinerary {n : ℕ} {w : List Branch} (h : CycleMax n w) :
    CycleItinerary n w :=
  h.1

theorem cycleMax_le {n : ℕ} {w : List Branch} {j : ℕ}
    (h : CycleMax n w) (hj : j < w.length) : floorPower^[j] n ≤ n :=
  h.2 j hj

theorem exists_iterate_max (n k : ℕ) (hk : 1 ≤ k) :
    ∃ i < k, ∀ j < k, floorPower^[j] n ≤ floorPower^[i] n := by
  induction k with
  | zero => omega
  | succ k ih =>
      match k with
      | 0 =>
          refine ⟨0, by omega, ?_⟩
          intro j hj
          have : j = 0 := by omega
          subst this
          exact le_rfl
      | k' + 1 =>
          have ⟨i, hi, hmax⟩ := ih (by omega : 1 ≤ k' + 1)
          cases le_or_gt (floorPower^[k' + 1] n) (floorPower^[i] n) with
          | inl hle =>
              refine ⟨i, Nat.lt_trans hi (by omega), ?_⟩
              intro j hj
              rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hj) with hlt | heq
              · exact hmax j hlt
              · simpa [heq] using hle
          | inr hgt =>
              refine ⟨k' + 1, by omega, ?_⟩
              intro j hj
              rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hj) with hjt | heq
              · exact (hmax j hjt).trans (le_of_lt hgt)
              · subst heq
                exact le_rfl

/-- The maximum state of a nontrivial cycle is even, because an odd
state strictly ascends. -/
theorem exists_cycle_max_even {n : ℕ} {w : List Branch}
    (hn : 2 ≤ n) (h : CycleItinerary n w) :
    ∃ i < w.length,
      (∀ j < w.length, floorPower^[j] n ≤ floorPower^[i] n) ∧
        floorPower^[i] n % 2 = 0 := by
  have ⟨i, hi, hmax⟩ := exists_iterate_max n w.length h.2.2
  refine ⟨i, hi, hmax, ?_⟩
  have hge := cycleItinerary_iterate_ge_two hn h hi
  rcases Nat.mod_two_eq_zero_or_one (floorPower^[i] n) with he | ho
  · exact he
  · exfalso
    have hn3 : 3 ≤ floorPower^[i] n := by omega
    have hlt : floorPower^[i] n < floorPower^[i + 1] n := by
      simpa [Function.iterate_succ_apply'] using floorPower_odd_gt hn3 ho
    cases lt_or_eq_of_le (Nat.succ_le_of_lt hi) with
    | inl hlen =>
        exact (not_le_of_gt hlt) (hmax (i + 1) hlen)
    | inr heq =>
        have hper := cycle_iterate_period h
        have hlt' : floorPower^[i] n < floorPower^[w.length] n := by
          convert hlt
          exact heq.symm
        rw [hper] at hlt'
        exact (not_le_of_gt hlt') (hmax 0 (lt_of_lt_of_le (by decide : (0 : ℕ) < 1) h.2.2))

theorem cycleMax_start_even {n : ℕ} {w : List Branch}
    (hn : 2 ≤ n) (h : CycleMax n w) : n % 2 = 0 := by
  rcases Nat.mod_two_eq_zero_or_one n with he | ho
  · exact he
  · exfalso
    have hn3 : 3 ≤ n := by omega
    have hgt : n < floorPower n := floorPower_odd_gt hn3 ho
    cases Nat.eq_or_lt_of_le h.1.2.2 with
    | inl h1 =>
        have hper := cycle_iterate_period h.1
        have hlen1 : w.length = 1 := by omega
        rw [hlen1] at hper
        change floorPower n = n at hper
        omega
    | inr hgt1 =>
        have hle : floorPower^[1] n ≤ n := cycleMax_le h hgt1
        exact (not_le_of_gt hgt) hle

theorem exists_cycleMax {n : ℕ} {w : List Branch}
    (hn : 2 ≤ n) (h : CycleItinerary n w) :
    ∃ k < w.length, CycleMax (floorPower^[k] n) (rotateItinerary w k) := by
  have ⟨i, hi, hge, _heven⟩ := exists_cycle_max_even hn h
  refine ⟨i, hi, cycleItinerary_rotateItinerary h i, ?_⟩
  intro j hj
  have hlen : (rotateItinerary w i).length = w.length := rotateItinerary_length w i
  rw [hlen] at hj
  have himg : floorPower^[j] (floorPower^[i] n) = floorPower^[i + j] n := by
    simpa [Nat.add_comm] using
      (Function.iterate_add_apply floorPower j i n).symm
  rw [himg, cycle_iterate_mod (k := i + j) h]
  exact hge _ (Nat.mod_lt _ (lt_of_lt_of_le (by decide : (0 : ℕ) < 1) h.2.2))

/-- On a cycle minimum the maximum is even and strictly above `n^2`. -/
theorem cycleMin_max_gt_sq {n : ℕ} {w : List Branch}
    (hn : 2 ≤ n) (h : CycleMin n w) :
    ∃ i < w.length,
      (∀ j < w.length, floorPower^[j] n ≤ floorPower^[i] n) ∧
        floorPower^[i] n % 2 = 0 ∧ n ^ 2 < floorPower^[i] n := by
  have ⟨i, hi, hmax, heven⟩ := exists_cycle_max_even hn h.1
  refine ⟨i, hi, hmax, heven, ?_⟩
  have hsq := cycleMin_even_ge_sq hn h hi heven
  have hodd := cycleMin_start_odd hn h
  exact lt_of_le_of_ne hsq (even_ne_odd_square heven hodd).symm

theorem cycleMax_return_preimage {n : ℕ} {w : List Branch}
    (hn : 2 ≤ n) (h : CycleMax n w) :
    n % 2 = 0 ∧ n.sqrt ^ 2 ≤ n ∧ n < (n.sqrt + 1) ^ 2 := by
  have he := cycleMax_start_even hn h
  have hfp : floorPower n = n.sqrt := floorPower_even_eq he
  have hI := (floorPower_even_eq_iff_sq_interval he).mp hfp
  exact ⟨he, hI.1, hI.2⟩

theorem square_scale_superquadratic {n : ℕ} {w : List Branch}
    (hn : 2 ≤ n) (hw : follows n w) (himg : n ^ 2 ≤ image n w) :
    2 ^ (w.length + 1) ≤ 3 ^ oddCount w := by
  have hpow : (image n w) ^ (2 ^ w.length) ≤ n ^ (3 ^ oddCount w) := by
    simpa [image_eq_iterate] using power_bound_word hw
  have hleft :
      (n ^ 2) ^ (2 ^ w.length) ≤ (image n w) ^ (2 ^ w.length) :=
    Nat.pow_le_pow_left himg _
  have hmul : (n ^ 2) ^ (2 ^ w.length) = n ^ (2 * 2 ^ w.length) :=
    (Nat.pow_mul n 2 (2 ^ w.length)).symm
  have h2 : 2 * 2 ^ w.length = 2 ^ (w.length + 1) :=
    (two_pow_succ w.length).symm
  have hle : n ^ (2 ^ (w.length + 1)) ≤ n ^ (3 ^ oddCount w) := by
    rw [← h2, ← hmul]
    exact le_trans hleft hpow
  exact
    (Nat.pow_le_pow_iff_right
        (lt_of_lt_of_le (by decide : (1 : ℕ) < 2) hn)).mp
      hle

/-- The path from a cycle minimum to any later even state — in
particular to the maximum — is superquadratic. -/
theorem cycleMin_to_even_superquadratic {n : ℕ} {w : List Branch} {i : ℕ}
    (hn : 2 ≤ n) (h : CycleMin n w) (hi : i < w.length)
    (he : floorPower^[i] n % 2 = 0) :
    2 ^ (i + 1) ≤ 3 ^ oddCount (w.take i) := by
  have hw : follows n (w.take i) := follows_take w i h.1.1
  have hlen : (w.take i).length = i := by
    rw [List.length_take, Nat.min_eq_left (Nat.le_of_lt hi)]
  have himg : image n (w.take i) = floorPower^[i] n :=
    image_take_of_le (Nat.le_of_lt hi)
  have hsq : n ^ 2 ≤ floorPower^[i] n := cycleMin_even_ge_sq hn h hi he
  have hsq' : n ^ 2 ≤ image n (w.take i) := by simpa [himg] using hsq
  have hα := square_scale_superquadratic hn hw hsq'
  simpa [hlen] using hα

theorem cycleMin_to_max_superquadratic {n : ℕ} {w : List Branch}
    (hn : 2 ≤ n) (h : CycleMin n w) :
    ∃ i < w.length,
      floorPower^[i] n % 2 = 0 ∧ n ^ 2 < floorPower^[i] n ∧
        2 ^ (i + 1) ≤ 3 ^ oddCount (w.take i) := by
  have ⟨i, hi, _hmax, heven, hgt⟩ := cycleMin_max_gt_sq hn h
  exact ⟨i, hi, heven, hgt, cycleMin_to_even_superquadratic hn h hi heven⟩

/-- `r` consecutive even iterates give `T^r(x)^{2^r} ≤ x`. -/
theorem even_iter_pow_le {x : ℕ} :
    ∀ r, (∀ i < r, floorPower^[i] x % 2 = 0) →
      (floorPower^[r] x) ^ (2 ^ r) ≤ x
  | 0, _ => by simp
  | r + 1, he => by
      have he0 : x % 2 = 0 := he 0 (by omega)
      have her : ∀ i < r, floorPower^[i] (floorPower x) % 2 = 0 := by
        intro i hi
        have := he (i + 1) (by omega)
        simpa [Function.iterate_succ_apply] using this
      have ih := even_iter_pow_le r her
      have hstep : floorPower x ^ 2 ≤ x := floorPower_even_sq_le he0
      have hiter : floorPower^[r + 1] x = floorPower^[r] (floorPower x) :=
        Function.iterate_succ_apply floorPower r x
      have hpow :
          (floorPower^[r + 1] x) ^ (2 ^ (r + 1)) =
            ((floorPower^[r] (floorPower x)) ^ (2 ^ r)) ^ 2 := by
        have hr2 : 2 ^ (r + 1) = 2 ^ r * 2 := by
          rw [two_pow_succ, mul_comm]
        rw [hiter, hr2, Nat.pow_mul]
      rw [hpow]
      exact le_trans (Nat.pow_le_pow_left ih 2) hstep

/-- Matching upper cell: `x < (T^r(x)+1)^{2^r}`. -/
theorem even_iter_lt_succ_pow {x : ℕ} :
    ∀ r, (∀ i < r, floorPower^[i] x % 2 = 0) →
      x < (floorPower^[r] x + 1) ^ (2 ^ r)
  | 0, _ => by simp
  | r + 1, he => by
      have he0 : x % 2 = 0 := he 0 (by omega)
      have her : ∀ i < r, floorPower^[i] (floorPower x) % 2 = 0 := by
        intro i hi
        have := he (i + 1) (by omega)
        simpa [Function.iterate_succ_apply] using this
      have ih := even_iter_lt_succ_pow r her
      have hfp : floorPower x = x.sqrt := floorPower_even_eq he0
      have hcell : x < (floorPower x + 1) ^ 2 := by
        have hI := (floorPower_even_eq_iff_sq_interval he0).mp hfp
        simpa [hfp] using hI.2
      have hiter : floorPower^[r + 1] x = floorPower^[r] (floorPower x) :=
        Function.iterate_succ_apply floorPower r x
      have hle :
          floorPower x + 1 ≤
            (floorPower^[r + 1] x + 1) ^ (2 ^ r) := by
        refine Nat.succ_le_of_lt ?_
        simpa [hiter] using ih
      have hlt :
          x < ((floorPower^[r + 1] x + 1) ^ (2 ^ r)) ^ 2 :=
        lt_of_lt_of_le hcell (Nat.pow_le_pow_left hle 2)
      have hpow :
          ((floorPower^[r + 1] x + 1) ^ (2 ^ r)) ^ 2 =
            (floorPower^[r + 1] x + 1) ^ (2 ^ (r + 1)) := by
        have hr2 : 2 ^ (r + 1) = 2 ^ r * 2 := by
          rw [two_pow_succ, mul_comm]
        rw [hr2, Nat.pow_mul]
      rwa [hpow] at hlt

theorem exists_first_odd_iterate {n t : ℕ}
    (h0 : n % 2 = 0) (ht : 1 ≤ t)
    (hodd : floorPower^[t] n % 2 = 1) :
    ∃ r, 1 ≤ r ∧ r ≤ t ∧
      (∀ i < r, floorPower^[i] n % 2 = 0) ∧
      floorPower^[r] n % 2 = 1 := by
  let P : ℕ → Prop :=
    fun r => 1 ≤ r ∧ r ≤ t ∧ floorPower^[r] n % 2 = 1
  have hP : ∃ r, P r := ⟨t, ht, le_rfl, hodd⟩
  let r := Nat.find hP
  have hr : P r := Nat.find_spec hP
  refine ⟨r, hr.1, hr.2.1, ?_, hr.2.2⟩
  intro i hi
  have hnot : ¬P i := Nat.find_min hP hi
  cases i with
  | zero => exact h0
  | succ i =>
      have hi1 : 1 ≤ i + 1 := Nat.succ_le_succ (Nat.zero_le i)
      have hi2 : i + 1 ≤ t :=
        Nat.le_of_lt (lt_of_lt_of_le hi hr.2.1)
      have : ¬floorPower^[i + 1] n % 2 = 1 := fun h =>
        hnot ⟨hi1, hi2, h⟩
      rcases Nat.mod_two_eq_zero_or_one (floorPower^[i + 1] n) with he | ho
      · exact he
      · exact (this ho).elim

/-- Reaching scale `n^{2^s}` requires `3^o ≥ 2^{k+s}`. -/
theorem power_scale_superquadratic {n : ℕ} {w : List Branch} {s : ℕ}
    (hn : 2 ≤ n) (hw : follows n w)
    (himg : n ^ (2 ^ s) ≤ image n w) :
    2 ^ (w.length + s) ≤ 3 ^ oddCount w := by
  have hpow : (image n w) ^ (2 ^ w.length) ≤ n ^ (3 ^ oddCount w) := by
    simpa [image_eq_iterate] using power_bound_word hw
  have hleft :
      (n ^ (2 ^ s)) ^ (2 ^ w.length) ≤ (image n w) ^ (2 ^ w.length) :=
    Nat.pow_le_pow_left himg _
  have hmul : (n ^ (2 ^ s)) ^ (2 ^ w.length) = n ^ (2 ^ s * 2 ^ w.length) :=
    (Nat.pow_mul n (2 ^ s) (2 ^ w.length)).symm
  have h2 : 2 ^ s * 2 ^ w.length = 2 ^ (w.length + s) := by
    rw [← Nat.pow_add, Nat.add_comm]
  have hle : n ^ (2 ^ (w.length + s)) ≤ n ^ (3 ^ oddCount w) := by
    rw [← h2, ← hmul]
    exact le_trans hleft hpow
  exact
    (Nat.pow_le_pow_iff_right
        (lt_of_lt_of_le (by decide : (1 : ℕ) < 2) hn)).mp
      hle

theorem follows_of_even_iter {n : ℕ} :
    ∀ r, (∀ i < r, floorPower^[i] n % 2 = 0) →
      follows n (List.replicate r Branch.even)
  | 0, _ => trivial
  | r + 1, he => by
      refine ⟨he 0 (by omega), ?_⟩
      refine follows_of_even_iter r ?_
      intro i hi
      have := he (i + 1) (by omega)
      simpa [Function.iterate_succ_apply] using this

theorem take_eq_replicate_even {n : ℕ} :
    ∀ (w : List Branch) r,
      follows n w → r ≤ w.length →
        (∀ i < r, floorPower^[i] n % 2 = 0) →
          w.take r = List.replicate r Branch.even
  | w, 0, _, _, _ => by simp
  | [], r + 1, _, hlen, _ => by
      simp at hlen
  | b :: rest, r + 1, hw, hlen, he => by
      have he0 : n % 2 = 0 := he 0 (by omega)
      have hb : b = Branch.even := by
        cases b with
        | even => rfl
        | odd =>
            have : n % 2 = 1 := hw.1
            omega
      subst hb
      have hrest :
          rest.take r = List.replicate r Branch.even := by
        refine take_eq_replicate_even rest r hw.2 (by simp at hlen; omega) ?_
        intro i hi
        have := he (i + 1) (by omega)
        simpa [Function.iterate_succ_apply] using this
      simpa [List.take, List.replicate_succ] using hrest

theorem rotateItinerary_even_run :
    ∀ r u, rotateItinerary (List.replicate r Branch.even ++ u) r =
      u ++ List.replicate r Branch.even
  | 0, u => by simp [rotateItinerary]
  | r + 1, u => by
      have hrep :
          List.replicate (r + 1) Branch.even ++ u =
            Branch.even :: (List.replicate r Branch.even ++ u) := by
        rw [List.replicate_succ, List.cons_append]
      rw [hrep, rotateItinerary]
      have hassoc :
          List.replicate r Branch.even ++ u ++ [Branch.even] =
            List.replicate r Branch.even ++ (u ++ [Branch.even]) := by
        simp [List.append_assoc]
      rw [hassoc, rotateItinerary_even_run r (u ++ [Branch.even])]
      simp [List.append_assoc, List.replicate_succ]

/-- Every cycle maximum begins a finite even run onto an odd landing. -/
theorem cycleMax_top_even_run {n : ℕ} {w : List Branch}
    (hn : 2 ≤ n) (h : CycleMax n w) :
    ∃ r, 1 ≤ r ∧ r < w.length ∧
      (∀ i < r, floorPower^[i] n % 2 = 0) ∧
        floorPower^[r] n % 2 = 1 ∧
          (floorPower^[r] n) ^ (2 ^ r) ≤ n ∧
            n < (floorPower^[r] n + 1) ^ (2 ^ r) := by
  have ⟨i, hi, _, hodd⟩ := exists_cycle_min_odd hn h.1
  have h0 := cycleMax_start_even hn h
  have hi1 : 1 ≤ i := by
    cases i with
    | zero =>
        have : n % 2 = 1 := by simpa using hodd
        omega
    | succ _ => omega
  have ⟨r, hr1, hrle, heven, hodd'⟩ := exists_first_odd_iterate h0 hi1 hodd
  have hrlt : r < w.length := lt_of_le_of_lt hrle hi
  exact ⟨r, hr1, hrlt, heven, hodd', even_iter_pow_le r heven,
    even_iter_lt_succ_pow r heven⟩

/-- Rotate a cycle maximum to the odd landing after its top even run. -/
theorem cycleMax_top_normal_form {n : ℕ} {w : List Branch}
    (hn : 2 ≤ n) (h : CycleMax n w) :
    ∃ r u p, 1 ≤ r ∧
      w = List.replicate r Branch.even ++ u ∧
        p = floorPower^[r] n ∧ p % 2 = 1 ∧ 2 ≤ p ∧
          CycleItinerary p (u ++ List.replicate r Branch.even) ∧
            image p u = n ∧
              p ^ (2 ^ r) ≤ n ∧ n < (p + 1) ^ (2 ^ r) ∧
                2 ^ (u.length + r) ≤ 3 ^ oddCount u := by
  have ⟨r, hr1, hrlt, heven, hodd, hlo, hhi⟩ := cycleMax_top_even_run hn h
  have hw := h.1.1
  have htake :=
    take_eq_replicate_even w r hw (Nat.le_of_lt hrlt) heven
  have hsplit := (List.take_append_drop r w).symm
  set u := w.drop r
  have hwform : w = List.replicate r Branch.even ++ u := by
    simpa [htake, u] using hsplit
  have hp : 2 ≤ floorPower^[r] n := cycleItinerary_iterate_ge_two hn h.1 hrlt
  have hrot := cycleItinerary_rotateItinerary h.1 r
  have hrotw : rotateItinerary w r = u ++ List.replicate r Branch.even := by
    simpa [hwform] using rotateItinerary_even_run r u
  have hC : CycleItinerary (floorPower^[r] n) (u ++ List.replicate r Branch.even) := by
    simpa [hrotw] using hrot
  have himg : image (floorPower^[r] n) u = n := by
    have hlenu : u.length = w.length - r := by
      simp [u, List.length_drop]
    have himg' : image (floorPower^[r] n) u =
        floorPower^[w.length - r] (floorPower^[r] n) := by
      simpa [hlenu] using image_eq_iterate (floorPower^[r] n) u
    have hsum : w.length - r + r = w.length :=
      Nat.sub_add_cancel (Nat.le_of_lt hrlt)
    have hcomp : floorPower^[w.length - r] (floorPower^[r] n) =
        floorPower^[w.length] n := by
      have hiter := Function.iterate_add_apply floorPower (w.length - r) r n
      simpa [hsum] using hiter.symm
    simpa [himg', hcomp] using cycle_iterate_period h.1
  have hα : 2 ^ (u.length + r) ≤ 3 ^ oddCount u := by
    have hu : follows (floorPower^[r] n) u := by
      have := follows_of_append_left (u := u) hC.1
      exact this
    exact power_scale_superquadratic hp hu (by simpa [himg] using hlo)
  exact ⟨r, u, floorPower^[r] n, hr1, hwform, rfl, hodd, hp, hC, himg, hlo, hhi, hα⟩

theorem top_ascent_superquadratic {p : ℕ} {u : List Branch} {r : ℕ}
    (hp : 2 ≤ p) (hu : follows p u)
    (hM : p ^ (2 ^ r) ≤ image p u) :
    2 ^ (u.length + r) ≤ 3 ^ oddCount u :=
  power_scale_superquadratic hp hu hM

theorem cycleMax_length_ge_two {n : ℕ} {w : List Branch}
    (hn : 2 ≤ n) (h : CycleMax n w) : 2 ≤ w.length := by
  have hlen : 1 ≤ w.length := h.1.2.2
  cases Nat.eq_or_lt_of_le hlen with
  | inl h1 =>
      have hper := cycle_iterate_period h.1
      have he := cycleMax_start_even hn h
      have hlt := floorPower_even_lt hn he
      have : floorPower n = n := by
        rw [show w.length = 1 from h1.symm] at hper
        simpa using hper
      omega
  | inr hgt => exact hgt

/-- The predecessor of a cycle maximum is odd: an even predecessor
would strictly descend. -/
theorem cycleMax_predecessor_odd {n : ℕ} {w : List Branch}
    (hn : 2 ≤ n) (h : CycleMax n w) :
    floorPower^[w.length - 1] n % 2 = 1 := by
  have hlen : 2 ≤ w.length := cycleMax_length_ge_two hn h
  have hi : w.length - 1 < w.length := by omega
  have hx2 : 2 ≤ floorPower^[w.length - 1] n :=
    cycleItinerary_iterate_ge_two hn h.1 hi
  have hTx : floorPower (floorPower^[w.length - 1] n) = n := by
    have hper := cycle_iterate_period h.1
    have hsum : w.length = w.length - 1 + 1 := by omega
    rw [hsum, Function.iterate_succ_apply'] at hper
    exact hper
  rcases Nat.mod_two_eq_zero_or_one (floorPower^[w.length - 1] n) with he | ho
  · have hlt := floorPower_even_lt hx2 he
    have hle := cycleMax_le h hi
    omega
  · exact ho

theorem cycleMax_predecessor_apply {n : ℕ} {w : List Branch}
    (hn : 2 ≤ n) (h : CycleMax n w) :
    floorPower (floorPower^[w.length - 1] n) = n := by
  have hlen : 2 ≤ w.length := cycleMax_length_ge_two hn h
  have hper := cycle_iterate_period h.1
  have hsum : w.length = w.length - 1 + 1 := by omega
  rw [hsum, Function.iterate_succ_apply'] at hper
  exact hper

theorem cycleMax_predecessor_lt {n : ℕ} {w : List Branch}
    (hn : 2 ≤ n) (h : CycleMax n w) :
    floorPower^[w.length - 1] n < n := by
  have hlen : 2 ≤ w.length := cycleMax_length_ge_two hn h
  have hi : w.length - 1 < w.length := by omega
  have hx2 : 2 ≤ floorPower^[w.length - 1] n :=
    cycleItinerary_iterate_ge_two hn h.1 hi
  have ho := cycleMax_predecessor_odd hn h
  have hn3 : 3 ≤ floorPower^[w.length - 1] n := by omega
  have hTx := cycleMax_predecessor_apply hn h
  have hgt := floorPower_odd_gt hn3 ho
  simpa [hTx] using hgt

/-- Inverse odd one-step preimage at the predecessor of the maximum. -/
theorem cycle_top_predecessor_preimage {n : ℕ} {w : List Branch}
    (hn : 2 ≤ n) (h : CycleMax n w) :
    n ^ 2 ≤ (floorPower^[w.length - 1] n) ^ 3 ∧
      (floorPower^[w.length - 1] n) ^ 3 < (n + 1) ^ 2 := by
  have ho := cycleMax_predecessor_odd hn h
  have hTx := cycleMax_predecessor_apply hn h
  exact (floorPower_odd_eq_iff_cube_interval ho).mp hTx

/-- Even-run iterates after the first step are at most `T(x)`. -/
theorem even_iter_le_first {x : ℕ} :
    ∀ r, (∀ i < r, floorPower^[i] x % 2 = 0) →
      (∀ i < r, 2 ≤ floorPower^[i] x) →
        1 ≤ r →
          floorPower^[r] x ≤ floorPower x
  | 0, _, _, hr => (Nat.not_succ_le_zero 0 hr).elim
  | 1, _, _, _ => le_rfl
  | r + 2, he, h2, _ => by
      have hmid_even : floorPower^[r + 1] x % 2 = 0 := he (r + 1) (by omega)
      have hmid_ge : 2 ≤ floorPower^[r + 1] x := h2 (r + 1) (by omega)
      have hstep : floorPower^[r + 2] x < floorPower^[r + 1] x := by
        simpa [Function.iterate_succ_apply'] using
          floorPower_even_lt hmid_ge hmid_even
      have ih : floorPower^[r + 1] x ≤ floorPower x :=
        even_iter_le_first (r + 1)
          (fun i hi => he i (lt_trans hi (by omega)))
          (fun i hi => h2 i (lt_trans hi (by omega)))
          (by omega)
      exact le_of_lt (lt_of_lt_of_le hstep ih)

/-- The odd-cell lower bound forces `M < x^2` for `x ≥ 2`. -/
theorem cycle_top_max_lt_pred_sq {x n : ℕ}
    (hx : 2 ≤ x) (hcell : n ^ 2 ≤ x ^ 3) : n < x ^ 2 := by
  have hx0 : 0 < x := lt_of_lt_of_le (by decide : (0 : ℕ) < 2) hx
  have hstrict : x ^ 3 < x ^ 4 := by
    have : x ^ 3 * 1 < x ^ 3 * x :=
      Nat.mul_lt_mul_of_pos_left (by omega : 1 < x) (Nat.pow_pos hx0)
    simpa [pow_succ] using this
  have hpow : x ^ 4 = (x ^ 2) ^ 2 := by
    rw [← Nat.pow_mul]
  have : n ^ 2 < (x ^ 2) ^ 2 :=
    lt_of_le_of_lt hcell (hpow ▸ hstrict)
  exact (Nat.pow_lt_pow_iff_left (by decide : (2 : ℕ) ≠ 0)).mp this

/-- From the nested lower cells: `x^3 ≥ p^{2^{r+1}}`. -/
theorem cycle_top_pred_scale {p n x r : ℕ}
    (hM : p ^ (2 ^ r) ≤ n) (hcell : n ^ 2 ≤ x ^ 3) :
    p ^ (2 ^ (r + 1)) ≤ x ^ 3 := by
  have hsq : (p ^ (2 ^ r)) ^ 2 ≤ n ^ 2 := Nat.pow_le_pow_left hM 2
  have hpow : p ^ (2 ^ (r + 1)) = (p ^ (2 ^ r)) ^ 2 := pow_two_succ_sq p r
  exact le_trans (hpow ▸ hsq) hcell

/-- From `M < x^2` and the top lower window: `p^{2^{r-1}} < x`. -/
theorem cycle_top_pred_gt_pow {p n x r : ℕ}
    (hr : 1 ≤ r) (hM : p ^ (2 ^ r) ≤ n) (hMx : n < x ^ 2) :
    p ^ (2 ^ (r - 1)) < x := by
  have hlt : p ^ (2 ^ r) < x ^ 2 := lt_of_le_of_lt hM hMx
  have hpow : p ^ (2 ^ r) = (p ^ (2 ^ (r - 1))) ^ 2 := pow_two_pred_sq hr
  have : (p ^ (2 ^ (r - 1))) ^ 2 < x ^ 2 := by rwa [hpow] at hlt
  exact (Nat.pow_lt_pow_iff_left (by decide : (2 : ℕ) ≠ 0)).mp this

theorem follows_replicate_even_iter {n : ℕ} :
    ∀ r, follows n (List.replicate r Branch.even) →
      ∀ i < r, floorPower^[i] n % 2 = 0
  | 0, _, i, hi => by omega
  | r + 1, hf, i, hi => by
      rw [List.replicate_succ] at hf
      have he0 : n % 2 = 0 := hf.1
      cases i with
      | zero => exact he0
      | succ i =>
          have : floorPower^[i] (floorPower n) % 2 = 0 :=
            follows_replicate_even_iter r hf.2 i (by omega)
          simpa [Function.iterate_succ_apply] using this

/-- Three-level top: landing, odd predecessor, maximum. The two-step
odd-to-even law gives `T(M) < x`; even descent then gives `p ≤ T(M)`.
`T(M) = p` only when `r = 1`. -/
theorem cycle_top_three_level {n : ℕ} {w : List Branch}
    (hn : 2 ≤ n) (h : CycleMax n w) :
    ∃ r u p x, 1 ≤ r ∧
      w = List.replicate r Branch.even ++ u ∧
        p = floorPower^[r] n ∧
          x = floorPower^[w.length - 1] n ∧
            p % 2 = 1 ∧ 2 ≤ p ∧
              x % 2 = 1 ∧ 2 ≤ x ∧
                p < x ∧ x < n ∧
                  floorPower x = n ∧
                    image p u = n ∧
                      CycleItinerary p (u ++ List.replicate r Branch.even) := by
  have ⟨r, u, p, hr1, hw, hpdef, hpodd, hp2, hC, himg, _, _, _⟩ :=
    cycleMax_top_normal_form hn h
  have hi : w.length - 1 < w.length := by
    have : 2 ≤ w.length := cycleMax_length_ge_two hn h
    omega
  have hxodd := cycleMax_predecessor_odd hn h
  have hx2 : 2 ≤ floorPower^[w.length - 1] n :=
    cycleItinerary_iterate_ge_two hn h.1 hi
  have hxl := cycleMax_predecessor_lt hn h
  have hTx := cycleMax_predecessor_apply hn h
  have he := cycleMax_start_even hn h
  have htwo : floorPower n < floorPower^[w.length - 1] n := by
    have hsqrt : (floorPower^[w.length - 1] n ^ 3).sqrt % 2 = 0 := by
      have hfpeq :
          floorPower (floorPower^[w.length - 1] n) =
            (floorPower^[w.length - 1] n ^ 3).sqrt :=
        floorPower_odd_eq hxodd
      rw [← hfpeq, hTx]
      exact he
    have hstep := floorPower_odd_even_two_step_lt hx2 hxodd hsqrt
    rwa [hTx] at hstep
  have hrw : r < w.length := by
    have hwu : w.length = r + u.length := by
      simp [hw, List.length_append, List.length_replicate]
    cases u with
    | nil =>
        have : p = n := by simpa [image] using himg
        omega
    | cons _ _ =>
        simp [hwu]
  have hge : ∀ i < r, 2 ≤ floorPower^[i] n := fun i hi =>
    cycleItinerary_iterate_ge_two hn h.1 (lt_trans hi hrw)
  have heven : ∀ i < r, floorPower^[i] n % 2 = 0 := by
    have hf : follows n (List.replicate r Branch.even ++ u) := by
      simpa [hw] using h.1.1
    exact follows_replicate_even_iter r (follows_of_append_left hf)
  have hple : p ≤ floorPower n := by
    simpa [hpdef] using even_iter_le_first r heven hge hr1
  have hpx : p < floorPower^[w.length - 1] n := lt_of_le_of_lt hple htwo
  exact ⟨r, u, p, floorPower^[w.length - 1] n, hr1, hw, hpdef, rfl, hpodd, hp2,
    hxodd, hx2, hpx, hxl, hTx, himg, hC⟩

/-- Nested exact top cells at the maximum, its odd predecessor, and
the even-run landing. -/
theorem cycle_top_nested_preimage {n : ℕ} {w : List Branch}
    (hn : 2 ≤ n) (h : CycleMax n w) :
    ∃ r p x, 1 ≤ r ∧
      p = floorPower^[r] n ∧
        x = floorPower^[w.length - 1] n ∧
          p < x ∧ x < n ∧
            p ^ (2 ^ r) ≤ n ∧ n < (p + 1) ^ (2 ^ r) ∧
              n ^ 2 ≤ x ^ 3 ∧ x ^ 3 < (n + 1) ^ 2 := by
  have ⟨r, u, p, x, hr1, hw, hpdef, hxdef, _, _, _, _, hpx, hxn, _, _, _⟩ :=
    cycle_top_three_level hn h
  have hcell := cycle_top_predecessor_preimage hn h
  have heven : ∀ i < r, floorPower^[i] n % 2 = 0 := by
    have hf : follows n (List.replicate r Branch.even ++ u) := by
      simpa [hw] using h.1.1
    exact follows_replicate_even_iter r (follows_of_append_left hf)
  have hlo : p ^ (2 ^ r) ≤ n := by
    simpa [hpdef] using even_iter_pow_le r heven
  have hhi : n < (p + 1) ^ (2 ^ r) := by
    simpa [hpdef] using even_iter_lt_succ_pow r heven
  have hcell' : n ^ 2 ≤ x ^ 3 ∧ x ^ 3 < (n + 1) ^ 2 := by
    simpa [hxdef] using hcell
  exact ⟨r, p, x, hr1, hpdef, hxdef, hpx, hxn, hlo, hhi, hcell'⟩

/-- Scale constraint implied by the nested cells. Weaker than a
top-run obstruction: the integer region is not shown empty. -/
theorem cycle_top_scale_constraint {n : ℕ} {w : List Branch}
    (hn : 2 ≤ n) (h : CycleMax n w) :
    ∃ r p x, 1 ≤ r ∧
      p = floorPower^[r] n ∧
        x = floorPower^[w.length - 1] n ∧
          p ^ (2 ^ (r + 1)) ≤ x ^ 3 ∧
            n < x ^ 2 ∧
              p ^ (2 ^ (r - 1)) < x := by
  have ⟨r, p, x, hr1, hpdef, hxdef, _, _, hlo, _, hcell, _⟩ :=
    cycle_top_nested_preimage hn h
  have hx2 : 2 ≤ x := by
    have hi : w.length - 1 < w.length := by
      have : 2 ≤ w.length := cycleMax_length_ge_two hn h
      omega
    simpa [hxdef] using cycleItinerary_iterate_ge_two hn h.1 hi
  have hMx := cycle_top_max_lt_pred_sq hx2 hcell
  exact ⟨r, p, x, hr1, hpdef, hxdef, cycle_top_pred_scale hlo hcell, hMx,
    cycle_top_pred_gt_pow hr1 hlo hMx⟩

/-- The canonical peak block `OE^r` is formally contracting for `r ≥ 1`. -/
theorem peak_block_formally_contracting {r : ℕ} (hr : 1 ≤ r) :
    3 ^ oddCount (oddEvenBlock 1 r) < 2 ^ (oddEvenBlock 1 r).length := by
  have hlen : (oddEvenBlock 1 r).length = 1 + r := length_oddEvenBlock 1 r
  have hodd : oddCount (oddEvenBlock 1 r) = 1 := oddCount_oddEvenBlock 1 r
  have hgap : (3 : ℕ) ^ 1 < 2 ^ (1 + r) := by
    have h4 : (2 : ℕ) ^ 2 ≤ 2 ^ (1 + r) :=
      Nat.pow_le_pow_right (by decide : (1 : ℕ) ≤ 2) (by omega)
    omega
  simpa [hlen, hodd] using hgap

theorem peak_block_contracts {x r : ℕ} (hx : 2 ≤ x) (hr : 1 ≤ r)
    (hw : follows x (oddEvenBlock 1 r)) :
    image x (oddEvenBlock 1 r) < x :=
  contracting_odd_even_block_contracts hx
    (by
      have : (3 : ℕ) ^ 1 < 2 ^ (1 + r) := by
        have h4 : (2 : ℕ) ^ 2 ≤ 2 ^ (1 + r) :=
          Nat.pow_le_pow_right (by decide : (1 : ℕ) ≤ 2) (by omega)
        omega
      exact this)
    hw

/-- Every cycle maximum carries a canonical peak descent
`x --OE^r--> p` with `p < x`. Determined by the maximum, not by a
itinerary search. -/
theorem cycle_peak_descent {n : ℕ} {w : List Branch}
    (hn : 2 ≤ n) (h : CycleMax n w) :
    ∃ r p x, 1 ≤ r ∧
      p = floorPower^[r] n ∧
        x = floorPower^[w.length - 1] n ∧
          p < x ∧
            follows x (oddEvenBlock 1 r) ∧
              image x (oddEvenBlock 1 r) = p := by
  have ⟨r, u, p, x, hr1, hw, hpdef, hxdef, hpodd, _, hxodd, _, hpx, _, hTx,
      _, _⟩ := cycle_top_three_level hn h
  have heven : ∀ i < r, floorPower^[i] n % 2 = 0 := by
    have hf : follows n (List.replicate r Branch.even ++ u) := by
      simpa [hw] using h.1.1
    exact follows_replicate_even_iter r (follows_of_append_left hf)
  have hfE : follows n (List.replicate r Branch.even) :=
    follows_of_even_iter r heven
  have hform : oddEvenBlock 1 r = Branch.odd :: List.replicate r Branch.even := by
    simp [oddEvenBlock]
  have hf : follows x (oddEvenBlock 1 r) := by
    rw [hform]
    refine ⟨hxodd, ?_⟩
    simpa [hTx] using hfE
  have himg : image x (oddEvenBlock 1 r) = p := by
    rw [hform, image, hTx, image_eq_iterate, List.length_replicate, hpdef]
  exact ⟨r, p, x, hr1, hpdef, hxdef, hpx, hf, himg⟩

/-- Closed peak-ascent accounting: the peak lower cell plus the
ascent envelope from `p` to `x` give `3^{o+1} ≥ 2^{k+r+1}`. This is
the existing top-ascent law after appending the final `O`. -/
theorem peak_ascent_scale {p x : ℕ} {v : List Branch} {r : ℕ}
    (hp : 2 ≤ p) (hv : follows p v) (hx : image p v = x)
    (hpeak : p ^ (2 ^ (r + 1)) ≤ x ^ 3) :
    2 ^ (v.length + r + 1) ≤ 3 ^ (oddCount v + 1) := by
  have hxiter : floorPower^[v.length] p = x := by
    simpa [image_eq_iterate] using hx
  have hpow : x ^ (2 ^ v.length) ≤ p ^ (3 ^ oddCount v) := by
    simpa [hxiter] using power_bound_word hv
  have hexp : r + 1 + v.length = v.length + r + 1 := by omega
  have hL :
      (p ^ (2 ^ (r + 1))) ^ (2 ^ v.length) = p ^ (2 ^ (v.length + r + 1)) := by
    rw [← Nat.pow_mul, ← Nat.pow_add, hexp]
  have hleft : p ^ (2 ^ (v.length + r + 1)) ≤ (x ^ 3) ^ (2 ^ v.length) := by
    rw [← hL]
    exact Nat.pow_le_pow_left hpeak _
  have hmid : (x ^ 3) ^ (2 ^ v.length) = (x ^ (2 ^ v.length)) ^ 3 := by
    rw [(Nat.pow_mul x 3 (2 ^ v.length)).symm, Nat.mul_comm,
      Nat.pow_mul x (2 ^ v.length) 3]
  have hright : (x ^ (2 ^ v.length)) ^ 3 ≤ (p ^ (3 ^ oddCount v)) ^ 3 :=
    Nat.pow_le_pow_left hpow 3
  have hthree : (p ^ (3 ^ oddCount v)) ^ 3 = p ^ (3 ^ (oddCount v + 1)) := by
    rw [← Nat.pow_mul, Nat.mul_comm, three_pow_succ]
  have hle : p ^ (2 ^ (v.length + r + 1)) ≤ p ^ (3 ^ (oddCount v + 1)) :=
    le_trans hleft (le_trans (le_of_eq hmid) (le_trans hright (le_of_eq hthree)))
  exact
    (Nat.pow_le_pow_iff_right
        (lt_of_lt_of_le (by decide : (1 : ℕ) < 2) hp)).mp
      hle

/-- The peak predecessor is reached by a prefix of the top ascent.
Financing `OE^r` recovers the existing superquadratic law on that
ascent, not a stronger envelope. -/
theorem cycle_peak_finance {n : ℕ} {w : List Branch}
    (hn : 2 ≤ n) (h : CycleMax n w) :
    ∃ r v p x, 1 ≤ r ∧
      p = floorPower^[r] n ∧
        x = floorPower^[w.length - 1] n ∧
          p < x ∧
            follows p v ∧ image p v = x ∧
              follows x (oddEvenBlock 1 r) ∧
                image x (oddEvenBlock 1 r) = p ∧
                  p ^ (2 ^ (r + 1)) ≤ x ^ 3 ∧
                    2 ^ (v.length + r + 1) ≤ 3 ^ (oddCount v + 1) ∧
                      2 ^ ((v ++ [Branch.odd]).length + r) ≤
                        3 ^ oddCount (v ++ [Branch.odd]) := by
  have ⟨r, u, p, x, hr1, hw, hpdef, hxdef, _, hp2, hxodd, _, hpx, _, hTx,
      himg, hC⟩ := cycle_top_three_level hn h
  have hne : u ≠ [] := by
    intro hu
    have : p = n := by simpa [hu, image] using himg
    have he := cycleMax_start_even hn h
    omega
  have hsplit : u.dropLast ++ [u.getLast hne] = u :=
    List.dropLast_append_getLast hne
  set v := u.dropLast
  have hu : follows p u := follows_of_append_left (u := u) hC.1
  have hv : follows p v := by
    have : follows p (v ++ [u.getLast hne]) := by
      simpa [v, hsplit] using hu
    exact follows_of_append_left this
  have hulen : 1 ≤ u.length := by
    cases u with
    | nil => exact (hne rfl).elim
    | cons _ _ => simp
  have hx_as : x = floorPower^[u.length - 1] p := by
    have hwlen : w.length = r + u.length := by
      simp [hw, List.length_append, List.length_replicate]
    have hsum : w.length - 1 = (u.length - 1) + r := by omega
    have hiter :
        floorPower^[w.length - 1] n =
          floorPower^[u.length - 1] (floorPower^[r] n) := by
      rw [hsum]
      exact Function.iterate_add_apply floorPower (u.length - 1) r n
    rw [hxdef, hpdef, hiter]
  have himgv : image p v = x := by
    have hlenv : v.length = u.length - 1 := by simp [v]
    rw [image_eq_iterate, hlenv, hx_as]
  have heven : ∀ i < r, floorPower^[i] n % 2 = 0 := by
    have hf : follows n (List.replicate r Branch.even ++ u) := by
      simpa [hw] using h.1.1
    exact follows_replicate_even_iter r (follows_of_append_left hf)
  have hfE : follows n (List.replicate r Branch.even) :=
    follows_of_even_iter r heven
  have hform : oddEvenBlock 1 r = Branch.odd :: List.replicate r Branch.even := by
    simp [oddEvenBlock]
  have hfP : follows x (oddEvenBlock 1 r) := by
    rw [hform]
    refine ⟨hxodd, ?_⟩
    simpa [hTx] using hfE
  have himgP : image x (oddEvenBlock 1 r) = p := by
    rw [hform, image, hTx, image_eq_iterate, List.length_replicate, hpdef]
  have hcell := cycle_top_predecessor_preimage hn h
  have hlo : p ^ (2 ^ r) ≤ n := by
    simpa [hpdef] using even_iter_pow_le r heven
  have hcube : n ^ 2 ≤ x ^ 3 := by
    simpa [hxdef] using hcell.1
  have hpeak : p ^ (2 ^ (r + 1)) ≤ x ^ 3 := cycle_top_pred_scale hlo hcube
  have hfin := peak_ascent_scale hp2 hv himgv hpeak
  have hrep : 2 ^ ((v ++ [Branch.odd]).length + r) ≤
      3 ^ oddCount (v ++ [Branch.odd]) := by
    have hlen : (v ++ [Branch.odd]).length = v.length + 1 := by
      simp [List.length_append]
    have hodd : oddCount (v ++ [Branch.odd]) = oddCount v + 1 := by
      simp [oddCount_append]
    have hidx : v.length + r + 1 = v.length + 1 + r := by omega
    simpa [hlen, hodd, hidx] using hfin
  exact ⟨r, v, p, x, hr1, hpdef, hxdef, hpx, hv, himgv, hfP, himgP, hpeak,
    hfin, hrep⟩

/-- Dual of `exists_first_odd_iterate`. -/
theorem exists_first_even_iterate {n t : ℕ}
    (h0 : n % 2 = 1) (ht : 1 ≤ t)
    (heven : floorPower^[t] n % 2 = 0) :
    ∃ a, 1 ≤ a ∧ a ≤ t ∧
      (∀ i < a, floorPower^[i] n % 2 = 1) ∧
      floorPower^[a] n % 2 = 0 := by
  let P : ℕ → Prop :=
    fun a => 1 ≤ a ∧ a ≤ t ∧ floorPower^[a] n % 2 = 0
  have hP : ∃ a, P a := ⟨t, ht, le_rfl, heven⟩
  let a := Nat.find hP
  have ha : P a := Nat.find_spec hP
  refine ⟨a, ha.1, ha.2.1, ?_, ha.2.2⟩
  intro i hi
  have hnot : ¬P i := Nat.find_min hP hi
  cases i with
  | zero => exact h0
  | succ i =>
      have hi1 : 1 ≤ i + 1 := Nat.succ_le_succ (Nat.zero_le i)
      have hi2 : i + 1 ≤ t :=
        Nat.le_of_lt (lt_of_lt_of_le hi ha.2.1)
      have : ¬floorPower^[i + 1] n % 2 = 0 := fun h =>
        hnot ⟨hi1, hi2, h⟩
      rcases Nat.mod_two_eq_zero_or_one (floorPower^[i + 1] n) with he | ho
      · exact (this he).elim
      · exact ho

/-- Top-window lower bound is strict: `p` odd and `M` even forbid
equality `M = p^{2^r}`. Parity, not an envelope. -/
theorem cycle_top_window_strict {p M r : ℕ}
    (hp : p % 2 = 1) (hM : M % 2 = 0)
    (hlo : p ^ (2 ^ r) ≤ M) :
    p ^ (2 ^ r) < M := by
  refine lt_of_le_of_ne hlo ?_
  intro heq
  have hodd : (p ^ (2 ^ r)) % 2 = 1 := odd_iff_pow_two_depth_odd.mp hp
  rw [heq] at hodd
  omega

theorem cycleMax_iterate_le {n : ℕ} {w : List Branch} (h : CycleMax n w)
    (j : ℕ) : floorPower^[j] n ≤ n := by
  have hlen : 1 ≤ w.length := h.1.2.2
  rw [cycle_iterate_mod h.1]
  exact cycleMax_le h
    (Nat.mod_lt _ (lt_of_lt_of_le (by decide : (0 : ℕ) < 1) hlen))

/-- A cycle maximum cannot also be a cycle minimum. -/
theorem cycleMax_not_cycleMin {n : ℕ} {w : List Branch}
    (hn : 2 ≤ n) (h : CycleMax n w) : ¬CycleMin n w := by
  intro hm
  have he := cycleMax_start_even hn h
  have ho := cycleMin_start_odd hn hm
  omega

/-- On a cycle maximum the rotated minimum satisfies `m^2 < M`.
The laboratory sharpening is `cycleMax_min_succ_sq_le`. -/
theorem cycleMax_min_sq_lt {n : ℕ} {w : List Branch} {k : ℕ}
    (hn : 2 ≤ n) (h : CycleMax n w) (hk : k < w.length)
    (hmin : CycleMin (floorPower^[k] n) (rotateItinerary w k)) :
    floorPower^[k] n ^ 2 < n := by
  have hk0 : k ≠ 0 := by
    intro hk0
    have : CycleMin n w := by
      simpa [hk0, rotateItinerary] using hmin
    exact cycleMax_not_cycleMin hn h this
  have hm2 : 2 ≤ floorPower^[k] n := cycleItinerary_iterate_ge_two hn h.1 hk
  have ⟨i, hi, hmax, _, hgt⟩ :=
    cycleMin_max_gt_sq (n := floorPower^[k] n) hm2 hmin
  have hlen : (rotateItinerary w k).length = w.length := rotateItinerary_length w k
  have hle : floorPower^[i] (floorPower^[k] n) ≤ n := by
    have himg : floorPower^[i] (floorPower^[k] n) = floorPower^[k + i] n := by
      simpa [Nat.add_comm] using
        (Function.iterate_add_apply floorPower i k n).symm
    simpa [himg] using cycleMax_iterate_le h (k + i)
  have hfrom : floorPower^[w.length - k] (floorPower^[k] n) = n := by
    have hsum : w.length - k + k = w.length := Nat.sub_add_cancel (Nat.le_of_lt hk)
    have hiter := Function.iterate_add_apply floorPower (w.length - k) k n
    rw [← hiter, hsum, cycle_iterate_period h.1]
  have hidx : w.length - k < (rotateItinerary w k).length := by
    rw [hlen]
    omega
  have hnle : n ≤ floorPower^[i] (floorPower^[k] n) := by
    simpa [hfrom] using hmax (w.length - k) hidx
  have heq : floorPower^[i] (floorPower^[k] n) = n := le_antisymm hle hnle
  simpa [heq] using hgt

/-- Distinguished cycle order: minimum, top landing, peak predecessor,
maximum. The rotation witness is included so the laboratory
sharpening `(m+1)^2 ≤ M` is a one-line corollary. Scale
compositions beyond this package are envelope repackaging. -/
theorem cycle_distinguished_order {n : ℕ} {w : List Branch}
    (hn : 2 ≤ n) (h : CycleMax n w) :
    ∃ k m p x r, k < w.length ∧
      CycleMin (floorPower^[k] n) (rotateItinerary w k) ∧
      m = floorPower^[k] n ∧
      2 ≤ m ∧ 2 ≤ p ∧
      m % 2 = 1 ∧ p % 2 = 1 ∧
        m ≤ p ∧ p < x ∧ x < n ∧
          m ^ 2 < n ∧
            1 ≤ r ∧
              p ^ (2 ^ r) < n ∧ n < (p + 1) ^ (2 ^ r) ∧
                n ^ 2 ≤ x ^ 3 ∧ x ^ 3 < (n + 1) ^ 2 ∧
                  m ^ 4 < x ^ 3 := by
  have ⟨r, u, p, x, hr1, hw, hpdef, hxdef, hpodd, hp2, _, _, hpx, hxn, _,
      himg, hC⟩ := cycle_top_three_level hn h
  have ⟨k, hk, hmin⟩ := exists_cycleMin hn h.1
  have hm : 2 ≤ floorPower^[k] n := cycleItinerary_iterate_ge_two hn h.1 hk
  have hmodd := cycleMin_start_odd (n := floorPower^[k] n) hm hmin
  have hMsq := cycleMax_min_sq_lt hn h hk hmin
  have heven : ∀ i < r, floorPower^[i] n % 2 = 0 := by
    have hf : follows n (List.replicate r Branch.even ++ u) := by
      simpa [hw] using h.1.1
    exact follows_replicate_even_iter r (follows_of_append_left hf)
  have hlo : p ^ (2 ^ r) ≤ n := by
    simpa [hpdef] using even_iter_pow_le r heven
  have hhi : n < (p + 1) ^ (2 ^ r) := by
    simpa [hpdef] using even_iter_lt_succ_pow r heven
  have hwin := cycle_top_window_strict hpodd (cycleMax_start_even hn h) hlo
  have hcell := cycle_top_predecessor_preimage hn h
  have hcell' : n ^ 2 ≤ x ^ 3 ∧ x ^ 3 < (n + 1) ^ 2 := by
    simpa [hxdef] using hcell
  have hrlt : r < w.length := by
    have hwu : w.length = r + u.length := by
      simp [hw, List.length_append, List.length_replicate]
    cases u with
    | nil =>
        have : p = n := by simpa [image] using himg
        omega
    | cons _ _ =>
        simp [hwu]
  have hm_le_p : floorPower^[k] n ≤ p := by
    have : floorPower^[k] n ≤ floorPower^[r] n :=
      cycleMin_le_cycle_state h.1 hk hrlt hmin
    simpa [hpdef] using this
  have hfourth : floorPower^[k] n ^ 4 < x ^ 3 := by
    have hpow : (floorPower^[k] n ^ 2) ^ 2 < n ^ 2 :=
      Nat.pow_lt_pow_left hMsq (by decide : (2 : ℕ) ≠ 0)
    have h4 : floorPower^[k] n ^ 4 = (floorPower^[k] n ^ 2) ^ 2 := by
      rw [← Nat.pow_mul]
    have : floorPower^[k] n ^ 4 < n ^ 2 := by
      simpa [h4] using hpow
    exact lt_of_lt_of_le this hcell'.1
  exact ⟨k, floorPower^[k] n, p, x, r, hk, hmin, rfl, hm, hp2, hmodd, hpodd,
    hm_le_p, hpx, hxn, hMsq, hr1, hwin, hhi, hcell'.1, hcell'.2, hfourth⟩

/-!
## Exact local remainders on a cycle

`branchDefect` is the floor remainder the envelope forgets. The path
sums below are not a remainder-dynamics object.
-/

def pathDefectSum (n : ℕ) : List Branch → ℕ
  | [] => 0
  | b :: w => branchDefect b n + pathDefectSum (floorPower n) w

def pathPows (n : ℕ) : List Branch → ℕ
  | [] => 0
  | .even :: w => n + pathPows (floorPower n) w
  | .odd :: w => n ^ 3 + pathPows (floorPower n) w

def pathSquares (n : ℕ) : List Branch → ℕ
  | [] => 0
  | _ :: w => n ^ 2 + pathSquares (floorPower n) w

def pathNextSquares (n : ℕ) : List Branch → ℕ
  | [] => 0
  | _ :: w => floorPower n ^ 2 + pathNextSquares (floorPower n) w

def pathEvenGaps (n : ℕ) : List Branch → ℕ
  | [] => 0
  | .even :: w => n * (n - 1) + pathEvenGaps (floorPower n) w
  | .odd :: w => pathEvenGaps (floorPower n) w

def pathOddGaps (n : ℕ) : List Branch → ℕ
  | [] => 0
  | .odd :: w => n ^ 2 * (n - 1) + pathOddGaps (floorPower n) w
  | .even :: w => pathOddGaps (floorPower n) w

theorem follows_singleton_of_get {n : ℕ} {w : List Branch}
    (hw : follows n w) {i : ℕ} (hi : i < w.length) :
    follows (floorPower^[i] n) [w[i]] := by
  rcases hbranch : w[i] with _ | _
  · exact ⟨follows_get_even w hw i hi hbranch, trivial⟩
  · exact ⟨follows_get_odd w hw i hi hbranch, trivial⟩

theorem cycle_remainder_eq {n : ℕ} {w : List Branch} {i : ℕ}
    (h : CycleItinerary n w) (hi : i < w.length) :
    (floorPower^[i] n) ^ branchExp w[i] =
      (floorPower^[i + 1] n) ^ 2 +
        branchDefect w[i] (floorPower^[i] n) := by
  have hadd := branchDefect_add (follows_singleton_of_get h.1 hi)
  have hiter : floorPower (floorPower^[i] n) = floorPower^[i + 1] n :=
    (Function.iterate_succ_apply' floorPower i n).symm
  simpa [hiter] using hadd

theorem cycle_remainder_lt {n : ℕ} {w : List Branch} {i : ℕ}
    (h : CycleItinerary n w) (hi : i < w.length) :
    branchDefect w[i] (floorPower^[i] n) <
      2 * floorPower^[i + 1] n + 1 := by
  have hlt := branchDefect_lt (follows_singleton_of_get h.1 hi)
  have hiter : floorPower (floorPower^[i] n) = floorPower^[i + 1] n :=
    (Function.iterate_succ_apply' floorPower i n).symm
  simpa [hiter] using hlt

theorem pathPows_eq_next_add_defects {n : ℕ} :
    ∀ {w}, follows n w →
      pathPows n w = pathNextSquares n w + pathDefectSum n w
  | [], _ => by simp [pathPows, pathNextSquares, pathDefectSum]
  | .even :: rest, h => by
      have ih := pathPows_eq_next_add_defects (n := floorPower n) h.2
      have hadd : n = floorPower n ^ 2 + branchDefect .even n := by
        simpa [branchExp, pow_one] using
          branchDefect_add (b := .even) ⟨h.1, trivial⟩
      simp only [pathPows, pathNextSquares, pathDefectSum]
      omega
  | .odd :: rest, h => by
      have ih := pathPows_eq_next_add_defects (n := floorPower n) h.2
      have hadd : n ^ 3 = floorPower n ^ 2 + branchDefect .odd n := by
        simpa [branchExp] using branchDefect_add (b := .odd) ⟨h.1, trivial⟩
      simp only [pathPows, pathNextSquares, pathDefectSum]
      omega

theorem pathPows_add_evenGaps (n : ℕ) :
    ∀ w, pathPows n w + pathEvenGaps n w =
      pathSquares n w + pathOddGaps n w
  | [] => by simp [pathPows, pathEvenGaps, pathSquares, pathOddGaps]
  | .even :: rest => by
      have ih := pathPows_add_evenGaps (floorPower n) rest
      have hsq : n + n * (n - 1) = n ^ 2 := by
        cases n with
        | zero => simp
        | succ n =>
            simp [pow_two]
            ring
      simp only [pathPows, pathEvenGaps, pathSquares, pathOddGaps]
      omega
  | .odd :: rest => by
      have ih := pathPows_add_evenGaps (floorPower n) rest
      have hcub : n ^ 3 = n ^ 2 + n ^ 2 * (n - 1) := by
        cases n with
        | zero => simp
        | succ k =>
            have : k + 1 - 1 = k := Nat.add_sub_cancel k 1
            simp [this]
            ring
      simp only [pathPows, pathEvenGaps, pathSquares, pathOddGaps]
      omega

theorem pathNextSquares_add_sq (n : ℕ) :
    ∀ w, pathNextSquares n w + n ^ 2 =
      pathSquares n w + image n w ^ 2
  | [] => by simp [pathNextSquares, pathSquares, image]
  | _b :: rest => by
      have ih := pathNextSquares_add_sq (floorPower n) rest
      simp only [pathNextSquares, pathSquares, image]
      calc
        floorPower n ^ 2 + pathNextSquares (floorPower n) rest + n ^ 2
            = pathNextSquares (floorPower n) rest + floorPower n ^ 2 + n ^ 2 := by
              omega
        _ = pathSquares (floorPower n) rest + image (floorPower n) rest ^ 2 + n ^ 2 := by
            rw [ih]
        _ = n ^ 2 + pathSquares (floorPower n) rest +
              image (floorPower n) rest ^ 2 := by
            omega

theorem cycle_pathNextSquares_eq {n : ℕ} {w : List Branch}
    (h : CycleItinerary n w) :
    pathNextSquares n w = pathSquares n w := by
  have heq := pathNextSquares_add_sq n w
  rw [h.2.1] at heq
  exact Nat.add_right_cancel heq

/-- Cyclic closure keeps the remainders: `∑ρ + even gaps = odd gaps`.
This is not the exponent envelope. -/
theorem cycle_remainder_balance {n : ℕ} {w : List Branch}
    (h : CycleItinerary n w) :
    pathDefectSum n w + pathEvenGaps n w = pathOddGaps n w := by
  have hpow := pathPows_eq_next_add_defects h.1
  have hsq := cycle_pathNextSquares_eq h
  have hgap := pathPows_add_evenGaps n w
  rw [hpow, hsq, Nat.add_assoc] at hgap
  exact Nat.add_left_cancel hgap

/-- Dropping every remainder recovers the ordinary itinerary envelope. -/
theorem cycle_remainders_project_to_envelope {n : ℕ} {w : List Branch}
    (h : CycleItinerary n w) :
    (floorPower^[w.length] n) ^ (2 ^ w.length) ≤
      n ^ (3 ^ oddCount w) := by
  simpa [image_eq_iterate] using power_bound_word h.1

theorem localsTight_of_defects_zero {n : ℕ} :
    ∀ {w}, follows n w →
      (∀ i, (hi : i < w.length) →
        branchDefect w[i] (floorPower^[i] n) = 0) →
          localsTight n w
  | [], _, _ => trivial
  | b :: rest, hw, hz => by
      cases b with
      | even =>
          have hf : follows n [.even] := ⟨hw.1, trivial⟩
          have h0 : branchDefect .even n = 0 := by
            simpa [List.getElem_cons_zero] using hz 0 (Nat.succ_pos _)
          refine ⟨(branchDefect_eq_zero_iff_localTight hf).mp h0, ?_⟩
          refine localsTight_of_defects_zero (n := floorPower n) hw.2 ?_
          intro i hi
          have hi' : i + 1 < (Branch.even :: rest).length := by
            simpa [List.length_cons] using Nat.succ_lt_succ hi
          have hzi := hz (i + 1) hi'
          simpa [List.getElem_cons_succ, iterate_cons] using hzi
      | odd =>
          have hf : follows n [.odd] := ⟨hw.1, trivial⟩
          have h0 : branchDefect .odd n = 0 := by
            simpa [List.getElem_cons_zero] using hz 0 (Nat.succ_pos _)
          refine ⟨(branchDefect_eq_zero_iff_localTight hf).mp h0, ?_⟩
          refine localsTight_of_defects_zero (n := floorPower n) hw.2 ?_
          intro i hi
          have hi' : i + 1 < (Branch.odd :: rest).length := by
            simpa [List.length_cons] using Nat.succ_lt_succ hi
          have hzi := hz (i + 1) hi'
          simpa [List.getElem_cons_succ, iterate_cons] using hzi

/-- All-zero remainders are incompatible with a nontrivial cycle. -/
theorem cycle_not_localsTight {n : ℕ} {w : List Branch}
    (hn : 2 ≤ n) (h : CycleItinerary n w) : ¬localsTight n w := by
  intro ht
  have hmono : isMonochrome w := by
    by_contra hmix
    exact not_localsTight_of_nonmonochrome h.1 hmix ht
  rcases hmono with he | ho
  · have hwE : follows n (List.replicate w.length Branch.even) := by
      rw [← he]
      exact h.1
    have hlt := even_itinerary_contracts hn h.2.2 hwE
    have himg := cycle_iterate_period h
    rw [himg] at hlt
    exact (lt_irrefl n) hlt
  · have hwO : follows n (List.replicate w.length Branch.odd) := by
      rw [← ho]
      exact h.1
    have hodd := follows_replicate_odd_head h.2.2 hwO
    have hn3 : 3 ≤ n := by
      have : n ≠ 2 := fun h2 =>
        (by decide : ¬(2 : ℕ) % 2 = 1) (h2 ▸ hodd)
      omega
    have hgt := odd_itinerary_expands hn3 h.2.2 hwO
    have himg := cycle_iterate_period h
    rw [himg] at hgt
    exact (lt_irrefl n) hgt

theorem cycle_exists_pos_remainder {n : ℕ} {w : List Branch}
    (hn : 2 ≤ n) (h : CycleItinerary n w) :
    ∃ i, ∃ hi : i < w.length,
      0 < branchDefect (w[i]'hi) (floorPower^[i] n) := by
  by_contra hnone
  have hall : ∀ i, (hi : i < w.length) →
      branchDefect (w[i]'hi) (floorPower^[i] n) = 0 := by
    intro i hi
    cases hρ : branchDefect (w[i]'hi) (floorPower^[i] n) with
    | zero => rfl
    | succ k =>
        exact (hnone ⟨i, hi, by simp [hρ]⟩).elim
  exact cycle_not_localsTight hn h (localsTight_of_defects_zero h.1 hall)

/-- Peak odd remainder is positive: `M` even and `x` odd forbid `x^3 = M^2`. -/
theorem cycleMax_pred_cube_strict {n : ℕ} {w : List Branch}
    (hn : 2 ≤ n) (h : CycleMax n w) :
    n ^ 2 < (floorPower^[w.length - 1] n) ^ 3 := by
  have hcell := cycle_top_predecessor_preimage hn h
  refine lt_of_le_of_ne hcell.1 ?_
  intro heq
  have hx := cycleMax_predecessor_odd hn h
  have hM := cycleMax_start_even hn h
  have hx3 : ((floorPower^[w.length - 1] n) ^ 3) % 2 = 1 := by
    simp [Nat.pow_mod, hx]
  have hM2 : (n ^ 2) % 2 = 0 := by
    simp [Nat.pow_mod, hM]
  have : (n ^ 2) % 2 = 1 := by
    simpa [heq] using hx3
  omega

theorem cycle_peak_odd_remainder_pos {n : ℕ} {w : List Branch}
    (hn : 2 ≤ n) (h : CycleMax n w) :
    0 < localDefectOdd (floorPower^[w.length - 1] n) := by
  have ho := cycleMax_predecessor_odd hn h
  have hTx := cycleMax_predecessor_apply hn h
  have hlt := cycleMax_pred_cube_strict hn h
  have hadd := localDefectOdd_add ho
  have : floorPower (floorPower^[w.length - 1] n) = n := hTx
  have hρ : localDefectOdd (floorPower^[w.length - 1] n) =
      (floorPower^[w.length - 1] n) ^ 3 - n ^ 2 := by
    simp [localDefectOdd, this]
  have hpos :
      n ^ 2 < (floorPower^[w.length - 1] n) ^ 3 := hlt
  omega

end Problems.Juggler
