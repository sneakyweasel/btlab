import Problems.Juggler.ItineraryStats
import Problems.Juggler.Minimal

namespace Problems.Juggler

/-!
# Scale barriers on a minimal non-1 trajectory

Exact power-envelope specializations of `OE` and `(OE)^r`, then the
minimal-counterexample scale barrier. Not a frequency theorem, not a
halt theorem, and not a new energy.
-/

/-- One realized `OE` block: `T^2(x)^4 ≤ x^3`. -/
theorem oe_block_scale {x : ℕ} (hw : follows x itineraryOE) :
    image x itineraryOE ^ 4 ≤ x ^ 3 := by
  have h := power_bound_word hw
  simpa [itineraryOE, image_eq_iterate] using h

theorem oe_block_contracts {x : ℕ} (hx : 2 ≤ x) (hw : follows x itineraryOE) :
    image x itineraryOE < x := by
  have hgap : (3 : ℕ) ^ oddCount itineraryOE < 2 ^ itineraryOE.length := by
    simp [itineraryOE]
  have h := power_bound_contracts hx hw hgap
  simpa [itineraryOE, image_eq_iterate] using h

theorem repeated_oe_scale_barrier {n x k r : ℕ} (h : MinimalNonTerm n)
    (hk : floorPower^[k] n = x) (hw : follows x (repeatedOE r)) :
    n ^ (4 ^ r) ≤ x ^ (3 ^ r) := by
  have hexit : floorPower^[k + 2 * r] n = floorPower^[2 * r] x := by
    rw [iterate_add_right, hk]
  have hge : n ≤ floorPower^[2 * r] x :=
    minimal_nonterm_ge_of_not_reachesOne h
      (by
        rw [← hexit]
        exact floorPower_iterate_pos h.pos (k + 2 * r))
      (trajectory_not_reachesOne h hexit)
  exact le_trans (Nat.pow_le_pow_left hge (4 ^ r)) (repeated_oe_scale hw)

theorem repeated_oe_scale_barrier_of_image {n : ℕ} {u : List Branch} {r : ℕ}
    (h : MinimalNonTerm n) (_hu : follows n u)
    (hw : follows (image n u) (repeatedOE r)) :
    n ^ (4 ^ r) ≤ image n u ^ (3 ^ r) :=
  repeated_oe_scale_barrier h (image_eq_iterate n u).symm hw

theorem oe_requires_scale {n x k : ℕ} (h : MinimalNonTerm n)
    (hk : floorPower^[k] n = x) (hw : follows x itineraryOE) : n ^ 4 ≤ x ^ 3 := by
  have hrep : follows x (repeatedOE 1) := by
    simpa [repeatedOE, itineraryOE] using hw
  simpa using repeated_oe_scale_barrier (r := 1) h hk hrep

/-- `(OE)^r` cannot start at the minimal state itself: the first image
is odd. Not a frequency theorem. -/
theorem minimal_nonterm_not_repeated_oe {n r : ℕ} (h : MinimalNonTerm n)
    (hr : 1 ≤ r) : ¬follows n (repeatedOE r) := by
  intro hw
  cases r with
  | zero => omega
  | succ r =>
      have hOE : follows n itineraryOE :=
        follows_of_append_left (u := itineraryOE) hw
      have heven : floorPower n % 2 = 0 := hOE.2.1
      have hodd := minimal_nonterm_odd_image_odd h
      omega

/-!
# Odd-run financing of the first legal even residual

If a later state `x` realizes `O^a E^b` on a `MinimalNonTerm` trajectory,
then `n ^ (2 ^ (a + b)) ≤ x ^ (3 ^ a)`. The start itself cannot meet
an even residual before `OOE`. Not a frequency theorem and not a halt
theorem.
-/

theorem pow_add_two (a b : ℕ) : 2 ^ (a + b) = 2 ^ b * 2 ^ a := by
  rw [Nat.pow_add, mul_comm]

/-- Isolated odd prefix envelope: `T^a(x)^{2^a} ≤ x^{3^a}`. -/
theorem odd_run_power_bound {x a : ℕ}
    (hw : follows x (List.replicate a Branch.odd)) :
    (floorPower^[a] x) ^ (2 ^ a) ≤ x ^ (3 ^ a) := by
  have h := power_bound_word hw
  simpa [List.length_replicate, oddCount_replicate_odd] using h

/-- Growth pays for collapse: `O^a E^b` on a minimal non-1 trajectory
requires `n ^ (2 ^ (a + b)) ≤ x ^ (3 ^ a)`. -/
theorem odd_even_block_scale_barrier {n x k a b : ℕ}
    (h : MinimalNonTerm n) (hk : floorPower^[k] n = x)
    (hw : follows x (oddEvenBlock a b)) :
    n ^ (2 ^ (a + b)) ≤ x ^ (3 ^ a) := by
  have hodd := follows_of_append_left (u := List.replicate a Branch.odd) hw
  have heven := follows_of_append_right (u := List.replicate a Branch.odd) hw
  have hxa : floorPower^[k + a] n = image x (List.replicate a Branch.odd) := by
    rw [iterate_add_right, hk, image_eq_iterate, List.length_replicate]
  have hbar := even_run_scale_barrier h hxa heven
  have hpow := odd_run_power_bound hodd
  have hexp : n ^ (2 ^ (a + b)) = (n ^ (2 ^ b)) ^ (2 ^ a) := by
    rw [pow_add_two, Nat.pow_mul]
  rw [hexp]
  have hmid :
      (n ^ (2 ^ b)) ^ (2 ^ a) ≤
        (floorPower^[a] x) ^ (2 ^ a) :=
    Nat.pow_le_pow_left (by
      simpa [image_eq_iterate, List.length_replicate] using hbar) _
  exact le_trans hmid hpow

/-- First legal even residual after an odd run: `n ^ (2 ^ (a + 1)) ≤ x ^ (3 ^ a)`. -/
theorem odd_run_financing_scale_barrier {n x k a : ℕ}
    (h : MinimalNonTerm n) (hk : floorPower^[k] n = x)
    (hw : follows x (oddEvenBlock a 1)) :
    n ^ (2 ^ (a + 1)) ≤ x ^ (3 ^ a) :=
  odd_even_block_scale_barrier (b := 1) h hk hw

theorem odd_run_financing_scale_barrier_of_image {n : ℕ} {u : List Branch} {a : ℕ}
    (h : MinimalNonTerm n) (_hu : follows n u)
    (hw : follows (image n u) (oddEvenBlock a 1)) :
    n ^ (2 ^ (a + 1)) ≤ image n u ^ (3 ^ a) :=
  odd_run_financing_scale_barrier h (image_eq_iterate n u).symm hw

/-- At the minimal start, an even residual cannot occur before `OOE`.
Later odd runs may be shorter if the entry is already large. -/
theorem initial_even_not_before_ooe {n a : ℕ} (h : MinimalNonTerm n)
    (hw : follows n (oddEvenBlock a 1)) : 2 ≤ a := by
  have hfin := odd_run_financing_scale_barrier (k := 0) h rfl hw
  have hn : 1 < n := lt_of_lt_of_le (by decide : (1 : ℕ) < 12)
    (minimal_nonterm_ge_twelve h)
  have hexp : 2 ^ (a + 1) ≤ 3 ^ a :=
    (Nat.pow_le_pow_iff_right hn).mp hfin
  exact two_pow_succ_le_three_pow_iff.mp hexp

/-!
# Repeated `O^a E^b` scale budget

If a later state realizes `r` consecutive copies of a fixed block
`O^a E^b`, the itinerary envelope and minimality give
`n ^ (2 ^ (r * (a + b))) ≤ x ^ (3 ^ (a * r))`.

Formally contracting blocks (`3^a < 2^{a+b}`) contract for `x ≥ 2`
and cannot start at a `MinimalNonTerm` state. Later copies may still
stay above `n`. Not a frequency theorem and not a halt theorem.
-/

def repeatedOddEven (a b : ℕ) : ℕ → List Branch
  | 0 => []
  | r + 1 => oddEvenBlock a b ++ repeatedOddEven a b r

theorem repeatedOddEven_zero (a b : ℕ) : repeatedOddEven a b 0 = [] :=
  rfl

theorem repeatedOddEven_succ (a b r : ℕ) :
    repeatedOddEven a b (r + 1) = oddEvenBlock a b ++ repeatedOddEven a b r :=
  rfl

theorem length_repeatedOddEven (a b : ℕ) :
    ∀ r, (repeatedOddEven a b r).length = r * (a + b)
  | 0 => by simp [repeatedOddEven]
  | r + 1 => by
      rw [repeatedOddEven_succ, List.length_append, length_oddEvenBlock,
        length_repeatedOddEven]
      ring

theorem oddCount_repeatedOddEven (a b : ℕ) :
    ∀ r, oddCount (repeatedOddEven a b r) = r * a
  | 0 => by simp [repeatedOddEven]
  | r + 1 => by
      rw [repeatedOddEven_succ, oddCount_append, oddCount_oddEvenBlock,
        oddCount_repeatedOddEven]
      ring

/-- No nonempty `O^a E^b` has formal exponent `1`. -/
theorem odd_even_exponents_ne {a b : ℕ} (h : 1 ≤ a + b) :
    3 ^ a ≠ 2 ^ (a + b) := by
  intro heq
  have hodd : 3 ^ a % 2 = 1 := three_pow_odd a
  have heven : 2 ^ (a + b) % 2 = 0 := two_pow_even_of_pos h
  rw [heq] at hodd
  omega

theorem contracting_gap_repeat {a b r : ℕ}
    (hgap : 3 ^ a < 2 ^ (a + b)) (hr : 1 ≤ r) :
    3 ^ (a * r) < 2 ^ (r * (a + b)) := by
  have hpow : (3 ^ a) ^ r < (2 ^ (a + b)) ^ r :=
    Nat.pow_lt_pow_left hgap (Nat.one_le_iff_ne_zero.mp hr)
  have hL : (3 ^ a) ^ r = 3 ^ (a * r) := (Nat.pow_mul 3 a r).symm
  have hR : (2 ^ (a + b)) ^ r = 2 ^ ((a + b) * r) :=
    (Nat.pow_mul 2 (a + b) r).symm
  have hR' : (a + b) * r = r * (a + b) := Nat.mul_comm _ _
  rw [hL, hR, hR'] at hpow
  exact hpow

/-- Repeated-block envelope: `T^{r|B|}(x)^{2^{r|B|}} ≤ x^{3^{r #O(B)}}`. -/
theorem repeated_block_power_bound {x a b r : ℕ}
    (hw : follows x (repeatedOddEven a b r)) :
    (floorPower^[r * (a + b)] x) ^ (2 ^ (r * (a + b))) ≤
      x ^ (3 ^ (a * r)) := by
  have h := power_bound_word hw
  have hlen := length_repeatedOddEven a b r
  have hodd := oddCount_repeatedOddEven a b r
  have hmul : r * a = a * r := Nat.mul_comm _ _
  rw [hlen, hodd, hmul] at h
  exact h

/-- A later `(O^a E^b)^r` segment on a minimal non-1 trajectory requires
`n^{2^{r(a+b)}} ≤ x^{3^{a r}}`. -/
theorem repeated_odd_even_scale_barrier {n x k a b r : ℕ}
    (h : MinimalNonTerm n) (hk : floorPower^[k] n = x)
    (hw : follows x (repeatedOddEven a b r)) :
    n ^ (2 ^ (r * (a + b))) ≤ x ^ (3 ^ (a * r)) := by
  have hexit :
      floorPower^[k + r * (a + b)] n = floorPower^[r * (a + b)] x := by
    rw [iterate_add_right, hk]
  have hge : n ≤ floorPower^[r * (a + b)] x :=
    minimal_nonterm_ge_of_not_reachesOne h
      (by
        rw [← hexit]
        exact floorPower_iterate_pos h.pos (k + r * (a + b)))
      (trajectory_not_reachesOne h hexit)
  exact le_trans (Nat.pow_le_pow_left hge _) (repeated_block_power_bound hw)

theorem repeated_odd_even_scale_barrier_of_image {n : ℕ} {u : List Branch}
    {a b r : ℕ} (h : MinimalNonTerm n) (_hu : follows n u)
    (hw : follows (image n u) (repeatedOddEven a b r)) :
    n ^ (2 ^ (r * (a + b))) ≤ image n u ^ (3 ^ (a * r)) :=
  repeated_odd_even_scale_barrier h (image_eq_iterate n u).symm hw

/-- One formally contracting block contracts for `x ≥ 2`. This is
`T_B(x) < x`, not `T_B(x) < n`. -/
theorem contracting_odd_even_block_contracts {x a b : ℕ}
    (hx : 2 ≤ x) (hgap : 3 ^ a < 2 ^ (a + b))
    (hw : follows x (oddEvenBlock a b)) :
    image x (oddEvenBlock a b) < x := by
  have h := power_bound_contracts hx hw
  have hlen := length_oddEvenBlock a b
  have hodd := oddCount_oddEvenBlock a b
  have hgap' : 3 ^ oddCount (oddEvenBlock a b) <
      2 ^ (oddEvenBlock a b).length := by
    simpa [hodd, hlen] using hgap
  simpa [image_eq_iterate, hlen] using h hgap'

/-- Repeated formally contracting copies still contract the entry. -/
theorem contracting_repeated_odd_even_contracts {x a b r : ℕ}
    (hx : 2 ≤ x) (hgap : 3 ^ a < 2 ^ (a + b)) (hr : 1 ≤ r)
    (hw : follows x (repeatedOddEven a b r)) :
    image x (repeatedOddEven a b r) < x := by
  have h := power_bound_contracts hx hw
  have hlen := length_repeatedOddEven a b r
  have hodd := oddCount_repeatedOddEven a b r
  have hrep := contracting_gap_repeat (a := a) (b := b) (r := r) hgap hr
  have hgap' : 3 ^ oddCount (repeatedOddEven a b r) <
      2 ^ (repeatedOddEven a b r).length := by
    have hmul : r * a = a * r := Nat.mul_comm _ _
    simpa [hodd, hlen, hmul] using hrep
  simpa [image_eq_iterate, hlen] using h hgap'

/-- A formally contracting block cannot start at `n_*`. Later copies
may stay above `n_*` if the entry is already large. -/
theorem initial_contracting_block_forbidden {n a b : ℕ}
    (h : MinimalNonTerm n) (hgap : 3 ^ a < 2 ^ (a + b)) :
    ¬follows n (oddEvenBlock a b) := by
  intro hw
  have hrep : follows n (repeatedOddEven a b 1) := by
    simpa [repeatedOddEven, oddEvenBlock] using hw
  have hfin := repeated_odd_even_scale_barrier (k := 0) (r := 1) h rfl hrep
  have hn : 1 < n := lt_of_lt_of_le (by decide : (1 : ℕ) < 12)
    (minimal_nonterm_ge_twelve h)
  have hexp : 2 ^ (1 * (a + b)) ≤ 3 ^ (a * 1) :=
    (Nat.pow_le_pow_iff_right hn).mp hfin
  have hsimp : 2 ^ (a + b) ≤ 3 ^ a := by
    simpa [Nat.one_mul, Nat.mul_one] using hexp
  exact (not_lt_of_ge hsimp) hgap

/-- Repeated formally contracting copies cannot start at `n_*`. -/
theorem initial_contracting_repeated_forbidden {n a b r : ℕ}
    (h : MinimalNonTerm n) (hgap : 3 ^ a < 2 ^ (a + b)) (hr : 1 ≤ r) :
    ¬follows n (repeatedOddEven a b r) := by
  intro hw
  have hfin := repeated_odd_even_scale_barrier (k := 0) h rfl hw
  have hn : 1 < n := lt_of_lt_of_le (by decide : (1 : ℕ) < 12)
    (minimal_nonterm_ge_twelve h)
  have hexp : 2 ^ (r * (a + b)) ≤ 3 ^ (a * r) :=
    (Nat.pow_le_pow_iff_right hn).mp hfin
  exact (not_lt_of_ge hexp) (contracting_gap_repeat hgap hr)

end Problems.Juggler
