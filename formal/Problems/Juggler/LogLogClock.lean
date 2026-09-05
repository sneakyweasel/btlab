import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Problems.Juggler.Dynamics
import Problems.Juggler.Termination
import Problems.Juggler.TerminationFloor257
import Problems.Juggler.FateContagion

namespace Problems.Juggler

/-!
# The exponent walk mod 1, and the even-chain burst interval

The exact layer of the Lachesis log-log clock branch
(`docs/problems/juggler_lachesis_loglog_clock.md`).

Two statements, both elementary.

* **The walk is a rotation orbit mod 1.**  The exponent walk after `t`
  steps with `o` odd letters is `o * log2 3 - t`.  Since `t` and `o` are
  integers and `log2 3 = 1 + alpha` with `alpha = log2 (3/2)`, the walk
  is congruent mod 1 to `o * alpha`.  Along any orbit the odd count runs
  through consecutive integers, so the walk values mod 1 are the
  rotation orbit `{j * alpha}` — for a cycle, for a divergent orbit, for
  a terminating one alike.  The statement is pure arithmetic of the
  fractional part and holds for every real `x` in place of `log2 3`.

* **The even chain lands in a burst interval.**  If `n` reaches `m` in
  `k` steps through even states only, then `m^(2^k) ≤ n < (m+1)^(2^k)`.
  Each even step is `Nat.sqrt`, and `s = Nat.sqrt n` means
  `s^2 ≤ n < (s+1)^2`; the chain composes those cells.  In the clock
  `c = log2 log` this is the offset `c(n) ∈ [c(m) + k, c(m+1) + k)`.

Nothing here is a halt theorem, a no-cycle theorem, a density estimate,
or an exclusion of any fate.  The equidistribution of `{j * alpha}` and
the counting of the burst are not formalized.
-/

/-- The rotation of the clock circle induced by one odd step, `log2 (3/2)`. -/
noncomputable def alphaClock : ℝ := Real.logb 2 3 - 1

/-- The exponent walk after `t` steps of which `o` are odd. -/
noncomputable def walk (o t : ℕ) : ℝ := (o : ℝ) * Real.logb 2 3 - t

/-- For every real `x` and integers `o`, `t`: `o * x - t ≡ o * (x - 1)` mod `1`. -/
theorem fract_mul_sub_nat_eq_fract_mul_sub_one (x : ℝ) (o t : ℕ) :
    Int.fract ((o : ℝ) * x - t) = Int.fract ((o : ℝ) * (x - 1)) := by
  have h : (o : ℝ) * x - t = (o : ℝ) * (x - 1) + (((o : ℤ) - (t : ℤ) : ℤ) : ℝ) := by
    push_cast
    ring
  rw [h, Int.fract_add_intCast]

/-- **The walk mod 1 is the rotation orbit.**  `walk o t ≡ o * alphaClock` mod `1`. -/
theorem fract_walk_eq_fract_rotation (o t : ℕ) :
    Int.fract (walk o t) = Int.fract ((o : ℝ) * alphaClock) := by
  unfold walk alphaClock
  exact fract_mul_sub_nat_eq_fract_mul_sub_one (Real.logb 2 3) o t

/-- Two prefixes with the same odd count have the same walk mod 1, whatever their lengths. -/
theorem fract_walk_depends_only_on_odd_count (o t t' : ℕ) :
    Int.fract (walk o t) = Int.fract (walk o t') := by
  rw [fract_walk_eq_fract_rotation, fract_walk_eq_fract_rotation]

/-! ### The hug band is the minimal invariant band

One walk step adds `alphaClock` (odd letter) or subtracts `1` (even letter).  The band
`[0, 1 + alphaClock)` is invariant: some step always stays inside.  Every narrower band
`[0, w)`, `w < 1 + alphaClock`, has a nonempty dead zone `[w - alphaClock, 1)` from which no
step stays inside; below `1` no even step is possible at all, and at most one odd step fits.
These are the exact reasons the Clotho every-block gate is vacuous below the cube of the
anchor, and the Lachesis bursts only begin at its square. -/

/-- One walk step: an odd letter adds `alphaClock`, an even letter subtracts `1`. -/
def WalkStep (u v : ℝ) : Prop := v = u + alphaClock ∨ v = u - 1

theorem one_lt_logb_two_three : (1 : ℝ) < Real.logb 2 3 := by
  rw [Real.lt_logb_iff_rpow_lt (by norm_num) (by norm_num)]
  norm_num

theorem logb_two_three_lt_two : Real.logb 2 3 < 2 := by
  rw [Real.logb_lt_iff_lt_rpow (by norm_num) (by norm_num)]
  norm_num

theorem alphaClock_pos : 0 < alphaClock := by
  unfold alphaClock
  linarith [one_lt_logb_two_three]

theorem alphaClock_lt_one : alphaClock < 1 := by
  unfold alphaClock
  linarith [logb_two_three_lt_two]

/-- `alphaClock > 1/2`, i.e. `log2 3 > 3/2`, i.e. `9 > 8`. -/
theorem half_lt_alphaClock : (1 : ℝ) / 2 < alphaClock := by
  unfold alphaClock
  have h9 : (3 : ℝ) < Real.logb 2 9 := by
    rw [Real.lt_logb_iff_rpow_lt (by norm_num) (by norm_num)]
    norm_num
  have h : Real.logb 2 9 = 2 * Real.logb 2 3 := by
    have : (9 : ℝ) = 3 ^ (2 : ℕ) := by norm_num
    rw [this, Real.logb_pow]
    norm_num
  linarith

/-- **Invariance of the hug band.**  From any `u` in `[0, 1 + alphaClock)` some step stays. -/
theorem hug_band_step_exists {u : ℝ} (h0 : 0 ≤ u) (h1 : u < 1 + alphaClock) :
    ∃ v, WalkStep u v ∧ 0 ≤ v ∧ v < 1 + alphaClock := by
  by_cases hu : u < 1
  · exact ⟨u + alphaClock, Or.inl rfl, by linarith [alphaClock_pos], by linarith⟩
  · push Not at hu
    exact ⟨u - 1, Or.inr rfl, by linarith, by linarith [alphaClock_pos]⟩

/-- **The dead zone of a narrow band.**  If `w < 1 + alphaClock` and `u` lies in
`[w - alphaClock, 1) ∩ [0, w)`, no step stays in `[0, w)`. -/
theorem narrow_band_dead {w u : ℝ} (hlo : w - alphaClock ≤ u) (hu1 : u < 1) :
    ∀ v, WalkStep u v → ¬ (0 ≤ v ∧ v < w) := by
  intro v hv hin
  rcases hv with rfl | rfl
  · linarith [hin.2]
  · linarith [hin.1]

/-- The dead zone is nonempty exactly when the band is narrower than the hug band. -/
theorem dead_zone_nonempty {w : ℝ} (hw0 : 0 < w) (hw : w < 1 + alphaClock) :
    ∃ u, 0 ≤ u ∧ u < w ∧ w - alphaClock ≤ u ∧ u < 1 := by
  refine ⟨max 0 (w - alphaClock), le_max_left _ _, ?_, le_max_right _ _, ?_⟩
  · exact max_lt hw0 (by linarith [alphaClock_pos])
  · exact max_lt (by norm_num) (by linarith)

/-- **Inside the band the letter is forced, below `1`: it must be odd.**  From `u < 1`, the even
step leaves `[0, 1 + alphaClock)` downwards. -/
theorem band_step_forced_odd {u v : ℝ} (hu1 : u < 1) (hv : WalkStep u v)
    (hin : 0 ≤ v ∧ v < 1 + alphaClock) : v = u + alphaClock := by
  rcases hv with h | h
  · exact h
  · exfalso; rw [h] at hin; linarith [hin.1]

/-- **Inside the band the letter is forced, above `1`: it must be even.**  From `1 ≤ u`, the odd
step leaves `[0, 1 + alphaClock)` upwards. -/
theorem band_step_forced_even {u v : ℝ} (hu1 : 1 ≤ u) (hv : WalkStep u v)
    (hin : 0 ≤ v ∧ v < 1 + alphaClock) : v = u - 1 := by
  rcases hv with h | h
  · exfalso; rw [h] at hin; linarith [hin.2]
  · exact h

/-- **The band walk is the rotation by `alphaClock`.**  A walk confined to the hug band has a
single admissible successor at every point, given by the lift of the rotation: `u + alphaClock`
below `1`, `u - 1` above.  So the parity word of a band-confined orbit is determined by nothing
but the starting walk — it is the mechanical word of the rotation, the hug itinerary. -/
theorem band_successor_unique {u v w : ℝ} (_h0 : 0 ≤ u) (_h1 : u < 1 + alphaClock)
    (hv : WalkStep u v) (hvin : 0 ≤ v ∧ v < 1 + alphaClock)
    (hw : WalkStep u w) (hwin : 0 ≤ w ∧ w < 1 + alphaClock) : v = w := by
  by_cases hu : u < 1
  · rw [band_step_forced_odd hu hv hvin, band_step_forced_odd hu hw hwin]
  · push Not at hu
    rw [band_step_forced_even hu hv hvin, band_step_forced_even hu hw hwin]

/-- Below `1` no even step is possible: from `0 ≤ u < 1` the step `u - 1` is negative. -/
theorem no_even_step_below_one {u v : ℝ} (hu : u < 1) (hv : v = u - 1) : v < 0 := by
  linarith

/-- At most one odd step fits below `1`: `k * alphaClock < 1` forces `k ≤ 1`. -/
theorem odd_steps_below_one_le_one {k : ℕ} (hk : (k : ℝ) * alphaClock < 1) : k ≤ 1 := by
  by_contra h
  push Not at h
  have hk2 : (2 : ℝ) ≤ k := by exact_mod_cast h
  have := half_lt_alphaClock
  nlinarith [alphaClock_pos]

/-- The even preimage cell: `s = Nat.sqrt n` gives `s^2 ≤ n < (s+1)^2`. -/
theorem sqrt_cell (n : ℕ) : n.sqrt ^ 2 ≤ n ∧ n < (n.sqrt + 1) ^ 2 := by
  refine ⟨?_, ?_⟩
  · simpa [pow_two] using Nat.sqrt_le n
  · simpa [pow_two] using Nat.lt_succ_sqrt n

/-- **The even chain lands in the burst interval.**  If the first `k` states of the orbit
of `n` are even and the `k`-th iterate is `m`, then `m^(2^k) ≤ n < (m+1)^(2^k)`. -/
theorem even_chain_mem_burst :
    ∀ (k n m : ℕ), (∀ i, i < k → (floorPower^[i] n) % 2 = 0) → floorPower^[k] n = m →
      m ^ (2 ^ k) ≤ n ∧ n < (m + 1) ^ (2 ^ k) := by
  intro k
  induction k with
  | zero =>
      intro n m _ hk
      simp only [Function.iterate_zero, id_eq] at hk
      subst hk
      constructor
      · simp
      · simp
  | succ k ih =>
      intro n m hpar hk
      have heven : n % 2 = 0 := by simpa using hpar 0 (Nat.succ_pos k)
      have hstep : floorPower n = n.sqrt := floorPower_even_eq heven
      have hk' : floorPower^[k] (floorPower n) = m := by
        rw [← Function.iterate_succ_apply]
        exact hk
      have hpar' : ∀ i, i < k → (floorPower^[i] (floorPower n)) % 2 = 0 := by
        intro i hi
        have := hpar (i + 1) (Nat.succ_lt_succ hi)
        rw [Function.iterate_succ_apply] at this
        exact this
      obtain ⟨hlo, hhi⟩ := ih (floorPower n) m hpar' hk'
      rw [hstep] at hlo hhi
      obtain ⟨hcell_lo, hcell_hi⟩ := sqrt_cell n
      have hpow : ∀ a : ℕ, a ^ (2 ^ (k + 1)) = (a ^ (2 ^ k)) ^ 2 := by
        intro a
        rw [pow_succ, pow_mul]
      constructor
      · rw [hpow]
        exact le_trans (Nat.pow_le_pow_left hlo 2) hcell_lo
      · rw [hpow]
        have hsucc : n.sqrt + 1 ≤ (m + 1) ^ (2 ^ k) := Nat.succ_le_of_lt hhi
        exact lt_of_lt_of_le hcell_hi (Nat.pow_le_pow_left hsucc 2)

/-- The burst interval in the clock: `2^k * log m ≤ log n < 2^k * log (m+1)`, for `1 ≤ m`. -/
theorem even_chain_log_offset {k n m : ℕ} (hm : 1 ≤ m)
    (hpar : ∀ i, i < k → (floorPower^[i] n) % 2 = 0) (hk : floorPower^[k] n = m) :
    (2 : ℝ) ^ k * Real.log m ≤ Real.log n ∧ Real.log n < (2 : ℝ) ^ k * Real.log (m + 1) := by
  obtain ⟨hlo, hhi⟩ := even_chain_mem_burst k n m hpar hk
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hmk : (0 : ℝ) < (m : ℝ) ^ (2 ^ k) := pow_pos hm0 _
  have hn0 : (0 : ℝ) < n := lt_of_lt_of_le hmk (by exact_mod_cast hlo)
  constructor
  · have h := Real.log_le_log hmk (by exact_mod_cast hlo : (m : ℝ) ^ (2 ^ k) ≤ n)
    rw [Real.log_pow] at h
    simpa using h
  · have h := Real.log_lt_log hn0 (by exact_mod_cast hhi : (n : ℝ) < ((m : ℝ) + 1) ^ (2 ^ k))
    rw [Real.log_pow] at h
    simpa using h

/-! ### The floor stratifies the failure set by its leading even steps

A start that does not reach `1` and whose first `k` states are even sits above
`261^(2^k)`: its `k`-th iterate is again a failure, hence at least `261` by the Lean floor,
and the even chain multiplies exponents.  At the certified floor `N0 = 3.5e8` the same
argument (verified computation, not Lean) gives `(N0 + 1)^(2^k)`: the failure set is purely
odd on `(N0, (N0+1)^2)`, and its `E^k`-cylinder is empty below `(N0+1)^(2^k)`.  This is the
depth-`k` form of the fate note's "min F is an OO-start". -/

/-- A failure is at least `261`: every start in `[1, 260]` reaches `1`. -/
theorem not_reachesOne_ge {m : ℕ} (hm : 1 ≤ m) (h : ¬ ReachesOne m) : 261 ≤ m := by
  by_contra hlt
  push Not at hlt
  exact h (reachesOne_of_lt_two_hundred_sixty_one hm hlt)

/-- **The floor stratifies the failure set.**  If `n ≥ 1` does not reach `1` and its first `k`
states are even, then `261^(2^k) ≤ n`. -/
theorem not_reachesOne_even_chain_ge {n k : ℕ} (hn : 1 ≤ n) (h : ¬ ReachesOne n)
    (hpar : ∀ i, i < k → (floorPower^[i] n) % 2 = 0) : 261 ^ (2 ^ k) ≤ n := by
  have hm : ¬ ReachesOne (floorPower^[k] n) := fun hr =>
    h (backwardClosed_iterate reachesOne_backwardClosed k n hr)
  have h261 : 261 ≤ floorPower^[k] n := not_reachesOne_ge (floorPower_iterate_pos hn k) hm
  have hburst := (even_chain_mem_burst k n (floorPower^[k] n) hpar rfl).1
  exact le_trans (Nat.pow_le_pow_left h261 _) hburst

end Problems.Juggler
