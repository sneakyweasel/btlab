import Problems.Juggler.Progress
import Problems.Juggler.MinimumRelative

namespace Problems.Juggler

/-!
# Minimal non-termination

Conditional constraints on a hypothetical minimal `n` that never
reaches `1`. The already-proved half is

```
MinimalNonTerm n  →  ∀ k, T^[k] n ≥ n
HasFiniteCoeffStop n  →  ¬MinimalNonTerm n
```

The missing implication `MinimalNonTerm n → HasFiniteCoeffStop n`
is packaged as a Prop and is not proved. Not an all-odd trajectory claim.
-/

def MinimalNonTerm (n : ℕ) : Prop :=
  1 ≤ n ∧ ¬ReachesOne n ∧ ∀ m, 1 ≤ m → m < n → ReachesOne m

/-- Isolated missing implication. Not a theorem. -/
def MinimalImpliesCoeffStop (n : ℕ) : Prop :=
  MinimalNonTerm n → HasFiniteCoeffStop n

theorem MinimalNonTerm.pos {n : ℕ} (h : MinimalNonTerm n) : 1 ≤ n :=
  h.1

theorem MinimalNonTerm.not_reachesOne {n : ℕ} (h : MinimalNonTerm n) :
    ¬ReachesOne n :=
  h.2.1

theorem MinimalNonTerm.below {n m : ℕ} (h : MinimalNonTerm n)
    (hm0 : 1 ≤ m) (hm : m < n) : ReachesOne m :=
  h.2.2 m hm0 hm

theorem minimal_nonterm_ge_of_not_reachesOne {n m : ℕ}
    (h : MinimalNonTerm n) (hm0 : 1 ≤ m) (hm : ¬ReachesOne m) : n ≤ m := by
  by_contra hlt
  exact hm (h.below hm0 (Nat.lt_of_not_ge hlt))

theorem minimal_nonterm_ge_twelve {n : ℕ} (h : MinimalNonTerm n) : 12 ≤ n :=
  non_reachesOne_ge_twelve h.pos h.not_reachesOne

theorem trajectory_not_reachesOne {n m k : ℕ} (h : MinimalNonTerm n)
    (hk : floorPower^[k] n = m) : ¬ReachesOne m :=
  fun hm => h.not_reachesOne (reachesOne_of_iterate hk hm)

theorem image_not_reachesOne {n : ℕ} {w : List Branch}
    (h : MinimalNonTerm n) : ¬ReachesOne (image n w) :=
  trajectory_not_reachesOne h (image_eq_iterate n w).symm

theorem minimal_nonterm_no_capture {n : ℕ} {w : List Branch}
    (h : MinimalNonTerm n) : ¬(follows n w ∧ image n w = 1) :=
  fun hc => h.not_reachesOne (capture_reachesOne hc.1 hc.2)

theorem minimal_nonterm_no_descent {n : ℕ} {w : List Branch}
    (h : MinimalNonTerm n) : ¬(follows n w ∧ image n w < n) := by
  intro hd
  have hpos := image_pos h.pos w
  have hr := h.below hpos hd.2
  exact h.not_reachesOne (reachesOne_of_image hr)

theorem minimal_nonterm_image_ge {n : ℕ} {w : List Branch}
    (h : MinimalNonTerm n) (hw : follows n w) : n ≤ image n w := by
  by_contra hlt
  exact minimal_nonterm_no_descent h ⟨hw, Nat.lt_of_not_ge hlt⟩

theorem minimal_nonterm_iterate_ge {n : ℕ} (h : MinimalNonTerm n) :
    ∀ k, n ≤ floorPower^[k] n
  | 0 => le_rfl
  | k + 1 => by
      have hw : follows n (itinerary n (k + 1)) := follows_itinerary_self n (k + 1)
      have := minimal_nonterm_image_ge h hw
      simpa [image_word] using this

theorem minimal_nonterm_odd {n : ℕ} (h : MinimalNonTerm n) : n % 2 = 1 := by
  by_cases heven : n % 2 = 0
  · have hw : follows n (List.replicate 1 Branch.even) := ⟨heven, trivial⟩
    have hlt : floorPower n < n :=
      even_itinerary_contracts (by have := minimal_nonterm_ge_twelve h; omega)
        (by decide) hw
    have hr : ReachesOne (floorPower n) :=
      h.below (floorPower_pos h.pos) hlt
    exact (h.not_reachesOne (reachesOne_of_iterate (k := 1) rfl hr)).elim
  · omega

theorem even_run_exit_ge {n m k r : ℕ} (h : MinimalNonTerm n)
    (hk : floorPower^[k] n = m)
    (_hw : follows m (List.replicate r Branch.even)) :
    n ≤ floorPower^[r] m := by
  have hexit : floorPower^[k + r] n = floorPower^[r] m := by
    rw [iterate_add_right, hk]
  exact minimal_nonterm_ge_of_not_reachesOne h
    (by rw [← hexit]; exact floorPower_iterate_pos h.pos (k + r))
    (trajectory_not_reachesOne h hexit)

theorem even_run_scale_barrier {n m k r : ℕ} (h : MinimalNonTerm n)
    (hk : floorPower^[k] n = m)
    (hw : follows m (List.replicate r Branch.even)) :
    n ^ (2 ^ r) ≤ m := by
  have hu : follows n (itinerary n k) := follows_itinerary_self n k
  have himg : image n (itinerary n k) = m := by
    simpa [image_word] using hk
  have hfull :
      follows n (itinerary n k ++ List.replicate r Branch.even) :=
    follows_append hu (by simpa [himg] using hw)
  have ha : AboveAnchor n (itinerary n k ++ List.replicate r Branch.even) :=
    ⟨hfull, fun i _ => minimal_nonterm_iterate_ge h i⟩
  have := aboveAnchor_even_run_ge_pow ha
  simpa [himg] using this

theorem even_run_scale_barrier_of_image {n : ℕ} {u : List Branch} {r : ℕ}
    (h : MinimalNonTerm n) (_hu : follows n u)
    (hw : follows (image n u) (List.replicate r Branch.even)) :
    n ^ (2 ^ r) ≤ image n u :=
  even_run_scale_barrier h (image_eq_iterate n u).symm hw

theorem minimal_nonterm_even_ge_sq {n m k : ℕ} (h : MinimalNonTerm n)
    (hk : floorPower^[k] n = m) (heven : m % 2 = 0) : n ^ 2 ≤ m :=
  even_run_scale_barrier (r := 1) h hk ⟨heven, trivial⟩

theorem minimal_nonterm_first_even_ge_sq {n : ℕ} {u : List Branch}
    (h : MinimalNonTerm n) (_hu : follows n u)
    (heven : image n u % 2 = 0) : n ^ 2 ≤ image n u :=
  minimal_nonterm_even_ge_sq h (image_eq_iterate n u).symm heven

theorem minimal_nonterm_avoid_even_lt_sq_twelve {n m k : ℕ}
    (h : MinimalNonTerm n) (hk : floorPower^[k] n = m)
    (heven : m % 2 = 0) : 144 ≤ m := by
  have hm0 : 1 ≤ m := by
    rw [← hk]
    exact floorPower_iterate_pos h.pos k
  by_contra hlt
  exact trajectory_not_reachesOne h hk
    (even_lt_sq_twelve_reachesOne heven hm0 (Nat.lt_of_not_ge hlt))

theorem even_tower_not_on_minimal {n k j : ℕ} (h : MinimalNonTerm n)
    (hk : 1 ≤ k) : floorPower^[j] n ≠ 2 ^ (2 ^ (k - 1)) :=
  fun heq =>
    trajectory_not_reachesOne h heq
      (capture_reachesOne (even_tower_capture hk).1 (even_tower_capture hk).2)

theorem minimal_nonterm_oe_descent {n : ℕ} (h : MinimalNonTerm n)
    (heven : floorPower n % 2 = 0) :
    follows n [.odd, .even] ∧ image n [.odd, .even] < n := by
  have hodd := minimal_nonterm_odd h
  have hw : follows n [.odd, .even] := ⟨hodd, heven, trivial⟩
  have hT : floorPower n = (n ^ 3).sqrt := floorPower_odd_eq hodd
  have hlt :=
    floorPower_odd_even_two_step_lt
      (by have := minimal_nonterm_ge_twelve h; omega) hodd
      (by simpa [hT] using heven)
  exact ⟨hw, by simpa [image] using hlt⟩

theorem minimal_nonterm_odd_image_odd {n : ℕ} (h : MinimalNonTerm n) :
    floorPower n % 2 = 1 := by
  by_cases heven : floorPower n % 2 = 0
  · exact (minimal_nonterm_no_descent h (minimal_nonterm_oe_descent h heven)).elim
  · omega

theorem minimal_counterexample_normal_form {n : ℕ} {w : List Branch}
    (h : MinimalNonTerm n) (hw : follows n w) :
    12 ≤ n ∧
      n % 2 = 1 ∧
      n ≤ image n w ∧
      ¬ReachesOne (image n w) ∧
      ¬(follows n w ∧ image n w < n) ∧
      ¬(follows n w ∧ image n w = 1) ∧
      (image n w % 2 = 0 → n ^ 2 ≤ image n w) :=
  ⟨minimal_nonterm_ge_twelve h,
    minimal_nonterm_odd h,
    minimal_nonterm_image_ge h hw,
    image_not_reachesOne h,
    minimal_nonterm_no_descent h,
    minimal_nonterm_no_capture h,
    fun heven =>
      minimal_nonterm_even_ge_sq h (image_eq_iterate n w).symm heven⟩

/-- A minimal non-1 start has no finite-progress certificate. -/
theorem minimal_nonterm_not_finiteProgress {n : ℕ}
    (h : MinimalNonTerm n) : ¬FiniteProgress n :=
  fun hfp => h.not_reachesOne (reachesOne_of_finiteProgress h.2.2 hfp)

/-- Finite coefficient stopping time contradicts minimality. -/
theorem coeffStop_contradicts_minimal {n : ℕ}
    (h : MinimalNonTerm n) (hτ : HasFiniteCoeffStop n) : False := by
  have hn : 2 ≤ n := le_trans (by decide : 2 ≤ 12) (minimal_nonterm_ge_twelve h)
  obtain ⟨k, hk, hlt⟩ := coeffStop_implies_stop hn hτ
  have hge := minimal_nonterm_iterate_ge h k
  exact (not_le_of_gt hlt) hge

theorem no_minimal_of_all_coeffStop
    (h : FiniteCoeffStopConjecture) : ∀ n, ¬MinimalNonTerm n := by
  intro n hm
  have hn : 2 ≤ n := le_trans (by decide : 2 ≤ 12) (minimal_nonterm_ge_twelve hm)
  exact coeffStop_contradicts_minimal hm (h n hn)

/-- A minimal non-1 trajectory stays `≥ n` at every iterate, so every
realized finite prefix is minimum-relative. Not a cycle hypothesis. -/
theorem aboveAnchor_of_minimalNonTerm {n : ℕ} {w : List Branch}
    (h : MinimalNonTerm n) (hw : follows n w) : AboveAnchor n w :=
  ⟨hw, fun i _ => minimal_nonterm_iterate_ge h i⟩

theorem minimal_nonterm_not_follow_odd_even {n : ℕ} {v : List Branch}
    (h : MinimalNonTerm n) (hw : follows n (.odd :: .even :: v)) : False :=
  aboveAnchor_not_odd_even
    (le_trans (by decide : (2 : ℕ) ≤ 12) (minimal_nonterm_ge_twelve h))
    (aboveAnchor_of_minimalNonTerm h hw)

/-- On a CE, a cube-cell even landing is followed by an odd image. -/
theorem minimal_cube_even_forces_odd_image {n : ℕ} {w : List Branch}
    (h : MinimalNonTerm n) (hw : follows n w)
    (he : image n w % 2 = 0) (hlt : image n w < n ^ 3) :
    floorPower (image n w) % 2 = 1 := by
  have hn : 2 ≤ n :=
    le_trans (by decide : (2 : ℕ) ≤ 12) (minimal_nonterm_ge_twelve h)
  by_contra heven
  have he2 : floorPower (image n w) % 2 = 0 := by omega
  exact minimal_nonterm_not_finiteProgress h
    (finiteProgress_of_cube_even_even hn hw he hlt he2)

/-- On a CE, an odd cube lift with even first image cannot return
even below `n^2`. The return may still sit in `[n^2, n^3)`. -/
theorem minimal_cube_odd_even_not_even_below_square
    {n : ℕ} {w : List Branch}
    (h : MinimalNonTerm n) (hw : follows n w)
    (hc : CubeOddLanding n (image n w))
    (he : floorPower (image n w) % 2 = 0) :
    ¬(floorPower (floorPower (image n w)) % 2 = 0 ∧
        floorPower (floorPower (image n w)) < n ^ 2) := by
  intro ⟨he2, hz⟩
  exact minimal_nonterm_not_finiteProgress h
    (finiteProgress_of_cube_odd_even_below_square hw hc he he2 hz)

/-- On a CE, an eighth-cell even lift cannot return even. The
square comparison is the mixed OE cell `x^3 < n^8`. -/
theorem minimal_odd_even_eighth_forces_odd_return
    {n : ℕ} {w : List Branch}
    (h : MinimalNonTerm n) (hw : follows n w)
    (hodd : image n w % 2 = 1)
    (he : floorPower (image n w) % 2 = 0)
    (hx : image n w ^ 3 < n ^ 8) :
    floorPower (floorPower (image n w)) % 2 = 1 := by
  by_contra heven
  have he2 : floorPower (floorPower (image n w)) % 2 = 0 := by omega
  exact minimal_nonterm_not_finiteProgress h
    (finiteProgress_of_odd_even_eighth hw hodd he hx he2)

/-- Termination application: a CE-realized isolated prefix with
`a₀ = 2` forces `r = 0`. -/
theorem minimal_isolated_two {n r : ℕ} (h : MinimalNonTerm n)
    (hw : follows n (isolatedPrefix 2 r)) : r = 0 :=
  aboveAnchor_isolated_two
    (le_trans (by decide : (2 : ℕ) ≤ 12) (minimal_nonterm_ge_twelve h))
    (aboveAnchor_of_minimalNonTerm h hw)

end Problems.Juggler
