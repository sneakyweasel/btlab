import Problems.Juggler.Corridor
import Problems.Juggler.FirstInternalOO

namespace Problems.Juggler

/-!
# Minimum-relative trajectory geometry

`AboveAnchor n w` is the shared finite-prefix hypothesis

```
follows n w  ∧  ∀ i ≤ |w|,  n ≤ T^i(n).
```

This file contains only the predicate and the lemmas whose primary
content is deriving, restricting, or extracting bounds from it.
It does not import `Scale`, `Minimal`, or `CycleCore`.

Cube-band arithmetic lives in `CubeCorridor`. Isolated-prefix
envelopes live in `FirstInternalOO`. Finite-progress bridges live
in `Progress`.
-/

/-- Every realized state along `w`, including the endpoint, is at
least the anchor `n`. -/
def AboveAnchor (n : ℕ) (w : List Branch) : Prop :=
  follows n w ∧ ∀ i, i ≤ w.length → n ≤ floorPower^[i] n

theorem aboveAnchor_follows {n : ℕ} {w : List Branch}
    (h : AboveAnchor n w) : follows n w :=
  h.1

theorem aboveAnchor_iterate_ge {n : ℕ} {w : List Branch} {i : ℕ}
    (h : AboveAnchor n w) (hi : i ≤ w.length) : n ≤ floorPower^[i] n :=
  h.2 i hi

theorem aboveAnchor_image_ge {n : ℕ} {w : List Branch}
    (h : AboveAnchor n w) : n ≤ image n w := by
  simpa [image_eq_iterate] using h.2 w.length le_rfl

/-- An anchor-relative prefix cannot drop. The image is at least `n`. -/
theorem aboveAnchor_not_lt {n : ℕ} {w : List Branch}
    (h : AboveAnchor n w) : ¬image n w < n :=
  fun hlt => (not_le_of_gt hlt) (aboveAnchor_image_ge h)

/-- Corollary D: a contracting itinerary envelope forbids `AboveAnchor`. -/
theorem aboveAnchor_not_envelope_drop {n : ℕ} {w : List Branch}
    (hn : 2 ≤ n) (hw : follows n w)
    (hgap : 3 ^ oddCount w < 2 ^ w.length) :
    ¬AboveAnchor n w :=
  fun h => aboveAnchor_not_lt h (by
    have hlt := power_bound_lt_pow (k := 1) hn hw (by simpa using hgap)
    simpa [image_eq_iterate] using hlt)

/-- A drop after a prefix forbids `AboveAnchor` on the combined word. -/
theorem aboveAnchor_not_continuation_drop {n : ℕ} {u v : List Branch}
    (h : AboveAnchor n (u ++ v))
    (hlt : image (image n u) v < n) : False := by
  have : image n (u ++ v) = image (image n u) v := image_append n u v
  exact aboveAnchor_not_lt h (this ▸ hlt)

theorem aboveAnchor_of_prefix {n : ℕ} {u v : List Branch}
    (h : AboveAnchor n (u ++ v)) : AboveAnchor n u :=
  ⟨follows_of_append_left h.1, fun i hi =>
    h.2 i (by
      simp only [List.length_append]
      exact le_trans hi (Nat.le_add_right _ _))⟩

/-- On an anchor prefix the next state is still `≥ n`, so an even
current state sits at or above `n^2`. -/
theorem even_ge_sq_of_aboveAnchor {n : ℕ} {w : List Branch} {i : ℕ}
    (h : AboveAnchor n w) (hi : i + 1 ≤ w.length)
    (he : floorPower^[i] n % 2 = 0) :
    n ^ 2 ≤ floorPower^[i] n :=
  even_ge_sq_of_succ_ge he (by
    have := aboveAnchor_iterate_ge h hi
    simpa [Function.iterate_succ_apply'] using this)

/-- Corollary E: an anchor prefix that finishes with `r` evens sits
at least `n^{2^r}` before the run. -/
theorem aboveAnchor_even_run_ge_pow {n : ℕ} {u : List Branch} {r : ℕ}
    (h : AboveAnchor n (u ++ List.replicate r Branch.even)) :
    n ^ (2 ^ r) ≤ image n u := by
  have hw : follows (image n u) (List.replicate r Branch.even) :=
    follows_of_append_right h.1
  have hpow := even_run_pow_le hw
  have hexit := aboveAnchor_image_ge h
  have himg :
      image n (u ++ List.replicate r Branch.even) =
        floorPower^[r] (image n u) := by
    calc image n (u ++ List.replicate r Branch.even)
        = image (image n u) (List.replicate r Branch.even) :=
          image_append n u _
      _ = floorPower^[(List.replicate r Branch.even).length] (image n u) :=
          image_eq_iterate _ _
      _ = floorPower^[r] (image n u) := by rw [List.length_replicate]
  have hge : n ≤ floorPower^[r] (image n u) := by
    rwa [himg] at hexit
  exact le_trans (Nat.pow_le_pow_left hge _) hpow

/-- An `OE` start cannot stay at or above the anchor: the first even
residual is below `n^2`. -/
theorem aboveAnchor_not_odd_even {n : ℕ} {v : List Branch}
    (hn : 2 ≤ n) (h : AboveAnchor n (.odd :: .even :: v)) : False := by
  have hodd : n % 2 = 1 := h.1.1
  have he : floorPower n % 2 = 0 := h.1.2.1
  have hlt := odd_floor_lt_sq hn hodd
  have hlen : (1 : ℕ) + 1 ≤ (.odd :: .even :: v).length := by simp
  have hsq := even_ge_sq_of_aboveAnchor (i := 1) h hlen (by simpa using he)
  have : floorPower^[1] n = floorPower n := by simp
  rw [this] at hsq
  exact (not_le_of_gt hlt) hsq

theorem aboveAnchor_isolatedOddSurvival {n a r : ℕ}
    (hn : 2 ≤ n) (h : AboveAnchor n (isolatedPrefix a r)) :
    isolatedOESurvives a r :=
  isolatedOddSurvival_bound hn h.1 (aboveAnchor_image_ge h)

theorem forbidden_isolated_under_anchor {n a r : ℕ}
    (hn : 2 ≤ n) (hgap : ¬isolatedOESurvives a r)
    (h : AboveAnchor n (isolatedPrefix a r)) : False :=
  hgap (aboveAnchor_isolatedOddSurvival hn h)

theorem aboveAnchor_isolated_two {n r : ℕ} (hn : 2 ≤ n)
    (h : AboveAnchor n (isolatedPrefix 2 r)) : r = 0 :=
  isolatedOESurvives_two (aboveAnchor_isolatedOddSurvival hn h)

end Problems.Juggler
