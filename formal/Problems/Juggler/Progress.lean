import Problems.Juggler.Certificates
import Problems.Juggler.CubeCorridor

namespace Problems.Juggler

/-!
# Finite-progress spine

`FiniteProgress n` means a descent certificate exists. Strong induction
turns a universal finite-progress hypothesis into `ReachesOne`. The
automatic coverage is every `n ≥ 2` that is not odd-to-odd.

Geometric descent bridges (`even_below_square`, cube cells, envelope
gaps) live here. They do not know `AboveAnchor`, `CycleMin`, or
`MinimalNonTerm`. This is not a halt theorem.
-/

def FiniteProgress (n : ℕ) : Prop :=
  DescentCertificate n

theorem finiteProgress_of_imageLt {n : ℕ} {w : List Branch}
    (hw : follows n w) (hlt : image n w < n) : FiniteProgress n :=
  DescentCertificate.imageLt w hw hlt

/-- Naming alias of `finiteProgress_of_imageLt`. -/
theorem finiteProgress_of_descent {n : ℕ} {w : List Branch}
    (hw : follows n w) (hlt : image n w < n) : FiniteProgress n :=
  finiteProgress_of_imageLt hw hlt

theorem finiteProgress_of_capture {n : ℕ} {w : List Branch}
    (hw : follows n w) (himg : image n w = 1) : FiniteProgress n :=
  DescentCertificate.capture w hw himg

theorem finiteProgress_of_certificate {n : ℕ}
    (C : DescentCertificate n) : FiniteProgress n :=
  C

/-- Below `n`, every positive state already reaches `1`. Then one
finite-progress certificate at `n` gives `ReachesOne n`. -/
theorem reachesOne_of_finiteProgress {n : ℕ}
    (hbelow : ∀ m, 1 ≤ m → m < n → ReachesOne m)
    (hfp : FiniteProgress n) : ReachesOne n := by
  cases descentCertificate_stop_or_reachesOne hfp with
  | inl hstop =>
      obtain ⟨k, _hk, hlt⟩ := hstop
      have hn : 1 ≤ n := Nat.succ_le_of_lt (Nat.zero_lt_of_lt hlt)
      have himg : 1 ≤ floorPower^[k] n := floorPower_iterate_pos hn k
      exact reachesOne_of_iterate rfl (hbelow (floorPower^[k] n) himg hlt)
  | inr hone =>
      exact hone

/-- If every `n > 1` has finite progress, every positive integer
reaches `1`. The hypothesis is not proved here. -/
theorem reachesOne_of_all_finiteProgress
    (h : ∀ n, 1 < n → FiniteProgress n) :
    ∀ n, 1 ≤ n → ReachesOne n := by
  intro n hn
  induction n using Nat.strong_induction_on with
  | h n ih =>
      match n with
      | 0 => omega
      | 1 => exact reachesOne_one
      | n + 2 =>
          exact reachesOne_of_finiteProgress
            (fun m hm0 hmlt => ih m hmlt hm0) (h (n + 2) (by omega))

/-- Even `n ≥ 2` has finite progress: the one-letter word `E`. -/
theorem even_finiteProgress {n : ℕ} (hn : 2 ≤ n) (heven : n % 2 = 0) :
    FiniteProgress n :=
  finiteProgress_of_imageLt
    (even_itinerary_descent hn (by decide : (1 : ℕ) ≤ 1) ⟨heven, trivial⟩).1
    (even_itinerary_descent hn (by decide : (1 : ℕ) ≤ 1) ⟨heven, trivial⟩).2

/-- Odd `n ≥ 2` whose first image is even has finite progress: `OE`. -/
theorem odd_even_finiteProgress {n : ℕ} (hn : 2 ≤ n)
    (hodd : n % 2 = 1) (heven : floorPower n % 2 = 0) :
    FiniteProgress n := by
  have hw : follows n [.odd, .even] := ⟨hodd, heven, trivial⟩
  have hT : floorPower n = (n ^ 3).sqrt := floorPower_odd_eq hodd
  have hlt :=
    floorPower_odd_even_two_step_lt hn hodd (by simpa [hT] using heven)
  exact finiteProgress_of_imageLt hw (by simpa [image] using hlt)

/-- Automatic coverage: every `n ≥ 2` that is not odd-to-odd has
`FiniteProgress`. -/
theorem finiteProgress_of_not_odd_odd {n : ℕ} (hn : 2 ≤ n)
    (h : ¬(n % 2 = 1 ∧ floorPower n % 2 = 1)) : FiniteProgress n := by
  rcases Nat.mod_two_eq_zero_or_one n with heven | hodd
  · exact even_finiteProgress hn heven
  · rcases Nat.mod_two_eq_zero_or_one (floorPower n) with hTe | hTo
    · exact odd_even_finiteProgress hn hodd hTe
    · exact (h ⟨hodd, hTo⟩).elim

/-- If `n ≥ 2` has no finite-progress certificate, it is odd-to-odd. -/
theorem no_finiteProgress_implies_odd_odd {n : ℕ} (hn : 2 ≤ n)
    (h : ¬FiniteProgress n) :
    n % 2 = 1 ∧ floorPower n % 2 = 1 := by
  by_contra hnot
  exact h (finiteProgress_of_not_odd_odd hn hnot)

/-- Legacy name of `no_finiteProgress_implies_odd_odd`. -/
theorem unresolved_is_odd_odd {n : ℕ} (hn : 2 ≤ n)
    (h : ¬FiniteProgress n) :
    n % 2 = 1 ∧ floorPower n % 2 = 1 :=
  no_finiteProgress_implies_odd_odd hn h

/-- The first odd-to-odd image expands. Induction cannot fire there. -/
theorem odd_odd_image_gt {n : ℕ} (hn : 3 ≤ n) (hodd : n % 2 = 1)
    (_hoddT : floorPower n % 2 = 1) : n < floorPower n :=
  floorPower_odd_gt hn hodd

/-- Naming alias of `finiteProgress_of_imageLt`. A realized drop
below the start is the standard finite-progress certificate. -/
theorem finiteProgress_of_prefix_drop {n : ℕ} {w : List Branch}
    (hw : follows n w) (hlt : image n w < n) : FiniteProgress n :=
  finiteProgress_of_imageLt hw hlt

/-- If an even image sits below `n^2`, one more even letter is a
descent certificate. -/
theorem finiteProgress_of_even_below_square {n : ℕ} {w : List Branch}
    (hw : follows n w) (he : image n w % 2 = 0)
    (hlt : image n w < n ^ 2) : FiniteProgress n :=
  finiteProgress_of_prefix_drop
    (follows_append hw (follows_even_letter he))
    (by
      have hdrop := even_below_square_drop he hlt
      simpa [image_append, image] using hdrop)

/-- `k = 1` envelope gap is a descent certificate. -/
theorem finiteProgress_of_power_bound_lt_pow {n : ℕ} {w : List Branch}
    (hn : 2 ≤ n) (hw : follows n w)
    (hgap : 3 ^ oddCount w < 2 ^ w.length) : FiniteProgress n :=
  finiteProgress_of_prefix_drop hw (by
    have hlt := power_bound_lt_pow (k := 1) hn hw (by simpa using hgap)
    simpa [image_eq_iterate] using hlt)

/-- Square-cell pipeline: `power_bound_lt_pow (k := 2)` plus an even
image is `FiniteProgress`. -/
theorem finiteProgress_of_even_power_bound_square {n : ℕ} {w : List Branch}
    (hn : 2 ≤ n) (hw : follows n w) (he : image n w % 2 = 0)
    (hgap : 3 ^ oddCount w < 2 * 2 ^ w.length) : FiniteProgress n :=
  finiteProgress_of_even_below_square hw he
    (power_bound_lt_pow (k := 2) hn hw hgap)

/-- `OEE` after an eighth-cell even lift is `FiniteProgress`. -/
theorem finiteProgress_of_odd_even_eighth {n : ℕ} {w : List Branch}
    (hw : follows n w) (hodd : image n w % 2 = 1)
    (he : floorPower (image n w) % 2 = 0)
    (hx : image n w ^ 3 < n ^ 8)
    (he2 : floorPower (floorPower (image n w)) % 2 = 0) :
    FiniteProgress n := by
  have hw1 : follows n (w ++ [Branch.odd]) :=
    follows_append hw ⟨hodd, trivial⟩
  have himg1 : image n (w ++ [Branch.odd]) = floorPower (image n w) := by
    simp [image_append, image]
  have he' : image n (w ++ [Branch.odd]) % 2 = 0 := by
    simpa [himg1] using he
  exact finiteProgress_of_even_below_square
    (follows_append hw1 (follows_even_letter he'))
    (by simpa [image_append, image] using he2)
    (by
      have hz := (odd_even_eighth_lt_sq hodd he).mpr hx
      simpa [image_append, image] using hz)

/-- `OEE` after a cube-odd landing drops if the even reset is even
and already below `n^2`. Not a claim that every even reset is. -/
theorem finiteProgress_of_cube_odd_even_below_square
    {n : ℕ} {w : List Branch} (hw : follows n w)
    (h : CubeOddLanding n (image n w))
    (he : floorPower (image n w) % 2 = 0)
    (he2 : floorPower (floorPower (image n w)) % 2 = 0)
    (hz : floorPower (floorPower (image n w)) < n ^ 2) :
    FiniteProgress n := by
  have hw1 : follows n (w ++ [Branch.odd]) :=
    follows_append hw ⟨h.2.2, trivial⟩
  have himg1 : image n (w ++ [Branch.odd]) = floorPower (image n w) := by
    simp [image_append, image]
  have he' : image n (w ++ [Branch.odd]) % 2 = 0 := by
    simpa [himg1] using he
  exact finiteProgress_of_even_below_square
    (follows_append hw1 (follows_even_letter he'))
    (by simpa [image_append, image] using he2)
    (by simpa [image_append, image] using hz)

/-- Two evens after a cube-cell even landing drop below `n`. -/
theorem finiteProgress_of_cube_even_even {n : ℕ} {w : List Branch}
    (hn : 2 ≤ n) (hw : follows n w)
    (he : image n w % 2 = 0) (hlt : image n w < n ^ 3)
    (he2 : floorPower (image n w) % 2 = 0) : FiniteProgress n := by
  have hv : follows (image n w) [.even, .even] := ⟨he, he2, trivial⟩
  have hdrop := two_even_below_cube hn he he2 hlt
  refine finiteProgress_of_imageLt (follows_append hw hv) ?_
  simpa [image_append, image] using hdrop

end Problems.Juggler
