import Problems.Juggler.Itinerary

namespace Problems.Juggler.ReturnWordFactorization

/-- The two chronological products differ in the indicated two-letter block. -/
def Factorization (U V P Q : List Branch) : Prop :=
  U ++ V = P ++ [.odd, .even] ++ Q ∧
    V ++ U = P ++ [.even, .odd] ++ Q

theorem initial_factorization :
    Factorization [.odd, .odd, .even] [.odd, .even] [.odd] [.odd, .even] := by
  exact ⟨rfl, rfl⟩

theorem Factorization.left {U V P Q : List Branch} (h : Factorization U V P Q) :
    Factorization U (U ++ V) (U ++ P) Q := by
  rcases h with ⟨h₁, h₂⟩
  constructor
  · simpa only [List.append_assoc] using congrArg (fun w => U ++ w) h₁
  · simpa only [List.append_assoc] using congrArg (fun w => U ++ w) h₂

theorem Factorization.right {U V P Q : List Branch} (h : Factorization U V P Q) :
    Factorization (U ++ V) V P (Q ++ V) := by
  rcases h with ⟨h₁, h₂⟩
  constructor
  · simpa only [List.append_assoc] using congrArg (fun w => w ++ V) h₁
  · simpa only [List.append_assoc] using congrArg (fun w => w ++ V) h₂

/-- Pairs obtained by any finite sequence of the two exact substitutions. -/
inductive InducedPair : List Branch → List Branch → Prop
  | initial : InducedPair [.odd, .odd, .even] [.odd, .even]
  | left {U V} : InducedPair U V → InducedPair U (U ++ V)
  | right {U V} : InducedPair U V → InducedPair (U ++ V) V

theorem induced_factorization {U V : List Branch} (h : InducedPair U V) :
    ∃ P Q, Factorization U V P Q := by
  induction h with
  | initial => exact ⟨_, _, initial_factorization⟩
  | left _ ih =>
      obtain ⟨P, Q, h⟩ := ih
      exact ⟨_, _, h.left⟩
  | right _ ih =>
      obtain ⟨P, Q, h⟩ := ih
      exact ⟨_, _, h.right⟩

/-- The common prefix and suffix retain actual guards at a two-point return.
The two middle paths are OE and EO; no guard is asserted on a different domain. -/
theorem terminal_actual_factorization {U V P Q : List Branch} {m v : ℕ}
    (h : Factorization U V P Q)
    (hU : follows m U) (hV : follows v V)
    (hmv : image m U = v) (hvm : image v V = m) :
    follows m P ∧ follows v P ∧
      (image m P) % 2 = 1 ∧ (floorPower (image m P)) % 2 = 0 ∧
      (image v P) % 2 = 0 ∧ (floorPower (image v P)) % 2 = 1 ∧
      follows (floorPower (floorPower (image m P))) Q ∧
      follows (floorPower (floorPower (image v P))) Q ∧
      image (floorPower (floorPower (image m P))) Q = m ∧
      image (floorPower (floorPower (image v P))) Q = v := by
  have hUV : follows m (U ++ V) := follows_append hU (by simpa [hmv] using hV)
  have hVU : follows v (V ++ U) := follows_append hV (by simpa [hvm] using hU)
  have hUVim : image m (U ++ V) = m := by rw [image_append, hmv, hvm]
  have hVUim : image v (V ++ U) = v := by rw [image_append, hvm, hmv]
  rw [h.1, List.append_assoc] at hUV hUVim
  rw [h.2, List.append_assoc] at hVU hVUim
  have hmP := follows_of_append_left hUV
  have hvP := follows_of_append_left hVU
  have hmR := follows_of_append_right hUV
  have hvR := follows_of_append_right hVU
  change (image m P) % 2 = 1 ∧
    (floorPower (image m P)) % 2 = 0 ∧
    follows (floorPower (floorPower (image m P))) Q at hmR
  change (image v P) % 2 = 0 ∧
    (floorPower (image v P)) % 2 = 1 ∧
    follows (floorPower (floorPower (image v P))) Q at hvR
  rw [image_append] at hUVim hVUim
  change image (floorPower (floorPower (image m P))) Q = m at hUVim
  change image (floorPower (floorPower (image v P))) Q = v at hVUim
  exact ⟨hmP, hvP, hmR.1, hmR.2.1, hvR.1, hvR.2.1,
    hmR.2.2, hvR.2.2, hUVim, hVUim⟩

theorem induced_terminal_actual_factorization {U V : List Branch} {m v : ℕ}
    (h : InducedPair U V) (hU : follows m U) (hV : follows v V)
    (hmv : image m U = v) (hvm : image v V = m) :
    ∃ P Q, Factorization U V P Q ∧
      follows m P ∧ follows v P ∧
      (image m P) % 2 = 1 ∧ (floorPower (image m P)) % 2 = 0 ∧
      (image v P) % 2 = 0 ∧ (floorPower (image v P)) % 2 = 1 ∧
      follows (floorPower (floorPower (image m P))) Q ∧
      follows (floorPower (floorPower (image v P))) Q ∧
      image (floorPower (floorPower (image m P))) Q = m ∧
      image (floorPower (floorPower (image v P))) Q = v := by
  obtain ⟨P, Q, hF⟩ := induced_factorization h
  exact ⟨P, Q, hF, terminal_actual_factorization hF hU hV hmv hvm⟩

end Problems.Juggler.ReturnWordFactorization
