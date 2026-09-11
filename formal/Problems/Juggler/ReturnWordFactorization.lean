import Problems.Juggler.Itinerary
import Problems.Juggler.ItineraryStats

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

/-- Substitution preserves the unimodular matrix of letter counts. -/
theorem InducedPair.count_determinant {U V : List Branch} (h : InducedPair U V) :
    oddCount U * evenCount V = oddCount V * evenCount U + 1 := by
  induction h with
  | initial => norm_num [oddCount, evenCount]
  | left _ ih => simp only [oddCount_append, evenCount_append]; nlinarith
  | right _ ih => simp only [oddCount_append, evenCount_append]; nlinarith

/-- Both columns of the induced count matrix are primitive. -/
theorem InducedPair.count_coprime {U V : List Branch} (h : InducedPair U V) :
    Nat.Coprime (oddCount U) (evenCount U) ∧
      Nat.Coprime (oddCount V) (evenCount V) := by
  have hdet := h.count_determinant
  constructor
  · change Nat.gcd (oddCount U) (evenCount U) = 1
    apply Nat.dvd_one.mp
    have ha := dvd_mul_of_dvd_left (Nat.gcd_dvd_left (oddCount U) (evenCount U))
      (evenCount V)
    have hb := dvd_mul_of_dvd_right (Nat.gcd_dvd_right (oddCount U) (evenCount U))
      (oddCount V)
    rw [hdet] at ha
    exact (Nat.dvd_add_iff_right hb).mpr ha
  · change Nat.gcd (oddCount V) (evenCount V) = 1
    apply Nat.dvd_one.mp
    have ha := dvd_mul_of_dvd_right (Nat.gcd_dvd_right (oddCount V) (evenCount V))
      (oddCount U)
    have hb := dvd_mul_of_dvd_left (Nat.gcd_dvd_left (oddCount V) (evenCount V))
      (evenCount U)
    rw [hdet] at ha
    exact (Nat.dvd_add_iff_right hb).mpr ha

/-- Expanded counts recover exactly the gcd of the two branch populations. -/
theorem InducedPair.expanded_count_gcd {U V : List Branch} (h : InducedPair U V)
    (a b : ℕ) :
    Nat.gcd (a * oddCount U + b * oddCount V)
      (a * evenCount U + b * evenCount V) = Nat.gcd a b := by
  let O := a * oddCount U + b * oddCount V
  let E := a * evenCount U + b * evenCount V
  have hdet := h.count_determinant
  have h₁ : O * evenCount V = E * oddCount V + a := by
    dsimp [O, E]; nlinarith
  have h₂ : E * oddCount U = O * evenCount U + b := by
    dsimp [O, E]; nlinarith
  apply Nat.dvd_antisymm
  · apply Nat.dvd_gcd
    · have hx := dvd_mul_of_dvd_left (Nat.gcd_dvd_left O E) (evenCount V)
      have hy := dvd_mul_of_dvd_left (Nat.gcd_dvd_right O E) (oddCount V)
      rw [h₁] at hx
      exact (Nat.dvd_add_iff_right hy).mpr hx
    · have hx := dvd_mul_of_dvd_left (Nat.gcd_dvd_right O E) (oddCount U)
      have hy := dvd_mul_of_dvd_left (Nat.gcd_dvd_left O E) (evenCount U)
      rw [h₂] at hx
      exact (Nat.dvd_add_iff_right hy).mpr hx
  · apply Nat.dvd_gcd <;> apply dvd_add
    · exact dvd_mul_of_dvd_left (Nat.gcd_dvd_left a b) _
    · exact dvd_mul_of_dvd_left (Nat.gcd_dvd_right a b) _
    · exact dvd_mul_of_dvd_left (Nat.gcd_dvd_left a b) _
    · exact dvd_mul_of_dvd_left (Nat.gcd_dvd_right a b) _

/-- Conserved length and odd count transfer primitivity to retained populations. -/
theorem InducedPair.coprime_of_totals {U V : List Branch} (h : InducedPair U V)
    {a b L o : ℕ} (hL : a * U.length + b * V.length = L)
    (ho : a * oddCount U + b * oddCount V = o) (hc : Nat.Coprime L o) :
    Nat.Coprime a b := by
  have he : a * evenCount U + b * evenCount V + o = L := by
    have hu := evenCount_add_oddCount U
    have hv := evenCount_add_oddCount V
    nlinarith
  have hg := h.expanded_count_gcd a b
  rw [ho, ← Nat.gcd_add_self_right, he, Nat.gcd_comm] at hg
  exact hg.symm.trans hc

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
