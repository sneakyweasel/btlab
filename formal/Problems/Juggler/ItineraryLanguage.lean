import Problems.Juggler.ExpansionBlocks

set_option maxRecDepth 4000000

namespace Problems.Juggler

/-!
# Existential Juggler itinerary languages

An itinerary is in `jugglerLanguage` when some integer realises it. The
expanding and persistent-expanding languages keep the same
existential quantifier: they do not say that every realisation
expands. Syntactic `expandingItinerary` remains a letter-count predicate
and is not used here.

`jugglerLanguage` is closed under factors. `expandingLanguage` is
not: `OOE` expands at `5`, while the factor `OE` never expands.
That is the odd-to-even two-step contraction, not a new
forbidden-factor calculus.

This file does not claim a finite automaton, a surviving PE
forbidden factor, or that every start reaches `1`.
-/

def jugglerLanguage (w : List Branch) : Prop :=
  ∃ n, follows n w

def expandingLanguage (w : List Branch) : Prop :=
  ∃ n, follows n w ∧ n < image n w

def persistentExpandingLanguage (w : List Branch) : Prop :=
  ∃ n, follows n w ∧ PersistentExpandingResidual n (image n w)

def itineraryPrefix (p w : List Branch) : Prop :=
  ∃ s, p ++ s = w

def itinerarySuffix (s w : List Branch) : Prop :=
  ∃ p, p ++ s = w

def itineraryFactor (u w : List Branch) : Prop :=
  ∃ p s, p ++ u ++ s = w

theorem jugglerLanguage_of_follows {n : ℕ} {w : List Branch}
    (h : follows n w) : jugglerLanguage w :=
  ⟨n, h⟩

theorem jugglerLanguage_prefix {p w : List Branch}
    (h : jugglerLanguage w) (hp : itineraryPrefix p w) : jugglerLanguage p := by
  obtain ⟨n, hw⟩ := h
  obtain ⟨s, hs⟩ := hp
  exact ⟨n, follows_of_append_left (Eq.mp (congrArg (follows n) hs.symm) hw)⟩

theorem jugglerLanguage_suffix {s w : List Branch}
    (h : jugglerLanguage w) (hs : itinerarySuffix s w) : jugglerLanguage s := by
  obtain ⟨n, hw⟩ := h
  obtain ⟨p, hp⟩ := hs
  exact ⟨image n p,
    follows_of_append_right (Eq.mp (congrArg (follows n) hp.symm) hw)⟩

theorem jugglerLanguage_factor {u w : List Branch}
    (h : jugglerLanguage w) (hu : itineraryFactor u w) : jugglerLanguage u := by
  obtain ⟨n, hw⟩ := h
  obtain ⟨p, s, hps⟩ := hu
  have hw' : follows n ((p ++ u) ++ s) := by
    simpa [List.append_assoc, hps] using hw
  exact ⟨image n p, follows_of_append_right (follows_of_append_left hw')⟩

theorem oddEvenBlock_one_one :
    oddEvenBlock 1 1 = [.odd, .even] := by
  simp [oddEvenBlock]

theorem ooe_mem_expandingLanguage :
    expandingLanguage (oddEvenBlock 2 1) := by
  refine ⟨5, follows_oddEvenBlock_two_one (by decide +kernel), ?_⟩
  have : image 5 (oddEvenBlock 2 1) = 6 :=
    image_oddEvenBlock_two_one (by decide +kernel)
  omega

theorem oe_not_mem_expandingLanguage :
    ¬ expandingLanguage (oddEvenBlock 1 1) := by
  rintro ⟨n, hw, hgt⟩
  have hodd : n % 2 = 1 := by
    simpa [oddEvenBlock_one_one] using hw.1
  have heven : floorPower n % 2 = 0 := by
    simpa [oddEvenBlock_one_one] using hw.2.1
  have himg : image n (oddEvenBlock 1 1) = floorPower (floorPower n) := by
    simp [oddEvenBlock_one_one, image]
  have hn0 : n ≠ 0 := by
    intro h
    subst h
    simp at hodd
  have hn1 : n ≠ 1 := by
    intro h
    subst h
    have : floorPower 1 = 1 := by decide +kernel
    omega
  have hn2 : 2 ≤ n := by omega
  have hlt :=
    floorPower_odd_even_two_step_lt hn2 hodd (by
      simpa [floorPower_odd_eq hodd] using heven)
  exact Nat.lt_asymm hgt (himg ▸ hlt)

theorem oe_factor_of_ooe :
    itineraryFactor (oddEvenBlock 1 1) (oddEvenBlock 2 1) :=
  ⟨[.odd], [], by simp [oddEvenBlock]⟩

/-- Expanding language is not factor-closed. Arrangement, not a
letter-count restatement of `3^{#O}>2^{|w|}`. -/
theorem expandingLanguage_not_factor_closed :
    expandingLanguage (oddEvenBlock 2 1) ∧
      itineraryFactor (oddEvenBlock 1 1) (oddEvenBlock 2 1) ∧
        ¬ expandingLanguage (oddEvenBlock 1 1) :=
  ⟨ooe_mem_expandingLanguage, oe_factor_of_ooe, oe_not_mem_expandingLanguage⟩

theorem ooe_mem_persistentExpandingLanguage :
    persistentExpandingLanguage (oddEvenBlock 2 1) := by
  refine ⟨365, follows_oddEvenBlock_two_one (by decide +kernel), ?_⟩
  have himg : image 365 (oddEvenBlock 2 1) = 763 :=
    image_oddEvenBlock_two_one (by decide +kernel)
  simpa [himg] using two_block_ooe_365.1

end Problems.Juggler
