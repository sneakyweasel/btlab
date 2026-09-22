import Problems.Juggler.CycleCore
import Problems.Juggler.CycleObstructions
import Problems.Juggler.Residuals

namespace Problems.Juggler

/-!
# Trajectory split: cycle or escape

A Juggler trajectory in `ℕ` is eventually periodic or unbounded. On a
`MinimalNonTerm` start the periodic case stays `≥ n`, so it is not
the `1`-cycle. The `OOEOOE` square-cell trap survives after dropping
the `CycleMin` return hypothesis: an even landing, or an even next
image below `n^2`, is descent and is impossible on a CE. After the
forced `OO`, the third residual `OOEOOEOO` lies below `n^3` and a
completed third `OOE` lies below `n^2`. The escaped-even `OE`
`OOEOOEOOEOE` still lies below `n^2`. The next `O` after an odd
`OE` landing still lies below `n^2`. The following second `O`
loses the square cell and stays below `n^3`.

This is not a halt theorem. It does not prove
`∀ n, ¬EscapesToInfinity n`. It does not prove that every cycle is
impossible. `FiniteCoeffStopConjecture` remains a `def`.
-/

def EscapesToInfinity (n : ℕ) : Prop :=
  ∀ B, ∃ k, B < floorPower^[k] n

def EventuallyCycles (n : ℕ) : Prop :=
  ∃ i j, i < j ∧ floorPower^[i] n = floorPower^[j] n

def itineraryOOEOOEO : List Branch :=
  itineraryOOEOOE ++ [Branch.odd]

theorem not_escapes_iff_bounded {n : ℕ} :
    ¬EscapesToInfinity n ↔ ∃ M, ∀ k, floorPower^[k] n ≤ M := by
  constructor
  · intro h
    obtain ⟨B, hB⟩ := not_forall.mp h
    refine ⟨B, fun k => Nat.le_of_not_lt ?_⟩
    exact not_exists.mp hB k
  · intro ⟨M, hM⟩ hEsc
    obtain ⟨k, hk⟩ := hEsc M
    exact (not_lt_of_ge (hM k)) hk

/-- A uniformly bounded trajectory repeats. Finite pigeonhole on the
prefix of length `M + 2`. -/
theorem bounded_trajectory_eventually_cycles {n M : ℕ}
    (hbound : ∀ k, floorPower^[k] n ≤ M) :
    EventuallyCycles n := by
  by_contra hnone
  have hdistinct :
      ∀ i j, i < j → j < M + 2 → floorPower^[i] n ≠ floorPower^[j] n := by
    intro i j hij _hj heq
    exact hnone ⟨i, j, hij, heq⟩
  have hinj :
      Function.Injective fun i : Fin (M + 2) => floorPower^[i.val] n := by
    intro a b h
    apply Fin.ext
    rcases lt_trichotomy a.val b.val with hlt | heq | hgt
    · exact (hdistinct a.val b.val hlt (by omega) h).elim
    · exact heq
    · exact (hdistinct b.val a.val hgt (by omega) h.symm).elim
  have hsubset :
      (Finset.univ.image fun i : Fin (M + 2) => floorPower^[i.val] n) ⊆
        Finset.range (M + 1) := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨i, _, rfl⟩
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (hbound i.val))
  have hcard := Finset.card_le_card hsubset
  have himg :=
    Finset.card_image_of_injective
      (f := fun i : Fin (M + 2) => floorPower^[i.val] n) Finset.univ hinj
  simp [himg, Fintype.card_fin, Finset.card_univ, Finset.card_range] at hcard

theorem cycles_or_escapes (n : ℕ) :
    EventuallyCycles n ∨ EscapesToInfinity n := by
  by_cases h : EscapesToInfinity n
  · exact Or.inr h
  · obtain ⟨M, hM⟩ := not_escapes_iff_bounded.mp h
    exact Or.inl (bounded_trajectory_eventually_cycles hM)

theorem reachesOne_implies_eventually_cycles {n : ℕ}
    (h : ReachesOne n) : EventuallyCycles n := by
  obtain ⟨k, hk⟩ := h
  refine ⟨k, k + 1, Nat.lt_succ_self k, ?_⟩
  calc
    floorPower^[k] n = 1 := hk
    _ = floorPower 1 := floorPower_one.symm
    _ = floorPower^[k + 1] n := by
        rw [Function.iterate_succ_apply', hk]

theorem minimal_nonterm_cycles_or_escapes {n : ℕ}
    (_h : MinimalNonTerm n) :
    EventuallyCycles n ∨ EscapesToInfinity n :=
  cycles_or_escapes n

theorem minimal_nonterm_cycle_values_ge {n i : ℕ}
    (h : MinimalNonTerm n) : n ≤ floorPower^[i] n :=
  minimal_nonterm_iterate_ge h i

theorem cycleItinerary_of_repeat {n i j : ℕ} (hij : i < j)
    (heq : floorPower^[i] n = floorPower^[j] n) :
    CycleItinerary (floorPower^[i] n) (itinerary (floorPower^[i] n) (j - i)) := by
  have hlen : 1 ≤ (itinerary (floorPower^[i] n) (j - i)).length := by
    simpa [itinerary_length] using Nat.succ_le_of_lt (Nat.sub_pos_of_lt hij)
  refine ⟨follows_itinerary_self _ _, ?_, hlen⟩
  have hsum : i + (j - i) = j := Nat.add_sub_of_le (Nat.le_of_lt hij)
  have himg :
      image (floorPower^[i] n) (itinerary (floorPower^[i] n) (j - i)) =
        floorPower^[j - i] (floorPower^[i] n) :=
    image_word _ _
  rw [himg, ← iterate_add_right, hsum, heq]

/-- No nontrivial cycle implies no bounded nontermination. This is
not a no-cycle theorem and not a halt theorem: unbounded escape
remains. -/
theorem no_nontrivial_cycle_no_bounded_nonterm
    (hno : ∀ (m : ℕ) (w : List Branch), 2 ≤ m → ¬CycleItinerary m w)
    {n : ℕ} (hn : 2 ≤ n) (hnt : ¬ReachesOne n) :
    EscapesToInfinity n := by
  cases cycles_or_escapes n with
  | inr hesc => exact hesc
  | inl hcyc =>
      obtain ⟨i, j, hij, heq⟩ := hcyc
      have hC := cycleItinerary_of_repeat hij heq
      have hpos : 1 ≤ floorPower^[i] n :=
        floorPower_iterate_pos (le_trans (by decide : (1 : ℕ) ≤ 2) hn) i
      have hne1 : floorPower^[i] n ≠ 1 := fun h1 => hnt ⟨i, h1⟩
      have hm2 : 2 ≤ floorPower^[i] n :=
        Nat.succ_le_of_lt (lt_of_le_of_ne hpos hne1.symm)
      exact (hno _ _ hm2 hC).elim

theorem itineraryOOEOOE_length : itineraryOOEOOE.length = 6 := rfl

theorem itineraryOOEOOE_oddCount : oddCount itineraryOOEOOE = 4 := by
  simp [itineraryOOEOOE]

theorem itineraryOOEOOEO_length : itineraryOOEOOEO.length = 7 := by
  simp [itineraryOOEOOEO, itineraryOOEOOE]

theorem itineraryOOEOOEO_oddCount : oddCount itineraryOOEOOEO = 5 := by
  simp [itineraryOOEOOEO, itineraryOOEOOE]

/-- Same square-cell comparison as the human `OOEOOE` corridor, with
no `CycleMin` return hypothesis. -/
theorem follows_ooeooe_image_lt_sq {n : ℕ} (hn : 2 ≤ n)
    (hw : follows n itineraryOOEOOE) :
    image n itineraryOOEOOE < n ^ 2 :=
  power_bound_lt_pow (k := 2) hn hw (by
    rw [itineraryOOEOOE_length, itineraryOOEOOE_oddCount]
    decide)

/-- The itinerary `OOEOOEO` has the square-cell gap `256 > 243`. -/
theorem follows_ooeooeo_image_lt_sq {n : ℕ} (hn : 2 ≤ n)
    (hw : follows n itineraryOOEOOEO) :
    image n itineraryOOEOOEO < n ^ 2 :=
  power_bound_lt_pow (k := 2) hn hw (by
    rw [itineraryOOEOOEO_length, itineraryOOEOOEO_oddCount]
    decide)

theorem follows_singleton_even {m : ℕ} (he : m % 2 = 0) :
    follows m [Branch.even] :=
  ⟨he, trivial⟩

theorem follows_singleton_odd {m : ℕ} (hodd : m % 2 = 1) :
    follows m [Branch.odd] :=
  ⟨hodd, trivial⟩

theorem follows_ooeooe_even {n : ℕ} (hw : follows n itineraryOOEOOE)
    (he : image n itineraryOOEOOE % 2 = 0) :
    follows n (itineraryOOEOOE ++ [Branch.even]) :=
  follows_append hw (follows_singleton_even he)

theorem image_ooeooe_even (n : ℕ) :
    image n (itineraryOOEOOE ++ [Branch.even]) =
      floorPower (image n itineraryOOEOOE) := by
  rw [image_append]
  rfl

/-- Even `OOEOOE` landing is the shared square trap, hence
`FiniteProgress`. No cycle-return hypothesis. -/
theorem finiteProgress_of_ooeooe_even_landing {n : ℕ}
    (hn : 2 ≤ n) (hw : follows n itineraryOOEOOE)
    (he : image n itineraryOOEOOE % 2 = 0) : FiniteProgress n :=
  finiteProgress_of_even_below_square hw he (follows_ooeooe_image_lt_sq hn hw)

/-- Even `OOEOOE` landing is descent, hence impossible on a CE. -/
theorem minimal_ooeooe_not_even_landing {n : ℕ}
    (h : MinimalNonTerm n) (hw : follows n itineraryOOEOOE) :
    image n itineraryOOEOOE % 2 = 1 := by
  have hn2 : 2 ≤ n :=
    le_trans (by decide : (2 : ℕ) ≤ 12) (minimal_nonterm_ge_twelve h)
  by_contra heven
  have he : image n itineraryOOEOOE % 2 = 0 := by omega
  exact minimal_nonterm_not_finiteProgress h
    (finiteProgress_of_ooeooe_even_landing hn2 hw he)

theorem follows_itineraryOOEOOEO_of_odd_landing {n : ℕ}
    (hw : follows n itineraryOOEOOE) (hodd : image n itineraryOOEOOE % 2 = 1) :
    follows n itineraryOOEOOEO := by
  simpa [itineraryOOEOOEO] using follows_append hw (follows_singleton_odd hodd)

theorem follows_ooeooeo_even {n : ℕ} (hw : follows n itineraryOOEOOEO)
    (he : image n itineraryOOEOOEO % 2 = 0) :
    follows n (itineraryOOEOOEO ++ [Branch.even]) :=
  follows_append hw (follows_singleton_even he)

theorem image_ooeooeo_even (n : ℕ) :
    image n (itineraryOOEOOEO ++ [Branch.even]) =
      floorPower (image n itineraryOOEOOEO) := by
  rw [image_append]
  rfl

/-- On a CE, `OOEOOE` forces another `OO`. The next completed letter
after the forced `O` cannot be `E`. -/
theorem minimal_ooeooe_forces_oo {n : ℕ}
    (h : MinimalNonTerm n) (hw : follows n itineraryOOEOOE) :
    follows n itineraryOOEOOEO ∧ image n itineraryOOEOOEO % 2 = 1 := by
  have hodd := minimal_ooeooe_not_even_landing h hw
  have hf := follows_itineraryOOEOOEO_of_odd_landing hw hodd
  refine ⟨hf, ?_⟩
  have hn2 : 2 ≤ n :=
    le_trans (by decide : (2 : ℕ) ≤ 12) (minimal_nonterm_ge_twelve h)
  have hzlt := follows_ooeooeo_image_lt_sq hn2 hf
  by_contra heven
  have he : image n itineraryOOEOOEO % 2 = 0 := by omega
  exact minimal_nonterm_not_finiteProgress h
    (finiteProgress_of_even_below_square hf he hzlt)

/-- A CE never realizes a formally contracting itinerary. Contrapositive of
`power_bound_contracts`. -/
theorem minimal_nonterm_not_exponentGap {n : ℕ} {w : List Branch}
    (h : MinimalNonTerm n) (hw : follows n w) : ¬exponentGap w := by
  intro hg
  have hn : 2 ≤ n :=
    le_trans (by decide : (2 : ℕ) ≤ 12) (minimal_nonterm_ge_twelve h)
  have hlt := power_bound_contracts hn hw hg
  exact minimal_nonterm_no_descent h
    ⟨hw, by simpa [image_eq_iterate] using hlt⟩

/-- Every realized prefix of a CE is prefix-noncontracting. Concatenating
expanding residual blocks therefore cannot create an exponent certificate
on a CE. This is not a halt theorem. -/
theorem minimal_nonterm_prefix_noncontracting {n : ℕ} {w : List Branch}
    (h : MinimalNonTerm n) (hw : follows n w) : prefixNoncontracting w := by
  intro k _hk hg
  have hw' : follows n (w.take k ++ w.drop k) := by
    simpa [List.take_append_drop] using hw
  exact minimal_nonterm_not_exponentGap h (follows_of_append_left hw') hg

def itineraryOOEOOEOO : List Branch :=
  itineraryOOEOOEO ++ [Branch.odd]

def itineraryOOEOOEOOE : List Branch :=
  itineraryOOEOOEOO ++ [Branch.even]

theorem itineraryOOEOOEOO_length : itineraryOOEOOEOO.length = 8 := by
  simp [itineraryOOEOOEOO, itineraryOOEOOEO, itineraryOOEOOE]

theorem itineraryOOEOOEOO_oddCount : oddCount itineraryOOEOOEOO = 6 := by
  simp [itineraryOOEOOEOO, itineraryOOEOOEO, itineraryOOEOOE]

theorem itineraryOOEOOEOOE_length : itineraryOOEOOEOOE.length = 9 := by
  simp [itineraryOOEOOEOOE, itineraryOOEOOEOO, itineraryOOEOOEO, itineraryOOEOOE]

theorem itineraryOOEOOEOOE_oddCount : oddCount itineraryOOEOOEOOE = 6 := by
  simp [itineraryOOEOOEOOE, itineraryOOEOOEOO, itineraryOOEOOEO, itineraryOOEOOE]

theorem follows_itineraryOOEOOEOO_of_forced_oo {n : ℕ}
    (h : follows n itineraryOOEOOEO ∧ image n itineraryOOEOOEO % 2 = 1) :
    follows n itineraryOOEOOEOO := by
  simpa [itineraryOOEOOEOO] using follows_append h.1 (follows_singleton_odd h.2)

theorem minimal_ooeooe_follows_ooeooeoo {n : ℕ}
    (h : MinimalNonTerm n) (hw : follows n itineraryOOEOOE) :
    follows n itineraryOOEOOEOO :=
  follows_itineraryOOEOOEOO_of_forced_oo (minimal_ooeooe_forces_oo h hw)

/-- The itinerary `OOEOOEOO` has the cube-cell gap `768 > 729`. -/
theorem follows_ooeooeoo_image_lt_cube {n : ℕ} (hn : 2 ≤ n)
    (hw : follows n itineraryOOEOOEOO) :
    image n itineraryOOEOOEOO < n ^ 3 :=
  power_bound_lt_pow (k := 3) hn hw (by
    rw [itineraryOOEOOEOO_length, itineraryOOEOOEOO_oddCount]
    decide)

/-- The completed third `OOE` has the square-cell gap `1024 > 729`. -/
theorem follows_ooeooeooe_image_lt_sq {n : ℕ} (hn : 2 ≤ n)
    (hw : follows n itineraryOOEOOEOOE) :
    image n itineraryOOEOOEOOE < n ^ 2 :=
  power_bound_lt_pow (k := 2) hn hw (by
    rw [itineraryOOEOOEOOE_length, itineraryOOEOOEOOE_oddCount]
    decide)

theorem follows_ooeooeooe_even {n : ℕ} (hw : follows n itineraryOOEOOEOOE)
    (he : image n itineraryOOEOOEOOE % 2 = 0) :
    follows n (itineraryOOEOOEOOE ++ [Branch.even]) :=
  follows_append hw (follows_singleton_even he)

theorem image_ooeooeooe_even (n : ℕ) :
    image n (itineraryOOEOOEOOE ++ [Branch.even]) =
      floorPower (image n itineraryOOEOOEOOE) := by
  rw [image_append]
  rfl

/-- On a CE, a completed third `OOE` cannot land even: the landing is
below `n^2`, so an even landing is descent. This is not a PE theorem. -/
theorem minimal_ooeooeooe_not_even_landing {n : ℕ}
    (h : MinimalNonTerm n) (hw : follows n itineraryOOEOOEOOE) :
    image n itineraryOOEOOEOOE % 2 = 1 := by
  have hn2 : 2 ≤ n :=
    le_trans (by decide : (2 : ℕ) ≤ 12) (minimal_nonterm_ge_twelve h)
  have hlt := follows_ooeooeooe_image_lt_sq hn2 hw
  by_contra heven
  have he : image n itineraryOOEOOEOOE % 2 = 0 := by omega
  have hdrop : floorPower (image n itineraryOOEOOEOOE) < n :=
    (even_floorPower_lt_iff he).mpr hlt
  exact minimal_nonterm_no_descent h
    ⟨follows_ooeooeooe_even hw he, by simpa [image_ooeooeooe_even] using hdrop⟩

def itineraryOOEOOEOOEO : List Branch :=
  itineraryOOEOOEOOE ++ [Branch.odd]

def itineraryOOEOOEOOEOE : List Branch :=
  itineraryOOEOOEOOEO ++ [Branch.even]

theorem itineraryOOEOOEOOEO_length : itineraryOOEOOEOOEO.length = 10 := by
  simp [itineraryOOEOOEOOEO, itineraryOOEOOEOOE, itineraryOOEOOEOO, itineraryOOEOOEO, itineraryOOEOOE]

theorem itineraryOOEOOEOOEO_oddCount : oddCount itineraryOOEOOEOOEO = 7 := by
  simp [itineraryOOEOOEOOEO, itineraryOOEOOEOOE, itineraryOOEOOEOO, itineraryOOEOOEO, itineraryOOEOOE]

theorem itineraryOOEOOEOOEOE_length : itineraryOOEOOEOOEOE.length = 11 := by
  simp [itineraryOOEOOEOOEOE, itineraryOOEOOEOOEO, itineraryOOEOOEOOE, itineraryOOEOOEOO,
    itineraryOOEOOEO, itineraryOOEOOE]

theorem itineraryOOEOOEOOEOE_oddCount : oddCount itineraryOOEOOEOOEOE = 7 := by
  simp [itineraryOOEOOEOOEOE, itineraryOOEOOEOOEO, itineraryOOEOOEOOE, itineraryOOEOOEOO,
    itineraryOOEOOEO, itineraryOOEOOE]

theorem follows_itineraryOOEOOEOOEO_of_odd_third {n : ℕ}
    (hw : follows n itineraryOOEOOEOOE) (hodd : image n itineraryOOEOOEOOE % 2 = 1) :
    follows n itineraryOOEOOEOOEO := by
  simpa [itineraryOOEOOEOOEO] using follows_append hw (follows_singleton_odd hodd)

theorem minimal_ooeooeooe_follows_o {n : ℕ}
    (h : MinimalNonTerm n) (hw : follows n itineraryOOEOOEOOE) :
    follows n itineraryOOEOOEOOEO :=
  follows_itineraryOOEOOEOOEO_of_odd_third hw
    (minimal_ooeooeooe_not_even_landing h hw)

/-- The escaped-even `OE` after a third `OOE` has the square-cell gap
`4096 > 2187`. This is not a length-11 cycle census. -/
theorem follows_ooeooeooeoe_image_lt_sq {n : ℕ} (hn : 2 ≤ n)
    (hw : follows n itineraryOOEOOEOOEOE) :
    image n itineraryOOEOOEOOEOE < n ^ 2 :=
  power_bound_lt_pow (k := 2) hn hw (by
    rw [itineraryOOEOOEOOEOE_length, itineraryOOEOOEOOEOE_oddCount]
    decide)

theorem follows_ooeooeooeoe_even {n : ℕ} (hw : follows n itineraryOOEOOEOOEOE)
    (he : image n itineraryOOEOOEOOEOE % 2 = 0) :
    follows n (itineraryOOEOOEOOEOE ++ [Branch.even]) :=
  follows_append hw (follows_singleton_even he)

theorem image_ooeooeooeoe_even (n : ℕ) :
    image n (itineraryOOEOOEOOEOE ++ [Branch.even]) =
      floorPower (image n itineraryOOEOOEOOEOE) := by
  rw [image_append]
  rfl

/-- On a CE, the `OE` landing after a third `OOE` cannot be even.
The landing is below `n^2`, so an even landing is descent. This does
not kill an odd landing such as `1517`. -/
theorem minimal_ooeooeooeoe_not_even_landing {n : ℕ}
    (h : MinimalNonTerm n) (hw : follows n itineraryOOEOOEOOEOE) :
    image n itineraryOOEOOEOOEOE % 2 = 1 := by
  have hn2 : 2 ≤ n :=
    le_trans (by decide : (2 : ℕ) ≤ 12) (minimal_nonterm_ge_twelve h)
  have hlt := follows_ooeooeooeoe_image_lt_sq hn2 hw
  by_contra heven
  have he : image n itineraryOOEOOEOOEOE % 2 = 0 := by omega
  have hdrop : floorPower (image n itineraryOOEOOEOOEOE) < n :=
    (even_floorPower_lt_iff he).mpr hlt
  exact minimal_nonterm_no_descent h
    ⟨follows_ooeooeooeoe_even hw he, by simpa [image_ooeooeooeoe_even] using hdrop⟩

def itineraryOOEOOEOOEOEO : List Branch :=
  itineraryOOEOOEOOEOE ++ [Branch.odd]

theorem itineraryOOEOOEOOEOEO_length : itineraryOOEOOEOOEOEO.length = 12 := by
  simp [itineraryOOEOOEOOEOEO, itineraryOOEOOEOOEOE, itineraryOOEOOEOOEO, itineraryOOEOOEOOE,
    itineraryOOEOOEOO, itineraryOOEOOEO, itineraryOOEOOE]

theorem itineraryOOEOOEOOEOEO_oddCount : oddCount itineraryOOEOOEOOEOEO = 8 := by
  simp [itineraryOOEOOEOOEOEO, itineraryOOEOOEOOEOE, itineraryOOEOOEOOEO, itineraryOOEOOEOOE,
    itineraryOOEOOEOO, itineraryOOEOOEO, itineraryOOEOOE]

theorem follows_itineraryOOEOOEOOEOEO_of_odd_oe {n : ℕ}
    (hw : follows n itineraryOOEOOEOOEOE) (hodd : image n itineraryOOEOOEOOEOE % 2 = 1) :
    follows n itineraryOOEOOEOOEOEO := by
  simpa [itineraryOOEOOEOOEOEO] using follows_append hw (follows_singleton_odd hodd)

theorem minimal_ooeooeooeoe_follows_o {n : ℕ}
    (h : MinimalNonTerm n) (hw : follows n itineraryOOEOOEOOEOE) :
    follows n itineraryOOEOOEOOEOEO :=
  follows_itineraryOOEOOEOOEOEO_of_odd_oe hw
    (minimal_ooeooeooeoe_not_even_landing h hw)

/-- After an odd `OE` landing the next `O` still has the square-cell
gap `8192 > 6561`. Another escaped even is impossible on this step. -/
theorem follows_ooeooeooeoeo_image_lt_sq {n : ℕ} (hn : 2 ≤ n)
    (hw : follows n itineraryOOEOOEOOEOEO) :
    image n itineraryOOEOOEOOEOEO < n ^ 2 :=
  power_bound_lt_pow (k := 2) hn hw (by
    rw [itineraryOOEOOEOOEOEO_length, itineraryOOEOOEOOEOEO_oddCount]
    decide)

theorem follows_ooeooeooeoeo_even {n : ℕ} (hw : follows n itineraryOOEOOEOOEOEO)
    (he : image n itineraryOOEOOEOOEOEO % 2 = 0) :
    follows n (itineraryOOEOOEOOEOEO ++ [Branch.even]) :=
  follows_append hw (follows_singleton_even he)

theorem image_ooeooeooeoeo_even (n : ℕ) :
    image n (itineraryOOEOOEOOEOEO ++ [Branch.even]) =
      floorPower (image n itineraryOOEOOEOOEOEO) := by
  rw [image_append]
  rfl

/-- On a CE, the next image after an odd `OE` landing is odd and
below `n^2`. An even image would be descent. This is not a halt
theorem. -/
theorem minimal_ooeooeooeoeo_not_even {n : ℕ}
    (h : MinimalNonTerm n) (hw : follows n itineraryOOEOOEOOEOE) :
    follows n itineraryOOEOOEOOEOEO ∧ image n itineraryOOEOOEOOEOEO % 2 = 1 := by
  have hf := minimal_ooeooeooeoe_follows_o h hw
  refine ⟨hf, ?_⟩
  have hn2 : 2 ≤ n :=
    le_trans (by decide : (2 : ℕ) ≤ 12) (minimal_nonterm_ge_twelve h)
  have hlt := follows_ooeooeooeoeo_image_lt_sq hn2 hf
  by_contra heven
  have he : image n itineraryOOEOOEOOEOEO % 2 = 0 := by omega
  have hdrop : floorPower (image n itineraryOOEOOEOOEOEO) < n :=
    (even_floorPower_lt_iff he).mpr hlt
  exact minimal_nonterm_no_descent h
    ⟨follows_ooeooeooeoeo_even hf he, by simpa [image_ooeooeooeoeo_even] using hdrop⟩

def itineraryOOEOOEOOEOEOO : List Branch :=
  itineraryOOEOOEOOEOEO ++ [Branch.odd]

theorem itineraryOOEOOEOOEOEOO_length : itineraryOOEOOEOOEOEOO.length = 13 := by
  simp [itineraryOOEOOEOOEOEOO, itineraryOOEOOEOOEOEO, itineraryOOEOOEOOEOE, itineraryOOEOOEOOEO,
    itineraryOOEOOEOOE, itineraryOOEOOEOO, itineraryOOEOOEO, itineraryOOEOOE]

theorem itineraryOOEOOEOOEOEOO_oddCount : oddCount itineraryOOEOOEOOEOEOO = 9 := by
  simp [itineraryOOEOOEOOEOEOO, itineraryOOEOOEOOEOEO, itineraryOOEOOEOOEOE, itineraryOOEOOEOOEO,
    itineraryOOEOOEOOE, itineraryOOEOOEOO, itineraryOOEOOEO, itineraryOOEOOE]

theorem follows_itineraryOOEOOEOOEOEOO_of_forced_oo {n : ℕ}
    (h : follows n itineraryOOEOOEOOEOEO ∧ image n itineraryOOEOOEOOEOEO % 2 = 1) :
    follows n itineraryOOEOOEOOEOEOO := by
  simpa [itineraryOOEOOEOOEOEOO] using follows_append h.1 (follows_singleton_odd h.2)

theorem minimal_ooeooeooeoeo_follows_o {n : ℕ}
    (h : MinimalNonTerm n) (hw : follows n itineraryOOEOOEOOEOE) :
    follows n itineraryOOEOOEOOEOEOO :=
  follows_itineraryOOEOOEOOEOEOO_of_forced_oo (minimal_ooeooeooeoeo_not_even h hw)

theorem ooeooeooeoeoo_loses_square : ¬(3 ^ 9 < 2 ^ (13 + 1)) := by
  decide

/-- The second `O` after the new `OO` loses the square cell
(`19683 > 16384`) but keeps the cube-cell gap `24576 > 19683`.
The square comparison `3^9 < 2 · 2^13` fails; see
`ooeooeooeoeoo_loses_square`. A cube-cell even landing is therefore
not `FiniteProgress`. -/
theorem follows_ooeooeooeoeoo_image_lt_cube {n : ℕ} (hn : 2 ≤ n)
    (hw : follows n itineraryOOEOOEOOEOEOO) :
    image n itineraryOOEOOEOOEOEOO < n ^ 3 :=
  power_bound_lt_pow (k := 3) hn hw (by
    rw [itineraryOOEOOEOOEOEOO_length, itineraryOOEOOEOOEOEOO_oddCount]
    decide)

end Problems.Juggler
