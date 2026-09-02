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

def wordOOEOOEO : List Branch :=
  wordOOEOOE ++ [Branch.odd]

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

theorem cycleWord_of_repeat {n i j : ℕ} (hij : i < j)
    (heq : floorPower^[i] n = floorPower^[j] n) :
    CycleWord (floorPower^[i] n) (word (floorPower^[i] n) (j - i)) := by
  have hlen : 1 ≤ (word (floorPower^[i] n) (j - i)).length := by
    simpa [word_length] using Nat.succ_le_of_lt (Nat.sub_pos_of_lt hij)
  refine ⟨follows_word_self _ _, ?_, hlen⟩
  have hsum : i + (j - i) = j := Nat.add_sub_of_le (Nat.le_of_lt hij)
  have himg :
      image (floorPower^[i] n) (word (floorPower^[i] n) (j - i)) =
        floorPower^[j - i] (floorPower^[i] n) :=
    image_word _ _
  rw [himg, ← iterate_add_right, hsum, heq]

/-- No nontrivial cycle implies no bounded nontermination. This is
not a no-cycle theorem and not a halt theorem: unbounded escape
remains. -/
theorem no_nontrivial_cycle_no_bounded_nonterm
    (hno : ∀ (m : ℕ) (w : List Branch), 2 ≤ m → ¬CycleWord m w)
    {n : ℕ} (hn : 2 ≤ n) (hnt : ¬ReachesOne n) :
    EscapesToInfinity n := by
  cases cycles_or_escapes n with
  | inr hesc => exact hesc
  | inl hcyc =>
      obtain ⟨i, j, hij, heq⟩ := hcyc
      have hC := cycleWord_of_repeat hij heq
      have hpos : 1 ≤ floorPower^[i] n :=
        floorPower_iterate_pos (le_trans (by decide : (1 : ℕ) ≤ 2) hn) i
      have hne1 : floorPower^[i] n ≠ 1 := fun h1 => hnt ⟨i, h1⟩
      have hm2 : 2 ≤ floorPower^[i] n :=
        Nat.succ_le_of_lt (lt_of_le_of_ne hpos hne1.symm)
      exact (hno _ _ hm2 hC).elim

theorem wordOOEOOE_length : wordOOEOOE.length = 6 := rfl

theorem wordOOEOOE_oddCount : oddCount wordOOEOOE = 4 := by
  simp [wordOOEOOE]

theorem wordOOEOOEO_length : wordOOEOOEO.length = 7 := by
  simp [wordOOEOOEO, wordOOEOOE]

theorem wordOOEOOEO_oddCount : oddCount wordOOEOOEO = 5 := by
  simp [wordOOEOOEO, wordOOEOOE]

/-- Same square-cell comparison as the human `OOEOOE` corridor, with
no `CycleMin` return hypothesis. -/
theorem follows_ooeooe_image_lt_sq {n : ℕ} (hn : 2 ≤ n)
    (hw : follows n wordOOEOOE) :
    image n wordOOEOOE < n ^ 2 :=
  power_bound_lt_pow (k := 2) hn hw (by
    rw [wordOOEOOE_length, wordOOEOOE_oddCount]
    decide)

/-- The word `OOEOOEO` has the square-cell gap `256 > 243`. -/
theorem follows_ooeooeo_image_lt_sq {n : ℕ} (hn : 2 ≤ n)
    (hw : follows n wordOOEOOEO) :
    image n wordOOEOOEO < n ^ 2 :=
  power_bound_lt_pow (k := 2) hn hw (by
    rw [wordOOEOOEO_length, wordOOEOOEO_oddCount]
    decide)

theorem follows_singleton_even {m : ℕ} (he : m % 2 = 0) :
    follows m [Branch.even] :=
  ⟨he, trivial⟩

theorem follows_singleton_odd {m : ℕ} (hodd : m % 2 = 1) :
    follows m [Branch.odd] :=
  ⟨hodd, trivial⟩

theorem follows_ooeooe_even {n : ℕ} (hw : follows n wordOOEOOE)
    (he : image n wordOOEOOE % 2 = 0) :
    follows n (wordOOEOOE ++ [Branch.even]) :=
  follows_append hw (follows_singleton_even he)

theorem image_ooeooe_even (n : ℕ) :
    image n (wordOOEOOE ++ [Branch.even]) =
      floorPower (image n wordOOEOOE) := by
  rw [image_append]
  rfl

/-- Even `OOEOOE` landing is the shared square trap, hence
`FiniteProgress`. No cycle-return hypothesis. -/
theorem finiteProgress_of_ooeooe_even_landing {n : ℕ}
    (hn : 2 ≤ n) (hw : follows n wordOOEOOE)
    (he : image n wordOOEOOE % 2 = 0) : FiniteProgress n :=
  finiteProgress_of_even_below_square hw he (follows_ooeooe_image_lt_sq hn hw)

/-- Even `OOEOOE` landing is descent, hence impossible on a CE. -/
theorem minimal_ooeooe_not_even_landing {n : ℕ}
    (h : MinimalNonTerm n) (hw : follows n wordOOEOOE) :
    image n wordOOEOOE % 2 = 1 := by
  have hn2 : 2 ≤ n :=
    le_trans (by decide : (2 : ℕ) ≤ 12) (minimal_nonterm_ge_twelve h)
  by_contra heven
  have he : image n wordOOEOOE % 2 = 0 := by omega
  exact minimal_nonterm_not_finiteProgress h
    (finiteProgress_of_ooeooe_even_landing hn2 hw he)

theorem follows_wordOOEOOEO_of_odd_landing {n : ℕ}
    (hw : follows n wordOOEOOE) (hodd : image n wordOOEOOE % 2 = 1) :
    follows n wordOOEOOEO := by
  simpa [wordOOEOOEO] using follows_append hw (follows_singleton_odd hodd)

theorem follows_ooeooeo_even {n : ℕ} (hw : follows n wordOOEOOEO)
    (he : image n wordOOEOOEO % 2 = 0) :
    follows n (wordOOEOOEO ++ [Branch.even]) :=
  follows_append hw (follows_singleton_even he)

theorem image_ooeooeo_even (n : ℕ) :
    image n (wordOOEOOEO ++ [Branch.even]) =
      floorPower (image n wordOOEOOEO) := by
  rw [image_append]
  rfl

/-- On a CE, `OOEOOE` forces another `OO`. The next completed letter
after the forced `O` cannot be `E`. -/
theorem minimal_ooeooe_forces_oo {n : ℕ}
    (h : MinimalNonTerm n) (hw : follows n wordOOEOOE) :
    follows n wordOOEOOEO ∧ image n wordOOEOOEO % 2 = 1 := by
  have hodd := minimal_ooeooe_not_even_landing h hw
  have hf := follows_wordOOEOOEO_of_odd_landing hw hodd
  refine ⟨hf, ?_⟩
  have hn2 : 2 ≤ n :=
    le_trans (by decide : (2 : ℕ) ≤ 12) (minimal_nonterm_ge_twelve h)
  have hzlt := follows_ooeooeo_image_lt_sq hn2 hf
  by_contra heven
  have he : image n wordOOEOOEO % 2 = 0 := by omega
  exact minimal_nonterm_not_finiteProgress h
    (finiteProgress_of_even_below_square hf he hzlt)

/-- A CE never realizes a formally contracting word. Contrapositive of
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

def wordOOEOOEOO : List Branch :=
  wordOOEOOEO ++ [Branch.odd]

def wordOOEOOEOOE : List Branch :=
  wordOOEOOEOO ++ [Branch.even]

theorem wordOOEOOEOO_length : wordOOEOOEOO.length = 8 := by
  simp [wordOOEOOEOO, wordOOEOOEO, wordOOEOOE]

theorem wordOOEOOEOO_oddCount : oddCount wordOOEOOEOO = 6 := by
  simp [wordOOEOOEOO, wordOOEOOEO, wordOOEOOE]

theorem wordOOEOOEOOE_length : wordOOEOOEOOE.length = 9 := by
  simp [wordOOEOOEOOE, wordOOEOOEOO, wordOOEOOEO, wordOOEOOE]

theorem wordOOEOOEOOE_oddCount : oddCount wordOOEOOEOOE = 6 := by
  simp [wordOOEOOEOOE, wordOOEOOEOO, wordOOEOOEO, wordOOEOOE]

theorem follows_wordOOEOOEOO_of_forced_oo {n : ℕ}
    (h : follows n wordOOEOOEO ∧ image n wordOOEOOEO % 2 = 1) :
    follows n wordOOEOOEOO := by
  simpa [wordOOEOOEOO] using follows_append h.1 (follows_singleton_odd h.2)

theorem minimal_ooeooe_follows_ooeooeoo {n : ℕ}
    (h : MinimalNonTerm n) (hw : follows n wordOOEOOE) :
    follows n wordOOEOOEOO :=
  follows_wordOOEOOEOO_of_forced_oo (minimal_ooeooe_forces_oo h hw)

/-- The word `OOEOOEOO` has the cube-cell gap `768 > 729`. -/
theorem follows_ooeooeoo_image_lt_cube {n : ℕ} (hn : 2 ≤ n)
    (hw : follows n wordOOEOOEOO) :
    image n wordOOEOOEOO < n ^ 3 :=
  power_bound_lt_pow (k := 3) hn hw (by
    rw [wordOOEOOEOO_length, wordOOEOOEOO_oddCount]
    decide)

/-- The completed third `OOE` has the square-cell gap `1024 > 729`. -/
theorem follows_ooeooeooe_image_lt_sq {n : ℕ} (hn : 2 ≤ n)
    (hw : follows n wordOOEOOEOOE) :
    image n wordOOEOOEOOE < n ^ 2 :=
  power_bound_lt_pow (k := 2) hn hw (by
    rw [wordOOEOOEOOE_length, wordOOEOOEOOE_oddCount]
    decide)

theorem follows_ooeooeooe_even {n : ℕ} (hw : follows n wordOOEOOEOOE)
    (he : image n wordOOEOOEOOE % 2 = 0) :
    follows n (wordOOEOOEOOE ++ [Branch.even]) :=
  follows_append hw (follows_singleton_even he)

theorem image_ooeooeooe_even (n : ℕ) :
    image n (wordOOEOOEOOE ++ [Branch.even]) =
      floorPower (image n wordOOEOOEOOE) := by
  rw [image_append]
  rfl

/-- On a CE, a completed third `OOE` cannot land even: the landing is
below `n^2`, so an even landing is descent. This is not a PE theorem. -/
theorem minimal_ooeooeooe_not_even_landing {n : ℕ}
    (h : MinimalNonTerm n) (hw : follows n wordOOEOOEOOE) :
    image n wordOOEOOEOOE % 2 = 1 := by
  have hn2 : 2 ≤ n :=
    le_trans (by decide : (2 : ℕ) ≤ 12) (minimal_nonterm_ge_twelve h)
  have hlt := follows_ooeooeooe_image_lt_sq hn2 hw
  by_contra heven
  have he : image n wordOOEOOEOOE % 2 = 0 := by omega
  have hdrop : floorPower (image n wordOOEOOEOOE) < n :=
    (even_floorPower_lt_iff he).mpr hlt
  exact minimal_nonterm_no_descent h
    ⟨follows_ooeooeooe_even hw he, by simpa [image_ooeooeooe_even] using hdrop⟩

def wordOOEOOEOOEO : List Branch :=
  wordOOEOOEOOE ++ [Branch.odd]

def wordOOEOOEOOEOE : List Branch :=
  wordOOEOOEOOEO ++ [Branch.even]

theorem wordOOEOOEOOEO_length : wordOOEOOEOOEO.length = 10 := by
  simp [wordOOEOOEOOEO, wordOOEOOEOOE, wordOOEOOEOO, wordOOEOOEO, wordOOEOOE]

theorem wordOOEOOEOOEO_oddCount : oddCount wordOOEOOEOOEO = 7 := by
  simp [wordOOEOOEOOEO, wordOOEOOEOOE, wordOOEOOEOO, wordOOEOOEO, wordOOEOOE]

theorem wordOOEOOEOOEOE_length : wordOOEOOEOOEOE.length = 11 := by
  simp [wordOOEOOEOOEOE, wordOOEOOEOOEO, wordOOEOOEOOE, wordOOEOOEOO,
    wordOOEOOEO, wordOOEOOE]

theorem wordOOEOOEOOEOE_oddCount : oddCount wordOOEOOEOOEOE = 7 := by
  simp [wordOOEOOEOOEOE, wordOOEOOEOOEO, wordOOEOOEOOE, wordOOEOOEOO,
    wordOOEOOEO, wordOOEOOE]

theorem follows_wordOOEOOEOOEO_of_odd_third {n : ℕ}
    (hw : follows n wordOOEOOEOOE) (hodd : image n wordOOEOOEOOE % 2 = 1) :
    follows n wordOOEOOEOOEO := by
  simpa [wordOOEOOEOOEO] using follows_append hw (follows_singleton_odd hodd)

theorem minimal_ooeooeooe_follows_o {n : ℕ}
    (h : MinimalNonTerm n) (hw : follows n wordOOEOOEOOE) :
    follows n wordOOEOOEOOEO :=
  follows_wordOOEOOEOOEO_of_odd_third hw
    (minimal_ooeooeooe_not_even_landing h hw)

/-- The escaped-even `OE` after a third `OOE` has the square-cell gap
`4096 > 2187`. This is not a length-11 cycle census. -/
theorem follows_ooeooeooeoe_image_lt_sq {n : ℕ} (hn : 2 ≤ n)
    (hw : follows n wordOOEOOEOOEOE) :
    image n wordOOEOOEOOEOE < n ^ 2 :=
  power_bound_lt_pow (k := 2) hn hw (by
    rw [wordOOEOOEOOEOE_length, wordOOEOOEOOEOE_oddCount]
    decide)

theorem follows_ooeooeooeoe_even {n : ℕ} (hw : follows n wordOOEOOEOOEOE)
    (he : image n wordOOEOOEOOEOE % 2 = 0) :
    follows n (wordOOEOOEOOEOE ++ [Branch.even]) :=
  follows_append hw (follows_singleton_even he)

theorem image_ooeooeooeoe_even (n : ℕ) :
    image n (wordOOEOOEOOEOE ++ [Branch.even]) =
      floorPower (image n wordOOEOOEOOEOE) := by
  rw [image_append]
  rfl

/-- On a CE, the `OE` landing after a third `OOE` cannot be even.
The landing is below `n^2`, so an even landing is descent. This does
not kill an odd landing such as `1517`. -/
theorem minimal_ooeooeooeoe_not_even_landing {n : ℕ}
    (h : MinimalNonTerm n) (hw : follows n wordOOEOOEOOEOE) :
    image n wordOOEOOEOOEOE % 2 = 1 := by
  have hn2 : 2 ≤ n :=
    le_trans (by decide : (2 : ℕ) ≤ 12) (minimal_nonterm_ge_twelve h)
  have hlt := follows_ooeooeooeoe_image_lt_sq hn2 hw
  by_contra heven
  have he : image n wordOOEOOEOOEOE % 2 = 0 := by omega
  have hdrop : floorPower (image n wordOOEOOEOOEOE) < n :=
    (even_floorPower_lt_iff he).mpr hlt
  exact minimal_nonterm_no_descent h
    ⟨follows_ooeooeooeoe_even hw he, by simpa [image_ooeooeooeoe_even] using hdrop⟩

def wordOOEOOEOOEOEO : List Branch :=
  wordOOEOOEOOEOE ++ [Branch.odd]

theorem wordOOEOOEOOEOEO_length : wordOOEOOEOOEOEO.length = 12 := by
  simp [wordOOEOOEOOEOEO, wordOOEOOEOOEOE, wordOOEOOEOOEO, wordOOEOOEOOE,
    wordOOEOOEOO, wordOOEOOEO, wordOOEOOE]

theorem wordOOEOOEOOEOEO_oddCount : oddCount wordOOEOOEOOEOEO = 8 := by
  simp [wordOOEOOEOOEOEO, wordOOEOOEOOEOE, wordOOEOOEOOEO, wordOOEOOEOOE,
    wordOOEOOEOO, wordOOEOOEO, wordOOEOOE]

theorem follows_wordOOEOOEOOEOEO_of_odd_oe {n : ℕ}
    (hw : follows n wordOOEOOEOOEOE) (hodd : image n wordOOEOOEOOEOE % 2 = 1) :
    follows n wordOOEOOEOOEOEO := by
  simpa [wordOOEOOEOOEOEO] using follows_append hw (follows_singleton_odd hodd)

theorem minimal_ooeooeooeoe_follows_o {n : ℕ}
    (h : MinimalNonTerm n) (hw : follows n wordOOEOOEOOEOE) :
    follows n wordOOEOOEOOEOEO :=
  follows_wordOOEOOEOOEOEO_of_odd_oe hw
    (minimal_ooeooeooeoe_not_even_landing h hw)

/-- After an odd `OE` landing the next `O` still has the square-cell
gap `8192 > 6561`. Another escaped even is impossible on this step. -/
theorem follows_ooeooeooeoeo_image_lt_sq {n : ℕ} (hn : 2 ≤ n)
    (hw : follows n wordOOEOOEOOEOEO) :
    image n wordOOEOOEOOEOEO < n ^ 2 :=
  power_bound_lt_pow (k := 2) hn hw (by
    rw [wordOOEOOEOOEOEO_length, wordOOEOOEOOEOEO_oddCount]
    decide)

theorem follows_ooeooeooeoeo_even {n : ℕ} (hw : follows n wordOOEOOEOOEOEO)
    (he : image n wordOOEOOEOOEOEO % 2 = 0) :
    follows n (wordOOEOOEOOEOEO ++ [Branch.even]) :=
  follows_append hw (follows_singleton_even he)

theorem image_ooeooeooeoeo_even (n : ℕ) :
    image n (wordOOEOOEOOEOEO ++ [Branch.even]) =
      floorPower (image n wordOOEOOEOOEOEO) := by
  rw [image_append]
  rfl

/-- On a CE, the next image after an odd `OE` landing is odd and
below `n^2`. An even image would be descent. This is not a halt
theorem. -/
theorem minimal_ooeooeooeoeo_not_even {n : ℕ}
    (h : MinimalNonTerm n) (hw : follows n wordOOEOOEOOEOE) :
    follows n wordOOEOOEOOEOEO ∧ image n wordOOEOOEOOEOEO % 2 = 1 := by
  have hf := minimal_ooeooeooeoe_follows_o h hw
  refine ⟨hf, ?_⟩
  have hn2 : 2 ≤ n :=
    le_trans (by decide : (2 : ℕ) ≤ 12) (minimal_nonterm_ge_twelve h)
  have hlt := follows_ooeooeooeoeo_image_lt_sq hn2 hf
  by_contra heven
  have he : image n wordOOEOOEOOEOEO % 2 = 0 := by omega
  have hdrop : floorPower (image n wordOOEOOEOOEOEO) < n :=
    (even_floorPower_lt_iff he).mpr hlt
  exact minimal_nonterm_no_descent h
    ⟨follows_ooeooeooeoeo_even hf he, by simpa [image_ooeooeooeoeo_even] using hdrop⟩

def wordOOEOOEOOEOEOO : List Branch :=
  wordOOEOOEOOEOEO ++ [Branch.odd]

theorem wordOOEOOEOOEOEOO_length : wordOOEOOEOOEOEOO.length = 13 := by
  simp [wordOOEOOEOOEOEOO, wordOOEOOEOOEOEO, wordOOEOOEOOEOE, wordOOEOOEOOEO,
    wordOOEOOEOOE, wordOOEOOEOO, wordOOEOOEO, wordOOEOOE]

theorem wordOOEOOEOOEOEOO_oddCount : oddCount wordOOEOOEOOEOEOO = 9 := by
  simp [wordOOEOOEOOEOEOO, wordOOEOOEOOEOEO, wordOOEOOEOOEOE, wordOOEOOEOOEO,
    wordOOEOOEOOE, wordOOEOOEOO, wordOOEOOEO, wordOOEOOE]

theorem follows_wordOOEOOEOOEOEOO_of_forced_oo {n : ℕ}
    (h : follows n wordOOEOOEOOEOEO ∧ image n wordOOEOOEOOEOEO % 2 = 1) :
    follows n wordOOEOOEOOEOEOO := by
  simpa [wordOOEOOEOOEOEOO] using follows_append h.1 (follows_singleton_odd h.2)

theorem minimal_ooeooeooeoeo_follows_o {n : ℕ}
    (h : MinimalNonTerm n) (hw : follows n wordOOEOOEOOEOE) :
    follows n wordOOEOOEOOEOEOO :=
  follows_wordOOEOOEOOEOEOO_of_forced_oo (minimal_ooeooeooeoeo_not_even h hw)

theorem ooeooeooeoeoo_loses_square : ¬(3 ^ 9 < 2 ^ (13 + 1)) := by
  decide

/-- The second `O` after the new `OO` loses the square cell
(`19683 > 16384`) but keeps the cube-cell gap `24576 > 19683`.
The square comparison `3^9 < 2 · 2^13` fails; see
`ooeooeooeoeoo_loses_square`. A cube-cell even landing is therefore
not `FiniteProgress`. -/
theorem follows_ooeooeooeoeoo_image_lt_cube {n : ℕ} (hn : 2 ≤ n)
    (hw : follows n wordOOEOOEOOEOEOO) :
    image n wordOOEOOEOOEOEOO < n ^ 3 :=
  power_bound_lt_pow (k := 3) hn hw (by
    rw [wordOOEOOEOOEOEOO_length, wordOOEOOEOOEOEOO_oddCount]
    decide)

end Problems.Juggler
