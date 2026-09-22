import Problems.Juggler.RateFreeDensity

namespace Problems.Juggler

open Finset

/-!
# Cylinder energy and the first-letter bias (Section 10, the counting identity)

Paper C (`docs/theory/juggler_fate_almost_all_note.md`), Section 10(d). With
`D(w) = #[wO] - #[w]/2` the bias of a cylinder towards an odd next letter and
`C_t = Σ_{|w|=t} #[w]²` the energy at depth `t`, the note records the exact identity
```
Σ_{|w|=t} D(w)² = 2^{-t-2} Σ_S |W_{S ∪ {t}}|² = C_{t+1}/2 - C_t/4.
```
The second equality is counting and is what the argument uses; it is `sum_bias_sq` here.
The first equality is Parseval for the Walsh sums on the same starts and is **not**
formalized: no Walsh transform appears in this file.

Everything is stated for an arbitrary finite set `S` of starts, so it covers the note's odd
starts of a dyadic block and the full range `{1, …, N}` alike. The one input is that a
cylinder splits into its two children, `#[w] = #[wE] + #[wO]` (`wordCount_split`), which
holds because the `(t+1)`-st letter of a start's itinerary is the parity of its `t`-th image
(`itinerary_succ_append`). The rest is `(b - (a+b)/2)² = (a² + b²)/2 - (a+b)²/4`.

Nothing here bounds a discrepancy, supplies the exceptional-atom estimate the note asks for,
or is a halt theorem.
-/

namespace CylinderEnergy

/-- The `(d+1)`-st letter of an itinerary is the parity of the `d`-th image, so depth grows
by appending on the right. -/
theorem itinerary_succ_append (n d : ℕ) :
    itinerary n (d + 1) = itinerary n d ++ [bit (floorPower^[d] n)] := by
  induction d generalizing n with
  | zero => simp [itinerary_succ, itinerary_zero]
  | succ d ih =>
      rw [itinerary_succ, ih (floorPower n), ← List.cons_append, ← itinerary_succ,
        Function.iterate_succ_apply]

/-- `#[w]`: the starts of `S` whose length-`|w|` itinerary is `w`. -/
def wordCount (S : Finset ℕ) (w : List Branch) : ℕ :=
  {n ∈ S | itinerary n w.length = w}.card

/-- A cylinder is the disjoint union of its two children: `#[w] = #[wE] + #[wO]`. -/
theorem wordCount_split (S : Finset ℕ) (w : List Branch) :
    wordCount S w = wordCount S (w ++ [Branch.even]) + wordCount S (w ++ [Branch.odd]) := by
  classical
  have key : ∀ b : Branch, wordCount S (w ++ [b]) =
      {n ∈ S | itinerary n w.length = w ∧ bit (floorPower^[w.length] n) = b}.card := by
    intro b
    unfold wordCount
    congr 1
    apply Finset.filter_congr
    intro n _
    constructor
    · intro h
      rw [List.length_append, List.length_cons, List.length_nil, itinerary_succ_append] at h
      have hlen : (itinerary n w.length).length = w.length := itinerary_length n w.length
      obtain ⟨h1, h2⟩ := List.append_inj h hlen
      exact ⟨h1, by simpa using h2⟩
    · rintro ⟨h1, h2⟩
      rw [List.length_append, List.length_cons, List.length_nil, itinerary_succ_append, h1, h2]
  rw [key, key]
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := {n ∈ S | itinerary n w.length = w})
    (fun n => bit (floorPower^[w.length] n) = Branch.even)
  unfold wordCount
  rw [← hsplit, Finset.filter_filter, Finset.filter_filter]
  congr 2
  ext n
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hS, hit, hne⟩
    exact ⟨hS, hit, by cases hb : bit (floorPower^[w.length] n) <;> simp_all⟩
  · rintro ⟨hS, hit, ho⟩
    exact ⟨hS, hit, by rw [ho]; simp⟩

/-- `C_t = Σ_{|w| = t} #[w]²`, the energy of the depth-`t` cylinders. -/
noncomputable def energy (S : Finset ℕ) (t : ℕ) : ℝ :=
  ∑ w ∈ allWords t, (wordCount S w : ℝ) ^ 2

/-- `D(w) = #[wO] - #[w]/2`, the bias of a cylinder towards an odd next letter. -/
noncomputable def bias (S : Finset ℕ) (w : List Branch) : ℝ :=
  (wordCount S (w ++ [Branch.odd]) : ℝ) - (wordCount S w : ℝ) / 2

theorem energy_succ (S : Finset ℕ) (t : ℕ) :
    energy S (t + 1) = ∑ w ∈ allWords t,
      ((wordCount S (w ++ [Branch.even]) : ℝ) ^ 2
        + (wordCount S (w ++ [Branch.odd]) : ℝ) ^ 2) := by
  classical
  have hdisj : ∀ x ∈ allWords t, ∀ y ∈ allWords t, x ≠ y →
      Disjoint ({x ++ [Branch.even], x ++ [Branch.odd]} : Finset (List Branch))
        {y ++ [Branch.even], y ++ [Branch.odd]} := by
    intro x hx y hy hne
    have hlen : x.length = y.length := by
      rw [mem_allWords.mp hx, mem_allWords.mp hy]
    simp only [Finset.disjoint_insert_left, Finset.mem_insert, Finset.mem_singleton,
      Finset.disjoint_singleton_left]
    constructor
    · rintro (h | h)
      · exact hne (List.append_inj h hlen).1
      · exact absurd (List.append_inj h hlen).2 (by simp)
    · rintro (h | h)
      · exact absurd (List.append_inj h hlen).2 (by simp)
      · exact hne (List.append_inj h hlen).1
  rw [energy, allWords, Finset.sum_biUnion hdisj]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [Finset.sum_pair (by simp)]

/-- **The counting identity of Section 10(d).** `Σ_{|w|=t} D(w)² = C_{t+1}/2 - C_t/4`,
exactly. The Parseval form of the same quantity in terms of Walsh sums is not formalized. -/
theorem sum_bias_sq (S : Finset ℕ) (t : ℕ) :
    ∑ w ∈ allWords t, bias S w ^ 2 = energy S (t + 1) / 2 - energy S t / 4 := by
  rw [energy_succ, energy, Finset.sum_div, Finset.sum_div, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun w _ => ?_
  have hsplit : (wordCount S w : ℝ)
      = (wordCount S (w ++ [Branch.even]) : ℝ) + (wordCount S (w ++ [Branch.odd]) : ℝ) := by
    exact_mod_cast congrArg (fun k : ℕ => (k : ℝ)) (wordCount_split S w)
  unfold bias
  rw [hsplit]
  ring

end CylinderEnergy

end Problems.Juggler
