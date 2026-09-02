import Problems.Juggler.CycleFinance
import Problems.Juggler.CycleFinanceLeftovers
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace Problems.Juggler

/-!
# Odd-run height law and leftover 84 with m ≥ 3

After `j` consecutive odd steps from a `CycleMin` valley the state
is at least the odd-run height given by `oddRunDepth` and the
certificates `floorPower 261 = 4216`, `floorPower 4217 = 273845`.
Combined with the inv-sum form of `cycleMin_finance`
(`cycleMin_finance_inv_sum` in `CycleFinance`, Paper A
Corollary 4.4c) this excludes every length-84 cycle with at most
two odd-runs at the residual floor 261. The leftover is period 84
with at least three odd-runs on a `CycleMin` rotation, or length
at least 85.

Writeup: `docs/theory/juggler_cycle_finance_note.md`.
Not a halt theorem. The inv-sum envelope is proved in
`CycleFinance` and imported here. This file is not imported by
`Problems.JugglerPaper`.
-/

open Finset

/-- Drop a leading odd-run. -/
def dropOddRun : List Branch → List Branch
  | .odd :: w => dropOddRun w
  | w => w

theorem dropOddRun_length_le : ∀ w : List Branch, (dropOddRun w).length ≤ w.length
  | [] => le_rfl
  | .odd :: w =>
      le_trans (dropOddRun_length_le w) (Nat.le_succ _)
  | .even :: _ => le_rfl

/-- Trailing odd-run length of a prefix. -/
def trailingOdds (w : List Branch) : ℕ :=
  (w.reverse.takeWhile (fun b => decide (b = Branch.odd))).length

theorem trailingOdds_nil : trailingOdds [] = 0 := rfl

theorem trailingOdds_append_odd (w : List Branch) :
    trailingOdds (w ++ [Branch.odd]) = trailingOdds w + 1 := by
  simp [trailingOdds, List.reverse_append]

theorem trailingOdds_append_even (w : List Branch) :
    trailingOdds (w ++ [Branch.even]) = 0 := by
  simp [trailingOdds, List.reverse_append]

/-- Depth of the odd-run containing index `i` (0 if `w[i]` is even). -/
def oddRunDepth (w : List Branch) (i : ℕ) : ℕ :=
  if h : i < w.length then
    match w[i] with
    | .even => 0
    | .odd => trailingOdds (w.take i) + 1
  else 0

/-- Number of odd-runs: indices of odd-run starts (`oddRunDepth = 1`). -/
def cycleCircuitCount (w : List Branch) : ℕ :=
  (List.range w.length).filter (fun i => oddRunDepth w i = 1) |>.length

theorem dropOddRun_even_cons (w : List Branch) :
    dropOddRun (.even :: w) = .even :: w := rfl

theorem dropOddRun_nil : dropOddRun [] = [] := rfl

theorem cycleCircuitCount_nil : cycleCircuitCount [] = 0 := rfl

theorem floorPower_two_hundred_sixty_one :
    floorPower 261 = 4216 := by
  native_decide

theorem floorPower_four_thousand_two_hundred_seventeen :
    floorPower 4217 = 273845 := by
  native_decide

theorem odd_two_hundred_sixty_one : (261 : ℕ) % 2 = 1 := by decide

theorem odd_four_thousand_two_hundred_seventeen : (4217 : ℕ) % 2 = 1 := by
  decide

/-- Least odd integer `≥ T(n)`. -/
def nextOddHeight (x : ℕ) : ℕ :=
  let t := floorPower x
  if t % 2 = 0 then t + 1 else t

/-- Odd-run height `τ_j`. `τ_0 = n`, `τ_{j+1}` is the least odd
integer `≥ T(τ_j)`. -/
def oddRunHeight (n : ℕ) : ℕ → ℕ
  | 0 => n
  | j + 1 => nextOddHeight (oddRunHeight n j)

theorem oddRunHeight_zero (n : ℕ) : oddRunHeight n 0 = n := rfl

theorem oddRunHeight_succ (n j : ℕ) :
    oddRunHeight n (j + 1) = nextOddHeight (oddRunHeight n j) :=
  rfl

theorem nextOddHeight_two_hundred_sixty_one :
    nextOddHeight 261 = 4217 := by
  simp [nextOddHeight, floorPower_two_hundred_sixty_one]

theorem oddRunHeight_one_two_hundred_sixty_one :
    oddRunHeight 261 1 = 4217 := by
  simp [oddRunHeight, nextOddHeight_two_hundred_sixty_one]

theorem oddRunHeight_two_two_hundred_sixty_one :
    oddRunHeight 261 2 = 273845 := by
  have h1 : oddRunHeight 261 1 = 4217 :=
    oddRunHeight_one_two_hundred_sixty_one
  unfold oddRunHeight nextOddHeight
  rw [h1, floorPower_four_thousand_two_hundred_seventeen]
  native_decide

theorem floorPower_odd_ge_of_ge_two_hundred_sixty_one
    {n : ℕ} (hn : 261 ≤ n) (ho : n % 2 = 1) :
    4216 ≤ floorPower n := by
  have hmono :=
    floorPower_odd_mono odd_two_hundred_sixty_one ho hn
  simpa [floorPower_two_hundred_sixty_one] using hmono

theorem floorPower_odd_ge_four_thousand_two_hundred_seventeen
    {x : ℕ} (hx : 4217 ≤ x) (ho : x % 2 = 1) :
    273845 ≤ floorPower x := by
  have hmono :=
    floorPower_odd_mono odd_four_thousand_two_hundred_seventeen ho hx
  simpa [floorPower_four_thousand_two_hundred_seventeen] using hmono

theorem cycleMin_start_odd_run {n : ℕ} {w : List Branch}
    (hn : 2 ≤ n) (h : CycleMin n w) : 1 ≤ cycleCircuitCount w := by
  have h0 : 0 < w.length := h.1.2.2
  have hfirst : w[0] = Branch.odd := by
    cases hb : w[0] with
    | odd => rfl
    | even =>
        have he := follows_get_even w h.1.1 0 h0 hb
        have ho := cycleMin_start_odd hn h
        simp at he
        omega
  have hd : oddRunDepth w 0 = 1 := by
    unfold oddRunDepth
    simp [h0, hfirst, trailingOdds_nil]
  have hmem : 0 ∈ (List.range w.length).filter (fun i => oddRunDepth w i = 1) := by
    simp [List.mem_filter, hd, h0]
  exact List.length_pos_of_mem hmem

theorem cycleMin_end_even {n : ℕ} {w : List Branch}
    (hn : 2 ≤ n) (h : CycleMin n w) :
    ∃ u, w = u ++ [.even] := by
  induction w using List.reverseRecOn with
  | nil =>
      have := h.1.2.2
      simp at this
  | append_singleton u b =>
      cases b with
      | even => exact ⟨u, rfl⟩
      | odd => exact (cycleMin_not_end_odd hn h).elim

/-- After one odd letter from a `CycleMin` valley, the image is at
least `T(261) = 4216`. -/
theorem cycleMin_first_odd_image_ge {n : ℕ} {w : List Branch} {i : ℕ}
    (hn : 261 ≤ n) (h : CycleMin n w) (hi : i < w.length)
    (hd : oddRunDepth w i = 1) :
    4216 ≤ floorPower^[i + 1] n := by
  have hn2 : 2 ≤ n := le_trans (by decide : (2 : ℕ) ≤ 261) hn
  have hletter : w[i] = Branch.odd := by
    unfold oddRunDepth at hd
    rw [dif_pos hi] at hd
    cases hb : w[i] with
    | even => simp [hb] at hd
    | odd => rfl
  have hpar : (floorPower^[i] n) % 2 = 1 :=
    follows_get_odd w h.1.1 i hi hletter
  have hval : n ≤ floorPower^[i] n := cycleMin_iterate_ge h i (Nat.le_of_lt hi)
  have hiter : floorPower^[i + 1] n = floorPower (floorPower^[i] n) :=
    Function.iterate_succ_apply' floorPower i n
  have hT : 4216 ≤ floorPower (floorPower^[i] n) :=
    floorPower_odd_ge_of_ge_two_hundred_sixty_one
      (le_trans hn hval) hpar
  simpa [hiter] using hT

theorem oddRunDepth_even {w : List Branch} {i : ℕ}
    (hi : i < w.length) (he : w[i] = Branch.even) : oddRunDepth w i = 0 := by
  unfold oddRunDepth
  simp [hi, he]

theorem oddRunDepth_odd {w : List Branch} {i : ℕ}
    (hi : i < w.length) (ho : w[i] = Branch.odd) :
    oddRunDepth w i = trailingOdds (w.take i) + 1 := by
  unfold oddRunDepth
  simp [hi, ho]

theorem oddRunDepth_le_of_odd {w : List Branch} {i : ℕ}
    (hi : i < w.length) (ho : w[i] = Branch.odd) : 1 ≤ oddRunDepth w i := by
  rw [oddRunDepth_odd hi ho]
  omega

/-- After two or more consecutive odds from a `CycleMin` valley,
the image is at least `T(4217) = 273845`. The intermediate state is
odd (the next letter is odd). -/
theorem cycleMin_later_odd_image_ge {n : ℕ} {w : List Branch} {i : ℕ}
    (hn : 261 ≤ n) (h : CycleMin n w) (hi : i < w.length)
    (hd : 2 ≤ oddRunDepth w i) :
    273845 ≤ floorPower^[i + 1] n := by
  have hn2 : 2 ≤ n := le_trans (by decide : (2 : ℕ) ≤ 261) hn
  have hletter : w[i] = Branch.odd := by
    unfold oddRunDepth at hd
    rw [dif_pos hi] at hd
    cases hb : w[i] with
    | even => simp [hb] at hd
    | odd => rfl
  have hpar : (floorPower^[i] n) % 2 = 1 :=
    follows_get_odd w h.1.1 i hi hletter
  have hd' : oddRunDepth w i = trailingOdds (w.take i) + 1 :=
    oddRunDepth_odd hi hletter
  have htr : 1 ≤ trailingOdds (w.take i) := by omega
  have hi0 : 1 ≤ i := by
    have hne : w.take i ≠ [] := by
      intro he
      rw [he, trailingOdds_nil] at htr
      omega
    have hlen : (w.take i).length = i := by
      simp [List.length_take, Nat.min_eq_left (Nat.le_of_lt hi)]
    have : 0 < i := by
      rw [← hlen]
      exact List.length_pos_iff.mpr hne
    exact Nat.succ_le_of_lt this
  have hi1 : i - 1 < w.length := Nat.lt_of_le_of_lt (Nat.sub_le i 1) hi
  have htake : w.take i = w.take (i - 1) ++ [w[i - 1]] := by
    have h1 : w.take (i - 1 + 1) = w.take (i - 1) ++ [w[i - 1]] := by
      rw [List.take_add_one, List.getElem?_eq_getElem hi1]
      rfl
    simpa [Nat.sub_add_cancel hi0] using h1
  have hprev : w[i - 1] = Branch.odd := by
    cases hb : w[i - 1] with
    | even =>
        have : trailingOdds (w.take i) = 0 := by
          rw [htake, hb, trailingOdds_append_even]
        omega
    | odd => rfl
  have hpari : (floorPower^[i - 1] n) % 2 = 1 :=
    follows_get_odd w h.1.1 (i - 1) hi1 hprev
  have hval : n ≤ floorPower^[i - 1] n :=
    cycleMin_iterate_ge h (i - 1) (Nat.le_of_lt hi1)
  have hx : floorPower^[i] n = floorPower (floorPower^[i - 1] n) := by
    conv_lhs => rw [show i = (i - 1) + 1 from (Nat.sub_add_cancel hi0).symm]
    exact Function.iterate_succ_apply' floorPower (i - 1) n
  have hxi : 4217 ≤ floorPower^[i] n := by
    have hT0 : 4216 ≤ floorPower (floorPower^[i - 1] n) :=
      floorPower_odd_ge_of_ge_two_hundred_sixty_one (le_trans hn hval) hpari
    rw [hx]
    rcases Nat.mod_two_eq_zero_or_one (floorPower (floorPower^[i - 1] n)) with he | ho'
    · have : (floorPower^[i] n) % 2 = 0 := by simpa [hx] using he
      omega
    · omega
  have hiter : floorPower^[i + 1] n = floorPower (floorPower^[i] n) :=
    Function.iterate_succ_apply' floorPower i n
  have hT : 273845 ≤ floorPower (floorPower^[i] n) :=
    floorPower_odd_ge_four_thousand_two_hundred_seventeen hxi hpar
  simpa [hiter] using hT

/-- Inv-sum terms are classified by the producing letter. -/
theorem cycleMin_inv_term_le {n : ℕ} {w : List Branch} {i : ℕ}
    (hn : 261 ≤ n) (h : CycleMin n w) (hi : i < w.length) :
    (1 : ℝ) / (floorPower^[i + 1] n) ≤
      if w[i] = .even then
        if (floorPower^[i + 1] n) % 2 = 1 then (1 : ℝ) / n
        else (1 : ℝ) / (n * n)
      else if oddRunDepth w i = 1 then (1 : ℝ) / 4217
      else (1 : ℝ) / 273845 := by
  have hn2 : 2 ≤ n := le_trans (by decide : (2 : ℕ) ≤ 261) hn
  have hx : 2 ≤ floorPower^[i + 1] n :=
    cycleMin_iterate_ge_two hn2 h (Nat.succ_le_of_lt hi)
  have hx0 : (0 : ℝ) < (floorPower^[i + 1] n : ℝ) := by
    have : 0 < floorPower^[i + 1] n := by omega
    exact_mod_cast this
  have hn0 : (0 : ℝ) < n := by
    have : 0 < n := by omega
    exact_mod_cast this
  by_cases hev : w[i] = Branch.even
  · rw [if_pos hev]
    by_cases hodd : (floorPower^[i + 1] n) % 2 = 1
    · rw [if_pos hodd]
      have hge : n ≤ floorPower^[i + 1] n :=
        cycleMin_iterate_ge h (i + 1) (Nat.succ_le_of_lt hi)
      have hgeR : (n : ℝ) ≤ (floorPower^[i + 1] n : ℝ) := by exact_mod_cast hge
      simpa [one_div] using one_div_le_one_div_of_le hn0 hgeR
    · rw [if_neg hodd]
      have hsq : n ^ 2 ≤ floorPower^[i + 1] n := by
        have hi1 : i + 1 ≤ w.length := Nat.succ_le_of_lt hi
        have himg_even : (floorPower^[i + 1] n) % 2 = 0 := by omega
        rcases lt_or_eq_of_le hi1 with hlt | heq
        · exact cycleMin_even_ge_sq hn2 h hlt himg_even
        · have hper : floorPower^[i + 1] n = n := by
            rw [heq, cycle_iterate_period h.1]
          have : n % 2 = 0 := by simpa [hper] using himg_even
          have : n % 2 = 1 := cycleMin_start_odd hn2 h
          omega
      have hsqR : (n * n : ℝ) ≤ (floorPower^[i + 1] n : ℝ) := by
        have : (n ^ 2 : ℕ) ≤ floorPower^[i + 1] n := hsq
        exact_mod_cast (by simpa [pow_two] using this)
      simpa [one_div, mul_inv] using
        (one_div_le_one_div_of_le (by positivity : (0 : ℝ) < n * n) hsqR)
  · rw [if_neg hev]
    have hb : w[i] = Branch.odd := by
      cases hbr : w[i] with
      | even => exact (hev hbr).elim
      | odd => rfl
    by_cases h1 : oddRunDepth w i = 1
    · rw [if_pos h1]
      have hge : (4217 : ℕ) ≤ floorPower^[i + 1] n := by
        rcases Nat.mod_two_eq_zero_or_one (floorPower^[i + 1] n) with he | ho
        · have hsq : n ^ 2 ≤ floorPower^[i + 1] n := by
            have hi1 : i + 1 ≤ w.length := Nat.succ_le_of_lt hi
            rcases lt_or_eq_of_le hi1 with hlt | heq
            · exact cycleMin_even_ge_sq hn2 h hlt he
            · have hper : floorPower^[i + 1] n = n := by
                rw [heq, cycle_iterate_period h.1]
              have : n % 2 = 0 := by simpa [hper] using he
              have : n % 2 = 1 := cycleMin_start_odd hn2 h
              omega
          have h4217 : (4217 : ℕ) ≤ 261 ^ 2 := by decide
          have hsqn : 261 ^ 2 ≤ n ^ 2 := Nat.pow_le_pow_left hn 2
          exact le_trans h4217 (le_trans hsqn hsq)
        · have hT := cycleMin_first_odd_image_ge hn h hi (by omega)
          omega
      have hgeR : (4217 : ℝ) ≤ (floorPower^[i + 1] n : ℝ) := by
        exact_mod_cast hge
      simpa [one_div] using
        (one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 4217) hgeR)
    · rw [if_neg h1]
      have h2 : 2 ≤ oddRunDepth w i := by
        have := oddRunDepth_le_of_odd hi hb
        omega
      have hT := cycleMin_later_odd_image_ge hn h hi h2
      have hgeR : (273845 : ℝ) ≤ (floorPower^[i + 1] n : ℝ) := by
        exact_mod_cast hT
      simpa [one_div] using
        (one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 273845) hgeR)

theorem oddRunDepth_eq_one_lt {w : List Branch} {i : ℕ}
    (h : oddRunDepth w i = 1) : i < w.length := by
  unfold oddRunDepth at h
  by_contra hne
  rw [dif_neg hne] at h
  omega

theorem oddRunDepth_eq_one_odd {w : List Branch} {i : ℕ}
    (h : oddRunDepth w i = 1) : w[i]? = some Branch.odd := by
  have hi := oddRunDepth_eq_one_lt h
  unfold oddRunDepth at h
  rw [dif_pos hi] at h
  cases hb : (w[i]'hi) with
  | even => simp [hb] at h
  | odd => simp [List.getElem?_eq_getElem hi, hb]

theorem finset_range_succ (n : ℕ) :
    Finset.range (n + 1) = insert n (Finset.range n) := by
  ext x
  simp [Finset.mem_range, Finset.mem_insert]
  omega

theorem list_range_filter_card (n : ℕ) (p : ℕ → Prop) [DecidablePred p] :
    ((List.range n).filter p).length = ((Finset.range n).filter p).card := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [List.range_succ, finset_range_succ, List.filter_append]
      have hlast : List.filter p [n] = if p n then [n] else [] := by
        by_cases hp : p n <;> simp [hp]
      rw [hlast, List.length_append, ih, Finset.filter_insert]
      by_cases hp : p n <;> simp [hp, ih]

theorem cycleCircuitCount_eq_card (w : List Branch) :
    cycleCircuitCount w =
      ((Finset.range w.length).filter (fun i => oddRunDepth w i = 1)).card := by
  simpa [cycleCircuitCount] using
    list_range_filter_card w.length (fun i => oddRunDepth w i = 1)

theorem oddCount_eq_card (w : List Branch) :
    oddCount w =
      ((Finset.range w.length).filter
        (fun i => w[i]? = some Branch.odd)).card := by
  induction w using List.reverseRecOn with
  | nil => simp
  | append_singleton u b ih =>
      have hlen : (u ++ [b]).length = u.length + 1 := by simp
      have hlast : (u ++ [b])[u.length]? = some b := by
        have hlt : u.length < (u ++ [b]).length := by simp
        rw [List.getElem?_eq_getElem hlt]
        simp
      have hprefix : ∀ i ∈ Finset.range u.length, (u ++ [b])[i]? = u[i]? := by
        intro i hi
        have hi' : i < u.length := Finset.mem_range.mp hi
        have hi'' : i < (u ++ [b]).length := Nat.lt_trans hi' (by simp)
        rw [List.getElem?_eq_getElem hi'', List.getElem?_eq_getElem hi']
        simp [List.getElem_append_left hi']
      rw [oddCount_append, hlen, finset_range_succ]
      have hcongr :
          ((Finset.range u.length).filter
              (fun i => (u ++ [b])[i]? = some Branch.odd)) =
            (Finset.range u.length).filter
              (fun i => u[i]? = some Branch.odd) :=
        Finset.filter_congr (fun i hi => by rw [hprefix i hi])
      cases b with
      | odd =>
          rw [Finset.filter_insert, if_pos (by simp [hlast])]
          have hnotin :
              u.length ∉
                (Finset.range u.length).filter
                  (fun i => (u ++ [Branch.odd])[i]? = some Branch.odd) :=
            fun hmem => Finset.notMem_range_self (Finset.mem_filter.mp hmem).1
          rw [Finset.card_insert_of_notMem hnotin, hcongr, ih]
          simp [oddCount]
      | even =>
          rw [Finset.filter_insert, if_neg (by simp [hlast]), hcongr, ih]
          simp [oddCount]

theorem cycleCircuitCount_le_oddCount (w : List Branch) :
    cycleCircuitCount w ≤ oddCount w := by
  rw [cycleCircuitCount_eq_card, oddCount_eq_card]
  refine Finset.card_le_card ?_
  intro i hi
  have hd := (Finset.mem_filter.mp hi).2
  exact Finset.mem_filter.mpr
    ⟨Finset.mem_range.mpr (oddRunDepth_eq_one_lt hd), oddRunDepth_eq_one_odd hd⟩

/-- Send an even-letter odd landing to the odd-run it starts
(wrapping the last letter onto index `0`). -/
def evenOddToClimb (L i : ℕ) : ℕ :=
  if i + 1 = L then 0 else i + 1

theorem cycleMin_next_odd_of_odd_image {n : ℕ} {w : List Branch} {i : ℕ}
    (_hn : 2 ≤ n) (h : CycleMin n w) (hi : i + 1 < w.length)
    (hodd : (floorPower^[i + 1] n) % 2 = 1) :
    w[i + 1] = Branch.odd := by
  cases hb : w[i + 1] with
  | odd => rfl
  | even =>
      have he := follows_get_even w h.1.1 (i + 1) hi hb
      omega

theorem cycleMin_internal_evenOdd_is_firstClimb {n : ℕ} {w : List Branch} {i : ℕ}
    (hn : 2 ≤ n) (h : CycleMin n w) (hi : i + 1 < w.length)
    (he : w[i] = Branch.even)
    (hodd : (floorPower^[i + 1] n) % 2 = 1) :
    oddRunDepth w (i + 1) = 1 := by
  have hnext := cycleMin_next_odd_of_odd_image hn h hi hodd
  have htake : w.take (i + 1) = w.take i ++ [w[i]] := by
    have hi0 : i < w.length := Nat.lt_of_succ_lt hi
    rw [List.take_add_one, List.getElem?_eq_getElem hi0]
    rfl
  rw [oddRunDepth_odd hi hnext, htake, he, trailingOdds_append_even]

theorem cycleMin_evenOdd_maps_to_firstClimb {n : ℕ} {w : List Branch} {i : ℕ}
    (hn : 2 ≤ n) (h : CycleMin n w) (hi : i < w.length)
    (he : w[i] = Branch.even)
    (hodd : (floorPower^[i + 1] n) % 2 = 1) :
    oddRunDepth w (evenOddToClimb w.length i) = 1 := by
  unfold evenOddToClimb
  by_cases hlast : i + 1 = w.length
  · simp [hlast]
    have h0 : 0 < w.length := h.1.2.2
    have hfirst : w[0] = Branch.odd := by
      cases hb : w[0] with
      | odd => rfl
      | even =>
          have := follows_get_even w h.1.1 0 h0 hb
          have ho := cycleMin_start_odd hn h
          simp at this
          omega
    have hd : oddRunDepth w 0 = 1 := by
      unfold oddRunDepth
      simp [h0, hfirst, trailingOdds_nil]
    exact hd
  · have hi1 : i + 1 < w.length := Nat.lt_of_le_of_ne (Nat.succ_le_of_lt hi) hlast
    simp [hlast]
    exact cycleMin_internal_evenOdd_is_firstClimb hn h hi1 he hodd

theorem evenOddToClimb_inj {L i j : ℕ} (hi : i < L) (hj : j < L)
    (h : evenOddToClimb L i = evenOddToClimb L j) : i = j := by
  unfold evenOddToClimb at h
  split_ifs at h <;> omega

theorem cycleMin_valley_card_le {n : ℕ} {w : List Branch}
    (hn : 2 ≤ n) (h : CycleMin n w) :
    ((Finset.range w.length).filter (fun i =>
        w[i]? = some Branch.even ∧
          (floorPower^[i + 1] n) % 2 = 1)).card ≤
      cycleCircuitCount w := by
  rw [cycleCircuitCount_eq_card]
  let s := (Finset.range w.length).filter (fun i =>
      w[i]? = some Branch.even ∧ (floorPower^[i + 1] n) % 2 = 1)
  let t := (Finset.range w.length).filter (fun i => oddRunDepth w i = 1)
  have hmaps : ∀ i ∈ s, evenOddToClimb w.length i ∈ t := by
    intro i hi
    have hiL : i < w.length := Finset.mem_range.mp (Finset.mem_filter.mp hi).1
    have hP := (Finset.mem_filter.mp hi).2
    have he : w[i] = Branch.even := by
      simpa [List.getElem?_eq_getElem hiL] using hP.1
    have hd := cycleMin_evenOdd_maps_to_firstClimb hn h hiL he hP.2
    have himg : evenOddToClimb w.length i < w.length := by
      unfold evenOddToClimb
      split_ifs with hlast
      · exact h.1.2.2
      · have : i + 1 ≤ w.length := Nat.succ_le_of_lt hiL
        omega
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr himg, hd⟩
  have himg : s.image (evenOddToClimb w.length) ⊆ t := by
    intro j hj
    rcases Finset.mem_image.mp hj with ⟨i, hi, rfl⟩
    exact hmaps i hi
  have hinj : Set.InjOn (evenOddToClimb w.length) (s : Set ℕ) := by
    intro i hi j hj heq
    have hiL : i < w.length :=
      Finset.mem_range.mp
        (Finset.mem_filter.mp (Finset.mem_coe.mp hi)).1
    have hjL : j < w.length :=
      Finset.mem_range.mp
        (Finset.mem_filter.mp (Finset.mem_coe.mp hj)).1
    exact evenOddToClimb_inj hiL hjL heq
  have hcard : s.card = (s.image (evenOddToClimb w.length)).card :=
    (Finset.card_image_of_injOn hinj).symm
  exact hcard ▸ Finset.card_le_card himg

noncomputable def invTermCap (n : ℕ) (w : List Branch) (i : ℕ) : ℝ :=
  if w[i]? = some Branch.even then
    if (floorPower^[i + 1] n) % 2 = 1 then (1 : ℝ) / n
    else (1 : ℝ) / (n * n)
  else if oddRunDepth w i = 1 then (1 : ℝ) / 4217
  else (1 : ℝ) / 273845

theorem invTermCap_of_mem {n : ℕ} {w : List Branch} {i : ℕ}
    (hi : i < w.length) :
    invTermCap n w i =
      if w[i] = Branch.even then
        if (floorPower^[i + 1] n) % 2 = 1 then (1 : ℝ) / n
        else (1 : ℝ) / (n * n)
      else if oddRunDepth w i = 1 then (1 : ℝ) / 4217
      else (1 : ℝ) / 273845 := by
  unfold invTermCap
  simp [List.getElem?_eq_getElem hi]

theorem cycleMin_inv_term_le_cap {n : ℕ} {w : List Branch} {i : ℕ}
    (hn : 261 ≤ n) (h : CycleMin n w) (hi : i < w.length) :
    (1 : ℝ) / (floorPower^[i + 1] n) ≤ invTermCap n w i := by
  simpa [invTermCap_of_mem hi] using cycleMin_inv_term_le hn h hi

theorem invTermCap_le_parts (n : ℕ) (w : List Branch) {i : ℕ}
    (hi : i < w.length) :
    invTermCap n w i ≤
      (if oddRunDepth w i = 1 then (1 : ℝ) / 4217 else 0) +
        (if w[i]? = some Branch.odd then (1 : ℝ) / 273845 else 0) +
          (if w[i]? = some Branch.even ∧
              (floorPower^[i + 1] n) % 2 = 1 then (1 : ℝ) / n else 0) +
            (if w[i]? = some Branch.even then (1 : ℝ) / (n * n) else 0) := by
  have hget : w[i]? = some (w[i]'hi) := List.getElem?_eq_getElem hi
  have hfirst0 : (0 : ℝ) ≤ if oddRunDepth w i = 1 then (1 : ℝ) / 4217 else 0 := by
    split_ifs <;> positivity
  have hsq0 : (0 : ℝ) ≤ (1 : ℝ) / (n * n) := by positivity
  have hlat0 : (0 : ℝ) ≤ (1 : ℝ) / 273845 := by positivity
  cases hbr : (w[i]'hi) with
  | even =>
      have he : w[i]? = some Branch.even := by rw [hget, hbr]
      have hodd : w[i]? ≠ some Branch.odd := by
        rw [he]
        decide
      have hcap : invTermCap n w i =
          if (floorPower^[i + 1] n) % 2 = 1 then (1 : ℝ) / n
          else (1 : ℝ) / (n * n) := by
        unfold invTermCap
        simp only [he, ite_true]
      have hlat : (if w[i]? = some Branch.odd then (1 : ℝ) / 273845 else 0) = (0 : ℝ) := by
        simp only [hodd, ite_false]
      have hsq : (if w[i]? = some Branch.even then (1 : ℝ) / (n * n) else 0) =
          (1 : ℝ) / (n * n) := by
        simp only [he, ite_true]
      have hvalley :
          (if w[i]? = some Branch.even ∧ (floorPower^[i + 1] n) % 2 = 1
            then (1 : ℝ) / n else 0) =
            if (floorPower^[i + 1] n) % 2 = 1 then (1 : ℝ) / n else 0 := by
        simp only [he, true_and]
      rw [hcap, hlat, hsq, hvalley]
      by_cases hval : (floorPower^[i + 1] n) % 2 = 1
      · simp only [hval, ite_true]
        linarith [hfirst0, hsq0]
      · simp only [hval, ite_false]
        linarith [hfirst0]
  | odd =>
      have ho : w[i]? = some Branch.odd := by rw [hget, hbr]
      have he : w[i]? ≠ some Branch.even := by
        rw [ho]
        decide
      have hcap : invTermCap n w i =
          if oddRunDepth w i = 1 then (1 : ℝ) / 4217
          else (1 : ℝ) / 273845 := by
        unfold invTermCap
        simp only [he, ite_false]
      have hlat : (if w[i]? = some Branch.odd then (1 : ℝ) / 273845 else 0) =
          (1 : ℝ) / 273845 := by
        simp only [ho, ite_true]
      have hsq : (if w[i]? = some Branch.even then (1 : ℝ) / (n * n) else 0) = (0 : ℝ) := by
        simp only [he, ite_false]
      have hvalley :
          (if w[i]? = some Branch.even ∧ (floorPower^[i + 1] n) % 2 = 1
            then (1 : ℝ) / n else 0) = (0 : ℝ) := by
        simp only [he, false_and, ite_false]
      rw [hcap, hlat, hsq, hvalley]
      by_cases hd : oddRunDepth w i = 1
      · simp only [hd, ite_true]
        linarith [hlat0]
      · simp only [hd, ite_false]
        linarith

theorem sum_ite_const_eq_card (s : Finset ℕ) (p : ℕ → Prop)
    [DecidablePred p] (c : ℝ) :
    ∑ i ∈ s, (if p i then c else (0 : ℝ)) = c * (s.filter p).card := by
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  ring

theorem evenLetter_card (w : List Branch) :
    ((Finset.range w.length).filter
        (fun i => w[i]? = some Branch.even)).card =
      w.length - oddCount w := by
  have hcomp : ∀ i ∈ Finset.range w.length,
      (w[i]? = some Branch.odd) ↔ ¬ (w[i]? = some Branch.even) := by
    intro i hi
    have hlt : i < w.length := Finset.mem_range.mp hi
    cases hb : (w[i]'hlt) with
    | odd => simp [List.getElem?_eq_getElem hlt, hb]
    | even => simp [List.getElem?_eq_getElem hlt, hb]
  have hnot :
      (Finset.range w.length).filter (fun i => ¬ w[i]? = some Branch.even) =
        (Finset.range w.length).filter (fun i => w[i]? = some Branch.odd) :=
    Finset.filter_congr (fun i hi => (hcomp i hi).symm)
  have hsdiff :
      (Finset.range w.length).filter (fun i => ¬ w[i]? = some Branch.even) =
        Finset.range w.length \
          (Finset.range w.length).filter (fun i => w[i]? = some Branch.even) :=
    Finset.filter_not
      (p := fun i : ℕ => w[i]? = some Branch.even) (Finset.range w.length)
  have hsub :
      ((Finset.range w.length).filter
          (fun i => w[i]? = some Branch.odd)).card +
        ((Finset.range w.length).filter
            (fun i => w[i]? = some Branch.even)).card =
        w.length := by
    have hss :=
      Finset.card_sdiff_add_card_eq_card
        (Finset.filter_subset
          (fun i => w[i]? = some Branch.even) (Finset.range w.length))
    rw [← hsdiff, hnot] at hss
    simpa [Finset.card_range] using hss
  have ho := oddCount_eq_card w
  have hle : oddCount w ≤ w.length := oddCount_le_length w
  omega

theorem cycleMin_inv_sum_le_pack {n : ℕ} {w : List Branch}
    (hn : 261 ≤ n) (h : CycleMin n w) :
    ∑ i ∈ Finset.range w.length, (1 : ℝ) / (floorPower^[i + 1] n) ≤
      (cycleCircuitCount w : ℝ) / n +
        (cycleCircuitCount w : ℝ) / 4217 +
          (oddCount w : ℝ) / 273845 +
            ((w.length - oddCount w : ℕ) : ℝ) / (n * n) := by
  have hn2 : 2 ≤ n := le_trans (by decide : (2 : ℕ) ≤ 261) hn
  have hterm :
      ∑ i ∈ Finset.range w.length, (1 : ℝ) / (floorPower^[i + 1] n) ≤
        ∑ i ∈ Finset.range w.length, invTermCap n w i :=
    Finset.sum_le_sum fun i hi =>
      cycleMin_inv_term_le_cap hn h (Finset.mem_range.mp hi)
  have hparts :
      ∑ i ∈ Finset.range w.length, invTermCap n w i ≤
        ∑ i ∈ Finset.range w.length,
            ((if oddRunDepth w i = 1 then (1 : ℝ) / 4217 else 0) +
              (if w[i]? = some Branch.odd then (1 : ℝ) / 273845 else 0) +
                (if w[i]? = some Branch.even ∧
                    (floorPower^[i + 1] n) % 2 = 1 then (1 : ℝ) / n
                  else 0) +
                  (if w[i]? = some Branch.even then (1 : ℝ) / (n * n)
                    else 0)) :=
    Finset.sum_le_sum fun i hi =>
      invTermCap_le_parts n w (Finset.mem_range.mp hi)
  have hsum4 :
      ∑ i ∈ Finset.range w.length,
          ((if oddRunDepth w i = 1 then (1 : ℝ) / 4217 else 0) +
            (if w[i]? = some Branch.odd then (1 : ℝ) / 273845 else 0) +
              (if w[i]? = some Branch.even ∧
                  (floorPower^[i + 1] n) % 2 = 1 then (1 : ℝ) / n else 0) +
                (if w[i]? = some Branch.even then (1 : ℝ) / (n * n)
                  else 0)) =
        ((Finset.range w.length).filter
            (fun i => oddRunDepth w i = 1)).card * ((1 : ℝ) / 4217) +
          ((Finset.range w.length).filter
              (fun i => w[i]? = some Branch.odd)).card *
            ((1 : ℝ) / 273845) +
            ((Finset.range w.length).filter (fun i =>
                w[i]? = some Branch.even ∧
                  (floorPower^[i + 1] n) % 2 = 1)).card *
              ((1 : ℝ) / n) +
              ((Finset.range w.length).filter
                  (fun i => w[i]? = some Branch.even)).card *
                ((1 : ℝ) / (n * n)) := by
    simp_rw [Finset.sum_add_distrib]
    rw [sum_ite_const_eq_card, sum_ite_const_eq_card,
      sum_ite_const_eq_card, sum_ite_const_eq_card]
    ring
  have hm := cycleMin_valley_card_le hn2 h
  have ho := (oddCount_eq_card w).symm
  have hf := (cycleCircuitCount_eq_card w).symm
  have he := evenLetter_card w
  have hmR : (((Finset.range w.length).filter (fun i =>
        w[i]? = some Branch.even ∧
          (floorPower^[i + 1] n) % 2 = 1)).card : ℝ) ≤
      (cycleCircuitCount w : ℝ) := by exact_mod_cast hm
  calc
    ∑ i ∈ Finset.range w.length, (1 : ℝ) / (floorPower^[i + 1] n)
        ≤ ∑ i ∈ Finset.range w.length, invTermCap n w i := by exact hterm
      _ ≤ ∑ i ∈ Finset.range w.length,
            ((if oddRunDepth w i = 1 then (1 : ℝ) / 4217 else 0) +
              (if w[i]? = some Branch.odd then (1 : ℝ) / 273845 else 0) +
                (if w[i]? = some Branch.even ∧
                    (floorPower^[i + 1] n) % 2 = 1 then (1 : ℝ) / n
                  else 0) +
                  (if w[i]? = some Branch.even then (1 : ℝ) / (n * n)
                    else 0)) := by exact hparts
      _ = ((Finset.range w.length).filter
              (fun i => oddRunDepth w i = 1)).card * ((1 : ℝ) / 4217) +
            ((Finset.range w.length).filter
                (fun i => w[i]? = some Branch.odd)).card *
              ((1 : ℝ) / 273845) +
              ((Finset.range w.length).filter (fun i =>
                  w[i]? = some Branch.even ∧
                    (floorPower^[i + 1] n) % 2 = 1)).card *
                ((1 : ℝ) / n) +
                ((Finset.range w.length).filter
                    (fun i => w[i]? = some Branch.even)).card *
                  ((1 : ℝ) / (n * n)) := by exact hsum4
      _ = (cycleCircuitCount w : ℝ) * (1 / 4217) +
            (oddCount w : ℝ) * (1 / 273845) +
              (((Finset.range w.length).filter (fun i =>
                  w[i]? = some Branch.even ∧
                    (floorPower^[i + 1] n) % 2 = 1)).card : ℝ) *
                (1 / n) +
                ((w.length - oddCount w : ℕ) : ℝ) * (1 / (n * n)) := by
          rw [hf, ho, he]
          try ring
      _ ≤ (cycleCircuitCount w : ℝ) * (1 / 4217) +
            (oddCount w : ℝ) * (1 / 273845) +
              (cycleCircuitCount w : ℝ) * (1 / n) +
                ((w.length - oddCount w : ℕ) : ℝ) * (1 / (n * n)) := by
          have hpos : (0 : ℝ) ≤ 1 / n := by positivity
          gcongr
      _ = (cycleCircuitCount w : ℝ) / n +
            (cycleCircuitCount w : ℝ) / 4217 +
              (oddCount w : ℝ) / 273845 +
                ((w.length - oddCount w : ℕ) : ℝ) / (n * n) := by
          ring

/-- Uniform inv-sum cap for `L = 84`, `m ≤ 2`, `o ≥ 53`, `n ≥ 261`. -/
theorem l84_height_cap_nat :
    61 * (3 ^ 53 - 2 ^ 84) * 78666428148165 >
      11 * 3 ^ 53 * 700046369923 := by
  native_decide

theorem l84_height_cap_eq :
    (2 : ℝ) / 261 + (2 : ℝ) / 4217 + (84 : ℝ) / 273845 + (31 : ℝ) / 68121 =
      (700046369923 : ℝ) / 78666428148165 := by
  norm_num

theorem l84_height_cap_lt_log :
    (700046369923 : ℝ) / 78666428148165 < (61 : ℝ) / 11 := by
  have h : (11 : ℕ) * 700046369923 < 61 * 78666428148165 := by
    native_decide
  have hR : (11 : ℝ) * 700046369923 < 61 * 78666428148165 := by
    exact_mod_cast h
  have hden : (0 : ℝ) < 78666428148165 := by norm_num
  have h11 : (0 : ℝ) < 11 := by norm_num
  rw [div_lt_div_iff₀ hden h11]
  linarith

theorem cycleMin_l84_inv_sum_le_cap {n : ℕ} {w : List Branch}
    (hn : 261 ≤ n) (h : CycleMin n w)
    (hL : w.length = 84) (hm : cycleCircuitCount w ≤ 2)
    (ho : 53 ≤ oddCount w) :
    ∑ i ∈ Finset.range w.length, (1 : ℝ) / (floorPower^[i + 1] n) ≤
      (2 : ℝ) / 261 + (2 : ℝ) / 4217 + (84 : ℝ) / 273845 +
        (31 : ℝ) / 68121 := by
  have hpack := cycleMin_inv_sum_le_pack hn h
  have hle_o : oddCount w ≤ 84 := by
    simpa [hL] using oddCount_le_length w
  have heven : w.length - oddCount w ≤ 31 := by omega
  have hninv : (1 : ℝ) / n ≤ (1 : ℝ) / 261 :=
    one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 261)
      (by exact_mod_cast hn)
  have hnsq : (1 : ℝ) / (n * n) ≤ (1 : ℝ) / 68121 := by
    have hsq : (261 : ℕ) * 261 ≤ n * n := Nat.mul_le_mul hn hn
    have hsqR : (68121 : ℝ) ≤ (n * n : ℝ) := by
      have heq : (261 * 261 : ℕ) = 68121 := by decide
      exact_mod_cast (heq ▸ hsq)
    exact one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 68121) hsqR
  have hmR : (cycleCircuitCount w : ℝ) ≤ 2 := by exact_mod_cast hm
  have hoR : (oddCount w : ℝ) ≤ 84 := by exact_mod_cast hle_o
  have heR : ((w.length - oddCount w : ℕ) : ℝ) ≤ 31 := by exact_mod_cast heven
  have h1 : (cycleCircuitCount w : ℝ) / n ≤ 2 / 261 := by
    have := mul_le_mul hmR hninv (by positivity) (by norm_num)
    simpa [div_eq_mul_inv] using this
  have h2 : (cycleCircuitCount w : ℝ) / 4217 ≤ 2 / 4217 := by
    have hpos : (0 : ℝ) ≤ 1 / 4217 := by positivity
    simpa [div_eq_mul_inv] using mul_le_mul_of_nonneg_right hmR hpos
  have h3 : (oddCount w : ℝ) / 273845 ≤ 84 / 273845 := by
    have hpos : (0 : ℝ) ≤ 1 / 273845 := by positivity
    simpa [div_eq_mul_inv] using mul_le_mul_of_nonneg_right hoR hpos
  have h4 : ((w.length - oddCount w : ℕ) : ℝ) / (n * n) ≤ 31 / 68121 := by
    have := mul_le_mul heR hnsq (by positivity) (by norm_num)
    simpa [div_eq_mul_inv] using this
  linarith [hpack, h1, h2, h3, h4]

theorem no_cycleMin_length_eighty_four_of_circuit_le_two
    {n : ℕ} {w : List Branch}
    (hn : 2 ≤ n) (h : CycleMin n w) (hL : w.length = 84)
    (hm : cycleCircuitCount w ≤ 2) : False := by
  have hn261 : 261 ≤ n := by
    simpa using
      (cycleItinerary_iterate_not_lt_two_hundred_sixty_one (i := 0) hn h.1)
  have ho : 53 ≤ oddCount w := by
    have hpred : (3 : ℕ) ^ 52 ≤ 2 ^ w.length := by
      rw [hL]
      native_decide
    exact Nat.succ_le_of_lt (cycle_oddCount_gt_of_three_pow_le hn h.1 hpred)
  have hn2 : 2 ≤ n := hn
  have hfin := cycleMin_finance_inv_sum hn2 h
  have hS := cycleMin_l84_inv_sum_le_cap hn261 h hL hm ho
  have hexp : (2 : ℝ) ^ w.length < (3 : ℝ) ^ oddCount w := by
    exact_mod_cast cycle_itinerary_formally_expanding hn h.1
  have hlog : (61 / 11 : ℝ) < Real.log n := by
    have hle257 : (257 : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast (le_trans (by decide : (257 : ℕ) ≤ 261) hn261)
    have hmono : Real.log (257 : ℝ) ≤ Real.log n :=
      Real.log_le_log (by norm_num) hle257
    linarith [log_two_hundred_fifty_seven_gt]
  have hposA : (0 : ℝ) < (3 : ℝ) ^ oddCount w - (2 : ℝ) ^ w.length :=
    sub_pos.mpr hexp
  have hpos3 : (0 : ℝ) < (3 : ℝ) ^ oddCount w := by positivity
  have hS0 :
      ∑ i ∈ Finset.range w.length, (1 : ℝ) / (floorPower^[i + 1] n) ≤
        (700046369923 : ℝ) / 78666428148165 := by
    simpa [l84_height_cap_eq] using hS
  have hA53 : (3 : ℝ) ^ 53 ≤ (3 : ℝ) ^ oddCount w := by
    have : (3 : ℕ) ^ 53 ≤ 3 ^ oddCount w :=
      Nat.pow_le_pow_right (by norm_num) ho
    exact_mod_cast this
  have hL2 : (2 : ℝ) ^ w.length = (2 : ℝ) ^ 84 := by simp [hL]
  have hlePow : (2 : ℕ) ^ 84 ≤ 3 ^ 53 := by native_decide
  have hsub : ((3 ^ 53 - 2 ^ 84 : ℕ) : ℝ) = (3 : ℝ) ^ 53 - (2 : ℝ) ^ 84 := by
    rw [Nat.cast_sub hlePow]
    norm_cast
  have hN :
      (61 : ℝ) * ((3 ^ 53 - 2 ^ 84 : ℕ) : ℝ) * 78666428148165 >
        (11 : ℝ) * (3 : ℝ) ^ 53 * 700046369923 := by
    exact_mod_cast l84_height_cap_nat
  have h53 :
      (61 / 11 : ℝ) * ((3 : ℝ) ^ 53 - (2 : ℝ) ^ 84) >
        (3 : ℝ) ^ 53 * ((700046369923 : ℝ) / 78666428148165) := by
    have hden : (0 : ℝ) < 78666428148165 := by norm_num
    have h11 : (0 : ℝ) < 11 := by norm_num
    rw [← hsub] at *
    field_simp
    linarith [hN]
  have hS0lt : (700046369923 : ℝ) / 78666428148165 < 61 / 11 :=
    l84_height_cap_lt_log
  have hmono :
      (61 / 11 : ℝ) * ((3 : ℝ) ^ 53 - (2 : ℝ) ^ 84) -
          (3 : ℝ) ^ 53 * ((700046369923 : ℝ) / 78666428148165) ≤
        (61 / 11 : ℝ) * ((3 : ℝ) ^ oddCount w - (2 : ℝ) ^ 84) -
          (3 : ℝ) ^ oddCount w * ((700046369923 : ℝ) / 78666428148165) := by
    have hc : (0 : ℝ) ≤ 61 / 11 - (700046369923 : ℝ) / 78666428148165 :=
      sub_nonneg.mpr hS0lt.le
    have := mul_le_mul_of_nonneg_right hA53 hc
    linarith
  have ho_gt :
      (61 / 11 : ℝ) * ((3 : ℝ) ^ oddCount w - (2 : ℝ) ^ w.length) >
        (3 : ℝ) ^ oddCount w * ((700046369923 : ℝ) / 78666428148165) := by
    rw [hL2]
    linarith
  have hfin' :
      ((3 : ℝ) ^ oddCount w - (2 : ℝ) ^ w.length) * Real.log n ≤
        (3 : ℝ) ^ oddCount w *
          ((700046369923 : ℝ) / 78666428148165) :=
    le_trans hfin (mul_le_mul_of_nonneg_left hS0 hpos3.le)
  have hleft :
      ((3 : ℝ) ^ oddCount w - (2 : ℝ) ^ w.length) * (61 / 11) ≤
        ((3 : ℝ) ^ oddCount w - (2 : ℝ) ^ w.length) * Real.log n :=
    mul_le_mul_of_nonneg_left hlog.le hposA.le
  have : (61 / 11 : ℝ) * ((3 : ℝ) ^ oddCount w - (2 : ℝ) ^ w.length) ≤
      (3 : ℝ) ^ oddCount w * ((700046369923 : ℝ) / 78666428148165) := by
    linarith
  exact not_le_of_gt ho_gt this

/-- Length `84` with at most two odd-runs is impossible. -/
theorem no_length_eighty_four_circuit_le_two
    {n : ℕ} {w : List Branch}
    (hn : 2 ≤ n) (hL : w.length = 84) (h : CycleItinerary n w)
    {k : ℕ} (hk : k < w.length)
    (hmin : CycleMin (floorPower^[k] n) (rotateItinerary w k))
    (hm : cycleCircuitCount (rotateItinerary w k) ≤ 2) : False := by
  have hlen : (rotateItinerary w k).length = 84 := by
    simpa [rotateItinerary_length, hL]
  have hm2 : 2 ≤ floorPower^[k] n :=
    cycleItinerary_iterate_ge_two hn h hk
  exact no_cycleMin_length_eighty_four_of_circuit_le_two hm2 hmin hlen hm

/-- If a nontrivial cycle exists, it is period `84` with at least
three odd-runs on a `CycleMin` rotation, or else length at least
`85`. -/
theorem cycle_itinerary_length_eighty_four_m_ge_three_or_ge_eighty_five
    {n : ℕ} {w : List Branch}
    (hn : 2 ≤ n) (h : CycleItinerary n w) :
    (w.length = 84 ∧ ∃ k < w.length,
        CycleMin (floorPower^[k] n) (rotateItinerary w k) ∧
          3 ≤ cycleCircuitCount (rotateItinerary w k)) ∨
      85 ≤ w.length := by
  rcases cycle_itinerary_length_eighty_four_or_ge_eighty_five hn h with h84 | h85
  · obtain ⟨k, hk, hmin⟩ := exists_cycleMin hn h
    refine Or.inl ⟨h84, k, hk, hmin, ?_⟩
    by_contra hm
    exact no_length_eighty_four_circuit_le_two hn h84 h hk hmin
      (Nat.le_of_lt_succ (lt_of_not_ge hm))
  · exact Or.inr h85

end Problems.Juggler
