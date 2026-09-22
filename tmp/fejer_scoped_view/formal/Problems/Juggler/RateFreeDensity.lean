import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
import Problems.Juggler.Progress

namespace Problems.Juggler

open Finset

/-!
# Rate-free density-one reductions (exact combinatorial layer)

The exact layer of the K3 rate-free dossier
(`docs/problems/juggler_k3_rate_free.md`).

Already in `Progress.lean`: one certificate plus induction gives
`ReachesOne`, and a *universal* finite-progress hypothesis gives
`ReachesOne` for every positive start. This file adds the
parameterized residual-floor wrapper, the finite Proposition J
count, the generating-function domination of the biased-split
reduction, and the fair-then-all-odd word weights that keep a
positive live mass at every bounded depth.

Nothing here is a halt theorem, a density-one claim about the
Juggler map, or a pressure bound. The live tower conjecture is
not formalized. The words of incompleteness do not appear.
-/

/-- Every start above a residual floor carries a finite-progress
certificate, and every positive start at most the floor already
reaches `1`. Then every positive start reaches `1`. The certificate
hypothesis is universal, not a density statement. -/
theorem reachesOne_of_floor_and_certificates {N0 : ℕ}
    (hfloor : ∀ m, 1 ≤ m → m ≤ N0 → ReachesOne m)
    (hcert : ∀ n, N0 < n → FiniteProgress n) :
    ∀ n, 1 ≤ n → ReachesOne n := by
  intro n hn
  induction n using Nat.strong_induction_on with
  | h n ih =>
      match n with
      | 0 => omega
      | 1 => exact reachesOne_one
      | n + 2 =>
          by_cases hle : n + 2 ≤ N0
          · exact hfloor (n + 2) (by omega) hle
          · exact reachesOne_of_finiteProgress
              (fun m hm0 hmlt => ih m hmlt hm0)
              (hcert (n + 2) (Nat.lt_of_not_ge hle))

instance : DecidablePred exponentGap :=
  fun w => inferInstanceAs (Decidable (3 ^ oddCount w < 2 ^ w.length))

instance instDecidablePrefixNoncontracting (w : List Branch) :
    Decidable (prefixNoncontracting w) :=
  decidable_of_iff (∀ k : Fin (w.length + 1), ¬exponentGap (w.take k.val))
    ⟨fun h k hk => h ⟨k, Nat.lt_succ_of_le hk⟩,
     fun h ⟨k, hk⟩ => h k (Nat.le_of_lt_succ hk)⟩

/-- All parity words of length `d`, built by appending the next letter. -/
def allWords : ℕ → Finset (List Branch)
  | 0 => {[]}
  | n + 1 =>
      (allWords n).biUnion fun w => {w ++ [.even], w ++ [.odd]}

theorem mem_allWords {d : ℕ} {w : List Branch} :
    w ∈ allWords d ↔ w.length = d := by
  induction d generalizing w with
  | zero =>
      simp [allWords, List.length_eq_zero_iff]
  | succ d ih =>
      constructor
      · intro h
        simp [allWords, mem_biUnion] at h
        obtain ⟨u, hu, hmem⟩ := h
        have hulen : u.length = d := ih.mp hu
        rcases hmem with h | h
        · simp [h, hulen]
        · simp [h, hulen]
      · intro hlen
        simp [allWords, mem_biUnion]
        have hdlen : (w.drop d).length = 1 := by
          simp [List.length_drop, hlen]
        obtain ⟨b, hb⟩ := List.length_eq_one_iff.mp hdlen
        let u := w.take d
        have hu : u.length = d := by
          simp [u, List.length_take, hlen]
        have hw' : w = u ++ [b] := by
          calc
            w = w.take d ++ w.drop d := (List.take_append_drop d w).symm
            _ = u ++ [b] := by rw [hb]
        refine ⟨u, ih.mpr hu, ?_⟩
        rw [hw']
        cases b <;> simp [u]

theorem itinerary_mem_allWords (n d : ℕ) : itinerary n d ∈ allWords d :=
  mem_allWords.mpr (itinerary_length n d)

/-- Starts in `{1, …, N}` whose length-`|w|` itinerary is `w`. -/
def classCount (w : List Branch) (N : ℕ) : ℕ :=
  ((Icc 1 N).filter (fun n => itinerary n w.length = w)).card

theorem classCount_eq {d N : ℕ} {w : List Branch} (hw : w ∈ allWords d) :
    classCount w N = ((Icc 1 N).filter (fun n => itinerary n d = w)).card := by
  simp [classCount, mem_allWords.mp hw]

theorem classCount_fiber_disjoint {d N : ℕ} {x y : List Branch}
    (hne : x ≠ y) :
    Disjoint
      ((Icc 1 N).filter (fun n => itinerary n d = x))
      ((Icc 1 N).filter (fun n => itinerary n d = y)) := by
  rw [disjoint_left]
  intro n hx hy
  simp only [mem_filter] at hx hy
  exact hne (hx.2.symm.trans hy.2)

/-- Length-`d` itineraries partition `{1, …, N}`. -/
theorem classCount_sum (d N : ℕ) :
    ∑ w ∈ allWords d, classCount w N = N := by
  have hcard : (Icc 1 N).card = N := by
    rw [Nat.card_Icc]
    omega
  have hunion :
      Icc 1 N =
        (allWords d).biUnion fun w =>
          (Icc 1 N).filter (fun n => itinerary n d = w) := by
    ext n
    simp only [mem_biUnion, mem_filter, mem_Icc]
    constructor
    · intro hn
      exact ⟨itinerary n d, itinerary_mem_allWords n d, hn, rfl⟩
    · intro ⟨w, _hw, hn, _heq⟩
      exact hn
  have hdisj :
      ∀ x ∈ allWords d, ∀ y ∈ allWords d, x ≠ y →
        Disjoint
          ((Icc 1 N).filter (fun n => itinerary n d = x))
          ((Icc 1 N).filter (fun n => itinerary n d = y)) := by
    intro _x _hx _y _hy hne
    exact classCount_fiber_disjoint hne
  calc
    ∑ w ∈ allWords d, classCount w N
        = ∑ w ∈ allWords d,
            ((Icc 1 N).filter (fun n => itinerary n d = w)).card := by
          apply Finset.sum_congr rfl
          intro w hw
          exact classCount_eq hw
    _ = ((allWords d).biUnion fun w =>
            (Icc 1 N).filter (fun n => itinerary n d = w)).card := by
          rw [card_biUnion hdisj]
    _ = (Icc 1 N).card := by rw [← hunion]
    _ = N := hcard

/-- Prefix-noncontracting words of length `d`. This is `N_d` as a set. -/
def neverNegWords (d : ℕ) : Finset (List Branch) :=
  (allWords d).filter prefixNoncontracting

def neverNegCount (d : ℕ) : ℕ := (neverNegWords d).card

theorem neverNegWords_subset (d : ℕ) : neverNegWords d ⊆ allWords d :=
  filter_subset _ _

/-- Starts in `{1, …, N}` whose length-`d` itinerary is prefix-noncontracting. -/
def uncertifiedCount (d N : ℕ) : ℕ :=
  ((Icc 1 N).filter (fun n => prefixNoncontracting (itinerary n d))).card

theorem prefixNoncontracting_iff_mem_neverNeg {d : ℕ} {w : List Branch}
    (hw : w ∈ allWords d) :
    prefixNoncontracting w ↔ w ∈ neverNegWords d := by
  simp [neverNegWords, hw]

theorem uncertifiedCount_eq_sum (d N : ℕ) :
    uncertifiedCount d N = ∑ w ∈ neverNegWords d, classCount w N := by
  have hfilter :
      (Icc 1 N).filter (fun n => prefixNoncontracting (itinerary n d)) =
        (Icc 1 N).filter (fun n => itinerary n d ∈ neverNegWords d) := by
    ext n
    simp only [mem_filter, mem_Icc, and_congr_right_iff]
    intro _hn
    exact prefixNoncontracting_iff_mem_neverNeg (itinerary_mem_allWords n d)
  have hunion :
      (Icc 1 N).filter (fun n => itinerary n d ∈ neverNegWords d) =
        (neverNegWords d).biUnion fun w =>
          (Icc 1 N).filter (fun n => itinerary n d = w) := by
    ext n
    simp only [mem_biUnion, mem_filter, mem_Icc]
    constructor
    · intro ⟨hn, hw⟩
      exact ⟨itinerary n d, hw, hn, rfl⟩
    · intro ⟨w, hw, hn, heq⟩
      exact ⟨hn, by simpa [heq] using hw⟩
  have hdisj :
      ∀ x ∈ neverNegWords d, ∀ y ∈ neverNegWords d, x ≠ y →
        Disjoint
          ((Icc 1 N).filter (fun n => itinerary n d = x))
          ((Icc 1 N).filter (fun n => itinerary n d = y)) := by
    intro _x _hx _y _hy hne
    exact classCount_fiber_disjoint hne
  calc
    uncertifiedCount d N
        = ((Icc 1 N).filter
            (fun n => itinerary n d ∈ neverNegWords d)).card := by
          simp [uncertifiedCount, hfilter]
    _ = ((neverNegWords d).biUnion fun w =>
            (Icc 1 N).filter (fun n => itinerary n d = w)).card := by
          rw [hunion]
    _ = ∑ w ∈ neverNegWords d,
            ((Icc 1 N).filter (fun n => itinerary n d = w)).card := by
          rw [card_biUnion hdisj]
    _ = ∑ w ∈ neverNegWords d, classCount w N := by
          apply Finset.sum_congr rfl
          intro w hw
          exact (classCount_eq (neverNegWords_subset d hw)).symm

/-- Finite Proposition J. One-sided class bounds
`#w(N) · 2^d ≤ N + E · 2^d` lift to the uncertified count. -/
theorem propJ_count (d N E : ℕ)
    (h : ∀ w ∈ allWords d, classCount w N * 2 ^ d ≤ N + E * 2 ^ d) :
    uncertifiedCount d N * 2 ^ d ≤ neverNegCount d * (N + E * 2 ^ d) := by
  have hsum := uncertifiedCount_eq_sum d N
  calc
    uncertifiedCount d N * 2 ^ d
        = (∑ w ∈ neverNegWords d, classCount w N) * 2 ^ d := by rw [hsum]
    _ = ∑ w ∈ neverNegWords d, classCount w N * 2 ^ d := by
          rw [Finset.sum_mul]
    _ ≤ ∑ w ∈ neverNegWords d, (N + E * 2 ^ d) := by
          apply Finset.sum_le_sum
          intro w hw
          exact h w (neverNegWords_subset d hw)
    _ = neverNegCount d * (N + E * 2 ^ d) := by
          simp [neverNegCount, Finset.sum_const]

theorem itinerary_take (n : ℕ) : ∀ d k, k ≤ d → (itinerary n d).take k = itinerary n k
  | 0, k, hk => by
      have hk0 : k = 0 := Nat.eq_zero_of_le_zero hk
      simp [itinerary_zero, hk0]
  | d + 1, 0, _ => by
      simp [itinerary]
  | d + 1, k + 1, hk => by
      have hk' : k ≤ d := Nat.succ_le_succ_iff.mp hk
      simp [itinerary_succ]
      exact itinerary_take (floorPower n) d k hk'

theorem exponentGap_nil : ¬exponentGap [] := by
  simp [exponentGap, oddCount]

/-- A start with no coefficient stop has every finite itinerary
prefix-noncontracting. -/
theorem not_coeffStop_prefixNoncontracting {n d : ℕ}
    (h : ¬HasFiniteCoeffStop n) : prefixNoncontracting (itinerary n d) := by
  intro k hk hg
  have hlen : (itinerary n d).length = d := itinerary_length n d
  have hk' : k ≤ d := by simpa [hlen] using hk
  have htake : (itinerary n d).take k = itinerary n k := itinerary_take n d k hk'
  have hgap : exponentGap (itinerary n k) := by simpa [htake] using hg
  have hkpos : 0 < k := by
    cases k with
    | zero =>
        simpa [itinerary_zero] using (exponentGap_nil hgap)
    | succ k =>
        exact Nat.succ_pos _
  exact h ⟨k, hkpos, hgap⟩

theorem neverCertified_subset_uncertified {d N : ℕ} {s : Finset ℕ}
    (hs : s ⊆ Icc 1 N) (hstop : ∀ n ∈ s, ¬HasFiniteCoeffStop n) :
    s ⊆ (Icc 1 N).filter (fun n => prefixNoncontracting (itinerary n d)) := by
  intro n hn
  exact mem_filter.mpr ⟨hs hn, not_coeffStop_prefixNoncontracting (hstop n hn)⟩

theorem neverCertifiedCount_le_uncertified {d N : ℕ} {s : Finset ℕ}
    (hs : s ⊆ Icc 1 N) (hstop : ∀ n ∈ s, ¬HasFiniteCoeffStop n) :
    s.card ≤ uncertifiedCount d N :=
  card_le_card (neverCertified_subset_uncertified hs hstop)

/-- Finite Lemma A: qualitative class bounds at a fixed depth control
any finite set of never-certified starts in `{1, …, N}`. The limit
order `N → ∞` before `d → ∞` stays prose. -/
theorem lemmaA_finite (d N E : ℕ)
    (hequi : ∀ w ∈ allWords d, classCount w N * 2 ^ d ≤ N + E * 2 ^ d)
    {s : Finset ℕ} (hs : s ⊆ Icc 1 N)
    (hstop : ∀ n ∈ s, ¬HasFiniteCoeffStop n) :
    s.card * 2 ^ d ≤ neverNegCount d * (N + E * 2 ^ d) :=
  (Nat.mul_le_mul_right (2 ^ d)
      (neverCertifiedCount_le_uncertified hs hstop)).trans
    (propJ_count d N E hequi)

theorem prefixNoncontracting_not_gap {w : List Branch}
    (h : prefixNoncontracting w) : ¬exponentGap w := by
  have htake : w.take w.length = w := List.take_length
  simpa [htake] using h w.length le_rfl

theorem neverNeg_endpoint {d : ℕ} {w : List Branch} (hw : w ∈ neverNegWords d) :
    2 ^ d ≤ 3 ^ oddCount w := by
  have hlen : w.length = d := mem_allWords.mp (neverNegWords_subset d hw)
  have hnc : prefixNoncontracting w := (mem_filter.mp hw).2
  have hng : ¬exponentGap w := prefixNoncontracting_not_gap hnc
  exact Nat.le_of_not_lt (by simpa [exponentGap, hlen] using hng)

/-- Node partition: the two one-letter extensions do not exceed the parent. -/
def WeightSplit (μ : List Branch → ℝ) : Prop :=
  ∀ σ, 0 ≤ μ (σ ++ [.even]) ∧ 0 ≤ μ (σ ++ [.odd]) ∧
    μ (σ ++ [.even]) + μ (σ ++ [.odd]) ≤ μ σ

/-- Node-wise odd share at most `1 - β`. -/
def OddShareBound (μ : List Branch → ℝ) (β : ℝ) : Prop :=
  ∀ σ, μ (σ ++ [.odd]) ≤ (1 - β) * μ σ

noncomputable def weightGen (μ : List Branch → ℝ) (x : ℝ) (d : ℕ) : ℝ :=
  ∑ w ∈ allWords d, μ w * x ^ oddCount w

theorem allWords_succ (d : ℕ) :
    allWords (d + 1) =
      (allWords d).biUnion fun w => {w ++ [.even], w ++ [.odd]} :=
  rfl

theorem weightGen_zero (μ : List Branch → ℝ) (x : ℝ) :
    weightGen μ x 0 = μ [] := by
  simp [weightGen, allWords, oddCount]

theorem append_singleton_inj {a b : List Branch} {x y : Branch}
    (h : a ++ [x] = b ++ [y]) : a = b ∧ x = y := by
  have ⟨ha, hb⟩ := List.append_inj' h (by simp)
  cases hb
  exact ⟨ha, rfl⟩

theorem weight_split_step (μ : List Branch → ℝ) (β x : ℝ)
    (_hβ1 : β ≤ 1) (hx : 1 ≤ x)
    (hsplit : WeightSplit μ) (hodd : OddShareBound μ β) (σ : List Branch) :
    μ (σ ++ [.even]) + x * μ (σ ++ [.odd]) ≤
      (β + (1 - β) * x) * μ σ := by
  obtain ⟨_he0, _ho0, hsum⟩ := hsplit σ
  have hbound := hodd σ
  have hx1 : 0 ≤ x - 1 := sub_nonneg.mpr hx
  have hlin :
      μ σ + (x - 1) * μ (σ ++ [.odd]) ≤
        μ σ + (x - 1) * ((1 - β) * μ σ) :=
    add_le_add_right (mul_le_mul_of_nonneg_left hbound hx1) _
  calc
    μ (σ ++ [.even]) + x * μ (σ ++ [.odd])
        ≤ μ σ - μ (σ ++ [.odd]) + x * μ (σ ++ [.odd]) := by linarith
    _ = μ σ + (x - 1) * μ (σ ++ [.odd]) := by ring
    _ ≤ μ σ + (x - 1) * ((1 - β) * μ σ) := hlin
    _ = (β + (1 - β) * x) * μ σ := by ring

theorem extend_fiber_disjoint {x y : List Branch} (hne : x ≠ y) :
    Disjoint
      ({x ++ [.even], x ++ [.odd]} : Finset (List Branch))
      ({y ++ [.even], y ++ [.odd]} : Finset (List Branch)) := by
  rw [disjoint_left]
  intro t htx hty
  have hx : t = x ++ [.even] ∨ t = x ++ [.odd] := by
    simpa [mem_insert, mem_singleton] using htx
  have hy : t = y ++ [.even] ∨ t = y ++ [.odd] := by
    simpa [mem_insert, mem_singleton] using hty
  rcases hx with hx | hx <;> rcases hy with hy | hy
  · exact hne (append_singleton_inj (hx.symm.trans hy)).1
  · exact Branch.noConfusion (append_singleton_inj (hx.symm.trans hy)).2
  · exact Branch.noConfusion (append_singleton_inj (hx.symm.trans hy)).2
  · exact hne (append_singleton_inj (hx.symm.trans hy)).1

theorem weightGen_inner (μ : List Branch → ℝ) (x : ℝ) (w : List Branch) :
    ∑ i ∈ ({w ++ [.even], w ++ [.odd]} : Finset (List Branch)),
        μ i * x ^ oddCount i =
      μ (w ++ [.even]) * x ^ oddCount w +
        μ (w ++ [.odd]) * x ^ (oddCount w + 1) := by
  have hne : w ++ [.even] ≠ w ++ [.odd] := by
    intro h
    exact Branch.noConfusion (append_singleton_inj h).2
  simp [sum_pair hne, oddCount_append, oddCount]

theorem weightGen_succ (μ : List Branch → ℝ) (x : ℝ) (d : ℕ) :
    weightGen μ x (d + 1) =
      ∑ w ∈ allWords d,
        (μ (w ++ [.even]) * x ^ oddCount w +
          μ (w ++ [.odd]) * x ^ (oddCount w + 1)) := by
  have hdisj :
      ∀ x ∈ allWords d, ∀ y ∈ allWords d, x ≠ y →
        Disjoint
          ({x ++ [.even], x ++ [.odd]} : Finset (List Branch))
          ({y ++ [.even], y ++ [.odd]} : Finset (List Branch)) := by
    intro _x _hx _y _hy hne
    exact extend_fiber_disjoint hne
  simp only [weightGen, allWords_succ]
  rw [sum_biUnion hdisj]
  exact Finset.sum_congr rfl fun w _ => weightGen_inner μ x w

/-- Generating-function domination for a node-wise odd-share bound.
This is the algebraic half of the biased-split reduction. -/
theorem weightGen_domination (μ : List Branch → ℝ) (β x : ℝ)
    (hβ1 : β ≤ 1) (hx : 1 ≤ x)
    (hsplit : WeightSplit μ) (hodd : OddShareBound μ β) :
    ∀ d, weightGen μ x d ≤ μ [] * (β + (1 - β) * x) ^ d
  | 0 => by
      simp [weightGen_zero]
  | d + 1 => by
      have ih := weightGen_domination μ β x hβ1 hx hsplit hodd d
      have hx0 : 0 ≤ x := le_trans (by norm_num : (0 : ℝ) ≤ 1) hx
      have hstep : ∀ w ∈ allWords d,
          μ (w ++ [.even]) * x ^ oddCount w +
              μ (w ++ [.odd]) * x ^ (oddCount w + 1)
            ≤ (β + (1 - β) * x) * (μ w * x ^ oddCount w) := by
        intro w _hw
        have hpow : x ^ (oddCount w + 1) = x * x ^ oddCount w :=
          pow_succ' x _
        have hlin := weight_split_step μ β x hβ1 hx hsplit hodd w
        have hxpow : 0 ≤ x ^ oddCount w := pow_nonneg hx0 _
        calc
          μ (w ++ [.even]) * x ^ oddCount w +
              μ (w ++ [.odd]) * x ^ (oddCount w + 1)
              = (μ (w ++ [.even]) + x * μ (w ++ [.odd])) * x ^ oddCount w := by
                rw [hpow]
                ring
          _ ≤ ((β + (1 - β) * x) * μ w) * x ^ oddCount w := by
                exact mul_le_mul_of_nonneg_right hlin hxpow
          _ = (β + (1 - β) * x) * (μ w * x ^ oddCount w) := by ring
      have hfac : 0 ≤ β + (1 - β) * x := by nlinarith [hβ1, hx]
      calc
        weightGen μ x (d + 1)
            = ∑ w ∈ allWords d,
                (μ (w ++ [.even]) * x ^ oddCount w +
                  μ (w ++ [.odd]) * x ^ (oddCount w + 1)) :=
              weightGen_succ μ x d
        _ ≤ ∑ w ∈ allWords d, (β + (1 - β) * x) * (μ w * x ^ oddCount w) := by
              apply Finset.sum_le_sum
              exact hstep
        _ = (β + (1 - β) * x) * weightGen μ x d := by
              simp [weightGen, Finset.mul_sum]
        _ ≤ (β + (1 - β) * x) * (μ [] * (β + (1 - β) * x) ^ d) :=
              mul_le_mul_of_nonneg_left ih hfac
        _ = μ [] * (β + (1 - β) * x) ^ (d + 1) := by
              rw [pow_succ']
              ring

/-- Markov tilt of a nonnegative word weight: the mass on
`oddCount ≥ k` is at most `weightGen / x^k`. Combined with
`weightGen_domination` this is the Chernoff engine; the optimal
tilt that fires exactly when `β` is strictly above
`1 - log 2 / log 3` stays prose. -/
theorem weight_markov (μ : List Branch → ℝ) (x : ℝ) (d k : ℕ)
    (hx : 1 ≤ x) (hμ : ∀ w, 0 ≤ μ w) :
    (∑ w ∈ (allWords d).filter (fun w => k ≤ oddCount w), μ w)
      ≤ weightGen μ x d / x ^ k := by
  have hx0 : 0 < x := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hx
  have hxpow : 0 < x ^ k := pow_pos hx0 k
  have hterm : ∀ w ∈ (allWords d).filter (fun w => k ≤ oddCount w),
      μ w ≤ μ w * x ^ oddCount w / x ^ k := by
    intro w hw
    have hodd : k ≤ oddCount w := (mem_filter.mp hw).2
    have hμw : 0 ≤ μ w := hμ w
    have hdiv : (1 : ℝ) ≤ x ^ oddCount w / x ^ k := by
      rw [le_div_iff₀ hxpow]
      simpa [one_mul] using pow_le_pow_right₀ hx hodd
    calc
      μ w = μ w * 1 := by ring
      _ ≤ μ w * (x ^ oddCount w / x ^ k) :=
            mul_le_mul_of_nonneg_left hdiv hμw
      _ = μ w * x ^ oddCount w / x ^ k := by ring
  have hsum :
      (∑ w ∈ (allWords d).filter (fun w => k ≤ oddCount w), μ w)
        ≤ ∑ w ∈ (allWords d).filter (fun w => k ≤ oddCount w),
            μ w * x ^ oddCount w / x ^ k :=
    Finset.sum_le_sum hterm
  have hsub :
      ∑ w ∈ (allWords d).filter (fun w => k ≤ oddCount w),
          μ w * x ^ oddCount w
        ≤ weightGen μ x d := by
    refine Finset.sum_le_sum_of_subset_of_nonneg (filter_subset _ _) ?_
    intro w _hw _h
    exact mul_nonneg (hμ w) (pow_nonneg (le_of_lt hx0) _)
  calc
    ∑ w ∈ (allWords d).filter (fun w => k ≤ oddCount w), μ w
        ≤ ∑ w ∈ (allWords d).filter (fun w => k ≤ oddCount w),
            μ w * x ^ oddCount w / x ^ k := hsum
    _ = (∑ w ∈ (allWords d).filter (fun w => k ≤ oddCount w),
            μ w * x ^ oddCount w) / x ^ k := by
          rw [← Finset.sum_div]
    _ ≤ weightGen μ x d / x ^ k :=
          div_le_div_of_nonneg_right hsub (le_of_lt hxpow)

/-- Fair to depth `k`, then all-odd: Bernoulli on every word of
length at most `k`, and after that the unique all-odd continuation
of each length-`k` prefix. -/
def fairThenAllOdd (k : ℕ) (w : List Branch) : ℚ :=
  if w.length ≤ k then
    (1 : ℚ) / (2 ^ w.length : ℚ)
  else if w.drop k = List.replicate (w.length - k) Branch.odd then
    (1 : ℚ) / (2 ^ k : ℚ)
  else
    0

theorem fairThenAllOdd_bernoulli {k d : ℕ} (hd : d ≤ k) {w : List Branch}
    (hw : w.length = d) :
    fairThenAllOdd k w = (1 : ℚ) / (2 ^ d : ℚ) := by
  simp [fairThenAllOdd, hw, hd]

theorem fairThenAllOdd_allOdd {k d : ℕ} (hd : k ≤ d) :
    fairThenAllOdd k (List.replicate d Branch.odd) = (1 : ℚ) / (2 ^ k : ℚ) := by
  by_cases hle : d ≤ k
  · have heq : d = k := Nat.le_antisymm hle hd
    simp [fairThenAllOdd, List.length_replicate, heq]
  · simp [fairThenAllOdd, List.length_replicate, hle, List.drop_replicate]

theorem allOdd_prefixNoncontracting (d : ℕ) :
    prefixNoncontracting (List.replicate d Branch.odd) := by
  intro t ht hg
  have hlen : (List.replicate d Branch.odd).length = d :=
    List.length_replicate
  have ht' : t ≤ d := by simpa [hlen] using ht
  have htake :
      (List.replicate d Branch.odd).take t = List.replicate t Branch.odd := by
    simp [List.take_replicate, Nat.min_eq_left ht']
  have hodd : oddCount (List.replicate t Branch.odd) = t :=
    oddCount_replicate_odd t
  have hle : 2 ^ t ≤ 3 ^ t :=
    Nat.pow_le_pow_left (by decide : (2 : ℕ) ≤ 3) t
  rw [htake] at hg
  exact not_lt_of_ge (by simpa [exponentGap, hodd] using hle) hg

/-- The all-odd ray keeps mass `2^{-k}` at every depth `d ≥ k`.
A word measure fair to depth `k` and all-odd afterwards therefore
satisfies every depth-`≤ k` Bernoulli count and keeps a positive
never-contracting mass, so no bounded-depth certificate statement
can force the live mass to vanish. -/
theorem fairThenAllOdd_live_mass {k d : ℕ} (hd : k ≤ d) :
    fairThenAllOdd k (List.replicate d Branch.odd) = (1 : ℚ) / (2 ^ k : ℚ) ∧
      prefixNoncontracting (List.replicate d Branch.odd) ∧
      0 < (1 : ℚ) / (2 ^ k : ℚ) :=
  ⟨fairThenAllOdd_allOdd hd, allOdd_prefixNoncontracting d,
    div_pos one_pos (pow_pos (by norm_num) k)⟩

end Problems.Juggler
