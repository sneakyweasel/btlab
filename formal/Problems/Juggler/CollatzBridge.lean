/-
# The Juggler–Collatz bridge, made exact at the word level

`J-juggler-is-collatz-one-exponential-up` records that the accelerated Collatz map and the
Juggler map realise the same additive walk -- steps `+log(3/2)` and `-log 2` -- on `log x` and
on `log log n` respectively, and that the two problems part at how a parity word attaches to an
integer. This file states that identification as theorems about one shared object, the
`List Branch` word, with nothing measured and no real number in any statement.

**Collatz is word-affine, with the correction pointing up.** Write `C` for the shortcut map
`x ↦ x/2, (3x+1)/2` and `w = parityWord x d` for the first `d` parities of the orbit of `x`.
Then

  `2 ^ d · C^d(x) = 3 ^ oddCount w · x + wordConst w`,       `wordConst w ≥ 0`,

with `wordConst` a function of the word alone (`word_affine`). The multiplier `3^o / 2^d` acts
on `x`; every `+1` pushes the orbit above the pure multiplier.

**Juggler is exponent-affine, with the correction pointing down.** For a realised word `w`,

  `(J_w n) ^ (2 ^ d) ≤ n ^ (3 ^ oddCount w)`                      (`juggler_word_power`),

so the same multiplier acts on `log n`, and every floor pushes the orbit below it. The two
inequalities have opposite senses, which is the whole of the sign flip on cycles:

  * a Collatz cycle word contracts, `3 ^ o < 2 ^ d`   (`cycle_contracting`, proved here);
  * a Juggler cycle word expands, `2 ^ d < 3 ^ o`      (`juggler_cycle_expanding`, from
    `CycleCore`).

**Terras, in this vocabulary.** The word of length `d` is a function of `x mod 2 ^ d`, and the
induced map from residues to words is a bijection (`parityWord_eq_iff`, `image_parityWord`).
Hence the survivor count `neverNegCount d` of `RateFreeDensity` -- Paper B's `N_d` -- is the
number of residue classes modulo `2 ^ d` whose word has no contracting prefix
(`undecidedResidues_card`), and the minimal-certificate count of `PaperBCertificateRecursion` is
the number of classes whose word first contracts at `d` (`decidedAtResidues_card`). Those are
the definitions of OEIS A076227 and A100982; the kernel checks at the end reproduce the entry's
own example, the eight surviving residues modulo `64`, and the terms `3, 4, 8, 13, 19, 38, 64`.

**What the classes mean dynamically.** No member of an undecided class drops within `d` steps
(`le_iter_of_prefixNoncontracting`), and every member of a decided class beyond an explicit
threshold drops at the contracting length (`iter_lt_of_exponentGap_class`) -- the two halves of
Terras's structure theorem, from the affine identity alone.

**What is not here.** No density, no asymptotic, no bound in either problem, and nothing about
how the Juggler word attaches to `n` (Hypothesis FD). This file is the well-definedness of the
bridge and nothing more: the shared word, the two opposite corrections, and the exact Collatz
reading of the laboratory's kernel-checked word counts.
-/
import Mathlib.Tactic
import Problems.Collatz.Shortcut
import Problems.Juggler.RateFreeDensity
import Problems.Juggler.PaperBCertificateRecursion
import Problems.Juggler.Envelope
import Problems.Juggler.CycleCore

namespace Problems.Juggler

namespace CollatzBridge

open Problems.Collatz

/-! ## 1. The shortcut map without its division -/

/-- One step of the shortcut map, cleared of its division: `2 · C(x)` is `x` on an even `x` and
`3x + 1` on an odd `x`. -/
theorem two_mul_shortcutC (x : ℕ) :
    2 * shortcutC x = if x % 2 = 0 then x else 3 * x + 1 := by
  unfold shortcutC
  split_ifs with h
  · have := Nat.div_add_mod x 2
    omega
  · have := Nat.div_add_mod (3 * x + 1) 2
    omega

/-- Peeling the first step: `C^{k+1}(x) = C^k(C(x))`. -/
theorem shortcutCIter_succ' (k x : ℕ) :
    shortcutCIter (k + 1) x = shortcutCIter k (shortcutC x) := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih =>
    show shortcutC (shortcutCIter (k + 1) x) = shortcutC (shortcutCIter k (shortcutC x))
    rw [ih]

/-! ## 2. The parity word of a Collatz orbit -/

/-- The first `d` parities of the shortcut orbit of `x`, read as a Juggler word: the same
alphabet, the same `oddCount`, the same `exponentGap`. -/
def parityWord : ℕ → ℕ → List Branch
  | _, 0 => []
  | x, d + 1 => bit x :: parityWord (shortcutC x) d

@[simp] theorem parityWord_zero (x : ℕ) : parityWord x 0 = [] := rfl

@[simp] theorem parityWord_succ (x d : ℕ) :
    parityWord x (d + 1) = bit x :: parityWord (shortcutC x) d := rfl

@[simp] theorem parityWord_length (x d : ℕ) : (parityWord x d).length = d := by
  induction d generalizing x with
  | zero => rfl
  | succ d ih => simp [ih]

/-- A prefix of the word is the word of the prefix. -/
theorem parityWord_take {x d t : ℕ} (ht : t ≤ d) :
    (parityWord x d).take t = parityWord x t := by
  induction d generalizing x t with
  | zero =>
    have : t = 0 := Nat.le_zero.mp ht
    subst this
    rfl
  | succ d ih =>
    cases t with
    | zero => rfl
    | succ t =>
      simp only [parityWord_succ, List.take_succ_cons]
      rw [ih (Nat.le_of_succ_le_succ ht)]

/-! ## 3. The word-affine formula -/

/-- The additive constant of the word-affine formula: reading the word from the front, an even
letter doubles the constant and an odd letter adds `3` to the power of the odd letters still to
come. -/
def wordConst : List Branch → ℕ
  | [] => 0
  | .even :: w => 2 * wordConst w
  | .odd :: w => 3 ^ oddCount w + 2 * wordConst w

@[simp] theorem wordConst_nil : wordConst [] = 0 := rfl

@[simp] theorem wordConst_even (w : List Branch) : wordConst (.even :: w) = 2 * wordConst w := rfl

@[simp] theorem wordConst_odd (w : List Branch) :
    wordConst (.odd :: w) = 3 ^ oddCount w + 2 * wordConst w := rfl

/-- The constant vanishes exactly on the all-even words. -/
theorem wordConst_eq_zero_iff (w : List Branch) : wordConst w = 0 ↔ oddCount w = 0 := by
  induction w with
  | nil => simp
  | cons b w ih =>
    cases b with
    | even => simpa using ih
    | odd =>
      have : 0 < 3 ^ oddCount w := pow_pos (by norm_num) _
      simp only [wordConst_odd, oddCount_odd_cons]
      omega

/-- **Collatz is word-affine.** `2 ^ d · C^d(x) = 3 ^ o · x + wordConst w` with `w` the parity
word of `x` and `o` its odd count. The multiplier `3 ^ o / 2 ^ d` is the one Juggler carries on
the exponent; the correction is nonnegative. -/
theorem word_affine (x d : ℕ) :
    2 ^ d * shortcutCIter d x =
      3 ^ oddCount (parityWord x d) * x + wordConst (parityWord x d) := by
  induction d generalizing x with
  | zero => simp [shortcutCIter]
  | succ d ih =>
    rw [shortcutCIter_succ', parityWord_succ]
    have h := ih (shortcutC x)
    have h2 := two_mul_shortcutC x
    rcases Nat.mod_two_eq_zero_or_one x with hx | hx
    · rw [bit_even hx, oddCount_even_cons, wordConst_even]
      rw [if_pos hx] at h2
      generalize oddCount (parityWord (shortcutC x) d) = o at h ⊢
      generalize wordConst (parityWord (shortcutC x) d) = c at h ⊢
      generalize shortcutCIter d (shortcutC x) = z at h ⊢
      generalize shortcutC x = y at h h2
      calc 2 ^ (d + 1) * z = 2 * (2 ^ d * z) := by ring
        _ = 2 * (3 ^ o * y + c) := by rw [h]
        _ = 3 ^ o * (2 * y) + 2 * c := by ring
        _ = 3 ^ o * x + 2 * c := by rw [h2]
    · rw [bit_odd hx, oddCount_odd_cons, wordConst_odd]
      rw [if_neg (by omega)] at h2
      generalize oddCount (parityWord (shortcutC x) d) = o at h ⊢
      generalize wordConst (parityWord (shortcutC x) d) = c at h ⊢
      generalize shortcutCIter d (shortcutC x) = z at h ⊢
      generalize shortcutC x = y at h h2
      calc 2 ^ (d + 1) * z = 2 * (2 ^ d * z) := by ring
        _ = 2 * (3 ^ o * y + c) := by rw [h]
        _ = 3 ^ o * (2 * y) + 2 * c := by ring
        _ = 3 ^ o * (3 * x + 1) + 2 * c := by rw [h2]
        _ = 3 ^ (o + 1) * x + (3 ^ o + 2 * c) := by ring

/-! ## 4. Terras: residues modulo `2 ^ d` are the words of length `d` -/

/-- Two integers carry the same first letter exactly when they have the same parity. -/
private theorem bit_eq_iff (x y : ℕ) : bit x = bit y ↔ x % 2 = y % 2 := by
  unfold bit
  split_ifs with hx hy hy <;> simp <;> omega

/-- One step of Terras's argument: agreement modulo `2 ^ (d + 1)` is agreement of the first
parity together with agreement of the shortcut images modulo `2 ^ d`. -/
private theorem mod_pow_succ_iff (x y d : ℕ) :
    x % 2 ^ (d + 1) = y % 2 ^ (d + 1) ↔
      x % 2 = y % 2 ∧ shortcutC x % 2 ^ d = shortcutC y % 2 ^ d := by
  have hx := two_mul_shortcutC x
  have hy := two_mul_shortcutC y
  have hc : Nat.Coprime (2 ^ (d + 1)) 3 := Nat.Coprime.pow_left _ (by norm_num)
  rw [pow_succ'] at hc ⊢
  constructor
  · intro h
    have h2 : x % 2 = y % 2 := Nat.ModEq.of_mul_right (2 ^ d) (h : x ≡ y [MOD 2 * 2 ^ d])
    refine ⟨h2, ?_⟩
    split_ifs at hx hy with hx0 hy0
    · have this : 2 * shortcutC x ≡ 2 * shortcutC y [MOD 2 * 2 ^ d] := by
        rw [hx, hy]; exact h
      exact (Nat.ModEq.mul_left_cancel_iff' (by norm_num)).mp this
    · omega
    · omega
    · have h3 : 3 * x ≡ 3 * y [MOD 2 * 2 ^ d] := Nat.ModEq.mul_left 3 h
      have h4 : 3 * x + 1 ≡ 3 * y + 1 [MOD 2 * 2 ^ d] := Nat.ModEq.add_right 1 h3
      have this : 2 * shortcutC x ≡ 2 * shortcutC y [MOD 2 * 2 ^ d] := by
        rw [hx, hy]; exact h4
      exact (Nat.ModEq.mul_left_cancel_iff' (by norm_num)).mp this
  · rintro ⟨h2, h⟩
    split_ifs at hx hy with hx0 hy0
    · have this : 2 * shortcutC x ≡ 2 * shortcutC y [MOD 2 * 2 ^ d] :=
        (Nat.ModEq.mul_left_cancel_iff' (by norm_num)).mpr h
      rw [hx, hy] at this
      exact this
    · omega
    · omega
    · have this : 2 * shortcutC x ≡ 2 * shortcutC y [MOD 2 * 2 ^ d] :=
        (Nat.ModEq.mul_left_cancel_iff' (by norm_num)).mpr h
      rw [hx, hy] at this
      have h3 : 3 * x ≡ 3 * y [MOD 2 * 2 ^ d] := Nat.ModEq.add_right_cancel' 1 this
      exact Nat.ModEq.cancel_left_of_coprime hc h3

/-- The word of length `d` is determined by `x mod 2 ^ d`, and determines it. -/
theorem parityWord_eq_iff (x y d : ℕ) :
    parityWord x d = parityWord y d ↔ x % 2 ^ d = y % 2 ^ d := by
  induction d generalizing x y with
  | zero => simp [Nat.mod_one]
  | succ d ih =>
    rw [parityWord_succ, parityWord_succ, List.cons.injEq, bit_eq_iff, ih, mod_pow_succ_iff]

theorem parityWord_mod (x d : ℕ) : parityWord (x % 2 ^ d) d = parityWord x d :=
  (parityWord_eq_iff _ _ _).mpr (Nat.mod_mod _ _)

/-- There are `2 ^ d` words of length `d`. -/
theorem allWords_card (d : ℕ) : (allWords d).card = 2 ^ d := by
  induction d with
  | zero => simp [allWords]
  | succ d ih =>
    have hdisj : ∀ x ∈ allWords d, ∀ y ∈ allWords d, x ≠ y →
        Disjoint ({x ++ [.even], x ++ [.odd]} : Finset (List Branch))
          {y ++ [.even], y ++ [.odd]} := by
      intro x _ y _ hxy
      rw [Finset.disjoint_left]
      intro w hw hw'
      simp only [Finset.mem_insert, Finset.mem_singleton] at hw hw'
      apply hxy
      rcases hw with rfl | rfl <;> rcases hw' with h | h <;>
        exact List.append_inj_left' h rfl
    have hpair : ∀ w : List Branch,
        ({w ++ [.even], w ++ [.odd]} : Finset (List Branch)).card = 2 := by
      intro w
      apply Finset.card_pair
      intro h
      have h' := List.append_inj_right' h rfl
      simp at h'
    rw [allWords, Finset.card_biUnion hdisj, Finset.sum_congr rfl (fun w _ => hpair w),
      Finset.sum_const, smul_eq_mul, ih]
    ring

/-- The parity map is a bijection from the residues modulo `2 ^ d` onto the words of length
`d`: Terras's structure theorem, as a `Finset` identity. -/
theorem image_parityWord (d : ℕ) :
    (Finset.range (2 ^ d)).image (fun r ↦ parityWord r d) = allWords d := by
  apply Finset.eq_of_subset_of_card_le
  · intro w hw
    rw [Finset.mem_image] at hw
    obtain ⟨r, _, rfl⟩ := hw
    exact mem_allWords.mpr (parityWord_length r d)
  · rw [allWords_card, Finset.card_image_of_injOn, Finset.card_range]
    intro x hx y hy hxy
    rw [Finset.mem_coe, Finset.mem_range] at hx hy
    have hmod := (parityWord_eq_iff x y d).mp hxy
    rwa [Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy] at hmod

/-- **Every word is realised**, by some residue below `2 ^ d`: the surjective half of Terras's
bijection, read off `image_parityWord`. This is what lets the hug word -- every odd step at
height `frac(a * log2(3/2))` -- be placed at any large minimum, so that no bound using only
`x_j + 1 >= 2 ^ h_j (x + 1)` can improve on `H(p)`. -/
theorem exists_residue_of_word {w : List Branch} (hw : w.length = d) :
    ∃ r, r < 2 ^ d ∧ parityWord r d = w := by
  have hmem : w ∈ allWords d := mem_allWords.mpr hw
  rw [← image_parityWord] at hmem
  obtain ⟨r, hr, hrw⟩ := Finset.mem_image.mp hmem
  exact ⟨r, Finset.mem_range.mp hr, hrw⟩

/-! ## 5. The laboratory's word counts are Collatz residue counts -/

/-- The residues modulo `2 ^ d` whose word has no contracting prefix: the classes in which the
stopping time is not yet decided after `d` steps. -/
def undecidedResidues (d : ℕ) : Finset ℕ :=
  (Finset.range (2 ^ d)).filter fun r ↦ prefixNoncontracting (parityWord r d)

/-- The parity map is injective on the residues below `2 ^ d`. -/
private theorem parityWord_injOn (d : ℕ) :
    Set.InjOn (fun r ↦ parityWord r d) ↑(Finset.range (2 ^ d)) := by
  intro x hx y hy hxy
  have hx' : x < 2 ^ d := Finset.mem_range.mp hx
  have hy' : y < 2 ^ d := Finset.mem_range.mp hy
  have h := (parityWord_eq_iff x y d).mp hxy
  rwa [Nat.mod_eq_of_lt hx', Nat.mod_eq_of_lt hy'] at h

/-- Counting a filtered set of words through the residue bijection. -/
private theorem card_filter_parityWord (d : ℕ) (p : List Branch → Prop) [DecidablePred p] :
    ((Finset.range (2 ^ d)).filter fun r ↦ p (parityWord r d)).card
      = ((allWords d).filter p).card := by
  rw [← image_parityWord, Finset.filter_image,
    Finset.card_image_of_injOn ((parityWord_injOn d).mono (Finset.coe_subset.mpr (Finset.filter_subset _ _)))]

/-- **The survivor count is a Collatz count.** Paper B's `N_d` is the number of residue classes
modulo `2 ^ d` with no contracting prefix -- the definition of OEIS A076227. -/
theorem undecidedResidues_card (d : ℕ) : (undecidedResidues d).card = neverNegCount d := by
  unfold undecidedResidues neverNegCount neverNegWords
  exact card_filter_parityWord d prefixNoncontracting

/-- The residues modulo `2 ^ d` whose word first contracts at length `d`. -/
def decidedAtResidues (d : ℕ) : Finset ℕ :=
  (Finset.range (2 ^ d)).filter fun r ↦ PaperBCertificates.IsMinimalCertificate (parityWord r d)

/-- **The minimal-certificate count is a Collatz count.** `M_d` is the number of residue classes
modulo `2 ^ d` whose stopping time is decided at exactly `d` -- OEIS A100982 read by length. -/
theorem decidedAtResidues_card (d : ℕ) : (decidedAtResidues d).card = minimalCertCount d := by
  unfold decidedAtResidues minimalCertCount minimalCertWords
  exact card_filter_parityWord d PaperBCertificates.IsMinimalCertificate

/-! ## 6. What the classes mean for the orbit -/

/-- On a prefix-noncontracting word, every prefix length `t ≤ d` has `2 ^ t ≤ 3 ^ o_t`. -/
private theorem two_pow_le_three_pow_of_prefixNoncontracting {x d t : ℕ}
    (h : prefixNoncontracting (parityWord x d)) (ht : t ≤ d) :
    2 ^ t ≤ 3 ^ oddCount (parityWord x t) := by
  have h1 := h t (by rw [parityWord_length]; exact ht)
  rw [parityWord_take ht] at h1
  unfold exponentGap at h1
  rw [parityWord_length] at h1
  exact Nat.le_of_not_lt h1

/-- No member of an undecided class drops within `d` steps. -/
theorem le_iter_of_prefixNoncontracting {x d : ℕ} (h : prefixNoncontracting (parityWord x d)) :
    ∀ t, t ≤ d → x ≤ shortcutCIter t x := by
  intro t ht
  have hgap := two_pow_le_three_pow_of_prefixNoncontracting h ht
  have haff := word_affine x t
  have hpos : 0 < 2 ^ t := Nat.two_pow_pos t
  apply Nat.le_of_mul_le_mul_left _ hpos
  rw [haff]
  calc 2 ^ t * x ≤ 3 ^ oddCount (parityWord x t) * x := Nat.mul_le_mul_right x hgap
    _ ≤ 3 ^ oddCount (parityWord x t) * x + wordConst (parityWord x t) := Nat.le_add_right _ _

/-- Strictly: a positive start in an undecided class sits strictly below every later state. -/
theorem lt_iter_of_prefixNoncontracting {x d : ℕ} (hx : 1 ≤ x)
    (h : prefixNoncontracting (parityWord x d)) :
    ∀ t, 0 < t → t ≤ d → x < shortcutCIter t x := by
  intro t ht0 ht
  have hgap := two_pow_le_three_pow_of_prefixNoncontracting h ht
  have hne : 2 ^ t ≠ 3 ^ oddCount (parityWord x t) := by
    intro heq
    have h2 : 2 ^ t % 2 = 0 := by
      obtain ⟨s, rfl⟩ := Nat.exists_eq_add_of_lt ht0
      rw [Nat.pow_succ]; simp
    have h3 : 3 ^ oddCount (parityWord x t) % 2 = 1 := three_pow_odd _
    omega
  have hlt : 2 ^ t < 3 ^ oddCount (parityWord x t) := lt_of_le_of_ne hgap hne
  have haff := word_affine x t
  have hpos : 0 < 2 ^ t := Nat.two_pow_pos t
  apply Nat.lt_of_mul_lt_mul_left (a := 2 ^ t)
  rw [haff]
  calc 2 ^ t * x < 3 ^ oddCount (parityWord x t) * x := Nat.mul_lt_mul_of_pos_right hlt hx
    _ ≤ 3 ^ oddCount (parityWord x t) * x + wordConst (parityWord x t) := Nat.le_add_right _ _

/-- A contracting word drops every start beyond its own constant. -/
theorem iter_lt_of_exponentGap {x t : ℕ} (h : exponentGap (parityWord x t))
    (hx : wordConst (parityWord x t) < x) : shortcutCIter t x < x := by
  unfold exponentGap at h
  rw [parityWord_length] at h
  obtain ⟨g, hg⟩ := Nat.exists_eq_add_of_lt h
  have haff := word_affine x t
  have hpos : 0 < 2 ^ t := Nat.two_pow_pos t
  apply Nat.lt_of_mul_lt_mul_left (a := 2 ^ t)
  rw [haff, hg]
  nlinarith

/-- The drop is a property of the residue class: one constant serves every member. -/
theorem iter_lt_of_exponentGap_class {r t : ℕ} (h : exponentGap (parityWord r t)) :
    ∀ y, y % 2 ^ t = r % 2 ^ t → wordConst (parityWord r t) < y → shortcutCIter t y < y := by
  intro y hy hc
  have hw : parityWord y t = parityWord r t := (parityWord_eq_iff y r t).mpr hy
  rw [← hw] at h hc
  exact iter_lt_of_exponentGap h hc

/-! ## 7. The sign flip on cycles -/

/-- **Collatz cycles contract.** A positive shortcut cycle of length `d ≥ 1` has `3 ^ o < 2 ^ d`,
because `2 ^ d · x = 3 ^ o · x + wordConst w` with a positive constant. -/
theorem cycle_contracting {x d : ℕ} (hd : 0 < d) (hx : 0 < x) (hcyc : shortcutCIter d x = x) :
    3 ^ oddCount (parityWord x d) < 2 ^ d := by
  have haff := word_affine x d
  rw [hcyc] at haff
  set w := parityWord x d with hw
  have hc : 0 < wordConst w := by
    rcases Nat.eq_zero_or_pos (wordConst w) with h0 | h0
    · exfalso
      have ho : oddCount w = 0 := (wordConst_eq_zero_iff w).mp h0
      rw [h0, ho, pow_zero, one_mul, add_zero] at haff
      have h2 : 2 ≤ 2 ^ d := by
        calc 2 = 2 ^ 1 := (pow_one 2).symm
          _ ≤ 2 ^ d := Nat.pow_le_pow_right (by norm_num) hd
      have : 2 * x ≤ 2 ^ d * x := Nat.mul_le_mul_right x h2
      omega
    · exact h0
  have hlt : 3 ^ oddCount w * x < 2 ^ d * x := by omega
  exact Nat.lt_of_mul_lt_mul_right hlt

/-- **Juggler realises the same multiplier on the exponent, with the correction pointing
down.** Restated from `power_bound_word` in the vocabulary of this file. -/
theorem juggler_word_power {n : ℕ} {w : List Branch} (hw : follows n w) :
    (image n w) ^ (2 ^ w.length) ≤ n ^ (3 ^ oddCount w) := by
  rw [image_eq_iterate]
  exact power_bound_word hw

/-- **Juggler cycles expand.** `CycleCore`'s theorem, placed beside its Collatz mirror. -/
theorem juggler_cycle_expanding {n : ℕ} {w : List Branch} (hn : 2 ≤ n) (h : CycleItinerary n w) :
    2 ^ w.length < 3 ^ oddCount w :=
  cycle_itinerary_formally_expanding hn h

/-! ## 8. Kernel checks against OEIS A076227

The entry's own example: modulo `64` the surviving residues are `7, 15, 27, 31, 39, 47, 59, 63`
(Labos Elemer, 2002). And its terms at `n = 4 … 10`, which are the laboratory's `N_4 … N_10`. -/

theorem undecidedResidues_six : undecidedResidues 6 = {7, 15, 27, 31, 39, 47, 59, 63} := by
  decide +kernel

theorem undecidedResidues_card_four : (undecidedResidues 4).card = 3 := by decide +kernel
theorem undecidedResidues_card_five : (undecidedResidues 5).card = 4 := by decide +kernel
theorem undecidedResidues_card_six : (undecidedResidues 6).card = 8 := by decide +kernel
theorem undecidedResidues_card_seven : (undecidedResidues 7).card = 13 := by decide +kernel
theorem undecidedResidues_card_eight : (undecidedResidues 8).card = 19 := by decide +kernel
theorem undecidedResidues_card_nine : (undecidedResidues 9).card = 38 := by decide +kernel
theorem undecidedResidues_card_ten : (undecidedResidues 10).card = 64 := by decide +kernel


/-! ## 9. The even-step charge: the Collatz walk charge, in integers

Paper A's walk charge reads the floor losses of a Juggler cycle against the height of the
exponent walk. On the Collatz side the same reading is an identity. Conjugating the odd step by
`z = x + 1` (`(3x+1)/2 + 1 = (3/2)(x+1)`) shows that every even step, and only an even step,
injects a correction, and that correction is `3` to the power of the odd letters still to come:

  `2 ^ d · (C^d(x) + 1) = 3 ^ o · (x + 1) + evenCharge w`,

so on a cycle `(x + 1)(2 ^ d - 3 ^ o) = evenCharge w` exactly. Reading `evenCharge` as
`sum over even positions i of 3 ^ (o - a_i) · 2 ^ i`, the surplus is the sum over even steps of
`2 ^ (-h_i)` scaled by `2 ^ d`, with `h_i = a_i · log2 3 - i` the walk height; this is the
statement whose analytic form, `Lambda ≤ H(p) / (3 x_min)` with `H(p)/p → 1/(2 log 2)`, is
recorded in `docs/problems/juggler_collatz_finance_mirror.md`. Nothing analytic is proved here:
these are natural-number identities. -/

/-- The even-step charge of a word: an even letter contributes `3` to the power of the odd
letters still to come, and every letter doubles what follows. Closed form: the sum over even
positions `i` of `3 ^ (o - a_i) * 2 ^ i`, with `a_i` the odd letters before `i`. -/
def evenCharge : List Branch → ℕ
  | [] => 0
  | .even :: w => 3 ^ oddCount w + 2 * evenCharge w
  | .odd :: w => 2 * evenCharge w

@[simp] theorem evenCharge_nil : evenCharge [] = 0 := rfl

@[simp] theorem evenCharge_even (w : List Branch) :
    evenCharge (.even :: w) = 3 ^ oddCount w + 2 * evenCharge w := rfl

@[simp] theorem evenCharge_odd (w : List Branch) : evenCharge (.odd :: w) = 2 * evenCharge w := rfl

/-- The odd-step constant and the even-step charge differ by the multiplier gap:
`wordConst w + 2 ^ |w| = 3 ^ o + evenCharge w`. -/
theorem wordConst_add_two_pow (w : List Branch) :
    wordConst w + 2 ^ w.length = 3 ^ oddCount w + evenCharge w := by
  induction w with
  | nil => simp
  | cons b w ih =>
    cases b with
    | even =>
      simp only [wordConst_even, evenCharge_even, oddCount_even_cons, List.length_cons, pow_succ]
      linarith
    | odd =>
      simp only [wordConst_odd, evenCharge_odd, oddCount_odd_cons, List.length_cons, pow_succ]
      linarith

/-- **The affine formula in the `x + 1` coordinate.** Every correction comes from an even step. -/
theorem two_pow_mul_iter_add_one (x d : ℕ) :
    2 ^ d * (shortcutCIter d x + 1) =
      3 ^ oddCount (parityWord x d) * (x + 1) + evenCharge (parityWord x d) := by
  have h := word_affine x d
  have h2 := wordConst_add_two_pow (parityWord x d)
  rw [parityWord_length] at h2
  linarith

/-- **The Collatz lower envelope**, the mirror of `power_bound_word`: the `+1`s only push up,
so `3 ^ o · (x + 1) ≤ 2 ^ d · (C^d(x) + 1)` for every start and every depth. -/
theorem three_pow_mul_add_one_le (x d : ℕ) :
    3 ^ oddCount (parityWord x d) * (x + 1) ≤ 2 ^ d * (shortcutCIter d x + 1) := by
  rw [two_pow_mul_iter_add_one]
  exact Nat.le_add_right _ _

/-- **The Collatz walk charge, exactly.** On a cycle the surplus `(x + 1)(2 ^ d - 3 ^ o)` is the
even-step charge of the word. This is the counterpart of Paper A's finance inequality
`n log n (3 ^ o - 2 ^ L) ≤ L 3 ^ o`, as an identity rather than a bound. -/
theorem cycle_even_charge {x d : ℕ} (hcyc : shortcutCIter d x = x) :
    (x + 1) * 2 ^ d = (x + 1) * 3 ^ oddCount (parityWord x d) + evenCharge (parityWord x d) := by
  have h := two_pow_mul_iter_add_one x d
  rw [hcyc] at h
  linarith

/-- The trivial cycle `1 → 2 → 1` has word `OE`, charge `2`, and `(1+1)(4 - 3) = 2`. -/
theorem trivial_cycle_charge :
    (1 + 1) * 2 ^ 2 = (1 + 1) * 3 ^ oddCount (parityWord 1 2) + evenCharge (parityWord 1 2) := by
  decide +kernel

end CollatzBridge

end Problems.Juggler
