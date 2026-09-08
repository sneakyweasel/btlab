/-
# Variation across a jump

Paper A's Theorem 5.7 bounds the variation of its observable by "\(<2\), including the wrap
jump": the observable falls monotonically across a period and then jumps back up.  Mathlib
computes the variation of a *monotone* function on an interval (`MonotoneOn.eVariationOn_eq`)
and has nothing for that shape.  This file supplies the three general facts needed.

* `eVariationOn_neg` — variation ignores a sign, so the monotone lemma serves antitone
  functions too (`antitoneOn_eVariationOn_eq`).
* `eVariationOn_add_le` — variation is subadditive in the function.  Mathlib has the
  subadditivity in the *set* (`eVariationOn.add_le_union`), not in the function.
* `eVariationOn_le_of_jump` — the shape itself.  If `f` is antitone below `b`, bounded below
  there by `L`, and `f b` is at least everything below, then the variation on `Icc a b` is at
  most `(f a − L) + (f b − L)`: the fall, plus the jump.

`periodic_window_variation_le` then reads the bound off for a one-periodic sawtooth on *any*
window of length one — the uniform bound `denjoy_koksma_blocks` asks for — and the last
section instantiates all of it at Paper A's own observable, ending at `block_envelope`, which
is Theorem 5.7's display.

The proof of the jump lemma is a decomposition rather than a computation.  Write
`g x = if x < b then f x else L`, which is antitone on `Icc a b`, and `h = f − g`, which is
`0` below `b` and `f b − L` at it, hence monotone.  Then `f = g + h` *everywhere* — that is
why `h` is defined by subtraction rather than by a second `if` — and the two variations are
Mathlib's monotone computation.
-/

import Problems.Juggler.DenjoyKoksmaOrbit
import Mathlib.MeasureTheory.Function.Floor
import Problems.Juggler.OstrowskiSandwich

open Set

namespace Problems.Juggler

/-- Variation ignores a sign. -/
theorem eVariationOn_neg (f : ℝ → ℝ) (s : Set ℝ) :
    eVariationOn (fun x => -f x) s = eVariationOn f s := by
  unfold eVariationOn
  refine iSup_congr fun p => Finset.sum_congr rfl fun i _ => ?_
  rw [edist_dist, edist_dist, Real.dist_eq, Real.dist_eq, ← abs_neg]
  ring_nf

/-- The antitone counterpart of `MonotoneOn.eVariationOn_eq`. -/
theorem antitoneOn_eVariationOn_eq {f : ℝ → ℝ} {s : Set ℝ} {a b : ℝ}
    (hf : AntitoneOn f s) (as : a ∈ s) (bs : b ∈ s) :
    eVariationOn f (s ∩ Icc a b) = ENNReal.ofReal (f a - f b) := by
  have hm : MonotoneOn (fun x => -f x) s := fun x hx y hy hxy => neg_le_neg (hf hx hy hxy)
  have h := hm.eVariationOn_eq as bs
  rw [eVariationOn_neg] at h
  rw [h]
  congr 1
  ring

/-- Variation is subadditive in the function. -/
theorem eVariationOn_add_le (f g : ℝ → ℝ) (s : Set ℝ) :
    eVariationOn (fun x => f x + g x) s ≤ eVariationOn f s + eVariationOn g s := by
  apply iSup_le
  rintro ⟨n, u⟩
  calc ∑ i ∈ Finset.range n,
        edist (f (u.1 (i + 1)) + g (u.1 (i + 1))) (f (u.1 i) + g (u.1 i))
      ≤ ∑ i ∈ Finset.range n,
          (edist (f (u.1 (i + 1))) (f (u.1 i)) + edist (g (u.1 (i + 1))) (g (u.1 i))) := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [edist_dist, edist_dist, edist_dist, Real.dist_eq, Real.dist_eq, Real.dist_eq,
          ← ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)]
        exact ENNReal.ofReal_le_ofReal (by
          have := abs_add_le (f (u.1 (i + 1)) - f (u.1 i)) (g (u.1 (i + 1)) - g (u.1 i))
          calc |f (u.1 (i + 1)) + g (u.1 (i + 1)) - (f (u.1 i) + g (u.1 i))|
              = |(f (u.1 (i + 1)) - f (u.1 i)) + (g (u.1 (i + 1)) - g (u.1 i))| := by ring_nf
            _ ≤ _ := this)
    _ = (∑ i ∈ Finset.range n, edist (f (u.1 (i + 1))) (f (u.1 i)))
          + ∑ i ∈ Finset.range n, edist (g (u.1 (i + 1))) (g (u.1 i)) := Finset.sum_add_distrib
    _ ≤ eVariationOn f s + eVariationOn g s :=
        add_le_add (le_iSup (fun p : ℕ × { v : ℕ → ℝ // Monotone v ∧ ∀ i, v i ∈ s } =>
            ∑ i ∈ Finset.range p.1, edist (f (p.2.1 (i + 1))) (f (p.2.1 i))) ⟨n, u⟩)
          (le_iSup (fun p : ℕ × { v : ℕ → ℝ // Monotone v ∧ ∀ i, v i ∈ s } =>
            ∑ i ∈ Finset.range p.1, edist (g (p.2.1 (i + 1))) (g (p.2.1 i))) ⟨n, u⟩)

/-- **Variation across an upward jump at the right endpoint.**  The fall, plus the jump. -/
theorem eVariationOn_le_of_jump {f : ℝ → ℝ} {a b L : ℝ} (hab : a ≤ b)
    (hanti : AntitoneOn f (Ico a b))
    (hL : ∀ t ∈ Ico a b, L ≤ f t)
    (hmax : ∀ t ∈ Ico a b, f t ≤ f b) (hLb : L ≤ f b) :
    eVariationOn f (Icc a b) ≤ ENNReal.ofReal (f a - L) + ENNReal.ofReal (f b - L) := by
  rcases eq_or_lt_of_le hab with rfl | hlt
  · have h0 : eVariationOn f (Icc a a) = 0 := eVariationOn.subsingleton f (by simp)
    rw [h0]
    exact zero_le
  set g : ℝ → ℝ := fun x => if x < b then f x else L with hg
  set h : ℝ → ℝ := fun x => f x - g x with hh
  have hga : g a = f a := by simp [hg, hlt]
  have hgb : g b = L := by simp [hg]
  have hha : h a = 0 := by simp [hh, hga]
  have hhb : h b = f b - L := by simp [hh, hgb]
  have hganti : AntitoneOn g (Icc a b) := by
    intro s hs t ht hst
    by_cases hsb : s < b
    · by_cases htb : t < b
      · simpa [hg, hsb, htb] using hanti ⟨hs.1, hsb⟩ ⟨ht.1, htb⟩ hst
      · simpa [hg, hsb, htb] using hL s ⟨hs.1, hsb⟩
    · have : t = b := le_antisymm ht.2 (le_trans (not_lt.mp hsb) hst)
      simp [hg, hsb, this]
  have hhmono : MonotoneOn h (Icc a b) := by
    intro s hs t ht hst
    by_cases hsb : s < b
    · by_cases htb : t < b
      · simp [hh, hg, hsb, htb]
      · have htb' : t = b := le_antisymm ht.2 (not_lt.mp htb)
        simp only [hh, hg, if_pos hsb, if_neg htb, sub_self]
        rw [htb']
        simp
        linarith [hLb]
    · have hsb' : s = b := le_antisymm hs.2 (not_lt.mp hsb)
      have htb' : t = b := le_antisymm ht.2 (le_trans (not_lt.mp hsb) hst)
      rw [hsb', htb']
  have hsplit : ∀ x, f x = g x + h x := by intro x; simp [hh]
  calc eVariationOn f (Icc a b)
      = eVariationOn (fun x => g x + h x) (Icc a b) := by
        refine iSup_congr fun p => Finset.sum_congr rfl fun i _ => ?_
        simp only [hsplit]
    _ ≤ eVariationOn g (Icc a b) + eVariationOn h (Icc a b) := eVariationOn_add_le g h _
    _ = ENNReal.ofReal (f a - L) + ENNReal.ofReal (f b - L) := by
        have hgv := antitoneOn_eVariationOn_eq hganti (left_mem_Icc.mpr hab)
          (right_mem_Icc.mpr hab)
        have hhv := hhmono.eVariationOn_eq (left_mem_Icc.mpr hab) (right_mem_Icc.mpr hab)
        rw [inter_self] at hgv hhv
        rw [hgv, hhv, hga, hgb, hha, hhb, sub_zero]

/-- **The variation of a one-periodic sawtooth on any window of length one.**  If `P` has
period `1`, is antitone across `[0,1)` with `P 0 = M` its maximum and `m` a lower bound, then
every window `[y, y+1]` carries variation at most `2(M − m)` — the fall, plus the jump, and
that is all, whatever the phase `y`.  This is the uniform bound `denjoy_koksma_blocks` asks
for. -/
theorem periodic_window_variation_le {P : ℝ → ℝ} {m M : ℝ}
    (hper : Function.Periodic P 1) (hanti : AntitoneOn P (Ico 0 1)) (hP0 : P 0 = M)
    (hlow : ∀ t ∈ Ico (0:ℝ) 1, m ≤ P t) (y : ℝ) :
    eVariationOn P (Icc y (y + 1)) ≤ ENNReal.ofReal (2 * (M - m)) := by
  have hshift : ∀ (k : ℤ) (x : ℝ), P (x + k) = P x := by
    intro k x
    simpa [sub_eq_add_neg] using hper.sub_int_mul_eq (x := x) (-k)
  set n : ℤ := ⌊y⌋ with hn
  have hyn : (n : ℝ) ≤ y := Int.floor_le y
  have hyn1 : y < (n : ℝ) + 1 := Int.lt_floor_add_one y
  set j : ℝ := (n : ℝ) + 1 with hj
  have hyj : y ≤ j := le_of_lt hyn1
  have hjy1 : j ≤ y + 1 := by simp only [hj]; linarith
  -- `P` is antitone across each unit block, by periodicity
  have hantiOn : ∀ k : ℤ, AntitoneOn P (Ico (k : ℝ) ((k : ℝ) + 1)) := by
    intro k s hs t ht hst
    have hs' : s - (k : ℝ) ∈ Ico (0:ℝ) 1 := ⟨by linarith [hs.1], by linarith [hs.2]⟩
    have ht' : t - (k : ℝ) ∈ Ico (0:ℝ) 1 := ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have hkey := hanti hs' ht' (by linarith)
    have e1 : s - (k : ℝ) = s + ((-k : ℤ) : ℝ) := by push_cast; ring
    have e2 : t - (k : ℝ) = t + ((-k : ℤ) : ℝ) := by push_cast; ring
    rwa [e1, e2, hshift, hshift] at hkey
  -- values on the block containing `y`
  have hblock : ∀ t, (n : ℝ) ≤ t → t < j → m ≤ P t ∧ P t ≤ M := by
    intro t ht1 ht2
    have hmem : t - (n : ℝ) ∈ Ico (0:ℝ) 1 := ⟨by linarith, by simp only [hj] at ht2; linarith⟩
    have e : t - (n : ℝ) = t + ((-n : ℤ) : ℝ) := by push_cast; ring
    refine ⟨?_, ?_⟩
    · have := hlow _ hmem
      rwa [e, hshift] at this
    · have := hanti (left_mem_Ico.mpr one_pos) hmem hmem.1
      rw [hP0, e, hshift] at this
      exact this
  have hPj : P j = M := by
    have : P ((0:ℝ) + ((n + 1 : ℤ) : ℝ)) = P 0 := hshift (n + 1) 0
    simpa [hj, hP0] using this
  have hPy1 : P (y + 1) = P y := by
    have := hshift 1 y
    simpa using this
  have hy := hblock y hyn hyn1
  -- the left piece carries the jump
  have hleft : eVariationOn P (Icc y j)
      ≤ ENNReal.ofReal (P y - m) + ENNReal.ofReal (M - m) := by
    have hsub : Ico y j ⊆ Ico (n : ℝ) ((n : ℝ) + 1) := Ico_subset_Ico hyn le_rfl
    have h := eVariationOn_le_of_jump (f := P) (a := y) (b := j) (L := m) hyj
      ((hantiOn n).mono hsub)
      (fun t ht => (hblock t (le_trans hyn ht.1) ht.2).1)
      (fun t ht => by rw [hPj]; exact (hblock t (le_trans hyn ht.1) ht.2).2)
      (by rw [hPj]; linarith [hy.1, hy.2])
    rwa [hPj] at h
  -- the right piece is a plain antitone fall
  have hright : eVariationOn P (Icc j (y + 1)) = ENNReal.ofReal (M - P y) := by
    have hsub : Icc j (y + 1) ⊆ Ico ((n + 1 : ℤ) : ℝ) (((n + 1 : ℤ) : ℝ) + 1) := by
      intro t ht
      refine ⟨by push_cast; simp only [hj] at ht; linarith [ht.1], ?_⟩
      push_cast
      linarith [ht.2, hyn1]
    have h := antitoneOn_eVariationOn_eq ((hantiOn (n + 1)).mono hsub)
      (left_mem_Icc.mpr hjy1) (right_mem_Icc.mpr hjy1)
    rw [inter_self] at h
    rw [h, hPj, hPy1]
  have hadd := eVariationOn.Icc_add_Icc P (s := univ) hyj hjy1 (mem_univ j)
  simp only [univ_inter] at hadd
  rw [← hadd, hright]
  have hnn1 : (0:ℝ) ≤ P y - m := by linarith [hy.1]
  have hnn2 : (0:ℝ) ≤ M - m := by linarith [hy.1, hy.2]
  have hnn3 : (0:ℝ) ≤ M - P y := by linarith [hy.2]
  calc eVariationOn P (Icc y j) + ENNReal.ofReal (M - P y)
      ≤ (ENNReal.ofReal (P y - m) + ENNReal.ofReal (M - m))
          + ENNReal.ofReal (M - P y) := add_le_add hleft le_rfl
    _ = ENNReal.ofReal ((P y - m) + (M - m) + (M - P y)) := by
        rw [← ENNReal.ofReal_add hnn1 hnn2, ← ENNReal.ofReal_add (by linarith) hnn3]
    _ = ENNReal.ofReal (2 * (M - m)) := by congr 1; ring

/-! ### Paper A's own observable

Theorem 5.7 takes `F(u) = n'^{1−2^u}/2^u` on the circle `ℝ/(1+α)ℤ`, `α = log₂(3/2)`, and
asserts that it "decreases on the circle from `F(0)=1` to `F((1+α)⁻) = n'^{-2}/3`, so its
variation including the wrap jump is `<2`; the rescaled observable on `ℝ/ℤ` has the same
variation."  Both halves are below.  The rescaling is not a separate step here: the periodic
observable is *defined* as `F` of the fractional part times the period, so it lives on `ℝ/ℤ`
from the start.
-/

/-- Paper A's block observable `F(u) = n'^{1−2^u}/2^u`. -/
noncomputable def blockObservable (n' u : ℝ) : ℝ := n' ^ (1 - (2:ℝ) ^ u) / (2:ℝ) ^ u

/-- The circle length `1 + α` with `α = log₂(3/2)` — which is `log₂ 3`, since
`1 + log₂(3/2) = log₂ 2 + log₂(3/2)`.  Writing it that way keeps the file to `Real.log`. -/
noncomputable def circlePeriod : ℝ := Real.log 3 / Real.log 2

theorem log_two_ne_zero : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))

theorem two_rpow_circlePeriod : (2:ℝ) ^ circlePeriod = 3 := by
  unfold circlePeriod
  rw [Real.rpow_def_of_pos (by norm_num),
    show Real.log 2 * (Real.log 3 / Real.log 2) = Real.log 3 by
      field_simp]
  exact Real.exp_log (by norm_num)

theorem circlePeriod_pos : 0 < circlePeriod := by
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  unfold circlePeriod
  positivity

/-- `F` falls: for `n' > 1` it is antitone on the whole line. -/
theorem blockObservable_antitone {n' : ℝ} (hn : 1 < n') : Antitone (blockObservable n') := by
  intro u v huv
  have h2u : (0:ℝ) < (2:ℝ) ^ u := Real.rpow_pos_of_pos (by norm_num) u
  have h2v : (0:ℝ) < (2:ℝ) ^ v := Real.rpow_pos_of_pos (by norm_num) v
  have h2 : (2:ℝ) ^ u ≤ (2:ℝ) ^ v := (Real.rpow_le_rpow_left_iff (by norm_num)).mpr huv
  have hexp : n' ^ (1 - (2:ℝ) ^ v) ≤ n' ^ (1 - (2:ℝ) ^ u) :=
    (Real.rpow_le_rpow_left_iff hn).mpr (by linarith)
  have hnum : (0:ℝ) ≤ n' ^ (1 - (2:ℝ) ^ v) :=
    le_of_lt (Real.rpow_pos_of_pos (by linarith) _)
  unfold blockObservable
  calc n' ^ (1 - (2:ℝ) ^ v) / (2:ℝ) ^ v ≤ n' ^ (1 - (2:ℝ) ^ u) / (2:ℝ) ^ v := by gcongr
    _ ≤ n' ^ (1 - (2:ℝ) ^ u) / (2:ℝ) ^ u := by gcongr

theorem blockObservable_zero {n' : ℝ} (_hn : 0 < n') : blockObservable n' 0 = 1 := by
  unfold blockObservable
  rw [Real.rpow_zero, sub_self, Real.rpow_zero]
  norm_num

theorem blockObservable_period {n' : ℝ} (_hn : 0 < n') :
    blockObservable n' circlePeriod = n' ^ (-2 : ℝ) / 3 := by
  unfold blockObservable
  rw [two_rpow_circlePeriod]
  norm_num

/-- The observable transported to `ℝ/ℤ`: `F` of the fractional part times the period. -/
noncomputable def periodicObservable (n' x : ℝ) : ℝ :=
  blockObservable n' (Int.fract x * circlePeriod)

theorem periodicObservable_periodic (n' : ℝ) : Function.Periodic (periodicObservable n') 1 := by
  intro x
  simp [periodicObservable, Int.fract_add_one]

theorem periodicObservable_zero {n' : ℝ} (hn : 0 < n') : periodicObservable n' 0 = 1 := by
  simp [periodicObservable, blockObservable_zero hn]

theorem periodicObservable_antitoneOn {n' : ℝ} (hn : 1 < n') :
    AntitoneOn (periodicObservable n') (Ico 0 1) := by
  intro s hs t ht hst
  have hfs : Int.fract s = s := Int.fract_eq_self.mpr ⟨hs.1, hs.2⟩
  have hft : Int.fract t = t := Int.fract_eq_self.mpr ⟨ht.1, ht.2⟩
  simp only [periodicObservable, hfs, hft]
  exact blockObservable_antitone hn
    (mul_le_mul_of_nonneg_right hst (le_of_lt circlePeriod_pos))

theorem periodicObservable_lower {n' : ℝ} (hn : 1 < n') {t : ℝ} (ht : t ∈ Ico (0:ℝ) 1) :
    n' ^ (-2 : ℝ) / 3 ≤ periodicObservable n' t := by
  have hfs : Int.fract t = t := Int.fract_eq_self.mpr ⟨ht.1, ht.2⟩
  have hle : t * circlePeriod ≤ circlePeriod := by
    nlinarith [circlePeriod_pos, ht.2]
  have := blockObservable_antitone hn hle
  rw [blockObservable_period (by linarith)] at this
  simpa [periodicObservable, hfs] using this

/-- **Theorem 5.7's variation bound.**  Every window of length one carries variation at most
`2(1 − n'^{-2}/3)`: the fall from `1` to `n'^{-2}/3`, plus the wrap jump back. -/
theorem observable_window_variation_le {n' : ℝ} (hn : 1 < n') (y : ℝ) :
    eVariationOn (periodicObservable n') (Icc y (y + 1))
      ≤ ENNReal.ofReal (2 * (1 - n' ^ (-2 : ℝ) / 3)) :=
  periodic_window_variation_le (periodicObservable_periodic n')
    (periodicObservable_antitoneOn hn) (periodicObservable_zero (by linarith))
    (fun _ ht => periodicObservable_lower hn ht) y

/-- And so it is under `2`, which is the constant Theorem 5.7 quotes. -/
theorem observable_window_variation_lt_two {n' : ℝ} (hn : 1 < n') (y : ℝ) :
    (eVariationOn (periodicObservable n') (Icc y (y + 1))).toReal < 2 := by
  have hpos : (0:ℝ) < n' ^ (-2 : ℝ) / 3 := by
    have := Real.rpow_pos_of_pos (show (0:ℝ) < n' by linarith) (-2 : ℝ)
    linarith
  have hlt1 : n' ^ (-2 : ℝ) < 1 := Real.rpow_lt_one_of_one_lt_of_neg hn (by norm_num)
  have hle := observable_window_variation_le hn y
  have hfin : eVariationOn (periodicObservable n') (Icc y (y + 1)) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hle
  have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hle
  rw [ENNReal.toReal_ofReal (by linarith)] at this
  linarith

theorem observable_boundedVariationOn {n' : ℝ} (hn : 1 < n') (y : ℝ) :
    BoundedVariationOn (periodicObservable n') (Icc y (y + 1)) :=
  ne_top_of_le_ne_top ENNReal.ofReal_ne_top (observable_window_variation_le hn y)

theorem blockObservable_pos {n' : ℝ} (hn : 0 < n') (u : ℝ) : 0 < blockObservable n' u := by
  unfold blockObservable
  exact div_pos (Real.rpow_pos_of_pos hn _) (Real.rpow_pos_of_pos (by norm_num) _)

theorem periodicObservable_pos {n' : ℝ} (hn : 0 < n') (x : ℝ) : 0 < periodicObservable n' x :=
  blockObservable_pos hn _

theorem periodicObservable_le_one {n' : ℝ} (hn : 1 < n') (x : ℝ) :
    periodicObservable n' x ≤ 1 := by
  have h0 : (0:ℝ) ≤ Int.fract x := Int.fract_nonneg x
  have := blockObservable_antitone hn
    (show (0:ℝ) ≤ Int.fract x * circlePeriod from
      mul_nonneg h0 (le_of_lt circlePeriod_pos))
  rw [blockObservable_zero (by linarith)] at this
  exact this

theorem blockObservable_continuous {n' : ℝ} (hn : 0 < n') :
    Continuous (blockObservable n') := by
  unfold blockObservable
  have hnum : Continuous fun u : ℝ => n' ^ (1 - (2:ℝ) ^ u) := by
    fun_prop (disch := positivity)
  have hden : Continuous fun u : ℝ => (2:ℝ) ^ u := by fun_prop (disch := positivity)
  exact hnum.div hden fun u => ne_of_gt (Real.rpow_pos_of_pos (by norm_num) u)

theorem periodicObservable_measurable {n' : ℝ} (hn : 0 < n') :
    Measurable (periodicObservable n') :=
  (blockObservable_continuous hn).measurable.comp (measurable_fract.mul_const circlePeriod)

theorem periodicObservable_intervalIntegrable {n' : ℝ} (hn : 1 < n') (y : ℝ) :
    IntervalIntegrable (periodicObservable n') MeasureTheory.volume y (y + 1) := by
  rw [intervalIntegrable_iff, uIoc_of_le (by linarith : y ≤ y + 1)]
  refine MeasureTheory.Measure.integrableOn_of_bounded (M := 1) measure_Ioc_lt_top.ne
    ((periodicObservable_measurable (by linarith)).aestronglyMeasurable) ?_
  filter_upwards with t
  rw [Real.norm_eq_abs, abs_of_pos (periodicObservable_pos (by linarith) t)]
  exact periodicObservable_le_one hn t

/-- **Theorem 5.7's block envelope.**  For Paper A's observable and any decomposition of `L`
into convergent denominators, the ergodic sum is within `2·s(L)` of `L·C_*` — which, divided
by `L`, is the display `|C_L − C_*| ≤ 2 s(L)/L`. -/
theorem block_envelope {n' θ : ℝ} (hn : 1 < n') (blocks : List (ℕ × ℕ))
    (hblocks : ∀ pq ∈ blocks, 0 < pq.2 ∧ Nat.Coprime pq.1 pq.2 ∧
      |θ - (pq.1 : ℝ) / pq.2| ≤ 1 / (pq.2 : ℝ) ^ 2) (x : ℝ) :
    |∑ k ∈ Finset.range (blocks.map Prod.snd).sum, periodicObservable n' (x + k * θ)
       - ((blocks.map Prod.snd).sum : ℕ) * ∫ t in (0:ℝ)..1, periodicObservable n' t|
      ≤ blocks.length * 2 :=
  denjoy_koksma_blocks (periodicObservable_periodic n')
    (fun y => observable_boundedVariationOn hn y)
    (fun y => periodicObservable_intervalIntegrable hn y)
    (fun y => le_of_lt (observable_window_variation_lt_two hn y)) blocks hblocks x

/-- The certified convergents of `θ` satisfy the block hypothesis verbatim. -/
theorem thetaConvergents_block_hypothesis :
    ∀ pq ∈ thetaConvergents, 0 < pq.2 ∧ Nat.Coprime pq.1 pq.2 ∧
      |walkTheta - (pq.1 : ℝ) / pq.2| ≤ 1 / (pq.2 : ℝ) ^ 2 := by
  intro pq hpq
  refine ⟨?_, theta_convergents_coprime pq hpq, le_of_lt (theta_convergent_quality pq hpq)⟩
  fin_cases hpq <;> norm_num

/-- **Theorem 5.7 for `θ` itself.**  Any list of certified convergents — a pair repeated once
per Ostrowski digit — bounds the ergodic sum of Paper A's observable along the rescaled
rotation.  `(blocks.map Prod.snd).sum` is `L` and `blocks.length` is `s(L)`, so dividing by
`L` gives the display `|C_L − C_*| ≤ 2 s(L)/L`. -/
theorem theta_block_envelope {n' : ℝ} (hn : 1 < n') (blocks : List (ℕ × ℕ))
    (hsub : ∀ pq ∈ blocks, pq ∈ thetaConvergents) (x : ℝ) :
    |∑ k ∈ Finset.range (blocks.map Prod.snd).sum,
        periodicObservable n' (x + k * walkTheta)
       - ((blocks.map Prod.snd).sum : ℕ) * ∫ t in (0:ℝ)..1, periodicObservable n' t|
      ≤ blocks.length * 2 :=
  block_envelope hn blocks (fun pq h => thetaConvergents_block_hypothesis pq (hsub pq h)) x

end Problems.Juggler
